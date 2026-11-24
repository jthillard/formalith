//! Remarkable points of curves `y = f(x)` in a range, roots, extrema and intersections, searched in compute
//! shaders ([`crate::shader::analysis`]). Results are read back asynchronously: [`Analyzer::start`] a search, then
//! [`Analyzer::poll`] it at each frame.

use std::{
    collections::HashMap,
    sync::{
        Arc,
        atomic::{AtomicU8, Ordering},
    },
};

use eframe::egui_wgpu::wgpu::{self, util::DeviceExt as _};

use super::{Shader, bytes};
use crate::shader::{self, AnalysisCurves};

/// The kind of a remarkable point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `f(x) = 0`.
    Root,
    /// A local minimum.
    Minimum,
    /// A local maximum.
    Maximum,
    /// Two curves meet.
    Intersection,
}

impl Kind {
    /// The name of the kind.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Root => "root",
            Self::Minimum => "minimum",
            Self::Maximum => "maximum",
            Self::Intersection => "intersection",
        }
    }

    /// The kind of its number in [`crate::shader::ANALYSIS`].
    fn from_code(code: f32) -> Option<Self> {
        Some(match code {
            1. => Self::Root,
            2. => Self::Minimum,
            3. => Self::Maximum,
            4. => Self::Intersection,
            _ => return None,
        })
    }
}

/// A remarkable point.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Point {
    /// Its kind.
    pub kind: Kind,
    /// Its abscissa.
    pub x: f64,
    /// Its ordinate.
    pub y: f64,
}

/// Maximum number of zeros of a function, past which its points aren't shown (like for `sin(1/x)`).
const MAX_POINTS: u32 = 100;

/// The size of workgroups of [`crate::shader::ANALYSIS`].
const WORKGROUP: u32 = 64;

/// Compiled shaders kept, by hash.
const MAX_PIPELINES: usize = 16;

/// A search of remarkable points.
pub struct Request<'a> {
    /// The curves.
    pub curves: AnalysisCurves<'a>,
    /// The values of the parameters of `f`, then of each other curve.
    pub params: Vec<f32>,
    /// The range.
    pub a: f64,
    /// The end of the range.
    pub b: f64,
    /// The number of intervals the range is sampled on.
    pub samples: usize,
}

/// A search whose results are read back.
struct Pending {
    staging: wgpu::Buffer,
    /// 0 while mapping, 1 once mapped, 2 on failure.
    status: Arc<AtomicU8>,
    modes: usize,
    capacity: usize,
    /// The offset of points in `staging`.
    offset: usize,
    step: f64,
    /// The offset of the timestamps of the passes in `staging` and the CPU time they were submitted at, if timed.
    #[cfg(feature = "profile")]
    timing: Option<(usize, i64)>,
}

/// Searches remarkable points on a GPU with compute shaders.
pub struct Analyzer {
    device: wgpu::Device,
    queue: wgpu::Queue,
    layout: wgpu::BindGroupLayout,
    pipeline_layout: wgpu::PipelineLayout,
    /// The `sample` and `refine` pipelines of shaders, by hash.
    pipelines: HashMap<u64, (wgpu::ComputePipeline, wgpu::ComputePipeline)>,
    pending: Option<Pending>,
    repaint: Arc<dyn Fn() + Send + Sync>,
    /// The timestamps of the passes, the buffer they are resolved to and the period of ticks, when the GPU has
    /// them, for the profiler.
    #[cfg(feature = "profile")]
    timestamps: Option<(wgpu::QuerySet, wgpu::Buffer, f32)>,
}

/// The names of the timed passes.
#[cfg(feature = "profile")]
const PASSES: [(&str, &str); 2] = [("sample", ""), ("refine", "")];

/// A layout entry of a buffer of a compute shader.
const fn entry(binding: u32, ty: wgpu::BufferBindingType) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty,
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }
}

impl Analyzer {
    /// A searcher on `device`, `None` when `adapter` has no compute shaders (WebGL). `repaint` is called when
    /// results are ready.
    #[must_use]
    pub fn new(
        adapter: &wgpu::Adapter,
        device: wgpu::Device,
        queue: wgpu::Queue,
        repaint: Arc<dyn Fn() + Send + Sync>,
    ) -> Option<Self> {
        let compute = adapter
            .get_downlevel_capabilities()
            .flags
            .contains(wgpu::DownlevelFlags::COMPUTE_SHADERS);
        if !compute || device.limits().max_storage_buffers_per_shader_stage < 5 {
            return None;
        }
        let storage = |read_only| wgpu::BufferBindingType::Storage { read_only };
        let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("analysis"),
            entries: &[
                entry(0, wgpu::BufferBindingType::Uniform),
                entry(1, storage(true)),
                entry(2, storage(false)),
                entry(3, storage(false)),
                entry(4, storage(false)),
                entry(5, storage(false)),
            ],
        });
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("analysis"),
            bind_group_layouts: &[Some(&layout)],
            immediate_size: 0,
        });
        Some(Self {
            layout,
            pipeline_layout,
            pipelines: HashMap::new(),
            pending: None,
            repaint,
            #[cfg(feature = "profile")]
            timestamps: device
                .features()
                .contains(wgpu::Features::TIMESTAMP_QUERY)
                .then(|| {
                    let query_set = device.create_query_set(&wgpu::QuerySetDescriptor {
                        label: Some("analysis timestamps"),
                        ty: wgpu::QueryType::Timestamp,
                        count: 4,
                    });
                    let resolve = device.create_buffer(&wgpu::BufferDescriptor {
                        label: Some("analysis timestamps"),
                        size: 32,
                        usage: wgpu::BufferUsages::QUERY_RESOLVE | wgpu::BufferUsages::COPY_SRC,
                        mapped_at_creation: false,
                    });
                    (query_set, resolve, queue.get_timestamp_period())
                }),
            device,
            queue,
        })
    }

    /// The timestamps of the passes, if the profiler records and the GPU has them.
    fn timestamps(&self) -> Option<&wgpu::QuerySet> {
        #[cfg(feature = "profile")]
        return self
            .timestamps
            .as_ref()
            .filter(|_| crate::profiler::is_recording())
            .map(|(query_set, ..)| query_set);
        #[cfg(not(feature = "profile"))]
        None
    }

    /// Check if a search is running.
    #[must_use]
    pub const fn is_busy(&self) -> bool {
        self.pending.is_some()
    }

    /// The pipelines of `shader`, compiled if needed.
    fn pipelines(&mut self, shader: &Shader) -> &(wgpu::ComputePipeline, wgpu::ComputePipeline) {
        if !self.pipelines.contains_key(&shader.hash) {
            if self.pipelines.len() >= MAX_PIPELINES {
                self.pipelines.clear();
            }
            let module = self
                .device
                .create_shader_module(wgpu::ShaderModuleDescriptor {
                    label: Some("analysis"),
                    source: wgpu::ShaderSource::Wgsl(shader.source.as_str().into()),
                });
            let pipeline = |entry_point| {
                self.device
                    .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                        label: Some("analysis"),
                        layout: Some(&self.pipeline_layout),
                        module: &module,
                        entry_point: Some(entry_point),
                        compilation_options: wgpu::PipelineCompilationOptions::default(),
                        cache: None,
                    })
            };
            let pipelines = (pipeline("sample"), pipeline("refine"));
            self.pipelines.insert(shader.hash, pipelines);
        }
        &self.pipelines[&shader.hash]
    }

    /// Start the search of `request`, unless one is running. Returns whether it started.
    pub fn start(&mut self, request: &Request<'_>) -> bool {
        profile_scope!("Analyzer::start");
        if self.pending.is_some() || request.samples == 0 || !(request.b > request.a) {
            return false;
        }
        let shader = Shader::new(shader::analysis(&request.curves));
        let (sample, refine) = self.pipelines(&shader).clone();
        let n = request.samples;
        let modes = request.curves.modes();
        let width = request.b - request.a;
        let step = width / n as f64;
        #[allow(clippy::cast_possible_truncation)]
        let config: Vec<u8> = [
            bytes(&[request.a as f32, step as f32, (width * 1e-3) as f32]),
            [n as u32, modes as u32, 0, 0, 0]
                .iter()
                .flat_map(|value| value.to_le_bytes())
                .collect(),
        ]
        .concat();
        let device = &self.device;
        let init = |label, contents: &[u8], usage| {
            device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some(label),
                contents,
                usage,
            })
        };
        let storage = |label, size: usize, usage| {
            device.create_buffer(&wgpu::BufferDescriptor {
                label: Some(label),
                size: size as u64,
                usage: wgpu::BufferUsages::STORAGE | usage,
                mapped_at_creation: false,
            })
        };
        let config = init("config", &config, wgpu::BufferUsages::UNIFORM);
        let mut params = request.params.clone();
        // Bindings can't be empty
        params.push(0.);
        let params = init("params", &bytes(&params), wgpu::BufferUsages::STORAGE);
        let values = storage("values", modes * (n + 1) * 4, wgpu::BufferUsages::empty());
        let scales = storage("scales", modes * 4, wgpu::BufferUsages::empty());
        let capacity = modes * n;
        let points = storage("points", capacity * 16, wgpu::BufferUsages::COPY_SRC);
        let counters_size = (1 + modes) * 4;
        let counters = storage("counters", counters_size, wgpu::BufferUsages::COPY_SRC);
        let offset = counters_size.next_multiple_of(16);
        let timestamps = self.timestamps();
        // The timestamps of the passes after the points
        let timestamps_offset = offset + capacity * 16;
        let staging = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("staging"),
            size: (timestamps_offset + if timestamps.is_some() { 32 } else { 0 }) as u64,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("analysis"),
            layout: &self.layout,
            entries: &[&config, &params, &values, &scales, &points, &counters]
                .iter()
                .zip(0..)
                .map(|(buffer, binding)| wgpu::BindGroupEntry {
                    binding,
                    resource: buffer.as_entire_binding(),
                })
                .collect::<Vec<_>>(),
        });
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("analysis"),
        });
        #[allow(clippy::cast_possible_truncation)]
        let (n, modes) = (n as u32, modes as u32);
        // A pass each, so that each can be timed
        let passes = [
            (&sample, (n + 1).div_ceil(WORKGROUP)),
            (&refine, n.div_ceil(WORKGROUP)),
        ];
        for ((pipeline, groups), index) in passes.into_iter().zip(0..) {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("analysis"),
                timestamp_writes: timestamps.map(|query_set| wgpu::ComputePassTimestampWrites {
                    query_set,
                    beginning_of_pass_write_index: Some(2 * index),
                    end_of_pass_write_index: Some(2 * index + 1),
                }),
            });
            pass.set_bind_group(0, &bind_group, &[]);
            pass.set_pipeline(pipeline);
            pass.dispatch_workgroups(groups, modes, 1);
        }
        encoder.copy_buffer_to_buffer(&counters, 0, &staging, 0, counters_size as u64);
        encoder.copy_buffer_to_buffer(&points, 0, &staging, offset as u64, (capacity * 16) as u64);
        #[cfg(feature = "profile")]
        let timing =
            self.timestamps
                .as_ref()
                .zip(timestamps)
                .map(|((query_set, resolve, _), _)| {
                    encoder.resolve_query_set(query_set, 0..4, resolve, 0);
                    encoder.copy_buffer_to_buffer(
                        resolve,
                        0,
                        &staging,
                        timestamps_offset as u64,
                        32,
                    );
                    (timestamps_offset, puffin::now_ns())
                });
        self.queue.submit([encoder.finish()]);
        let modes = modes as usize;
        let status = Arc::new(AtomicU8::new(0));
        let mapped = status.clone();
        let repaint = self.repaint.clone();
        staging.map_async(wgpu::MapMode::Read, .., move |result| {
            mapped.store(if result.is_ok() { 1 } else { 2 }, Ordering::Release);
            repaint();
        });
        self.pending = Some(Pending {
            staging,
            status,
            modes,
            capacity,
            offset,
            step,
            #[cfg(feature = "profile")]
            timing,
        });
        true
    }

    /// The points found by the running search, once it is done.
    pub fn poll(&mut self) -> Option<Vec<Point>> {
        profile_scope!("Analyzer::poll");
        let pending = self.pending.as_ref()?;
        if pending.status.load(Ordering::Acquire) == 0 {
            // Natively, callbacks are only called when polling
            let _ = self.device.poll(wgpu::PollType::Poll);
        }
        let status = pending.status.load(Ordering::Acquire);
        if status == 0 {
            return None;
        }
        let pending = self.pending.take()?;
        if status != 1 {
            return Some(vec![]);
        }
        let points = {
            let Ok(data) = pending.staging.get_mapped_range(..) else {
                return Some(vec![]);
            };
            #[cfg(feature = "profile")]
            if let (Some((offset, anchor_ns)), Some((.., period))) =
                (pending.timing, &self.timestamps)
            {
                super::timer::report(
                    super::timer::ANALYSIS,
                    &PASSES,
                    &data[offset..offset + 32],
                    anchor_ns,
                    *period,
                );
            }
            read_points(&data, &pending)
        };
        pending.staging.unmap();
        Some(points)
    }

    /// Wait for the running search, natively.
    #[cfg(test)]
    fn wait(&mut self) -> Vec<Point> {
        let _ = self.device.poll(wgpu::PollType::wait_indefinitely());
        self.poll().expect("The search is done")
    }
}

/// The points in the readback buffer of `pending`.
fn read_points(data: &[u8], pending: &Pending) -> Vec<Point> {
    let word = |offset: usize| {
        let bytes = data[offset..offset + 4].try_into().expect("4 bytes");
        u32::from_le_bytes(bytes)
    };
    let count = (word(0) as usize).min(pending.capacity);
    // Zeros of each target, which aren't shown when there are too many
    let shown: Vec<bool> = (0..pending.modes)
        .map(|mode| word(4 * (1 + mode)) <= MAX_POINTS)
        .collect();
    let mut points: Vec<Point> = (0..count)
        .filter_map(|i| {
            let value = |k: usize| f32::from_bits(word(pending.offset + 16 * i + 4 * k));
            let kind = Kind::from_code(value(0))?;
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            let mode = value(3) as usize;
            let point = Point {
                kind,
                x: f64::from(value(1)),
                y: f64::from(value(2)),
            };
            (*shown.get(mode)? && point.x.is_finite() && point.y.is_finite()).then_some(point)
        })
        .collect();
    points.sort_by(|a, b| a.x.total_cmp(&b.x));
    points.dedup_by(|a, b| a.kind == b.kind && (a.x - b.x).abs() < pending.step * 1e-3);
    points
}

#[cfg(test)]
mod tests {
    use formalith_session::formalith::field::real::numeric::Numeric;

    use super::*;
    use crate::{
        gpu::tests::device,
        shader::{PRELUDE, function, tests::compile},
    };

    fn analyzer() -> Option<Analyzer> {
        let Some((adapter, device, queue)) = device() else {
            eprintln!("No GPU, skipped");
            return None;
        };
        Analyzer::new(&adapter, device, queue, Arc::new(|| {}))
    }

    /// Evaluate `expr` at `(x, 0.5)` for each `x` in `xs` on the GPU, with the parameters `a = 2`, `b = -3`.
    fn evaluate(
        (_, device, queue): &(wgpu::Adapter, wgpu::Device, wgpu::Queue),
        expr: &Numeric,
        xs: &[f32],
    ) -> Vec<f32> {
        let source = format!(
            "{PRELUDE}
{}
@group(0) @binding(0) var<storage, read> xs: array<f32>;
@group(0) @binding(1) var<storage, read_write> ys: array<f32>;
@group(0) @binding(2) var<storage, read> params: array<f32>;
fn param(i: u32) -> f32 {{
    return params[i];
}}
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {{
    if id.x < arrayLength(&xs) {{
        ys[id.x] = F(xs[id.x], 0.5) + 0.0 * params[0];
    }}
}}",
            function(expr, "F", 0)
        );
        let module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: None,
            source: wgpu::ShaderSource::Wgsl(source.into()),
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: None,
            layout: None,
            module: &module,
            entry_point: Some("main"),
            compilation_options: wgpu::PipelineCompilationOptions::default(),
            cache: None,
        });
        let size = (xs.len() * 4) as u64;
        let init = |contents: &[u8]| {
            device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: None,
                contents,
                usage: wgpu::BufferUsages::STORAGE,
            })
        };
        let inputs = init(&bytes(xs));
        let params = init(&bytes(&[2., -3.]));
        let outputs = device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let staging = device.create_buffer(&wgpu::BufferDescriptor {
            label: None,
            size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &pipeline.get_bind_group_layout(0),
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: inputs.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: outputs.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: params.as_entire_binding(),
                },
            ],
        });
        let mut encoder = device.create_command_encoder(&wgpu::CommandEncoderDescriptor::default());
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor::default());
            pass.set_pipeline(&pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups((xs.len() as u32).div_ceil(64), 1, 1);
        }
        encoder.copy_buffer_to_buffer(&outputs, 0, &staging, 0, size);
        queue.submit([encoder.finish()]);
        staging.map_async(wgpu::MapMode::Read, .., |result| result.expect("Mapped"));
        let _ = device.poll(wgpu::PollType::wait_indefinitely());
        let data = staging.get_mapped_range(..).expect("Mapped");
        data.chunks_exact(4)
            .map(|chunk| f32::from_le_bytes(chunk.try_into().expect("4 bytes")))
            .collect()
    }

    #[test]
    fn test_functions() {
        let Some(device) = device() else {
            eprintln!("No GPU, skipped");
            return;
        };
        let xs: Vec<f32> = vec![
            -7.5, -3.2, -2., -1., -0.7, -0.3, -1e-4, 0., 1e-4, 0.25, 0.5, 0.9, 1., 1.5, 2., 2.7,
            3., 4.2, 6.5, 12., 30.,
        ];
        let cases = [
            "x^2 + 3*x*y - 1/2",
            "sqrt(x)",
            "x^(1/3)",
            "x^(2/3)",
            "x^(-2/5)",
            "x^-3",
            "x^y",
            "2^x",
            "(-2)^x",
            "a*x + b",
            "exp(x)",
            "ln(x)",
            "sin(x) + cos(x)",
            "tan(x)",
            "asin(x)",
            "acos(x)",
            "atan(x)",
            "sinh(x)",
            "cosh(x)",
            "tanh(x)",
            "asinh(x)",
            "acosh(x)",
            "atanh(x)",
            "abs(x)",
            "sign(x)",
            "floor(x)",
            "ceil(x)",
            "min(x, y, a)",
            "max(x, b)",
            "erf(x)",
            "erfi(x)",
            "gamma(x)",
            "factorial(x)",
            "lambertw(x)",
            "lambertw(x, -1)",
            "polygamma(0, x)",
            "polygamma(1, x)",
            "polygamma(2, x)",
            "zeta(x)",
            "binomial(x, 3)",
            "binomial(5, x)",
            "piecewise(x < 0, -x, x <= 1, x^2, x > 2, a, x >= 3, b, 1)",
            "piecewise(x < 0, -x, x > 1, x^2)",
            "integrate(exp(x^3), x)",
        ];
        for input in cases {
            let expr = compile(input);
            let got = evaluate(&device, &expr, &xs);
            for (x, got) in xs.iter().zip(got) {
                let expected = expr.eval(&[f64::from(*x), 0.5, 2., -3.]);
                let got = f64::from(got);
                let ok = if expected.is_nan() {
                    got.is_nan()
                } else if expected.is_infinite() || expected.abs() > 1e38 {
                    got.is_infinite() && got.signum() == expected.signum() || got.abs() > 1e30
                } else {
                    (got - expected).abs() <= 2e-4 * expected.abs().max(1.)
                };
                assert!(ok, "{input} at {x}: {got} != {expected}");
            }
        }
    }

    fn find(points: &[Point], kind: Kind) -> Vec<f64> {
        points
            .iter()
            .filter(|point| point.kind == kind)
            .map(|point| point.x)
            .collect()
    }

    fn assert_close(a: &[f64], b: &[f64]) {
        assert_eq!(a.len(), b.len(), "{a:?} != {b:?}");
        for (a, b) in a.iter().zip(b) {
            assert!((a - b).abs() < 1e-4, "{a:?} != {b:?}");
        }
    }

    /// The points of `f` (with the derivative `derivative`) and its intersections with `others` on `[a, b]`.
    fn search(
        analyzer: &mut Analyzer,
        f: &str,
        derivative: Option<&str>,
        others: &[&str],
        a: f64,
        b: f64,
    ) -> Vec<Point> {
        let f = compile(f);
        let derivative = derivative.map(compile);
        let others: Vec<Numeric> = others.iter().map(|g| compile(g)).collect();
        let request = Request {
            curves: AnalysisCurves {
                f: (&f, 0),
                derivative: derivative.as_ref(),
                others: others.iter().map(|g| (g, 0)).collect(),
            },
            params: vec![],
            a,
            b,
            samples: 200,
        };
        assert!(analyzer.start(&request));
        analyzer.wait()
    }

    #[cfg(feature = "profile")]
    #[test]
    fn test_timestamps() {
        let Some((adapter, ..)) = device() else {
            eprintln!("No GPU, skipped");
            return;
        };
        let features = adapter.features() & wgpu::Features::TIMESTAMP_QUERY;
        if features.is_empty() {
            eprintln!("No timestamps, skipped");
            return;
        }
        let descriptor = wgpu::DeviceDescriptor {
            required_features: features,
            ..Default::default()
        };
        let (device, queue) = pollster::block_on(adapter.request_device(&descriptor)).unwrap();
        let mut analyzer = Analyzer::new(&adapter, device, queue, Arc::new(|| {})).unwrap();
        let _recording = crate::profiler::tests::RECORDING
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        crate::profiler::start();
        search(&mut analyzer, "x^2 - 1", Some("2*x"), &[], -3., 3.);
        let lanes = crate::profiler::stop(false);
        let lane = lanes
            .iter()
            .find(|lane| lane.name == super::super::timer::ANALYSIS)
            .expect("The passes are timed");
        let names: Vec<&str> = lane
            .frames
            .iter()
            .map(|frame| frame.name.as_str())
            .collect();
        assert_eq!(names, ["sample", "refine"]);
        assert!(lane.frames[0].start_ns <= lane.frames[0].end_ns);
        assert!(lane.frames[0].end_ns <= lane.frames[1].start_ns);
        assert!(lane.frames[1].start_ns <= lane.frames[1].end_ns);
    }

    #[test]
    fn test_remarkable_points() {
        let Some(mut analyzer) = analyzer() else {
            return;
        };
        // `x^3 - x` has roots -1, 0, 1 and extrema at `±1/sqrt(3)`
        let e = 1. / 3f64.sqrt();
        for derivative in [Some("3*x^2 - 1"), None] {
            let points = search(&mut analyzer, "x^3 - x", derivative, &[], -2., 2.3);
            assert_close(&find(&points, Kind::Root), &[-1., 0., 1.]);
            assert_close(&find(&points, Kind::Maximum), &[-e]);
            assert_close(&find(&points, Kind::Minimum), &[e]);
        }
        // Touching root, and no root at the pole of `1/x`
        let points = search(&mut analyzer, "(x - 0.3)^2", None, &[], -2., 2.);
        assert_close(&find(&points, Kind::Root), &[0.3]);
        assert_close(&find(&points, Kind::Minimum), &[0.3]);
        let points = search(&mut analyzer, "1/x", None, &[], -2., 2.1);
        assert!(points.is_empty(), "{points:?}");
    }

    #[test]
    fn test_intersections() {
        let Some(mut analyzer) = analyzer() else {
            return;
        };
        let points = search(&mut analyzer, "x^2", None, &["x + 2", "x"], -5., 5.5);
        assert_close(&find(&points, Kind::Intersection), &[-1., 0., 1., 2.]);
        let at = |x: f64| points.iter().find(|point| (point.x - x).abs() < 1e-4);
        assert!((at(2.).expect("Intersection at 2").y - 4.).abs() < 1e-4);
    }
}
