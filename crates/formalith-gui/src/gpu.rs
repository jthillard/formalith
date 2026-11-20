//! Drawing of graphs on the GPU: a paint callback runs the shader of a graph ([`crate::shader::render`]) over the
//! whole plot, with its view, colors and parameters as uniforms.

pub mod analysis;
#[cfg(feature = "profile")]
pub mod timer;

use std::{
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
    sync::Arc,
};

use eframe::egui_wgpu::{self, wgpu};

/// The WGSL source of a shader, identified by its hash.
pub struct Shader {
    /// The hash of the source.
    pub hash: u64,
    /// The source.
    pub source: String,
}

impl Shader {
    /// The shader of `source`.
    #[must_use]
    pub fn new(source: String) -> Arc<Self> {
        let mut hasher = DefaultHasher::new();
        source.hash(&mut hasher);
        Arc::new(Self {
            hash: hasher.finish(),
            source,
        })
    }
}

/// The number of floats of the uniforms of [`crate::shader::RENDER`].
pub const UNIFORMS: usize = 20 + 4 * 16;

/// The bytes of floats, as written in buffers.
#[must_use]
pub fn bytes(values: &[f32]) -> Vec<u8> {
    values
        .iter()
        .flat_map(|value| value.to_le_bytes())
        .collect()
}

/// Frames after which unused pipelines and buffers are dropped.
const UNUSED_FRAMES: u64 = 120;

/// The GPU resources of the graphs, in the callback resources of the renderer.
pub(crate) struct Resources {
    layout: wgpu::BindGroupLayout,
    pipeline_layout: wgpu::PipelineLayout,
    format: wgpu::TextureFormat,
    /// Pipelines by shader hash, with the frame they were last used in.
    pipelines: HashMap<u64, (wgpu::RenderPipeline, u64)>,
    /// Uniform buffers by graph, with the frame they were last used in.
    graphs: HashMap<u64, (wgpu::Buffer, wgpu::BindGroup, u64)>,
    frame: u64,
    /// Times the graphs while the profiler records, when the GPU can.
    #[cfg(feature = "profile")]
    timer: Option<timer::RenderTimer>,
}

/// Prepare the renderer of `render_state` to draw graphs, returning whether colors must be given in linear space.
pub fn install(render_state: &egui_wgpu::RenderState) -> bool {
    let format = render_state.target_format;
    #[allow(unused_mut)]
    let mut resources = Resources::new(&render_state.device, format);
    #[cfg(feature = "profile")]
    {
        resources.timer = timer::RenderTimer::new(&render_state.device, &render_state.queue);
    }
    render_state
        .renderer
        .write()
        .callback_resources
        .insert(resources);
    format.is_srgb()
}

/// Draws a graph in the rectangle of its paint callback.
pub struct GraphCallback {
    /// The identifier of the graph, which owns a uniform buffer.
    pub id: u64,
    /// The number of the frame, to drop resources unused for a while.
    pub frame: u64,
    /// The shader of the graph.
    pub shader: Arc<Shader>,
    /// The uniforms of the shader.
    pub uniforms: Box<[f32; UNIFORMS]>,
    /// The name of the graph, shown by the profiler.
    #[cfg(feature = "profile")]
    pub label: String,
}

impl Resources {
    pub(crate) fn new(device: &wgpu::Device, format: wgpu::TextureFormat) -> Self {
        let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("graph"),
            entries: &[wgpu::BindGroupLayoutEntry {
                binding: 0,
                visibility: wgpu::ShaderStages::VERTEX_FRAGMENT,
                ty: wgpu::BindingType::Buffer {
                    ty: wgpu::BufferBindingType::Uniform,
                    has_dynamic_offset: false,
                    min_binding_size: None,
                },
                count: None,
            }],
        });
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("graph"),
            bind_group_layouts: &[Some(&layout)],
            immediate_size: 0,
        });
        Self {
            layout,
            pipeline_layout,
            format,
            pipelines: HashMap::new(),
            graphs: HashMap::new(),
            frame: 0,
            #[cfg(feature = "profile")]
            timer: None,
        }
    }

    fn pipeline(&self, device: &wgpu::Device, shader: &Shader) -> wgpu::RenderPipeline {
        let module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("graph"),
            source: wgpu::ShaderSource::Wgsl(shader.source.as_str().into()),
        });
        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("graph"),
            layout: Some(&self.pipeline_layout),
            vertex: wgpu::VertexState {
                module: &module,
                entry_point: Some("vs_main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[],
            },
            primitive: wgpu::PrimitiveState::default(),
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            fragment: Some(wgpu::FragmentState {
                module: &module,
                entry_point: Some("fs_main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.format,
                    blend: Some(wgpu::BlendState::PREMULTIPLIED_ALPHA_BLENDING),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            multiview_mask: None,
            cache: None,
        })
    }
}

impl egui_wgpu::CallbackTrait for GraphCallback {
    fn prepare(
        &self,
        device: &wgpu::Device,
        queue: &wgpu::Queue,
        _screen_descriptor: &egui_wgpu::ScreenDescriptor,
        egui_encoder: &mut wgpu::CommandEncoder,
        callback_resources: &mut egui_wgpu::CallbackResources,
    ) -> Vec<wgpu::CommandBuffer> {
        profile_scope!("GraphCallback::prepare");
        let Some(resources) = callback_resources.get_mut::<Resources>() else {
            return vec![];
        };
        let frame = self.frame;
        if resources.frame != frame {
            resources.frame = frame;
            let used = |last: u64| last + UNUSED_FRAMES >= frame;
            resources.pipelines.retain(|_, (_, last)| used(*last));
            resources.graphs.retain(|_, (_, _, last)| used(*last));
            #[cfg(feature = "profile")]
            if let Some(timer) = &mut resources.timer {
                timer.new_frame(egui_encoder);
            }
        }
        #[cfg(feature = "profile")]
        if let Some(timer) = &mut resources.timer {
            timer.time(self.id, &self.label);
        }
        #[cfg(not(feature = "profile"))]
        let _ = egui_encoder;
        if !resources.pipelines.contains_key(&self.shader.hash) {
            profile_scope!("create graph pipeline");
            let pipeline = resources.pipeline(device, &self.shader);
            resources
                .pipelines
                .insert(self.shader.hash, (pipeline, frame));
        }
        if let Some((_, last)) = resources.pipelines.get_mut(&self.shader.hash) {
            *last = frame;
        }
        let layout = &resources.layout;
        let (buffer, _, last) = resources.graphs.entry(self.id).or_insert_with(|| {
            let buffer = device.create_buffer(&wgpu::BufferDescriptor {
                label: Some("graph"),
                size: (UNIFORMS * 4) as u64,
                usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
                mapped_at_creation: false,
            });
            let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("graph"),
                layout,
                entries: &[wgpu::BindGroupEntry {
                    binding: 0,
                    resource: buffer.as_entire_binding(),
                }],
            });
            (buffer, bind_group, frame)
        });
        *last = frame;
        queue.write_buffer(buffer, 0, &bytes(&self.uniforms[..]));
        vec![]
    }

    fn paint(
        &self,
        _info: eframe::egui::PaintCallbackInfo,
        render_pass: &mut wgpu::RenderPass<'static>,
        callback_resources: &egui_wgpu::CallbackResources,
    ) {
        let Some(resources) = callback_resources.get::<Resources>() else {
            return;
        };
        let (Some((pipeline, _)), Some((_, bind_group, _))) = (
            resources.pipelines.get(&self.shader.hash),
            resources.graphs.get(&self.id),
        ) else {
            return;
        };
        #[cfg(feature = "profile")]
        let queries = resources
            .timer
            .as_ref()
            .and_then(|timer| timer.queries(self.id));
        #[cfg(feature = "profile")]
        if let Some((query_set, index)) = queries {
            render_pass.write_timestamp(query_set, index);
        }
        render_pass.set_pipeline(pipeline);
        render_pass.set_bind_group(0, bind_group, &[]);
        render_pass.draw(0..3, 0..1);
        #[cfg(feature = "profile")]
        if let Some((query_set, index)) = queries {
            render_pass.write_timestamp(query_set, index + 1);
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::wgpu;

    /// A device, `None` without GPU.
    pub fn device() -> Option<(wgpu::Adapter, wgpu::Device, wgpu::Queue)> {
        let instance = wgpu::Instance::default();
        let adapter =
            pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions::default()))
                .ok()?;
        let (device, queue) =
            pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor::default())).ok()?;
        Some((adapter, device, queue))
    }
}
