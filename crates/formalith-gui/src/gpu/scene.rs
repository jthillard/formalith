//! Drawing of the surfaces of the 3D view ([`crate::space`]). egui's render pass has no depth buffer, so the surfaces
//! are drawn in `prepare` into textures of their own (multisampled color and depth, resolved), then copied into the
//! view by `paint`. The axes are drawn as lines in the same pass, hidden by the surfaces in front of them.

use std::{collections::HashMap, sync::Arc};

use eframe::egui_wgpu::{self, wgpu};

use super::{Shader, UNUSED_FRAMES, bytes};

/// The number of floats of the uniforms of [`crate::shader::SURFACE`].
pub const SURFACE_UNIFORMS: usize = 32 + 4 * 16;

/// The number of floats of the uniforms of [`AXES`]: the matrix, the color and the ends of the segments.
pub const AXES_UNIFORMS: usize = 16 + 4 + 4 * 6;

/// The number of quads along each side of the grid of a surface.
pub const RESOLUTION: u32 = 160;

/// The samples per pixel of the surfaces.
const SAMPLES: u32 = 4;

const DEPTH_FORMAT: wgpu::TextureFormat = wgpu::TextureFormat::Depth32Float;

/// Copies the resolved texture of the surfaces into the view.
const BLIT: &str = "
@group(0) @binding(0) var scene: texture_2d<f32>;

struct VertexOutput {
    @builtin(position) position: vec4<f32>,
    @location(0) uv: vec2<f32>,
}

@vertex
fn vs_main(@builtin(vertex_index) index: u32) -> VertexOutput {
    let p = vec2<f32>(f32((index << 1u) & 2u), f32(index & 2u));
    var out: VertexOutput;
    out.position = vec4<f32>(p * 2.0 - 1.0, 0.0, 1.0);
    out.uv = vec2<f32>(p.x, 1.0 - p.y);
    return out;
}

@fragment
fn fs_main(in: VertexOutput) -> @location(0) vec4<f32> {
    let size = vec2<f32>(textureDimensions(scene));
    let texel = min(vec2<i32>(in.uv * size), vec2<i32>(size) - 1);
    return textureLoad(scene, texel, 0);
}
";

/// Draws up to 3 segments of the box `[-1, 1]^3` in a premultiplied color.
const AXES: &str = "
struct Uniforms {
    view_proj: mat4x4<f32>,
    color: vec4<f32>,
    ends: array<vec4<f32>, 6>,
}

@group(0) @binding(0) var<uniform> u: Uniforms;

@vertex
fn vs_main(@builtin(vertex_index) index: u32) -> @builtin(position) vec4<f32> {
    return u.view_proj * vec4<f32>(u.ends[index].xyz, 1.0);
}

@fragment
fn fs_main() -> @location(0) vec4<f32> {
    return u.color;
}
";

/// The axes to draw.
pub struct AxesDraw {
    /// The uniforms of [`AXES`].
    pub uniforms: Box<[f32; AXES_UNIFORMS]>,
    /// The number of ends of segments in the uniforms, at most 6.
    pub vertices: u32,
}

/// A surface to draw.
pub struct SurfaceDraw {
    /// The identifier of the surface, which owns a uniform buffer.
    pub id: u64,
    /// Its shader ([`crate::shader::surface`]).
    pub shader: Arc<Shader>,
    /// The uniforms of the shader.
    pub uniforms: Box<[f32; SURFACE_UNIFORMS]>,
}

/// Draws the surfaces of the 3D view in the rectangle of its paint callback.
pub struct SceneCallback {
    /// The number of the frame, to drop resources unused for a while.
    pub frame: u64,
    /// The size of the rectangle in pixels.
    pub size: [u32; 2],
    /// The surfaces.
    pub surfaces: Vec<SurfaceDraw>,
    /// The axes, drawn after the surfaces.
    pub axes: Option<AxesDraw>,
}

/// The textures the surfaces are drawn into, for a size.
struct Targets {
    size: [u32; 2],
    color: wgpu::TextureView,
    depth: wgpu::TextureView,
    resolved: wgpu::TextureView,
    /// The bind group of `resolved` for the copy into the view.
    blit: wgpu::BindGroup,
}

/// The GPU resources of the 3D view, in the callback resources of the renderer.
pub(crate) struct SceneResources {
    format: wgpu::TextureFormat,
    layout: wgpu::BindGroupLayout,
    pipeline_layout: wgpu::PipelineLayout,
    blit_layout: wgpu::BindGroupLayout,
    blit_pipeline: wgpu::RenderPipeline,
    axes_pipeline: wgpu::RenderPipeline,
    axes_buffer: wgpu::Buffer,
    axes_bind_group: wgpu::BindGroup,
    /// Pipelines by shader hash, with the frame they were last used in.
    pipelines: HashMap<u64, (wgpu::RenderPipeline, u64)>,
    /// Uniform buffers by surface, with the frame they were last used in.
    surfaces: HashMap<u64, (wgpu::Buffer, wgpu::BindGroup, u64)>,
    targets: Option<Targets>,
    frame: u64,
}

/// The depth test of the scene, with `compare`.
fn depth_state(compare: wgpu::CompareFunction) -> wgpu::DepthStencilState {
    wgpu::DepthStencilState {
        format: DEPTH_FORMAT,
        depth_write_enabled: Some(true),
        depth_compare: Some(compare),
        stencil: wgpu::StencilState::default(),
        bias: wgpu::DepthBiasState::default(),
    }
}

impl SceneResources {
    pub(crate) fn new(device: &wgpu::Device, format: wgpu::TextureFormat) -> Self {
        let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("surface"),
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
            label: Some("surface"),
            bind_group_layouts: &[Some(&layout)],
            immediate_size: 0,
        });
        let blit_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("scene blit"),
            entries: &[wgpu::BindGroupLayoutEntry {
                binding: 0,
                visibility: wgpu::ShaderStages::FRAGMENT,
                ty: wgpu::BindingType::Texture {
                    sample_type: wgpu::TextureSampleType::Float { filterable: false },
                    view_dimension: wgpu::TextureViewDimension::D2,
                    multisampled: false,
                },
                count: None,
            }],
        });
        let blit_module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("scene blit"),
            source: wgpu::ShaderSource::Wgsl(BLIT.into()),
        });
        let blit_pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("scene blit"),
            bind_group_layouts: &[Some(&blit_layout)],
            immediate_size: 0,
        });
        let blit_pipeline = device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("scene blit"),
            layout: Some(&blit_pipeline_layout),
            vertex: wgpu::VertexState {
                module: &blit_module,
                entry_point: Some("vs_main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[],
            },
            primitive: wgpu::PrimitiveState::default(),
            depth_stencil: None,
            multisample: wgpu::MultisampleState::default(),
            fragment: Some(wgpu::FragmentState {
                module: &blit_module,
                entry_point: Some("fs_main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format,
                    blend: Some(wgpu::BlendState::PREMULTIPLIED_ALPHA_BLENDING),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            multiview_mask: None,
            cache: None,
        });
        let axes_module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("axes"),
            source: wgpu::ShaderSource::Wgsl(AXES.into()),
        });
        let axes_pipeline = device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("axes"),
            layout: Some(&pipeline_layout),
            vertex: wgpu::VertexState {
                module: &axes_module,
                entry_point: Some("vs_main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[],
            },
            primitive: wgpu::PrimitiveState {
                topology: wgpu::PrimitiveTopology::LineList,
                ..wgpu::PrimitiveState::default()
            },
            // `LessEqual`, so that an axis on a flat surface isn't hidden by it
            depth_stencil: Some(depth_state(wgpu::CompareFunction::LessEqual)),
            multisample: wgpu::MultisampleState {
                count: SAMPLES,
                ..wgpu::MultisampleState::default()
            },
            fragment: Some(wgpu::FragmentState {
                module: &axes_module,
                entry_point: Some("fs_main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format,
                    blend: Some(wgpu::BlendState::PREMULTIPLIED_ALPHA_BLENDING),
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            multiview_mask: None,
            cache: None,
        });
        let axes_buffer = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("axes"),
            size: (AXES_UNIFORMS * 4) as u64,
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let axes_bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("axes"),
            layout: &layout,
            entries: &[wgpu::BindGroupEntry {
                binding: 0,
                resource: axes_buffer.as_entire_binding(),
            }],
        });
        Self {
            format,
            layout,
            pipeline_layout,
            blit_layout,
            blit_pipeline,
            axes_pipeline,
            axes_buffer,
            axes_bind_group,
            pipelines: HashMap::new(),
            surfaces: HashMap::new(),
            targets: None,
            frame: 0,
        }
    }

    fn pipeline(&self, device: &wgpu::Device, shader: &Shader) -> wgpu::RenderPipeline {
        let module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("surface"),
            source: wgpu::ShaderSource::Wgsl(shader.source.as_str().into()),
        });
        device.create_render_pipeline(&wgpu::RenderPipelineDescriptor {
            label: Some("surface"),
            layout: Some(&self.pipeline_layout),
            vertex: wgpu::VertexState {
                module: &module,
                entry_point: Some("vs_main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                buffers: &[],
            },
            primitive: wgpu::PrimitiveState::default(),
            depth_stencil: Some(depth_state(wgpu::CompareFunction::Less)),
            multisample: wgpu::MultisampleState {
                count: SAMPLES,
                ..wgpu::MultisampleState::default()
            },
            fragment: Some(wgpu::FragmentState {
                module: &module,
                entry_point: Some("fs_main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                targets: &[Some(wgpu::ColorTargetState {
                    format: self.format,
                    blend: None,
                    write_mask: wgpu::ColorWrites::ALL,
                })],
            }),
            multiview_mask: None,
            cache: None,
        })
    }

    /// The textures for `size`, made again when it changed.
    fn targets(&mut self, device: &wgpu::Device, size: [u32; 2]) -> &Targets {
        if self
            .targets
            .as_ref()
            .is_none_or(|targets| targets.size != size)
        {
            let texture = |format, samples, usage| {
                device
                    .create_texture(&wgpu::TextureDescriptor {
                        label: Some("scene"),
                        size: wgpu::Extent3d {
                            width: size[0],
                            height: size[1],
                            depth_or_array_layers: 1,
                        },
                        mip_level_count: 1,
                        sample_count: samples,
                        dimension: wgpu::TextureDimension::D2,
                        format,
                        usage,
                        view_formats: &[],
                    })
                    .create_view(&wgpu::TextureViewDescriptor::default())
            };
            let attachment = wgpu::TextureUsages::RENDER_ATTACHMENT;
            let resolved = texture(
                self.format,
                1,
                attachment | wgpu::TextureUsages::TEXTURE_BINDING,
            );
            let blit = device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some("scene blit"),
                layout: &self.blit_layout,
                entries: &[wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::TextureView(&resolved),
                }],
            });
            self.targets = Some(Targets {
                size,
                color: texture(self.format, SAMPLES, attachment),
                depth: texture(DEPTH_FORMAT, SAMPLES, attachment),
                resolved,
                blit,
            });
        }
        self.targets.as_ref().expect("Made above")
    }
}

impl egui_wgpu::CallbackTrait for SceneCallback {
    fn prepare(
        &self,
        device: &wgpu::Device,
        queue: &wgpu::Queue,
        _screen_descriptor: &egui_wgpu::ScreenDescriptor,
        egui_encoder: &mut wgpu::CommandEncoder,
        callback_resources: &mut egui_wgpu::CallbackResources,
    ) -> Vec<wgpu::CommandBuffer> {
        profile_scope!("SceneCallback::prepare");
        let Some(resources) = callback_resources.get_mut::<SceneResources>() else {
            return vec![];
        };
        let frame = self.frame;
        if resources.frame != frame {
            resources.frame = frame;
            let used = |last: u64| last + UNUSED_FRAMES >= frame;
            resources.pipelines.retain(|_, (_, last)| used(*last));
            resources.surfaces.retain(|_, (_, _, last)| used(*last));
        }
        for surface in &self.surfaces {
            if !resources.pipelines.contains_key(&surface.shader.hash) {
                profile_scope!("create surface pipeline");
                let pipeline = resources.pipeline(device, &surface.shader);
                resources
                    .pipelines
                    .insert(surface.shader.hash, (pipeline, frame));
            }
            if let Some((_, last)) = resources.pipelines.get_mut(&surface.shader.hash) {
                *last = frame;
            }
            let layout = &resources.layout;
            let (buffer, _, last) = resources.surfaces.entry(surface.id).or_insert_with(|| {
                let buffer = device.create_buffer(&wgpu::BufferDescriptor {
                    label: Some("surface"),
                    size: (SURFACE_UNIFORMS * 4) as u64,
                    usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
                    mapped_at_creation: false,
                });
                let bind_group = device.create_bind_group(&wgpu::BindGroupDescriptor {
                    label: Some("surface"),
                    layout,
                    entries: &[wgpu::BindGroupEntry {
                        binding: 0,
                        resource: buffer.as_entire_binding(),
                    }],
                });
                (buffer, bind_group, frame)
            });
            *last = frame;
            queue.write_buffer(buffer, 0, &bytes(&surface.uniforms[..]));
        }
        if let Some(axes) = &self.axes {
            queue.write_buffer(&resources.axes_buffer, 0, &bytes(&axes.uniforms[..]));
        }
        let size = self.size.map(|side| side.max(1));
        resources.targets(device, size);
        let resources = &*resources;
        let targets = resources.targets.as_ref().expect("Made above");
        let mut pass = egui_encoder.begin_render_pass(&wgpu::RenderPassDescriptor {
            label: Some("scene"),
            color_attachments: &[Some(wgpu::RenderPassColorAttachment {
                view: &targets.color,
                depth_slice: None,
                resolve_target: Some(&targets.resolved),
                ops: wgpu::Operations {
                    load: wgpu::LoadOp::Clear(wgpu::Color::TRANSPARENT),
                    store: wgpu::StoreOp::Discard,
                },
            })],
            depth_stencil_attachment: Some(wgpu::RenderPassDepthStencilAttachment {
                view: &targets.depth,
                depth_ops: Some(wgpu::Operations {
                    load: wgpu::LoadOp::Clear(1.),
                    store: wgpu::StoreOp::Discard,
                }),
                stencil_ops: None,
            }),
            timestamp_writes: None,
            occlusion_query_set: None,
            multiview_mask: None,
        });
        let vertices = RESOLUTION * RESOLUTION * 6;
        for surface in &self.surfaces {
            let (Some((pipeline, _)), Some((_, bind_group, _))) = (
                resources.pipelines.get(&surface.shader.hash),
                resources.surfaces.get(&surface.id),
            ) else {
                continue;
            };
            pass.set_pipeline(pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.draw(0..vertices, 0..1);
        }
        if let Some(axes) = &self.axes {
            pass.set_pipeline(&resources.axes_pipeline);
            pass.set_bind_group(0, &resources.axes_bind_group, &[]);
            pass.draw(0..axes.vertices.min(6), 0..1);
        }
        vec![]
    }

    fn paint(
        &self,
        _info: eframe::egui::PaintCallbackInfo,
        render_pass: &mut wgpu::RenderPass<'static>,
        callback_resources: &egui_wgpu::CallbackResources,
    ) {
        let Some(resources) = callback_resources.get::<SceneResources>() else {
            return;
        };
        let Some(targets) = &resources.targets else {
            return;
        };
        render_pass.set_pipeline(&resources.blit_pipeline);
        render_pass.set_bind_group(0, &targets.blit, &[]);
        render_pass.draw(0..3, 0..1);
    }
}
