module

public import Unfoldings.Cap.Gnomonic

public import Unfoldings.Roof.NormalImage

/-!
# Gnomonic coordinates recover the actual supporting normals

The normalized lift of a planar slope is a unit upward normal. The two maps
are inverse on unit upward normals, identifying the cap's planar normal image
with its actual spherical normal image.
-/

@[expose] public section

noncomputable section



namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

theorem gnomonicNormal_normalSlope (f : Face) : Cap.gnomonicNormal (K.normalSlope f) = K.normal f :=
  Cap.gnomonicNormal_slope (K.normal f) (K.normal_unit f) (K.normal_upward f)

end Unfoldings.ConvexRoof
