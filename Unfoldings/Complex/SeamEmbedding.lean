module

public import Unfoldings.Complex.RelativeSeamGeometry
public import Unfoldings.Complex.SeamGraph
public import Unfoldings.Topology.FiniteEmbeddedGraph

/-! The full original internal-edge graph embeds in the uncut intrinsic surface. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

def fullCutSeam (s : C.Seam) : C.RelativeCutSeam ∅ Set.univ :=
  ⟨s, Set.mem_univ _, Set.notMem_empty _⟩

def seamMap (s : C.Seam) : C(unitInterval, C.Realization Set.univ) :=
  C.relativeSeamMap (Set.empty_subset Set.univ) (C.fullCutSeam s)

@[simp] theorem seamMap_zero (s : C.Seam) :
    C.seamMap s 0 = C.vertexPoint Set.univ (C.seamVertex s false) :=
  C.relativeSeamMap_zero _ _

@[simp] theorem seamMap_one (s : C.Seam) :
    C.seamMap s 1 = C.vertexPoint Set.univ (C.seamVertex s true) :=
  C.relativeSeamMap_one _ _

/-- The original seams are embedded arcs; isolated original vertices remain present. -/
def seamEmbedding (F : SpatialFolding C) :
    FiniteEmbeddedGraph (C.Vertex Set.univ) C.Seam (C.Realization Set.univ) where
  finite_vertices := inferInstance
  finite_edges := inferInstance
  vertex := C.vertexPoint Set.univ
  vertex_injective := C.vertexPoint_injective Set.univ
  left s := C.seamVertex s false
  right s := C.seamVertex s true
  edge := C.seamMap
  edge_zero := C.seamMap_zero
  edge_one := C.seamMap_one
  edge_injective s := (F.relativeSeamMap_injective _ (C.fullCutSeam s)).injOn
  edge_avoids_vertices s t ht hs v equal :=
    C.relativeSeamMap_avoids_vertices _ (C.fullCutSeam s) t ht hs ⟨v, equal.symm⟩
  disjoint_open_edges s r different := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ ⟨z, _hz, equal⟩
    exact C.relativeSeamMap_ne_of_ne _
      (fun same => different (congrArg Subtype.val same)) t z ht.1 ht.2 equal.symm

@[simp] theorem seamEmbedding_graph (F : SpatialFolding C) :
    (C.seamEmbedding F).graph = C.seamGraph := rfl

end Unfoldings.TriangleComplex
