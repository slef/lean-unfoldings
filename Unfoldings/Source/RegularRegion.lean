module

public import Unfoldings.Source.OffCutCoordinates
public import Unfoldings.Metric.RegularLocus

/-! The actual open flat retained region, with its constructed source coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {X : Type*} [MetricSpace X]

def sourceRegularRegion (source : X) : Set X :=
  {x | x ∉ sourceCutLocus source ∧ HasMetricBallChart Plane x}

theorem isOpen_sourceRegularRegion (source : X) : IsOpen (sourceRegularRegion source) :=
  (isClosed_sourceCutLocus source).isOpen_compl.inter isOpen_metric_regular_locus

/-- The closed slit set also includes singular endpoints, including unique incoming cone leaves. -/
def sourceSlitSet (source : X) : Set X :=
  sourceCutLocus source ∪ {x | ¬ HasMetricBallChart Plane x}

theorem isClosed_sourceSlitSet (source : X) : IsClosed (sourceSlitSet source) :=
  (isClosed_sourceCutLocus source).union isOpen_metric_regular_locus.isClosed_compl

theorem sourceRegularRegion_eq_compl_slitSet (source : X) :
    sourceRegularRegion source = (sourceSlitSet source)ᶜ := by
  classical
  ext x
  simp only [sourceRegularRegion, sourceSlitSet, Set.mem_compl_iff, Set.mem_union,
    Set.mem_ofPred_eq, not_or, not_not]

def regularRegionToOffCut {source : X} (x : sourceRegularRegion source) :
    ↥((sourceCutLocus source)ᶜ) := ⟨x.val, x.property.1⟩

theorem regularRegionToOffCut_isometry {source : X} :
    Isometry (regularRegionToOffCut (source := source)) := fun _ _ => rfl

namespace SourceFrame

variable [CompactSpace X] {source : X} (R : SourceFrame source)
  (exists_paths : Function.Surjective (SourcePath.target (source := source)))

def regularSourcePoint : sourceRegularRegion source :=
  ⟨source, R.source_not_mem_cutLocus, ⟨R.radius, R.positive, R.center, ⟨R.chart⟩⟩⟩

def regularCoordinates (x : sourceRegularRegion source) : Plane :=
  R.coordinatesOffCutLocus exists_paths (regularRegionToOffCut x)

theorem continuous_regularCoordinates : Continuous (R.regularCoordinates exists_paths) :=
  (R.continuous_coordinatesOffCutLocus exists_paths).comp regularRegionToOffCut_isometry.continuous

theorem regularCoordinates_injective
    (injective : Function.Injective (fun p : SourcePath source => R.coordinate p.path p.geodesic)) :
    Function.Injective (R.regularCoordinates exists_paths) :=
  (R.coordinatesOffCutLocus_injective exists_paths injective).comp
    regularRegionToOffCut_isometry.injective

end SourceFrame
end Unfoldings
