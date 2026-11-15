module

public import Unfoldings.Geometry.PolygonalVertexRays
public import Unfoldings.Geometry.RadialBankInterior

/-! Original internal path rays are the exact hinge directions in radial closures. -/

@[expose] public section

namespace Unfoldings.PolygonalChain

open Filter Topology

variable {n : ℕ} (P : PolygonalChain Plane (n + 1)) (source c : Plane)

/-- The closing links cannot introduce an extra hinge direction: their only path contacts
are its two endpoints, as derived from the actual source-radius order. -/
theorem eventually_mem_radialClosure_iff_internal_rays
    (radial : P.RadialFrom source 0) (genuine : ∀ i, P.edge i ≠ 0)
    (initial : 0 < dist source (P.vertex 0)) (height : Plane →ₗ[ℝ] ℝ)
    (supported : ∀ z ∈ Set.range P.path, 0 ≤ height (z - source))
    (excluded : height (c - source) < 0)
    (outward : 0 < inner ℝ (P.vertex (Fin.last (n + 1)) - source)
      (c - P.vertex (Fin.last (n + 1)))) (k : Fin n) :
    ∀ᶠ z in 𝓝 (P.vertex k.succ.castSucc), z ∈ P.threeSegmentClosure source c ↔
      z - P.vertex k.succ.castSucc ∈
        nonnegativeRay (P.vertex k.castSucc.castSucc - P.vertex k.succ.castSucc) ∪
        nonnegativeRay (P.vertex k.succ.succ - P.vertex k.succ.castSucc) := by
  have injective : Function.Injective P.vertex := fun _ _ same =>
    (P.vertex_radius_strictMono_of_radial source radial genuine).injective
      (congrArg (dist source) same)
  have outside : P.vertex k.succ.castSucc ∉ P.radialClosingArc source c := by
    intro member
    have contacts := P.radial_bank_closing_contacts source c radial initial height
      supported excluded outward
    have endpoint := contacts.subset ⟨P.vertex_mem_path_range k.succ.castSucc, member⟩
    rcases endpoint with first | last
    · have values := congrArg Fin.val (injective first)
      simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at values
      omega
    · have values := congrArg Fin.val (injective (Set.mem_singleton_iff.mp last))
      simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last] at values
      have bound := k.isLt
      omega
  exact P.eventually_mem_path_union_iff_internal_rays source radial genuine k
    (P.radialClosingArc_closed source c) outside

end Unfoldings.PolygonalChain
