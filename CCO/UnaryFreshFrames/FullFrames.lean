import CCO.UnaryFreshFrames.Frames
import CCO.UnaryFreshFrames.SAPAlgebraicity

/-! The explanatory source corollary uses FULL Aut. The actual-subgroup
frame theorem remains separate and requires its own real-base orbit premise. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

theorem top_orbitOver_eq (A : Set V) (x : V) :
    orbitOver (⊤ : Subgroup H.Aut) A x = orbitOver H.Aut A x := by
  ext y
  rw [mem_orbitOver_iff, mem_orbitOver_iff]
  constructor
  · rintro ⟨g, hg, hgy⟩
    exact ⟨g.val, hg, hgy⟩
  · rintro ⟨g, hg, hgy⟩
    exact ⟨⟨g, Subgroup.mem_top g⟩, hg, hgy⟩

def FullRealBaseOrbits (R : Set V) : Prop :=
  ∀ D : Set V, D.Finite → D ⊆ R → ∀ x, x ∉ H.closure D →
    (orbitOver H.Aut D x).Infinite

theorem full_infiniteClosedOrbits_of_frames (hfin : H.LocallyFinite)
    {R : Set V} (hFrames : H.FreshFrames R) (hReal : H.FullRealBaseOrbits R) :
    H.InfiniteClosedOrbits H.Aut := by
  have hTopReal : H.RealBaseOrbits (⊤ : Subgroup H.Aut) R := by
    intro D hD hDR x hx
    rw [H.top_orbitOver_eq]
    exact hReal D hD hDR x hx
  have ht := H.infiniteClosedOrbits_of_frames (⊤ : Subgroup H.Aut) hfin hFrames hTopReal
  intro A hA hc x hx
  rw [← H.top_orbitOver_eq]
  exact ht A hA hc x hx

theorem full_real_orbits_of_acl {R : Set V}
    (h : ∀ D : Set V, D.Finite → D ⊆ R → Acl H.Aut D = H.closure D) :
    H.FullRealBaseOrbits R := by
  intro D hD hDR x hx hf
  apply hx
  exact h D hD hDR ▸ hf

theorem frames_iff_full_orbits (hfin : H.LocallyFinite) (real : L.Sorts → Prop)
    (hGen : H.RealGenerating (H.realSet real))
    (hReal : H.FullRealBaseOrbits (H.realSet real)) :
    H.FreshFrames (H.realSet real) ↔ H.InfiniteClosedOrbits H.Aut := by
  have hTopReal : H.RealBaseOrbits (⊤ : Subgroup H.Aut) (H.realSet real) := by
    intro D hD hDR x hx
    rw [H.top_orbitOver_eq]
    exact hReal D hD hDR x hx
  have hTop := H.fresh_frames_iff (⊤ : Subgroup H.Aut) hfin hGen
    (H.realSet_invariant _ real) hTopReal
  refine hTop.trans ⟨?_, ?_⟩
  · intro ht A hA hc x hx
    rw [← H.top_orbitOver_eq]
    exact ht A hA hc x hx
  · intro ht A hA hc x hx
    rw [H.top_orbitOver_eq]
    exact ht A hA hc x hx

/-- `rem:typed-fresh-frame-iff-sap`, expanded internally rather than assuming
the hereditary criterion. Every finite hidden base is covered. -/
theorem fresh_frames_hidden_acl_sap [Countable V] (hfin : H.LocallyFinite)
    (hom : H.Homogeneous) (real : L.Sorts → Prop)
    (hGen : H.RealGenerating (H.realSet real))
    (hReal : ∀ D : Set V, D.Finite → D ⊆ H.realSet real →
      Acl H.Aut D = H.closure D) :
    (H.FreshFrames (H.realSet real) ↔
      ∀ T : Set V, T.Finite → Acl H.Aut T = H.closure T) ∧
    (H.FreshFrames (H.realSet real) ↔ H.AgeSAP) := by
  have hf := H.frames_iff_full_orbits hfin real hGen (H.full_real_orbits_of_acl hReal)
  exact ⟨hf.trans (H.infiniteClosedOrbits_iff_full_acl hfin),
    hf.trans (H.ageSAP_iff_infiniteClosedOrbits hfin hom).symm⟩

end CCO.UnaryFreshFrames.Structure
