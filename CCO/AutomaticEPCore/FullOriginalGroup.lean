import CCO.AutomaticEPCore.FunctionalTypes
import CCO.TerminalPowers.FullSource

/-! The presenting original homogeneous group has the SAME centralizer
as the full actual old automorphism group. Thus the source functional
group is literally all Aut(M)-equivariant real permutations; no assumed
faithfulness, group section or marked automorphism is introduced. -/

universe u v w r
namespace CCO.AutomaticEPCore

open CCO.ParityHasse.Original CCO.TerminalPowers

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i : ι}

include H

/-- The actual old orbital graph of a functional map is preserved by
EVERY old colour automorphism, hence the map commutes with full Aut(M). -/
theorem original_functional_full_equivariant
    (h : OriginalFunctionalGroup G (X i)) (g : FullAut S) (x : X i) :
    h.val (g • x) = g • h.val x := by
  obtain ⟨x₀⟩ := S.nonemptySort i
  apply (original_functional_colour_iff S H h x₀ _ _).mp
  calc
    S.colour (g • x) (g • h.val x) = S.colour x (h.val x) :=
      fullAut_colour S g i i x (h.val x)
    _ = S.colour x₀ (h.val x₀) :=
      (original_functional_colour_iff S H h x₀ x (h.val x)).mpr rfl

/-- Exact equality of the two permutation subgroups: the source uses all
full-old-Aut equivariant maps, even when its source data present a smaller
homogeneous group. Logical identity and all nonidentity graphs are retained. -/
theorem original_functional_group_eq_full :
    originalFunctionalGroup G (X i) =
      originalFunctionalGroup (FullAut S) (X i) := by
  ext h
  constructor
  · intro hh
    exact original_functional_full_equivariant S H ⟨h,hh⟩
  · intro hh g x
    exact hh (motionAut S H g) x

/-- The full original group itself has the genuine original finite
homogeneity provider; there is no further full-Aut hypothesis on a caller. -/
theorem original_full_homogeneous : HomogeneousSource S (FullAut S) :=
  full_homogeneous S H

end CCO.AutomaticEPCore
