import CCO.APCharacter.GateSource
import CCO.RawExact.DiagramReindex

/-! An actual finite relative interval produces the reachable character
split on THIS original homogeneous source. Positive parity words, their
exactness, original maximality and the detecting character are constructed. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry
open ParityHasse.Original
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable {i : ι}

include H cco in
theorem finite_interval_character (E F : ColourEq S i) (hEF : E < F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    ∃ Y U : ColourEq S i, Y ⋖ U ∧ relativeIndex Y.val U.val a = 2 ∧
      U ≤ F ∧ ¬U ≤ E ∧ ∃ K : Kernel S i,
        Nonempty (SourcePhase S H (exactCalculus_of_homogeneous_CCO S H cco) K) := by
  classical
  have ex : ∃ x y, F x y ∧ ¬E x y := by
    by_contra hn
    apply hEF.not_ge
    intro x y hF
    exact Classical.byContradiction fun hE => hn ⟨x,y,hF,hE⟩
  obtain ⟨x,y,hF,hE⟩ := ex
  have hcne : S.colour x y ≠ none := by
    intro hc
    have hxy : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff x y).mp hc
    exact hE (hxy ▸ E.val.refl y)
  obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hcne
  have hAtom : ∀ u v, S.atomRel c u v → F u v ∧ ¬E u v := by
    intro u v huv
    have heq : S.colour x y = S.colour u v := hc.trans huv.symm
    exact ⟨(F.property x y u v heq).mp hF,fun he => hE ((E.property x y u v heq).mpr he)⟩
  have cco₀ : SemanticCCO.{u,v,0,w} S := semanticCCO_change_universe S cco
  have noOdd : ∀ x n, Odd n → ¬relPow (S.atomRel c) n x x := by
    intro x n hn hp
    obtain ⟨p,hp⟩ := (relPow_atom_iff_walk S c n x x).mp hp
    exact no_odd_orbital_walk S H cco₀ E F a c hAtom x p (by simpa only [hp] using hn)
  let Y := evenColourEq S H c
  let U := connectivityColourEq S H c
  obtain ⟨EY,EO,hEY,hEO⟩ := parity_profiles_nonempty_exact S H c
  have hY : ParityHasse.Relative.Exact S Y := by
    refine ⟨EY,?_⟩
    funext x y
    exact propext (hEY x y)
  have ho : ∀ x y, OddWalk (S.atomRel c) x y ↔ ParityHasse.Relative.odd Y.val U.val x y := by
    intro x y
    constructor
    · intro h
      exact ⟨(connectivity_eq_even_union_odd S H c x y).mpr (Or.inr h),
        fun he => even_odd_disjoint (S.atomRel c) (fun x y h => by simpa only [AtomicSource.atomRel,S.symmetricLoop] using (S.colour_swap x y c).mp h) noOdd x y ⟨he,h⟩⟩
    · rintro ⟨hU,hY⟩
      exact ((connectivity_eq_even_union_odd S H c x y).mp hU).resolve_left hY
  have hO : ParityHasse.Relative.Exact S (ParityHasse.Relative.odd Y.val U.val) := by
    refine ⟨EO,?_⟩
    funext x y
    exact propext ((hEO x y).trans (ho x y))
  have hYU : Y ≤ U := even_le_connectivity S H c
  have hTwo : relativeIndex Y.val U.val a = 2 := parity_seed_index_two S H c noOdd a
  obtain ⟨K,hK⟩ := actual_maximal_character S H
    (exactCalculus_of_homogeneous_CCO S H cco) cco Y U hY hYU hO a hTwo
  exact ⟨Y,U,parity_seed_cover S H c noOdd,hTwo,
    connectivity_le_of_atom_le S H c F (fun x y h => (hAtom x y h).1),
    connectivity_not_le_of_atom_disjoint S H c E (fun x y h => (hAtom x y h).2),K,hK⟩

end
end CCO.APCharacter
