import CCO.RawExact.ExactCalculusSource
import CCO.RawExact.ActualOrbitalExact
import CCO.ParityHasse.Original.OrbitalAlgebra

/-! Genuine equality-inclusive exact relations and the accepted RAW calculus.
The source instances use homogeneity and semantic CCO, with no SAP or Hasse
hypothesis. The three-domain theorem below is support Helly, not ball Helly. -/
universe u v w t
namespace CCO.ParityHasse.Relative
open Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

/-- Semantic exactness always has a genuine finite RAW presentation and pair. -/
def Exact (R : X i → X i → Prop) : Prop :=
  ∃ D : RawExact.NonemptyExact S i i, RawExact.evaluate S D.words = R

theorem Exact.nonempty {R : X i → X i → Prop} (h : Exact S R) : ∃ x y, R x y := by
  obtain ⟨D, rfl⟩ := h
  exact D.nonempty

variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include H in
 theorem Exact.colourInvariant {R : X i → X i → Prop} (h : Exact S R) :
    ColourInvariant S i R := by
  obtain ⟨D, rfl⟩ := h
  exact groupInvariant_colourInvariant S H
    (RawExact.presentation_invariant_of_homogeneous S H D.words)

include H cco in
 theorem exact_comp {R T : X i → X i → Prop} (hR : Exact S R) (hT : Exact S T) :
    Exact S (RawSymmetric.compose R T) := by
  obtain ⟨D, rfl⟩ := hR
  obtain ⟨F, rfl⟩ := hT
  refine ⟨⟨RawExact.pairWords S D.words F.words,
    RawExact.pairWords_nonempty_of_homogeneous S H D F⟩, ?_⟩
  exact (RawExact.convolution_of_CCO S H cco D F).symm

 theorem exact_meet {R T : X i → X i → Prop} (hR : Exact S R) (hT : Exact S T)
    (hne : ∃ x y, R x y ∧ T x y) : Exact S (fun x y => R x y ∧ T x y) := by
  obtain ⟨D, rfl⟩ := hR
  obtain ⟨F, rfl⟩ := hT
  exact ⟨RawExact.NonemptyExact.meet S D F hne, RawExact.evaluate_append S D.words F.words⟩

 theorem exact_identity : Exact S (fun x y : X i => x = y) := by
  exact ⟨RawExact.exactIdentityAtom S i, RawExact.exactIdentityAtom_relation S i⟩

 theorem exact_top : Exact S (fun _ _ : X i => True) :=
  ⟨RawExact.NonemptyExact.top S i i, RawExact.evaluate_nil S⟩

 theorem exact_actual_colour (x y : X i) : Exact S (S.rawAtomRel (S.colour x y)) :=
  RawExact.actual_pair_colour_exact S x y

include H cco in
/-- The exact three-domain support theorem; duplicate domains are allowed. -/
theorem exact_three_helly {A B T : X i → X i → Prop}
    (hA : Exact S A) (hB : Exact S B) (hT : Exact S T)
    (hAB : ∃ x y, A x y ∧ B x y)
    (hAT : ∃ x y, A x y ∧ T x y)
    (hBT : ∃ x y, B x y ∧ T x y) :
    ∃ x y, A x y ∧ B x y ∧ T x y := by
  obtain ⟨DA, rfl⟩ := hA
  obtain ⟨DB, rfl⟩ := hB
  obtain ⟨DT, rfl⟩ := hT
  have self (D : RawExact.NonemptyExact S i i) : ∃ x y, RawExact.evaluate S D.words x y ∧ RawExact.evaluate S D.words x y := by
    obtain ⟨x,y,h⟩ := D.nonempty
    exact ⟨x,y,h,h⟩
  have pair : ∀ d ∈ [DA, DB, DT], ∀ e ∈ [DA, DB, DT],
      d ≠ e → ∃ x y, RawExact.evaluate S d.words x y ∧ RawExact.evaluate S e.words x y := by
    intro d hd e he _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd he
    rcases hd with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl
    · exact self _
    · exact hAB
    · exact hAT
    · obtain ⟨x,y,h,k⟩ := hAB; exact ⟨x,y,k,h⟩
    · exact self _
    · exact hBT
    · obtain ⟨x,y,h,k⟩ := hAT; exact ⟨x,y,k,h⟩
    · obtain ⟨x,y,h,k⟩ := hBT; exact ⟨x,y,k,h⟩
    · exact self _
  obtain ⟨x,y,h⟩ := RawExact.exactMenuHelly_of_CCO S H cco [DA, DB, DT] pair
  exact ⟨x,y,h DA (by simp),h DB (by simp),h DT (by simp)⟩

end CCO.ParityHasse.Relative
