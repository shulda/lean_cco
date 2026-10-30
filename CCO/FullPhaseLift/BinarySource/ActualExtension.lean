import CCO.FullPhaseLift.BinarySource.FrozenDiagram
import CCO.FullPhaseLift.BinarySource.FrozenExtension
import CCO.FullPhaseLift.BinarySource.LowNames
import CCO.FullPhaseLift.BinarySource.ChosenPairsByFactors

/-! C07: the ACTUAL binary reduct has its finite extension property.
Freeze the entire actual FULL base, lift the chosen complete pair target
through raw A03, then align that FULL base by original homogeneity.
No binary homogeneity or full old SAP is a premise. -/

universe u
namespace CCO.FullPhaseLift.BinarySource
open Canonical Full
open APCharacter.SourceAge
noncomputable section

def baseFactor {L : Signature} {M : Type u} (U : BoolTable L M)
    {n m : ℕ} (j : Fin n ↪ Fin m) (q : Fin n ↪ M) :
    FrozenFactor U (frozenPartial U j q) where
  size := n
  inclusion := j
  table := pullback U q
  age := ⟨embeddingOf q q.injective (fun _ _ => rfl)⟩
  agrees := frozenPartial_on U j q

theorem baseFactor_covered {L : Signature} {M : Type u} (U : BoolTable L M)
    {n m : ℕ} (j : Fin n ↪ Fin m) (q : Fin n ↪ M) :
    HigherCovered (fun _ : Fin 1 => baseFactor U j q) := by
  intro r xs b hd _
  obtain ⟨ys,hys,_⟩ := frozenPartial_specified U j q r xs b hd
  refine ⟨0,?_⟩
  rintro x ⟨i,rfl⟩
  exact ⟨ys i,congrFun hys i⟩

theorem base_lowRealizes {L : Signature} {M : Type u} (U : BoolTable L M)
    (hsym : SameSortSymmetric U) {n m : ℕ} (j : Fin n ↪ Fin m)
    (p : Fin m ↪ M) (q : Fin n ↪ M)
    (names : ∀ x y, (pairTable U hsym).colour (q x) (q y) =
      (pairTable U hsym).colour (p (j x)) (p (j y))) :
    LowRealizes U (frozenPartial U j q) p := by
  intro r xs b hs hd
  obtain ⟨ys,hys,hb⟩ := frozenPartial_specified U j q r xs b hd
  have hs' : SmallSupport ys := by
    intro i k l
    have h := hs i k l
    rw [← congrFun hys i,← congrFun hys k,← congrFun hys l] at h
    rcases h with he | he | he
    · exact Or.inl (j.injective he)
    · exact Or.inr (Or.inl (j.injective he))
    · exact Or.inr (Or.inr (j.injective he))
  have he := small_truth_of_pair_names U hsym q (p ∘ j) names r ys hs'
  rw [← hys]
  exact he.symm.trans hb

/-- The only completion premise is the original signed, support-normal
frozen-factor interface A03. The full old homogeneous realization is A01. -/
theorem actual_pair_finiteExtension {L : Signature} {M : Type u}
    (U : BoolTable L M) (hsym : SameSortSymmetric U)
    (hom : (toRelational U).Homogeneous) (normal : SupportNormal U) :
    FiniteExtension (pairTable U hsym) (pairTable U hsym) := by
  apply finiteExtension_of_frozen_lift (toRelational U) hom (pairTable U hsym)
    (pairTable_invariant U hsym)
  intro n m j p q hnames
  let D := frozenPartial U j q
  let factors : Fin 1 → FrozenFactor U D := fun _ => baseFactor U j q
  obtain ⟨r,_,hfix,hlow⟩ := lift_chosen_pairs_by_factors U normal m D 1 factors
    (baseFactor_covered U j q) p (base_lowRealizes U hsym j p q hnames.2)
  have hn := names_of_lowEquivalent U hsym r p hlow
  refine ⟨r,hn.1,hn.2,?_⟩
  intro k R xs
  exact ((factors 0).fixedEmbedding r (hfix 0)).rel_iff R xs

/-- Countable back-and-forth now derives genuine homogeneity of the
actual binary source on this SAME full old carrier. -/
theorem actual_binary_homogeneous {L : Signature} {M : Type u} [Countable M]
    (U : BoolTable L M) (hsym : SameSortSymmetric U)
    (hom : (toRelational U).Homogeneous) (normal : SupportNormal U) :
    HomogeneousSource (source U hsym) (TerminalPowers.FullAut (source U hsym)) :=
  canonical_homogeneous U hsym (actual_pair_finiteExtension U hsym hom normal)

end
end CCO.FullPhaseLift.BinarySource
