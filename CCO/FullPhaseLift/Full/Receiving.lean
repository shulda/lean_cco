import CCO.FullPhaseLift.Full.ShadowNormalization
import CCO.FullPhaseLift.BinarySource.FullSAP
import CCO.FullPhaseLift.Canonical.Expansion

/-! Source-facing chosen-complete-pair lift. The only completion gate is
EXACT certified-shadow A03. Global injectivity is DERIVED from actual
irreflexive named canonical predicates in the definitional expansion. -/

universe v w
namespace CCO.FullPhaseLift.Full
open Canonical
noncomputable section
variable {L : Signature} {M : Type w} {V : Type v}

/-- C04: augmenting a chosen strict target adds no higher-support data;
its complete atomic shadow is its own cycle-certified source premise. -/
theorem chosen_augmentation_premises (U : BoolTable L M)
    (hsym : SameSortSymmetric U) [Finite V]
    (D : Partial L V) {m : ℕ} (F : Fin m → FrozenFactor U D)
    (covered : HigherCovered F) (p : V ↪ M) (hp : LowRealizes U D p) :
    Consistent U (augmentLow U D p) ∧
    HigherCovered (fun j => (F j).augment p hp) ∧
    Nonempty (Shadow.CertifiedPairCompletion U hsym (augmentLow U D p)
      (fun j => (F j).augment p hp)) ∧
    (∀ r xs, ¬ SmallSupport xs → augmentLow U D p r xs = D r xs) := by
  have low : LowRealizes U (augmentLow U D p) p := by
    intro r xs b hs hd
    rw [augmentLow_small U D p r xs hs] at hd
    exact Option.some.inj hd
  exact ⟨augmentLow_consistent U D p,higherCovered_augment F covered p hp,
    ⟨Shadow.CertifiedPairCompletion.of_actual U hsym _ p low⟩,
    fun r xs hs => augmentLow_high U D p r xs hs⟩

/-- C05 on the actual full canonical definitional expansion. Every
original distinct pair is guarded by its actual irreflexive name; no
point-separation or chosen-completion callback is among the assumptions.
All positive/negative frozen tuples remain induced on the SAME vertices. -/
theorem canonical_chosen_pair_lift (T : BoolTable L M)
    (hsym : SameSortSymmetric T)
    (normal : Shadow.SupportNormal (expand T) (sameSortSymmetric_expand hsym))
    [Finite V] (D : Partial (expansion L) V) (m : ℕ)
    (F : Fin m → FrozenFactor (expand T) D) (covered : HigherCovered F)
    (p : V ↪ M) (hp : LowRealizes (expand T) D p) :
    ∃ q : V ↪ M, Realizes (expand T) D q ∧
      (∀ j, (F j).FixedBy q) ∧ LowEquivalent (expand T) q p :=
  lift_chosen_pairs_finite (by
    intro x y h
    have he : twoPoint x y = ![x,y] := by
      funext i
      fin_cases i <;> rfl
    simpa only [he] using expand_separates T x y h)
    (normal.to_strict _ _) D m F covered p hp

/-- Actual full-language SAP is an OUTPUT under A02 and exact A03.
Neither full-old SAP nor binary homogeneity is supplied as a callback. -/
theorem source_full_ageSAP (U : BoolTable L M) (hsym : SameSortSymmetric U)
    (normal : Shadow.SupportNormal U hsym) (sap : AgeSAP (source U hsym)) :
    (toRelational U).AgeSAP :=
  BinarySource.actual_full_ageSAP U hsym (normal.to_strict U hsym) sap

end
end CCO.FullPhaseLift.Full
