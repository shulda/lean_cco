import CCO.FullPhaseLift.Marked.Model
import CCO.FullPhaseLift.Full.ShadowNormalization

/-! Preserve the strict semantic helper in the ACTUAL constructed full
marked model. The certified RAW source interface is then recovered by the
proved Shadow normalization theorem, with actual binary homogeneity derived. -/
universe m
namespace CCO.FullPhaseLift.Marked
open Canonical APCharacter Full BinarySource
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable (hsym : SameSortSymmetric U) (mask : MaskData (source U hsym))
variable (sap : StrongAmalgamation U (source U hsym) (Canonical.pack U) mask)

private def oldPartial {n : ℕ} (D : Partial (addBit L) (Fin n)) : Partial L (Fin n) :=
  fun r xs => D r.succ xs

private def oldFactor {n : ℕ} {D : Partial (addBit L) (Fin n)}
    (e : Canonical.Iso (FullReduct.oldTable U (source U hsym) (Canonical.pack U) mask sap) U)
    (F : FrozenFactor (FullReduct.expandedTable U (source U hsym) (Canonical.pack U) mask sap) D) :
    FrozenFactor U (oldPartial D) where
  size := F.size
  inclusion := F.inclusion
  table := Marked.oldTable F.table
  age := ⟨e.toEmbedding.comp (embeddingOf F.age.some.point F.age.some.injective
    (fun r xs => embedding_read F.age.some r.succ xs))⟩
  agrees r xs := F.agrees r.succ xs

/-- Every strict chosen marked pair target lifts to a FULL marked class
object with exactly those bits. All higher declarations remain on the same
induced frozen factors, so no later-stage completion provider is assumed. -/
theorem strictSupportNormal (normal : Full.StrictSupportNormal U)
    (e : Canonical.Iso (FullReduct.oldTable U (source U hsym) (Canonical.pack U) mask sap) U) :
    Full.StrictSupportNormal
      (FullReduct.expandedTable U (source U hsym) (Canonical.pack U) mask sap) := by
  let S := source U hsym
  let E := FullReduct.expandedTable U S (Canonical.pack U) mask sap
  let bit := FullReduct.bits U S (Canonical.pack U) mask sap
  intro n D k F _consistent covered pair
  obtain ⟨p,hp,_⟩ := pair
  let Dold := oldPartial D
  let Fold : Fin k → FrozenFactor U Dold := fun i => oldFactor U hsym mask sap e (F i)
  let pold : Fin n ↪ M := p.trans e.point.toEmbedding
  have oldcovered : HigherCovered Fold := by
    intro r xs b hd hs
    change ∃ i, Set.range xs ⊆ Set.range (F i).inclusion
    exact covered r.succ xs b hd hs
  have oldlow : LowRealizes U Dold pold := by
    intro r xs b hs hd
    exact (embedding_read e.toEmbedding r (p ∘ xs)).trans (hp r.succ xs b hs hd)
  obtain ⟨q,hq,hfix,hLow⟩ := lift_chosen_pairs_by_factors_finite U normal
    Dold k Fold oldcovered pold oldlow
  have plegal := model_legal U S (Canonical.pack U) mask sap (actualPairFaithful U hsym) e p
  have names := names_of_lowEquivalent U hsym q pold hLow
  have qlegal : Age.Legal S mask (Canonical.pack U ∘ q) (bit ∘ p) := by
    apply Age.legal_of_names S mask plegal
    exact names.2
  let T := pullback U q
  let qfull : Canonical.Embedding (table T (bit ∘ p)) E :=
    classEmbedding U S (Canonical.pack U) mask sap T (bit ∘ p)
      ⟨embeddingOf q q.injective (fun _ _ => rfl),qlegal⟩
  have hr : Realizes E D qfull.point := by
    intro r
    refine Fin.cases ?_ (fun s => ?_) r
    · intro xs b hd
      have hs : SmallSupport xs := by
        intro i j k
        exact Or.inl (congrArg xs (Subsingleton.elim (show Fin 1 from i) (show Fin 1 from j)))
      have hbit := hp 0 xs b hs hd
      have hEq : table T (bit ∘ p) 0 xs = E 0 (p ∘ xs) := by
        have he := congrFun (congrFun (table_oldTable_bits E) 0) (p ∘ xs)
        exact he
      exact (embedding_read qfull 0 xs).trans (hEq.trans hbit)
    · intro xs b hd
      exact (embedding_read qfull s.succ xs).trans (hq s xs b hd)
  refine ⟨qfull.point,hr,?_⟩
  intro i
  exact (F i).fixedBy_of_realizes qfull.point hr
    (qfull.injective.comp (F i).inclusion.injective)

end
end CCO.FullPhaseLift.Marked
