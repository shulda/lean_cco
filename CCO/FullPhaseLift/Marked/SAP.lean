import CCO.FullPhaseLift.Marked.Fraisse
import CCO.FullPhaseLift.Marked.Canonical
import CCO.FullPhaseLift.Marked.PairSAP
import CCO.FullPhaseLift.BinarySource.SpanFactors
import CCO.FullPhaseLift.BinarySource.ChosenPairsByFactors

/-! Full marked SAP is obtained by first choosing the ACTUAL strict
marked-pair amalgam and then lifting that one target with both full legs
frozen. Every higher positive/negative tuple is retained inducedly. -/
universe m
namespace CCO.FullPhaseLift.Marked
open Canonical APCharacter Full BinarySource
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable (hsym : SameSortSymmetric U) (mask : MaskData (source U hsym))

/-- The chosen-pair construction proves actual FULL marked class SAP.
The pair SAP argument is instantiated by the accepted B047 source theorem. -/
theorem strongAmalgamation (normal : SupportNormal U)
    (pairSAP : PairStrongAmalgamation (source U hsym) mask) :
    StrongAmalgamation U (source U hsym) (Canonical.pack U) mask := by
  intro A B C f g
  let S := source U hsym
  let names : PairFaithful U S (Canonical.pack U) := actualPairFaithful U hsym
  let fa := pairEmbedding U S (Canonical.pack U) mask names f
  let ga := pairEmbedding U S (Canonical.pack U) mask names g
  obtain ⟨Z,l,r,hbase,hinter⟩ := pairSAP
    (pairChart U S (Canonical.pack U) mask A)
    (pairChart U S (Canonical.pack U) mask B)
    (pairChart U S (Canonical.pack U) mask C) fa ga
  letI := (pairChart U S (Canonical.pack U) mask A).structure
  letI := (pairChart U S (Canonical.pack U) mask B).structure
  letI := (pairChart U S (Canonical.pack U) mask C).structure
  letI := Z.structure
  change (∀ x, l.toFun (f.point x) = r.toFun (g.point x)) at hbase
  change (∀ x y, l.toFun x = r.toFun y → ∃ a, f.point a = x ∧ g.point a = y) at hinter
  let j := l.toEmbedding
  let k := r.toEmbedding
  let qB : Fin B.old.size ↪ M := ⟨B.realization.point,B.realization.injective⟩
  let qC : Fin C.old.size ↪ M := ⟨C.realization.point,C.realization.injective⟩
  let target : Fin Z.size ↪ M :=
    (⟨Z.point,Z.point_injective⟩ : Fin Z.size ↪ Sigma (Carrier U)).trans (Canonical.pack U).symm.toEmbedding
  have compatible := overlap_compatible U j qB k qC f.point g.point hinter
    (fun s xs =>
      ((embedding_read B.realization s (f.point ∘ xs)).trans
        (embedding_read (oldEmbedding f) s xs)).trans
      ((embedding_read C.realization s (g.point ∘ xs)).trans
        (embedding_read (oldEmbedding g) s xs)).symm)
  let D := unionPartial U j qB k qC
  let F := spanFactors U j qB k qC compatible
  have target_point (x : Fin Z.size) : Canonical.pack U (target x) = Z.point x :=
    (Canonical.pack U).apply_symm_apply _
  have low : LowRealizes U D target := by
    apply span_lowRealizes U hsym j qB k qC target
    · intro x y
      have h := (pairEmbedding_names U S (Canonical.pack U) mask l).2 x y
      change taggedColour S (Canonical.pack U (B.realization.point x))
        (Canonical.pack U (B.realization.point y)) =
          taggedColour S (Canonical.pack U (target (l.toFun x)))
            (Canonical.pack U (target (l.toFun y)))
      rw [target_point,target_point]
      exact h.symm
    · intro x y
      have h := (pairEmbedding_names U S (Canonical.pack U) mask r).2 x y
      change taggedColour S (Canonical.pack U (C.realization.point x))
        (Canonical.pack U (C.realization.point y)) =
          taggedColour S (Canonical.pack U (target (r.toFun x)))
            (Canonical.pack U (target (r.toFun y)))
      rw [target_point,target_point]
      exact h.symm
  obtain ⟨q,hq,hfix,hLow⟩ := lift_chosen_pairs_by_factors_finite U normal D 2 F
    (spanFactors_covered U j qB k qC compatible) target low
  have hn := names_of_lowEquivalent U hsym q target hLow
  have hlegal : Age.Legal S mask (Canonical.pack U ∘ q) Z.bits := by
    apply Age.legal_of_names S mask Z.legal
    intro x y
    have h := hn.2 x y
    change taggedColour S (Canonical.pack U (q x)) (Canonical.pack U (q y)) =
      taggedColour S (Canonical.pack U (target x)) (Canonical.pack U (target y)) at h
    rw [target_point,target_point] at h
    exact h
  let final : Chart U S (Canonical.pack U) mask :=
    ⟨⟨Z.size,pullback U q,⟨embeddingOf q q.injective (fun _ _ => rfl)⟩⟩,
      Z.bits,⟨embeddingOf q q.injective (fun _ _ => rfl),hlegal⟩⟩
  let hL : Canonical.Embedding B.old.full final.old.full :=
    embeddingOf j j.injective (by
      intro s xs
      have h := (hfix (0 : Fin 2)).2 s xs
      exact h.trans (embedding_read B.realization s xs))
  let hR : Canonical.Embedding C.old.full final.old.full :=
    embeddingOf k k.injective (by
      intro s xs
      have h := (hfix (1 : Fin 2)).2 s xs
      exact h.trans (embedding_read C.realization s xs))
  let left : B ⟶ final := embedding hL (fun x =>
    (pairEmbedding_names U S (Canonical.pack U) mask l).1 x |>.2)
  let right : C ⟶ final := embedding hR (fun x =>
    (pairEmbedding_names U S (Canonical.pack U) mask r).1 x |>.2)
  exact ⟨final,left,right,hbase,hinter⟩

end
end CCO.FullPhaseLift.Marked
