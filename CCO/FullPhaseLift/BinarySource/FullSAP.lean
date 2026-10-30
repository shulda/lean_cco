import CCO.FullPhaseLift.BinarySource.SourceSpan
import CCO.FullPhaseLift.BinarySource.SpanFactors

/-! B048 C06. Actual strong pair spans are lifted while BOTH entire full
legs remain frozen. Full old SAP is a conclusion, not an input. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace CCO.FullPhaseLift.BinarySource
open Canonical Full
noncomputable section
/-- A strong pair target on the formal union is converted into an actual
full target by freezing BOTH complete old legs, including every negative
higher tuple. Only raw support normality and pair SAP are source premises. -/
theorem full_span_amalgam {L : Signature} {M : Type v}
    (U : BoolTable L M) (hsym : SameSortSymmetric U) (normal : SupportNormal U)
    (sap : AgeSAP (Canonical.source U hsym)) {a b c : ℕ}
    (p : Fin a ↪ M) (q : Fin b ↪ M) (s : Fin c ↪ Fin a) (t : Fin c ↪ Fin b)
    (base : ∀ r (xs : Fin (L.arity r) → Fin c),
      U r (p ∘ (s ∘ xs)) = U r (q ∘ (t ∘ xs))) :
    ∃ (V : Type v) (_ : Finite V) (j : Fin a ↪ V) (k : Fin b ↪ V) (f : V ↪ M),
      (∀ x, j (s x) = k (t x)) ∧
      (∀ x y, j x = k y → ∃ z, s z = x ∧ t z = y) ∧
      (∀ r xs, U r (f ∘ j ∘ xs) = U r (p ∘ xs)) ∧
      (∀ r xs, U r (f ∘ k ∘ xs) = U r (q ∘ xs)) := by
  classical
  have hn := names_of_lowEquivalent U hsym (s.trans p) (t.trans q)
    (fun r xs _ => base r xs)
  let p' := p.trans (pack U).toEmbedding
  let q' := q.trans (pack U).toEmbedding
  obtain ⟨V,hV,j,k,target,comm,inter,hl,hr,_⟩ := strict_pair_span (Canonical.source U hsym) sap
    p' q' s t hn.2
  letI : Finite V := hV
  let targetOld := target.trans (pack U).symm.toEmbedding
  have leftNames : ∀ x y, (pairTable U hsym).colour (p x) (p y) =
      (pairTable U hsym).colour (targetOld (j x)) (targetOld (j y)) := by
    intro x y
    change taggedColour (Canonical.source U hsym) (pack U (p x)) (pack U (p y)) =
      taggedColour (Canonical.source U hsym) (pack U ((pack U).symm (target (j x))))
        (pack U ((pack U).symm (target (j y))))
    have h := hl x y
    change taggedColour (Canonical.source U hsym) (pack U (p x)) (pack U (p y)) =
      taggedColour (Canonical.source U hsym) (target (j x)) (target (j y)) at h
    simpa only [Equiv.apply_symm_apply] using h
  have rightNames : ∀ x y, (pairTable U hsym).colour (q x) (q y) =
      (pairTable U hsym).colour (targetOld (k x)) (targetOld (k y)) := by
    intro x y
    change taggedColour (Canonical.source U hsym) (pack U (q x)) (pack U (q y)) =
      taggedColour (Canonical.source U hsym) (pack U ((pack U).symm (target (k x))))
        (pack U ((pack U).symm (target (k y))))
    have h := hr x y
    change taggedColour (Canonical.source U hsym) (pack U (q x)) (pack U (q y)) =
      taggedColour (Canonical.source U hsym) (target (k x)) (target (k y)) at h
    simpa only [Equiv.apply_symm_apply] using h
  have compat := overlap_compatible U j p k q s t inter base
  let D := unionPartial U j p k q
  let factors := spanFactors U j p k q compat
  have hcov : HigherCovered factors := spanFactors_covered U j p k q compat
  have hlow : LowRealizes U D targetOld := span_lowRealizes U hsym j p k q targetOld leftNames rightNames
  obtain ⟨f,_,hfix,_⟩ := lift_chosen_pairs_by_factors_finite U normal D 2 factors hcov targetOld hlow
  refine ⟨V,inferInstance,j,k,f,comm,inter,?_,?_⟩
  · intro r xs
    exact (hfix 0).2 r xs
  · intro r xs
    exact (hfix 1).2 r xs

private theorem full_embeddings_truth_eq {L : Signature} {M : Type v} {V : Type u}
    (U : BoolTable L M) (B : Canonical.R.Structure L.language V)
    (f g : B.Embedding (toRelational U)) (r : Fin L.size) (xs : Fin (L.arity r) → V) :
    U r (f.point ∘ xs) = U r (g.point ∘ xs) := by
  have h : U r (f.point ∘ xs) = true ↔ U r (g.point ∘ xs) = true :=
    (f.rel_iff ⟨r,rfl⟩ xs).trans (g.rel_iff ⟨r,rfl⟩ xs).symm
  cases hf : U r (f.point ∘ xs) <;> cases hg : U r (g.point ∘ xs) <;> simp_all

/-- Actual FULL old-age SAP, derived from the support-normal source
interface and actual pair SAP. Both full legs and their ENTIRE common
base are preserved inducedly. There is no full-SAP or binary-homogeneity
callback among the premises. -/
theorem actual_full_ageSAP {L : Signature} {M : Type v}
    (U : BoolTable L M) (hsym : SameSortSymmetric U) (normal : SupportNormal U)
    (sap : AgeSAP (Canonical.source U hsym)) : (toRelational U).AgeSAP := by
  classical
  intro V0 V1 V2 _ _ _ B0 B1 B2 _ h1 h2 s t
  obtain ⟨f1⟩ := h1
  obtain ⟨f2⟩ := h2
  letI : Fintype V0 := Fintype.ofFinite V0
  letI : Fintype V1 := Fintype.ofFinite V1
  letI : Fintype V2 := Fintype.ofFinite V2
  let e0 := (Fintype.equivFin V0).symm
  let e1 := (Fintype.equivFin V1).symm
  let e2 := (Fintype.equivFin V2).symm
  let p : Fin (Fintype.card V1) ↪ M := ⟨f1.point ∘ e1,f1.injective.comp e1.injective⟩
  let q : Fin (Fintype.card V2) ↪ M := ⟨f2.point ∘ e2,f2.injective.comp e2.injective⟩
  let s0 : Fin (Fintype.card V0) ↪ Fin (Fintype.card V1) :=
    e0.toEmbedding.trans ((⟨s.point,s.injective⟩ : V0 ↪ V1).trans e1.symm.toEmbedding)
  let t0 : Fin (Fintype.card V0) ↪ Fin (Fintype.card V2) :=
    e0.toEmbedding.trans ((⟨t.point,t.injective⟩ : V0 ↪ V2).trans e2.symm.toEmbedding)
  have base : ∀ r (xs : Fin (L.arity r) → Fin (Fintype.card V0)),
      U r (p ∘ (s0 ∘ xs)) = U r (q ∘ (t0 ∘ xs)) := by
    intro r xs
    have hp : (p : Fin _ → M) ∘ (s0 ∘ xs) = f1.point ∘ s.point ∘ e0 ∘ xs := by
      funext i
      change f1.point (e1 (e1.symm (s.point (e0 (xs i)))) ) = _
      rw [e1.apply_symm_apply]
      rfl
    have hq : (q : Fin _ → M) ∘ (t0 ∘ xs) = f2.point ∘ t.point ∘ e0 ∘ xs := by
      funext i
      change f2.point (e2 (e2.symm (t.point (e0 (xs i)))) ) = _
      rw [e2.apply_symm_apply]
      rfl
    rw [hp,hq]
    exact full_embeddings_truth_eq U B0 (f1.comp s) (f2.comp t) r (e0 ∘ xs)
  obtain ⟨V,hV,j,k,f,comm,inter,leftTruth,rightTruth⟩ := full_span_amalgam U hsym normal sap p q s0 t0 base
  letI : Finite V := hV
  let D := toRelational (pullback U f)
  let l : B1.Embedding D := {
    point := j ∘ e1.symm
    injective := j.injective.comp e1.symm.injective
    rel_iff := by
      intro n R xs
      rcases R with ⟨r,hr⟩
      subst n
      change U r (f ∘ j ∘ e1.symm ∘ xs) = true ↔ B1.rel ⟨r,rfl⟩ xs
      rw [leftTruth r (e1.symm ∘ xs)]
      have hp : (p : Fin _ → M) ∘ (e1.symm ∘ xs) = f1.point ∘ xs := by
        funext i
        exact congrArg f1.point (e1.apply_symm_apply (xs i))
      rw [hp]
      exact f1.rel_iff ⟨r,rfl⟩ xs }
  let r : B2.Embedding D := {
    point := k ∘ e2.symm
    injective := k.injective.comp e2.symm.injective
    rel_iff := by
      intro n R xs
      rcases R with ⟨r,hr⟩
      subst n
      change U r (f ∘ k ∘ e2.symm ∘ xs) = true ↔ B2.rel ⟨r,rfl⟩ xs
      rw [rightTruth r (e2.symm ∘ xs)]
      have hq : (q : Fin _ → M) ∘ (e2.symm ∘ xs) = f2.point ∘ xs := by
        funext i
        exact congrArg f2.point (e2.apply_symm_apply (xs i))
      rw [hq]
      exact f2.rel_iff ⟨r,rfl⟩ xs }
  refine ⟨V,inferInstance,D,⟨embeddingOf f f.injective (fun _ _ => rfl)⟩,l,r,?_,?_⟩
  · intro x
    change j (e1.symm (s.point x)) = k (e2.symm (t.point x))
    have h := comm (e0.symm x)
    change j (e1.symm (s.point (e0 (e0.symm x)))) =
      k (e2.symm (t.point (e0 (e0.symm x)))) at h
    simpa only [Equiv.apply_symm_apply] using h
  · intro x y h
    obtain ⟨z,hz,hz'⟩ := inter (e1.symm x) (e2.symm y) h
    refine ⟨e0 z,?_,?_⟩
    · have h := congrArg e1 hz
      change e1 (e1.symm (s.point (e0 z))) = e1 (e1.symm x) at h
      simpa only [Equiv.apply_symm_apply] using h
    · have h := congrArg e2 hz'
      change e2 (e2.symm (t.point (e0 z))) = e2 (e2.symm y) at h
      simpa only [Equiv.apply_symm_apply] using h

end
end CCO.FullPhaseLift.BinarySource
