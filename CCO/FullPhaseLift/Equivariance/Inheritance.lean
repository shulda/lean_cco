import CCO.FullPhaseLift.Equivariance.Marked
import CCO.FullPhaseLift.Marked.Inheritance

/-! C25: the OPTIONAL A04 restricted to supplied natural STRICT pair
targets is preserved in the actual constructed full marked model. One
completion retains all prescribed original vertex permutations at once.
No natural target or arbitrary colliding-completion equivalence is proved. -/

universe m n
namespace CCO.FullPhaseLift.Equivariance
open Canonical APCharacter Full BinarySource
noncomputable section

private theorem consistent_of_low {L : Signature} {M : Type m} {V : Type n}
    (U : BoolTable L M) (D : Partial L V) (p : V ↪ M) (hp : LowRealizes U D p) :
    Consistent U D := by
  intro k hk j
  refine ⟨j.trans p,?_⟩
  intro r xs b hd
  exact hp r (j ∘ xs) b ((smallSupport_fin hk xs).comp j) hd

private def oldPartial {L : Signature} {V : Type n}
    (D : Partial (Marked.addBit L) V) : Partial L V := fun r xs => D r.succ xs

private def oldFactor {L : Signature} {M : Type m} {N : Type n}
    {U : BoolTable L M} {E : BoolTable (Marked.addBit L) N}
    (e : Canonical.Iso (Marked.oldTable E) U) {V : Type} {D : Partial (Marked.addBit L) V}
    (F : FrozenFactor E D) : FrozenFactor U (oldPartial D) where
  size := F.size
  inclusion := F.inclusion
  table := Marked.oldTable F.table
  age := ⟨e.toEmbedding.comp (embeddingOf F.age.some.point F.age.some.injective
    (fun r xs => embedding_read F.age.some r.succ xs))⟩
  agrees r xs := F.agrees r.succ xs

/-- Exact optional natural-STRICT source gate inherited by the actual
full marked Fraisse model. Separation is the structural canonical naming
property and is discharged by that naming construction at source use. -/
theorem naturalSupportNormal {L : Signature} {M : Type m}
    (U : BoolTable L M) (hsym : SameSortSymmetric U)
    (mask : MaskData (source U hsym))
    (sap : Marked.StrongAmalgamation U (source U hsym) (Canonical.pack U) mask)
    (sep : SeparatesPoints U) (optional : NaturalSupportNormal U)
    (e : Canonical.Iso (FullReduct.oldTable U (source U hsym) (Canonical.pack U) mask sap) U) :
    NaturalSupportNormal (FullReduct.expandedTable U (source U hsym) (Canonical.pack U) mask sap) := by
  let S := source U hsym
  let E := FullReduct.expandedTable U S (Canonical.pack U) mask sap
  let bit := FullReduct.bits U S (Canonical.pack U) mask sap
  intro v D k F _consistent covered p hp natural
  let Dold := oldPartial D
  let Fold : Fin k → FrozenFactor U Dold := fun i => oldFactor e (F i)
  let pold : Fin v ↪ M := p.trans e.point.toEmbedding
  let Γ : Set (Equiv.Perm (Fin v)) :=
    {γ | PartialAuto D γ ∧ PreservesFactors F γ}
  have oldcovered : HigherCovered Fold := by
    intro r xs b hd hs
    change ∃ i, Set.range xs ⊆ Set.range (F i).inclusion
    exact covered r.succ xs b hd hs
  have oldlow : LowRealizes U Dold pold := by
    intro r xs b hs hd
    exact (embedding_read e.toEmbedding r (p ∘ xs)).trans (hp r.succ xs b hs hd)
  have hΓ : ∀ γ ∈ Γ, PartialAuto Dold γ ∧ PreservesFactors Fold γ ∧
      LowEquivalent U (pold ∘ γ) pold := by
    intro γ hγ
    refine ⟨fun r xs => hγ.1 r.succ xs,hγ.2,?_⟩
    intro r xs hs
    have hlow := natural γ hγ.1 hγ.2 r.succ xs hs
    exact (embedding_read e.toEmbedding r ((p ∘ γ) ∘ xs)).trans
      (hlow.trans (embedding_read e.toEmbedding r (p ∘ xs)).symm)
  have hbits : ∀ γ ∈ Γ, ∀ x, bit (p (γ x)) = bit (p x) := by
    intro γ hγ x
    have h := natural γ hγ.1 hγ.2 0 (fun _ => x) (fun _ _ _ => Or.inl rfl)
    exact congrArg Marked.boolBit h
  obtain ⟨q,hq,hfix,hLow,hinvariant⟩ :=
    chosen_lift U sep optional v Dold k Fold oldcovered pold oldlow Γ hΓ
  have plegal := Marked.model_legal U S (Canonical.pack U) mask sap (Marked.actualPairFaithful U hsym) e p
  have names := names_of_lowEquivalent U hsym q pold hLow
  have qlegal : Age.Legal S mask (Canonical.pack U ∘ q) (bit ∘ p) := by
    apply Age.legal_of_names S mask plegal
    exact names.2
  let T := pullback U q
  let qfull : Canonical.Embedding (Marked.table T (bit ∘ p)) E :=
    Marked.classEmbedding U S (Canonical.pack U) mask sap T (bit ∘ p)
      ⟨embeddingOf q q.injective (fun _ _ => rfl),qlegal⟩
  have hr : Realizes E D qfull.point := by
    intro r
    refine Fin.cases ?_ (fun s => ?_) r
    · intro xs b hd
      have hs : SmallSupport xs := by
        intro i j k
        exact Or.inl (congrArg xs (Subsingleton.elim (show Fin 1 from i) (show Fin 1 from j)))
      have hbit := hp 0 xs b hs hd
      have hEq : Marked.table T (bit ∘ p) 0 xs = E 0 (p ∘ xs) := by
        exact congrFun (congrFun (Marked.table_oldTable_bits E) 0) (p ∘ xs)
      exact (embedding_read qfull 0 xs).trans (hEq.trans hbit)
    · intro xs b hd
      exact (embedding_read qfull s.succ xs).trans (hq s xs b hd)
  refine ⟨qfull.point,hr,?_,?_⟩
  · intro i
    exact (F i).fixedBy_of_realizes qfull.point hr
      (qfull.injective.comp (F i).inclusion.injective)
  · intro γ hD hF r xs
    have hΓ' : γ ∈ Γ := ⟨hD,hF⟩
    have hrestored := restore_bits_invariant T (bit ∘ p) γ
      (hinvariant γ hΓ') (hbits γ hΓ')
    exact (embedding_read qfull r (γ ∘ xs)).trans
      ((hrestored r xs).trans (embedding_read qfull r xs).symm)

private def isoFactor {L : Signature} {M : Type m} {N : Type n}
    {U : BoolTable L M} {V : BoolTable L N} (e : Canonical.Iso V U)
    {A : Type} {D : Partial L A} (F : FrozenFactor V D) : FrozenFactor U D where
  size := F.size
  inclusion := F.inclusion
  table := F.table
  age := ⟨e.toEmbedding.comp F.age.some⟩
  agrees := F.agrees

/-- Transport the exact OPTIONAL natural-STRICT gate through a true FULL
old-language isomorphism, preserving every tuple and original finite
source permutation. In particular this applies to OnOldCarrier. -/
theorem naturalSupportNormal_of_fullIso {L : Signature} {M : Type m} {N : Type n}
    {U : BoolTable L M} {V : BoolTable L N} (e : Canonical.Iso V U)
    (optional : NaturalSupportNormal U) : NaturalSupportNormal V := by
  intro k D m F _consistent covered p hp natural
  let Fold : Fin m → FrozenFactor U D := fun i => isoFactor e (F i)
  let pold : Fin k ↪ M := p.trans e.point.toEmbedding
  have oldlow : LowRealizes U D pold := by
    intro r xs b hs hd
    exact (embedding_read e.toEmbedding r (p ∘ xs)).trans (hp r xs b hs hd)
  have oldnatural : NaturalPair U D Fold pold := by
    intro γ hD hF r xs hs
    have h := natural γ hD hF r xs hs
    exact (embedding_read e.toEmbedding r ((p ∘ γ) ∘ xs)).trans
      (h.trans (embedding_read e.toEmbedding r (p ∘ xs)).symm)
  have oldcovered : HigherCovered Fold := covered
  obtain ⟨q,hq,hfix,hauto⟩ := optional k D m Fold
    (consistent_of_low U D pold oldlow) oldcovered pold oldlow oldnatural
  let result : Fin k → N := e.point.symm ∘ q
  have read (r : Fin L.size) (xs : Fin (L.arity r) → Fin k) :
      V r (result ∘ xs) = U r (q ∘ xs) := iso_read e.symm r (q ∘ xs)
  refine ⟨result,?_,?_,?_⟩
  · intro r xs b hd
    exact (read r xs).trans (hq r xs b hd)
  · intro i
    refine ⟨e.point.symm.injective.comp (hfix i).1,?_⟩
    intro r xs
    exact (read r ((F i).inclusion ∘ xs)).trans ((hfix i).2 r xs)
  · intro γ hD hF r xs
    exact (read r (γ ∘ xs)).trans ((hauto γ hD hF r xs).trans (read r xs).symm)

end
end CCO.FullPhaseLift.Equivariance
