import CCO.FullPhaseLift.Marked.Inheritance

/-! Pull the ENTIRE constructed full marked model back along its proved
old FULL isomorphism. This produces a homogeneous expansion on the original
carrier; it is not an assertion about the unrelated canonical B047 mark. -/
universe m n
namespace CCO.FullPhaseLift.Marked
open Canonical APCharacter Full BinarySource
noncomputable section

/-- The full completion interface transports along a true all-arity
isomorphism. No binary isomorphism is used for any higher relation. -/
theorem strictSupportNormal_of_iso {L : Signature} {M : Type m} {N : Type n}
    {U : BoolTable L M} {V : BoolTable L N} (e : Canonical.Iso V U)
    (normal : Full.StrictSupportNormal U) : Full.StrictSupportNormal V := by
  intro a D k F consistent covered pair
  let F' : Fin k → FrozenFactor U D := fun i => {
    size := (F i).size
    inclusion := (F i).inclusion
    table := (F i).table
    age := ⟨e.toEmbedding.comp (F i).age.some⟩
    agrees := (F i).agrees }
  have hc : Consistent U D := by
    intro b hb j
    obtain ⟨p,hp⟩ := consistent b hb j
    refine ⟨p.trans e.point.toEmbedding,?_⟩
    intro r xs c hd
    exact (embedding_read e.toEmbedding r (p ∘ xs)).trans (hp r xs c hd)
  have hcov : HigherCovered F' := by
    intro r xs b hd hs
    exact covered r xs b hd hs
  obtain ⟨p,hp,_⟩ := pair
  have hpair : PairCompletion U D F' := by
    apply PairCompletion.of_actual F' (p.trans e.point.toEmbedding)
    intro r xs b hs hd
    exact (embedding_read e.toEmbedding r (p ∘ xs)).trans (hp r xs b hs hd)
  obtain ⟨q,hq,hfix⟩ := normal a D k F' hc hcov hpair
  let f : Fin a → N := e.point.symm ∘ q
  have hf : Realizes V D f := by
    intro r xs b hd
    exact (embedding_read e.symm.toEmbedding r (q ∘ xs)).trans (hq r xs b hd)
  refine ⟨f,hf,?_⟩
  intro i
  apply (F i).fixedBy_of_realizes f hf
  exact e.point.symm.injective.comp (hfix i).1

variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type*} {X : ι → Type*} (S : AtomicSource ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S)
variable (sap : StrongAmalgamation U S pack mask)

/-- Actual full Fraisse bits transported through its old FULL reduct
isomorphism; every old relation entry is literally U. -/
def onOldTable
    (e : Canonical.Iso (FullReduct.oldTable U S pack mask sap) U) :
    BoolTable (addBit L) M := table U (FullReduct.bits U S pack mask sap ∘ e.point.symm)

def onOldIso
    (e : Canonical.Iso (FullReduct.oldTable U S pack mask sap) U) :
    Canonical.Iso (onOldTable U S pack mask sap e)
      (FullReduct.expandedTable U S pack mask sap) := by
  apply isoOf e.point.symm
  intro r
  refine Fin.cases ?_ (fun s => ?_) r
  · intro xs
    have h := congrFun (congrFun (table_oldTable_bits
      (FullReduct.expandedTable U S pack mask sap)) 0) (e.point.symm ∘ xs)
    exact h.symm
  · intro xs
    exact embedding_read e.symm.toEmbedding s xs

/-- Strict helper inheritance on the SAME original carrier and full
signature. The preceding native model proof supplies every completion. -/
theorem onOld_strictSupportNormal
    {S : AtomicSource (UnaryName U) (Carrier U)}
    (hsym : SameSortSymmetric U) (hS : S = source U hsym)
    (mask : MaskData S) (sap : StrongAmalgamation U S (Canonical.pack U) mask)
    (normal : Full.StrictSupportNormal U)
    (e : Canonical.Iso (FullReduct.oldTable U S (Canonical.pack U) mask sap) U) :
    Full.StrictSupportNormal (onOldTable U S (Canonical.pack U) mask sap e) := by
  subst S
  exact strictSupportNormal_of_iso (onOldIso U (source U hsym) (Canonical.pack U) mask sap e)
    (strictSupportNormal U hsym mask sap normal e)

end
end CCO.FullPhaseLift.Marked
