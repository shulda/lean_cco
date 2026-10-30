import CCO.FullPhaseLift.Marked.SAP
import CCO.FullPhaseLift.BinarySource.FullReduct

/-! Concrete finite full embeddings into the constructed marked model,
and literal pair-mask legality through its proved old FULL isomorphism. -/
universe u v w m
namespace CCO.FullPhaseLift.Marked
open Canonical APCharacter
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S)
variable (sap : StrongAmalgamation U S pack mask)

/-- Every legal full marked class object embeds into the ACTUAL native
Fraisse limit preserving all old tuples and precisely its given bits. -/
def classEmbedding {A : Type} [Finite A] (T : BoolTable L A) (b : A → Bit)
    (h : Realized U S pack mask T b) :
    Canonical.Embedding (table T b)
      (BinarySource.FullReduct.expandedTable U S pack mask sap) := by
  let C := chartOf U S pack mask T b h
  let iso := chartOfIso U S pack mask T b h
  let c := (data U S pack mask sap).chart_embeds C |>.some
  let ec : Canonical.Embedding (table C.old.full C.bits)
      (BinarySource.FullReduct.expandedTable U S pack mask sap) :=
    BinarySource.FullReduct.fromLimit U S pack mask sap c
  exact ec.comp iso.toEmbedding

/-- A tuple in the actual model has legal phase bits under ANY proved
old FULL reduct isomorphism. Full realizations agree on canonical names. -/
theorem model_legal (names : PairFaithful U S pack)
    (e : Canonical.Iso (BinarySource.FullReduct.oldTable U S pack mask sap) U)
    {n : ℕ} (p : Fin n ↪ BinarySource.FullReduct.Carrier U S pack mask sap) :
    Age.Legal S mask (pack ∘ e.point ∘ p)
      (BinarySource.FullReduct.bits U S pack mask sap ∘ p) := by
  obtain ⟨q,hq⟩ := BinarySource.FullReduct.finite_old_witness U S pack mask sap p
  let p' : Canonical.Embedding
      (pullback (BinarySource.FullReduct.oldTable U S pack mask sap) p) U :=
    e.toEmbedding.comp (embeddingOf p p.injective (fun _ _ => rfl))
  apply Age.legal_of_names S mask hq
  intro x y
  exact names q p' x y

end
end CCO.FullPhaseLift.Marked
