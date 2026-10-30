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

/-- Repetitions in a finite tuple are handled through its actual finite
image, without adding false injectivity or distinctness assumptions. -/
theorem model_legal_tuple (names : PairFaithful U S pack)
    (e : Canonical.Iso (BinarySource.FullReduct.oldTable U S pack mask sap) U)
    {A : Type} [Finite A] (p : A → BinarySource.FullReduct.Carrier U S pack mask sap) :
    Age.Legal S mask (pack ∘ e.point ∘ p)
      (BinarySource.FullReduct.bits U S pack mask sap ∘ p) := by
  let B := Set.range p
  letI : Fintype B := Fintype.ofFinite B
  let f := Fintype.equivFin B
  let q : Fin (Fintype.card B) ↪ BinarySource.FullReduct.Carrier U S pack mask sap :=
    f.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  let j : A → Fin (Fintype.card B) := fun x => f ⟨p x,⟨x,rfl⟩⟩
  have he : (q : Fin (Fintype.card B) → _) ∘ j = p := by
    funext x
    change (f.symm (f ⟨p x,⟨x,rfl⟩⟩)).val = p x
    rw [f.symm_apply_apply]
  have hl := model_legal U S pack mask sap names e q
  rw [← he]
  exact ⟨fun x => hl.1 (j x),fun x y => hl.2 (j x) (j y)⟩

/-- The genuinely constructed full marking is globally phase legal on
all original points after the FULL old-reduct identification. -/
theorem model_global_legal (names : PairFaithful U S pack)
    (e : Canonical.Iso (BinarySource.FullReduct.oldTable U S pack mask sap) U) :
    mask.GlobalMarking (BinarySource.FullReduct.bits U S pack mask sap ∘ e.point.symm ∘ pack.symm) := by
  constructor
  · intro x
    let p : Fin 1 → BinarySource.FullReduct.Carrier U S pack mask sap :=
      fun _ => e.point.symm (pack.symm x)
    have h := (model_legal_tuple U S pack mask sap names e p).1 0
    simpa only [p,Function.comp_def,Equiv.apply_symm_apply] using h
  · intro x y
    let p : Fin 2 → BinarySource.FullReduct.Carrier U S pack mask sap :=
      ![e.point.symm (pack.symm x),e.point.symm (pack.symm y)]
    have h := model_legal_tuple U S pack mask sap names e p
    have he : pack ∘ e.point ∘ p = ![x,y] := by
      funext i
      fin_cases i
      · exact (congrArg pack (e.point.apply_symm_apply _)).trans (pack.apply_symm_apply x)
      · exact (congrArg pack (e.point.apply_symm_apply _)).trans (pack.apply_symm_apply y)
    rw [he] at h
    simpa only [p,Function.comp_def,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one] using h.2 0 1

end
end CCO.FullPhaseLift.Marked
