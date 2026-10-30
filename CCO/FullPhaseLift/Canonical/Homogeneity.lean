import CCO.FullPhaseLift.Canonical.FirstOrder
import Mathlib.ModelTheory.Fraisse

/-! Exact native first-order ultrahomogeneity gives full relational-table
homogeneity. Every relation arity, negative truth and nullary is retained;
the theorem does not pass to a binary reduct. -/

universe v
namespace CCO.FullPhaseLift.Canonical
open scoped FirstOrder

theorem decoded_rel {L : Signature} {M : Type v} (A : L.firstOrder.Structure M)
    {n : ℕ} (R : L.language.Rel n) (xs : Fin n → M) :
    (toRelational (ofFirstOrder A)).rel R xs ↔ A.RelMap R xs := by
  have h := congrArg (fun T : RelationalCompletion.Relational.Structure L.language M => T.rel R xs)
    (toRelational_ofRelational
      (⟨A.RelMap⟩ : RelationalCompletion.Relational.Structure L.language M))
  exact Iff.of_eq h

def nativeEmbedding {L : Signature} {M V : Type v} (A : L.firstOrder.Structure M)
    {B : R.Structure L.language V}
    (f : RelationalCompletion.Relational.Structure.Embedding B (toRelational (ofFirstOrder A))) :
    @FirstOrder.Language.Embedding L.firstOrder V M
      (toFirstOrder (ofRelational B)) A := by
  letI := A
  letI := toFirstOrder (ofRelational B)
  exact {
    toFun := f.point
    inj' := f.injective
    map_fun' := fun F => nomatch F
    map_rel' := by
      intro n R xs
      have h := f.rel_iff R xs
      rw [← decoded_rel A R (f.point ∘ xs)]
      change (toRelational (ofFirstOrder A)).rel R (f.point ∘ xs) ↔
        (toRelational (ofRelational B)).rel R xs
      rw [toRelational_ofRelational]
      exact h }

def nativeIso {L : Signature} {M : Type v} (A : L.firstOrder.Structure M)
    (e : @FirstOrder.Language.Equiv L.firstOrder M M A A) :
    Iso (ofFirstOrder A) (ofFirstOrder A) where
  point := e.toEquiv
  rel_iff R xs := (decoded_rel A R (e ∘ xs)).trans
    ((e.map_rel' R xs).trans (decoded_rel A R xs).symm)

theorem homogeneous_of_firstOrder {L : Signature} {M : Type v}
    (A : L.firstOrder.Structure M)
    (hom : @FirstOrder.Language.IsUltrahomogeneous L.firstOrder M A) :
    (toRelational (ofFirstOrder A)).Homogeneous := by
  intro V _ B f g
  letI : L.firstOrder.Structure M := A
  letI : L.firstOrder.Structure V := toFirstOrder (ofRelational B)
  let f' := nativeEmbedding A f
  let g' := nativeEmbedding A g
  have hfg : FirstOrder.Language.Structure.FG L.firstOrder V :=
    FirstOrder.Language.Structure.FG.of_finite
  let S := f'.toHom.range
  have hS : S.FG := hfg.range f'.toHom
  let p : S ↪[L.firstOrder] M := g'.comp f'.equivRange.symm.toEmbedding
  obtain ⟨a,ha⟩ := hom S hS p
  refine ⟨nativeIso A a,?_⟩
  intro x
  have h := DFunLike.congr_fun ha (f'.equivRange x)
  change g' (f'.equivRange.symm (f'.equivRange x)) = a (f' x) at h
  rw [FirstOrder.Language.Equiv.symm_apply_apply] at h
  exact h.symm

end CCO.FullPhaseLift.Canonical
