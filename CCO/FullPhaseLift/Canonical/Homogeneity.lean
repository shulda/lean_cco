import CCO.FullPhaseLift.Canonical.FirstOrder
import Mathlib.ModelTheory.Fraisse
import Mathlib.Data.Fintype.EquivFin

/-! Exact native first-order ultrahomogeneity gives full relational-table
homogeneity. Every relation arity, negative truth and nullary is retained;
the theorem does not pass to a binary reduct. -/

universe u v
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

/-- FULL isomorphism preserves homogeneity even when the native Fraïssé
carrier and the receiving old carrier lie in different universes. The
finite source is explicitly recoded into the first carrier's universe. -/
theorem homogeneous_of_iso {L : Signature} {M : Type u} {N : Type v}
    {U : BoolTable L M} {V : BoolTable L N} (e : Iso U V)
    (hom : (toRelational U).Homogeneous) : (toRelational V).Homogeneous := by
  classical
  intro W _ B f g
  letI := Fintype.ofFinite W
  let c : W ≃ ULift.{u} (Fin (Fintype.card W)) := {
    toFun x := ⟨(Fintype.equivFin W) x⟩
    invFun x := (Fintype.equivFin W).symm x.down
    left_inv x := (Fintype.equivFin W).symm_apply_apply x
    right_inv x := by
      apply ULift.ext
      exact (Fintype.equivFin W).apply_symm_apply x.down }
  let B' : R.Structure L.language (ULift.{u} (Fin (Fintype.card W))) := {
    rel R xs := B.rel R (c.symm ∘ xs) }
  let back : RelationalCompletion.Relational.Structure.Embedding B' B := {
    point := c.symm
    injective := c.symm.injective
    rel_iff _ _ := Iff.rfl }
  let f' := e.symm.toEmbedding.comp (f.comp back)
  let g' := e.symm.toEmbedding.comp (g.comp back)
  obtain ⟨a,ha⟩ := hom (ULift.{u} (Fin (Fintype.card W))) B' f' g'
  refine ⟨(e.symm.trans a).trans e,?_⟩
  intro x
  have hx : back.point (c x) = x := c.symm_apply_apply x
  have h := ha (c x)
  change a.point (e.point.symm (f.point (back.point (c x)))) =
    e.point.symm (g.point (back.point (c x))) at h
  rw [hx] at h
  have h' := congrArg e.point h
  change e.point (a.point (e.point.symm (f.point x))) = g.point x
  simpa only [Equiv.apply_symm_apply] using h'

end CCO.FullPhaseLift.Canonical
