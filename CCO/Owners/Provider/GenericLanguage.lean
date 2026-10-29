import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Actual relational structures of arbitrary arity

All induced maps preserve and reflect EVERY named relation on every tuple.
There is no binary-orbital reduct premise in the generic finite-base branch.
The language may be arbitrary; finite relational languages are a special case.
-/

universe u v
namespace CCO.Owners.Provider.Relational

structure Structure (A : Type u) where
  Symbol : Type v
  arity : Symbol → Nat
  relation : ∀ s, (Fin (arity s) → A) → Prop

variable {A : Type u} (S : Structure.{u,v} A)

def Preserves {U V : Type*} (ι : U → A) (κ : V → A) (f : U → V) : Prop :=
  ∀ s (t : Fin (S.arity s) → U),
    S.relation s (fun k => κ (f (t k))) ↔ S.relation s (fun k => ι (t k))

def Aut {U : Type*} (ι : U → A) : Subgroup (Equiv.Perm U) where
  carrier := {f | Preserves S ι ι f}
  one_mem' := by intro s t; exact Iff.rfl
  mul_mem' := by
    intro f g hf hg s t
    exact (hf s (fun k => g (t k))).trans (hg s t)
  inv_mem' := by
    intro g hg s t
    have h := (hg s (fun k => g⁻¹ (t k))).symm
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h

theorem Aut.preserves {U : Type*} {ι : U → A} (g : Aut S ι) :
    Preserves S ι ι g.val := g.property

structure Partial {U : Type*} (ι : U → A) where
  domain : Set U
  map : domain → U
  injective : Function.Injective map
  preserves : Preserves S (fun x : domain => ι x.val) ι map

/-- Ordinary finite induced homogeneity, with the inverse orientation
convenient for anchoring an arbitrary age embedding. -/
def Homogeneous : Prop :=
  ∀ T : Set A, T.Finite → ∀ f : T → A, Function.Injective f →
    Preserves S Subtype.val id f →
    ∃ g : Aut S id, ∀ x : T, g.val (f x) = x.val

theorem extend_finite (hom : Homogeneous S) (T : Set A) (hT : T.Finite)
    (f : T → A) (hinj : Function.Injective f)
    (hf : Preserves S Subtype.val id f) :
    ∃ g : Aut S id, ∀ x : T, g.val x.val = f x := by
  obtain ⟨g, hg⟩ := hom T hT f hinj hf
  refine ⟨g⁻¹, ?_⟩
  intro x
  have h := congrArg g.val.symm (hg x)
  change g.val.symm x.val = f x
  simpa only [Equiv.symm_apply_apply] using h.symm

/-- In particular every actual finite induced automorphism extends
ambiently. This derives finite kernel recognition from ambient invariance. -/
theorem finite_aut_ambient (hom : Homogeneous S) (T : Set A) (hT : T.Finite)
    (β : Aut S (Subtype.val : T → A)) :
    ∃ g : Aut S id, ∀ x : T, g.val x.val = (β.val x).val := by
  apply extend_finite S hom T hT (fun x => (β.val x).val)
  · exact Subtype.val_injective.comp β.val.injective
  · exact Aut.preserves S β

/-- Conjugation along a genuine all-arity induced isomorphism. -/
def conjugateAut {U V : Type*} (ι : U → A) (κ : V → A)
    (e : U ≃ V) (he : Preserves S ι κ e) (β : Aut S ι) : Aut S κ := by
  refine ⟨e.permCongr β.val, ?_⟩
  intro s t
  change S.relation s (fun k => κ (e (β.val (e.symm (t k)))) ) ↔
    S.relation s (fun k => κ (t k))
  apply (he s (fun k => β.val (e.symm (t k)))).trans
  apply ((Aut.preserves S β) s (fun k => e.symm (t k))).trans
  simpa only [Equiv.apply_symm_apply] using (he s (fun k => e.symm (t k))).symm

@[simp] theorem conjugateAut_apply {U V : Type*} (ι : U → A) (κ : V → A)
    (e : U ≃ V) (he : Preserves S ι κ e) (β : Aut S ι) (x : V) :
    (conjugateAut S ι κ e he β).val x = e (β.val (e.symm x)) := rfl

end CCO.Owners.Provider.Relational
