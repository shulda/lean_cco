import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Pi

/-! Independent finite original-sort/atom tables for B064 N01 and N13.
The new labels are the carrier of the table, not individually named
relations or constants. Original sort predicates and all old atoms remain. -/

universe u v w
namespace CCO.UnfilteredEP

structure FiniteTemplate (OldSort : Type u) (Atom : Type v) (Label : Type w) where
  sort : Label → OldSort
  rel : Atom → Label → Label → Prop

namespace FiniteTemplate
variable {OldSort : Type u} {Atom : Type v} {Label : Type w}
variable (T : FiniteTemplate OldSort Atom Label)

def Endomorphism (f : Label → Label) : Prop :=
  (∀ t, T.sort (f t) = T.sort t) ∧
  ∀ a s t, T.rel a s t → T.rel a (f s) (f t)

def Automorphism (f : Label → Label) : Prop :=
  Function.Bijective f ∧ (∀ t, T.sort (f t) = T.sort t) ∧
  ∀ a s t, T.rel a (f s) (f t) ↔ T.rel a s t

def Core : Prop := ∀ f : Label → Label, T.Endomorphism f → T.Automorphism f

theorem endomorphism_id : T.Endomorphism id :=
  ⟨fun _ => rfl,fun _ _ _ h => h⟩

theorem Endomorphism.comp {f g : Label → Label}
    (hf : T.Endomorphism f) (hg : T.Endomorphism g) : T.Endomorphism (f ∘ g) :=
  ⟨fun t => (hf.1 (g t)).trans (hg.1 t),fun a s t h => hf.2 a _ _ (hg.2 a s t h)⟩

/-- Finite bijective endomorphisms reflect every original relation.
The finite relation carrier, rather than just the point carrier, is used. -/
theorem automorphism_of_injective [Finite Label] (f : Label → Label)
    (hf : T.Endomorphism f) (hinj : Function.Injective f) : T.Automorphism f := by
  classical
  refine ⟨⟨hinj,Finite.surjective_of_injective hinj⟩,hf.1,?_⟩
  intro a s t
  constructor
  · intro hst
    let C := {p : Label × Label // T.rel a p.1 p.2}
    let g : C → C := fun p => ⟨(f p.val.1,f p.val.2),hf.2 a _ _ p.property⟩
    have hg : Function.Injective g := by
      intro p q hpq
      apply Subtype.ext
      exact Prod.ext (hinj (congrArg (fun z : C => z.val.1) hpq))
        (hinj (congrArg (fun z : C => z.val.2) hpq))
    obtain ⟨p,hp⟩ := (Finite.surjective_of_injective hg) ⟨(f s,f t),hst⟩
    have hs := hinj (congrArg (fun z : C => z.val.1) hp)
    have ht := hinj (congrArg (fun z : C => z.val.2) hp)
    simpa only [hs,ht] using p.property
  · exact fun h => hf.2 a s t h

/-- C01: for an endomorphism of a finite table, surjectivity is exactly
being an automorphism of the full original-sort/atom structure. -/
theorem automorphism_iff_surjective [Finite Label] (f : Label → Label)
    (hf : T.Endomorphism f) : T.Automorphism f ↔ Function.Surjective f := by
  constructor
  · exact fun h => h.1.2
  · intro h
    exact T.automorphism_of_injective f hf (Finite.injective_iff_surjective.mpr h)

theorem Automorphism.endomorphism {f : Label → Label} (hf : T.Automorphism f) :
    T.Endomorphism f := ⟨hf.2.1,fun a s t h => (hf.2.2 a s t).mpr h⟩

noncomputable def automorphismEquiv {f : Label → Label} (hf : T.Automorphism f) :
    Label ≃ Label := Equiv.ofBijective f hf.1

theorem automorphism_inverse_endomorphism {f : Label → Label} (hf : T.Automorphism f) :
    T.Endomorphism (T.automorphismEquiv hf).symm := by
  let e := T.automorphismEquiv hf
  have he (x : Label) : f (e.symm x) = x := e.apply_symm_apply x
  constructor
  · intro t
    exact ((congrArg T.sort (he t)).symm.trans (hf.2.1 (e.symm t))).symm
  · intro a s t h
    apply (hf.2.2 a (e.symm s) (e.symm t)).mp
    simpa only [he] using h

end FiniteTemplate
end CCO.UnfilteredEP
