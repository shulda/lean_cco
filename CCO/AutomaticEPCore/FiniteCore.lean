import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Finite.Prod

/-! B063 C56–C57: a finite old-atom table separated by globally loopless
relations is a core. New unary labels are not named in this vocabulary.
The reflection proof uses a finite relation carrier, so no infinite
bijective-endomorphism inference is made. -/

namespace CCO.AutomaticEPCore

universe u v
variable {A : Type u} {T : Type v}

/-- Preservation of precisely the given original binary names. -/
def TableEndomorphism (R : A → T → T → Prop) (f : T → T) : Prop :=
  ∀ a ⦃s t⦄, R a s t → R a (f s) (f t)

/-- Both preservation and reflection on the same original names. -/
def TableAutomorphism (R : A → T → T → Prop) (f : T → T) : Prop :=
  Function.Bijective f ∧ ∀ a s t, R a (f s) (f t) ↔ R a s t

/-- A preserved globally loopless separator prevents every collision. -/
theorem table_endomorphism_injective_of_separation
    (R : A → T → T → Prop) (BP : Set A)
    (loopless : ∀ a ∈ BP, ∀ t, ¬ R a t t)
    (separates : ∀ s t : T, s ≠ t → ∃ a ∈ BP, R a s t)
    (f : T → T) (hf : TableEndomorphism R f) :
    Function.Injective f := by
  intro s t h
  by_contra hne
  obtain ⟨a,ha,hst⟩ := separates s t hne
  have hImage := hf a hst
  rw [h] at hImage
  exact loopless a ha (f t) hImage

/-- A finite injective relational endomorphism reflects every relation.
For each original atom its relation carrier maps injectively into itself,
thus surjectively, with the SAME point permutation on both endpoints. -/
theorem finite_table_endomorphism_automorphism [Finite T]
    (R : A → T → T → Prop) (f : T → T)
    (hf : TableEndomorphism R f) (hinj : Function.Injective f) :
    TableAutomorphism R f := by
  classical
  refine ⟨⟨hinj,Finite.surjective_of_injective hinj⟩,?_⟩
  intro a s t
  constructor
  · intro hst
    let C := {p : T × T // R a p.1 p.2}
    let g : C → C := fun p => ⟨(f p.val.1,f p.val.2),hf a p.property⟩
    have hg : Function.Injective g := by
      intro p q hpq
      apply Subtype.ext
      apply Prod.ext
      · exact hinj (congrArg (fun z : C => z.val.1) hpq)
      · exact hinj (congrArg (fun z : C => z.val.2) hpq)
    obtain ⟨p,hp⟩ := (Finite.surjective_of_injective hg) ⟨(f s,f t),hst⟩
    have hs : p.val.1 = s := hinj (congrArg (fun z : C => z.val.1) hp)
    have ht : p.val.2 = t := hinj (congrArg (fun z : C => z.val.2) hp)
    simpa only [hs,ht] using p.property
  · exact fun h => hf a h

/-- The generic finite consequence used only after actual source
bipartite separation and terminal looplessness have both been proved. -/
theorem finite_table_core_of_separation [Finite T]
    (R : A → T → T → Prop) (BP : Set A)
    (loopless : ∀ a ∈ BP, ∀ t, ¬ R a t t)
    (separates : ∀ s t : T, s ≠ t → ∃ a ∈ BP, R a s t)
    (f : T → T) (hf : TableEndomorphism R f) :
    TableAutomorphism R f :=
  finite_table_endomorphism_automorphism R f hf
    (table_endomorphism_injective_of_separation R BP loopless separates f hf)

end CCO.AutomaticEPCore
