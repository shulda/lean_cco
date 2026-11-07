import CCO.UnfilteredEP.FiniteTemplate
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.OrderOfElement
import Lean.Elab.Tactic.Omega

/-!
# B064 C105–C106: a genuine finite core retract

Choose a minimum-rank endomorphism of the actual finite original-sort and
atom table. Its action on its image is a finite permutation, so a positive
power fixes that image. This power is an idempotent of the same minimum
rank. Every endomorphism of the induced image is an automorphism: otherwise
its composite with the retraction has smaller rank on the original table.
No Ramsey provider, concrete CCO source or terminal-label premise is used.
-/

universe u v w
namespace CCO.UnfilteredEP.FiniteTemplate
variable {OldSort : Type u} {Atom : Type v} {Label : Type w}
variable (T : FiniteTemplate OldSort Atom Label)

/-- The full induced table on a set of retained labels. -/
def induced (U : Set Label) : FiniteTemplate OldSort Atom U where
  sort x := T.sort x.val
  rel a x y := T.rel a x.val y.val

/-- Cardinality of the image, including the empty template. -/
noncomputable def rank (_T : FiniteTemplate OldSort Atom Label) (f : Label → Label) : Nat := Nat.card (Set.range f)

theorem Endomorphism.iterate {f : Label → Label} (hf : T.Endomorphism f) (n : Nat) :
    T.Endomorphism f^[n] := by
  induction n with
  | zero => exact T.endomorphism_id
  | succ n ih =>
    rw [Function.iterate_succ]
    exact Endomorphism.comp T ih hf

/-- A minimum exists among actual endomorphisms, since identity is one. -/
theorem exists_minimum_rank :
    ∃ f : Label → Label, T.Endomorphism f ∧
      ∀ g : Label → Label, T.Endomorphism g → T.rank f ≤ T.rank g := by
  classical
  have ex : ∃ n : Nat, ∃ f : Label → Label, T.Endomorphism f ∧ T.rank f = n :=
    ⟨T.rank id,id,T.endomorphism_id,rfl⟩
  obtain ⟨f,hf,hr⟩ := Nat.find_spec ex
  refine ⟨f,hf,?_⟩
  intro g hg
  rw [hr]
  exact Nat.find_min' ex ⟨g,hg,rfl⟩

/-- Minimum rank makes the restriction to the image a permutation. -/
theorem minimum_rank_image_bijective [Finite Label]
    (f : Label → Label) (hf : T.Endomorphism f)
    (minimal : ∀ g, T.Endomorphism g → T.rank f ≤ T.rank g) :
    Function.Bijective (fun x : Set.range f => (⟨f x.val, x.val, rfl⟩ : Set.range f)) := by
  classical
  let : Fintype (Set.range f) := Fintype.ofFinite _
  let : Fintype (Set.range (f ∘ f)) := Fintype.ofFinite _
  let inc : Set.range (f ∘ f) → Set.range f := fun x =>
    ⟨x.val,by obtain ⟨y,hy⟩ := x.property; exact ⟨f y,hy⟩⟩
  have hi : Function.Injective inc := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : Set.range f => z.val) h
  have hs : Function.Surjective inc := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective inc hi hn
    have hle := minimal (f ∘ f) (Endomorphism.comp T hf hf)
    unfold rank at hle
    simp only [Nat.card_eq_fintype_card] at hle
    omega
  have onto : Function.Surjective
      (fun x : Set.range f => (⟨f x.val,x.val,rfl⟩ : Set.range f)) := by
    intro y
    obtain ⟨z,hz⟩ := hs y
    obtain ⟨x,hx⟩ := z.property
    refine ⟨⟨f x,x,rfl⟩,?_⟩
    apply Subtype.ext
    exact hx.trans (congrArg Subtype.val hz)
  exact ⟨(Finite.injective_iff_surjective.mpr onto),onto⟩

/-- C105: an actual positive power of a minimum-rank map is an
idempotent, has the same image and retains the minimum rank. -/
theorem minimum_rank_idempotent_power [Finite Label]
    (f : Label → Label) (hf : T.Endomorphism f)
    (minimal : ∀ g, T.Endomorphism g → T.rank f ≤ T.rank g) :
    ∃ n : Nat, 0 < n ∧ T.Endomorphism f^[n] ∧
      (∀ x, f^[n] (f^[n] x) = f^[n] x) ∧ Set.range f^[n] = Set.range f ∧
      ∀ g, T.Endomorphism g → T.rank f^[n] ≤ T.rank g := by
  classical
  let : Fintype (Set.range f) := Fintype.ofFinite _
  let g : Equiv.Perm (Set.range f) := Equiv.ofBijective _
    (T.minimum_rank_image_bijective f hf minimal)
  have step (x : Set.range f) : (g x).val = f x.val := rfl
  have iter (n : Nat) (x : Set.range f) : f^[n] x.val = ((g ^ n) x).val := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply',pow_succ']
      change f (f^[n] x.val) = (g ((g ^ n) x)).val
      rw [ih,step]
  let n := orderOf g
  have hn : 0 < n := orderOf_pos g
  have fixed (x : Set.range f) : f^[n] x.val = x.val := by
    rw [iter,pow_orderOf_eq_one]
    rfl
  have lands (x : Label) : f^[n] x ∈ Set.range f := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [hk,Function.iterate_succ_apply']
    exact ⟨f^[k] x,rfl⟩
  have range_eq : Set.range f^[n] = Set.range f := by
    apply Set.Subset.antisymm
    · rintro y ⟨x,rfl⟩
      exact lands x
    · intro y hy
      exact ⟨y,fixed ⟨y,hy⟩⟩
  refine ⟨n,hn,Endomorphism.iterate T hf n,?_,range_eq,?_⟩
  · intro x
    exact fixed ⟨f^[n] x,lands x⟩
  · intro h hh
    unfold rank
    rw [range_eq]
    exact minimal h hh

/-- Every finite table has an idempotent endomorphism of minimum rank. -/
theorem exists_minimum_rank_retract [Finite Label] :
    ∃ e : Label → Label, T.Endomorphism e ∧ (∀ x, e (e x) = e x) ∧
      ∀ g, T.Endomorphism g → T.rank e ≤ T.rank g := by
  obtain ⟨f,hf,hm⟩ := T.exists_minimum_rank
  obtain ⟨n,_,he,hi,_,hm'⟩ := T.minimum_rank_idempotent_power f hf hm
  exact ⟨f^[n],he,hi,hm'⟩

/-- C106: the induced retract image is a core, with its original sorts
and atom relations. No individual label has become a constant. -/
theorem minimum_rank_retract_image_core [Finite Label]
    (e : Label → Label) (he : T.Endomorphism e) (_idem : (∀ x, e (e x) = e x))
    (minimal : ∀ g, T.Endomorphism g → T.rank e ≤ T.rank g) :
    (T.induced (Set.range e)).Core := by
  classical
  intro h hh
  let U := Set.range e
  let hmap : Label → Label := fun x => (h ⟨e x,x,rfl⟩).val
  have hm : T.Endomorphism hmap := by
    constructor
    · intro x
      exact (hh.1 ⟨e x,x,rfl⟩).trans (he.1 x)
    · intro a x y hxy
      exact hh.2 a _ _ (he.2 a x y hxy)
  have onto : Function.Surjective h := by
    by_contra hn
    let inc : Set.range hmap → U := fun x =>
      ⟨x.val,by obtain ⟨y,hy⟩ := x.property; rw [← hy]; exact (h ⟨e y,y,rfl⟩).property⟩
    have hi : Function.Injective inc := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : U => z.val) h
    have hnot : ¬ Function.Surjective inc := by
      intro hs
      apply hn
      intro y
      obtain ⟨z,hz⟩ := hs y
      obtain ⟨x,hx⟩ := z.property
      refine ⟨⟨e x,x,rfl⟩,?_⟩
      apply Subtype.ext
      exact hx.trans (congrArg Subtype.val hz)
    let : Fintype U := Fintype.ofFinite _
    let : Fintype (Set.range hmap) := Fintype.ofFinite _
    have hlt := Fintype.card_lt_of_injective_not_surjective inc hi hnot
    have hle := minimal hmap hm
    unfold rank at hle
    have hlt' : Nat.card (Set.range hmap) < Nat.card (Set.range e) := by
      simpa only [U,Nat.card_eq_fintype_card] using hlt
    exact Nat.not_lt_of_ge hle hlt'
  exact (T.induced U).automorphism_of_injective h hh
    ((Finite.injective_iff_surjective.mpr onto))

end CCO.UnfilteredEP.FiniteTemplate
