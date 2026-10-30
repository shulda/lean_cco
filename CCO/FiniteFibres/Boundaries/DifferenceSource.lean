import CCO.FiniteKernel.BinarySource
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel

/-! The literal complete difference language on an arbitrary abelian group.
It can have infinitely many named atoms; no finite-palette AtomicSource is
silently supplied. Its FULL original automorphism group is exactly translation. -/
namespace CCO.FiniteFibres.Boundaries.Difference

variable (A : Type*) [AddCommGroup A]

abbrev Atom := {a : A // a ≠ 0}

def source : FiniteKernel.BinaryStructure A where
  Unary := Empty
  Binary := Atom A
  unary r := Empty.elim r
  binary r x y := y = x + r.val

def converse (a : Atom A) : Atom A := ⟨-a.val,neg_ne_zero.mpr a.property⟩

theorem converse_involutive (a : Atom A) : converse A (converse A a) = a :=
  Subtype.ext (neg_neg a.val)

theorem relation_reverse (a : Atom A) (x y : A) :
    (source A).binary a x y ↔ (source A).binary (converse A a) y x := by
  change y = x + a.val ↔ x = y + -a.val
  constructor <;> intro h <;> rw [h] <;> abel

theorem irreflexive (a : Atom A) (x : A) : ¬(source A).binary a x x := by
  intro h
  change x = x + a.val at h
  exact a.property (add_left_cancel (show x + a.val = x + 0 by simpa using h.symm))

theorem complete {x y : A} (h : x ≠ y) :
    ∃! a : Atom A, (source A).binary a x y := by
  let a : Atom A := ⟨y-x,sub_ne_zero.mpr h.symm⟩
  refine ⟨a,by change y = x + (y-x); abel,?_⟩
  intro b hb
  apply Subtype.ext
  change y = x + b.val at hb
  change b.val = y-x
  rw [hb]
  abel

def translate (t : A) : (source A).Aut :=
  ⟨Equiv.addLeft t,⟨fun r => Empty.elim r,by
    intro r x y
    change t + y = (t + x) + r.val ↔ y = x + r.val
    simp only [add_assoc,add_left_cancel_iff]⟩⟩

@[simp] theorem translate_apply (t x : A) : (translate A t).val x = t + x := rfl

theorem fullAut_translation (g : (source A).Aut) (x : A) :
    g.val x = g.val 0 + x := by
  by_cases hx : x = 0
  · subst x
    simp
  · let a : Atom A := ⟨x,hx⟩
    have h := (g.property.2 a 0 x).mpr (by change x = 0+x; simp)
    exact h

theorem translate_injective : Function.Injective (translate A) := by
  intro a b h
  have hh := congrArg (fun g : (source A).Aut => g.val 0) h
  simpa only [translate_apply,add_zero] using hh

theorem translate_surjective : Function.Surjective (translate A) := by
  intro g
  refine ⟨g.val 0,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact (fullAut_translation A g x).symm

noncomputable def fullAutEquiv : A ≃ (source A).Aut :=
  Equiv.ofBijective (translate A) ⟨translate_injective A,translate_surjective A⟩

theorem fullAut_card : Nat.card (source A).Aut = Nat.card A :=
  Nat.card_congr (fullAutEquiv A).symm

theorem transitive (x y : A) : ∃ g : (source A).Aut, g.val x = y :=
  ⟨translate A (y-x),by simp only [translate_apply]; abel⟩

/-- Complete actual finite partial isomorphisms are restrictions of a SINGLE
translation, including the empty request. No named origin is added. -/
theorem homogeneous : (source A).Homogeneous := by
  classical
  intro C f _ _ hb
  by_cases hC : Nonempty ↥C
  · let a : ↥C := Classical.choice hC
    refine ⟨translate A (f a-a.val),fun x => ?_⟩
    by_cases hx : x = a
    · subst x
      change f a-a.val+a.val = f a
      abel
    · have hn : x.val-a.val ≠ 0 := by
        intro h
        exact hx (Subtype.ext (sub_eq_zero.mp h))
      let r : Atom A := ⟨x.val-a.val,hn⟩
      have hr : (source A).binary r a.val x.val := by
        change x.val = a.val + (x.val-a.val)
        abel
      have hh := (hb r a x).mpr hr
      change f x = f a + (x.val-a.val) at hh
      change f a-a.val+x.val = f x
      rw [hh]
      abel
  · exact ⟨translate A 0,fun x => False.elim (hC ⟨x⟩)⟩

/-- A point-fixing full automorphism is the identity, not just an element
whose action on some quotient happens to be trivial. -/
theorem stabilizer_trivial (g : (source A).Aut) (a : A) (h : g.val a = a) : g = 1 := by
  have hzero : g.val 0 = 0 := by
    have hh : g.val 0 + a = 0 + a := by simpa only [zero_add] using (fullAut_translation A g a).symm.trans h
    exact add_right_cancel hh
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change g.val x = x
  rw [fullAut_translation,hzero,zero_add]

def stabilizerOrbit (C : Finset A) (x : A) : Set A :=
  {y | ∃ g : (source A).Aut, (∀ a ∈ C, g.val a = a) ∧ g.val x = y}

/-- Real algebraicity is the actual finite orbit of the full pointwise
stabilizer. It is not an orbit of a selected smaller translation subgroup. -/
def realAcl (C : Finset A) : Set A := {x | (stabilizerOrbit A C x).Finite}

theorem singleton_orbit (a x : A) : stabilizerOrbit A {a} x = {x} := by
  classical
  ext y
  constructor
  · rintro ⟨g,hfix,hg⟩
    have he : g = 1 := stabilizer_trivial A g a (hfix a (Finset.mem_singleton_self a))
    subst g
    exact hg.symm
  · intro h
    have he : y = x := h
    subst y
    exact ⟨1,fun _ _ => rfl,rfl⟩

theorem realAcl_singleton (a : A) : realAcl A {a} = Set.univ := by
  classical
  ext x
  change (stabilizerOrbit A {a} x).Finite ↔ True
  rw [singleton_orbit]
  exact ⟨fun _ => trivial,fun _ => Set.finite_singleton x⟩

/-- Every point is uniquely defined over the anchor by logical equality
or ONE actual named binary atom. These are finite atomic formulas. -/
theorem unique_atomic_definition (a x : A) :
    x = a ∨ ∃ r : Atom A, {y | (source A).binary r a y} = {x} := by
  by_cases h : x = a
  · exact Or.inl h
  · refine Or.inr ⟨⟨x-a,sub_ne_zero.mpr h⟩,?_⟩
    ext y
    change y = a + (x-a) ↔ y = x
    have he : a + (x-a) = x := by abel
    rw [he]

end CCO.FiniteFibres.Boundaries.Difference
