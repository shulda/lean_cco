import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic

/-!
# Actual arbitrary unary/binary relational structures

This module also covers directed relations, loops, infinitely many predicate
symbols and the empty universe. Nullary predicates impose no condition on a
permutation. The acting group is the FULL original automorphism group.
The symmetric finite-palette `AtomicSource` is deliberately not substituted
for this more general source contract.
-/

universe u v w

namespace CCO.FiniteKernel

structure BinaryStructure (X : Type u) where
  Unary : Type v
  Binary : Type w
  unary : Unary → X → Prop
  binary : Binary → X → X → Prop

namespace BinaryStructure

variable {X : Type u} (S : BinaryStructure.{u,v,w} X)

def autGroup : Subgroup (Equiv.Perm X) where
  carrier := {g | (∀ r x, S.unary r (g x) ↔ S.unary r x) ∧
    ∀ r x y, S.binary r (g x) (g y) ↔ S.binary r x y}
  one_mem' := by exact ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  mul_mem' := by
    rintro g h ⟨hgu,hgb⟩ ⟨hhu,hhb⟩
    exact ⟨fun r x => (hgu r (h x)).trans (hhu r x),
      fun r x y => (hgb r (h x) (h y)).trans (hhb r x y)⟩
  inv_mem' := by
    rintro g ⟨hgu,hgb⟩
    constructor
    · intro r x
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hgu r (g⁻¹ x)).symm
    · intro r x y
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hgb r (g⁻¹ x) (g⁻¹ y)).symm

abbrev Aut := ↥S.autGroup

theorem Aut.unary (g : S.Aut) (r : S.Unary) (x : X) :
    S.unary r (g.val x) ↔ S.unary r x := g.property.1 r x

theorem Aut.binary (g : S.Aut) (r : S.Binary) (x y : X) :
    S.binary r (g.val x) (g.val y) ↔ S.binary r x y := g.property.2 r x y

def induced (A : Set X) : BinaryStructure ↥A where
  Unary := S.Unary
  Binary := S.Binary
  unary r x := S.unary r x.val
  binary r x y := S.binary r x.val y.val

/-- The ordinary actual finite-partial-isomorphism extension property for
the FULL automorphism group. Both orientations, loops and unary predicates
are part of the displayed hypothesis. -/
def Homogeneous : Prop :=
  ∀ (A : Finset X) (f : ↥A → X), Function.Injective f →
    (∀ r x, S.unary r (f x) ↔ S.unary r x.val) →
    (∀ r x y, S.binary r (f x) (f y) ↔ S.binary r x.val y.val) →
    ∃ g : S.Aut, ∀ x, g.val x.val = f x

/-- Name every owner separately. The predicates are literal equalities of
owner labels, so homogeneity of this expansion is the genuine extra A04. -/
def ownerExpansion {I : Type*} (owner : X → I) : BinaryStructure X where
  Unary := S.Unary ⊕ I
  Binary := S.Binary
  unary
    | .inl r, x => S.unary r x
    | .inr i, x => owner x = i
  binary := S.binary

theorem ownerExpansion_aut_iff {I : Type*} (owner : X → I) (g : Equiv.Perm X) :
    g ∈ (S.ownerExpansion owner).autGroup ↔
      g ∈ S.autGroup ∧ ∀ x, owner (g x) = owner x := by
  constructor
  · rintro ⟨hu,hb⟩
    refine ⟨⟨fun r x => hu (.inl r) x,hb⟩,?_⟩
    intro x
    exact (hu (.inr (owner x)) x).mpr rfl
  · rintro ⟨⟨hu,hb⟩,ho⟩
    refine ⟨?_,hb⟩
    intro r x
    cases r with
    | inl r => exact hu r x
    | inr i => change owner (g x) = i ↔ owner x = i; rw [ho]

end BinaryStructure
end CCO.FiniteKernel
