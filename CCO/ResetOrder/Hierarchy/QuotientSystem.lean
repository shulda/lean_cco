import CCO.ResetOrder.Hierarchy.Normalize

/-! ALL coordinates of an actual finite closed quotient object discharge
the recursion's rank and parent-key laws; these are not provider callbacks. -/
universe u v
namespace CCO.ResetOrder.Hierarchy
namespace QuotientSystem
variable {S : Type u} {L : S → Type u} {V : S → Type v}
variable [∀ s, Lattice (L s)] [∀ s, OrderTop (L s)] [∀ s, Fintype (L s)]
def Index := (s : S) × {j : L s // InfIrred j}

structure Priority where
  count : Index (L := L) → ℕ
  enumeration : ∀ i : Index (L := L), Fin (count i) ≃ EquivalenceLattice.CoarserMI i.2.val

variable (P : Priority (L := L))
def coordinate (i : Index (L := L)) (a : Fin (P.count i)) : Index (L := L) :=
  ⟨i.1, (P.enumeration i a).val, (P.enumeration i a).property.2⟩

noncomputable def schedule : Schedule (Index (L := L)) where
  rank i := upperRank i.2.val
  count := P.count
  coordinate := coordinate P
  coordinate_rank i a := upperRank_strict (P.enumeration i a).property.1

variable (R : ∀ s, EquivalenceLattice (L s) (V s))
def AmbientPoint (i : Index (L := L)) := (R i.1).Point i.2.val
def ambientUp (i : Index (L := L)) (a : Fin (P.count i)) :
    AmbientPoint R i → AmbientPoint R (coordinate P i a) :=
  (R i.1).up (P.enumeration i a).property.1.le

structure ClosedObject where
  points : ∀ i, Set (AmbientPoint R i)
  finite : ∀ i, (points i).Finite
  closed_up : ∀ i a x, x ∈ points i → ambientUp P R i a x ∈ points (coordinate P i a)

namespace ClosedObject
variable {P R} (A : ClosedObject P R)
def Carrier (i : Index (L := L)) : Type v := {x // x ∈ A.points i}
instance finiteCarrier (i : Index (L := L)) : Finite (A.Carrier i) := A.finite i

def parent (i : Index (L := L)) (x y : A.Carrier i) : Prop :=
  (R i.1).up (le_miParent i.2.val) x.val = (R i.1).up (le_miParent i.2.val) y.val

def up (i : Index (L := L)) (a : Fin (P.count i)) (x : A.Carrier i) :
    A.Carrier (coordinate P i a) := ⟨ambientUp P R i a x.val, A.closed_up i a x.val x.property⟩

theorem key_parent (i : Index (L := L)) (x y : A.Carrier i) :
    (∀ a, A.up i a x = A.up i a y) ↔ A.parent i x y := by
  constructor
  · intro h
    apply ((R i.1).key_eq_parent_iff i.2.val x.val y.val).1
    funext l
    obtain ⟨a, ha⟩ := (P.enumeration i).surjective l
    subst l
    exact congrArg Subtype.val (h a)
  · intro h a
    apply Subtype.ext
    exact congrFun (((R i.1).key_eq_parent_iff i.2.val x.val y.val).2 h) (P.enumeration i a)

def system : System (schedule P) A.Carrier where
  parent := A.parent
  parent_refl _ _ := rfl
  parent_symm _ := by intro x y h; exact h.symm
  parent_trans _ := by intro x y z h h'; exact h.trans h'
  up := A.up
  key_parent := A.key_parent
end ClosedObject
end QuotientSystem
end CCO.ResetOrder.Hierarchy
