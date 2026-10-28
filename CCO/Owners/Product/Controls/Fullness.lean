import CCO.FiniteKernel.BinarySource
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod

/-! Concrete C27/C28 controls. The original full carrier has every vector
 difference named; the nonfull subset and the additional fine relation
 deliberately violate the respective hypotheses of the product theorem. -/
namespace CCO.Owners.Product.Controls.Fullness
open CCO.FiniteKernel

abbrev Bit := ZMod 2
abbrev Factor := Bit × Bit
abbrev Point := Bit × Bit × Bit

def pD (x : Point) : Factor := (x.1,x.2.1)
def pC (x : Point) : Factor := (x.1,x.2.2)
def owner (x : Factor) : Bit := x.1

def differenceSource (V : Type*) [AddGroup V] : BinaryStructure V where
  Unary := Empty
  Binary := V
  unary e := e.elim
  binary a x y := y - x = a

def flipD : Equiv.Perm Factor where
  toFun x := (x.1,x.2+1)
  invFun x := (x.1,x.2+1)
  left_inv := by decide
  right_inv := by decide

def flip : Equiv.Perm Point where
  toFun x := (x.1,x.2.1+1,x.2.2)
  invFun x := (x.1,x.2.1+1,x.2.2)
  left_inv := by decide
  right_inv := by decide

theorem flipD_difference : ∀ x y : Factor, flipD y - flipD x = y - x := by decide

def flipDAut : (differenceSource Factor).Aut := ⟨flipD,by
  constructor
  · intro e; exact e.elim
  · intro a x y
    change flipD y - flipD x = a ↔ y - x = a
    rw [flipD_difference]⟩

theorem flip_coordinates : ∀ x : Point, pD (flip x) = flipD (pD x) ∧ pC (flip x) = pC x := by decide

theorem matching_owner : ∀ x : Factor, owner (flipDAut.val x) = owner x := by decide

/-- Every compatible coordinate pair occurs in the FULL carrier. -/
theorem full_product : ∀ d c : Factor, owner d = owner c →
    ∃ x : Point, pD x = d ∧ pC x = c := by decide

theorem full_coordinates_injective : Function.Injective (fun x : Point => (pD x,pC x)) := by decide

/-- The sparse subset still has BOTH coordinate maps onto. -/
def sparse (x : Point) : Prop := x.2.1 = x.2.2

instance (x : Point) : Decidable (sparse x) := inferInstanceAs (Decidable (x.2.1 = x.2.2))

theorem sparse_ontoD : ∀ d : Factor, ∃ x : Point, sparse x ∧ pD x = d := by decide

theorem sparse_ontoC : ∀ c : Factor, ∃ x : Point, sparse x ∧ pC x = c := by decide

/-- This is a compatible pair of ACTUAL factor automorphisms, but its
coordinatewise bijection does not restrict to the nonfull subset. -/
theorem sparse_not_preserved :
    sparse (0,0,0) ∧ ¬ sparse (flip (0,0,0)) := by decide

/-- Both coordinate difference colours are preserved on the full set. -/
theorem flip_coordinate_colours : ∀ x y : Point,
    pD (flip y) - pD (flip x) = pD y - pD x ∧
    pC (flip y) - pC (flip x) = pC y - pC x := by decide

def extra (x y : Point) : Prop := x.2.1 = y.2.2 ∧ x.2.2 = y.2.1

instance (x y : Point) : Decidable (extra x y) :=
  inferInstanceAs (Decidable (x.2.1 = y.2.2 ∧ x.2.2 = y.2.1))

def refinedSource : BinaryStructure Point where
  Unary := Empty
  Binary := Point ⊕ Unit
  unary e := e.elim
  binary
    | .inl a,x,y => y-x=a
    | .inr _,x,y => extra x y

/-- Fullness survives; exact fine-colour reconstruction fails. -/
theorem extra_not_preserved :
    extra (0,0,0) (1,0,0) ∧ ¬ extra (flip (0,0,0)) (flip (1,0,0)) := by decide

theorem flip_not_refined_aut : flip ∉ refinedSource.autGroup := by
  intro h
  have hh := h.2 (.inr ()) (0,0,0) (1,0,0)
  exact extra_not_preserved.2 (hh.mpr extra_not_preserved.1)

/-- The unchanged fine difference structure DOES admit the same bijection. -/
def flipAut : (differenceSource Point).Aut := ⟨flip,by
  constructor
  · intro e; exact e.elim
  · intro a x y
    change flip y - flip x = a ↔ y - x = a
    have hdiff : ∀ x y : Point, flip y - flip x = y - x := by decide
    rw [hdiff]⟩

theorem sparse_card : Fintype.card {x : Point // sparse x} = 4 := by decide

theorem full_card : Fintype.card Point = 8 := by decide

/-- C27 as one downstream premise-boundary consumer. -/
theorem nonfull_control :
    (∀ d : Factor, ∃ x : Point, sparse x ∧ pD x = d) ∧
    (∀ c : Factor, ∃ x : Point, sparse x ∧ pC x = c) ∧
    (∀ d : Factor, owner (flipDAut.val d) = owner d) ∧
    (∃ x : Point, sparse x ∧ ¬ sparse (flip x)) :=
  ⟨sparse_ontoD,sparse_ontoC,matching_owner,⟨(0,0,0),sparse_not_preserved⟩⟩

/-- C28 retains the full carrier and BOTH coordinate colours, but the
compatible coordinate pair fails to be a fine-structure automorphism. -/
theorem extra_colour_control :
    (∀ d c : Factor, owner d = owner c → ∃ x : Point, pD x = d ∧ pC x = c) ∧
    (∀ x y : Point, pD (flip y)-pD (flip x)=pD y-pD x ∧
      pC (flip y)-pC (flip x)=pC y-pC x) ∧
    flip ∉ refinedSource.autGroup :=
  ⟨full_product,flip_coordinate_colours,flip_not_refined_aut⟩

end CCO.Owners.Product.Controls.Fullness
