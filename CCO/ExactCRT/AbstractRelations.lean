import Mathlib.Data.Fin.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Sublattice

/-! B008 C01: represented products of permuting actual equivalences,
class intersections, and the canonical upward quotient maps. No finiteness,
action, exactness, or CCO premise occurs in this file. -/

universe u
namespace CCO.ExactCRT.Abstract

variable {A : Type u}

def comp (E F : A → A → Prop) : A → A → Prop :=
  fun x y => ∃ z, E x z ∧ F z y

def Permutes (E F : Setoid A) : Prop := comp E F = comp F E

/-- A represented product is an actual equivalence under commutation. -/
def productSetoid (E F : Setoid A) (h : Permutes E F) : Setoid A where
  r := comp E F
  iseqv := by
    refine ⟨fun x => ⟨x, E.refl x, F.refl x⟩, ?_, ?_⟩
    · rintro x y ⟨z, hxz, hzy⟩
      have hrev : comp F E y x := ⟨z, F.symm hzy, E.symm hxz⟩
      rw [← h] at hrev
      exact hrev
    · rintro x y z ⟨a, hxa, hay⟩ ⟨b, hyb, hbz⟩
      have hmid : comp F E a b := ⟨y, hay, hyb⟩
      rw [← h] at hmid
      obtain ⟨c, hac, hcb⟩ := hmid
      exact ⟨c, E.trans hxa hac, F.trans hcb hbz⟩

/-- C01: the ambient join is the represented two-step product. -/
theorem join_eq_comp (E F : Setoid A) (h : Permutes E F) :
    (E ⊔ F).r = comp E F := by
  have hE : E ≤ productSetoid E F h := fun _ y hxy => ⟨y, hxy, F.refl y⟩
  have hF : F ≤ productSetoid E F h := fun x _ hxy => ⟨x, E.refl x, hxy⟩
  have hSup : E ⊔ F = productSetoid E F h := by
    apply le_antisymm (sup_le hE hF)
    rintro x y ⟨z, hxz, hzy⟩
    exact (E ⊔ F).trans ((show E ≤ E ⊔ F from le_sup_left) hxz)
      ((show F ≤ E ⊔ F from le_sup_right) hzy)
  exact congrArg (fun J : Setoid A => J.r) hSup

/-- Class compatibility includes repeated centres and relations. -/
theorem class_intersection_iff_join (E F : Setoid A) (h : Permutes E F)
    (x y : A) : (∃ z, E x z ∧ F y z) ↔ (E ⊔ F) x y := by
  rw [show (E ⊔ F) x y ↔ comp E F x y from Iff.of_eq (congrFun (congrFun (join_eq_comp E F h) x) y)]
  constructor <;> rintro ⟨z, hE, hF⟩ <;> exact ⟨z, hE, F.symm hF⟩

/-- C16: literal upward quotient map; every target class has a preimage. -/
def quotientMap {E F : Setoid A} (h : E ≤ F) : Quotient E → Quotient F :=
  Quotient.map id (fun _ _ he => h he)

@[simp] theorem quotientMap_mk {E F : Setoid A} (h : E ≤ F) (x : A) :
    quotientMap h (Quotient.mk E x) = Quotient.mk F x := rfl

theorem quotientMap_surjective {E F : Setoid A} (h : E ≤ F) :
    Function.Surjective (quotientMap h) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨Quotient.mk E x, rfl⟩

/-- The equality of actual images is exactly class intersection. -/
theorem quotient_images_eq_iff (E F : Setoid A) (h : Permutes E F)
    (x y : A) :
    quotientMap (show E ≤ E ⊔ F from le_sup_left) (Quotient.mk E x) =
      quotientMap (show F ≤ E ⊔ F from le_sup_right) (Quotient.mk F y) ↔
      ∃ z, E x z ∧ F y z := by
  change Quotient.mk (E ⊔ F) x = Quotient.mk (E ⊔ F) y ↔ _
  rw [Quotient.eq]
  exact (class_intersection_iff_join E F h x y).symm

variable (S : Sublattice (Setoid A))

def Commutes : Prop := ∀ E F : S, Permutes E.val F.val

/-- Finite families are indexed by Fin n, so the definition includes n=0
without postulating an ambient top member of the sublattice. -/
def ClassHelly : Prop := ∀ n (E : Fin n → S) (centre : Fin n → A),
  (∀ i j, ∃ x, (E i).val (centre i) x ∧ (E j).val (centre j) x) →
    ∃ x, ∀ i, (E i).val (centre i) x

/-- Nonempty internal finite meets use only binary operations. -/
def nonemptyInf : {n : Nat} → (Fin (n + 1) → S) → S
  | 0, E => E 0
  | n + 1, E => E 0 ⊓ nonemptyInf (fun i : Fin (n+1) => E i.succ)

@[simp] theorem nonemptyInf_rel {n : Nat} (E : Fin (n + 1) → S) (x y : A) :
    (nonemptyInf S E).val x y ↔ ∀ i, (E i).val x y := by
  induction n with
  | zero =>
    change (E 0).val x y ↔ _
    constructor
    · intro h i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · intro h
      exact h 0
  | succ n ih =>
    change ((E 0).val x y ∧ (nonemptyInf S (fun i : Fin (n+1) => E i.succ)).val x y) ↔ _
    rw [ih]
    constructor
    · rintro ⟨h0, ht⟩ i
      exact Fin.cases h0 ht i
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

end CCO.ExactCRT.Abstract
