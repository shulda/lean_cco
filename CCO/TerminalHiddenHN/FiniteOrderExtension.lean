import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.WithBot

/-! Pure finite order extension along the supplied injective map.
The original order is preserved AND reflected on that exact image.
No hidden-structure, completion or Ramsey premise enters this step. -/

universe u v
namespace CCO.TerminalHiddenHN

/-- Extend the exact old order along an arbitrary supplied injection
into a finite carrier, including empty sources and targets. -/
theorem finite_linearOrder_extension {A : Type u} {B : Type v}
    [oldOrder : LinearOrder A] [Finite B] (f : A → B) (hf : Function.Injective f) :
    ∃ o : LinearOrder B, ∀ x y,
      @LT.lt B o.toLT (f x) (f y) ↔ @LT.lt A oldOrder.toLT x y := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  let label : B → WithBot A := fun z =>
    if h : ∃ x, f x = z then ((Classical.choose h : A) : WithBot A) else ⊥
  have hlabel (x : A) : label (f x) = (x : WithBot A) := by
    have hx : ∃ y, f y = f x := ⟨x,rfl⟩
    simp only [label,dite_eq_left hx]
    exact congrArg (fun y : A => (y : WithBot A)) (hf (Classical.choose_spec hx))
  let key : B → WithBot A ×ₗ Fin (Fintype.card B) :=
    fun z => toLex (label z,Fintype.equivFin B z)
  have hkey : Function.Injective key := by
    intro x y hxy
    exact (Fintype.equivFin B).injective (congrArg (fun p => (ofLex p).2) hxy)
  let o : LinearOrder B := LinearOrder.lift' key hkey
  have hstrict : ∀ x y : A, x < y → @LT.lt B o.toLT (f x) (f y) := by
    intro x y hxy
    change key (f x) < key (f y)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    change label (f x) < label (f y)
    rw [hlabel,hlabel]
    exact WithBot.coe_lt_coe.mpr hxy
  refine ⟨o,?_⟩
  letI : LinearOrder B := o
  have hm : StrictMono f := hstrict
  exact fun _ _ => hm.lt_iff_lt

/-- In particular, the existing order on an actual finite subset
extends to the ambient finite carrier through literal Subtype.val. -/
theorem finite_subset_order_extension {B : Type v} [Finite B]
    (A : Set B) [oldOrder : LinearOrder A] :
    ∃ o : LinearOrder B, ∀ x y : A,
      @LT.lt B o.toLT x.val y.val ↔ @LT.lt A oldOrder.toLT x y :=
  finite_linearOrder_extension (A := A) (B := B) (oldOrder := oldOrder)
    (@Subtype.val B A) Subtype.val_injective

/-- The same statement for literal inclusion of two actual subsets.
Closed hidden subsets can use this directly with their proved inclusion;
neither closedness nor any ambient structure is needed by the proof. -/
theorem finite_subset_inclusion_order_extension {V : Type u}
    {A B : Set V} [oldOrder : LinearOrder A] [Finite B] (hAB : A ⊆ B) :
    ∃ o : LinearOrder B, ∀ x y : A,
      @LT.lt B o.toLT ⟨x.val,hAB x.property⟩ ⟨y.val,hAB y.property⟩ ↔
        @LT.lt A oldOrder.toLT x y := by
  apply finite_linearOrder_extension (oldOrder := oldOrder)
    (fun x : A => (⟨x.val,hAB x.property⟩ : B))
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : B => z.val) hxy)

end CCO.TerminalHiddenHN
