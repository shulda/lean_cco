import CCO.QuotientTransport.Composition
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.PUnit

/-! Actual failures when the elementary transport hypotheses are removed.
The regular cyclic example also distinguishes induced transport from arbitrary
unrelated charts. Universal relations give genuine singleton quotients. -/
namespace CCO.QuotientTransport.Boundaries

theorem empty_kernel_but_no_predecessor :
    (∀ x x' y : Bool, False → False → x = x') ∧
    ¬ Coserial (fun (_ _ : Bool) => False) := by
  constructor
  · intro _ _ _ h; exact h.elim
  · intro h
    exact (h false).choose_spec

namespace Nontransitive
local instance : MulAction Unit Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
local instance : MulAction Unit Unit where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def relation (_ : Unit) (b : Bool) : Prop := b = false
theorem nonempty_invariant_misses_target :
    (∃ a b, relation a b) ∧ Invariant (G := Unit) relation ∧ ¬ Coserial relation := by
  refine ⟨⟨(),false,rfl⟩,fun _ _ _ h => h,?_⟩
  intro h
  obtain ⟨_,hfalse⟩ := h true
  cases hfalse

theorem target_not_transitive : ¬ ∀ x y : Bool, ∃ g : Unit, g • x = y := by
  intro h
  obtain ⟨_,he⟩ := h false true
  cases he
end Nontransitive

theorem full_relation_has_incompatible_predecessors :
    (∃ y : Bool, True ∧ True ∧ (false : Bool) ≠ true) ∧
      ¬ (∀ x x' y : Bool, True → True → x = x') := by
  refine ⟨⟨false,trivial,trivial,by decide⟩,?_⟩
  intro h
  exact Bool.false_ne_true (h false true false trivial trivial)

namespace Cyclic
abbrev C2 := Multiplicative (ZMod 2)
def nonzero : C2 := Multiplicative.ofAdd 1
theorem nonzero_ne : nonzero ≠ 1 := by decide

def equality : InvEq C2 C2 := ⟨⊥,fun _ _ _ h => congrArg _ h⟩
def shift (x y : C2) : Prop := y = x * nonzero
theorem shift_invariant : Invariant (G := C2) shift := by
  intro g x y h
  change g * y = (g * x) * nonzero
  rw [h,mul_assoc]
theorem shift_transport : Transport equality shift where
  serial x := ⟨x * nonzero,rfl⟩
  coserial y := ⟨y * nonzero⁻¹,by simp [shift,mul_assoc]⟩
  invariant := shift_invariant
  kernel x x' y hx hx' := mul_right_cancel (hx.symm.trans hx')

theorem shift_target : shift_transport.target = equality := by
  apply InvEq.ext
  intro y z
  rw [shift_transport.target_iff]
  constructor
  · rintro ⟨x,x',hx,he,hx'⟩
    change x = x' at he
    exact hx.trans ((congrArg (· * nonzero) he).trans hx'.symm)
  · intro he
    change y = z at he
    obtain ⟨x,hx⟩ := shift_transport.coserial y
    exact ⟨x,x,hx,rfl,he ▸ hx⟩

/-- The genuine induced one-letter return is a NONidentity quotient map
when the actual closed word is not contained in the base equivalence. -/
noncomputable def shiftQuotient : Quotient equality.val ≃ Quotient equality.val :=
  shift_transport.quotientEquiv.trans (InvEq.quotientCongr shift_target)

theorem shift_quotient_value (x : C2) :
    shiftQuotient (Quotient.mk'' x) = Quotient.mk'' (x * nonzero) := by
  change InvEq.quotientCongr _ (shift_transport.quotientEquiv _) = _
  rw [shift_transport.quotientEquiv_edge (y := x * nonzero) rfl,InvEq.quotientCongr_mk]

theorem shift_not_identity : (shiftQuotient : Quotient equality.val → Quotient equality.val) ≠ id := by
  intro h
  have he := congrFun h (Quotient.mk'' (1 : C2))
  rw [shift_quotient_value,one_mul] at he
  exact nonzero_ne (Quotient.exact he)

theorem whole_word_not_in_equality : ¬ ∀ x y, shift x y → equality x y := by
  intro h
  have he := h 1 nonzero (by simp [shift])
  exact nonzero_ne he.symm

theorem regular_action_transitive (x y : C2) : ∃ g : C2, g • x = y :=
  ⟨y * x⁻¹,by simp only [smul_eq_mul,mul_assoc,inv_mul_cancel,mul_one]⟩

/-- Even if an identity relation is the valid word, selecting an unrelated
edge chart such as this shift replaces its true identity map by a nonidentity. -/
theorem unrelated_chart_is_not_identity :
    ∃ q : Quotient equality.val, shiftQuotient q ≠ q := by
  by_contra h
  apply shift_not_identity
  funext q
  by_contra hq
  exact h ⟨q,hq⟩
end Cyclic

namespace Collapse
open Cyclic (C2)
def universal : InvEq C2 C2 := ⟨⊤,fun _ _ _ _ => trivial⟩
theorem universal_transport : Transport universal (fun (_ _ : C2) => True) where
  serial _ := ⟨1,trivial⟩
  coserial _ := ⟨1,trivial⟩
  invariant _ _ _ _ := trivial
  kernel _ _ _ _ _ := trivial

theorem universal_target : universal_transport.target = universal := by
  apply InvEq.ext
  intro y z
  constructor
  · intro _; trivial
  · intro _
    exact (universal_transport.target_iff y z).mpr ⟨1,1,trivial,trivial,trivial⟩

theorem singleton_actual_quotients :
    Subsingleton (Quotient universal.val) ∧ Subsingleton (Quotient universal_transport.target.val) := by
  have hs : Subsingleton (Quotient universal.val) := ⟨fun q q' =>
    Quotient.inductionOn₂ q q' (fun _ _ => Quotient.sound trivial)⟩
  refine ⟨hs,?_⟩
  rw [universal_target]
  exact hs
end Collapse
end CCO.QuotientTransport.Boundaries
