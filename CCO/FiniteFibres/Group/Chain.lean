import Mathlib.Order.Atoms.Finite
import Mathlib.Order.Fin.Basic

/-! C32/C33: a genuine finite saturated chain and explicit telescoping of
its relative counts. No group, source homogeneity or CCO is used here. -/
namespace CCO.FiniteFibres.Group
variable {α : Type*} [PartialOrder α]

structure SaturatedChain (a b : α) where
  length : ℕ
  point : Fin (length+1) → α
  first : point 0 = a
  last : point (Fin.last length) = b
  covers : ∀ i : Fin length, point i.castSucc ⋖ point i.succ

namespace SaturatedChain

def nil (a : α) : SaturatedChain a a where
  length := 0
  point := fun _ => a
  first := rfl
  last := rfl
  covers := Fin.elim0

def prepend {a b c : α} (h : a ⋖ c) (C : SaturatedChain c b) : SaturatedChain a b where
  length := C.length+1
  point := Fin.cases a C.point
  first := rfl
  last := by
    change Fin.cases a C.point ((Fin.last C.length).succ) = b
    simpa only [Fin.cases_succ] using C.last
  covers := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.castSucc_zero,Fin.cases_zero,Fin.cases_succ,C.first] using h
    · simpa only [Fin.castSucc_succ,Fin.cases_succ] using C.covers j

theorem monotone {a b : α} (C : SaturatedChain a b) : Monotone C.point :=
  Fin.monotone_iff_le_succ.mpr (fun i => (C.covers i).le)

theorem strictMono {a b : α} (C : SaturatedChain a b) : StrictMono C.point :=
  Fin.strictMono_iff_lt_succ.mpr (fun i => (C.covers i).lt)

theorem exists_between [Finite α] (a b : α) (hab : a ≤ b) : Nonempty (SaturatedChain a b) := by
  classical
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    by_cases heq : a = b
    · subst b
      exact ⟨nil a⟩
    obtain ⟨c,hac,hcb⟩ := exists_covBy_le_of_lt (lt_of_le_of_ne hab heq)
    obtain ⟨C⟩ := ih c hac.lt hcb
    exact ⟨prepend hac C⟩

/-- Relative multiplicities telescope at EVERY intermediate chain index. -/
theorem telescope {a b : α} (C : SaturatedChain a b) (w : α → ℕ) (p : ℕ)
    (hstep : ∀ i : Fin C.length, w (C.point i.castSucc) = p*w (C.point i.succ)) :
    w a = p^C.length*w b := by
  have h : ∀ k : Fin (C.length+1), w (C.point 0) = p^k.val*w (C.point k) := by
    intro k
    induction k using Fin.induction with
    | zero => simp
    | succ k ih =>
      calc
        w (C.point 0) = p^k.val*w (C.point k.castSucc) := ih
        _ = p^k.val*(p*w (C.point k.succ)) := congrArg (fun z => p^k.val*z) (hstep k)
        _ = p^k.succ.val*w (C.point k.succ) := by rw [Fin.val_succ,pow_succ,Nat.mul_assoc]
  simpa only [C.first,C.last,Fin.val_last] using h (Fin.last C.length)

end SaturatedChain
end CCO.FiniteFibres.Group
