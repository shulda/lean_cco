import CCO.UnarySupport.Irreducible
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Powerset

universe u v
namespace CCO.UnarySupport.Structure
variable {L : Signature.{u}} {V : Type v} (C : Structure L V)

/-- Each listed set always carries its FULL induced diagram. -/
inductive LocalSupport : Set V → Prop
  | singleton (x : V) : LocalSupport (C.closureAt x)
  | binary (R : L.Rel) (hR : L.arity R = 2) (xs : Fin (L.arity R) → V)
      (hr : C.rel R xs) (hd : ∃ i j, xs i ≠ xs j) : LocalSupport (C.closure (Set.range xs))

theorem localSupport_closed {S : Set V} (h : C.LocalSupport S) : C.IsClosed S := by
  cases h with
  | singleton x => exact C.isClosed_closure {x}
  | binary R hR xs hr hd => exact C.isClosed_closure (Set.range xs)

theorem localSupport_finite [Finite V] : {S | C.LocalSupport S}.Finite := Set.toFinite _

theorem point_support (x : V) : ∃ S, C.LocalSupport S ∧ x ∈ S :=
  ⟨C.closureAt x, .singleton x, C.mem_closureAt x⟩

theorem singleton_func (x : V) (F : L.Func) : C.func F x ⊆ C.closureAt x :=
  C.isClosed_closure {x} F x (C.mem_closureAt x)

/-- Every nonempty displayed tuple of arity at most two has a common
singleton or genuinely displayed binary support. -/
theorem tuple_support (hbin : ∀ R, L.arity R ≤ 2) (R : L.Rel)
    (xs : Fin (L.arity R) → V) (hr : C.rel R xs) (hn : 0 < L.arity R) :
    ∃ S, C.LocalSupport S ∧ ∀ i, xs i ∈ S := by
  classical
  by_cases hd : ∃ i j, xs i ≠ xs j
  · have htwo : L.arity R = 2 := by
      obtain ⟨i, j, hij⟩ := hd
      have hne : i ≠ j := fun h => hij (congrArg xs h)
      have hi := i.isLt
      have hj := j.isLt
      have hb := hbin R
      by_contra h
      have he : i.val = j.val := by omega
      exact hne (Fin.ext he)
    exact ⟨C.closure (Set.range xs), .binary R htwo xs hr hd,
      fun i => C.subset_closure _ ⟨i, rfl⟩⟩
  · let i : Fin (L.arity R) := ⟨0, hn⟩
    refine ⟨C.closureAt (xs i), .singleton (xs i), ?_⟩
    intro j
    have he : xs j = xs i := by by_contra h; exact hd ⟨j, i, h⟩
    rw [he]
    exact C.mem_closureAt _

end CCO.UnarySupport.Structure
