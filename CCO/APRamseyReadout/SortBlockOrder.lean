import Mathlib.Data.Prod.Lex
import Mathlib.Order.Basic

/-! Pure concatenation of the old within-sort orders in a fixed sort
priority. No structure, source, Ramsey, clone or term premise is used. -/

universe u v w
namespace CCO.APRamseyReadout
noncomputable section

/-- Lexicographic sorting changes no point or sort label. -/
def sortBlockOrder {I : Type u} {V : Type v} (sort : V → I)
    (priority : LinearOrder I) (old : LinearOrder V) : LinearOrder V := by
  letI := priority
  letI := old
  exact LinearOrder.lift' (fun x => toLex (sort x,x))
    (fun _ _ h => congrArg (fun p => (ofLex p).2) h)

theorem sortBlockOrder_lt_iff {I : Type u} {V : Type v} (sort : V → I)
    (priority : LinearOrder I) (old : LinearOrder V) (x y : V) :
    @LT.lt V (sortBlockOrder sort priority old).toLT x y ↔
      @LT.lt I priority.toLT (sort x) (sort y) ∨
        (sort x = sort y ∧ @LT.lt V old.toLT x y) := by
  letI := priority
  letI := old
  exact Prod.Lex.toLex_lt_toLex

theorem sortBlockOrder_same {I : Type u} {V : Type v} (sort : V → I)
    (priority : LinearOrder I) (old : LinearOrder V) {x y : V} (h : sort x = sort y) :
    @LT.lt V (sortBlockOrder sort priority old).toLT x y ↔ @LT.lt V old.toLT x y := by
  letI := priority
  rw [sortBlockOrder_lt_iff,h]
  simp

theorem sortBlockOrder_different {I : Type u} {V : Type v} (sort : V → I)
    (priority : LinearOrder I) (old : LinearOrder V) {x y : V} (h : sort x ≠ sort y) :
    @LT.lt V (sortBlockOrder sort priority old).toLT x y ↔
      @LT.lt I priority.toLT (sort x) (sort y) := by
  rw [sortBlockOrder_lt_iff]
  simp only [h,false_and,or_false]

theorem sortBlockOrder_idempotent {I : Type u} {V : Type v} (sort : V → I)
    (priority : LinearOrder I) (old : LinearOrder V) :
    sortBlockOrder sort priority (sortBlockOrder sort priority old) = sortBlockOrder sort priority old := by
  letI := priority
  apply LinearOrder.ext_lt
  intro x y
  by_cases h : sort x = sort y
  · rw [sortBlockOrder_same sort priority _ h]
  · rw [sortBlockOrder_different sort priority _ h,sortBlockOrder_different sort priority _ h]

/-- The SAME sort-preserving map remains induced after concatenation. -/
theorem sortBlockOrder_map_iff {I : Type u} {V : Type v} {W : Type w}
    (sortA : V → I) (sortB : W → I) (priority : LinearOrder I)
    (oldA : LinearOrder V) (oldB : LinearOrder W) (f : V → W)
    (hs : ∀ x, sortB (f x) = sortA x)
    (ho : ∀ x y, @LT.lt W oldB.toLT (f x) (f y) ↔ @LT.lt V oldA.toLT x y) (x y : V) :
    @LT.lt W (sortBlockOrder sortB priority oldB).toLT (f x) (f y) ↔
      @LT.lt V (sortBlockOrder sortA priority oldA).toLT x y := by
  rw [sortBlockOrder_lt_iff,sortBlockOrder_lt_iff,hs x,hs y,ho x y]

end
end CCO.APRamseyReadout
