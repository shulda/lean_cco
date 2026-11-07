import CCO.UnfilteredEP.TaskEnumeration
import CCO.UnfilteredEP.ParentFormula
import CCO.UnfilteredEP.HierarchyNormalizedAge
import CCO.APRamseyReadout.ResetCodecs
import CCO.APRamseyReadout.TupleScheme
import CCO.FullCode.ExpandedRestriction

/-! Concrete finite task-prefix languages. Every level retains exactly
ALL original unary function symbols, their domains and complete old fine
relations. Only representative task comparison relations are added. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z a
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- Prefixes stabilize beyond the finite number of actual tasks. This
also makes the zero-task branch a literal instance of the same tower. -/
abbrev PrefixTask (n : Nat) := {i : Fin (taskCount B ht) // i.val < n}

def prefixTaskInclusion {n m : Nat} (h : n ≤ m) : PrefixTask B ht n → PrefixTask B ht m :=
  fun i => ⟨i.val,Nat.lt_of_lt_of_le i.property h⟩

abbrev PrefixFullCodeLanguage (n : Nat) : Language.{max u v w} where
  Sorts := (CoordinateLanguage B ht).Sorts
  Func := (CoordinateLanguage B ht).Func
  Unary := (CoordinateLanguage B ht).Unary
  Binary := (CoordinateLanguage B ht).Binary ⊕ PrefixTask B ht n
  input := (CoordinateLanguage B ht).input
  output := (CoordinateLanguage B ht).output
  unarySort := (CoordinateLanguage B ht).unarySort
  leftSort := Sum.elim (CoordinateLanguage B ht).leftSort
    (fun i => hiddenCutSort B ht (taskCut B ht i.val))
  rightSort := Sum.elim (CoordinateLanguage B ht).rightSort
    (fun i => hiddenCutSort B ht (taskCut B ht i.val))
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteUnary := inferInstance
  finiteBinary := inferInstance

def prefixBaseReduct (n : Nat) : Reduct (CoordinateLanguage B ht) (PrefixFullCodeLanguage B ht n) where
  sortMap := id
  funcMap := id
  unaryMap := id
  binaryMap := Sum.inl
  input_eq _ := rfl
  output_eq _ := rfl
  unary_eq _ := rfl
  left_eq _ := rfl
  right_eq _ := rfl

abbrev prefixBase {n : Nat} {V : Type z} (C : Structure (PrefixFullCodeLanguage B ht n) V) :=
  C.reduct (prefixBaseReduct B ht n)

def prefixInclusion {n m : Nat} (h : n ≤ m) :
    Reduct (PrefixFullCodeLanguage B ht n) (PrefixFullCodeLanguage B ht m) where
  sortMap := id
  funcMap := id
  unaryMap := id
  binaryMap := Sum.map id (prefixTaskInclusion B ht h)
  input_eq _ := rfl
  output_eq _ := rfl
  unary_eq _ := rfl
  left_eq R := by cases R <;> rfl
  right_eq R := by cases R <;> rfl

/-- This prefix is read from the entire supplied ordered object. Each
new relation is exactly one representative fibre's task comparison. -/
def taskPrefixData (n : Nat) {V : Type z}
    (C : Structure (OrderedCoordinateLanguage B ht) V) :
    Structure (PrefixFullCodeLanguage B ht n) V where
  sort := C.sort
  func := C.func
  functional := C.functional
  func_sorted := C.func_sorted
  unary := C.unary
  unary_sorted := C.unary_sorted
  binary R x y := match R with
    | .inl R => C.binary (.inl R) x y
    | .inr i => (actualParentFormula B ht (taskCut B ht i.val)).same
        (C.reduct (coordinateOrderExpansion B ht).toReduct) x y ∧
      C.binary (.inr (hiddenCutSort B ht (taskCut B ht i.val),hiddenCutSort B ht (taskCut B ht i.val))) x y
  binary_sorted R x y h := by
    cases R with
    | inl R => exact C.binary_sorted (.inl R) x y h
    | inr i => exact ⟨h.1.1,h.1.2.1⟩

/-- Every old point map is retained, including complete partial unary
graphs. Generic parent-formula naturality holds on ALL structures. -/
def taskPrefixEmbedding (n : Nat) {V : Type z} {W : Type a}
    {C : Structure (OrderedCoordinateLanguage B ht) V}
    {D : Structure (OrderedCoordinateLanguage B ht) W} (e : Structure.Embedding C D) :
    Structure.Embedding (taskPrefixData B ht n C) (taskPrefixData B ht n D) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  unary_iff := e.unary_iff
  binary_iff R x y := by
    cases R with
    | inl R => exact e.binary_iff (.inl R) x y
    | inr i =>
      exact and_congr ((actualParentFormula B ht (taskCut B ht i.val)).same_natural
        (e.reduct (coordinateOrderExpansion B ht).toReduct) x y)
        (e.binary_iff (.inr (_, _)) x y)

/-- Prefix forgetting is strict on the same carrier, not merely an
isomorphism or a newly selected compatible ordered object. -/
theorem taskPrefixData_reduct {n m : Nat} (h : n ≤ m) {V : Type z}
    (C : Structure (OrderedCoordinateLanguage B ht) V) :
    (taskPrefixData B ht m C).reduct (prefixInclusion B ht h) = taskPrefixData B ht n C := by
  apply Structure.ext_data
    (C := (taskPrefixData B ht m C).reduct (prefixInclusion B ht h))
    (D := taskPrefixData B ht n C) rfl rfl rfl
  funext R x y
  cases R <;> rfl

end
end CCO.UnfilteredEP
