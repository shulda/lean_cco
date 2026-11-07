import CCO.UnfilteredEP.ActualTaskFibres
import CCO.UnfilteredEP.NormalizedExpansionAges
import Mathlib.Tactic.FinCases

/-! The ONE full normalized hidden provider in the actual unary task
record language. The old prefix, complete old functions and the entire
global order use identical carriers and point maps. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w z
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)

abbrev normalizedTaskExtra : ResetOrder.Unary.ExtraLanguage (TaskOldSignature B ht n) where
  Func := PEmpty
  Rel := (Sig B ht).Sorts × (Sig B ht).Sorts
  input := PEmpty.elim
  output := PEmpty.elim
  arity _ := 2
  argument p i := if i.val = 0 then p.1 else p.2

def taskPair {V : Type z} (x y : V) : Fin 2 → V :=
  fun i => if i.val = 0 then x else y

theorem taskPair_eta {V : Type z} (xs : Fin 2 → V) :
    taskPair (xs 0) (xs 1) = xs := by
  funext i
  fin_cases i <;> rfl

variable (D : HiddenCut B) (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2))
local notation "P" => actualTaskFibres B ht n D m
local notation "X" => normalizedTaskExtra B ht n

/-- Decode ALL global comparisons, independently of which current task
is being processed. No old unary function is added or removed. -/
def normalizedTaskDecode (A : ResetOrder.Unary.FullObject (P) (X)) :
    Structure (OrderedCoordinateLanguage B ht) A.task.old.Carrier where
  sort := A.task.old.data.sort
  func := A.task.old.data.func
  functional := A.task.old.data.functional
  func_sorted := A.task.old.data.func_sorted
  unary := PEmpty.elim
  unary_sorted U := PEmpty.elim U
  binary R x y := match R with
    | .inl R => (resetUnaryDecode (PrefixFullCodeLanguage B ht n) A.task.old.data).binary (.inl R) x y
    | .inr p => A.rel p (taskPair x y)
  binary_sorted R x y h := by
    cases R with
    | inl R => exact (resetUnaryDecode (PrefixFullCodeLanguage B ht n) A.task.old.data).binary_sorted (.inl R) x y h
    | inr p => exact ⟨A.rel_sorted p _ h 0,A.rel_sorted p _ h 1⟩

def normalizedTaskHidden (A : ResetOrder.Unary.FullObject (P) (X)) :
    FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht) :=
  ⟨A.task.old.Carrier,normalizedTaskDecode B ht n D m A,A.task.old.finite⟩

variable (priority : LinearOrder (Sig B ht).Sorts)

/-- Exactly the same normalized full class, with the literal prefix and
current comparison read from its own complete global order. -/
structure normalizedTaskFullAge (A : ResetOrder.Unary.FullObject (P) (X)) : Prop where
  normalized : NormalizedProperAge B ht priority (normalizedTaskHidden B ht n D m A)
  prefix_eq : resetUnaryDecode (PrefixFullCodeLanguage B ht n) A.task.old.data =
    taskPrefixData B ht n (normalizedTaskDecode B ht n D m A)
  comparison : ∀ x y, A.task.order.lt x y ↔
    (actualParentFormula B ht D).same (taskOldBase B ht n A.task.old) x y ∧
      (normalizedTaskDecode B ht n D m A).binary
        (.inr (hiddenCutSort B ht D,hiddenCutSort B ht D)) x y

/-- Upper task objects are the exact same-carrier image of the full
normalized provider. Later tasks stay available only in that provider. -/
def normalizedTaskUpperAge (A : ResetOrder.Unary.TaskObject (P)) : Prop :=
  ∃ F : ResetOrder.Unary.FullObject (P) (X),
    normalizedTaskFullAge B ht n D m priority F ∧ F.task = A

abbrev normalizedTaskOld (C : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht)) :
    ResetOrder.Unary.Object (TaskOldSignature B ht n) :=
  resetUnaryObject (PrefixFullCodeLanguage B ht n)
    ⟨C.Carrier,taskPrefixData B ht n C.model,C.finite⟩

def normalizedTaskFibreOrder
    (C : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht))
    (hC : NormalizedProperAge B ht priority C) :
    ResetOrder.Unary.FibreOrder (P) (normalizedTaskOld B ht n C) := by
  let Q := normalizedPresentation B ht priority hC
  letI : LinearOrder C.Carrier := Q.order
  have orderIff (x y : C.Carrier) :
      C.model.binary (.inr (hiddenCutSort B ht D,hiddenCutSort B ht D)) x y ↔
        C.model.sort x = hiddenCutSort B ht D ∧ C.model.sort y = hiddenCutSort B ht D ∧ x < y := by
    rw [Q.model_eq]
    rfl
  refine {
    valid := normalized_reduct_member B ht priority C hC
    lt := fun x y => (actualParentFormula B ht D).same
      (taskOldBase B ht n (normalizedTaskOld B ht n C)) x y ∧
      C.model.binary (.inr (hiddenCutSort B ht D,hiddenCutSort B ht D)) x y
    same := And.left
    irrefl := ?_
    trans := ?_
    total := ?_ }
  · intro x h
    exact (@lt_irrefl C.Carrier inferInstance x) ((orderIff x x).mp h.2).2.2
  · intro x y z hxy hyz
    refine ⟨(actualParentFormula B ht D).same_trans _ hxy.1 hyz.1,?_⟩
    have left := (orderIff x y).mp hxy.2
    have right := (orderIff y z).mp hyz.2
    exact (orderIff x z).mpr ⟨left.1,right.2.1,lt_trans left.2.2 right.2.2⟩
  · intro x y same distinct
    have sx : C.model.sort x = hiddenCutSort B ht D := same.1
    have sy : C.model.sort y = hiddenCutSort B ht D := same.2.1
    rcases @lt_or_gt_of_ne C.Carrier inferInstance x y distinct with h | h
    · exact Or.inl ⟨same,(orderIff x y).mpr ⟨sx,sy,h⟩⟩
    · exact Or.inr ⟨(actualParentFormula B ht D).same_symm _ same,
        (orderIff y x).mpr ⟨sy,sx,h⟩⟩

def normalizedTaskFullObject
    (C : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht))
    (hC : NormalizedProperAge B ht priority C) : ResetOrder.Unary.FullObject (P) (X) where
  task := ⟨normalizedTaskOld B ht n C,normalizedTaskFibreOrder B ht n D m priority C hC⟩
  func := PEmpty.elim
  functional F := PEmpty.elim F
  func_sorted F := PEmpty.elim F
  rel p xs := C.model.binary (.inr p) (xs 0) (xs 1)
  rel_sorted p xs h i := by
    have hs := C.model.binary_sorted (.inr p) (xs 0) (xs 1) h
    fin_cases i
    · exact hs.1
    · exact hs.2

theorem normalizedTaskDecode_fullObject
    (C : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht))
    (hC : NormalizedProperAge B ht priority C) :
    normalizedTaskDecode B ht n D m (normalizedTaskFullObject B ht n D m priority C hC) = C.model := by
  apply Structure.ext_data (C := normalizedTaskDecode B ht n D m
    (normalizedTaskFullObject B ht n D m priority C hC)) (D := C.model) rfl rfl
  · funext U
    exact PEmpty.elim U
  · funext R x y
    cases R <;> rfl

theorem normalizedTaskFullObject_mem
    (C : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht))
    (hC : NormalizedProperAge B ht priority C) :
    normalizedTaskFullAge B ht n D m priority
      (normalizedTaskFullObject B ht n D m priority C hC) := by
  constructor
  · change NormalizedProperAge B ht priority ⟨C.Carrier,_,C.finite⟩
    rw [normalizedTaskDecode_fullObject]
    exact hC
  · rw [normalizedTaskDecode_fullObject]
    rfl
  · intro x y
    rw [normalizedTaskDecode_fullObject]
    rfl

end
end CCO.UnfilteredEP
