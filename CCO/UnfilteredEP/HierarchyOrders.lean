import CCO.UnfilteredEP.HierarchyCharting
import CCO.ResetOrder.Hierarchy.SortPriority
import Mathlib.Order.RelClasses
import Mathlib.Logic.Equiv.Defs

/-!
# B064 C44: legal hierarchical orders on the SAME proper hidden carrier

The finite input order supplies only the independent representative-fibre
tasks. The accepted recursion rebuilds all strict-coarser parent-key
comparisons and synchronizes transition copies. A fixed priority of actual
hidden SORT symbols concatenates the resulting sort orders. No new point,
function or cylinder is introduced.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ResetOrder.Hierarchy
noncomputable section

/-- View an actual linear order as the strict-total order used by B036. -/
def strictOrderOfLinear {V : Type z} (o : LinearOrder V) : TotalOrder V where
  lt := @LT.lt _ o.toLT
  irrefl := @lt_irrefl _ o.toPreorder
  trans := @lt_trans _ o.toPreorder
  total := by
    intro x y h
    exact (@lt_or_gt_of_ne _ o x y h)

/-- Return from the generic strict-total order without changing its
literal comparison relation. -/
@[instance_reducible] def linearOrderOfStrict {V : Type z} (o : TotalOrder V) : LinearOrder V := by
  classical
  letI : IsStrictTotalOrder V o.lt := {
    irrefl := o.irrefl
    trans := fun _ _ _ => o.trans
    trichotomous := fun x y hxy hyx => by
      by_contra he
      exact (o.total he).elim hxy hyx }
  exact linearOrderOfSTO o.lt

@[simp] theorem linearOrderOfStrict_lt {V : Type z} (o : TotalOrder V) (x y : V) :
    @LT.lt _ (linearOrderOfStrict o).toLT x y ↔ o.lt x y := Iff.rfl

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

theorem hiddenCutSort_injective : Function.Injective (hiddenCutSort B ht) := by
  rintro ⟨i,D⟩ ⟨j,E⟩ h
  have hs := congrArg ULift.down h
  change (⟨i,Sum.inr D⟩ : CCO.UnaryTermsReturn.OriginalCompletedCoordinateCode (cloneSource B) (HF B)) =
    ⟨j,Sum.inr E⟩ at hs
  cases hs
  rfl

/-- Decode a proper SORT symbol. No quotient value or real representative
is chosen by this operation. -/
def cutOfProperSort (s : (Sig B ht).Sorts) (hs : ProperSort B ht s) : HiddenCut B := by
  rcases s with ⟨⟨i,c⟩⟩
  cases c with
  | inl c => exact hs.elim
  | inr D => exact ⟨i,D⟩

theorem cutOfProperSort_sort (s : (Sig B ht).Sorts) (hs : ProperSort B ht s) :
    hiddenCutSort B ht (cutOfProperSort B ht s hs) = s := by
  rcases s with ⟨⟨i,c⟩⟩
  cases c with
  | inl c => exact hs.elim
  | inr D => rfl

variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (hproper : ∀ x, ProperSort B ht (C.sort x))

def cutCarrierEquiv : V ≃ Sigma (HiddenCutCarrier B ht C) where
  toFun x := ⟨cutOfProperSort B ht (C.sort x) (hproper x),x,
    (cutOfProperSort_sort B ht (C.sort x) (hproper x)).symm⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨D,x,hx⟩
    have hD : cutOfProperSort B ht (C.sort x) (hproper x) = D :=
      hiddenCutSort_injective B ht ((cutOfProperSort_sort B ht (C.sort x) (hproper x)).trans hx)
    cases hD
    rfl

/-- Reindex only the sort symbols by the fixed transition orbits. -/
def orbitCarrierEquiv :
    V ≃ Sigma (fun i => HiddenCutCarrier B ht C (cutOrbitEquiv B ht i)) :=
  (cutCarrierEquiv B ht C hproper).trans (Equiv.sigmaCongrLeft (cutOrbitEquiv B ht)).symm

@[simp] theorem orbitCarrierEquiv_symm (x : Sigma (fun i => HiddenCutCarrier B ht C (cutOrbitEquiv B ht i))) :
    (orbitCarrierEquiv B ht C hproper).symm x = x.2.val := rfl

variable (hC : ActualAge B ht C)

/-- Input full orders restrict to every actual named quotient sort. -/
def cutInputOrders (o : LinearOrder V) : (reindexedCutSystem B ht C hC).Orders :=
  fun _ => (strictOrderOfLinear o).pullback Subtype.val Subtype.val_injective

/-- The actual fixed coarse-first, transition-synchronized order family. -/
def normalizedCutOrders (o : LinearOrder V) : (reindexedCutSystem B ht C hC).Orders :=
  (actualCutCharting B ht C hC).normalize (cutInputOrders B ht C hC o)

/-- The priority is on original actual hidden SORT symbols; it is fixed
independently of chart values, finite members and their input orders. -/
def orbitSortPriority (priority : LinearOrder (Sig B ht).Sorts) :
    TotalOrder (Sigma (CutInOrbit B ht)) :=
  (strictOrderOfLinear priority).pullback
    (fun i => hiddenCutSort B ht (cutOrbitEquiv B ht i))
    ((hiddenCutSort_injective B ht).comp (cutOrbitEquiv B ht).injective)

def hierarchicalTotalOrder (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V) :
    TotalOrder V :=
  (sortOrder (orbitSortPriority B ht priority) (normalizedCutOrders B ht C hC o)).pullback
    (orbitCarrierEquiv B ht C hproper) (orbitCarrierEquiv B ht C hproper).injective

@[instance_reducible] def hierarchicalOrder (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V) :
    LinearOrder V := linearOrderOfStrict (hierarchicalTotalOrder B ht C hproper hC priority o)

/-- On one actual named sort, the global normalized comparison is
exactly its reconstructed hierarchical sort comparison. -/
theorem hierarchicalOrder_same (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V)
    (i : Sigma (CutInOrbit B ht))
    (x y : HiddenCutCarrier B ht C (cutOrbitEquiv B ht i)) :
    @LT.lt _ (hierarchicalOrder B ht C hproper hC priority o).toLT x.val y.val ↔
      (normalizedCutOrders B ht C hC o i).lt x y := by
  change (sortOrder (orbitSortPriority B ht priority) (normalizedCutOrders B ht C hC o)).lt
    (orbitCarrierEquiv B ht C hproper x.val) (orbitCarrierEquiv B ht C hproper y.val) ↔ _
  have hx := (orbitCarrierEquiv B ht C hproper).apply_symm_apply ⟨i,x⟩
  have hy := (orbitCarrierEquiv B ht C hproper).apply_symm_apply ⟨i,y⟩
  rw [orbitCarrierEquiv_symm] at hx hy
  rw [hx,hy]
  exact sortOrder_same (orbitSortPriority B ht priority) (normalizedCutOrders B ht C hC o) i x y

/-- The whole coarse-key/transition-synchronized family is recovered
exactly when the resulting global order is read back on its sorts. -/
theorem cutInputOrders_hierarchical (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V) :
    cutInputOrders B ht C hC (hierarchicalOrder B ht C hproper hC priority o) =
      normalizedCutOrders B ht C hC o := by
  funext i
  apply TotalOrder.ext
  intro x y
  exact hierarchicalOrder_same B ht C hproper hC priority o i x y

/-- Strict idempotence holds as equality of the entire comparison
relation on the original carrier, with the same fixed sort priority. -/
theorem hierarchicalOrder_idempotent (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V) :
    hierarchicalOrder B ht C hproper hC priority
      (hierarchicalOrder B ht C hproper hC priority o) =
      hierarchicalOrder B ht C hproper hC priority o := by
  have horders : normalizedCutOrders B ht C hC
      (hierarchicalOrder B ht C hproper hC priority o) = normalizedCutOrders B ht C hC o := by
    unfold normalizedCutOrders
    rw [cutInputOrders_hierarchical]
    exact (actualCutCharting B ht C hC).normalize_idempotent _
  apply LinearOrder.ext_lt
  intro x y
  change (sortOrder (orbitSortPriority B ht priority)
    (normalizedCutOrders B ht C hC (hierarchicalOrder B ht C hproper hC priority o))).lt
      (orbitCarrierEquiv B ht C hproper x) (orbitCarrierEquiv B ht C hproper y) ↔ _
  rw [horders]
  rfl

end
end CCO.UnfilteredEP
