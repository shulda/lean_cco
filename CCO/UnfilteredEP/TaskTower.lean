import CCO.UnfilteredEP.TaskPrefixAge
import CCO.ResetOrder.FiniteTower

/-! C69--C70. The concrete relation-only finite prefix tower, with the
actual normalized image class at EVERY level. The A14 closed-image gate
is discharged by literal unchanged unary function symbols. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

abbrev taskTowerLanguage (n : Nat) := resetLanguage (PrefixFullCodeLanguage B ht n)

abbrev taskTowerClass (priority : LinearOrder (Sig B ht).Sorts) (n : Nat) :=
  resetAge (PrefixFullCodeLanguage B ht n) (NormalizedPrefixAge.{u,v,w,z} B ht priority n)

/-- The exact injective task-symbol map; ALL function names are unchanged. -/
def taskTowerInclusion {n m : Nat} (h : n ≤ m) :
    CCO.ResetOrder.Generic.Reduct (taskTowerLanguage B ht n) (taskTowerLanguage B ht m) where
  func F := match F with | .unary F => .unary F
  rel R := match R with
    | .unary U => .unary U
    | .binary R => .binary ((prefixInclusion B ht h).binaryMap R)
  input F := by cases F; rfl
  output F := by cases F; rfl
  argument R := by
    cases R with
    | unary U => rfl
    | binary R => cases R <;> rfl

abbrev taskTowerStep (n : Nat) := taskTowerInclusion B ht (Nat.le_succ n)

theorem taskTowerInclusion_keepsFunctions {n m : Nat} (h : n ≤ m) :
    (taskTowerInclusion B ht (n := n) (m := m) h).KeepsFunctions := by
  intro arity F
  cases F with | unary F => exact ⟨.unary F,rfl⟩

/-- The generic reset codec commutes with literal prefix forgetting. -/
theorem taskTowerInclusion_decode {n m : Nat} (h : n ≤ m) {V : Type z}
    (C : CCO.ResetOrder.Generic.Structure (taskTowerLanguage B ht m) V) :
    resetDecode (PrefixFullCodeLanguage B ht n) ((taskTowerInclusion B ht (n := n) (m := m) h).data C) =
      (resetDecode (PrefixFullCodeLanguage B ht m) C).reduct (prefixInclusion B ht h) := rfl

theorem taskTowerInclusion_mapsClass
    (priority : LinearOrder (Sig B ht).Sorts) {n m : Nat} (h : n ≤ m) :
    CCO.ResetOrder.Generic.MapsClass (taskTowerInclusion B ht (n := n) (m := m) h)
      (taskTowerClass.{u,v,w,z} B ht priority m) (taskTowerClass B ht priority n) := by
  intro A hA
  exact taskPrefixAge_reduct B ht h hA

theorem taskTowerClass_hereditary
    (priority : LinearOrder (Sig B ht).Sorts) (n : Nat) :
    CCO.ResetOrder.Generic.Hereditary (taskTowerLanguage B ht n)
      (taskTowerClass.{u,v,w,z} B ht priority n) :=
  resetAge_hereditary (PrefixFullCodeLanguage B ht n)
    (normalizedPrefixAge_fullHereditary B ht priority n)

/-- C70's unchanged-function restriction gate is PROVED for these actual
languages, independently of the single-task EP supplied at each level. -/
theorem taskTowerInclusion_restrictionGate
    (priority : LinearOrder (Sig B ht).Sorts) {n m : Nat} (h : n ≤ m) :
    CCO.ResetOrder.Generic.RestrictionGate (taskTowerInclusion B ht (n := n) (m := m) h)
      (taskTowerClass.{u,v,w,z} B ht priority m) (taskTowerClass B ht priority n) :=
  CCO.ResetOrder.Generic.relation_only_restrictionGate _
    (taskTowerInclusion_keepsFunctions B ht h) _ _

/-- The actual n-task composite; zero tasks is the genuine identity case. -/
abbrev taskTowerReduct (n : Nat) :=
  CCO.ResetOrder.Generic.towerReduct (taskTowerLanguage B ht) (taskTowerStep B ht) n

/-- Composition invokes the accepted A14 theorem at EVERY finite level.
The remaining input is precisely the concrete single-task I12 conclusion,
not intermediate Ramsey or a stronger preselected-host statement. -/
theorem taskTower_relativeEP
    (priority : LinearOrder (Sig B ht).Sorts)
    (singleTask : ∀ i, i < taskCount B ht →
      CCO.ResetOrder.Generic.RelativeEP (taskTowerStep B ht i)
        (taskTowerClass.{u,v,w,z} B ht priority (i+1)) (taskTowerClass B ht priority i)) :
    CCO.ResetOrder.Generic.RelativeEP (taskTowerReduct B ht (taskCount B ht))
      (taskTowerClass.{u,v,w,z} B ht priority (taskCount B ht)) (taskTowerClass B ht priority 0) :=
  CCO.ResetOrder.Generic.relation_only_relativeEP_finite_tower
    (taskTowerLanguage B ht) (taskTowerClass B ht priority) (taskTowerStep B ht) (taskCount B ht)
    (fun i _ => taskTowerClass_hereditary B ht priority i)
    (fun i _ => taskTowerInclusion_mapsClass B ht priority (Nat.le_succ i))
    (fun i _ => taskTowerInclusion_keepsFunctions B ht (Nat.le_succ i)) singleTask

end
end CCO.UnfilteredEP
