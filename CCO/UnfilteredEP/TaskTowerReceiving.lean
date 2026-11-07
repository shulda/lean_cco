import CCO.UnfilteredEP.TaskTower
import CCO.UnfilteredEP.TaskPrefixReconstruction

/-! Exact receiving of the finite source tower into full normalized
order witnesses. Every host is chosen before the arbitrary competitor. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- The recursively composed A14 map really forgets precisely the finite
task prefix; the zero prefix has no task symbol at all. -/
theorem taskTowerReduct_data (n : Nat) {V : Type z}
    (C : CCO.ResetOrder.Generic.Structure (taskTowerLanguage B ht n) V) :
    (taskTowerReduct B ht n).data C =
      (taskTowerInclusion B ht (n := 0) (m := n) (Nat.zero_le n)).data C := by
  induction n with
  | zero =>
    apply CCO.ResetOrder.Generic.Structure.ext
      (C := (taskTowerReduct B ht 0).data C)
      (D := (taskTowerInclusion B ht (n := 0) (m := 0) (Nat.zero_le 0)).data C) rfl
    · funext arity F xs
      cases F; rfl
    · funext arity R xs
      cases R with
      | unary U => rfl
      | binary R => cases R with
        | inl R => rfl
        | inr i => exact False.elim (Nat.not_lt_zero _ i.property)
  | succ n ih =>
    change (taskTowerReduct B ht n).data ((taskTowerStep B ht n).data C) = _
    rw [ih]
    apply CCO.ResetOrder.Generic.Structure.ext
      (C := (taskTowerInclusion B ht (n := 0) (m := n) (Nat.zero_le n)).data
        ((taskTowerStep B ht n).data C))
      (D := (taskTowerInclusion B ht (n := 0) (m := n+1) (Nat.zero_le (n+1))).data C) rfl
    · funext arity F xs
      cases F; rfl
    · funext arity R xs
      cases R with
      | unary U => rfl
      | binary R => cases R with
        | inl R => rfl
        | inr i => exact False.elim (Nat.not_lt_zero _ i.property)

/-- Equality of the entire unexpanded old structure is exactly equality
of the zero-task prefix, on the same carrier. -/
theorem taskPrefixData_zero_eq {V : Type z}
    {C D : Structure (OrderedCoordinateLanguage B ht) V}
    (same : C.reduct (coordinateOrderExpansion B ht).toReduct =
      D.reduct (coordinateOrderExpansion B ht).toReduct) :
    taskPrefixData B ht 0 C = taskPrefixData B ht 0 D := by
  apply Structure.ext_data
    (C := taskPrefixData B ht 0 C) (D := taskPrefixData B ht 0 D)
    (congrArg (fun M : Structure (CoordinateLanguage B ht) V => M.sort) same)
    (congrArg (fun M : Structure (CoordinateLanguage B ht) V => M.func) same)
    (congrArg (fun M : Structure (CoordinateLanguage B ht) V => M.unary) same)
  funext R x y
  cases R with
  | inl R => exact congrFun (congrFun (congrArg (fun M => M.binary R) same) x) y
  | inr i => exact False.elim (Nat.not_lt_zero _ i.property)

/-- C70's exact full normalized witness consequence. This is the
receiving bridge for the concrete single-task I12 theorems: the supplied
competitor is arbitrary on the already chosen entire old host. -/
theorem normalized_order_witness_of_taskSteps
    (priority : LinearOrder (Sig B ht).Sorts)
    (singleTask : ∀ i, i < taskCount B ht →
      CCO.ResetOrder.Generic.RelativeEP (taskTowerStep B ht i)
        (taskTowerClass.{u,v,w,z} B ht priority (i+1)) (taskTowerClass B ht priority i))
    (A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht))
    (hA : NormalizedProperAge B ht priority A) :
    ∃ H : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht),
      NormalizedProperAge B ht priority H ∧
      ∀ E : ExpansionOn (coordinateOrderExpansion B ht).toReduct
          (NormalizedProperAge B ht priority) (H.reduct (coordinateOrderExpansion B ht).toReduct),
        Nonempty (Structure.Embedding A.model E.model) := by
  let AN : FiniteHidden (PrefixFullCodeLanguage B ht (taskCount B ht)) :=
    ⟨A.Carrier,taskPrefixData B ht (taskCount B ht) A.model,A.finite⟩
  obtain ⟨host,hhost,witness⟩ := taskTower_relativeEP B ht priority singleTask
    (resetObject _ AN) (taskPrefixData_mem B ht _ A hA)
  obtain ⟨C,hC,he⟩ := hhost
  let H : FiniteHidden (OrderedCoordinateLanguage B ht) := ⟨host.Carrier,C,host.finite⟩
  refine ⟨H,hC,?_⟩
  intro E
  let CN := taskPrefixData B ht (taskCount B ht) E.model
  have red : (taskTowerReduct B ht (taskCount B ht)).data (resetStructure _ CN) = host.data := by
    rw [taskTowerReduct_data]
    have codec : (taskTowerInclusion B ht (n := 0) (m := taskCount B ht) (Nat.zero_le _)).data
          (resetStructure _ CN) =
        resetStructure (PrefixFullCodeLanguage B ht 0)
          (CN.reduct (prefixInclusion B ht (Nat.zero_le (taskCount B ht)))) := by
      apply CCO.ResetOrder.Generic.Structure.ext
        (C := (taskTowerInclusion B ht (n := 0) (m := taskCount B ht) (Nat.zero_le _)).data
          (resetStructure _ CN))
        (D := resetStructure _ (CN.reduct (prefixInclusion B ht (Nat.zero_le (taskCount B ht))))) rfl
      · funext arity F xs
        cases F; rfl
      · funext arity R xs
        cases R with
        | unary U => rfl
        | binary R => cases R <;> rfl
    have full : CN.reduct (prefixInclusion B ht (Nat.zero_le (taskCount B ht))) =
        taskPrefixData B ht 0 C :=
      (taskPrefixData_reduct B ht (Nat.zero_le _) E.model).trans
        (taskPrefixData_zero_eq B ht (C := E.model) (D := C) E.reduct_eq)
    have decoded : CN.reduct (prefixInclusion B ht (Nat.zero_le (taskCount B ht))) =
        resetDecode (PrefixFullCodeLanguage B ht 0) host.data := full.trans he.symm
    exact (codec.trans (congrArg (resetStructure (PrefixFullCodeLanguage B ht 0)) decoded)).trans
      (resetStructure_resetDecode (PrefixFullCodeLanguage B ht 0) host.data)
  let competitor : CCO.ResetOrder.Generic.Expansion
      (taskTowerReduct B ht (taskCount B ht))
      (taskTowerClass B ht priority (taskCount B ht)) host := {
    data := resetStructure _ CN
    member := taskPrefixData_mem B ht _ E.toHidden E.member
    reduct_eq := red }
  obtain ⟨g⟩ := witness competitor
  exact ⟨normalizedFullEmbeddingOfAllTaskPrefix B ht priority hA E.member
    (resetDecodeEmbedding _ g)⟩

end
end CCO.UnfilteredEP
