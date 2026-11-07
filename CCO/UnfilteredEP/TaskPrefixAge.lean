import CCO.UnfilteredEP.TaskPrefixLanguage
import CCO.UnfilteredEP.HierarchyRamsey

/-! Every intermediate class is a literal same-carrier reduct of the ONE
normalized proper hidden class. No intermediate Ramsey assumption occurs. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- An exact same-carrier image class, retaining the full original model
as its membership witness. -/
def TaskPrefixAge (K : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht) → Prop)
    (n : Nat) (A : FiniteHidden.{max u v w,z} (PrefixFullCodeLanguage B ht n)) : Prop :=
  ∃ C : Structure (OrderedCoordinateLanguage B ht) A.Carrier,
    K ⟨A.Carrier,C,A.finite⟩ ∧ A.model = taskPrefixData B ht n C

abbrev NormalizedPrefixAge (priority : LinearOrder (Sig B ht).Sorts) (n : Nat) :=
  TaskPrefixAge B ht (NormalizedProperAge.{u,v,w,z} B ht priority) n

/-- C69: forgetting the next task uses the SAME full normalized object. -/
theorem taskPrefixAge_reduct
    {K : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht) → Prop}
    {n m : Nat} (h : n ≤ m)
    {A : FiniteHidden.{max u v w,z} (PrefixFullCodeLanguage B ht m)}
    (hA : TaskPrefixAge B ht K m A) :
    TaskPrefixAge B ht K n ⟨A.Carrier,A.model.reduct (prefixInclusion B ht h),A.finite⟩ := by
  obtain ⟨C,hC,he⟩ := hA
  refine ⟨C,hC,?_⟩
  rw [he,taskPrefixData_reduct]

/-- Every upper unary function is literally retained at a prefix level.
Thus an induced prefix map has a full-function-closed image. -/
theorem taskPrefix_closed_range {n : Nat} {V W : Type z}
    {A : Structure (PrefixFullCodeLanguage B ht n) V}
    {C : Structure (OrderedCoordinateLanguage B ht) W}
    (e : Structure.Embedding A (taskPrefixData B ht n C)) :
    C.IsClosed (Set.range e.point) := by
  intro F x hx y hy
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,hb,he⟩ := e.reflect_func F a y hy
  exact ⟨b,he⟩

/-- All-induced-map heredity is proved by an actual full closed pullback;
it is not inferred from mere subset heredity. -/
theorem taskPrefixAge_fullHereditary
    {K : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht) → Prop}
    (hK : FullHereditary (OrderedCoordinateLanguage B ht) K) (n : Nat) :
    FullHereditary (PrefixFullCodeLanguage B ht n) (TaskPrefixAge B ht K n) := by
  intro A D hD e
  obtain ⟨C,hC,he⟩ := hD
  let e0 := e.targetCongr he
  let closed := taskPrefix_closed_range B ht e0
  let C0 := C.pullback e0.point e0.injective closed
  let j := C.pullbackEmbedding e0.point e0.injective closed
  refine ⟨C0,hK hC j,?_⟩
  exact (e0.source_eq_of_same_point (taskPrefixEmbedding B ht n j) (fun _ => rfl))

theorem normalizedPrefixAge_fullHereditary
    (priority : LinearOrder (Sig B ht).Sorts) (n : Nat) :
    FullHereditary (PrefixFullCodeLanguage B ht n) (NormalizedPrefixAge.{u,v,w,z} B ht priority n) :=
  taskPrefixAge_fullHereditary B ht
    (fun hD e => normalized_proper_of_embedding B ht priority hD e) n

/-- Every legal full object supplies its literal prefix at every level. -/
theorem taskPrefixData_mem
    {K : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht) → Prop}
    (n : Nat) (C : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)) (hC : K C) :
    TaskPrefixAge B ht K n ⟨C.Carrier,taskPrefixData B ht n C.model,C.finite⟩ :=
  ⟨C.model,hC,rfl⟩

end
end CCO.UnfilteredEP
