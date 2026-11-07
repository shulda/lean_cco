import CCO.UnfilteredEP.TaskPrefixAge
import CCO.UnfilteredEP.HierarchyTaskMaps

/-! C69--C70 final receiving map: all independent representative tasks
recover the entire normalized global order on the SAME supplied map. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z a
namespace CCO.UnfilteredEP
open CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)
variable {V : Type z} {W : Type a}
variable (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (D : CCO.UnarySupport.Structure (Sig B ht) W)
variable (hC : ActualAge B ht C) (hD : ActualAge B ht D)
variable (properC : ∀ x, ProperSort B ht (C.sort x))
variable (properD : ∀ x, ProperSort B ht (D.sort x))
variable (oC : LinearOrder V) (oD : LinearOrder W)
variable (fixedC : hierarchicalOrder B ht C properC hC priority oC = oC)
variable (fixedD : hierarchicalOrder B ht D properD hD priority oD = oD)
variable (e : Structure.Embedding
  (taskPrefixData B ht (taskCount B ht) (@OrderedCoordinateModel B ht V C oC))
  (taskPrefixData B ht (taskCount B ht) (@OrderedCoordinateModel B ht W D oD)))

include hC hD properC properD fixedC fixedD in
/-- No full-order premise is hidden in the final-prefix map. -/
theorem allTaskPrefix_order_iff (x y : V) :
    @LT.lt _ oD.toLT (e.point x) (e.point y) ↔ @LT.lt _ oC.toLT x y := by
  let raw := CCO.TerminalHiddenHN.binaryEmbeddingInverse (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) (e.reduct (prefixBaseReduct B ht (taskCount B ht)))
  apply hierarchy_fixed_map_of_representative_tasks B ht hC hD raw oC oD
    properC properD priority fixedC fixedD
  intro r p q hp hlt
  obtain ⟨i,rfl⟩ := (taskEnumeration B ht).surjective r
  let k : PrefixTask B ht (taskCount B ht) := ⟨i,i.isLt⟩
  have hs := (actualParentFormula_same_iff B ht C hC (taskCut B ht i) p q).mpr hp
  have hbin : (taskPrefixData B ht (taskCount B ht)
      (@OrderedCoordinateModel B ht V C oC)).binary (.inr k) p.val q.val :=
    ⟨hs,p.property,q.property,hlt⟩
  exact ((e.binary_iff (.inr k) p.val q.val).mpr hbin).2.2.2

include hC hD properC properD fixedC fixedD in
/-- The complete expanded induced embedding retains all old data and
uses literally the given final-prefix point map. -/
def fullEmbeddingOfAllTaskPrefix :
    Structure.Embedding (@OrderedCoordinateModel B ht V C oC)
      (@OrderedCoordinateModel B ht W D oD) where
  point := e.point
  injective := e.injective
  sort_eq := e.sort_eq
  map_func := e.map_func
  reflect_func := e.reflect_func
  unary_iff := e.unary_iff
  binary_iff R x y := by
    cases R with
    | inl R => exact e.binary_iff (.inl R) x y
    | inr p =>
      change (D.sort (e.point x) = p.1 ∧ D.sort (e.point y) = p.2 ∧
        @LT.lt _ oD.toLT (e.point x) (e.point y)) ↔
        (C.sort x = p.1 ∧ C.sort y = p.2 ∧ @LT.lt _ oC.toLT x y)
      have hx : D.sort (e.point x) = C.sort x := e.sort_eq x
      have hy : D.sort (e.point y) = C.sort y := e.sort_eq y
      rw [hx,hy]
      exact and_congr Iff.rfl (and_congr Iff.rfl
        (allTaskPrefix_order_iff B ht priority C D hC hD properC properD oC oD fixedC fixedD e x y))

/-- Exact same-map receiving theorem for the ONE actual normalized age. -/
def normalizedFullEmbeddingOfAllTaskPrefix
    {A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)}
    {D : FiniteHidden.{max u v w,a} (OrderedCoordinateLanguage B ht)}
    (hA : NormalizedProperAge B ht priority A) (hD : NormalizedProperAge B ht priority D)
    (f : Structure.Embedding (taskPrefixData B ht (taskCount B ht) A.model)
      (taskPrefixData B ht (taskCount B ht) D.model)) :
    Structure.Embedding A.model D.model := by
  let P := normalizedPresentation B ht priority hA
  let Q := normalizedPresentation B ht priority hD
  let f0 := FullEmbedding.castModels f
    (congrArg (taskPrefixData B ht (taskCount B ht)) P.model_eq)
    (congrArg (taskPrefixData B ht (taskCount B ht)) Q.model_eq)
  let g := fullEmbeddingOfAllTaskPrefix B ht priority P.raw Q.raw P.actual Q.actual
    P.proper Q.proper P.order Q.order P.fixed Q.fixed f0
  exact FullEmbedding.castModels g P.model_eq.symm Q.model_eq.symm

@[simp] theorem normalizedFullEmbeddingOfAllTaskPrefix_point
    {A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)}
    {D : FiniteHidden.{max u v w,a} (OrderedCoordinateLanguage B ht)}
    (hA : NormalizedProperAge B ht priority A) (hD : NormalizedProperAge B ht priority D)
    (f : Structure.Embedding (taskPrefixData B ht (taskCount B ht) A.model)
      (taskPrefixData B ht (taskCount B ht) D.model)) (x : A.Carrier) :
    (normalizedFullEmbeddingOfAllTaskPrefix B ht priority hA hD f).point x = f.point x := by
  simp only [normalizedFullEmbeddingOfAllTaskPrefix,FullEmbedding.castModels_point,
    fullEmbeddingOfAllTaskPrefix]

end
end CCO.UnfilteredEP
