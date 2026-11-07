import CCO.UnfilteredEP.NormalizedTaskArrows
import CCO.UnfilteredEP.TaskPrefixAge

/-! Concrete elementary setting fields for the relative single-task
criterion. The lower class is the literal normalized prefix image. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w a b
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section

section General
variable {L : ResetOrder.Unary.Primitive.Signature.{a}}
variable (P : ResetOrder.Unary.Fibres.{a,b} L)

def taskFibreOrderPullback {A C : ResetOrder.Unary.Object.{a,b} L}
    (f : A.Emb C) (o : ResetOrder.Unary.FibreOrder P C) :
    ResetOrder.Unary.FibreOrder P A where
  valid := P.hereditary o.valid ⟨f⟩
  lt x y := o.lt (f.point x) (f.point y)
  same h := (P.same_natural f _ _).mp (o.same h)
  irrefl x := o.irrefl (f.point x)
  trans hxy hyz := o.trans hxy hyz
  total same distinct := o.total ((P.same_natural f _ _).mpr same)
    (fun equal => distinct (f.injective equal))

theorem finite_task_fibre_orders (A : ResetOrder.Unary.Object.{a,b} L) :
    Finite (ResetOrder.Unary.FibreOrder P A) := by
  apply Finite.of_injective (fun o : ResetOrder.Unary.FibreOrder P A => o.lt)
  intro o p equal
  cases o
  cases p
  cases equal
  rfl

end General

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)
variable (D : HiddenCut B) (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2))
variable (priority : LinearOrder (Sig B ht).Sorts)

abbrev normalizedTaskLowerAge := resetUnaryAge (PrefixFullCodeLanguage B ht n)
  (NormalizedPrefixAge.{u,v,w,max u v} B ht priority n)

theorem normalized_task_lower_hereditary :
    ResetOrder.Unary.Hereditary (normalizedTaskLowerAge B ht n priority) :=
  resetUnaryAge_hereditary (PrefixFullCodeLanguage B ht n)
    (normalizedPrefixAge_fullHereditary B ht priority n)

theorem normalized_task_reduct
    (A : ResetOrder.Unary.TaskObject (actualTaskFibres B ht n D m))
    (member : normalizedTaskUpperAge B ht n D m priority A) :
    normalizedTaskLowerAge B ht n priority A.old := by
  obtain ⟨F,hF,equal⟩ := member
  subst A
  exact ⟨normalizedTaskDecode B ht n D m F,hF.normalized,hF.prefix_eq⟩

/-- Every supplied lower-prefix object lifts on its own literal carrier.
Only an old-model equality is transported; all point maps are identity. -/
theorem normalized_task_onto
    (A : ResetOrder.Unary.Object (TaskOldSignature B ht n))
    (member : normalizedTaskLowerAge B ht n priority A) :
    ∃ o : ResetOrder.Unary.FibreOrder (actualTaskFibres B ht n D m) A,
      normalizedTaskUpperAge B ht n D m priority ⟨A,o⟩ := by
  obtain ⟨C,hC,equal⟩ := member
  let source : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht) :=
    ⟨A.Carrier,C,A.finite⟩
  let F := normalizedTaskFullObject B ht n D m priority source hC
  let old : A.Emb F.task.old := resetUnaryEmbeddingOfDecode (PrefixFullCodeLanguage B ht n)
    ((Structure.Embedding.id (resetUnaryDecode (PrefixFullCodeLanguage B ht n) A.data)).targetCongr equal)
  let o := taskFibreOrderPullback (actualTaskFibres B ht n D m) old F.task.order
  let f : ResetOrder.Unary.TaskHom ⟨A,o⟩ F.task := ⟨old,fun _ _ => Iff.rfl⟩
  refine ⟨o,normalizedTaskPullback B ht n D m f,?_,rfl⟩
  exact normalized_task_full_hereditary B ht n D m priority
    (normalizedTaskFullObject_mem B ht n D m priority source hC)
    ⟨normalizedTaskPullbackMap B ht n D m f⟩

theorem normalized_task_precompact :
    ResetOrder.Unary.TaskPrecompact (normalizedTaskUpperAge B ht n D m priority)
      (normalizedTaskLowerAge B ht n priority) := by
  intro A _member
  let : Finite (ResetOrder.Unary.FibreOrder (actualTaskFibres B ht n D m) A) :=
    finite_task_fibre_orders (actualTaskFibres B ht n D m) A
  infer_instance

end
end CCO.UnfilteredEP
