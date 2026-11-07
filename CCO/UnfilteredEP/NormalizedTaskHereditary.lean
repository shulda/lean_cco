import CCO.UnfilteredEP.NormalizedTaskMaps

/-! Heredity of the ONE full task provider and its actual upper task
image. Restriction lifts are constructed on the source carrier. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)
variable (D : HiddenCut B) (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2))
variable (priority : LinearOrder (Sig B ht).Sorts)
local notation "P" => actualTaskFibres B ht n D m
local notation "X" => normalizedTaskExtra B ht n

theorem normalized_task_full_hereditary :
    ResetOrder.Unary.FullHereditary (normalizedTaskFullAge B ht n D m priority) := by
  intro A C hA maps
  obtain ⟨f⟩ := maps
  let g := normalizedTaskDecodeMap B ht n D m f
  refine ⟨normalized_proper_of_embedding B ht priority hA.normalized g,?_,?_⟩
  · let old := resetUnaryDecodeEmbedding (PrefixFullCodeLanguage B ht n) f.task.old
    let full := (taskPrefixEmbedding B ht n g).targetCongr hA.prefix_eq.symm
    exact old.source_eq_of_same_point full (fun _ => rfl)
  · intro x y
    have h := f.task.order_iff x y
    rw [hA.comparison] at h
    exact h.symm.trans (and_congr
      ((actualParentFormula B ht D).same_natural (taskOldBaseEmbedding B ht n f.task.old) x y)
      (g.binary_iff (.inr (hiddenCutSort B ht D,hiddenCutSort B ht D)) x y))

/-- Lift a prescribed task map to a full restriction of its target,
retaining the source task and every pulled-back full order relation. -/
def normalizedTaskPullback
    {A : ResetOrder.Unary.TaskObject (P)} {C : ResetOrder.Unary.FullObject (P) (X)}
    (f : ResetOrder.Unary.TaskHom A C.task) : ResetOrder.Unary.FullObject (P) (X) where
  task := A
  func := PEmpty.elim
  functional F := PEmpty.elim F
  func_sorted F := PEmpty.elim F
  rel R xs := C.rel R (f.old.point ∘ xs)
  rel_sorted R xs h i := by
    have hh := C.rel_sorted R (f.old.point ∘ xs) h i
    exact (f.old.sort_eq (xs i)).symm.trans hh

def normalizedTaskPullbackMap
    {A : ResetOrder.Unary.TaskObject (P)} {C : ResetOrder.Unary.FullObject (P) (X)}
    (f : ResetOrder.Unary.TaskHom A C.task) :
    ResetOrder.Unary.FullHom (normalizedTaskPullback B ht n D m f) C where
  task := f
  map_func F := PEmpty.elim F
  reflect_func F := PEmpty.elim F
  rel_iff _ _ := Iff.rfl

theorem normalized_task_upper_hereditary :
    ResetOrder.Unary.TaskHereditary (normalizedTaskUpperAge B ht n D m priority) := by
  intro A C hA maps
  obtain ⟨F,hF,equal⟩ := hA
  subst A
  obtain ⟨f⟩ := maps
  exact ⟨normalizedTaskPullback B ht n D m f,
    normalized_task_full_hereditary B ht n D m priority hF
      ⟨normalizedTaskPullbackMap B ht n D m f⟩,rfl⟩

theorem normalized_task_full_reduct
    (F : ResetOrder.Unary.FullObject (P) (X))
    (member : normalizedTaskFullAge B ht n D m priority F) :
    normalizedTaskUpperAge B ht n D m priority F.task := ⟨F,member,rfl⟩

theorem normalized_task_full_lift
    (A : ResetOrder.Unary.TaskObject (P))
    (member : normalizedTaskUpperAge B ht n D m priority A) :
    ∃ F, normalizedTaskFullAge B ht n D m priority F ∧ F.task = A := member

end
end CCO.UnfilteredEP
