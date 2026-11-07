import CCO.UnfilteredEP.NormalizedTaskHereditary

/-! Ramsey and joint embedding from the SAME actual full normalized
provider. No intermediate task-prefix class is asserted Ramsey. -/

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

def normalizedTaskMapToObject
    {A : ResetOrder.Unary.FullObject (actualTaskFibres B ht n D m) (normalizedTaskExtra B ht n)}
    (hA : normalizedTaskFullAge B ht n D m priority A)
    (C : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht))
    (hC : NormalizedProperAge B ht priority C)
    (e : Structure.Embedding (normalizedTaskDecode B ht n D m A) C.model) :
    ResetOrder.Unary.FullHom A (normalizedTaskFullObject B ht n D m priority C hC) :=
  normalizedTaskMapOfDecode B ht n D m priority hA
    (normalizedTaskFullObject_mem B ht n D m priority C hC)
    (e.targetCongr (normalizedTaskDecode_fullObject B ht n D m priority C hC).symm)

theorem normalized_task_full_jep :
    ResetOrder.Unary.FullJEP (normalizedTaskFullAge B ht n D m priority) := by
  intro A C hA hC
  obtain ⟨W,hW,⟨f⟩,⟨g⟩⟩ := normalized_proper_jep B ht priority
    (normalizedTaskHidden B ht n D m A) (normalizedTaskHidden B ht n D m C)
    hA.normalized hC.normalized
  exact ⟨normalizedTaskFullObject B ht n D m priority W hW,
    normalizedTaskFullObject_mem B ht n D m priority W hW,
    ⟨normalizedTaskMapToObject B ht n D m priority hA W hW f⟩,
    ⟨normalizedTaskMapToObject B ht n D m priority hC W hW g⟩⟩

theorem normalized_task_full_ramsey :
    ResetOrder.Unary.FullRamsey (normalizedTaskFullAge B ht n D m priority) := by
  intro A C hA hC k positive
  obtain ⟨W,hW,arrow⟩ := normalized_proper_ramsey B ht priority
    (normalizedTaskHidden B ht n D m A) (normalizedTaskHidden B ht n D m C)
    hA.normalized hC.normalized k positive
  let F := normalizedTaskFullObject B ht n D m priority W hW
  refine ⟨F,normalizedTaskFullObject_mem B ht n D m priority W hW,?_⟩
  intro colour
  obtain ⟨g,shade,mono⟩ := arrow (fun e =>
    colour (normalizedTaskMapToObject B ht n D m priority hA W hW e))
  refine ⟨normalizedTaskMapToObject B ht n D m priority hC W hW g,shade,?_⟩
  intro f
  have equal : ResetOrder.Unary.fullCompose
      (normalizedTaskMapToObject B ht n D m priority hC W hW g) f =
      normalizedTaskMapToObject B ht n D m priority hA W hW
        (g.comp (normalizedTaskDecodeMap B ht n D m f)) :=
    ResetOrder.Unary.fullHom_ext (fun _ => rfl)
  exact (congrArg colour equal).trans (mono (normalizedTaskDecodeMap B ht n D m f))

end
end CCO.UnfilteredEP
