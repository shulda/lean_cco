import CCO.APCharacter.ActualMasks
import CCO.APCharacter.Seeds

/-! The accepted free-action finite seed theorem supplies the ACTUAL
finite extension field of the constructed maximal-character masks. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
namespace SourcePhase
variable (P : SourcePhase S H C A)

theorem finite_seed_extension : P.masks.FiniteSeedExtension := by
  classical
  intro V _ sort point bits valid pair
  let I := {x : V // Nonempty (Bridge S A (sort x))}
  let p : I → Reached.Point H C A := fun x =>
    ⟨⟨sort x.val,x.property⟩,(Reached.kernel H C ⟨sort x.val,x.property⟩).project (point x.val)⟩
  letI := Reached.groupoid H C (A := A)
  have tests : ∀ x y (R : Arrow S (Reached.kernel H C (p x).1) (Reached.kernel H C (p y).1)),
      R.quotientMap H (p x).2 = (p y).2 → bits y.val = bits x.val + P.character.value R := by
    intro x y R hR
    have hr : R.rel (point x.val) (point y.val) := (R.quotientMap_eq_iff H _ _).mp hR
    exact (pair x.val y.val).2.2 _ _ rfl x.property y.property R hr
  obtain ⟨mark,hm,hmark⟩ := (indexed_actual_seed_extension_iff S H C A P.character p
    (fun x : I => bits x.val)).mpr tests
  refine ⟨originalMarking S H C A mark,P.original_global_marking mark hm,?_⟩
  intro x
  by_cases hx : Nonempty (Bridge S A (sort x))
  · rw [originalMarking_reached S H C A mark (⟨sort x,hx⟩ : Reached S A)]
    exact hmark ⟨x,hx⟩
  · have hz : bits x = 0 := valid x hx
    rw [hz]
    simp only [originalMarking,dif_neg hx]

end SourcePhase
end
end CCO.APCharacter
