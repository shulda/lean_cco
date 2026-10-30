import CCO.RelationalCompletion.Relational.Split
import Mathlib.Logic.Equiv.Set

universe u v w
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {V : Type v} {W : Type w}

/-- The profile invariant really yields a full induced isomorphism between
the TWO TARGET images, including all absent relation tuples and nullaries. -/
noncomputable def SameImageType.imageIso {U : Structure L W} {h k : V → W}
    {S : Set V} (p : U.SameImageType h k S) (hh : Set.InjOn h S)
    (hk : Set.InjOn k S) : Iso (U.induce (h '' S)) (U.induce (k '' S)) where
  point := (Equiv.Set.imageOfInjOn h S hh).symm.trans (Equiv.Set.imageOfInjOn k S hk)
  rel_iff R xs := by
    let eh := Equiv.Set.imageOfInjOn h S hh
    let zs : Fin _ → S := eh.symm ∘ xs
    have he : h ∘ (Subtype.val ∘ zs) = Subtype.val ∘ xs := by
      funext i
      exact congrArg Subtype.val (eh.apply_symm_apply (xs i))
    change U.rel R (k ∘ (Subtype.val ∘ zs)) ↔ U.rel R (Subtype.val ∘ xs)
    rw [← he]
    exact (p R (Subtype.val ∘ zs) (fun i => (zs i).property)).symm

@[simp] theorem SameImageType.imageIso_point {U : Structure L W} {h k : V → W}
    {S : Set V} (p : U.SameImageType h k S) (hh : Set.InjOn h S)
    (hk : Set.InjOn k S) (x : S) :
    (p.imageIso hh hk).point ⟨h x, ⟨x, x.property, rfl⟩⟩ =
      ⟨k x, ⟨x, x.property, rfl⟩⟩ := by
  let eh := Equiv.Set.imageOfInjOn h S hh
  change (Equiv.Set.imageOfInjOn k S hk) (eh.symm (eh x)) = _
  rw [eh.symm_apply_apply]
  rfl

end CCO.RelationalCompletion.Relational.Structure
