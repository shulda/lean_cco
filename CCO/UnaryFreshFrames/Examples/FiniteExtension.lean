import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Set.Finite.Range

/-! A finite partial correspondence with matching equality kernels extends
to an actual permutation. Repeated requests are allowed. -/
namespace CCO.UnaryFreshFrames.Examples

theorem extend_equal_kernels {I X : Type*} [Finite I] (f g : I → X)
    (h : ∀ x y, f x = f y ↔ g x = g y) :
    ∃ e : Equiv.Perm X, ∀ x, e (f x) = g x := by
  classical
  let T := Set.range f
  let _ : Finite T := (Set.finite_range f).to_subtype
  let rep : T → I := fun x => x.property.choose
  have hrep (x : T) : f (rep x) = x.val := x.property.choose_spec
  let k : T → X := fun x => g (rep x)
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    exact (hrep x).symm.trans (((h (rep x) (rep y)).mpr he).trans (hrep y))
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair (Subtype.val : T → X)
    k Subtype.val_injective hk
  refine ⟨e, ?_⟩
  intro x
  let tx : T := ⟨f x, ⟨x,rfl⟩⟩
  exact (he tx).trans ((h (rep tx) x).mp (hrep tx))

end CCO.UnaryFreshFrames.Examples
