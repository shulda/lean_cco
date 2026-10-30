import CCO.RelationalCompletion.Relational.Homogeneous
import Mathlib.Data.Set.Finite.Range

/-! Full homogeneity aligns arbitrary finite tuples using EVERY old relation,
including nullary and repeated-argument tuples. It does not imply binary
reduct homogeneity. The frozen-factor lift will supply the full type here. -/

universe u v w
namespace CCO.FullPhaseLift.BinarySource
open RelationalCompletion.Relational
noncomputable section

theorem full_tuple_homogeneous {L : Language.{u}} {M : Type v}
    (U : Structure L M) (hom : U.Homogeneous)
    {V : Type w} [Finite V] (p q : V → M)
    (heq : ∀ x y, p x = p y ↔ q x = q y)
    (hrel : ∀ {n} (R : L.Rel n) xs,
      U.rel R (p ∘ xs) ↔ U.rel R (q ∘ xs)) :
    ∃ a : U.Iso U, ∀ x, a.point (p x) = q x := by
  classical
  let A := Set.range p
  letI : Finite A := (Set.finite_range p).to_subtype
  let choose : A → V := fun a => a.property.choose
  have choose_spec (a : A) : p (choose a) = a.val := a.property.choose_spec
  let k : A → M := fun a => q (choose a)
  have hk : Function.Injective k := by
    intro a b he
    apply Subtype.ext
    exact (choose_spec a).symm.trans (((heq _ _).mpr he).trans (choose_spec b))
  let f : (U.induce A).Embedding U := U.inclusion A
  let g : (U.induce A).Embedding U := {
    point := k
    injective := hk
    rel_iff := by
      intro n R xs
      have hp : p ∘ (choose ∘ xs) = Subtype.val ∘ xs := by
        funext i
        exact choose_spec (xs i)
      have h := hrel R (choose ∘ xs)
      rw [hp] at h
      exact h.symm }
  obtain ⟨a,ha⟩ := hom A (U.induce A) f g
  refine ⟨a,fun x => ?_⟩
  let d : A := ⟨p x,⟨x,rfl⟩⟩
  exact (ha d).trans ((heq _ _).mp (choose_spec d))

end
end CCO.FullPhaseLift.BinarySource
