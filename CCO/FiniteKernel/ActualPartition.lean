import CCO.FiniteKernel.Partition
import Mathlib.Data.Set.Countable

/-! The owner presentation is obtained from the ACTUAL invariant equivalence
classes, including an empty universe. Countability transfers from real points.
-/
universe u v w
namespace CCO.FiniteKernel
variable {X : Type u} (S : BinaryStructure.{u,v,w} X)

noncomputable def FinitePartition.ofSetoid (F : Setoid X)
    (hfin : ∀ x, Finite {y : X // F.r x y})
    (hinv : ∀ (g : S.Aut) x y, F.r x y ↔ F.r (g.val x) (g.val y)) :
    FinitePartition S (Quotient F) where
  owner := Quotient.mk F
  surjective := Quotient.mk_surjective
  finite_fibre := by
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
      letI := hfin x
      apply Finite.of_injective (fun y : {y : X // Quotient.mk F y = Quotient.mk F x} =>
        (⟨y.val,F.symm (Quotient.exact y.property)⟩ : {y : X // F.r x y}))
      intro a b h
      exact Subtype.ext (congrArg (fun t : {y : X // F.r x y} => t.val) h)
  invariant := by
    intro g x y
    exact Quotient.eq_iff_equiv.trans ((hinv g x y).trans Quotient.eq_iff_equiv.symm)

theorem FinitePartition.countable_owners {I : Type*} (P : FinitePartition S I)
    [Countable X] : Countable I := by
  exact Function.Surjective.countable P.surjective

end CCO.FiniteKernel
