import CCO.UnfilteredEP.ActualTaskFibres

/-! Whole generated closures survive the faithful task record codecs.
The full provider adds only relations, so no function closure is lost. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w a b
namespace CCO.UnfilteredEP
noncomputable section

section General
open CCO.ResetOrder.Unary CCO.ResetOrder.Unary.Primitive
variable {L : Signature.{a}} {P : Fibres.{a,b} L} {X : ExtraLanguage L}

theorem primitive_closure_eq_of_func_eq {V : Type b} (C D : Structure L V)
    (h : C.func = D.func) (S : Set V) : C.closure S = D.closure S := by
  unfold Structure.closure Structure.Step
  rw [h]

theorem full_closure_eq_old [IsEmpty X.Func] (A : FullObject P X)
    (S : Set A.task.old.Carrier) : A.unary.closure S = A.task.old.data.closure S := by
  apply Set.Subset.antisymm
  · apply A.unary.closure_minimal _ (A.task.old.data.subset_closure S)
    intro F x hx y hy
    cases F with
    | inl F => exact A.task.old.data.isClosed_closure S F x hx hy
    | inr F => exact isEmptyElim F
  · exact A.task.old.data.closure_minimal
      (fullClosed_old (A.unary.isClosed_closure S)) (A.unary.subset_closure S)

theorem fullInduce_closure (A : FullObject P X) (S : Set A.task.old.Carrier)
    (hS : A.unary.IsClosed S) (T : Set S) :
    (fullInduce A S hS).unary.closure T = (A.unary.induce S hS).closure T := by
  apply primitive_closure_eq_of_func_eq
  funext F x
  cases F <;> rfl

/-- The entire full generated pair, with its two actual marked roots,
is generated in its own induced structure. -/
theorem full_pair_generated (A : FullObject P X) (x y : A.task.old.Carrier) :
    (pairClosure A x y).unary.closure {pairLeft A x y,pairRight A x y} = Set.univ := by
  refine (fullInduce_closure A (pairSet A x y) (A.unary.isClosed_closure {x,y})
    ({pairLeft A x y,pairRight A x y} : Set (pairSet A x y))).trans ?_
  apply Set.eq_univ_of_forall
  intro z
  have he := A.unary.closure_induce_image (A.unary.isClosed_closure {x,y})
    ({pairLeft A x y,pairRight A x y} : Set (pairSet A x y))
  have himage : Subtype.val '' ({pairLeft A x y,pairRight A x y} : Set (pairSet A x y)) =
      {x,y} := Set.image_pair Subtype.val _ _
  have he' := he.trans (congrArg A.unary.closure himage)
  have hz : z.val ∈ A.unary.closure {x,y} := z.property
  obtain ⟨t,ht,hte⟩ := (Set.ext_iff.mp he' z.val).mpr hz
  exact (Subtype.ext hte : t = z) ▸ ht

end General

open CCO.APRamseyReadout CCO.CloneTupleGeometry
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)

theorem taskOldRaw_closure
    (A : CCO.ResetOrder.Unary.Object.{max u v w,max u v} (TaskOldSignature B ht n))
    (S : Set A.Carrier) : (taskOldRaw B ht n A).closure S = A.data.closure S := rfl

end
end CCO.UnfilteredEP
