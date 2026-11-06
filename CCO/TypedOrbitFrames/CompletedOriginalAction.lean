import CCO.UnaryTermsReturn.CompletedNamedStepClosure

/-!
# Source11 T03: the original group on the actual completed carrier

The action on every represented quotient is induced from the ORIGINAL
invariant equivalence. Every genuine named primitive commutes with this
action, including full RAW transitions with their actual transported
target. No hidden automorphism or hidden SAP premise is introduced.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalLattice CCO.TransitionClosure
open CCO.UnaryTermsReturn CCO.QuotientTransport

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The actual original action retains the literal old sort and full
kernel of every represented quotient vertex. -/
def originalCompletedNamedAct (H : HomogeneousSource S G) (g : G) :
    OriginalCompletedNamedCarrier S H → OriginalCompletedNamedCarrier S H
  | .inl x => .inl (g • x)
  | .inr ⟨⟨i,⟨J,q⟩⟩,hNamed⟩ =>
      .inr ⟨⟨i,⟨J,(originalColourEqAsInvEq S H J).act g q⟩⟩,hNamed⟩

theorem original_completed_named_act_one (H : HomogeneousSource S G)
    (x : OriginalCompletedNamedCarrier S H) :
    originalCompletedNamedAct S H 1 x = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (one_smul G x)
  | inr x =>
      rcases x with ⟨⟨i,⟨J,q⟩⟩,hNamed⟩
      induction q using Quotient.inductionOn with
      | _ x =>
          change (Sum.inr ⟨⟨i,⟨J,Quotient.mk J.val (1 • x)⟩⟩,hNamed⟩ :
            OriginalCompletedNamedCarrier S H) = _
          rw [one_smul]

theorem original_completed_named_act_mul (H : HomogeneousSource S G)
    (g h : G) (x : OriginalCompletedNamedCarrier S H) :
    originalCompletedNamedAct S H (g * h) x =
      originalCompletedNamedAct S H g (originalCompletedNamedAct S H h x) := by
  cases x with
  | inl x => exact congrArg Sum.inl (mul_smul g h x)
  | inr x =>
      rcases x with ⟨⟨i,⟨J,q⟩⟩,hNamed⟩
      induction q using Quotient.inductionOn with
      | _ x =>
          change (Sum.inr ⟨⟨i,⟨J,Quotient.mk J.val ((g * h) • x)⟩⟩,hNamed⟩ :
            OriginalCompletedNamedCarrier S H) = _
          rw [mul_smul]
          rfl

/-- A proved actual MulAction, not a supplied hidden action. -/
@[instance_reducible] def originalCompletedNamedAction
    (H : HomogeneousSource S G) :
    MulAction G (OriginalCompletedNamedCarrier S H) where
  smul := originalCompletedNamedAct S H
  one_smul := original_completed_named_act_one S H
  mul_smul := original_completed_named_act_mul S H

theorem original_completed_named_act_real (H : HomogeneousSource S G)
    (g : G) (x : Sigma X) :
    originalCompletedNamedAct S H g (.inl x) = .inl (g • x) := rfl

theorem original_completed_named_act_hidden (H : HomogeneousSource S G)
    (g : G) {i : ι} (J : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient J.val.val) :
    originalCompletedNamedAct S H g (originalCompletedNamedHiddenNode S H J q) =
      originalCompletedNamedHiddenNode S H J
        ((originalColourEqAsInvEq S H J.val).act g q) := rfl

/-- The actual primitive upward factor is equivariant on quotient
classes, proved by the original representative action. -/
theorem original_completed_upward_equivariant
    (H : HomogeneousSource S G) (g : G) {i : ι}
    (D E : OriginalNamedHiddenCoordinate S H i) (hDE : D.val ≤ E.val)
    (q : Quotient D.val.val) :
    Quot.mapRight hDE ((originalColourEqAsInvEq S H D.val).act g q) =
      (originalColourEqAsInvEq S H E.val).act g (Quot.mapRight hDE q) := by
  induction q using Quotient.inductionOn with
  | _ x => rfl

/-- Every actual named FULL RAW transport commutes with the original
group. The accepted B040 equivariance is used on its literal target. -/
theorem original_completed_raw_equivariant
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (g : G) {i j : ι}
    (a : OriginalNamedRawTransitionSymbol S H i j)
    (q : Quotient a.val.1.val.val) :
    originalNamedRawTransitionSymbol_function S H sap nr2 a
        ((originalColourEqAsInvEq S H a.val.1.val).act g q) =
      (originalColourEqAsInvEq S H
        (originalNamedRawTransitionSymbol_target S H sap nr2 a).val).act g
        (originalNamedRawTransitionSymbol_function S H sap nr2 a q) :=
  (originalNamedRawTransitionSymbol_transport S H a).quotientEquiv_equivariant g q

/-- The ENTIRE genuine primitive graph is equivariant, retaining all
original sort and represented-kernel tags. -/
theorem original_completed_named_step_equivariant
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (g : G)
    {a b : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedStep S H sap nr2 a b) :
    OriginalCompletedNamedStep S H sap nr2
      (originalCompletedNamedAct S H g a) (originalCompletedNamedAct S H g b) := by
  cases h with
  | projection D x => exact .projection D (g • x)
  | upward D E hDE q =>
      have h := OriginalCompletedNamedStep.upward (sap := sap) (nr2 := nr2) D E hDE
        ((originalColourEqAsInvEq S H D.val).act g q)
      have heq := congrArg (originalCompletedNamedHiddenNode S H E)
        (original_completed_upward_equivariant S H g D E hDE q)
      exact Eq.mp (congrArg (fun z => OriginalCompletedNamedStep S H sap nr2
        (originalCompletedNamedHiddenNode S H D
          ((originalColourEqAsInvEq S H D.val).act g q)) z) heq) h
  | rawTransition a q =>
      have h := OriginalCompletedNamedStep.rawTransition (sap := sap) (nr2 := nr2) a
        ((originalColourEqAsInvEq S H a.val.1.val).act g q)
      have heq := congrArg
        (originalCompletedNamedHiddenNode S H
          (originalNamedRawTransitionSymbol_target S H sap nr2 a))
        (original_completed_raw_equivariant S H sap nr2 g a q)
      exact Eq.mp (congrArg (fun z => OriginalCompletedNamedStep S H sap nr2
        (originalCompletedNamedHiddenNode S H a.val.1
          ((originalColourEqAsInvEq S H a.val.1.val).act g q)) z) heq) h

end CCO.TypedOrbitFrames
