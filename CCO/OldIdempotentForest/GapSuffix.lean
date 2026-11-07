import CCO.OldIdempotentForest.GapReturn
import CCO.OldIdempotentForest.GapTermSupport

/-! The actual OLD atomic side maps telescope through the literal
canonical prefix coordinates of ONE original diversity RAW word. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.QuotientTransport
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

def gapHiddenSort {i : ι} (J : OriginalNamedHiddenCoordinate S H i) : (Lang).Sorts :=
  ⟨⟨i,.inr J⟩⟩

variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

def GapRootKernelLe (b : P) (J : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F b)) : Prop :=
  ∀ x z, RootKernel S H sap nr2 (F.sort b) x z → J.val x z

structure OldSideTransition {b c : P} (side : SupportedMacroSide S H sap nr2 F b c)
    (J : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F b))
    (K : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F c)) where
  leftKernel : GapRootKernelLe S H sap nr2 F b J
  rightKernel : GapRootKernelLe S H sap nr2 F c K
  term : CCO.UnaryFreshFrames.Term Lang (gapHiddenSort S H sap nr2 J) (gapHiddenSort S H sap nr2 K)
  equation : LiteralOldEquation S H sap nr2 F
    (term.comp (rootCoordinateTerm S H sap nr2 (F.sort b) J leftKernel))
    (rootCoordinateTerm S H sap nr2 (F.sort c) K rightKernel) b c
  edge : ∀ x y, S.menuRel (PositiveWord.profile S side.word) x y →
    (Hidden).eval term (originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)) =
      originalCompletedNamedHiddenNode S H K (Quotient.mk K.val.val y)

/-- Choose the actual common atom on the SAME selected local support.
Both OLD evaluation domains and equality are reflected by its embedding,
then included into the original ambient OLD partial source. -/
theorem gap_side_atomic_transition {b c : P}
    (side : SupportedMacroSide S H sap nr2 F b c)
    (J : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F b))
    (hKernel : ∀ x z,
      (∃ y, S.menuRel (PositiveWord.profile S side.word) x y ∧
        S.menuRel (PositiveWord.profile S side.word) z y) → J.val x z) :
    Nonempty (OldSideTransition S H sap nr2 F side J
      (positiveBranchTarget S H sap nr2 J side.word hKernel)) := by
  obtain ⟨a,ha,hMenu,hEq⟩ := old_branch_atomic_equation S H sap nr2
    (F.closureStructure {b,c}) side.model
    ⟨b,F.subset_closure _ (by simp)⟩ ⟨c,F.subset_closure _ (by simp)⟩
    (fun he => side.distinct (congrArg Subtype.val he)) J side.word hKernel side.contains
  let A := branchAtomicTarget S H sap nr2 J side.word hKernel a (side.contains ha)
  let out : OldSideTransition S H sap nr2 F side J A := {
    leftKernel := branchSourceKernel S H sap nr2 side.left side.right hMenu
      J side.word hKernel side.contains
    rightKernel := branchAtomicTargetKernel S H sap nr2 side.left side.right hMenu
      J side.word hKernel side.contains a (side.contains ha)
    term := branchAtomicTransitionTerm S H sap nr2 J side.word hKernel a (side.contains ha)
    equation := LiteralOldEquation.of_closed_support S H sap nr2 (F.isClosed_closure {b,c}) hEq
    edge := gap_atomic_transition_whole_edge S H sap nr2 J side.word hKernel a (side.contains ha) }
  have hA : A = positiveBranchTarget S H sap nr2 J side.word hKernel :=
    branchAtomicTarget_eq_positiveBranchTarget S H sap nr2 J side.word hKernel a (side.contains ha)
  exact ⟨Eq.mp (congrArg (fun K => OldSideTransition S H sap nr2 F side J K) hA) out⟩

theorem gap_side_return_transition {b c : P}
    (side : SupportedMacroSide S H sap nr2 F b c)
    {a : ι} (D : OriginalNamedHiddenCoordinate S H a)
    (p : Word G X a (gapSort S H sap nr2 F b))
    (s : Word G X (gapSort S H sap nr2 F c) a)
    (h : Return.Bound (originalColourEqAsInvEq S H D.val) p (.cons side.letter s)) :
    Nonempty (OldSideTransition S H sap nr2 F side
      (originalNamedReturnPrefixCoordinate S H sap nr2 D p (.cons side.letter s) h)
      (originalNamedReturnPrefixCoordinate S H sap nr2 D (p.extend side.letter) s
        (Return.next_bound (originalColourEqAsInvEq S H D.val) p side.letter s h))) := by
  obtain ⟨out⟩ := gap_side_atomic_transition S H sap nr2 F side _
    (gap_side_return_kernel S H sap nr2 F side D p s h)
  exact ⟨(gap_side_return_target S H sap nr2 F side D p s h) ▸ out⟩

/-- The term is a composite of the actual selected OLD atomic side maps.
Its semantics is the literal canonical prefix label, so no unrelated
existential identity term can stand in for this source chain. -/
structure GapSuffixCertificate {b c : P}
    (path : SourceMacroPath S H sap nr2 F b c)
    (D : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F c))
    (p : Word G X (gapSort S H sap nr2 F c) (gapSort S H sap nr2 F b))
    (h : Return.Bound (originalColourEqAsInvEq S H D.val) p path.rawWord) where
  leftKernel : GapRootKernelLe S H sap nr2 F b
    (originalNamedReturnPrefixCoordinate S H sap nr2 D p path.rawWord h)
  rightKernel : GapRootKernelLe S H sap nr2 F c D
  term : CCO.UnaryFreshFrames.Term Lang
    (gapHiddenSort S H sap nr2 (originalNamedReturnPrefixCoordinate S H sap nr2 D p path.rawWord h))
    (gapHiddenSort S H sap nr2 D)
  equation : LiteralOldEquation S H sap nr2 F
    (term.comp (rootCoordinateTerm S H sap nr2 (F.sort b)
      (originalNamedReturnPrefixCoordinate S H sap nr2 D p path.rawWord h) leftKernel))
    (rootCoordinateTerm S H sap nr2 (F.sort c) D rightKernel) b c
  semantics : ∀ x,
    (Hidden).eval term (originalCompletedNamedHiddenNode S H
      (originalNamedReturnPrefixCoordinate S H sap nr2 D p path.rawWord h)
      (Quotient.mk _ x)) =
      originalCompletedNamedHiddenNode S H D
        ((Return.prefixTransport (originalColourEqAsInvEq S H D.val)
          (originalReturnSortTransitivity S H) p path.rawWord h).label x)

theorem gap_return_suffix
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    {b c : P} (path : SourceMacroPath S H sap nr2 F b c)
    (D : OriginalNamedHiddenCoordinate S H (gapSort S H sap nr2 F c))
    (p : Word G X (gapSort S H sap nr2 F c) (gapSort S H sap nr2 F b))
    (h : Return.Bound (originalColourEqAsInvEq S H D.val) p path.rawWord) :
    Nonempty (GapSuffixCertificate S H sap nr2 F path D p h) := by
  induction path with
  | single side =>
    let E := originalColourEqAsInvEq S H D.val
    let trans := originalReturnSortTransitivity S H
    let hn := Return.next_bound E p side.letter (.nil _) h
    obtain ⟨out⟩ := gap_side_return_transition S H sap nr2 F side D p (.nil _) h
    have hFinal := original_named_return_empty_suffix_coordinate_eq S H sap nr2 D
      (p.extend side.letter) hn
    let outD : OldSideTransition S H sap nr2 F side
        (originalNamedReturnPrefixCoordinate S H sap nr2 D p (.cons side.letter (.nil _)) h) D :=
      Eq.mp (congrArg (fun K => OldSideTransition S H sap nr2 F side
        (originalNamedReturnPrefixCoordinate S H sap nr2 D p (.cons side.letter (.nil _)) h) K) hFinal) out
    refine ⟨{ leftKernel := outD.leftKernel
              rightKernel := outD.rightKernel
              term := outD.term
              equation := outD.equation
              semantics := ?_ }⟩
    intro x
    obtain ⟨y,hxy⟩ := (serial_coserial_of_invariant side.letter.relation side.letter.invariant
      side.letter.nonempty (trans _) (trans _)).1 x
    exact (outD.edge x y hxy).trans (congrArg (originalCompletedNamedHiddenNode S H D)
      ((Return.edge_label E trans p side.letter (.nil _) h hxy).trans
        (Return.final_label E trans (p.extend side.letter) hn y)).symm)
  | @cons b c d side tail ih =>
    let E := originalColourEqAsInvEq S H D.val
    let trans := originalReturnSortTransitivity S H
    let hn := Return.next_bound E p side.letter tail.rawWord h
    obtain ⟨out0⟩ := gap_side_return_transition S H sap nr2 F side D p tail.rawWord h
    obtain ⟨out1⟩ := ih D (p.extend side.letter) hn
    refine ⟨{ leftKernel := out0.leftKernel
              rightKernel := out1.rightKernel
              term := out1.term.comp out0.term
              equation := ?_
              semantics := ?_ }⟩
    · exact gap_literal_compose S H sap nr2 F
        (total_of_unary_admissible hUnary (originalPartialTarget_total S H sap nr2))
        _ _ _ out0.term out1.term b c d rfl rfl rfl out0.equation out1.equation
    · intro x
      obtain ⟨y,hxy⟩ := (serial_coserial_of_invariant side.letter.relation side.letter.invariant
        side.letter.nonempty (trans _) (trans _)).1 x
      exact ((Hidden).eval_comp out1.term out0.term _).trans
        ((congrArg ((Hidden).eval out1.term) (out0.edge x y hxy)).trans
          ((out1.semantics y).trans (congrArg (originalCompletedNamedHiddenNode S H D)
            (Return.edge_label E trans p side.letter tail.rawWord h hxy).symm)))

end
end CCO.OldIdempotentForest
