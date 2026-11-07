import CCO.OldIdempotentForest.GapPath

/-! Canonical return prefixes for the SAME actual diversity macro factors.
The exact B057 atomic transition is aligned with every edge of the WHOLE
original positive branch, not with an unrelated identity-loop term. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.QuotientTransport
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)

theorem gap_prefix_coordinate_relation {a i : ι}
    (D : OriginalNamedHiddenCoordinate S H a)
    (p : Word G X a i) (s : Word G X i a)
    (h : Return.Bound (originalColourEqAsInvEq S H D.val) p s)
    (x y : X i) :
    (originalNamedReturnPrefixCoordinate S H sap nr2 D p s h).val x y ↔
      (Return.prefixTransport (originalColourEqAsInvEq S H D.val)
        (originalReturnSortTransitivity S H) p s h).target x y := Iff.rfl

theorem gap_prefix_coordinate_invEq {a i : ι}
    (D : OriginalNamedHiddenCoordinate S H a)
    (p : Word G X a i) (s : Word G X i a)
    (h : Return.Bound (originalColourEqAsInvEq S H D.val) p s) :
    originalColourEqAsInvEq S H
        (originalNamedReturnPrefixCoordinate S H sap nr2 D p s h).val =
      (Return.prefixTransport (originalColourEqAsInvEq S H D.val)
        (originalReturnSortTransitivity S H) p s h).target := by
  rw [originalNamedReturnPrefixCoordinate_kernel]
  exact (originalFullColourEqInvEqOrderIso S H).apply_symm_apply _

section Side
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable {b c : P} (side : SupportedMacroSide S H sap nr2 F b c)
variable {a : ι} (D : OriginalNamedHiddenCoordinate S H a)
variable (p : Word G X a (gapSort S H sap nr2 F b))
variable (s : Word G X (gapSort S H sap nr2 F c) a)
variable (h : Return.Bound (originalColourEqAsInvEq S H D.val) p (.cons side.letter s))

/-- The WHOLE side's functionality is DERIVED from one closed return
bound; no primitive comparison in the source meet is assumed functional. -/
def gap_side_return_kernel :
    ∀ x z : X (gapSort S H sap nr2 F b),
      (∃ y : X (gapSort S H sap nr2 F c),
        S.menuRel (PositiveWord.profile S side.word) x y ∧
        S.menuRel (PositiveWord.profile S side.word) z y) →
      (originalNamedReturnPrefixCoordinate S H sap nr2 D p (.cons side.letter s) h).val x z := by
  intro x z hxz
  obtain ⟨y,hxy,hzy⟩ := hxz
  apply (gap_prefix_coordinate_relation S H sap nr2 D p (.cons side.letter s) h x z).mpr
  exact (Return.factor (originalColourEqAsInvEq S H D.val)
    (originalReturnSortTransitivity S H) p side.letter s h).kernel x z y hxy hzy

/-- Literal equality of the WHOLE branch's existing named target with
the NEXT canonical return prefix. This is the actual seam coordinate. -/
theorem gap_side_return_target :
    positiveBranchTarget S H sap nr2
      (originalNamedReturnPrefixCoordinate S H sap nr2 D p (.cons side.letter s) h)
      side.word (gap_side_return_kernel S H sap nr2 F side D p s h) =
      originalNamedReturnPrefixCoordinate S H sap nr2 D (p.extend side.letter) s
        (Return.next_bound (originalColourEqAsInvEq S H D.val) p side.letter s h) := by
  apply Subtype.ext
  apply ColourEq.ext
  intro y z
  change (originalNamedRawTransitionSymbol_transport S H
    (positiveBranchSymbol S H sap
      (originalNamedReturnPrefixCoordinate S H sap nr2 D p (.cons side.letter s) h)
      side.word (gap_side_return_kernel S H sap nr2 F side D p s h))).target y z ↔ _
  rw [gap_prefix_coordinate_relation]
  rw [← Return.factor_target (originalColourEqAsInvEq S H D.val)
    (originalReturnSortTransitivity S H) p side.letter s h]
  rw [Transport.target_iff,Transport.target_iff]
  constructor
  · rintro ⟨x,x',hxy,hxx',hx'z⟩
    exact ⟨x,x',hxy,
      (gap_prefix_coordinate_relation S H sap nr2 D p (.cons side.letter s) h x x').mp hxx',hx'z⟩
  · rintro ⟨x,x',hxy,hxx',hx'z⟩
    exact ⟨x,x',hxy,
      (gap_prefix_coordinate_relation S H sap nr2 D p (.cons side.letter s) h x x').mpr hxx',hx'z⟩

end Side

/-- The EXACT selected atomic primitive already has the WHOLE branch
map on EVERY original branch edge. No unrelated named identity term is
substituted for the OLD equation's chosen atomic transition. -/
theorem gap_atomic_transition_whole_edge {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (word : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S word) x y ∧
        S.menuRel (PositiveWord.profile S word) z y) → J.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S word)
    (x : X i) (y : X j) (hxy : S.menuRel (PositiveWord.profile S word) x y) :
    (originalCompletedStructure S H sap nr2).eval
        (branchAtomicTransitionTerm S H sap nr2 J word hKernel a ha)
        (originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)) =
      originalCompletedNamedHiddenNode S H
        (branchAtomicTarget S H sap nr2 J word hKernel a ha)
        (Quotient.mk (branchAtomicTarget S H sap nr2 J word hKernel a ha).val.val y) := by
  let Ta := originalNamedRawTransitionSymbol_transport S H
    (branchAtomicRawSymbol S H J word hKernel a ha)
  let Tp := originalNamedRawTransitionSymbol_transport S H
    (positiveBranchSymbol S H sap J word hKernel)
  have hLabel : Ta.label y = Quotient.mk J.val.val x :=
    (branchAtomic_labels S H sap J word hKernel a ha y).trans (Tp.label_edge hxy)
  have hMap : Ta.quotientEquiv (Quotient.mk J.val.val x) = Quotient.mk'' y := by
    apply Ta.labelEquiv.injective
    exact (Ta.labelEquiv.apply_symm_apply _).trans hLabel.symm
  have hValue := original_completed_primitive_function_of_graph S H sap nr2
    (OriginalCompletedNamedLabelledStep.raw (sap := sap) (nr2 := nr2)
      (branchAtomicRawSymbol S H J word hKernel a ha) (Quotient.mk J.val.val x))
  exact hValue.trans (congrArg (originalCompletedNamedHiddenNode S H _) hMap)

end
end CCO.OldIdempotentForest
