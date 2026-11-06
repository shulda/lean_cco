import CCO.TypedOrbitFrames.CompletedStructureClosure

/-! The original group preserves the ACTUAL full interpreted signature:
all named typed functions and complete semantic binary cylinders. This
constructs a homomorphism into full hidden Aut, with no equality of the
two automorphism groups asserted or assumed. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalLattice CCO.TransitionClosure
open CCO.UnaryTermsReturn CCO.QuotientTransport CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

theorem original_completed_vertex_sort_invariant
    (H : HomogeneousSource S G) (g : G) (x : OriginalCompletedNamedCarrier S H) :
    originalCompletedVertexSort S H (originalCompletedNamedAct S H g x) =
      originalCompletedVertexSort S H x := by
  cases x with
  | inl x => cases x; rfl
  | inr x => rcases x with ⟨⟨i,⟨J,q⟩⟩,hJ⟩; rfl

theorem original_completed_labelled_step_equivariant
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (g : G)
    {s : OriginalCompletedPrimitiveSymbol S H}
    {x y : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedLabelledStep S H sap nr2 s x y) :
    OriginalCompletedNamedLabelledStep S H sap nr2 s
      (originalCompletedNamedAct S H g x) (originalCompletedNamedAct S H g y) := by
  cases h with
  | projection D x => exact .projection D (g • x)
  | upward D E hDE q =>
      have h := OriginalCompletedNamedLabelledStep.upward (sap := sap) (nr2 := nr2)
        D E hDE ((originalColourEqAsInvEq S H D.val).act g q)
      have heq := congrArg (originalCompletedNamedHiddenNode S H E)
        (original_completed_upward_equivariant S H g D E hDE q)
      exact Eq.mp (congrArg (fun z => OriginalCompletedNamedLabelledStep S H sap nr2
        (.inr (.inl ⟨_,⟨(D,E),hDE⟩⟩))
        (originalCompletedNamedHiddenNode S H D
          ((originalColourEqAsInvEq S H D.val).act g q)) z) heq) h
  | raw a q =>
      have h := OriginalCompletedNamedLabelledStep.raw (sap := sap) (nr2 := nr2)
        a ((originalColourEqAsInvEq S H a.val.1.val).act g q)
      have heq := congrArg (originalCompletedNamedHiddenNode S H
          (originalNamedRawTransitionSymbol_target S H sap nr2 a))
        (original_completed_raw_equivariant S H sap nr2 g a q)
      exact Eq.mp (congrArg (fun z => OriginalCompletedNamedLabelledStep S H sap nr2
        (.inr (.inr ⟨_,⟨_,a⟩⟩))
        (originalCompletedNamedHiddenNode S H a.val.1
          ((originalColourEqAsInvEq S H a.val.1.val).act g q)) z) heq) h

theorem original_completed_structure_func_equivariant
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (g : G)
    (s : OriginalCompletedPrimitiveSymbol S H) (x : OriginalCompletedNamedCarrier S H) :
    originalCompletedNamedAct S H g (originalCompletedPrimitiveFunction S H sap nr2 s x) =
      originalCompletedPrimitiveFunction S H sap nr2 s (originalCompletedNamedAct S H g x) := by
  classical
  by_cases hx : originalCompletedVertexSort S H x = originalCompletedPrimitiveInput S H s
  · exact (original_completed_primitive_function_of_graph S H sap nr2
      (original_completed_labelled_step_equivariant S H sap nr2 g
        (original_completed_primitive_function_graph S H sap nr2 s x hx))).symm
  · have hxg : originalCompletedVertexSort S H (originalCompletedNamedAct S H g x) ≠
        originalCompletedPrimitiveInput S H s := by
      rwa [original_completed_vertex_sort_invariant]
    simp only [originalCompletedPrimitiveFunction,dif_neg hx,dif_neg hxg]

/-- The FULL spectrum of all actual representatives is invariant;
no finer group pair-orbit relation replaces the semantic cylinder. -/
theorem original_typed_cylinder_spectrum_equivariant
    (H : HomogeneousSource S G) (g : G) {i j : ι}
    (J : ColourEq S i) (K : ColourEq S j)
    (q : Quotient J.val) (r : Quotient K.val) :
    originalTypedQuotientPairSpectrum S J K
        ((originalColourEqAsInvEq S H J).act g q)
        ((originalColourEqAsInvEq S H K).act g r) =
      originalTypedQuotientPairSpectrum S J K q r := by
  letI : MulAction G (Quotient J.val) := (originalColourEqAsInvEq S H J).quotientAction
  letI : MulAction G (Quotient K.val) := (originalColourEqAsInvEq S H K).quotientAction
  ext c
  constructor
  · rintro ⟨x,y,hx,hy,hcol⟩
    refine ⟨g⁻¹ • x,g⁻¹ • y,?_,?_,?_⟩
    · change g⁻¹ • Quotient.mk J.val x = q
      rw [hx]
      exact inv_smul_smul g q
    · change g⁻¹ • Quotient.mk K.val y = r
      rw [hy]
      exact inv_smul_smul g r
    · exact (S.colourInvariant_of_homogeneous H g⁻¹ x y).trans hcol
  · rintro ⟨x,y,hx,hy,hcol⟩
    refine ⟨g • x,g • y,?_,?_,?_⟩
    · exact congrArg ((originalColourEqAsInvEq S H J).act g) hx
    · exact congrArg ((originalColourEqAsInvEq S H K).act g) hy
    · exact (S.colourInvariant_of_homogeneous H g x y).trans hcol

theorem original_completed_coordinate_reading_equivariant
    (H : HomogeneousSource S G) (g : G)
    {x : OriginalCompletedNamedCarrier S H} {C : OriginalCompletedCoordinateCode S H}
    {q : Quotient (originalCompletedCoordinateKernel S H C).val}
    (h : OriginalCompletedCoordinateReading S H x C q) :
    OriginalCompletedCoordinateReading S H (originalCompletedNamedAct S H g x) C
      ((originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H C)).act g q) := by
  cases h with
  | real x => exact .real (g • x)
  | hidden D q => exact .hidden D _

theorem original_completed_binary_preserved
    (H : HomogeneousSource S G) (g : G)
    (name : OriginalCompletedCylinderBinaryName S H)
    (x y : OriginalCompletedNamedCarrier S H)
    (h : originalCompletedCylinderBinaryPredicate S H name x y) :
    originalCompletedCylinderBinaryPredicate S H name
      (originalCompletedNamedAct S H g x) (originalCompletedNamedAct S H g y) := by
  letI := originalCompletedNamedAction S H
  obtain ⟨hne,q,r,hq,hr,hRelation⟩ := h
  refine ⟨fun he => hne (MulAction.injective g he),
    (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H name.1)).act g q,
    (originalColourEqAsInvEq S H (originalCompletedCoordinateKernel S H name.2.1)).act g r,
    original_completed_coordinate_reading_equivariant S H g hq,
    original_completed_coordinate_reading_equivariant S H g hr,?_⟩
  change name.2.2.val = _
  rw [original_typed_cylinder_spectrum_equivariant S H g]
  exact hRelation

theorem original_completed_binary_equivariant
    (H : HomogeneousSource S G) (g : G)
    (name : OriginalCompletedCylinderBinaryName S H)
    (x y : OriginalCompletedNamedCarrier S H) :
    originalCompletedCylinderBinaryPredicate S H name
        (originalCompletedNamedAct S H g x) (originalCompletedNamedAct S H g y) ↔
      originalCompletedCylinderBinaryPredicate S H name x y := by
  letI := originalCompletedNamedAction S H
  constructor
  · intro h
    have h' := original_completed_binary_preserved S H g⁻¹ name _ _ h
    change originalCompletedCylinderBinaryPredicate S H name (g⁻¹ • (g • x))
      (g⁻¹ • (g • y)) at h'
    simpa only [inv_smul_smul] using h'
  · exact original_completed_binary_preserved S H g name x y

/-- An actual homomorphism of the original group into full hidden Aut.
Surjectivity onto full hidden Aut is deliberately not asserted. -/
noncomputable def originalCompletedMotionHom
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) :
    G →* (originalCompletedStructure S H sap nr2).Aut := by
  letI := originalCompletedNamedAction S H
  refine {
    toFun := fun g => ⟨MulAction.toPerm g,?_,?_,?_⟩
    map_one' := ?_
    map_mul' := ?_ }
  · intro x
    exact congrArg ULift.up (original_completed_vertex_sort_invariant S H g x)
  · intro s x
    exact original_completed_structure_func_equivariant S H sap nr2 g s.down x
  · intro name xs
    change (Fin 2 → OriginalCompletedNamedCarrier S H) at xs
    exact original_completed_binary_equivariant S H g name (xs 0) (xs 1)
  · apply Subtype.ext
    apply Equiv.ext
    exact original_completed_named_act_one S H
  · intro g h
    apply Subtype.ext
    apply Equiv.ext
    exact original_completed_named_act_mul S H g h

end CCO.TypedOrbitFrames
