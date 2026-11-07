import CCO.GuardedOldSeams.FullPullback

/-! B057 C44--C48. Original visible SAP supplies the fresh neighbours
needed for the two actual root-kernel inclusions. The resulting readouts
are literal existing projections/upward maps in the old language. -/

universe u v w r
namespace CCO.GuardedOldSeams
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

theorem rootKernel_real {i : ι} (x z : X i) :
    RootKernel S H sap nr2 ⟨⟨i,.inl ()⟩⟩ x z ↔ x = z := by
  change (Sum.inl (⟨i,x⟩ : Sigma X) : OriginalCompletedNamedCarrier S H) = .inl ⟨i,z⟩ ↔ _
  simp only [Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and]

theorem rootKernel_proper {i : ι} (E : OriginalNamedHiddenCoordinate S H i)
    (x z : X i) :
    RootKernel S H sap nr2 ⟨⟨i,.inr E⟩⟩ x z ↔ E.val x z := by
  unfold RootKernel rootMap
  rw [rootBaseTerm_proper,rootBaseTerm_proper]
  exact (original_completed_hidden_node_injective S H E).eq_iff.trans
    Quotient.eq_iff_equiv

/-- Literal source root kernel inclusion, using the existing old-SAP
fresh-neighbour proof rather than false RAW saturation of D. -/
theorem visible_source_kernel_le {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    (hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty)
    (R : X C.down.1 → X D.down.1 → Prop)
    (J : ColourEq S C.down.1)
    (hContains : ∀ x y, guardedFactorPullback S H sap nr2 q s x y → R x y)
    (hFunctional : ∀ x z y, R x y → R z y → J x z) :
    ∀ x z, RootKernel S H sap nr2 C x z → J x z := by
  apply factor_left_kernel_le S H sap nr2 q s hMenu R J
  · simpa only [guardedFactorPullback_eq_menuRel] using hContains
  · exact hFunctional

/-- The target inclusion uses the actual transported FULL kernel
Rᵒᵖ;J;R. Reflexivity of J supplies the middle step. -/
theorem visible_target_kernel_le {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    (hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty)
    (J : OriginalNamedHiddenCoordinate S H C.down.1)
    {R : X C.down.1 → X D.down.1 → Prop}
    (T : QuotientTransport.Transport (originalColourEqAsInvEq S H J.val) R)
    (hContains : ∀ x y, guardedFactorPullback S H sap nr2 q s x y → R x y) :
    ∀ y z, RootKernel S H sap nr2 D y z →
      (original_named_hidden_transport_target S H sap nr2 J T).val y z := by
  apply factor_right_kernel_le S H sap nr2 q s hMenu R
    (original_named_hidden_transport_target S H sap nr2 J T).val
  · simpa only [guardedFactorPullback_eq_menuRel] using hContains
  · intro x y z hxy hxz
    exact (T.target_iff y z).mpr ⟨x,x,hxy,J.val.val.refl x,hxz⟩

/-- The canonical J-readout of an old root. It is exactly F_J for a
real root, or the existing named upward map for a proper root. -/
def rootCoordinateTerm (C : (Lang).Sorts)
    (J : OriginalNamedHiddenCoordinate S H C.down.1)
    (hKernel : ∀ x z, RootKernel S H sap nr2 C x z → J.val x z) :
    Term Lang C ⟨⟨C.down.1,.inr J⟩⟩ := by
  rcases C with ⟨⟨i,c⟩⟩
  cases c with
  | inl realTag =>
    cases realTag
    exact rootBaseTerm S H sap nr2 ⟨⟨i,.inr J⟩⟩
  | inr E =>
    have hEJ : E.val ≤ J.val := fun x z h =>
      hKernel x z ((rootKernel_proper S H sap nr2 E x z).mpr h)
    exact Term.func (L := originalCompletedLanguage S H sap nr2)
      (⟨.inr (.inl ⟨i,⟨(E,J),hEJ⟩⟩)⟩ : (Lang).Func) (.id _)

theorem rootCoordinateTerm_eval (C : (Lang).Sorts)
    (J : OriginalNamedHiddenCoordinate S H C.down.1)
    (hKernel : ∀ x z, RootKernel S H sap nr2 C x z → J.val x z)
    (x : X C.down.1) :
    (Hidden).eval (rootCoordinateTerm S H sap nr2 C J hKernel)
      (rootMap S H sap nr2 C x) =
      originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x) := by
  rcases C with ⟨⟨i,c⟩⟩
  cases c with
  | inl realTag =>
    cases realTag
    exact rootBaseTerm_proper S H sap nr2 J x
  | inr E =>
    have hEJ : E.val ≤ J.val := fun a b h =>
      hKernel a b ((rootKernel_proper S H sap nr2 E a b).mpr h)
    have hStep := OriginalCompletedNamedLabelledStep.upward (sap := sap) (nr2 := nr2)
      E J hEJ (Quotient.mk E.val.val x)
    have hValue := original_completed_primitive_function_of_graph S H sap nr2 hStep
    change originalCompletedPrimitiveFunction S H sap nr2
      (.inr (.inl ⟨i,⟨(E,J),hEJ⟩⟩))
      ((Hidden).eval (rootBaseTerm S H sap nr2 ⟨⟨i,.inr E⟩⟩) (.inl ⟨i,x⟩)) = _
    rw [rootBaseTerm_proper]
    exact hValue

/-- Both actual OLD anchors are obtained by their existing named terms;
no coordinate of an unrecorded representative is introduced. -/
theorem visible_branch_readouts {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    (hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty)
    (J : OriginalNamedHiddenCoordinate S H C.down.1)
    {R : X C.down.1 → X D.down.1 → Prop}
    (T : QuotientTransport.Transport (originalColourEqAsInvEq S H J.val) R)
    (hContains : ∀ x y, guardedFactorPullback S H sap nr2 q s x y → R x y) :
    (∀ x z, RootKernel S H sap nr2 C x z → J.val x z) ∧
    (∀ y z, RootKernel S H sap nr2 D y z →
      (original_named_hidden_transport_target S H sap nr2 J T).val y z) :=
  ⟨visible_source_kernel_le S H sap nr2 q s hMenu R J.val hContains T.kernel,
    visible_target_kernel_le S H sap nr2 q s hMenu J T hContains⟩

end
end CCO.GuardedOldSeams
