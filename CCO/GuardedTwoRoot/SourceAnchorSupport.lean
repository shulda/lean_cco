import CCO.GuardedTwoRoot.SourceRootSignature
import CCO.StabilizerSAP
import CCO.RawSource

/-! The anchor-support step is distinct from consistency of equations.
Complete factor menus are saturated by the ACTUAL root function fibres
away from the real diagonal. Original SAP supplies a common neighbour
avoiding that diagonal. Consequently every functional superrelation of
the full menu has source kernel containing the actual old root kernel.
No hidden SAP, completion or finite-orbit provider is assumed. -/

universe u v w r
namespace CCO.GuardedTwoRoot
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

include H in
theorem menuRel_invariant {i j : ι} (A : S.Menu i j) :
    TRel.Invariant (G := G) (S.menuRel A) := by
  rintro g x y ⟨a,ha,hxy⟩
  exact ⟨a,ha,(S.colourInvariant_of_homogeneous H g x y).trans hxy⟩

include H sap in
/-- A genuine invariant old diversity relation has a neighbour outside
ANY finite forbidden set, with the source endpoint fixed literally. -/
theorem invariant_diversity_fresh_right {i j : ι} (R : TRel X i j)
    (hInv : TRel.Invariant (G := G) R) (hNonempty : TRel.Nonempty R)
    (hDiversity : ∀ x y, R x y → (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩)
    (x : X i) (Z : Set (Sigma X)) (hZ : Z.Finite) :
    ∃ y : X j, R x y ∧ (⟨j,y⟩ : Sigma X) ∉ Z := by
  classical
  obtain ⟨y,hxy⟩ := S.raw_serial_of_homogeneous H R hNonempty hInv x
  let anchor : Sigma X := ⟨i,x⟩
  let output : Sigma X := ⟨j,y⟩
  let base : FiniteInduced (X := X) := FiniteInduced.ofFinset {anchor}
  have hAnchor : anchor ∈ base.vertices := by simp [base,FiniteInduced.ofFinset]
  have hOutput : output ∉ base.vertices := by
    intro h
    have he : output = anchor := by simpa [base,FiniteInduced.ofFinset] using h
    exact hDiversity x y hxy he.symm
  obtain ⟨other,⟨g,hFix,hMove⟩,hAvoid⟩ :=
    RealAction.orbit_has_fresh_point_of_SAP S H sap base output hOutput Z hZ
  have hFixX : g • x = x := by
    have h := (RealAction.mem_pointwiseStabilizer base.vertices g).mp hFix anchor hAnchor
    exact sigma_mk_injective h
  refine ⟨g • y,?_,?_⟩
  · simpa only [hFixX] using hInv g x y hxy
  · intro h
    exact hAvoid (hMove ▸ h)

theorem factor_menu_left_saturation {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {x z : X C.down.1} {y : X D.down.1}
    (hRoot : (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩) =
      (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,z⟩))
    (hxy : S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) x y)
    (hzy : (⟨C.down.1,z⟩ : Sigma X) ≠ ⟨D.down.1,y⟩) :
    S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) z y := by
  obtain ⟨a,ha,haxy⟩ := hxy
  obtain ⟨b,hb⟩ := S.some_colour_of_ne z y hzy
  refine ⟨b,?_,hb⟩
  rintro _ ⟨record,hRecord,rfl⟩
  have hOld := all_atoms_read_all_comparisons S H sap nr2 _ ha haxy
    record.pullback ⟨record,hRecord,rfl⟩
  have hLeft : namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 record.left) z =
      namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 record.left) x := by
    apply Subtype.ext
    exact (representativeTerm_eval S H sap nr2 record.left z).trans
      ((congrArg ((Hidden).eval record.left) hRoot.symm).trans
        (representativeTerm_eval S H sap nr2 record.left x).symm)
  apply record.pullback.atom_mem_of_holds hb
  change record.predicate
    (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 record.left) z)
    (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 record.right) y)
  rw [hLeft]
  exact hOld

theorem factor_menu_right_saturation {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {x : X C.down.1} {y z : X D.down.1}
    (hRoot : (Hidden).eval (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,y⟩) =
      (Hidden).eval (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,z⟩))
    (hxy : S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) x y)
    (hxz : (⟨C.down.1,x⟩ : Sigma X) ≠ ⟨D.down.1,z⟩) :
    S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) x z := by
  obtain ⟨a,ha,haxy⟩ := hxy
  obtain ⟨b,hb⟩ := S.some_colour_of_ne x z hxz
  refine ⟨b,?_,hb⟩
  rintro _ ⟨record,hRecord,rfl⟩
  have hOld := all_atoms_read_all_comparisons S H sap nr2 _ ha haxy
    record.pullback ⟨record,hRecord,rfl⟩
  have hRight : namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 record.right) z =
      namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 record.right) y := by
    apply Subtype.ext
    exact (representativeTerm_eval S H sap nr2 record.right z).trans
      ((congrArg ((Hidden).eval record.right) hRoot.symm).trans
        (representativeTerm_eval S H sap nr2 record.right y).symm)
  apply record.pullback.atom_mem_of_holds hb
  change record.predicate
    (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 record.left) x)
    (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 record.right) z)
  rw [hRight]
  exact hOld

/-- Every quotient-functional relation containing the complete factor
menu contains the ACTUAL left root function kernel in its source kernel. -/
theorem factor_left_kernel_le {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    (hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty)
    (R : X C.down.1 → X D.down.1 → Prop) (J : ColourEq S C.down.1)
    (hContains : ∀ x y,
      S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) x y → R x y)
    (hFunctional : ∀ x z y, R x y → R z y → J x z)
    (x z : X C.down.1)
    (hRoot : (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩) =
      (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,z⟩)) : J x z := by
  let A := pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)
  have hNonempty : TRel.Nonempty (S.menuRel A) := by
    obtain ⟨a,ha⟩ := hMenu
    obtain ⟨u,v,huv⟩ := S.realized a
    exact ⟨u,v,a,ha,huv⟩
  obtain ⟨y,hxy,hy⟩ := invariant_diversity_fresh_right S H sap (S.menuRel A)
    (menuRel_invariant S H A) hNonempty (fun _ _ h => S.menuRel_ne h)
    x {⟨C.down.1,z⟩} (Set.finite_singleton _)
  have hzy : (⟨C.down.1,z⟩ : Sigma X) ≠ ⟨D.down.1,y⟩ := by
    intro he
    exact hy (Set.mem_singleton_iff.mpr he.symm)
  exact hFunctional x z y (hContains x y hxy)
    (hContains z y (factor_menu_left_saturation S H sap nr2 q s hRoot hxy hzy))

/-- Symmetric target-kernel statement. Fresh old predecessors avoid
the literal real diagonal before either endpoint is substituted. -/
theorem factor_right_kernel_le {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    (hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty)
    (R : X C.down.1 → X D.down.1 → Prop) (K : ColourEq S D.down.1)
    (hContains : ∀ x y,
      S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) x y → R x y)
    (hFunctional : ∀ x y z, R x y → R x z → K y z)
    (y z : X D.down.1)
    (hRoot : (Hidden).eval (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,y⟩) =
      (Hidden).eval (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,z⟩)) : K y z := by
  let A := pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)
  have hNonempty : TRel.Nonempty (TRel.converse (S.menuRel A)) := by
    obtain ⟨a,ha⟩ := hMenu
    obtain ⟨u,v,huv⟩ := S.realized a
    exact ⟨v,u,a,ha,huv⟩
  obtain ⟨x,hxy,hx⟩ := invariant_diversity_fresh_right S H sap
    (TRel.converse (S.menuRel A))
    (fun g v u h => menuRel_invariant S H A g u v h) hNonempty
    (fun _ _ h => Ne.symm (S.menuRel_ne h)) y {⟨D.down.1,z⟩} (Set.finite_singleton _)
  have hxz : (⟨C.down.1,x⟩ : Sigma X) ≠ ⟨D.down.1,z⟩ := by
    intro he
    exact hx (Set.mem_singleton_iff.mpr he)
  exact hFunctional x y z (hContains x y hxy)
    (hContains x z (factor_menu_right_saturation S H sap nr2 q s hRoot hxy hxz))

/-- Kernel inclusion locates the anchor by an EXISTING named
projection/upward operation on the OLD root value itself. -/
theorem named_anchor_in_old_root_closure {C : (Lang).Sorts}
    (J : OriginalNamedHiddenCoordinate S H C.down.1)
    (hKernel : ∀ x z : X C.down.1,
      (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩) =
        (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,z⟩) → J.val x z)
    (x : X C.down.1) :
    originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x) ∈
      (Hidden).closureAt ((Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩)) := by
  rcases C with ⟨⟨i,c⟩⟩
  cases c with
  | inl realTag =>
    cases realTag
    have h := (Hidden).eval_mem_closed ((Hidden).closure_closed {Sum.inl ⟨i,x⟩})
      (rootBaseTerm S H sap nr2 ⟨⟨i,.inr J⟩⟩) ((Hidden).subset_closure _ rfl)
    rw [rootBaseTerm_proper] at h
    exact h
  | inr E =>
    have hEJ : E.val ≤ J.val := by
      intro a b hab
      apply hKernel a b
      rw [rootBaseTerm_proper,rootBaseTerm_proper]
      exact congrArg (originalCompletedNamedHiddenNode S H E) (Quotient.sound hab)
    rw [rootBaseTerm_proper]
    let symbol : OriginalCompletedPrimitiveSymbol S H :=
      .inr (.inl ⟨i,⟨(E,J),hEJ⟩⟩)
    have hStep := OriginalCompletedNamedLabelledStep.upward (sap := sap) (nr2 := nr2)
      E J hEJ (Quotient.mk E.val.val x)
    have hValue := original_completed_primitive_function_of_graph S H sap nr2 hStep
    have h := (Hidden).closure_closed {originalCompletedNamedHiddenNode S H E
        (Quotient.mk E.val.val x)} (ULift.up symbol)
      _ ((Hidden).subset_closure _ rfl)
    change originalCompletedPrimitiveFunction S H sap nr2 symbol
      (originalCompletedNamedHiddenNode S H E (Quotient.mk E.val.val x)) ∈ _ at h
    rw [hValue] at h
    exact h

namespace SourceThetaRootPackage
variable {S H sap nr2} {C D : (originalCompletedLanguage S H sap nr2).Sorts}
variable {q : (originalCompletedStructure S H sap nr2).Carrier C}
variable {s : (originalCompletedStructure S H sap nr2).Carrier D}
variable (T : SourceThetaRootPackage S H sap nr2 q s)

theorem signature_contains_full_menu
    (d : OriginalActualRootEquationDatum S H T.x T.y)
    (hd : d ∈ originalActualThetaRootSignature S H T.x T.y T.data) :
    ∀ x y, S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) x y → d.R x y := by
  rcases hd with hd | hd
  · obtain ⟨J,rfl⟩ := hd
    change ∀ x y, S.menuRel _ x y → T.data.direct.val.val x y
    rw [T.direct_eq]
    exact fun _ _ h => h
  · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hd
    obtain ⟨J,rfl⟩ := hk
    change ∀ x y, S.menuRel _ x y → (T.data.branch k).val.val x y
    rw [T.branch_eq]
    rintro x y ⟨a,ha,hxy⟩
    refine ⟨a,?_,hxy⟩
    have hPresent : a ∈ CCO.StrongExact.present S T.words := T.menu.symm ▸ ha
    exact hPresent _ (List.get_mem T.words k)

/-- EVERY direct/branch source anchor is an actual OLD endpoint term
value. New real representatives and private path vertices add no anchor. -/
theorem source_anchor_in_old_closure
    (d : OriginalActualRootEquationDatum S H T.x T.y)
    (hd : d ∈ originalActualThetaRootSignature S H T.x T.y T.data) :
    originalCompletedNamedHiddenNode S H d.J (Quotient.mk d.J.val.val T.x) ∈
      (originalCompletedStructure S H sap nr2).closureAt
        ((originalCompletedStructure S H sap nr2).eval
          (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,T.x⟩)) := by
  apply named_anchor_in_old_root_closure S H sap nr2 d.J
  intro x z hRoot
  exact factor_left_kernel_le S H sap nr2 q s ⟨T.atom,T.survives⟩ d.R d.J.val
    (T.signature_contains_full_menu d hd) d.T.kernel x z hRoot

/-- Every canonical transported TARGET anchor likewise lies in the
other OLD endpoint closure, with its literal named transported kernel. -/
theorem target_anchor_in_old_closure
    (d : OriginalActualRootEquationDatum S H T.x T.y)
    (hd : d ∈ originalActualThetaRootSignature S H T.x T.y T.data) :
    originalCompletedNamedHiddenNode S H (originalRootNamedTarget S H sap nr2 d.J d.T)
        (Quotient.mk (originalRootNamedTarget S H sap nr2 d.J d.T).val.val T.y) ∈
      (originalCompletedStructure S H sap nr2).closureAt
        ((originalCompletedStructure S H sap nr2).eval
          (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,T.y⟩)) := by
  apply named_anchor_in_old_root_closure S H sap nr2
    (originalRootNamedTarget S H sap nr2 d.J d.T)
  intro y z hRoot
  apply factor_right_kernel_le S H sap nr2 q s ⟨T.atom,T.survives⟩ d.R
    (originalRootNamedTarget S H sap nr2 d.J d.T).val
    (T.signature_contains_full_menu d hd) ?_ y z hRoot
  intro x a b hxa hxb
  change d.T.target a b
  exact (d.T.target_iff a b).mpr ⟨x,x,hxa,d.J.val.val.refl x,hxb⟩

def oldAnchorSupport : Set (OriginalCompletedNamedCarrier S H) :=
  (originalCompletedStructure S H sap nr2).closureAt
      ((originalCompletedStructure S H sap nr2).eval
        (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,T.x⟩)) ∪
    (originalCompletedStructure S H sap nr2).closureAt
      ((originalCompletedStructure S H sap nr2).eval
        (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,T.y⟩))

def signatureAnchors : Set (OriginalCompletedNamedCarrier S H) :=
  {v | ∃ d ∈ originalActualThetaRootSignature S H T.x T.y T.data,
    v = originalCompletedNamedHiddenNode S H d.J (Quotient.mk d.J.val.val T.x) ∨
    v = originalCompletedNamedHiddenNode S H (originalRootNamedTarget S H sap nr2 d.J d.T)
      (Quotient.mk (originalRootNamedTarget S H sap nr2 d.J d.T).val.val T.y)}

theorem oldAnchorSupport_finite : T.oldAnchorSupport.Finite :=
  (original_completed_all_singleton_closures_finite S H sap nr2 _).union
    (original_completed_all_singleton_closures_finite S H sap nr2 _)

theorem signatureAnchors_subset_old : T.signatureAnchors ⊆ T.oldAnchorSupport := by
  rintro v ⟨d,hd,rfl | rfl⟩
  · exact Or.inl (T.source_anchor_in_old_closure d hd)
  · exact Or.inr (T.target_anchor_in_old_closure d hd)

/-- The ENTIRE functional closure of ALL signature anchors remains in
the two OLD endpoint closures, independently of transition word length. -/
theorem full_anchor_closure_subset_old :
    (originalCompletedStructure S H sap nr2).closure T.signatureAnchors ⊆ T.oldAnchorSupport :=
  (originalCompletedStructure S H sap nr2).closure_minimal
    ((originalCompletedStructure S H sap nr2).closed_union
      ((originalCompletedStructure S H sap nr2).closure_closed _)
      ((originalCompletedStructure S H sap nr2).closure_closed _))
    T.signatureAnchors_subset_old

theorem old_anchor_support_bound : T.oldAnchorSupport.ncard ≤
    2 * originalSourceUniformNormalCodeBudget S H := by
  apply (Set.ncard_union_le _ _).trans
  have hLeft := original_completed_any_generator_uniform S H sap nr2
    ((originalCompletedStructure S H sap nr2).eval
      (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,T.x⟩))
  have hRight := original_completed_any_generator_uniform S H sap nr2
    ((originalCompletedStructure S H sap nr2).eval
      (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,T.y⟩))
  rw [← original_completed_structure_closureAt_eq] at hLeft hRight
  exact (Nat.add_le_add hLeft hRight).trans (by omega)

/-- Actual source-derived anchor budget, including every named unary
continuation, with no supplied anchor-count premise. -/
theorem full_anchor_closure_bound :
    ((originalCompletedStructure S H sap nr2).closure T.signatureAnchors).ncard ≤
      2 * originalSourceUniformNormalCodeBudget S H :=
  (Set.ncard_le_ncard T.full_anchor_closure_subset_old T.oldAnchorSupport_finite).trans
    T.old_anchor_support_bound

end SourceThetaRootPackage

end
end CCO.GuardedTwoRoot
