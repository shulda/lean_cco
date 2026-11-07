import CCO.GuardedTwoRoot.SourceAnchorSupport

/-! B057 C41--C43, C64--C65. The full restored pullback and its
diversity restriction are different relations. Only the former has
literal RAW root-kernel bisaturation; the latter has guarded TV1. -/

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

/-- The canonical real representative readout: identity at a real root,
and the existing named projection at a proper represented root. -/
def rootMap (C : (Lang).Sorts) (x : X C.down.1) :
    OriginalCompletedNamedCarrier S H :=
  (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩)

/-- The ACTUAL kernel of that readout, without an auxiliary quotient. -/
def RootKernel (C : (Lang).Sorts) (x z : X C.down.1) : Prop :=
  rootMap S H sap nr2 C x = rootMap S H sap nr2 C z

/-- ALL comparisons from ONE actual old root pair, before deleting the
real diagonal. This is the full relation Dhat, not a STRONG menu. -/
def fullFactorPullback {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    (x : X C.down.1) (y : X D.down.1) : Prop :=
  ∀ d : RootedComparison S H sap nr2 C D, d.Holds q s → d.pullback.Holds x y

/-- The source diversity relation D. Real equality is removed explicitly. -/
def guardedFactorPullback {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    (x : X C.down.1) (y : X D.down.1) : Prop :=
  fullFactorPullback S H sap nr2 q s x y ∧
    (⟨C.down.1,x⟩ : Sigma X) ≠ ⟨D.down.1,y⟩

theorem fullFactorPullback_fibre_iff {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {x x' : X C.down.1} {y y' : X D.down.1}
    (hx : RootKernel S H sap nr2 C x x')
    (hy : RootKernel S H sap nr2 D y y') :
    fullFactorPullback S H sap nr2 q s x y ↔
      fullFactorPullback S H sap nr2 q s x' y' := by
  have hLeft (d : RootedComparison S H sap nr2 C D) :
      namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 d.left) x =
        namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 d.left) x' := by
    apply Subtype.ext
    exact (representativeTerm_eval S H sap nr2 d.left x).trans
      ((congrArg ((Hidden).eval d.left) hx).trans
        (representativeTerm_eval S H sap nr2 d.left x').symm)
  have hRight (d : RootedComparison S H sap nr2 C D) :
      namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 d.right) y =
        namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 d.right) y' := by
    apply Subtype.ext
    exact (representativeTerm_eval S H sap nr2 d.right y).trans
      ((congrArg ((Hidden).eval d.right) hy).trans
        (representativeTerm_eval S H sap nr2 d.right y').symm)
  constructor <;> intro h d hd
  · change d.predicate
      (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 d.left) x')
      (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 d.right) y')
    rw [← hLeft d, ← hRight d]
    exact h d hd
  · change d.predicate
      (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 d.left) x)
      (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 d.right) y)
    rw [hLeft d, hRight d]
    exact h d hd

/-- Literal FULL relation equality H_b ; Dhat ; H_c = Dhat. -/
theorem fullFactorPullback_sandwich {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) :
    QuotientTransport.compose
      (QuotientTransport.compose (RootKernel S H sap nr2 C)
        (fullFactorPullback S H sap nr2 q s)) (RootKernel S H sap nr2 D) =
      fullFactorPullback S H sap nr2 q s := by
  funext x y
  apply propext
  constructor
  · rintro ⟨v,⟨u,hxu,huv⟩,hvy⟩
    exact (fullFactorPullback_fibre_iff S H sap nr2 q s hxu hvy.symm).mpr huv
  · intro hxy
    exact ⟨y,⟨x,rfl,hxy⟩,rfl⟩

/-- D is exactly the accepted simultaneous fine-atom menu, including
the quantifier over EVERY comparison in that same old factor. -/
theorem guardedFactorPullback_eq_menuRel {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) :
    guardedFactorPullback S H sap nr2 q s =
      S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨h,hne⟩
    obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hne
    refine ⟨a,?_,ha⟩
    rintro _ ⟨d,hd,rfl⟩
    exact d.pullback.atom_mem_of_holds ha (h d hd)
  · intro h
    refine ⟨?_,S.menuRel_ne h⟩
    obtain ⟨a,ha,hxy⟩ := h
    exact fun d hd => factorRecords_readback S H sap nr2 q s ha hxy d hd

/-- The exact diversity PALETTE of the full restored relation is the
same complete factor menu. Its possible real diagonal is invisible to
this operation, rather than being declared absent from the FULL relation. -/
theorem fullFactorPullback_diversityGuard {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) :
    S.diversityGuard (fullFactorPullback S H sap nr2 q s) =
      pairMenu S H sap nr2 (factorRecords S H sap nr2 q s) := by
  ext a
  constructor
  · rintro ⟨x,y,hFull,hxy⟩
    rintro _ ⟨d,hd,rfl⟩
    exact d.pullback.atom_mem_of_holds hxy (hFull d hd)
  · intro ha
    obtain ⟨x,y,hxy⟩ := S.realized a
    exact ⟨x,y,fun d hd => factorRecords_readback S H sap nr2 q s ha hxy d hd,hxy⟩

/-- Corrected guarded TV1: deleting the actual real diagonal AFTER
RAW composition recovers D. No RAW saturation is asserted for D. -/
theorem guardedFactorPullback_sandwich {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) :
    (fun x y =>
      QuotientTransport.compose
        (QuotientTransport.compose (RootKernel S H sap nr2 C)
          (guardedFactorPullback S H sap nr2 q s)) (RootKernel S H sap nr2 D) x y ∧
      (⟨C.down.1,x⟩ : Sigma X) ≠ ⟨D.down.1,y⟩) =
      guardedFactorPullback S H sap nr2 q s := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨v,⟨u,hxu,huv⟩,hvy⟩,hne⟩
    exact ⟨(fullFactorPullback_fibre_iff S H sap nr2 q s hxu hvy.symm).mpr huv.1,hne⟩
  · intro h
    exact ⟨⟨y,⟨x,rfl,h⟩,rfl⟩,h.2⟩

/-- A genuine nontrivial named quotient supplies the real/proper
projection counterexample to the printed unguarded TV1: a diversity
edge followed by its quotient kernel adds a true diagonal. -/
theorem diversity_projection_not_raw_saturated {i : ι}
    (J : OriginalNamedHiddenCoordinate S H i)
    (x y : X i) (hne : x ≠ y) (hxy : J.val x y) :
    QuotientTransport.compose (fun a b : X i => a ≠ b ∧ J.val a b) J.val x x ∧
      ¬ (x ≠ x ∧ J.val x x) := by
  exact ⟨⟨y,⟨hne,hxy⟩,J.val.val.symm hxy⟩,fun h => h.1 rfl⟩

/-- The counterexample has an actual source witness for EVERY existing
proper named coordinate: nonzero is part of that coordinate's proved
membership, so no additional witness/provider assumption is needed. -/
theorem named_projection_raw_saturation_fails {i : ι}
    (J : OriginalNamedHiddenCoordinate S H i) :
    QuotientTransport.compose (fun a b : X i => a ≠ b ∧ J.val a b) J.val ≠
      (fun a b : X i => a ≠ b ∧ J.val a b) := by
  classical
  have hWitness : ∃ x y : X i, x ≠ y ∧ J.val x y := by
    by_contra h
    apply (not_le_of_gt J.property.1)
    intro x y hxy
    change x = y
    by_contra hne
    exact h ⟨x,y,hne,hxy⟩
  obtain ⟨x,y,hne,hxy⟩ := hWitness
  obtain ⟨hDiag,hNot⟩ := diversity_projection_not_raw_saturated S H J x y hne hxy
  intro hEq
  exact hNot (Eq.mp (congrFun (congrFun hEq x) x) hDiag)

end
end CCO.GuardedOldSeams
