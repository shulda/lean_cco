import CCO.GuardedOldSeams.Visibility
import CCO.GuardedTwoRoot.JoinedClosedImage
import CCO.UnarySupport.TypedTerms

/-! B057 C49--C54. A quotient-functional positive branch uses existing
named quotient maps. ONE actual induced embedding of the complete OLD
support reflects its equation to literal partial-source term values.
No equation is claimed for an unconstrained pair or a nonfunctional
primitive comparison used in the intersection. -/

universe u v w r z
namespace CCO.GuardedOldSeams
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)

/-- The exact same unary syntax in the genuine partial-domain encoding.
This changes neither a named symbol nor any term value. -/
def oldTerm {C D : ((originalCompletedLanguage S H sap nr2)).Sorts} : Term (originalCompletedLanguage S H sap nr2) C D →
    CCO.UnarySupport.Structure.Term (originalPartialSignature S H sap nr2) C D := by
  intro t
  induction t with
  | id => exact CCO.UnarySupport.Structure.Term.var (L := originalPartialSignature S H sap nr2) C
  | func F t ih =>
    exact CCO.UnarySupport.Structure.Term.func
      (L := originalPartialSignature S H sap nr2) F ih

theorem oldTerm_target_eval {C D : ((originalCompletedLanguage S H sap nr2)).Sorts} (t : Term (originalCompletedLanguage S H sap nr2) C D)
    (x : OriginalCompletedNamedCarrier S H) (hx : ((originalCompletedStructure S H sap nr2)).sort x = C) :
    ((originalCompletedStructure S H sap nr2)).eval t x ∈ ((originalPartialTarget S H sap nr2)).eval (oldTerm S H sap nr2 t) x := by
  classical
  induction t with
  | id => rfl
  | func F t ih =>
    refine ⟨((originalCompletedStructure S H sap nr2)).eval t x,ih,?_⟩
    change ((originalCompletedStructure S H sap nr2)).func F (((originalCompletedStructure S H sap nr2)).eval t x) ∈
      if ((originalCompletedStructure S H sap nr2)).sort (((originalCompletedStructure S H sap nr2)).eval t x) = ((originalCompletedLanguage S H sap nr2)).input F then
        {((originalCompletedStructure S H sap nr2)).func F (((originalCompletedStructure S H sap nr2)).eval t x)} else ∅
    rw [if_pos (((originalCompletedStructure S H sap nr2)).eval_sort t hx)]
    rfl

/-- Both values exist in the OLD source, and are literally the same
source vertex. This is stronger than equality of future target images. -/
def LiteralOldEquation {P : Type z}
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    {C D E : ((originalCompletedLanguage S H sap nr2)).Sorts} (left : Term (originalCompletedLanguage S H sap nr2) C E) (right : Term (originalCompletedLanguage S H sap nr2) D E)
    (b c : P) : Prop :=
  ∃ a : P, a ∈ F.eval (oldTerm S H sap nr2 left) b ∧
    a ∈ F.eval (oldTerm S H sap nr2 right) c

/-- Domain reflection retrieves both OLD values; injectivity of this
ONE complete support embedding reflects their target equality. -/
theorem literalOldEquation_of_embedding {P : Type z}
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F ((originalPartialTarget S H sap nr2)))
    {C D E : ((originalCompletedLanguage S H sap nr2)).Sorts} (left : Term (originalCompletedLanguage S H sap nr2) C E) (right : Term (originalCompletedLanguage S H sap nr2) D E)
    (b c : P) (hb : F.sort b = C) (hc : F.sort c = D)
    (hEq : ((originalCompletedStructure S H sap nr2)).eval left (e.point b) = ((originalCompletedStructure S H sap nr2)).eval right (e.point c)) :
    LiteralOldEquation S H sap nr2 F left right b c := by
  obtain ⟨a,ha,hea⟩ := e.reflect_eval (oldTerm S H sap nr2 left)
    (oldTerm_target_eval S H sap nr2 left (e.point b) ((e.sort_eq b).trans hb))
  obtain ⟨a',ha',hea'⟩ := e.reflect_eval (oldTerm S H sap nr2 right)
    (oldTerm_target_eval S H sap nr2 right (e.point c) ((e.sort_eq c).trans hc))
  have hOld : a = a' := e.injective (hea.trans (hEq.trans hea'.symm))
  exact ⟨a,ha,hOld.symm ▸ ha'⟩

theorem LiteralOldEquation.values_equal {P : Type z}
    {F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P}
    {C D E : ((originalCompletedLanguage S H sap nr2)).Sorts} {left : Term (originalCompletedLanguage S H sap nr2) C E} {right : Term (originalCompletedLanguage S H sap nr2) D E}
    {b c : P} (h : LiteralOldEquation S H sap nr2 F left right b c)
    {a a' : P} (ha : a ∈ F.eval (oldTerm S H sap nr2 left) b)
    (ha' : a' ∈ F.eval (oldTerm S H sap nr2 right) c) : a = a' := by
  obtain ⟨v,hv,hv'⟩ := h
  exact (F.eval_functional _ ha hv).trans (F.eval_functional _ hv' ha')

/-- A literal equation in the complete closed OLD support is the same
literal equation in the original source. The inclusion changes no vertex
and needs no embedding/completion of that whole original source. -/
theorem LiteralOldEquation.of_closed_support {P : Type z}
    {F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P}
    {A : Set P} (hA : F.IsClosed A)
    {C D E : ((originalCompletedLanguage S H sap nr2)).Sorts} {left : Term (originalCompletedLanguage S H sap nr2) C E} {right : Term (originalCompletedLanguage S H sap nr2) D E}
    {b c : A}
    (h : LiteralOldEquation S H sap nr2 (F.induce A hA) left right b c) :
    LiteralOldEquation S H sap nr2 F left right b.val c.val := by
  obtain ⟨a,ha,ha'⟩ := h
  exact ⟨a.val,(F.inclusion A hA).toHom.map_eval _ ha,
    (F.inclusion A hA).toHom.map_eval _ ha'⟩

/-- A positive branch is already one of the actual complete named RAW
primitive symbols. Its relation and functionality are the actual old
positive-word semantics, not a supplied transition provider. -/
def positiveBranchSymbol {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z) :
    OriginalNamedRawTransitionSymbol S H i j :=
  ⟨⟨J,originalPositiveStrongBranchRelation S H sap p⟩,
    hKernel,fun _ _ h => S.menuRel_ne h⟩

def positiveBranchTarget {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z) :
    OriginalNamedHiddenCoordinate S H j :=
  originalNamedRawTransitionSymbol_target S H sap nr2
    (positiveBranchSymbol S H sap J p hKernel)

/-- Existing actual primitive in the fixed named language. -/
def positiveBranchTransitionTerm {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z) :
    Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inr J⟩⟩
      ⟨⟨j,.inr (positiveBranchTarget S H sap nr2 J p hKernel)⟩⟩ :=
  Term.func (L := originalCompletedLanguage S H sap nr2)
    (⟨.inr (.inr ⟨i,⟨j,positiveBranchSymbol S H sap J p hKernel⟩⟩)⟩ : ((originalCompletedLanguage S H sap nr2)).Func) (.id _)

theorem positiveBranchTransitionTerm_edge {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (x : X i) (y : X j) (hxy : S.menuRel (PositiveWord.profile S p) x y) :
    ((originalCompletedStructure S H sap nr2)).eval (positiveBranchTransitionTerm S H sap nr2 J p hKernel)
      (originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)) =
      originalCompletedNamedHiddenNode S H (positiveBranchTarget S H sap nr2 J p hKernel)
        (Quotient.mk (positiveBranchTarget S H sap nr2 J p hKernel).val.val y) := by
  let symbol := positiveBranchSymbol S H sap J p hKernel
  have hStep := OriginalCompletedNamedLabelledStep.raw (sap := sap) (nr2 := nr2)
    symbol (Quotient.mk J.val.val x)
  have hValue := original_completed_primitive_function_of_graph S H sap nr2 hStep
  change originalCompletedPrimitiveFunction S H sap nr2
    (.inr (.inr ⟨i,⟨j,symbol⟩⟩))
      (originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)) = _
  exact hValue.trans (congrArg (originalCompletedNamedHiddenNode S H _)
    ((originalNamedRawTransitionSymbol_transport S H symbol).quotientEquiv_edge hxy))

section ActualBranch
variable {C D : ((originalCompletedLanguage S H sap nr2)).Sorts}
variable (q : ((originalCompletedStructure S H sap nr2)).Carrier C) (s : ((originalCompletedStructure S H sap nr2)).Carrier D)
variable (hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty)
variable (J : OriginalNamedHiddenCoordinate S H C.down.1)
variable (p : PositiveWord S C.down.1 D.down.1)
variable (hKernel : ∀ x z : X C.down.1,
  (∃ y : X D.down.1, S.menuRel (PositiveWord.profile S p) x y ∧
    S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
variable (hContains : pairMenu S H sap nr2 (factorRecords S H sap nr2 q s) ⊆
  PositiveWord.profile S p)

include hContains in
theorem positiveBranch_contains_guard : ∀ x y,
    guardedFactorPullback S H sap nr2 q s x y →
      S.menuRel (PositiveWord.profile S p) x y := by
  intro x y h
  rw [guardedFactorPullback_eq_menuRel] at h
  obtain ⟨a,ha,hxy⟩ := h
  exact ⟨a,hContains ha,hxy⟩

include hMenu hKernel hContains in
def branchSourceKernel : ∀ x z, RootKernel S H sap nr2 C x z → J.val x z :=
  visible_source_kernel_le S H sap nr2 q s hMenu _ J.val
    (positiveBranch_contains_guard S H sap nr2 q s p hContains)
    (fun x z y hxy hzy => hKernel x z ⟨y,hxy,hzy⟩)

include hMenu hContains in
def branchTargetKernel : ∀ y z, RootKernel S H sap nr2 D y z →
    (positiveBranchTarget S H sap nr2 J p hKernel).val y z :=
  visible_target_kernel_le S H sap nr2 q s hMenu J
    (originalNamedRawTransitionSymbol_transport S H
      (positiveBranchSymbol S H sap J p hKernel))
    (positiveBranch_contains_guard S H sap nr2 q s p hContains)

include hMenu hContains in
def branchLeftTerm : Term (originalCompletedLanguage S H sap nr2) C
    ⟨⟨D.down.1,.inr (positiveBranchTarget S H sap nr2 J p hKernel)⟩⟩ :=
  (positiveBranchTransitionTerm S H sap nr2 J p hKernel).comp
    (rootCoordinateTerm S H sap nr2 C J
      (branchSourceKernel S H sap nr2 q s hMenu J p hKernel hContains))

include hMenu hContains in
def branchRightTerm : Term (originalCompletedLanguage S H sap nr2) D
    ⟨⟨D.down.1,.inr (positiveBranchTarget S H sap nr2 J p hKernel)⟩⟩ :=
  rootCoordinateTerm S H sap nr2 D (positiveBranchTarget S H sap nr2 J p hKernel)
    (branchTargetKernel S H sap nr2 q s hMenu J p hKernel hContains)

theorem branch_terms_edge (x : X C.down.1) (y : X D.down.1)
    (hxy : S.menuRel (PositiveWord.profile S p) x y) :
    ((originalCompletedStructure S H sap nr2)).eval (branchLeftTerm S H sap nr2 q s hMenu J p hKernel hContains)
        (rootMap S H sap nr2 C x) =
      ((originalCompletedStructure S H sap nr2)).eval (branchRightTerm S H sap nr2 q s hMenu J p hKernel hContains)
        (rootMap S H sap nr2 D y) := by
  unfold branchLeftTerm branchRightTerm
  exact (((originalCompletedStructure S H sap nr2)).eval_comp _ _ _).trans
    ((congrArg (((originalCompletedStructure S H sap nr2)).eval
      (positiveBranchTransitionTerm S H sap nr2 J p hKernel))
      (rootCoordinateTerm_eval S H sap nr2 C J
        (branchSourceKernel S H sap nr2 q s hMenu J p hKernel hContains) x)).trans
      ((positiveBranchTransitionTerm_edge S H sap nr2 J p hKernel x y hxy).trans
        (rootCoordinateTerm_eval S H sap nr2 D (positiveBranchTarget S H sap nr2 J p hKernel)
          (branchTargetKernel S H sap nr2 q s hMenu J p hKernel hContains) y).symm))

include hContains in
/-- ANY survivor in the complete source menu supplies an existing named
atomic representative of the WHOLE branch map and its actual target.
No generic invariant target is silently declared named. -/
theorem branch_has_existing_atomic_symbol
    (a : S.Atom C.down.1 D.down.1)
    (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) :
    ∃ d : OriginalNamedAtomicTransitionSymbol S H C.down.1 D.down.1,
      ∃ hd : d.val.1 = J, d.val.2 = a ∧
      ∃ hK : (originalNamedAtomicTransitionSymbol_transport S H d).target =
          (originalPositiveStrongBranch_transport S H sap J.val p hKernel).target,
        ∀ v : Quotient J.val.val,
          QuotientTransport.InvEq.quotientCongr hK
            ((originalNamedAtomicTransitionSymbol_transport S H d).quotientEquiv (hd.symm ▸ v)) =
            original_named_hidden_transport_function S H sap nr2 J
              (originalPositiveStrongBranch_transport S H sap J.val p hKernel) v :=
  original_named_positive_branch_has_atomic_symbol S H sap nr2 J p hKernel a (hContains ha)

end ActualBranch

/-- The atom is selected from the SAME full factor menu. Its actual
symbol already belongs to the fixed finite named atomic language. -/
def branchAtomicSymbol {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S p) :
    OriginalNamedAtomicTransitionSymbol S H i j :=
  ⟨⟨J,a⟩,fun x z y hxy hzy => hKernel x z ⟨y,⟨a,ha,hxy⟩,⟨a,ha,hzy⟩⟩⟩

def branchAtomicRawSymbol {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S p) :
    OriginalNamedRawTransitionSymbol S H i j :=
  originalNamedAtomicSymbol_asRaw S H (branchAtomicSymbol S H J p hKernel a ha)

def branchAtomicTarget {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S p) :
    OriginalNamedHiddenCoordinate S H j :=
  originalNamedRawTransitionSymbol_target S H sap nr2
    (branchAtomicRawSymbol S H J p hKernel a ha)

/-- Actual atomic and whole-branch labels are equal at EVERY old target.
This derives the target agreement rather than postulating naming or
functionality of a new symbol. -/
theorem branchAtomic_labels {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S p) (y : X j) :
    (originalNamedRawTransitionSymbol_transport S H
      (branchAtomicRawSymbol S H J p hKernel a ha)).label y =
    (originalNamedRawTransitionSymbol_transport S H
      (positiveBranchSymbol S H sap J p hKernel)).label y := by
  let T := originalNamedRawTransitionSymbol_transport S H
    (positiveBranchSymbol S H sap J p hKernel)
  have hAtom : a ∈ S.diversityGuard (originalPositiveStrongBranchRelation S H sap p).val.val := by
    rw [originalPositiveStrongBranchRelation_guard]
    exact ha
  obtain ⟨Ta,hLabels,_⟩ := original_atomic_transport_agrees_with_whole_raw S H J.val _ T a hAtom
  have hTa : originalNamedRawTransitionSymbol_transport S H
      (branchAtomicRawSymbol S H J p hKernel a ha) = Ta := Subsingleton.elim _ _
  rw [hTa]
  exact hLabels y

/-- The atomic representative has literally the SAME existing named
target as the whole positive branch. Equality is in the actual FULL
kernel, so representedness proofs cannot introduce another coordinate. -/
theorem branchAtomicTarget_eq_positiveBranchTarget {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S p) :
    branchAtomicTarget S H sap nr2 J p hKernel a ha =
      positiveBranchTarget S H sap nr2 J p hKernel := by
  apply Subtype.ext
  apply ColourEq.ext
  intro y z
  change (originalNamedRawTransitionSymbol_transport S H
    (branchAtomicRawSymbol S H J p hKernel a ha)).label y =
      (originalNamedRawTransitionSymbol_transport S H
        (branchAtomicRawSymbol S H J p hKernel a ha)).label z ↔
    (originalNamedRawTransitionSymbol_transport S H
      (positiveBranchSymbol S H sap J p hKernel)).label y =
      (originalNamedRawTransitionSymbol_transport S H
        (positiveBranchSymbol S H sap J p hKernel)).label z
  rw [branchAtomic_labels S H sap J p hKernel a ha y,
    branchAtomic_labels S H sap J p hKernel a ha z]
  rfl

def branchAtomicTransitionTerm {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S p) :
    Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inr J⟩⟩
      ⟨⟨j,.inr (branchAtomicTarget S H sap nr2 J p hKernel a ha)⟩⟩ :=
  Term.func (L := originalCompletedLanguage S H sap nr2)
    (⟨.inr (.inr ⟨i,⟨j,branchAtomicRawSymbol S H J p hKernel a ha⟩⟩)⟩ : ((originalCompletedLanguage S H sap nr2)).Func) (.id _)

theorem branchAtomicTransitionTerm_edge {i j : ι}
    (J : OriginalNamedHiddenCoordinate S H i) (p : PositiveWord S i j)
    (hKernel : ∀ x z : X i,
      (∃ y : X j, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (a : S.Atom i j) (ha : a ∈ PositiveWord.profile S p)
    (x : X i) (y : X j) (hxy : S.atomRel a x y) :
    ((originalCompletedStructure S H sap nr2)).eval (branchAtomicTransitionTerm S H sap nr2 J p hKernel a ha)
      (originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)) =
      originalCompletedNamedHiddenNode S H (branchAtomicTarget S H sap nr2 J p hKernel a ha)
        (Quotient.mk (branchAtomicTarget S H sap nr2 J p hKernel a ha).val.val y) := by
  let symbol := branchAtomicRawSymbol S H J p hKernel a ha
  have hValue := original_completed_primitive_function_of_graph S H sap nr2
    (OriginalCompletedNamedLabelledStep.raw (sap := sap) (nr2 := nr2)
      symbol (Quotient.mk J.val.val x))
  change originalCompletedPrimitiveFunction S H sap nr2
    (.inr (.inr ⟨i,⟨j,symbol⟩⟩))
      (originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val x)) = _
  exact hValue.trans (congrArg (originalCompletedNamedHiddenNode S H _)
    ((originalNamedRawTransitionSymbol_transport S H symbol).quotientEquiv_edge hxy))

section AtomicReadouts
variable {C D : ((originalCompletedLanguage S H sap nr2)).Sorts}
variable (q : ((originalCompletedStructure S H sap nr2)).Carrier C) (s : ((originalCompletedStructure S H sap nr2)).Carrier D)
variable (hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty)
variable (J : OriginalNamedHiddenCoordinate S H C.down.1)
variable (p : PositiveWord S C.down.1 D.down.1)
variable (hKernel : ∀ x z : X C.down.1,
  (∃ y : X D.down.1, S.menuRel (PositiveWord.profile S p) x y ∧
    S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
variable (hContains : pairMenu S H sap nr2 (factorRecords S H sap nr2 q s) ⊆
  PositiveWord.profile S p)
variable (a : S.Atom C.down.1 D.down.1) (ha : a ∈ PositiveWord.profile S p)

include hMenu hContains in
def branchAtomicTargetKernel : ∀ y z, RootKernel S H sap nr2 D y z →
    (branchAtomicTarget S H sap nr2 J p hKernel a ha).val y z := by
  intro y z hyz
  have hWhole := branchTargetKernel S H sap nr2 q s hMenu J p hKernel hContains y z hyz
  change (originalNamedRawTransitionSymbol_transport S H
    (branchAtomicRawSymbol S H J p hKernel a ha)).label y =
      (originalNamedRawTransitionSymbol_transport S H
        (branchAtomicRawSymbol S H J p hKernel a ha)).label z
  rw [branchAtomic_labels S H sap J p hKernel a ha y,
    branchAtomic_labels S H sap J p hKernel a ha z]
  exact hWhole

include hMenu hContains in
def branchAtomicLeftTerm : Term (originalCompletedLanguage S H sap nr2) C
    ⟨⟨D.down.1,.inr (branchAtomicTarget S H sap nr2 J p hKernel a ha)⟩⟩ :=
  (branchAtomicTransitionTerm S H sap nr2 J p hKernel a ha).comp
    (rootCoordinateTerm S H sap nr2 C J
      (branchSourceKernel S H sap nr2 q s hMenu J p hKernel hContains))

include hMenu hContains in
def branchAtomicRightTerm : Term (originalCompletedLanguage S H sap nr2) D
    ⟨⟨D.down.1,.inr (branchAtomicTarget S H sap nr2 J p hKernel a ha)⟩⟩ :=
  rootCoordinateTerm S H sap nr2 D (branchAtomicTarget S H sap nr2 J p hKernel a ha)
    (branchAtomicTargetKernel S H sap nr2 q s hMenu J p hKernel hContains a ha)

theorem branch_atomic_terms_edge (x : X C.down.1) (y : X D.down.1)
    (hxy : S.atomRel a x y) :
    ((originalCompletedStructure S H sap nr2)).eval (branchAtomicLeftTerm S H sap nr2 q s hMenu J p hKernel hContains a ha)
        (rootMap S H sap nr2 C x) =
      ((originalCompletedStructure S H sap nr2)).eval (branchAtomicRightTerm S H sap nr2 q s hMenu J p hKernel hContains a ha)
        (rootMap S H sap nr2 D y) := by
  unfold branchAtomicLeftTerm branchAtomicRightTerm
  exact (((originalCompletedStructure S H sap nr2)).eval_comp _ _ _).trans
    ((congrArg (((originalCompletedStructure S H sap nr2)).eval
      (branchAtomicTransitionTerm S H sap nr2 J p hKernel a ha))
      (rootCoordinateTerm_eval S H sap nr2 C J
        (branchSourceKernel S H sap nr2 q s hMenu J p hKernel hContains) x)).trans
      ((branchAtomicTransitionTerm_edge S H sap nr2 J p hKernel a ha x y hxy).trans
        (rootCoordinateTerm_eval S H sap nr2 D (branchAtomicTarget S H sap nr2 J p hKernel a ha)
          (branchAtomicTargetKernel S H sap nr2 q s hMenu J p hKernel hContains a ha) y).symm))

end AtomicReadouts

/-- Complete source15 OLD branch equation. The common atom, both visible
readouts and the equation are all derived from this SAME actual complete
support. The final equality is reflected through its actual induced
embedding into the canonical interpretation, before any completion. -/
theorem old_branch_equation
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F ((originalPartialTarget S H sap nr2)))
    (b c : P) (hbc : b ≠ c)
    (J : OriginalNamedHiddenCoordinate S H (F.sort b).down.1)
    (p : PositiveWord S (F.sort b).down.1 (F.sort c).down.1)
    (hKernel : ∀ x z : X (F.sort b).down.1,
      (∃ y : X (F.sort c).down.1, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (hContains : pairMenu S H sap nr2 (factorRecords S H sap nr2
      ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩) ⊆ PositiveWord.profile S p) :
    ∃ hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2
        ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩)).Nonempty,
      LiteralOldEquation S H sap nr2 F
        (branchLeftTerm S H sap nr2 ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩
          hMenu J p hKernel hContains)
        (branchRightTerm S H sap nr2 ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩
          hMenu J p hKernel hContains) b c := by
  obtain ⟨x,y,a,hxy,ha⟩ := one_factor_all_comparisons S H sap nr2 F e b c hbc
  have hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2
    ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩)).Nonempty := ⟨a,ha⟩
  obtain ⟨f,hfb,hfc,_,_⟩ := one_factor_complete_closed_image S H sap nr2 F e b c ha hxy
  refine ⟨hMenu,?_⟩
  apply literalOldEquation_of_embedding S H sap nr2 F f _ _ b c rfl rfl
  rw [hfb,hfc]
  exact branch_terms_edge S H sap nr2
    ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩ hMenu J p hKernel hContains
    x y ⟨a,hContains ha,hxy⟩

/-- Literal TOE with the EXISTING named ATOMIC representative itself as
the transition term. Its transported proper represented target and root
visibility are derived from the whole functional branch, not assumed. -/
theorem old_branch_atomic_equation
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F ((originalPartialTarget S H sap nr2)))
    (b c : P) (hbc : b ≠ c)
    (J : OriginalNamedHiddenCoordinate S H (F.sort b).down.1)
    (p : PositiveWord S (F.sort b).down.1 (F.sort c).down.1)
    (hKernel : ∀ x z : X (F.sort b).down.1,
      (∃ y : X (F.sort c).down.1, S.menuRel (PositiveWord.profile S p) x y ∧
        S.menuRel (PositiveWord.profile S p) z y) → J.val x z)
    (hContains : pairMenu S H sap nr2 (factorRecords S H sap nr2
      ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩) ⊆ PositiveWord.profile S p) :
    ∃ (a : S.Atom (F.sort b).down.1 (F.sort c).down.1)
      (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2
        ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩))
      (hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2
        ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩)).Nonempty),
      LiteralOldEquation S H sap nr2 F
        (branchAtomicLeftTerm S H sap nr2 ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩
          hMenu J p hKernel hContains a (hContains ha))
        (branchAtomicRightTerm S H sap nr2 ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩
          hMenu J p hKernel hContains a (hContains ha)) b c := by
  obtain ⟨x,y,a,hxy,ha⟩ := one_factor_all_comparisons S H sap nr2 F e b c hbc
  have hMenu : (pairMenu S H sap nr2 (factorRecords S H sap nr2
    ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩)).Nonempty := ⟨a,ha⟩
  obtain ⟨f,hfb,hfc,_,_⟩ := one_factor_complete_closed_image S H sap nr2 F e b c ha hxy
  refine ⟨a,ha,hMenu,?_⟩
  apply literalOldEquation_of_embedding S H sap nr2 F f _ _ b c rfl rfl
  rw [hfb,hfc]
  exact branch_atomic_terms_edge S H sap nr2
    ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩ hMenu J p hKernel hContains
    a (hContains ha) x y hxy

end
end CCO.GuardedOldSeams
