import CCO.APRamseyReadout.ActualSource
import CCO.CloneTupleGeometry.SelectedFamilyQF
import CCO.UnaryTermsReturn.CompletedNamedNodeEquality

/-! The literal B060 quotient coordinates in the ONE canonical B061
hidden interpretation. Only proof of named membership is forgotten;
no representative, additional cell vertex or new quotient chart is chosen.
Diagonal equality and named diversity cylinders remain separate. -/

universe u v w p z
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.CloneTupleGeometry.OwnerStage
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.QuotientTransport
noncomputable section
variable (B : OwnerStage.{u,v,w})

abbrev CoordinateLanguage (ht : B.Terminal) :=
  CCO.TerminalHiddenHN.binaryLanguage (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))

abbrev CoordinateModel (ht : B.Terminal) {V : Type z}
    (C : CCO.UnarySupport.Structure (Sig B ht) V) :=
  CCO.TerminalHiddenHN.binaryStructure (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) C

abbrev CoordinateTarget (ht : B.Terminal) := CoordinateModel B ht (Target B ht)

abbrev OrderedCoordinateLanguage (ht : B.Terminal) :=
  CCO.TerminalHiddenHN.orderedLanguage (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))

abbrev OrderedCoordinateModel (ht : B.Terminal) {V : Type z}
    (C : CCO.UnarySupport.Structure (Sig B ht) V) [LinearOrder V] :=
  CCO.TerminalHiddenHN.orderedStructure (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) C

abbrev NamedCoordinate (i : B.Sorts) :=
  OriginalNamedHiddenCoordinate (cloneSource B) (HF B) i

/-- Clone homogeneity already has the full automorphism group. Thus HF
changes only a proof, and the existing actual RAW witness is unchanged. -/
def namedCoordinateHF (ht : B.Terminal) (i : B.Sorts)
    (J : FullCloneProperMI B.source i) : NamedCoordinate B i :=
  B.namedMICoordinate ht i J

@[simp] theorem namedCoordinateHF_kernel (ht : B.Terminal) (i : B.Sorts)
    (J : FullCloneProperMI B.source i) : (namedCoordinateHF B ht i J).val = J.val := rfl

/-- Every canonical proper named sort is an actual FULL proper MI.
The entire proper age is retained, beyond any selected visible chart. -/
def fullMIOfNamed (i : B.Sorts) (D : NamedCoordinate B i) :
    FullCloneProperMI B.source i := by
  let e := originalFullColourEqInvEqOrderIso (cloneSource B) (HF B) (i := i)
  have hMI := D.property.2.1
  change ProperMeetIrreducible (e D.val) at hMI
  refine ⟨D.val,ne_of_gt D.property.1,?_⟩
  apply (CCO.RealClosure.SAP.FiniteLattice.proper_mi_iff D.val).mpr
  constructor
  · intro htop
    exact hMI.1 ((congrArg e htop).trans e.map_top)
  · intro A C hAC
    have hmeet : e D.val = e A ⊓ e C :=
      (congrArg e hAC).symm.trans (e.map_inf A C)
    rcases hMI.2 (e A) (e C) hmeet with hA | hC
    · exact Or.inl (e.injective hA).symm
    · exact Or.inr (e.injective hC).symm

def coordinateSort (ht : B.Terminal) {i : B.Sorts} (D : NamedCoordinate B i) :
    (Sig B ht).Sorts := ⟨⟨i,.inr D⟩⟩

def namedNode {i : B.Sorts} (D : NamedCoordinate B i) (q : Quotient D.val.val) : Values B :=
  originalCompletedNamedHiddenNode (cloneSource B) (HF B) D q

def coordinateNode (ht : B.Terminal) {i : B.Sorts}
    (J : FullCloneProperMI B.source i) (q : Quotient J.val.val) : Values B :=
  namedNode B (namedCoordinateHF B ht i J) q

@[simp] theorem namedNode_sort (ht : B.Terminal) {i : B.Sorts}
    (D : NamedCoordinate B i) (q : Quotient D.val.val) :
    (Target B ht).sort (namedNode B D q) = coordinateSort B ht D := rfl

theorem namedNode_injective {i : B.Sorts} (D : NamedCoordinate B i) :
    Function.Injective (namedNode B D) :=
  original_completed_hidden_node_injective (cloneSource B) (HF B) D

theorem namedNode_eq_iff {i j : B.Sorts} (D : NamedCoordinate B i)
    (E : NamedCoordinate B j) (q : Quotient D.val.val) (r : Quotient E.val.val) :
    namedNode B D q = namedNode B E r ↔
      QuotientPairQF.HiddenEqual (cloneSource B) D.val E.val q r := by
  constructor
  · intro h
    exact Sum.inr.inj (congrArg
      (originalCompletedCarrierForget (cloneSource B) (HF B)) h)
  · intro h
    exact congrArg Sum.inr (Subtype.ext h)

abbrev ProperValue (ht : B.Terminal) :=
  {x : Values B // ProperSort B ht ((Hidden B ht).sort x)}

def properForget (ht : B.Terminal) : ProperValue B ht →
    QuotientPairQF.HiddenPoint (cloneSource B)
  | ⟨.inl x,hx⟩ => by change False at hx; exact hx.elim
  | ⟨.inr x,_⟩ => x.val

theorem properForget_injective (ht : B.Terminal) :
    Function.Injective (properForget B ht) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h
  cases x with
  | inl x => change False at hx; exact hx.elim
  | inr x =>
    cases y with
    | inl y => change False at hy; exact hy.elim
    | inr y =>
      change x.val = y.val at h
      have he : x = y := Subtype.ext h
      cases he
      rfl

@[simp] theorem properForget_node (ht : B.Terminal) {i : B.Sorts}
    (D : NamedCoordinate B i) (q : Quotient D.val.val) :
    properForget B ht ⟨namedNode B D q,by trivial⟩ =
      QuotientPairQF.hiddenPoint (cloneSource B) D.val q := rfl

def kernelSort (ht : B.Terminal) (s : (Sig B ht).Sorts) :
    OwnerStage.FiniteHidden.HiddenSort B :=
  ⟨s.down.1,originalCompletedCoordinateKernel (cloneSource B) (HF B) s.down⟩

@[simp] theorem properForget_sort (ht : B.Terminal) (x : ProperValue B ht) :
    QuotientPairQF.hiddenSort (cloneSource B) (properForget B ht x) =
      kernelSort B ht ((Target B ht).sort x.val) := by
  rcases x with ⟨x,hx⟩
  cases x with
  | inl x => change False at hx; exact hx.elim
  | inr x =>
    rcases x with ⟨⟨i,J,q⟩,hNamed⟩
    rfl

def namedBinary (ht : B.Terminal) {i j : B.Sorts}
    (D : NamedCoordinate B i) (E : NamedCoordinate B j)
    (R : QuotientPairQF.Name (cloneSource B) D.val E.val) : (Sig B ht).Rel :=
  ⟨⟨i,.inr D⟩,⟨j,.inr E⟩,R⟩

theorem hiddenReading_iff {i : B.Sorts} (D : NamedCoordinate B i)
    (x : Values B) (q : Quotient D.val.val) :
    OriginalCompletedCoordinateReading (cloneSource B) (HF B) x ⟨i,.inr D⟩ q ↔
      x = namedNode B D q := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst x
    exact .hidden D q

/-- Full named cylinders agree with B060's actual off-diagonal named
relations. Literal equality is not inserted as a binary cylinder. -/
theorem namedBinary_semantics (ht : B.Terminal) {i j : B.Sorts}
    (D : NamedCoordinate B i) (E : NamedCoordinate B j)
    (R : QuotientPairQF.Name (cloneSource B) D.val E.val)
    (q : Quotient D.val.val) (r : Quotient E.val.val) :
    (CCO.TerminalHiddenHN.binaryStructure (Sig B ht)
      (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
        (cloneSAP B) (fullCovers B ht)) (Target B ht)).binary (namedBinary B ht D E R)
        (namedNode B D q) (namedNode B E r) ↔
      QuotientPairQF.NamedRelation (cloneSource B) R q r := by
  change (namedNode B D q ≠ namedNode B E r ∧
    ∃ q' r', OriginalCompletedCoordinateReading (cloneSource B) (HF B)
        (namedNode B D q) ⟨i,.inr D⟩ q' ∧
      OriginalCompletedCoordinateReading (cloneSource B) (HF B)
        (namedNode B E r) ⟨j,.inr E⟩ r' ∧
      originalTypedCylinderSemanticRelation (cloneSource B) D.val E.val R.val q' r') ↔ _
  have heq := namedNode_eq_iff B D E q r
  constructor
  · rintro ⟨hne,q',r',hq,hr,hR⟩
    have hq' : q = q' := namedNode_injective B D ((hiddenReading_iff B D _ q').mp hq)
    have hr' : r = r' := namedNode_injective B E ((hiddenReading_iff B E _ r').mp hr)
    exact ⟨fun h => hne (heq.mpr h),by simpa only [hq',hr'] using hR⟩
  · rintro ⟨hne,hR⟩
    exact ⟨fun h => hne (heq.mp h),q,r,.hidden D q,.hidden E r,hR⟩

/-- The existing finite equality/cylinder syntax on arbitrary displayed
vertices of the canonical full language. This retains both equality cases. -/
def pairEval (ht : B.Terminal) {i j : B.Sorts} (D : NamedCoordinate B i)
    (E : NamedCoordinate B j) {V : Type z}
    (M : CCO.FullCode.Structure (CoordinateLanguage B ht) V) (x y : V) :
    QuotientPairQF.Formula (cloneSource B) D.val E.val → Prop
  | .falsum => False
  | .truth => True
  | .equal => x = y
  | .named R => M.binary (namedBinary B ht D E R) x y
  | .neg p => ¬pairEval ht D E M x y p
  | .conj p q => pairEval ht D E M x y p ∧ pairEval ht D E M x y q
  | .disj p q => pairEval ht D E M x y p ∨ pairEval ht D E M x y q

theorem pairEval_target (ht : B.Terminal) {i j : B.Sorts} (D : NamedCoordinate B i)
    (E : NamedCoordinate B j) (q : Quotient D.val.val) (r : Quotient E.val.val)
    (test : QuotientPairQF.Formula (cloneSource B) D.val E.val) :
    pairEval B ht D E (CoordinateTarget B ht) (namedNode B D q) (namedNode B E r) test ↔
      test.eval q r := by
  induction test with
  | falsum => exact Iff.rfl
  | truth => exact Iff.rfl
  | equal => exact namedNode_eq_iff B D E q r
  | named R => exact namedBinary_semantics B ht D E R q r
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq
  | disj p q hp hq => exact or_congr hp hq

theorem pairEval_transport (ht : B.Terminal) {i j : B.Sorts} (D : NamedCoordinate B i)
    (E : NamedCoordinate B j) {V : Type z} {W : Type p}
    {M : CCO.FullCode.Structure (CoordinateLanguage B ht) V}
    {N : CCO.FullCode.Structure (CoordinateLanguage B ht) W}
    (f : CCO.FullCode.Structure.Embedding M N) (x y : V)
    (test : QuotientPairQF.Formula (cloneSource B) D.val E.val) :
    pairEval B ht D E N (f.point x) (f.point y) test ↔ pairEval B ht D E M x y test := by
  induction test with
  | falsum => exact Iff.rfl
  | truth => exact Iff.rfl
  | equal => exact f.injective.eq_iff
  | named R => exact f.binary_iff (namedBinary B ht D E R) x y
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq
  | disj p q hp hq => exact or_congr hp hq

end
end CCO.APRamseyReadout
