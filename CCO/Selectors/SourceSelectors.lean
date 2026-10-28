import CCO.Selectors.Engine
import CCO.Selectors.PureCovariance
import CCO.Selectors.TrivialEngine
import CCO.Selectors.OriginalFamily
import CCO.Selectors.Iteration
import CCO.Selectors.NoReturn
import CCO.Selectors.SourceCalculus

universe u v w z t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t}

/-- Every recorded strict step is an actual visible original gate, and
records its current/action-invariant domain and image. -/
structure IsVisibleGate (A : PureTagAction S Λ N) {J K : Family S}
    (R : Contraction S J K) : Prop where
  current_domain : CurrentFamily S J
  current_image : CurrentFamily S K
  invariant_domain : A.Invariant J
  invariant_image : A.Invariant K
  covariance : A.Covariant R
  actual_gate : ∃ F : Family S, FilterFamily S F ∧ A.Invariant F ∧ Visible S F J ∧
    K = gateImage S F J ∧ ∀ {i j} (D : S.Menu i j), R.toFun D = gate S F D

private theorem visible_chain_covariant (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat} (chain : DescentChain S (IsVisibleGate S A) J K n) :
    A.Covariant (DescentChain.composite chain) := by
  induction chain with
  | nil J => exact A.covariant_id J
  | cons R hstrict tail ih => exact A.covariant_comp R.property.covariance ih

/-- C26: genuine finite pure-tag gate iteration with the exact menu-count
bound and covariance of the actual composite, not an assumed selector. -/
theorem pure_gate_iteration (C : ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A : PureTagAction S Λ N) (hNoReturn : PureNoReturn S A)
    (J : Family S) (hJ : CurrentFamily S J) (hInv : A.Invariant J) :
    ∃ K, CurrentFamily S K ∧ A.Invariant K ∧ Terminal S K ∧
      ∃ n, n ≤ Nat.card J - Nat.card (atomicFamily S) ∧
        ∃ chain : DescentChain S (IsVisibleGate S A) J K n,
          A.Covariant (DescentChain.composite chain) := by
  let Admissible := fun J : Family S => CurrentFamily S J ∧ A.Invariant J
  have step : ∀ J, Admissible J → ¬Terminal S J →
      ∃ K, Admissible K ∧ ∃ R : Contraction S J K,
        IsVisibleGate S A R ∧ Nat.card K < Nat.card J := by
    intro J hJ hNot
    obtain ⟨F,hF,hFI,hV,i,j,D,P,hD,hP,hMeet,hProper⟩ :=
      visible_step_exists S C A hJ.1 hNoReturn hNot
    let R := gateContraction S C hPoint hEdge hF hJ.1 hV
    refine ⟨gateImage S F J,⟨gateImage_current S C hF hJ.1 hV,
      A.invariant_gateImage F J hFI hJ.2⟩,R,?_,
      gateImage_card_lt S C hF hJ.1 hV hD hP hMeet hProper⟩
    refine ⟨hJ.1,gateImage_current S C hF hJ.1 hV,hJ.2,
      A.invariant_gateImage F J hFI hJ.2,?_,⟨F,hF,hFI,hV,rfl,?_⟩⟩
    · intro g D hD
      exact A.act_gateTag F hFI g D
    · intro i j D
      rfl
  obtain ⟨K,⟨hK,hKI⟩,hTerm,n,hBound,⟨chain⟩⟩ :=
    finiteGateDescent S (Nat.card (atomicFamily S)) Admissible (Terminal S)
      (fun J hJ => atomicFamily_card_le S hJ.1) (IsVisibleGate S A) step J ⟨hJ,hInv⟩
  exact ⟨K,hK,hKI,hTerm,n,hBound,chain,visible_chain_covariant S A chain⟩


/-- Source C26 includes the literal displayed sum-of-menu-count bound. -/
theorem pure_gate_iteration_of_SAP_CCO
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)] [Fintype Λ]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (A : PureTagAction S Λ N)
    (hNoReturn : PureNoReturn S A) :
    ∃ K, CurrentFamily S K ∧ A.Invariant K ∧ Terminal S K ∧
      ∃ n, n ≤ originalMenuCount S -
        S.finiteSort.elems.sum (fun i => S.finiteSort.elems.sum fun j => Nat.card (S.Atom i j)) ∧
        ∃ chain : DescentChain S (IsVisibleGate S A) (originalFamily S) K n,
          A.Covariant (DescentChain.composite chain) := by
  let C := exactCalculus_of_SAP_CCO S H sap cco
  have hInv : A.Invariant (originalFamily S) := fun g D hD => (A.exact g D).mpr hD
  simpa only [originalFamily_card S,atomicFamily_card S] using
    pure_gate_iteration S C (S.realPointGluing_of_SAP H sap) (S.realEdgeGluing_of_SAP H sap)
      A hNoReturn (originalFamily S) (originalFamily_current S C) hInv


/-- C14–C18 source consumer: actual nonempty original-exact, conservative,
converse-compatible, all-PC-preserving and survivor-hereditary contraction. -/
def visible_gate_contraction_of_SAP_CCO
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (cco : SemanticCCO.{u,v,0,w} S)
    {F J : Family S} (hF : FilterFamily S F) (hJ : CurrentFamily S J)
    (hV : Visible S F J) : Contraction S J (gateImage S F J) :=
  gateContraction S (exactCalculus_of_SAP_CCO S H sap cco)
    (S.realPointGluing_of_SAP H sap) (S.realEdgeGluing_of_SAP H sap) hF hJ hV

/-- One named-sort selector, with no fine-colour permutation covariance claim. -/
structure HereditarySelector where
  choose : ∀ {i j} (D : S.Menu i j), StrongExact.Exact S D → S.Atom i j
  member : ∀ {i j} (D : S.Menu i j) (hD), choose D hD ∈ D
  opposite : ∀ {i j} (D : S.Menu i j) (hD) (hOpp),
    choose (S.opposite D) hOpp = S.conv (choose D hD)
  heredity : ∀ {i j} (E D : S.Menu i j) (hE) (hD),
    E ⊆ D → choose D hD ∈ E → choose E hE = choose D hD
  pc : ∀ {i j k} (A : S.Menu i j) (B : S.Menu j k) (D : S.Menu i k) (hA) (hB) (hD),
    S.PC A B D → S.PC {choose A hA} {choose B hB} {choose D hD}

private theorem opp_singleton {i j} (a : S.Atom i j) :
    S.opposite ({a} : S.Menu i j) = {S.conv a} := by
  ext b
  change S.conv b = a ↔ b = S.conv a
  constructor
  · intro h
    have h' := congrArg S.conv h
    simpa only [S.conv_invol] using h'
  · rintro rfl
    exact S.conv_invol a

/-- Read a genuine singleton target of an actual whole-family contraction. -/
noncomputable def selectorOfTerminal {K : Family S} (hTerm : Terminal S K)
    (R : Contraction S (originalFamily S) K) : HereditarySelector S := by
  classical
  let choose {i j} (D : S.Menu i j) (hD : StrongExact.Exact S D) : S.Atom i j :=
    Classical.choose (hTerm ⟨i,j,R.toFun D⟩ (R.maps hD))
  have hSingle {i j} (D : S.Menu i j) (hD : StrongExact.Exact S D) :
      R.toFun D = {choose D hD} :=
    Classical.choose_spec (hTerm ⟨i,j,R.toFun D⟩ (R.maps hD))
  have hMem {i j} (D : S.Menu i j) (hD : StrongExact.Exact S D) : choose D hD ∈ R.toFun D := by
    rw [hSingle D hD]
    exact Set.mem_singleton _
  refine {choose := choose, member := ?_, opposite := ?_, heredity := ?_, pc := ?_}
  · intro i j D hD
    exact R.conservative hD (hMem D hD)
  · intro i j D hD hOpp
    apply Set.singleton_injective
    rw [← hSingle (S.opposite D) hOpp, R.opposite hD, hSingle D hD, opp_singleton S]
  · intro i j E D hE hD hED hChoose
    have hHer := R.heredity hE hD hED ⟨choose D hD,hChoose,hMem D hD⟩
    have hEq : E ∩ R.toFun D = ({choose D hD} : S.Menu i j) := by
      rw [hSingle D hD]
      ext a
      simp only [Set.mem_inter_iff,Set.mem_singleton_iff]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨hChoose,rfl⟩
    apply Set.singleton_injective
    rw [← hSingle E hE,hHer,hEq]
  · intro i j k A B D hA hB hD hPC
    have h := R.pc hA hB hD hPC
    rwa [hSingle A hA,hSingle B hB,hSingle D hD] at h


namespace HereditarySelector
/-- Only preservation of the displayed literal names is asserted. -/
def Covariant (h : HereditarySelector S) (A : PureTagAction S Λ N) : Prop :=
  ∀ g (D : TaggedMenu S) (hD : IsExact S D),
    A.label (h.choose (A.act g D).2.2 ((A.exact g D).mpr hD)) = A.label (h.choose D.2.2 hD)
end HereditarySelector

theorem selectorOfTerminal_singleton {K : Family S} (hTerm : Terminal S K)
    (R : Contraction S (originalFamily S) K) {i j} (D : S.Menu i j)
    (hD : StrongExact.Exact S D) :
    R.toFun D = {(selectorOfTerminal S hTerm R).choose D hD} :=
  Classical.choose_spec (hTerm ⟨i,j,R.toFun D⟩ (R.maps hD))

private theorem names_singleton (A : PureTagAction S Λ N) {i j} (a : S.Atom i j) :
    names S A.label ⟨i,j,({a} : S.Menu i j)⟩ = {A.label a} := by
  ext n
  simp [names]

theorem selectorOfTerminal_covariant (A : PureTagAction S Λ N)
    {K : Family S} (hTerm : Terminal S K)
    (R : Contraction S (originalFamily S) K) (hCov : A.Covariant R) :
    (selectorOfTerminal S hTerm R).Covariant S A := by
  intro g D hD
  have h := congrArg (names S A.label) (hCov g D hD)
  rw [A.literal] at h
  change names S A.label ⟨D.1,D.2.1,R.toFun D.2.2⟩ =
    names S A.label ⟨(A.act g D).1,(A.act g D).2.1,R.toFun (A.act g D).2.2⟩ at h
  rw [selectorOfTerminal_singleton S hTerm R D.2.2 hD,
    selectorOfTerminal_singleton S hTerm R (A.act g D).2.2 ((A.exact g D).mpr hD),
    names_singleton S A,names_singleton S A] at h
  exact (Set.singleton_injective h).symm

/-- C26 source form: the ONLY conditional no-return premise is the one
explicitly displayed for the given pure tag action in the pinned source. -/
theorem exists_covariant_selector_of_pure_noReturn
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (A : PureTagAction S Λ N)
    (hNoReturn : PureNoReturn S A) :
    ∃ h : HereditarySelector S, h.Covariant S A := by
  let C := exactCalculus_of_SAP_CCO S H sap cco
  have hInv : A.Invariant (originalFamily S) := by
    intro g D hD
    exact (A.exact g D).mpr hD
  obtain ⟨K,hK,hKI,hTerm,n,hBound,chain,hCov⟩ :=
    pure_gate_iteration S C (S.realPointGluing_of_SAP H sap) (S.realEdgeGluing_of_SAP H sap)
      A hNoReturn (originalFamily S) (originalFamily_current S C) hInv
  exact ⟨selectorOfTerminal S hTerm (DescentChain.composite chain),
    selectorOfTerminal_covariant S A hTerm (DescentChain.composite chain) hCov⟩

/-- C27 source export: the conditional pure-action engine is discharged by
actual FULL original sortwise NR2 and the trivial pure tag action. -/
theorem exists_hereditary_selector_of_SAP_CCO_NR2
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (nr2 : OriginalNR2 S) :
    Nonempty (HereditarySelector S) := by
  let C := exactCalculus_of_SAP_CCO S H sap cco
  let A := PureTagAction.trivial (S := S)
  have hNR : FullNoReturn S := by
    intro i j B D hB hD hGen
    exact fullNoReturn_of_nr2 S C H sap (fullNR2_of_original S H nr2)
      (i := i) (j := j) B D hB hD hGen
  have hInv : A.Invariant (originalFamily S) := by intro g D hD; exact hD
  obtain ⟨K,hK,hKI,hTerm,n,hBound,chain,hCov⟩ :=
    pure_gate_iteration S C (S.realPointGluing_of_SAP H sap) (S.realEdgeGluing_of_SAP H sap)
      A (pureNoReturn_trivial S C hNR) (originalFamily S) (originalFamily_current S C) hInv
  exact ⟨selectorOfTerminal S hTerm (DescentChain.composite chain)⟩

namespace HereditarySelector
/-- A downstream geometric consumer: every chosen PC triple is an ACTUAL
three-distinct-real-point triangle, including repeated named sorts. -/
theorem triangle (h : HereditarySelector S)
    {i j k} (A : S.Menu i j) (B : S.Menu j k) (D : S.Menu i k)
    (hA : StrongExact.Exact S A) (hB : StrongExact.Exact S B) (hD : StrongExact.Exact S D)
    (hPC : S.PC A B D) : S.Triangle (h.choose A hA) (h.choose B hB) (h.choose D hD) := by
  obtain ⟨a,ha,b,hb,htri⟩ := (h.pc A B D hA hB hD hPC).1 (Set.mem_singleton _)
  have ha' := Set.mem_singleton_iff.mp ha
  have hb' := Set.mem_singleton_iff.mp hb
  subst a; subst b
  exact htri

theorem singleton (h : HereditarySelector S) {i j} (a : S.Atom i j) :
    h.choose {a} (StrongExact.exact_singleton S a) = a :=
  Set.mem_singleton_iff.mp (h.member {a} (StrongExact.exact_singleton S a))
end HereditarySelector

/-- Downstream original-source consumer: ONE coherent selector realizes
EVERY original exact PC triple by a genuine real triangle. -/
theorem source_joint_triangle_selection
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (nr2 : OriginalNR2 S) :
    ∃ h : HereditarySelector S, ∀ (i j k : ι)
      (A : S.Menu i j) (B : S.Menu j k) (D : S.Menu i k)
      (hA : StrongExact.Exact S A) (hB : StrongExact.Exact S B) (hD : StrongExact.Exact S D),
      S.PC A B D → S.Triangle (h.choose A hA) (h.choose B hB) (h.choose D hD) := by
  obtain ⟨h⟩ := exists_hereditary_selector_of_SAP_CCO_NR2 S H sap cco nr2
  exact ⟨h,fun i j k A B D hA hB hD hPC => h.triangle S A B D hA hB hD hPC⟩

end CCO.Selectors
