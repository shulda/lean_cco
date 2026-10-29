import CCO.SafeReadings.VisibleSeed

universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t} {Q : Family S}

theorem current_self (C : MenuCalculus S Q) : Current S Q Q where
  member := Set.Subset.rfl
  singleton := C.singleton
  opposite := C.opposite
  downward _ hE _ := hE

theorem atomicFamily_subset {J : Family S} (hJ : Current S Q J) : atomicFamily S ⊆ J := by
  rintro ⟨i,j,D⟩ ⟨a,hD⟩
  change S.Atom i j at a
  change D = {a} at hD
  rw [hD]
  exact hJ.singleton a

theorem atomicFamily_card_le {J : Family S} (hJ : Current S Q J) :
    Nat.card (atomicFamily S) ≤ Nat.card J :=
  Set.ncard_le_ncard (atomicFamily_subset S hJ)

/-- Every recorded strict step is an actual visible original gate, and
records its current/action-invariant domain and image. -/
structure IsVisibleGate (A : PureTagAction S Λ N) {J K : Family S}
    (R : Contraction S J K) : Prop where
  current_domain : Current S Q J
  current_image : Current S Q K
  invariant_domain : A.Invariant J
  invariant_image : A.Invariant K
  covariance : A.Covariant R
  actual_gate : ∃ F : Family S, Filter S Q F ∧ A.Invariant F ∧ Visible S F J ∧
    K = gateImage S F J ∧ ∀ {i j} (D : S.Menu i j), R.toFun D = gate S F D

private theorem visible_chain_covariant (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat} (chain : DescentChain S (IsVisibleGate S (Q := Q) A) J K n) :
    A.Covariant (DescentChain.composite chain) := by
  induction chain with
  | nil J => exact A.covariant_id J
  | cons R hstrict tail ih => exact A.covariant_comp R.property.covariance ih

/-- C26: genuine finite pure-tag gate iteration with the exact menu-count
bound and covariance of the actual composite, not an assumed selector. -/
theorem pure_gate_iteration (C : MenuCalculus S Q)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A : PureTagAction S Λ N) (hQI : A.Invariant Q) (hNoReturn : NoReturn S Q A)
    (J : Family S) (hJ : Current S Q J) (hInv : A.Invariant J) :
    ∃ K, Current S Q K ∧ A.Invariant K ∧ Terminal S K ∧
      ∃ n, n ≤ Nat.card J - Nat.card (atomicFamily S) ∧
        ∃ chain : DescentChain S (IsVisibleGate S (Q := Q) A) J K n,
          A.Covariant (DescentChain.composite chain) := by
  let Admissible := fun J : Family S => Current S Q J ∧ A.Invariant J
  have step : ∀ J, Admissible J → ¬Terminal S J →
      ∃ K, Admissible K ∧ ∃ R : Contraction S J K,
        IsVisibleGate S (Q := Q) A R ∧ Nat.card K < Nat.card J := by
    intro J hJ hNot
    obtain ⟨F,hF,hFI,hV,i,j,D,P,hD,hP,hMeet,hProper⟩ :=
      visible_step_exists S C A hQI hJ.1 hNoReturn hNot
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
      (fun J hJ => atomicFamily_card_le S hJ.1) (IsVisibleGate S (Q := Q) A) step J ⟨hJ,hInv⟩
  exact ⟨K,hK,hKI,hTerm,n,hBound,chain,visible_chain_covariant S A chain⟩


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
    (R : Contraction S Q K) : SelectorOn S Q := by
  classical
  let choose {i j} (D : S.Menu i j) (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ Q) : S.Atom i j :=
    Classical.choose (hTerm ⟨i,j,R.toFun D⟩ (R.maps hD))
  have hSingle {i j} (D : S.Menu i j) (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ Q) :
      R.toFun D = {choose D hD} :=
    Classical.choose_spec (hTerm ⟨i,j,R.toFun D⟩ (R.maps hD))
  have hMem {i j} (D : S.Menu i j) (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ Q) : choose D hD ∈ R.toFun D := by
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


theorem selectorOfTerminal_singleton {K : Family S} (hTerm : Terminal S K)
    (R : Contraction S Q K) {i j} (D : S.Menu i j)
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ Q) :
    R.toFun D = {(selectorOfTerminal S hTerm R).choose D hD} :=
  Classical.choose_spec (hTerm ⟨i,j,R.toFun D⟩ (R.maps hD))

private theorem names_singleton (A : PureTagAction S Λ N) {i j} (a : S.Atom i j) :
    names S A.label ⟨i,j,({a} : S.Menu i j)⟩ = {A.label a} := by
  ext n
  simp [names]

theorem selectorOfTerminal_covariant (A : PureTagAction S Λ N)
    {K : Family S} (hTerm : Terminal S K)
    (R : Contraction S Q K) (hCov : A.Covariant R) (hQI : A.Invariant Q) :
    (selectorOfTerminal S hTerm R).Covariant A hQI := by
  intro g D hD
  have h := congrArg (names S A.label) (hCov g D hD)
  rw [A.literal] at h
  change names S A.label ⟨D.1,D.2.1,R.toFun D.2.2⟩ =
    names S A.label ⟨(A.act g D).1,(A.act g D).2.1,R.toFun (A.act g D).2.2⟩ at h
  rw [selectorOfTerminal_singleton S hTerm R D.2.2 hD,
    selectorOfTerminal_singleton S hTerm R (A.act g D).2.2 (hQI g D hD),
    names_singleton S A,names_singleton S A] at h
  exact (Set.singleton_injective h).symm

/-- The generic gate engine actually constructs the singleton reading. -/
theorem exists_covariant_selector (C : MenuCalculus S Q)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A : PureTagAction S Λ N) (hQI : A.Invariant Q) (hNoReturn : NoReturn S Q A) :
    ∃ h : SelectorOn S Q, h.Covariant A hQI := by
  obtain ⟨K,_,_,hTerm,_,_,chain,hCov⟩ :=
    pure_gate_iteration S C hPoint hEdge A hQI hNoReturn Q (current_self S C) hQI
  exact ⟨selectorOfTerminal S hTerm (DescentChain.composite chain),
    selectorOfTerminal_covariant S A hTerm (DescentChain.composite chain) hCov hQI⟩

end CCO.SafeReadings
