import CCO.SafeReadings.AugmentedMenus
import CCO.SafeReadings.OrbitBound

universe u v w z t
namespace CCO.SafeReadings
open StrongExact Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (safe : ∀ i j, S.Menu i j)

/-- The actual safe retraction is defined on every evaluated menu. -/
noncomputable def safeRetract {i j} (D : S.Menu i j) : S.Menu i j := by
  classical
  exact if (D ∩ safe i j).Nonempty then D ∩ safe i j else D

@[simp] theorem safeRetract_of_meets {i j} {D : S.Menu i j}
    (h : (D ∩ safe i j).Nonempty) : safeRetract S safe D = D ∩ safe i j := by
  classical
  simp [safeRetract,h]

@[simp] theorem safeRetract_of_disjoint {i j} {D : S.Menu i j}
    (h : ¬(D ∩ safe i j).Nonempty) : safeRetract S safe D = D := by
  classical
  simp [safeRetract,h]

theorem safeRetract_subset {i j} (D : S.Menu i j) : safeRetract S safe D ⊆ D := by
  classical
  by_cases h : (D ∩ safe i j).Nonempty <;> simp only [safeRetract,h,if_pos,if_neg]
  · exact Set.inter_subset_left
  · exact Set.Subset.rfl

theorem safeRetract_nonempty {i j} {D : S.Menu i j} (hD : D.Nonempty) :
    (safeRetract S safe D).Nonempty := by
  classical
  by_cases h : (D ∩ safe i j).Nonempty <;> simp [safeRetract,h,hD]

theorem safeRetract_of_subset {i j} {D : S.Menu i j} (hD : D ⊆ safe i j) :
    safeRetract S safe D = D := by
  classical
  by_cases h : (D ∩ safe i j).Nonempty <;> simp [safeRetract,h,Set.inter_eq_left.mpr hD]

@[simp] theorem safeRetract_idempotent {i j} (D : S.Menu i j) :
    safeRetract S safe (safeRetract S safe D) = safeRetract S safe D := by
  classical
  by_cases h : (D ∩ safe i j).Nonempty
  · rw [safeRetract_of_meets S safe h]
    exact safeRetract_of_subset S safe Set.inter_subset_right
  · rw [safeRetract_of_disjoint S safe h]
    exact safeRetract_of_disjoint S safe h

/-- Survivor heredity is a set-theoretic property of this actual retraction. -/
theorem safeRetract_heredity {i j} {E D : S.Menu i j} (hED : E ⊆ D)
    (hsurvive : (E ∩ safeRetract S safe D).Nonempty) :
    safeRetract S safe E = E ∩ safeRetract S safe D := by
  classical
  by_cases hD : (D ∩ safe i j).Nonempty
  · have hE : (E ∩ safe i j).Nonempty := by
      obtain ⟨a,ha,hb⟩ := hsurvive
      rw [safeRetract_of_meets S safe hD] at hb
      exact ⟨a,ha,hb.2⟩
    rw [safeRetract_of_meets S safe hD,safeRetract_of_meets S safe hE]
    ext a
    exact ⟨fun h => ⟨h.1,hED h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩
  · have hE : ¬(E ∩ safe i j).Nonempty := by
      rintro ⟨a,ha,hb⟩
      exact hD ⟨a,hED ha,hb⟩
    rw [safeRetract_of_disjoint S safe hD,safeRetract_of_disjoint S safe hE]
    exact (Set.inter_eq_left.mpr hED).symm

theorem safeRetract_singleton {i j} (a : S.Atom i j) :
    safeRetract S safe ({a} : S.Menu i j) = {a} := by
  apply Set.Subset.antisymm (safeRetract_subset S safe _)
  obtain ⟨b,hb⟩ := safeRetract_nonempty S safe (Set.singleton_nonempty a)
  have hba : b = a := Set.mem_singleton_iff.mp (safeRetract_subset S safe _ hb)
  subst b
  exact Set.singleton_subset_iff.mpr hb

theorem safeRetract_opposite (hs : ∀ i j, S.opposite (safe i j) = safe j i)
    {i j} (D : S.Menu i j) : safeRetract S safe (S.opposite D) = S.opposite (safeRetract S safe D) := by
  classical
  have hi : S.opposite (D ∩ safe i j) = S.opposite D ∩ safe j i := by
    rw [opposite_inter,hs]
  have hn : (S.opposite D ∩ safe j i).Nonempty ↔ (D ∩ safe i j).Nonempty := by
    rw [← hi]
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨S.conv a,ha⟩
    · rintro ⟨a,ha⟩
      exact ⟨S.conv a,S.mem_opposite ha⟩
  by_cases hD : (D ∩ safe i j).Nonempty
  · rw [safeRetract_of_meets S safe hD,safeRetract_of_meets S safe (hn.mpr hD),hi]
  · rw [safeRetract_of_disjoint S safe hD,safeRetract_of_disjoint S safe (fun h => hD (hn.mp h))]

def safeRetractTag (D : TaggedMenu S) : TaggedMenu S := ⟨D.1,D.2.1,safeRetract S safe D.2.2⟩

variable {Λ : Type z} [Group Λ] {N : Type t}

/-- A displayed hypothesis on the GIVEN safe palette; no safe system is chosen here. -/
def SafeInvariant (A : PureTagAction S Λ N) : Prop :=
  ∀ g i j, A.act g (⟨i,j,safe i j⟩ : TaggedMenu S) =
    ⟨A.tag g i,A.tag g j,safe (A.tag g i) (A.tag g j)⟩

private theorem names_nonempty (A : PureTagAction S Λ N) (D : TaggedMenu S) :
    (names S A.label D).Nonempty ↔ D.2.2.Nonempty := by
  constructor
  · rintro ⟨n,a,ha,_⟩
    exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨A.label a,a,ha,rfl⟩

private theorem names_trace_act (A : PureTagAction S Λ N) (hSafe : SafeInvariant S safe A)
    (g : Λ) (D : TaggedMenu S) :
    names S A.label ⟨(A.act g D).1,(A.act g D).2.1,
      (A.act g D).2.2 ∩ safe (A.act g D).1 (A.act g D).2.1⟩ =
    names S A.label ⟨D.1,D.2.1,D.2.2 ∩ safe D.1 D.2.1⟩ := by
  rw [A.names_inter,A.names_inter,A.literal]
  congr 1
  have hp : ((A.act g D).1,(A.act g D).2.1) = (A.tag g D.1,A.tag g D.2.1) :=
    Prod.ext (A.source g D) (A.target g D)
  have ht := congrArg (fun p : ι × ι => names S A.label ⟨p.1,p.2,safe p.1 p.2⟩) hp
  exact ht.trans ((congrArg (names S A.label) (hSafe g D.1 D.2.1)).symm.trans
    (A.literal g ⟨D.1,D.2.1,safe D.1 D.2.1⟩))

theorem act_safeRetractTag (A : PureTagAction S Λ N) (hSafe : SafeInvariant S safe A)
    (g : Λ) (D : TaggedMenu S) :
    A.act g (safeRetractTag S safe D) = safeRetractTag S safe (A.act g D) := by
  have htrace := names_trace_act S safe A hSafe g D
  have hn : ((A.act g D).2.2 ∩ safe (A.act g D).1 (A.act g D).2.1).Nonempty ↔
      (D.2.2 ∩ safe D.1 D.2.1).Nonempty := by
    calc
      _ ↔ (names S A.label ⟨(A.act g D).1,(A.act g D).2.1,
          (A.act g D).2.2 ∩ safe (A.act g D).1 (A.act g D).2.1⟩).Nonempty :=
        (names_nonempty S A _).symm
      _ ↔ (names S A.label ⟨D.1,D.2.1,D.2.2 ∩ safe D.1 D.2.1⟩).Nonempty := by rw [htrace]
      _ ↔ _ := names_nonempty S A _
  apply A.tagged_names_injective
  · exact ⟨(A.source g _).trans (A.source g D).symm,
      (A.target g _).trans (A.target g D).symm⟩
  · rw [A.literal]
    change names S A.label ⟨D.1,D.2.1,safeRetract S safe D.2.2⟩ =
      names S A.label ⟨(A.act g D).1,(A.act g D).2.1,safeRetract S safe (A.act g D).2.2⟩
    by_cases hD : (D.2.2 ∩ safe D.1 D.2.1).Nonempty
    · rw [safeRetract_of_meets S safe hD,safeRetract_of_meets S safe (hn.mpr hD)]
      exact htrace.symm
    · rw [safeRetract_of_disjoint S safe hD,
        safeRetract_of_disjoint S safe (fun h => hD (hn.mp h)),A.literal]


/-- Covariance of the evaluated safe trace follows from literal names. -/
theorem act_traceTag (A : PureTagAction S Λ N) (hSafe : SafeInvariant S safe A)
    (g : Λ) (D : TaggedMenu S) :
    A.act g ⟨D.1,D.2.1,D.2.2 ∩ safe D.1 D.2.1⟩ =
      ⟨(A.act g D).1,(A.act g D).2.1,(A.act g D).2.2 ∩ safe (A.act g D).1 (A.act g D).2.1⟩ := by
  apply A.tagged_names_injective
  · exact ⟨(A.source g _).trans (A.source g D).symm,
      (A.target g _).trans (A.target g D).symm⟩
  · rw [A.literal]
    exact (names_trace_act S safe A hSafe g D).symm

theorem augmentedFamily_invariant (A : PureTagAction S Λ N) (hSafe : SafeInvariant S safe A) :
    A.Invariant (augmentedFamily S safe) := by
  rintro g ⟨i,j,D⟩ hD
  change Augmented S safe D at hD
  rcases hD with hD | ⟨E,hE,rfl,hne⟩
  · exact Or.inl ((A.exact g _).mpr hD)
  · change A.act g ⟨i,j,E ∩ safe i j⟩ ∈ augmentedFamily S safe
    rw [act_traceTag S safe A hSafe g ⟨i,j,E⟩]
    refine Or.inr ⟨(A.act g ⟨i,j,E⟩).2.2,(A.exact g _).mpr hE,rfl,?_⟩
    have ht := names_trace_act S safe A hSafe g ⟨i,j,E⟩
    apply (names_nonempty S A _).mp
    rw [ht]
    exact (names_nonempty S A _).mpr hne

theorem safeRetract_member {i j} {D : S.Menu i j} (hD : Augmented S safe D) :
    Augmented S safe (safeRetract S safe D) := by
  classical
  rcases hD with hD | ⟨E,hE,rfl,hne⟩
  · by_cases h : (D ∩ safe i j).Nonempty
    · rw [safeRetract_of_meets S safe h]
      exact Or.inr ⟨D,hD,rfl,h⟩
    · rw [safeRetract_of_disjoint S safe h]
      exact Or.inl hD
  · rw [safeRetract_of_subset S safe Set.inter_subset_right]
    exact Or.inr ⟨E,hE,rfl,hne⟩

variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]

/-- Traces already lie in the safe palette; every changed augmented menu
is original exact, so the actual arbitrary-multiplier theorem applies. -/
theorem safeRetract_left_product (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) {i j k} {D : S.Menu i j} (hD : Augmented S safe D) (E : S.Menu j k) :
    S.product (safeRetract S safe D) E = S.product D E := by
  classical
  rcases hD with hD | ⟨P,hP,rfl,_⟩
  · by_cases h : (D ∩ safe i j).Nonempty
    · rw [safeRetract_of_meets S safe h]
      exact safe_trace_product S H sap hs.amalgamation hD h E
    · rw [safeRetract_of_disjoint S safe h]
  · rw [safeRetract_of_subset S safe Set.inter_subset_right]

theorem safeRetract_right_product (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) {i j k} (D : S.Menu i j) {E : S.Menu j k} (hE : Augmented S safe E) :
    S.product D (safeRetract S safe E) = S.product D E := by
  classical
  rcases hE with hE | ⟨P,hP,rfl,_⟩
  · by_cases h : (E ∩ safe j k).Nonempty
    · rw [safeRetract_of_meets S safe h]
      exact product_safe_trace S H sap hs D hE h
    · rw [safeRetract_of_disjoint S safe h]
  · rw [safeRetract_of_subset S safe Set.inter_subset_right]

theorem safeRetract_product (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) {i j k} {D : S.Menu i j} {E : S.Menu j k}
    (hD : Augmented S safe D) (hE : Augmented S safe E) :
    S.product (safeRetract S safe D) (safeRetract S safe E) = S.product D E := by
  rw [safeRetract_left_product S safe H sap hs hD,safeRetract_right_product S safe H sap hs D hE]

theorem safeRetract_pc (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) {i j k} {D : S.Menu i j} {E : S.Menu j k} {P : S.Menu i k}
    (hD : Augmented S safe D) (hE : Augmented S safe E) (hP : Augmented S safe P)
    (hPC : S.PC D E P) : S.PC (safeRetract S safe D) (safeRetract S safe E) (safeRetract S safe P) := by
  refine ⟨?_,?_,?_⟩
  · rw [safeRetract_product S safe H sap hs hD hE]
    exact (safeRetract_subset S safe P).trans hPC.1
  · rw [← safeRetract_opposite S safe hs.opposite,
      safeRetract_product S safe H sap hs hP (augmented_opposite S H sap hs hE)]
    exact (safeRetract_subset S safe D).trans hPC.2.1
  · rw [← safeRetract_opposite S safe hs.opposite,
      safeRetract_product S safe H sap hs (augmented_opposite S H sap hs hD) hP]
    exact (safeRetract_subset S safe E).trans hPC.2.2

def safeImage : Family S := safeRetractTag S safe '' augmentedFamily S safe

theorem safeImage_subset : safeImage S safe ⊆ augmentedFamily S safe := by
  rintro _ ⟨⟨i,j,D⟩,hD,rfl⟩
  exact safeRetract_member S safe hD

theorem safeImage_eq_fixed : safeImage S safe =
    {D | D ∈ augmentedFamily S safe ∧ safeRetract S safe D.2.2 = D.2.2} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨i,j,D⟩,hD,rfl⟩
    exact ⟨safeRetract_member S safe hD,safeRetract_idempotent S safe D⟩
  · rintro ⟨i,j,D⟩ ⟨hD,he⟩
    exact ⟨⟨i,j,D⟩,hD,by simp [safeRetractTag,he]⟩

theorem safeImage_current (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) : Current S (augmentedFamily S safe) (safeImage S safe) := by
  rw [safeImage_eq_fixed]
  refine ⟨fun _ h => h.1,?_,?_,?_⟩
  · intro i j a
    exact ⟨Or.inl (exact_singleton S a),safeRetract_singleton S safe a⟩
  · rintro ⟨i,j,D⟩ ⟨hD,he⟩
    refine ⟨augmented_opposite S H sap hs hD,?_⟩
    change safeRetract S safe (S.opposite D) = S.opposite D
    rw [safeRetract_opposite S safe hs.opposite,he]
  · intro i j D E hD hE hED
    refine ⟨hE,?_⟩
    have hsurvive : (E ∩ safeRetract S safe D).Nonempty := by
      obtain ⟨a,ha⟩ := Augmented.nonempty S hE
      exact ⟨a,ha,by rw [hD.2]; exact hED ha⟩
    rw [safeRetract_heredity S safe hED hsurvive,hD.2]
    exact Set.inter_eq_left.mpr hED

def safeContraction (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) : Contraction S (augmentedFamily S safe) (safeImage S safe) where
  toFun D := safeRetract S safe D
  maps := by intro i j D hD; exact ⟨⟨i,j,D⟩,hD,rfl⟩
  conservative _ := safeRetract_subset S safe _
  opposite _ := safeRetract_opposite S safe hs.opposite _
  heredity _ _ hED hm := safeRetract_heredity S safe hED hm
  pc hD hE hP hPC := safeRetract_pc S safe H sap hs hD hE hP hPC

theorem safeContraction_covariant (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) (A : PureTagAction S Λ N) (hSafe : SafeInvariant S safe A) :
    A.Covariant (safeContraction S safe H sap hs) := by
  intro g D hD
  exact act_safeRetractTag S safe A hSafe g D

theorem safeImage_invariant (A : PureTagAction S Λ N) (hSafe : SafeInvariant S safe A) :
    A.Invariant (safeImage S safe) := by
  rintro g _ ⟨D,hD,rfl⟩
  exact ⟨A.act g D,augmentedFamily_invariant S safe A hSafe g D hD,
    (act_safeRetractTag S safe A hSafe g D).symm⟩


/-- Each distinct trace is an image of an original menu; duplicate
skeletons contribute no additional evaluated menu. -/
theorem augmented_hom_card_le_twice (i j : ι) :
    Nat.card (homFamily S (augmentedFamily S safe) i j) ≤
      2 * Nat.card (homFamily S (originalFamily S) i j) := by
  letI := S.finiteAtom i j
  let O : Set (S.Menu i j) := {D | Exact S D}
  let f : S.Menu i j → S.Menu i j := fun D => D ∩ safe i j
  have hsub : homFamily S (augmentedFamily S safe) i j ⊆ O ∪ f '' O := by
    intro D hD
    change Augmented S safe D at hD
    rcases hD with hD | ⟨E,hE,rfl,_⟩
    · exact Or.inl hD
    · exact Or.inr ⟨E,hE,rfl⟩
  have h := (Set.ncard_le_ncard hsub).trans
    ((Set.ncard_union_le O (f '' O)).trans
      (Nat.add_le_add_left (Set.ncard_image_le (f := f) (s := O)) O.ncard))
  change (homFamily S (augmentedFamily S safe) i j).ncard ≤ 2 * O.ncard
  simpa only [two_mul] using h

theorem augmented_current_self (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) : Current S (augmentedFamily S safe) (augmentedFamily S safe) where
  member := Set.Subset.rfl
  singleton a := Or.inl (exact_singleton S a)
  opposite h := augmented_opposite S H sap hs h
  downward _ hE _ := hE

/-- The literal displayed source bound counts each evaluated safe trace once. -/
theorem augmented_orbitCount_le_original_sum (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) (A : PureTagAction S Λ N) :
    orbitCount S A (augmentedFamily S safe) ≤ S.finiteSort.elems.sum (fun i =>
      S.finiteSort.elems.sum fun j =>
        2 * Nat.card (homFamily S (originalFamily S) i j) - Nat.card (S.Atom i j)) :=
  orbitCount_le_sum_of_hom_bound S A (augmented_current_self S safe H sap hs)
    (fun i j => 2 * Nat.card (homFamily S (originalFamily S) i j))
    (augmented_hom_card_le_twice S safe)

/-- Gates run after the actual T image, with the original augmented orbit budget. -/
theorem safe_gate_iteration (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) (C : MenuCalculus S (augmentedFamily S safe))
    (A : PureTagAction S Λ N) (hSafe : SafeInvariant S safe A)
    (hNoReturn : NoReturn S (augmentedFamily S safe) A) :
    ∃ K, Current S (augmentedFamily S safe) K ∧ A.Invariant K ∧ Terminal S K ∧
      ∃ n, n ≤ orbitCount S A (augmentedFamily S safe) ∧
        ∃ chain : DescentChain S (IsVisibleGate S (Q := augmentedFamily S safe) A)
            (safeImage S safe) K n,
          A.Covariant (DescentChain.composite chain) := by
  obtain ⟨K,hK,hKI,hTerm,n,hOrbit,_,chain,hCov⟩ :=
    pure_gate_iteration_orbit_bound S C (S.realPointGluing_of_SAP H sap) (S.realEdgeGluing_of_SAP H sap)
      A (augmentedFamily_invariant S safe A hSafe) hNoReturn (safeImage S safe)
      (safeImage_current S safe H sap hs) (safeImage_invariant S safe A hSafe)
  exact ⟨K,hK,hKI,hTerm,n,hOrbit.trans (orbitCount_mono S A (safeImage_subset S safe)),chain,hCov⟩

/-- A terminal contraction after T yields the promised safe reading. -/
theorem safe_selectorOfTerminal_safe (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) {K : Family S} (hTerm : Terminal S K)
    (R : Contraction S (safeImage S safe) K) {i j} (D : S.Menu i j)
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ augmentedFamily S safe)
    (hmeet : (D ∩ safe i j).Nonempty) :
    (selectorOfTerminal S hTerm ((safeContraction S safe H sap hs).comp R)).choose D hD ∈ safe i j := by
  let T := safeContraction S safe H sap hs
  let h := selectorOfTerminal S hTerm (T.comp R)
  have hout : h.choose D hD ∈ R.toFun (safeRetract S safe D) := by
    change h.choose D hD ∈ (T.comp R).toFun D
    rw [selectorOfTerminal_singleton S hTerm (T.comp R) D hD]
    exact Set.mem_singleton _
  have hT : h.choose D hD ∈ safeRetract S safe D := R.conservative (T.maps hD) hout
  rw [safeRetract_of_meets S safe hmeet] at hT
  exact hT.2

/-- The given safe palette yields an actual coherent safe singleton reading. -/
theorem exists_safe_covariant_selector (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hs : SafeSystem S safe) (C : MenuCalculus S (augmentedFamily S safe))
    (A : PureTagAction S Λ N) (hSafe : SafeInvariant S safe A)
    (hNoReturn : NoReturn S (augmentedFamily S safe) A) :
    ∃ h : SelectorOn S (augmentedFamily S safe),
      h.Covariant A (augmentedFamily_invariant S safe A hSafe) ∧
      ∀ {i j} (D : S.Menu i j) (hD), (D ∩ safe i j).Nonempty → h.choose D hD ∈ safe i j := by
  obtain ⟨K,_,_,hTerm,_,_,chain,hCov⟩ := safe_gate_iteration S safe H sap hs C A hSafe hNoReturn
  let R := DescentChain.composite chain
  let T := safeContraction S safe H sap hs
  refine ⟨selectorOfTerminal S hTerm (T.comp R),?_,?_⟩
  · exact selectorOfTerminal_covariant S A hTerm (T.comp R)
      (A.covariant_comp (safeContraction_covariant S safe H sap hs A hSafe) hCov)
      (augmentedFamily_invariant S safe A hSafe)
  · intro i j D hD hmeet
    exact safe_selectorOfTerminal_safe S safe H sap hs hTerm R D hD hmeet

end CCO.SafeReadings
