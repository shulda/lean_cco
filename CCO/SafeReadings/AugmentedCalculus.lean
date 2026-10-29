import CCO.SafeReadings.AugmentedMenus

/-! Actual finite 2-Helly for safe traces: choose long witnesses for ALL
skeletons and recolour ONCE. A common original atom is never simply
assumed safe. The singleton alternative is treated separately. -/
universe u v w
namespace CCO.SafeReadings
open StrongExact Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]

/-- The false flag means the WHOLE diversity palette, never equality. -/
theorem augmented_bool_skeleton {safe : ∀ i j, S.Menu i j} {i j} {D : S.Menu i j}
    (hD : Augmented S safe D) :
    ∃ E, Exact S E ∧ ∃ flag : Bool, D = E ∩ (if flag then safe i j else Set.univ) := by
  obtain ⟨E,hE,he⟩ := hD.skeleton
  rcases he with he | he
  · exact ⟨E,hE,false,by simpa only [Bool.false_eq_true,↓reduceIte,Set.inter_univ] using he⟩
  · exact ⟨E,hE,true,he⟩

theorem skeleton_flags_inter {safe : ∀ i j, S.Menu i j} {i j} (D E : S.Menu i j)
    (a b : Bool) :
    (D ∩ (if a then safe i j else Set.univ)) ∩ (E ∩ (if b then safe i j else Set.univ)) =
      (D ∩ E) ∩ (if a || b then safe i j else Set.univ) := by
  cases a <;> cases b <;> ext c <;> simp only [Bool.false_eq_true,Bool.or_false,Bool.or_true,
    ↓reduceIte,Set.mem_inter_iff,Set.mem_univ,and_true] <;> tauto

theorem singleton_trace_nonempty_iff {safe : ∀ i j, S.Menu i j} {i j} (a : S.Atom i j) :
    (({a} : S.Menu i j) ∩ safe i j).Nonempty ↔ a ∈ safe i j := by simp

/-- Explicit finite-meet closure, including the empty Top family. -/
theorem MenuCalculus.meet_member {Q : Family S} (C : MenuCalculus S Q)
    {i j} (menus : List (S.Menu i j))
    (hm : ∀ D ∈ menus, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q)
    (hne : (meetMenus S menus).Nonempty) :
    (⟨i,j,meetMenus S menus⟩ : TaggedMenu S) ∈ Q := by
  induction menus with
  | nil =>
    have he : meetMenus S ([] : List (S.Menu i j)) = Set.univ := by ext a; simp [meetMenus]
    rw [he]; exact C.top i j
  | cons D rest ih =>
    have he : meetMenus S (D :: rest) = D ∩ meetMenus S rest := by
      ext a; simp [meetMenus]
    have hnrest : (meetMenus S rest).Nonempty := by
      obtain ⟨a,ha⟩ := hne
      exact ⟨a,fun E hE => ha E (List.mem_cons_of_mem D hE)⟩
    rw [he]
    exact C.inter (hm D List.mem_cons_self)
      (ih (fun E hE => hm E (List.mem_cons_of_mem D hE)) hnrest) (he ▸ hne)

noncomputable def originalSkeleton (safe : ∀ i j, S.Menu i j) {i j} (D : S.Menu i j) : S.Menu i j := by
  classical
  exact if h : Augmented S safe D then Classical.choose h.skeleton else D

theorem originalSkeleton_spec {safe : ∀ i j, S.Menu i j} {i j} {D : S.Menu i j}
    (hD : Augmented S safe D) : Exact S (originalSkeleton S safe D) ∧
      (D = originalSkeleton S safe D ∨ D = originalSkeleton S safe D ∩ safe i j) := by
  classical
  simpa only [originalSkeleton,dite_eq_left hD] using Classical.choose_spec hD.skeleton

theorem wordsOfExact_long {i j} {D : S.Menu i j} (hD : Exact S D)
    (hns : ∀ a, D ≠ {a}) (a : S.Atom i j) :
    (PositiveWord.single a : PositiveWord S i j) ∉ wordsOfExact S D := by
  intro ha
  apply hns a
  have hsub : D ⊆ {a} := by
    intro b hb
    rw [wordsOfExact_spec S hD] at hb
    exact hb (.single a) ha
  obtain ⟨b,hb⟩ := hD.1
  have hba : b = a := Set.mem_singleton_iff.mp (hsub hb)
  exact Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr (hba ▸ hb))

theorem nonsingleton_exact_meet_safe (H : HomogeneousSource S G) (sap : AgeSAP S)
    {safe : ∀ i j, S.Menu i j} (hs : StrongSafeAmalgamation S safe)
    {i j} (menus : List (S.Menu i j))
    (hExact : ∀ D ∈ menus, Exact S D)
    (hns : ∀ D ∈ menus, ∀ a, D ≠ {a})
    (hne : (meetMenus S menus).Nonempty) :
    (meetMenus S menus ∩ safe i j).Nonempty := by
  classical
  let ws := menus.flatMap (wordsOfExact S)
  have he : meetMenus S menus = present S ws := by
    ext a
    constructor
    · intro ha word hw
      obtain ⟨D,hD,hword⟩ := List.mem_flatMap.mp hw
      have hd := ha D hD
      rw [wordsOfExact_spec S (hExact D hD)] at hd
      exact hd word hword
    · intro ha D hD
      rw [wordsOfExact_spec S (hExact D hD)]
      intro word hw
      exact ha word (List.mem_flatMap.mpr ⟨D,hD,hw⟩)
  have hlong : ∀ a, (PositiveWord.single a : PositiveWord S i j) ∉ ws := by
    intro a ha
    obtain ⟨D,hD,hw⟩ := List.mem_flatMap.mp ha
    exact wordsOfExact_long S (hExact D hD) (hns D hD) a hw
  rw [he]
  exact long_present_meets_safe S H sap hs ws hlong (he ▸ hne)

theorem augmented_helly (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    {safe : ∀ i j, S.Menu i j} (hs : StrongSafeAmalgamation S safe)
    {i j} (menus : List (S.Menu i j))
    (hAug : ∀ D ∈ menus, Augmented S safe D)
    (hPair : ∀ D ∈ menus, ∀ E ∈ menus, (D ∩ E).Nonempty) :
    (meetMenus S menus).Nonempty := by
  classical
  let skel : S.Menu i j → S.Menu i j := originalSkeleton S safe
  let originals := menus.map skel
  have hspec (D) (hD : D ∈ menus) := originalSkeleton_spec S (hAug D hD)
  have hExact : ∀ D ∈ originals, Exact S D := by
    intro D hD
    obtain ⟨E,hE,rfl⟩ := List.mem_map.mp hD
    exact (hspec E hE).1
  have hOriginalPair : ∀ D ∈ originals, ∀ E ∈ originals, (D ∩ E).Nonempty := by
    intro D hD E hE
    obtain ⟨D0,hD0,rfl⟩ := List.mem_map.mp hD
    obtain ⟨E0,hE0,rfl⟩ := List.mem_map.mp hE
    obtain ⟨a,ha,hb⟩ := hPair D0 hD0 E0 hE0
    exact ⟨a,Augmented.subset_skeleton S (hspec D0 hD0).2 ha,
      Augmented.subset_skeleton S (hspec E0 hE0).2 hb⟩
  have hmeet := exact_helly_of_SAP_CCO S H sap cco originals hExact hOriginalPair
  by_cases hsingle : ∃ D ∈ menus, ∃ a, skel D = {a}
  · obtain ⟨D,hD,a,ha⟩ := hsingle
    have hDa : D = {a} := by
      have hsub : D ⊆ {a} := ha ▸ Augmented.subset_skeleton S (hspec D hD).2
      obtain ⟨b,hb⟩ := (hAug D hD).nonempty
      have hba : b = a := Set.mem_singleton_iff.mp (hsub hb)
      exact Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr (hba ▸ hb))
    refine ⟨a,?_⟩
    intro E hE
    obtain ⟨b,hb,he⟩ := hPair D hD E hE
    have hba : b = a := Set.mem_singleton_iff.mp (hDa ▸ hb)
    exact hba ▸ he
  · have hns : ∀ D ∈ originals, ∀ a, D ≠ {a} := by
      intro D hD a he
      obtain ⟨E,hE,rfl⟩ := List.mem_map.mp hD
      exact hsingle ⟨E,hE,a,he⟩
    obtain ⟨a,ha,hasafe⟩ := nonsingleton_exact_meet_safe S H sap hs originals hExact hns hmeet
    refine ⟨a,?_⟩
    intro D hD
    have had : a ∈ skel D := ha _ (List.mem_map.mpr ⟨D,hD,rfl⟩)
    rcases (hspec D hD).2 with he | he
    · exact he.symm ▸ had
    · exact he.symm ▸ ⟨had,hasafe⟩

theorem skeleton_inter {safe : ∀ i j, S.Menu i j} {i j} {D E D' E' : S.Menu i j}
    (hd : D = D' ∨ D = D' ∩ safe i j) (he : E = E' ∨ E = E' ∩ safe i j) :
    D ∩ E = D' ∩ E' ∨ D ∩ E = (D' ∩ E') ∩ safe i j := by
  rcases hd with hd | hd <;> rcases he with he | he
  · exact Or.inl (by rw [hd,he])
  all_goals apply Or.inr; rw [hd,he]; ext a; simp only [Set.mem_inter_iff]; tauto

theorem augmented_distrib (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    {safe : ∀ i j, S.Menu i j} (hs : SafeSystem S safe)
    {i j k} {P : S.Menu i j} {D E : S.Menu j k}
    (hP : Augmented S safe P) (hD : Augmented S safe D) (hE : Augmented S safe E)
    (hne : (D ∩ E).Nonempty) :
    S.product P (D ∩ E) = S.product P D ∩ S.product P E := by
  obtain ⟨P',hP',hp⟩ := hP.skeleton
  obtain ⟨D',hD',hd⟩ := hD.skeleton
  obtain ⟨E',hE',he⟩ := hE.skeleton
  have hne' : (D' ∩ E').Nonempty := by
    obtain ⟨a,ha,hb⟩ := hne
    exact ⟨a,Augmented.subset_skeleton S hd ha,Augmented.subset_skeleton S he hb⟩
  have hde := skeleton_inter S hd he
  rw [Augmented.skeleton_product S H sap hs hP' (exact_inter S hD' hE' hne') hP.nonempty hne hp hde,
    (original_calculus S H sap cco).distrib hP' hD' hE' hne',
    Augmented.skeleton_product S H sap hs hP' hD' hP.nonempty hD.nonempty hp hd,
    Augmented.skeleton_product S H sap hs hP' hE' hP.nonempty hE.nonempty hp he]

/-- All generic-Q gate obligations are now discharged for the ACTUAL
evaluated augmented family. No assertion of original exactness for a
nonexact safe trace occurs in this construction. -/
theorem augmented_calculus (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    {safe : ∀ i j, S.Menu i j} (hs : SafeSystem S safe) :
    MenuCalculus S (augmentedFamily S safe) := by
  refine {
    nonempty := fun h => h.nonempty
    top := fun i j => Or.inl (exact_top_of_SAP S H sap)
    singleton := fun a => Or.inl (exact_singleton S a)
    opposite := ?_
    product := fun hD hE => Or.inl (augmented_product_exact S H sap cco hs hD hE)
    inter := augmented_inter S
    helly := augmented_helly S H sap cco hs.amalgamation
    distrib := augmented_distrib S H sap cco hs }
  intro D hD
  exact augmented_opposite S H sap hs hD

end CCO.SafeReadings
