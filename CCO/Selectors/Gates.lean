import CCO.Selectors.Basic

universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

noncomputable instance menuFintype (i j : ι) : Fintype (S.Menu i j) := by
  letI := S.finiteAtom i j
  exact Fintype.ofFinite _

noncomputable def active (F : Family S) (D : S.Menu i j) : Finset (S.Menu i j) := by
  classical
  exact Finset.univ.filter fun A => (⟨i,j,A⟩ : TaggedMenu S) ∈ F ∧ (A ∩ D).Nonempty

@[simp] theorem mem_active {F : Family S} {D A : S.Menu i j} :
    A ∈ active S F D ↔ (⟨i,j,A⟩ : TaggedMenu S) ∈ F ∧ (A ∩ D).Nonempty := by
  classical
  simp [active]

def gate (F : Family S) (D : S.Menu i j) : S.Menu i j :=
  D ∩ {a | ∀ A : S.Menu i j, (⟨i,j,A⟩ : TaggedMenu S) ∈ F →
    (A ∩ D).Nonempty → a ∈ A}

theorem gate_subset (F : Family S) (D : S.Menu i j) : gate S F D ⊆ D :=
  fun _ h => h.1

theorem gate_subset_active {F : Family S} {D A : S.Menu i j}
    (hA : (⟨i,j,A⟩ : TaggedMenu S) ∈ F) (hAD : (A ∩ D).Nonempty) :
    gate S F D ⊆ A := fun _ h => h.2 A hA hAD

theorem gate_eq_meet (F : Family S) (D : S.Menu i j) :
    gate S F D = StrongExact.meetMenus S (D :: (active S F D).toList) := by
  classical
  ext a
  simp only [gate, Set.mem_inter_iff, Set.mem_setOf_eq, StrongExact.meetMenus]
  constructor
  · rintro ⟨ha,h⟩ A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · exact ha
    · obtain ⟨hF,hAD⟩ := (mem_active S).mp (Finset.mem_toList.mp hA)
      exact h A hF hAD
  · intro h
    refine ⟨h D (by simp), ?_⟩
    intro A hF hAD
    exact h A (List.mem_cons_of_mem _ (Finset.mem_toList.mpr ((mem_active S).mpr ⟨hF,hAD⟩)))

theorem gate_exact (C : ExactCalculus S) {F J : Family S}
    (hF : FilterFamily S F) (hJ : CurrentFamily S J) (hV : Visible S F J)
    {D : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J) :
    StrongExact.Exact S (gate S F D) := by
  classical
  let L := D :: (active S F D).toList
  have hExact : ∀ A ∈ L, StrongExact.Exact S A := by
    intro A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · exact hJ.exact hD
    · exact hF.exact ((mem_active S).mp (Finset.mem_toList.mp hA)).1
  have hPair : ∀ A ∈ L, ∀ B ∈ L, (A ∩ B).Nonempty := by
    intro A hA B hB
    rcases List.mem_cons.mp hA with rfl | hA
    · rcases List.mem_cons.mp hB with rfl | hB
      · obtain ⟨a,ha⟩ := (hJ.exact hD).1
        exact ⟨a,ha,ha⟩
      · obtain ⟨_,b,hb,hbd⟩ := (mem_active S).mp (Finset.mem_toList.mp hB)
        exact ⟨b,hbd,hb⟩
    · obtain ⟨hAF,hAD⟩ := (mem_active S).mp (Finset.mem_toList.mp hA)
      rcases List.mem_cons.mp hB with rfl | hB
      · exact hAD
      · obtain ⟨hBF,hBD⟩ := (mem_active S).mp (Finset.mem_toList.mp hB)
        exact hV hD hAF hBF hAD hBD
  rw [gate_eq_meet S]
  exact StrongExact.exact_meetMenus_of_nonempty S L hExact (C.helly L hExact hPair)

theorem gate_current (C : ExactCalculus S) {F J : Family S}
    (hF : FilterFamily S F) (hJ : CurrentFamily S J) (hV : Visible S F J)
    {D : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J) :
    (⟨i,j,gate S F D⟩ : TaggedMenu S) ∈ J :=
  hJ.downward hD (gate_exact S C hF hJ hV hD) (gate_subset S F D)

/-- Actual active families agree on every surviving restriction. -/
theorem gate_heredity (F : Family S) {E D : S.Menu i j}
    (hED : E ⊆ D) (hSurvive : (E ∩ gate S F D).Nonempty) :
    gate S F E = E ∩ gate S F D := by
  obtain ⟨x,hxE,hxD⟩ := hSurvive
  apply Set.Subset.antisymm
  · intro a ha
    refine ⟨ha.1,hED ha.1,?_⟩
    intro A hAF hAD
    have hxA : x ∈ A := hxD.2 A hAF hAD
    exact ha.2 A hAF ⟨x,hxA,hxE⟩
  · rintro a ⟨haE,haD⟩
    refine ⟨haE,?_⟩
    intro A hAF hAE
    obtain ⟨b,hbA,hbE⟩ := hAE
    exact haD.2 A hAF ⟨b,hbA,hED hbE⟩

theorem gate_opposite {F : Family S} (hF : FilterFamily S F) (D : S.Menu i j) :
    gate S F (S.opposite D) = S.opposite (gate S F D) := by
  ext a
  constructor
  · intro ha
    refine ⟨ha.1,?_⟩
    intro A hAF hAD
    obtain ⟨b,hbA,hbD⟩ := hAD
    have hOppF : (⟨j,i,S.opposite A⟩ : TaggedMenu S) ∈ F := hF.opposite hAF
    have hOppD : (S.opposite A ∩ S.opposite D).Nonempty :=
      ⟨S.conv b,S.mem_opposite hbA,S.mem_opposite hbD⟩
    exact ha.2 (S.opposite A) hOppF hOppD
  · intro ha
    refine ⟨ha.1,?_⟩
    intro A hAF hAD
    obtain ⟨b,hbA,hbD⟩ := hAD
    have hOppF : (⟨i,j,S.opposite A⟩ : TaggedMenu S) ∈ F := hF.opposite hAF
    have hOppD : (S.opposite A ∩ D).Nonempty := ⟨S.conv b,S.mem_opposite hbA,hbD⟩
    have h := ha.2 (S.opposite A) hOppF hOppD
    change S.conv (S.conv a) ∈ A at h
    simpa only [S.conv_invol] using h

end CCO.Selectors
