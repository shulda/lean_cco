import CCO.Selectors.PureAction

universe u v w z t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t}

/-- Original generation, enlarged only by the stated pure tag action. -/
inductive ActionGenerated (A : PureTagAction S Λ N) (seed : TaggedMenu S) : TaggedMenu S → Prop
  | seed : ActionGenerated A seed seed
  | opposite {D} : ActionGenerated A seed D → ActionGenerated A seed (flip S D)
  | left {i j k} (P : S.Menu i j) (hP : StrongExact.Exact S P) {D : S.Menu j k} :
      ActionGenerated A seed ⟨j,k,D⟩ → ActionGenerated A seed ⟨i,k,S.product P D⟩
  | right {i j k} {D : S.Menu i j} (P : S.Menu j k) (hP : StrongExact.Exact S P) :
      ActionGenerated A seed ⟨i,j,D⟩ → ActionGenerated A seed ⟨i,k,S.product D P⟩
  | action (g : Λ) {D} : ActionGenerated A seed D → ActionGenerated A seed (A.act g D)

def generatedFamily (A : PureTagAction S Λ N) (seed : TaggedMenu S) : Family S :=
  {D | ActionGenerated S A seed D}

def PureNoReturn (A : PureTagAction S Λ N) : Prop :=
  ∀ seed, IsExact S seed → ∀ D E, D ∈ generatedFamily S A seed → E ∈ generatedFamily S A seed →
    Parallel S D E → generatedFamily S A D = generatedFamily S A E → D = E

theorem generated_exact (C : ExactCalculus S) (A : PureTagAction S Λ N)
    {seed D} (hs : IsExact S seed) (h : ActionGenerated S A seed D) : IsExact S D := by
  induction h with
  | seed => exact hs
  | opposite h ih => exact C.opposite ih
  | left P hP h ih => exact C.product hP ih
  | right P hP h ih => exact C.product ih hP
  | action g h ih => exact (A.exact g _).mpr ih

theorem generated_filter (C : ExactCalculus S) (A : PureTagAction S Λ N)
    (seed : TaggedMenu S) (hs : IsExact S seed) : FilterFamily S (generatedFamily S A seed) where
  exact h := generated_exact S C A hs h
  opposite := ActionGenerated.opposite
  left := by
    intro i j k P hP D h
    exact ActionGenerated.left P hP h
  right := by
    intro i j k P hP D h
    exact ActionGenerated.right P hP h

theorem generated_invariant (A : PureTagAction S Λ N) (seed : TaggedMenu S) :
    A.Invariant (generatedFamily S A seed) := fun g _ h => ActionGenerated.action g h

theorem generated_trans (A : PureTagAction S Λ N) {B C D : TaggedMenu S}
    (hBC : ActionGenerated S A B C) (hCD : ActionGenerated S A C D) : ActionGenerated S A B D := by
  induction hCD with
  | seed => exact hBC
  | opposite h ih => exact ActionGenerated.opposite ih
  | left P hP h ih => exact ActionGenerated.left P hP ih
  | right P hP h ih => exact ActionGenerated.right P hP ih
  | action g h ih => exact ActionGenerated.action g ih

theorem generated_subset (A : PureTagAction S Λ N) {B C : TaggedMenu S}
    (h : C ∈ generatedFamily S A B) : generatedFamily S A C ⊆ generatedFamily S A B :=
  fun _ hd => generated_trans S A h hd

def Viable (J : Family S) (seed : TaggedMenu S) : Prop :=
  ∃ D : S.Menu seed.1 seed.2.1, (⟨seed.1,seed.2.1,D⟩ : TaggedMenu S) ∈ J ∧
    (seed.2.2 ∩ D).Nonempty ∧ ¬D ⊆ seed.2.2

def Terminal (J : Family S) : Prop :=
  ∀ D ∈ J, ∃ a, D.2.2 = ({a} : S.Menu D.1 D.2.1)

theorem exists_viable (J : Family S) (hJ : CurrentFamily S J) (hNot : ¬Terminal S J) :
    ∃ seed, IsExact S seed ∧ Viable S J seed := by
  classical
  simp only [Terminal] at hNot
  push_neg at hNot
  obtain ⟨⟨i,j,D⟩,hD,hNot⟩ := hNot
  obtain ⟨a,ha⟩ := (hJ.exact hD).1
  refine ⟨⟨i,j,{a}⟩,StrongExact.exact_singleton S a,D,hD,⟨a,by simp,ha⟩,?_⟩
  intro hsub
  apply hNot a
  exact Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr ha)

/-- C25: finite MINIMUM of actual generated families is relatively visible. -/
theorem exists_visible_viable (C : ExactCalculus S) (A : PureTagAction S Λ N)
    (J : Family S) (hNoReturn : PureNoReturn S A)
    (hViable : ∃ seed, IsExact S seed ∧ Viable S J seed) :
    ∃ seed, IsExact S seed ∧ Viable S J seed ∧ Visible S (generatedFamily S A seed) J := by
  classical
  have hn : ∃ n : ℕ, ∃ seed, IsExact S seed ∧ Viable S J seed ∧
      Nat.card (generatedFamily S A seed) = n := by
    obtain ⟨seed,hs,hv⟩ := hViable
    exact ⟨_,seed,hs,hv,rfl⟩
  obtain ⟨seed,hs,hv,hsize⟩ := Nat.find_spec hn
  have hmin : ∀ B, IsExact S B → Viable S J B →
      Nat.card (generatedFamily S A seed) ≤ Nat.card (generatedFamily S A B) := by
    intro B hB hvB
    rw [hsize]
    exact Nat.find_min' hn ⟨B,hB,hvB,rfl⟩
  refine ⟨seed,hs,hv,?_⟩
  by_contra hVis
  simp only [Visible] at hVis
  push_neg at hVis
  obtain ⟨i,j,D,B,E,hD,hB,hE,hBD,hED,hBE⟩ := hVis
  have hvB : Viable S J ⟨i,j,B⟩ := by
    refine ⟨D,hD,hBD,?_⟩
    intro hsub
    obtain ⟨e,he,hed⟩ := hED
    have hbad : e ∈ B ∩ E := ⟨hsub hed,he⟩
    rw [hBE] at hbad
    exact hbad
  have hvE : Viable S J ⟨i,j,E⟩ := by
    refine ⟨D,hD,hED,?_⟩
    intro hsub
    obtain ⟨b,hb,hbd⟩ := hBD
    have hbad : b ∈ B ∩ E := ⟨hb,hsub hbd⟩
    rw [hBE] at hbad
    exact hbad
  have hEqB : generatedFamily S A ⟨i,j,B⟩ = generatedFamily S A seed :=
    Set.eq_of_subset_of_ncard_le (generated_subset S A hB)
      (hmin _ (generated_exact S C A hs hB) hvB)
  have hEqE : generatedFamily S A ⟨i,j,E⟩ = generatedFamily S A seed :=
    Set.eq_of_subset_of_ncard_le (generated_subset S A hE)
      (hmin _ (generated_exact S C A hs hE) hvE)
  have htag := hNoReturn seed hs ⟨i,j,B⟩ ⟨i,j,E⟩ hB hE ⟨rfl,rfl⟩ (hEqB.trans hEqE.symm)
  have hmenu : B = E := by cases htag; rfl
  subst E
  obtain ⟨b,hb,_⟩ := hBD
  have hbad : b ∈ B ∩ B := ⟨hb,hb⟩
  rw [hBE] at hbad
  exact hbad

/-- The chosen filter is actual, action-invariant, visible and has a proper active trace. -/
theorem visible_step_exists (C : ExactCalculus S) (A : PureTagAction S Λ N)
    {J : Family S} (hJ : CurrentFamily S J) (hNoReturn : PureNoReturn S A)
    (hNot : ¬Terminal S J) :
    ∃ F : Family S, FilterFamily S F ∧ A.Invariant F ∧ Visible S F J ∧
      ∃ (i j : ι) (D P : S.Menu i j), (⟨i,j,D⟩ : TaggedMenu S) ∈ J ∧
        (⟨i,j,P⟩ : TaggedMenu S) ∈ F ∧ (P ∩ D).Nonempty ∧ ¬D ⊆ P := by
  obtain ⟨seed,hs,hv,hVis⟩ := exists_visible_viable S C A J hNoReturn (exists_viable S J hJ hNot)
  obtain ⟨D,hD,hMeet,hProper⟩ := hv
  exact ⟨generatedFamily S A seed,generated_filter S C A seed hs,generated_invariant S A seed,
    hVis,seed.1,seed.2.1,D,seed.2.2,hD,ActionGenerated.seed,hMeet,hProper⟩

end CCO.Selectors
