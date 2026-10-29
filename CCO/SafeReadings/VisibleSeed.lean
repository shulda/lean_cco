import CCO.SafeReadings.GateImage

universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t} {Q : Family S}

theorem generated_member (C : MenuCalculus S Q) (A : PureTagAction S Λ N) (hQI : A.Invariant Q)
    {seed D} (hs : seed ∈ Q) (h : Generated S Q A seed D) : D ∈ Q := by
  induction h with
  | seed => exact hs
  | opposite h ih => exact C.opposite ih
  | left P hP h ih => exact C.product hP ih
  | right P hP h ih => exact C.product ih hP
  | action g h ih => exact hQI g _ ih

theorem generated_filter (C : MenuCalculus S Q) (A : PureTagAction S Λ N) (hQI : A.Invariant Q)
    (seed : TaggedMenu S) (hs : seed ∈ Q) : Filter S Q (generatedFamily S Q A seed) where
  member _ h := generated_member S C A hQI hs h
  opposite := Generated.opposite
  left := by
    intro i j k P hP D h
    exact Generated.left P hP h
  right := by
    intro i j k P hP D h
    exact Generated.right P hP h

theorem generated_invariant (A : PureTagAction S Λ N) (seed : TaggedMenu S) :
    A.Invariant (generatedFamily S Q A seed) := fun g _ h => Generated.action g h

theorem generated_trans (A : PureTagAction S Λ N) {B C D : TaggedMenu S}
    (hBC : Generated S Q A B C) (hCD : Generated S Q A C D) : Generated S Q A B D := by
  induction hCD with
  | seed => exact hBC
  | opposite h ih => exact Generated.opposite ih
  | left P hP h ih => exact Generated.left P hP ih
  | right P hP h ih => exact Generated.right P hP ih
  | action g h ih => exact Generated.action g ih

theorem generated_subset (A : PureTagAction S Λ N) {B C : TaggedMenu S}
    (h : C ∈ generatedFamily S Q A B) : generatedFamily S Q A C ⊆ generatedFamily S Q A B :=
  fun _ hd => generated_trans S A h hd

theorem exists_viable (C : MenuCalculus S Q) (J : Family S) (hJ : Current S Q J) (hNot : ¬Terminal S J) :
    ∃ seed, seed ∈ Q ∧ Viable S J seed := by
  classical
  simp only [Terminal] at hNot
  push_neg at hNot
  obtain ⟨⟨i,j,D⟩,hD,hNot⟩ := hNot
  obtain ⟨a,ha⟩ := C.nonempty (hJ.member hD)
  refine ⟨⟨i,j,{a}⟩,C.singleton a,D,hD,⟨a,by simp,ha⟩,?_⟩
  intro hsub
  apply hNot a
  exact Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr ha)

/-- C25: finite MINIMUM of actual generated families is relatively visible. -/
theorem exists_visible_viable (C : MenuCalculus S Q) (A : PureTagAction S Λ N) (hQI : A.Invariant Q)
    (J : Family S) (hNoReturn : NoReturn S Q A)
    (hViable : ∃ seed, seed ∈ Q ∧ Viable S J seed) :
    ∃ seed, seed ∈ Q ∧ Viable S J seed ∧ Visible S (generatedFamily S Q A seed) J := by
  classical
  have hn : ∃ n : ℕ, ∃ seed, seed ∈ Q ∧ Viable S J seed ∧
      Nat.card (generatedFamily S Q A seed) = n := by
    obtain ⟨seed,hs,hv⟩ := hViable
    exact ⟨_,seed,hs,hv,rfl⟩
  obtain ⟨seed,hs,hv,hsize⟩ := Nat.find_spec hn
  have hmin : ∀ B, B ∈ Q → Viable S J B →
      Nat.card (generatedFamily S Q A seed) ≤ Nat.card (generatedFamily S Q A B) := by
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
  have hEqB : generatedFamily S Q A ⟨i,j,B⟩ = generatedFamily S Q A seed :=
    Set.eq_of_subset_of_ncard_le (generated_subset S A hB)
      (hmin _ (generated_member S C A hQI hs hB) hvB)
  have hEqE : generatedFamily S Q A ⟨i,j,E⟩ = generatedFamily S Q A seed :=
    Set.eq_of_subset_of_ncard_le (generated_subset S A hE)
      (hmin _ (generated_member S C A hQI hs hE) hvE)
  have htag := hNoReturn seed hs ⟨i,j,B⟩ ⟨i,j,E⟩ hB hE ⟨rfl,rfl⟩ (hEqB.trans hEqE.symm)
  have hmenu : B = E := by cases htag; rfl
  subst E
  obtain ⟨b,hb,_⟩ := hBD
  have hbad : b ∈ B ∩ B := ⟨hb,hb⟩
  rw [hBE] at hbad
  exact hbad

/-- The chosen filter is actual, action-invariant, visible and has a proper active trace. -/
theorem visible_step_exists (C : MenuCalculus S Q) (A : PureTagAction S Λ N) (hQI : A.Invariant Q)
    {J : Family S} (hJ : Current S Q J) (hNoReturn : NoReturn S Q A)
    (hNot : ¬Terminal S J) :
    ∃ F : Family S, Filter S Q F ∧ A.Invariant F ∧ Visible S F J ∧
      ∃ (i j : ι) (D P : S.Menu i j), (⟨i,j,D⟩ : TaggedMenu S) ∈ J ∧
        (⟨i,j,P⟩ : TaggedMenu S) ∈ F ∧ (P ∩ D).Nonempty ∧ ¬D ⊆ P := by
  obtain ⟨seed,hs,hv,hVis⟩ := exists_visible_viable S C A hQI J hNoReturn (exists_viable S C J hJ hNot)
  obtain ⟨D,hD,hMeet,hProper⟩ := hv
  exact ⟨generatedFamily S Q A seed,generated_filter S C A hQI seed hs,generated_invariant S A seed,
    hVis,seed.1,seed.2.1,D,seed.2.2,hD,Generated.seed,hMeet,hProper⟩

end CCO.SafeReadings
