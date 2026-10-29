import CCO.SafeReadings.MenuCalculus

universe u v w
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι} {Q : Family S}

/-- Closure of a genuinely nonempty finite evaluated meet in Q. -/
theorem meet_member (C : MenuCalculus S Q) {i j} (L : List (S.Menu i j))
    (hQ : ∀ A ∈ L, (⟨i,j,A⟩ : TaggedMenu S) ∈ Q)
    (hne : (StrongExact.meetMenus S L).Nonempty) :
    (⟨i,j,StrongExact.meetMenus S L⟩ : TaggedMenu S) ∈ Q := by
  induction L with
  | nil => simpa [StrongExact.meetMenus] using C.top i j
  | cons A L ih =>
    have ht : (StrongExact.meetMenus S L).Nonempty := by
      obtain ⟨a,ha⟩ := hne
      exact ⟨a, fun E hE => ha E (by simp [hE])⟩
    have heq : StrongExact.meetMenus S (A :: L) = A ∩ StrongExact.meetMenus S L := by
      ext a
      simp [StrongExact.meetMenus]
    rw [heq] at hne ⊢
    exact C.inter (hQ A (by simp)) (ih (fun E hE => hQ E (by simp [hE])) ht) hne

/-- Visibility and the Q Helly axiom give actual gate nonemptiness. -/
theorem gate_nonempty (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J) :
    (gate S F D).Nonempty := by
  classical
  let L := D :: (active S F D).toList
  have hQ : ∀ A ∈ L, (⟨i,j,A⟩ : TaggedMenu S) ∈ Q := by
    intro A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · exact hJ.member hD
    · exact hF.member ((mem_active S).mp (Finset.mem_toList.mp hA)).1
  have hPair : ∀ A ∈ L, ∀ B ∈ L, (A ∩ B).Nonempty := by
    intro A hA B hB
    rcases List.mem_cons.mp hA with rfl | hA
    · rcases List.mem_cons.mp hB with rfl | hB
      · obtain ⟨a,ha⟩ := C.nonempty (hJ.member hD)
        exact ⟨a,ha,ha⟩
      · obtain ⟨_,b,hb,hbd⟩ := (mem_active S).mp (Finset.mem_toList.mp hB)
        exact ⟨b,hbd,hb⟩
    · obtain ⟨hAF,hAD⟩ := (mem_active S).mp (Finset.mem_toList.mp hA)
      rcases List.mem_cons.mp hB with rfl | hB
      · exact hAD
      · obtain ⟨hBF,hBD⟩ := (mem_active S).mp (Finset.mem_toList.mp hB)
        exact hV hD hAF hBF hAD hBD
  rw [gate_eq_meet S]
  exact C.helly L hQ hPair

theorem gate_member (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J) :
    (⟨i,j,gate S F D⟩ : TaggedMenu S) ∈ Q := by
  classical
  rw [gate_eq_meet S]
  apply meet_member S C
  · intro A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · exact hJ.member hD
    · exact hF.member ((mem_active S).mp (Finset.mem_toList.mp hA)).1
  · rw [← gate_eq_meet S]
    exact gate_nonempty S C hF hJ hV hD

theorem gate_current (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J) :
    (⟨i,j,gate S F D⟩ : TaggedMenu S) ∈ J :=
  hJ.downward hD (gate_member S C hF hJ hV hD) (gate_subset S F D)

theorem gate_opposite {F : Family S} (hF : Filter S Q F) (D : S.Menu i j) :
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

private theorem meet_cons_inter (E A : S.Menu k j) (L : List (S.Menu k j)) :
    StrongExact.meetMenus S ((E ∩ A) :: L) =
      StrongExact.meetMenus S (E :: A :: L) := by
  ext x
  simp [StrongExact.meetMenus]
  tauto

/-- Distribution used only at a genuinely nonempty evaluated meet. -/
theorem product_finite_meet_mem (C : MenuCalculus S Q)
    {P : S.Menu i k} (hP : (⟨i,k,P⟩ : TaggedMenu S) ∈ Q)
    {E : S.Menu k j} (L : List (S.Menu k j))
    (hE : (⟨k,j,E⟩ : TaggedMenu S) ∈ Q)
    (hExact : ∀ A ∈ L, (⟨k,j,A⟩ : TaggedMenu S) ∈ Q)
    (hMeet : (StrongExact.meetMenus S (E :: L)).Nonempty)
    {c : S.Atom i j} (hcE : c ∈ S.product P E)
    (hc : ∀ A ∈ L, c ∈ S.product P A) :
    c ∈ S.product P (StrongExact.meetMenus S (E :: L)) := by
  induction L generalizing E with
  | nil => simpa [StrongExact.meetMenus] using hcE
  | cons A L ih =>
      obtain ⟨x,hx⟩ := hMeet
      have hxE : x ∈ E := hx E (by simp)
      have hxA : x ∈ A := hx A (by simp)
      have hEA : (E ∩ A).Nonempty := ⟨x,hxE,hxA⟩
      have hEAexact := C.inter hE (hExact A (by simp)) hEA
      have hcEA : c ∈ S.product P (E ∩ A) := by
        rw [C.distrib hP hE (hExact A (by simp)) hEA]
        exact ⟨hcE,hc A (by simp)⟩
      have hNew : (StrongExact.meetMenus S ((E ∩ A) :: L)).Nonempty := by
        rw [meet_cons_inter S]
        exact ⟨x,hx⟩
      rw [← meet_cons_inter S]
      exact ih hEAexact (fun B hB => hExact B (by simp [hB])) hNew hcEA
        (fun B hB => hc B (by simp [hB]))

/-- C15: fixed LEFT original exact factor, not necessarily current. -/
theorem gate_bilateral_left (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D : S.Menu i j} {E : S.Menu k j} {P : S.Menu i k}
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J)
    (hE : (⟨k,j,E⟩ : TaggedMenu S) ∈ J) (hP : (⟨i,k,P⟩ : TaggedMenu S) ∈ Q)
    (hDE : D ⊆ S.product P E) (hED : E ⊆ S.product (S.opposite P) D) :
    gate S F D ⊆ S.product P (gate S F E) := by
  classical
  intro c hc
  rw [gate_eq_meet S F E]
  apply product_finite_meet_mem S C hP (active S F E).toList (hJ.member hE)
  · intro A hA
    exact hF.member ((mem_active S).mp (Finset.mem_toList.mp hA)).1
  · rw [← gate_eq_meet S]
    exact gate_nonempty S C hF hJ hV hE
  · exact hDE hc.1
  · intro A hA
    obtain ⟨hAF,e,heA,heE⟩ := (mem_active S).mp (Finset.mem_toList.mp hA)
    obtain ⟨p,hp,d,hd,htri⟩ := hED heE
    have hprod : d ∈ S.product P A :=
      ⟨S.conv p,hp,e,heA,S.triangle_rotate_back (S.triangle_cycle htri)⟩
    exact hc.2 (S.product P A) (hF.left P hP hAF) ⟨d,hprod,hd⟩

/-- Both original support inclusions survive the SAME visible gate. -/
theorem gate_bilateral (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D : S.Menu i j} {E : S.Menu k j} {P : S.Menu i k}
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J)
    (hE : (⟨k,j,E⟩ : TaggedMenu S) ∈ J) (hP : (⟨i,k,P⟩ : TaggedMenu S) ∈ Q)
    (hDE : D ⊆ S.product P E) (hED : E ⊆ S.product (S.opposite P) D) :
    gate S F D ⊆ S.product P (gate S F E) ∧
      gate S F E ⊆ S.product (S.opposite P) (gate S F D) := by
  refine ⟨gate_bilateral_left S C hF hJ hV hD hE hP hDE hED, ?_⟩
  apply gate_bilateral_left S C hF hJ hV hE hD (C.opposite hP) hED
  simpa only [S.opposite_opposite] using hDE

/-- C15 right-factor version, obtained by actual typed converse. -/
theorem gate_bilateral_right (C : MenuCalculus S Q) {F J : Family S}
    (hF : Filter S Q F) (hJ : Current S Q J) (hV : Visible S F J)
    {D : S.Menu i j} {E : S.Menu i k} {P : S.Menu k j}
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J)
    (hE : (⟨i,k,E⟩ : TaggedMenu S) ∈ J) (hP : (⟨k,j,P⟩ : TaggedMenu S) ∈ Q)
    (hDE : D ⊆ S.product E P) (hED : E ⊆ S.product D (S.opposite P)) :
    gate S F D ⊆ S.product (gate S F E) P := by
  have hDEop : S.opposite D ⊆ S.product (S.opposite P) (S.opposite E) := by
    rw [← S.product_opposite]
    exact fun _ h => hDE h
  have hEDop : S.opposite E ⊆ S.product (S.opposite (S.opposite P)) (S.opposite D) := by
    rw [← S.product_opposite]
    exact fun _ h => hED h
  have h := gate_bilateral_left S C hF hJ hV
    (D := S.opposite D) (E := S.opposite E) (P := S.opposite P)
    (hJ.opposite hD) (hJ.opposite hE) (C.opposite hP) hDEop hEDop
  rw [gate_opposite S hF D, gate_opposite S hF E] at h
  intro c hc
  have hin := h (S.mem_opposite hc)
  have hout : S.conv c ∈ S.opposite (S.product (gate S F E) P) := by
    rw [S.product_opposite]
    exact hin
  change S.conv (S.conv c) ∈ S.product (gate S F E) P at hout
  simpa only [S.conv_invol] using hout

end CCO.SafeReadings
