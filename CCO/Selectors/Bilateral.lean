import CCO.Selectors.Gates

universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

private theorem meet_cons_inter (E A : S.Menu k j) (L : List (S.Menu k j)) :
    StrongExact.meetMenus S ((E ∩ A) :: L) =
      StrongExact.meetMenus S (E :: A :: L) := by
  ext x
  simp [StrongExact.meetMenus]
  tauto

/-- Distribution used only at a genuinely nonempty evaluated meet. -/
theorem product_finite_meet_mem (C : ExactCalculus S)
    {P : S.Menu i k} (hP : StrongExact.Exact S P)
    {E : S.Menu k j} (L : List (S.Menu k j))
    (hE : StrongExact.Exact S E)
    (hExact : ∀ A ∈ L, StrongExact.Exact S A)
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
      have hEAexact := StrongExact.exact_inter S hE (hExact A (by simp)) hEA
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
theorem gate_bilateral_left (C : ExactCalculus S) {F J : Family S}
    (hF : FilterFamily S F) (hJ : CurrentFamily S J) (hV : Visible S F J)
    {D : S.Menu i j} {E : S.Menu k j} {P : S.Menu i k}
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J)
    (hE : (⟨k,j,E⟩ : TaggedMenu S) ∈ J) (hP : StrongExact.Exact S P)
    (hDE : D ⊆ S.product P E) (hED : E ⊆ S.product (S.opposite P) D) :
    gate S F D ⊆ S.product P (gate S F E) := by
  classical
  intro c hc
  rw [gate_eq_meet S F E]
  apply product_finite_meet_mem S C hP (active S F E).toList (hJ.exact hE)
  · intro A hA
    exact hF.exact ((mem_active S).mp (Finset.mem_toList.mp hA)).1
  · rw [← gate_eq_meet S]
    exact (gate_exact S C hF hJ hV hE).1
  · exact hDE hc.1
  · intro A hA
    obtain ⟨hAF,e,heA,heE⟩ := (mem_active S).mp (Finset.mem_toList.mp hA)
    obtain ⟨p,hp,d,hd,htri⟩ := hED heE
    have hprod : d ∈ S.product P A :=
      ⟨S.conv p,hp,e,heA,S.triangle_rotate_back (S.triangle_cycle htri)⟩
    exact hc.2 (S.product P A) (hF.left P hP hAF) ⟨d,hprod,hd⟩

/-- Both original support inclusions survive the SAME visible gate. -/
theorem gate_bilateral (C : ExactCalculus S) {F J : Family S}
    (hF : FilterFamily S F) (hJ : CurrentFamily S J) (hV : Visible S F J)
    {D : S.Menu i j} {E : S.Menu k j} {P : S.Menu i k}
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J)
    (hE : (⟨k,j,E⟩ : TaggedMenu S) ∈ J) (hP : StrongExact.Exact S P)
    (hDE : D ⊆ S.product P E) (hED : E ⊆ S.product (S.opposite P) D) :
    gate S F D ⊆ S.product P (gate S F E) ∧
      gate S F E ⊆ S.product (S.opposite P) (gate S F D) := by
  refine ⟨gate_bilateral_left S C hF hJ hV hD hE hP hDE hED, ?_⟩
  apply gate_bilateral_left S C hF hJ hV hE hD (C.opposite hP) hED
  simpa only [S.opposite_opposite] using hDE

/-- C15 right-factor version, obtained by actual typed converse. -/
theorem gate_bilateral_right (C : ExactCalculus S) {F J : Family S}
    (hF : FilterFamily S F) (hJ : CurrentFamily S J) (hV : Visible S F J)
    {D : S.Menu i j} {E : S.Menu i k} {P : S.Menu k j}
    (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J)
    (hE : (⟨i,k,E⟩ : TaggedMenu S) ∈ J) (hP : StrongExact.Exact S P)
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

end CCO.Selectors
