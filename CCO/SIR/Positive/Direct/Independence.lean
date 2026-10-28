import CCO.SIR.Positive.Direct.Fresh

namespace CCO.SIR.Positive.Direct

@[simp] theorem aut_F (g : Aut) (x y : Point) : F (g • x) (g • y) ↔ F x y :=
  (coordinates_of_colour_eq (aut_colour g x y)).2.1
@[simp] theorem aut_E (g : Aut) (x y : Point) : E (g • x) (g • y) ↔ E x y :=
  (coordinates_of_colour_eq (aut_colour g x y)).2.2

theorem independent_normalization (A B C : Finset Point) :
    Independent (A ∪ C) C (B ∪ C) ↔ Independent A C B := by
  constructor
  · intro h
    exact ⟨fun x ha hb => h.1 x (Finset.mem_union_left C ha)
      (Finset.mem_union_left C hb),fun a ha hac b hb hbc hab =>
      h.2 a (Finset.mem_union_left C ha) hac b (Finset.mem_union_left C hb) hbc hab⟩
  · intro h
    constructor
    · intro x hx hy
      rcases Finset.mem_union.mp hx with ha | hc
      · rcases Finset.mem_union.mp hy with hb | hc
        · exact h.1 x ha hb
        · exact hc
      · exact hc
    · intro a ha hac b hb hbc hab
      exact h.2 a ((Finset.mem_union.mp ha).resolve_right hac) hac b
        ((Finset.mem_union.mp hb).resolve_right hbc) hbc hab

theorem independent_symmetry {A B C : Finset Point} (h : Independent A C B) :
    Independent B C A := by
  refine ⟨fun x hb ha => h.1 x ha hb,?_⟩
  intro b hb hbc a ha hac hba
  have hh := h.2 a ha hac b hb hbc hba.symm
  exact hba.symm ▸ hh

theorem independent_restriction {A B C A' B' : Finset Point}
    (hA : A' ⊆ A) (hB : B' ⊆ B) (h : Independent A C B) :
    Independent A' C B' :=
  ⟨fun x ha hb => h.1 x (hA ha) (hB hb),
    fun a ha hac b hb hbc hab => h.2 a (hA ha) hac b (hB hb) hbc hab⟩

theorem independent_transport {A B C : Finset Point} (g : Aut)
    (h : Independent A C B) :
    Independent (transport g A) (transport g C) (transport g B) := by
  constructor
  · intro x hx hb
    rcases (mem_transport g A x).mp hx with ⟨a,ha,rfl⟩
    have hab : a ∈ B := (smul_mem_transport g B a).mp hb
    exact (smul_mem_transport g C a).mpr (h.1 a ha hab)
  · intro x hx hxc y hy hyc hxy
    rcases (mem_transport g A x).mp hx with ⟨a,ha,rfl⟩
    rcases (mem_transport g B y).mp hy with ⟨b,hb,rfl⟩
    have hac : a ∉ C := fun hc => hxc ((smul_mem_transport g C a).mpr hc)
    have hbc : b ∉ C := fun hc => hyc ((smul_mem_transport g C b).mpr hc)
    rcases h.2 a ha hac b hb hbc ((aut_F g a b).mp hxy) with ⟨c,hc,hp⟩
    refine ⟨g • c,(smul_mem_transport g C c).mpr hc,?_⟩
    exact (aut_F g c a).mpr hp

theorem independent_invariance (g : Aut) (A B C : Finset Point) :
    Independent (transport g A) (transport g C) (transport g B) ↔ Independent A C B := by
  constructor
  · intro h
    simpa only [transport_inv] using independent_transport g⁻¹ h
  · exact independent_transport g

theorem independent_transitivity (A B C D : Finset Point) :
    Independent A C (B ∪ D) ↔ Independent A C B ∧ Independent A (B ∪ C) D := by
  constructor
  · intro h
    constructor
    · exact independent_restriction (fun _ h => h) (fun _ hb => Finset.mem_union_left D hb) h
    · constructor
      · intro x ha hd
        exact Finset.mem_union_right B (h.1 x ha (Finset.mem_union_right B hd))
      · intro a ha hac d hd hdc had
        have hac' : a ∉ C := fun hc => hac (Finset.mem_union_right B hc)
        have hdc' : d ∉ C := fun hc => hdc (Finset.mem_union_right B hc)
        rcases h.2 a ha hac' d (Finset.mem_union_right B hd) hdc' had with ⟨c,hc,hp⟩
        exact ⟨c,Finset.mem_union_right B hc,hp⟩
  · rintro ⟨hAB,hAD⟩
    constructor
    · intro x ha hbd
      rcases Finset.mem_union.mp hbd with hb | hd
      · exact hAB.1 x ha hb
      · rcases Finset.mem_union.mp (hAD.1 x ha hd) with hb | hc
        · exact hAB.1 x ha hb
        · exact hc
    · intro a ha hac d hbd hdc had
      rcases Finset.mem_union.mp hbd with hb | hd
      · exact hAB.2 a ha hac d hb hdc had
      · by_cases hanchor : Anchored C (parent a)
        · exact hanchor
        · have haB : a ∉ B := fun hb => hac (hAB.1 a ha hb)
          have hdB : d ∉ B := by
            intro hb
            exact hanchor (hAB.2 a ha hac d hb hdc had)
          rcases hAD.2 a ha (by simpa using And.intro haB hac) d hd
            (by simpa using And.intro hdB hdc) had with ⟨c,hc,hp⟩
          rcases Finset.mem_union.mp hc with hcB | hcC
          · exact hAB.2 a ha hac c hcB (by
              intro hcC
              exact hanchor ⟨c,hcC,hp⟩) hp.symm
          · exact ⟨c,hcC,hp⟩

/-- The elementary TWO-SHEET fact includes the both-false case. -/
theorem bool_comparison (a b c : Bool) : (a = b) ↔ ((a = c) ↔ (b = c)) := by
  cases a <;> cases b <;> cases c <;> decide

theorem fixed_base_mem (g : Aut) (C : Finset Point) (hg : ∀ c ∈ C, g • c = c)
    (x : Point) : g • x ∈ C ↔ x ∈ C := by
  constructor
  · intro hx
    have hf := hg (g • x) hx
    have he : g • x = x := MulAction.injective g hf
    exact he ▸ hx
  · intro hx
    exact (hg x hx).symm ▸ hx

/-- All cross atoms are determined by the two pointwise types over the
real base. In an anchored parent the two Boolean comparisons determine
the relative sheet, including when BOTH comparisons are false. -/
theorem cross_colour {A B C : Finset Point} (g : Aut)
    (hg : ∀ c ∈ C, g • c = c)
    (hA : Independent A C B) (hG : Independent (transport g A) C B)
    {a b : Point} (ha : a ∈ A) (hb : b ∈ B ∪ C) :
    colour (g • a) b = colour a b := by
  classical
  by_cases hac : a ∈ C
  · rw [hg a hac]
  rcases Finset.mem_union.mp hb with hb | hbc
  swap
  · simpa only [hg b hbc] using aut_colour g a b
  by_cases hbc : b ∈ C
  · simpa only [hg b hbc] using aut_colour g a b
  have hgac : g • a ∉ C := fun hc => hac ((fixed_base_mem g C hg a).mp hc)
  have hne : a ≠ b := fun he => hac (hA.1 a ha (he ▸ hb))
  have hgne : g • a ≠ b := fun he => hgac (hG.1 (g • a)
    ((smul_mem_transport g A a).mpr ha) (he ▸ hb))
  have hparent : F (g • a) b ↔ F a b := by
    constructor
    · intro hF
      rcases hG.2 (g • a) ((smul_mem_transport g A a).mpr ha) hgac b hb hbc hF with ⟨c,hc,hcF⟩
      have hacF : F a c := (aut_F g a c).mp (by
        change parent (g • a) = parent (g • c)
        rw [hg c hc]
        exact hcF.symm)
      exact hacF.trans (hcF.trans hF)
    · intro hF
      rcases hA.2 a ha hac b hb hbc hF with ⟨c,hc,hcF⟩
      have hgacF : F (g • a) c := by simpa only [hg c hc] using (aut_F g a c).mpr hcF.symm
      exact hgacF.trans (hcF.trans hF)
  unfold colour
  simp only [hne,hgne,↓reduceIte]
  by_cases hF : F a b
  · have hgF := hparent.mpr hF
    rcases hA.2 a ha hac b hb hbc hF with ⟨c,hc,hcF⟩
    have hacF : F a c := hcF.symm
    have hgacF : F (g • a) c := by simpa only [hg c hc] using (aut_F g a c).mpr hacF
    have hbE : (sheet (g • a) = sheet c) ↔ (sheet a = sheet c) := by
      have hh := aut_E g a c
      simpa only [hg c hc,E,hacF,hgacF,true_and] using hh
    have hsheet : (sheet (g • a) = sheet b) ↔ (sheet a = sheet b) := by
      rw [bool_comparison _ _ (sheet c),bool_comparison (sheet a) _ (sheet c),hbE]
    simp only [hF,hgF,↓reduceIte,hsheet]
  · simp only [hF,show ¬ F (g • a) b from fun h => hF (hparent.mp h),↓reduceIte]

/-- Every prescribed real partial isomorphism is extended while every
member of B∪C is fixed individually. -/
theorem independent_stationarity (A B C : Finset Point) (g : Aut)
    (hg : ∀ c ∈ C, g • c = c)
    (hA : Independent A C B) (hG : Independent (transport g A) C B) :
    ∃ h : Aut, (∀ b ∈ B ∪ C, h • b = b) ∧ ∀ a ∈ A, h • a = g • a := by
  classical
  let T := A ∪ (B ∪ C)
  let u : Point → Point := fun x => if x ∈ A then g • x else x
  have huA {x : Point} (hx : x ∈ A) : u x = g • x := by simp [u,hx]
  have huB {x : Point} (hx : x ∈ B ∪ C) : u x = x := by
    by_cases ha : x ∈ A
    · have hc : x ∈ C := by
        rcases Finset.mem_union.mp hx with hb | hc
        · exact hA.1 x ha hb
        · exact hc
      simp [u,ha,hg x hc]
    · simp [u,ha]
  have huc : ∀ x y : ↥T, colour x.val y.val = colour (u x) (u y) := by
    intro x y
    by_cases ha : x.val ∈ A <;> by_cases hb : y.val ∈ A
    · rw [huA ha,huA hb,aut_colour]
    · have hy : y.val ∈ B ∪ C := (Finset.mem_union.mp y.2).resolve_left hb
      rw [huA ha,huB hy]
      exact (cross_colour g hg hA hG ha hy).symm
    · have hx : x.val ∈ B ∪ C := (Finset.mem_union.mp x.2).resolve_left ha
      rw [huB hx,huA hb,colour_symm x.val (g • y.val),colour_symm x.val y.val]
      exact (cross_colour g hg hA hG hb hx).symm
    · have hx : x.val ∈ B ∪ C := (Finset.mem_union.mp x.2).resolve_left ha
      have hy : y.val ∈ B ∪ C := (Finset.mem_union.mp y.2).resolve_left hb
      rw [huB hx,huB hy]
  obtain ⟨h,hh⟩ := finite_extension (fun x : ↥T => x.val) (fun x => u x) huc
  refine ⟨h,fun b hb => ?_,fun a ha => ?_⟩
  · exact (hh ⟨b,Finset.mem_union_right A hb⟩).trans (huB hb)
  · exact (hh ⟨a,Finset.mem_union_left (B ∪ C) ha⟩).trans (huA ha)

/-- The DIRECT SIR is independent of HS, NR2 and CCO. -/
theorem stationaryIndependence : StationaryIndependence (G := Aut) Independent where
  normalization := independent_normalization
  invariance := independent_invariance
  symmetry := fun _ _ _ => ⟨independent_symmetry,independent_symmetry⟩
  restriction := fun _ _ _ _ _ => independent_restriction
  transitivity := independent_transitivity
  existence := independent_existence
  stationarity := independent_stationarity

end CCO.SIR.Positive.Direct
