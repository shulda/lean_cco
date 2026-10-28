import CCO.SIR.Positive.Independence

universe u v w
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]

/-- The other orientation of the two-old/one-new free-span PC triangle. -/
theorem baseMenu_right_PC (K : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (C : Finset (Sigma X)) {a b d : Sigma X}
    (ha : a ∉ C) (hb : b ∉ C) (hd : d ∉ C)
    (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) :
    S.PC (baseMenu S C a b) (edgeMenu S b d) (baseMenu S C a d) := by
  have h₀ := baseMenu_PC S K hPoint hEdge C hb hd ha hbd had.symm hab.symm
  have h₁ := (S.pc_rotate_output_first _ _ _).mp h₀
  have h₂ := (S.pc_rotate_output_second _ _ _).mp h₁
  simpa only [baseMenu_opposite,S.opposite_opposite] using h₂

/-- C09: the actual old selected atom survives every added literal
constraint. Survivor heredity is applied only after proving this fact. -/
theorem independent_forward (K : Selectors.ExactCalculus S)
    (h : Selectors.HereditarySelector S) (A B C D : Finset (Sigma X))
    (hi : Independent S h A C (B ∪ D)) :
    Independent S h A C B ∧ Independent S h A (B ∪ C) D := by
  refine ⟨independent_restriction S h (Finset.Subset.refl A) (Finset.subset_union_left) hi,?_,?_⟩
  · intro x hx hd
    exact Finset.mem_union_right B (hi.1 x hx (Finset.mem_union_right B hd))
  · intro a ha d hd hac hdc
    have haC : a ∉ C := fun he => hac (Finset.mem_union_right B he)
    have hdC : d ∉ C := fun he => hdc (Finset.mem_union_right B he)
    obtain ⟨hOld,hcol⟩ := hi.2 a ha d (Finset.mem_union_right B hd) haC hdC
    have had : a ≠ d := S.atomRel_ne hcol
    have hNew := baseMenu_exact S K (B ∪ C) hac hdc had
    have hSub : baseMenu S (B ∪ C) a d ⊆ baseMenu S C a d := by
      intro q hq c hc
      exact hq c (Finset.mem_union_right B hc)
    have hSurvive := actual_mem_baseMenu S (B ∪ C) hac hdc hcol
    have hHer := h.heredity (baseMenu S (B ∪ C) a d) (baseMenu S C a d)
      hNew hOld hSub hSurvive
    exact ⟨hNew,by rw [hHer]; exact hcol⟩

/-- C10: reverse transitivity supplies the original-base overlap before
any free-span support is invoked. -/
theorem reverse_overlap {A B C D : Finset (Sigma X)}
    (hAB : ∀ x ∈ A, x ∈ B → x ∈ C)
    (hAD : ∀ x ∈ A, x ∈ D → x ∈ B ∪ C) :
    ∀ x ∈ A, x ∈ B ∪ D → x ∈ C := by
  intro x hx hBD
  rcases Finset.mem_union.mp hBD with hb | hd
  · exact hAB x hx hb
  · exact (Finset.mem_union.mp (hAD x hx hd)).elim (hAB x hx) id

/-- C11: all-coordinate PC puts the ORIGINAL selected atom into each
new constraint; heredity then identifies it with the second hypothesis. -/
theorem independent_reverse (K : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (h : Selectors.HereditarySelector S) (A B C D : Finset (Sigma X))
    (hAB : Independent S h A C B) (hAD : Independent S h A (B ∪ C) D) :
    Independent S h A C (B ∪ D) := by
  have ho := reverse_overlap (A := A) (B := B) (C := C) (D := D) hAB.1 hAD.1
  refine ⟨ho,?_⟩
  intro a ha d hd haC hdC
  by_cases hdB : d ∈ B
  · exact hAB.2 a ha d hdB haC hdC
  · have hdD : d ∈ D := (Finset.mem_union.mp hd).resolve_left hdB
    have haB : a ∉ B := fun he => haC (hAB.1 a ha he)
    have haBC : a ∉ B ∪ C := by simpa using And.intro haB haC
    have hdBC : d ∉ B ∪ C := by simpa using And.intro hdB hdC
    have had : a ≠ d := by intro he; subst d; exact haC (ho a ha hd)
    let hOld := baseMenu_exact S K C haC hdC had
    let q := h.choose (baseMenu S C a d) hOld
    have hOldMem : q ∈ baseMenu S C a d := h.member _ hOld
    have hNewMem : q ∈ baseMenu S (B ∪ C) a d := by
      intro b hb
      rcases Finset.mem_union.mp hb with hbB | hbC
      · by_cases hbC : b ∈ C
        · exact hOldMem b hbC
        · have hab : a ≠ b := by intro he; subst b; exact haB hbB
          have hbd : b ≠ d := by intro he; subst d; exact hdB hbB
          obtain ⟨hLeft,hLeftCol⟩ := hAB.2 a ha b hbB haC hbC
          obtain ⟨p,hp⟩ := S.some_colour_of_ne b.2 d.2 hbd
          have hMid : StrongExact.Exact S (edgeMenu S b d) := by
            rw [edgeMenu_of_colour S hp]
            exact StrongExact.exact_singleton S p
          have hPC := baseMenu_right_PC S K hPoint hEdge C haC hbC hdC hab hbd had
          have hTri := h.triangle S (baseMenu S C a b) (edgeMenu S b d)
            (baseMenu S C a d) hLeft hMid hOld hPC
          have hMidCol : S.colour b.2 d.2 = some (h.choose (edgeMenu S b d) hMid) :=
            h.member (edgeMenu S b d) hMid
          exact ⟨h.choose _ hLeft,hLeftCol,h.choose _ hMid,hMidCol,hTri⟩
      · exact hOldMem b hbC
    let hNew := baseMenu_exact S K (B ∪ C) haBC hdBC had
    have hSub : baseMenu S (B ∪ C) a d ⊆ baseMenu S C a d := by
      intro r hr c hc
      exact hr c (Finset.mem_union_right B hc)
    have hHer : h.choose (baseMenu S (B ∪ C) a d) hNew = q :=
      h.heredity _ _ hNew hOld hSub hNewMem
    obtain ⟨hActual,hCol⟩ := hAD.2 a ha d hdD haBC hdBC
    refine ⟨hOld,?_⟩
    change S.colour a.2 d.2 = some q
    rw [←hHer]
    exact hCol

theorem independent_transitivity (K : Selectors.ExactCalculus S)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (h : Selectors.HereditarySelector S) (A B C D : Finset (Sigma X)) :
    Independent S h A C (B ∪ D) ↔
      Independent S h A C B ∧ Independent S h A (B ∪ C) D :=
  ⟨independent_forward S K h A B C D,
    fun hh => independent_reverse S K hPoint hEdge h A B C D hh.1 hh.2⟩

end CCO.SIR.Positive
