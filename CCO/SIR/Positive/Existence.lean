import CCO.SIR.Positive.SelectedAmalgam
import CCO.SIR.Positive.Stationarity
import CCO.SIR.Positive.DisjointCopy

universe u v w t
namespace CCO.SIR.Positive
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable [DecidableEq (Sigma X)]

/-- Each old left factor, including its whole base, is untouched. -/
theorem freeMenu_old_left (A C : Finset (Sigma X)) {x y : Sigma X}
    (hx : x ∈ A ∪ C) (hy : y ∈ A ∪ C) : freeMenu S A C x y = edgeMenu S x y := by
  unfold freeMenu spanSide
  split_ifs <;> simp_all [crossSide]

/-- The same is true of the right factor, using the literal overlap. -/
theorem freeMenu_old_right (A B C : Finset (Sigma X))
    (ho : ∀ x ∈ A, x ∈ B → x ∈ C) {x y : Sigma X}
    (hx : x ∈ B ∪ C) (hy : y ∈ B ∪ C) : freeMenu S A C x y = edgeMenu S x y := by
  have hleft : ∀ z ∈ B ∪ C, z ∉ C → z ∉ A := by
    intro z hz hzc hzA
    exact hzc (ho z hzA ((Finset.mem_union.mp hz).resolve_right hzc))
  unfold freeMenu spanSide
  split_ifs <;> simp_all [crossSide]

theorem freeMenu_cross (A B C : Finset (Sigma X))
    (ho : ∀ x ∈ A, x ∈ B → x ∈ C) {x y : Sigma X}
    (hx : x ∈ A) (hy : y ∈ B) (hxC : x ∉ C) (hyC : y ∉ C) :
    freeMenu S A C x y = baseMenu S C x y := by
  have hyA : y ∉ A := fun he => hyC (ho y he hy)
  simp [freeMenu,spanSide,hx,hyA,hxC,hyC,crossSide]

section Action
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]

/-- C06 for an already disjoint actual span. The selected structure is
realized, then its entire B∪C copy is aligned with the prescribed real one. -/
theorem independent_exists_disjoint (H : HomogeneousSource S G)
    (K : Selectors.ExactCalculus S) (h : Selectors.HereditarySelector S)
    (fullness : TriangleFullness S) (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A B C : Finset (Sigma X)) (ho : ∀ x ∈ A, x ∈ B → x ∈ C) :
    ∃ g : G, (∀ c ∈ C, g • c = c) ∧ Independent S h (transport g A) C B := by
  let F := A ∪ (B ∪ C)
  obtain ⟨f,hf,hs,hcol⟩ := selected_realization S K h fullness hPoint hEdge A C F
  let incA : ↥(A ∪ C) → ↥F := fun x => ⟨x.val,by
    rcases Finset.mem_union.mp x.property with ha | hc
    · exact Finset.mem_union_left (B ∪ C) ha
    · exact Finset.mem_union_right A (Finset.mem_union_right B hc)⟩
  let incB : ↥(B ∪ C) → ↥F := fun x => ⟨x.val,Finset.mem_union_right A x.property⟩
  have hAcol : ∀ x y : ↥(A ∪ C), taggedColour S x.val y.val =
      taggedColour S (f (incA x)) (f (incA y)) := by
    intro x y
    rw [hcol]
    exact (selectedColour_old_pair S K h A C x.val y.val
      (freeMenu_old_left S A C x.property y.property)).symm
  have hBcol : ∀ x y : ↥(B ∪ C), taggedColour S x.val y.val =
      taggedColour S (f (incB x)) (f (incB y)) := by
    intro x y
    rw [hcol]
    exact (selectedColour_old_pair S K h A C x.val y.val
      (freeMenu_old_right S A B C ho x.property y.property)).symm
  obtain ⟨ga,hga⟩ := H.extends_finite_diagram (fun x : ↥(A ∪ C) => x.val) (fun x => f (incA x)) hAcol
  obtain ⟨gb,hgb⟩ := H.extends_finite_diagram (fun x : ↥(B ∪ C) => x.val) (fun x => f (incB x)) hBcol
  let g := gb⁻¹ * ga
  have hcAgree : ∀ c ∈ C, ga • c = gb • c := by
    intro c hc
    exact (hga ⟨c,Finset.mem_union_right A hc⟩).trans (hgb ⟨c,Finset.mem_union_right B hc⟩).symm
  have hgfix : ∀ c ∈ C, g • c = c := by
    intro c hc
    simp only [g,mul_smul,hcAgree c hc,inv_smul_smul]
  refine ⟨g,hgfix,?_,?_⟩
  · intro x hx hb
    obtain ⟨a,ha,rfl⟩ := (mem_transport g A x).mp hx
    have hsame : f (incA ⟨a,Finset.mem_union_left C ha⟩) =
        f (incB ⟨g • a,Finset.mem_union_left C hb⟩) := by
      rw [←hga,←hgb]
      simp [g,mul_smul,smul_inv_smul]
    have he : a = g • a := congrArg Subtype.val (hf hsame)
    exact ho (g • a) (he ▸ ha) hb
  · intro x hx b hb hxC hbC
    obtain ⟨a,ha,rfl⟩ := (mem_transport g A x).mp hx
    have haC : a ∉ C := by
      intro he
      apply hxC
      simpa only [hgfix a he] using he
    have hab : a ≠ b := by intro he; subst b; exact hbC (ho a ha hb)
    have hfree := freeMenu_cross S A B C ho ha hb haC hbC
    have hD := baseMenu_exact S K C haC hbC hab
    have hChosen : selectedColour S K h A C a b =
        ⟨a.1,b.1,some (h.choose (baseMenu S C a b) hD)⟩ := by
      simp only [selectedColour,dite_eq_right hab,selectedAtom]
      congr 3
      congr 1
    have hcross : taggedColour S (g • a) b = selectedColour S K h A C a b := by
      have hc := hcol (incA ⟨a,Finset.mem_union_left C ha⟩) (incB ⟨b,Finset.mem_union_left C hb⟩)
      rw [←hga,←hgb] at hc
      have hact := H.preserves_colours gb⁻¹ (ga • a) (gb • b)
      simp only [inv_smul_smul] at hact
      simpa only [g,mul_smul,incA,incB] using hact.trans hc
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    have hcol' : S.colour (g • a) b = some (h.choose (baseMenu S C ⟨i,a⟩ ⟨j,b⟩) hD) := by
      rw [hChosen] at hcross
      simpa only [taggedColour,Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and] using hcross
    have hm := baseMenu_fixed_left S H g C hgfix a b
    change SelectedPair S h C ⟨i,g • a⟩ ⟨j,b⟩
    have hD' : StrongExact.Exact S (baseMenu S C ⟨i,g • a⟩ ⟨j,b⟩) := hm ▸ hD
    refine ⟨hD',?_⟩
    have hch : h.choose (baseMenu S C ⟨i,g • a⟩ ⟨j,b⟩) hD' =
        h.choose (baseMenu S C ⟨i,a⟩ ⟨j,b⟩) hD := by congr 1
    rw [hch]
    exact hcol'

/-- C06 including arbitrary old overlaps and empty bases. SAP is used
only for the preliminary genuinely disjoint copy, never to choose output colours. -/
theorem independent_exists (H : HomogeneousSource S G) (sap : AgeSAP S)
    (K : Selectors.ExactCalculus S) (h : Selectors.HereditarySelector S)
    (fullness : TriangleFullness S) (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A B C : Finset (Sigma X)) :
    ∃ g : G, (∀ c ∈ C, g • c = c) ∧ Independent S h (transport g A) C B := by
  obtain ⟨g₀,hfix₀,hdis⟩ := disjoint_copy_over H sap A B C
  have ho : ∀ x ∈ transport g₀ A, x ∈ B → x ∈ C := by
    intro x hx hb
    obtain ⟨a,ha,rfl⟩ := (mem_transport g₀ A x).mp hx
    exact hdis a ha (g₀ • a) hb rfl
  obtain ⟨g₁,hfix₁,hI⟩ := independent_exists_disjoint S H K h fullness hPoint hEdge (transport g₀ A) B C ho
  have htrans : transport (g₁ * g₀) A = transport g₁ (transport g₀ A) := by
    ext x
    simp only [mem_transport,mul_smul]
    constructor
    · rintro ⟨a,ha,hx⟩
      exact ⟨g₀ • a,⟨a,ha,rfl⟩,hx⟩
    · rintro ⟨b,⟨a,ha,rfl⟩,hx⟩
      exact ⟨a,ha,hx⟩
  refine ⟨g₁ * g₀,?_,?_⟩
  · intro c hc
    rw [mul_smul,hfix₀ c hc,hfix₁ c hc]
  · rwa [htrans]

end Action
end CCO.SIR.Positive
