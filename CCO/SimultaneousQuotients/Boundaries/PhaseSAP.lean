import CCO.SimultaneousQuotients.Boundaries.PhaseSource

/-! Actual strong amalgamation for the infinite phase clones. Align the
displayed common base by homogeneity, retain that base, and move every other
clone index beyond all points of the fixed right side. -/
namespace CCO.SimultaneousQuotients.Boundaries.Phase
variable (I : Type) [Fintype I] [DecidableEq I]

noncomputable def bound (B C : Finset (Tagged I)) : ℕ := (B ∪ C).sup (taggedIndex I) + 1

theorem index_lt_bound {B C : Finset (Tagged I)} {x : Tagged I} (h : x ∈ B ∪ C) :
    taggedIndex I x < bound I B C := Nat.lt_succ_of_le (Finset.le_sup h)

noncomputable def freshen (B C : Finset (Tagged I)) (x : Tagged I) : Tagged I :=
  if x ∈ C then x else ⟨x.1,⟨taggedPhase I x,bound I B C + taggedIndex I x⟩⟩

@[simp] theorem freshen_fixed {B C : Finset (Tagged I)} {x : Tagged I} (h : x ∈ C) :
    freshen I B C x = x := by
  classical
  simp [freshen,h]

@[simp] theorem freshen_sort (B C : Finset (Tagged I)) (x : Tagged I) :
    (freshen I B C x).1 = x.1 := by
  classical
  unfold freshen
  split_ifs <;> rfl

@[simp] theorem freshen_phase (B C : Finset (Tagged I)) (x : Tagged I) :
    taggedPhase I (freshen I B C x) = taggedPhase I x := by
  classical
  unfold freshen
  split_ifs <;> rfl

theorem freshen_index {B C : Finset (Tagged I)} {x : Tagged I} (h : x ∉ C) :
    taggedIndex I (freshen I B C x) = bound I B C + taggedIndex I x := by
  unfold freshen
  split_ifs <;> simp_all [taggedIndex]

theorem freshen_injective (B C : Finset (Tagged I)) : Function.Injective (freshen I B C) := by
  classical
  intro x y h
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
  · simpa only [freshen_fixed I hx,freshen_fixed I hy] using h
  · have hi := congrArg (taggedIndex I) h
    rw [freshen_fixed I hx,freshen_index I hy] at hi
    have hl := index_lt_bound I (B := B) (C := C) (Finset.mem_union_right B hx)
    omega
  · have hi := congrArg (taggedIndex I) h
    rw [freshen_index I hx,freshen_fixed I hy] at hi
    have hl := index_lt_bound I (B := B) (C := C) (Finset.mem_union_right B hy)
    omega
  · apply tagged_ext I x y
    · simpa only [freshen_sort] using congrArg Sigma.fst h
    · simpa only [freshen_phase] using congrArg (taggedPhase I) h
    · have hi := congrArg (taggedIndex I) h
      rw [freshen_index I hx,freshen_index I hy] at hi
      exact Nat.add_left_cancel hi

theorem freshen_colour (B C : Finset (Tagged I)) (x y : Tagged I) :
    taggedColour (source I) (freshen I B C x) (freshen I B C y) =
      taggedColour (source I) x y := by
  have hc : colour I (freshen I B C x).2 (freshen I B C y).2 = colour I x.2 y.2 := by
    have hpx : (freshen I B C x).2.phase = x.2.phase := freshen_phase I B C x
    have hpy : (freshen I B C y).2.phase = y.2.phase := freshen_phase I B C y
    unfold colour
    simp only [Sigma.eta, (freshen_injective I B C).eq_iff,hpx,hpy]
  exact (congrArg (fun c : Option Bool =>
    (⟨(freshen I B C x).1,(freshen I B C y).1,c⟩ : Σ _ : I, Σ _ : I, Option Bool)) hc).trans
      (by simp only [freshen_sort]; rfl)

theorem freshen_mem_right {B C : Finset (Tagged I)} {x : Tagged I}
    (h : freshen I B C x ∈ B) : x ∈ C := by
  classical
  by_contra hx
  have hl := index_lt_bound I (B := B) (C := C) (Finset.mem_union_left C h)
  rw [freshen_index I hx] at hl
  omega

theorem strongAmalgamation : AgeSAP (source I) where
  strong_amalgamate := by
    classical
    intro C A B eCA eCB
    letI : Finite ↥C.vertices := C.finite_vertices.to_subtype
    letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
    letI : Fintype ↥C.vertices := Fintype.ofFinite _
    have hcol := fun c d => (eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d)
    obtain ⟨g,hg⟩ := finite_extension I
      (fun c : ↥C.vertices => (eCA.toEmbedding c).val)
      (fun c => (eCB.toEmbedding c).val) hcol
    let base : Finset (Tagged I) := Finset.univ.image (fun c : ↥C.vertices => (eCB.toEmbedding c).val)
    let right : Finset (Tagged I) := B.finite_vertices.toFinset
    let fa : ↥A.vertices → Tagged I := fun a => freshen I right base (g • a.val)
    have hbase (c : ↥C.vertices) : fa (eCA.toEmbedding c) = (eCB.toEmbedding c).val := by
      change freshen I right base (g • (eCA.toEmbedding c).val) = _
      rw [hg c]
      exact freshen_fixed I (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,rfl⟩)
    let D : FiniteInduced (X := Point I) :=
      ⟨Set.range fa ∪ B.vertices,(Set.finite_range fa).union B.finite_vertices⟩
    let eAD : InducedEmbedding (source I) A D := {
      toEmbedding := {
        toFun := fun a => ⟨fa a,Or.inl ⟨a,rfl⟩⟩
        inj' := by
          intro a b h
          have hh := freshen_injective I right base (congrArg (fun p : ↥D.vertices => p.val) h)
          exact Subtype.ext (MulAction.injective g hh) }
      preserves_sort := by
        intro a
        exact (freshen_sort I right base _).trans ((homogeneous I).preserves_sort g a.val)
      preserves_colours := by
        intro a b
        exact ((freshen_colour I right base _ _).trans
          ((homogeneous I).preserves_colours g a.val b.val)).symm }
    let eBD : InducedEmbedding (source I) B D := {
      toEmbedding := {
        toFun := fun b => ⟨b.val,Or.inr b.property⟩
        inj' := fun a b h => Subtype.ext (congrArg (fun p : ↥D.vertices => p.val) h) }
      preserves_sort := fun _ => rfl
      preserves_colours := fun _ _ => rfl }
    refine ⟨D,eAD,eBD,fun c => Subtype.ext (hbase c),?_⟩
    intro a b hab
    have he : freshen I right base (g • a.val) = b.val :=
      congrArg (fun p : ↥D.vertices => p.val) hab
    have hr : freshen I right base (g • a.val) ∈ right :=
      he.symm ▸ (Set.Finite.mem_toFinset B.finite_vertices).mpr b.property
    obtain ⟨c,_,hc⟩ := Finset.mem_image.mp (freshen_mem_right I hr)
    refine ⟨c,?_,?_⟩
    · apply Subtype.ext
      exact MulAction.injective g ((hg c).trans hc)
    · apply Subtype.ext
      have hfixed : freshen I right base (eCB.toEmbedding c).val = (eCB.toEmbedding c).val :=
        freshen_fixed I (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,rfl⟩)
      exact hfixed.symm.trans ((congrArg (freshen I right base) hc).trans he)

end CCO.SimultaneousQuotients.Boundaries.Phase
