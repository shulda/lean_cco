import CCO.OrbitalCover.Example.Homogeneity
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

namespace CCO.OrbitalCover.Example

abbrev TaggedPoint := Sigma (fun _ : Unit => Point)
def tag (x : Point) : TaggedPoint := ⟨(),x⟩
@[simp] theorem tag_val (p : TaggedPoint) : tag p.2 = p := by
  rcases p with ⟨i,p⟩; cases i; rfl

@[simp] theorem tagged_colour_eq (p q r s : TaggedPoint) :
    taggedColour source p q = taggedColour source r s ↔ colour p.2 q.2 = colour r.2 s.2 := by
  rcases p with ⟨i,p⟩; rcases q with ⟨j,q⟩
  rcases r with ⟨k,r⟩; rcases s with ⟨l,s⟩
  cases i; cases j; cases k; cases l
  simp only [taggedColour, source_colour, Sigma.mk.injEq, heq_eq_eq, true_and]
  constructor
  · exact fun h => congrArg (fun z : Σ _ : Unit, Option Colour => z.2) h
  · exact fun h => congrArg (fun c : Option Colour => (⟨(),c⟩ : Σ _ : Unit, Option Colour)) h

noncomputable def points (A : FiniteInduced (X := fun _ : Unit => Point)) : Finset Point :=
  A.finite_vertices.toFinset.image Sigma.snd

@[simp] theorem mem_points (A : FiniteInduced (X := fun _ : Unit => Point)) (x : Point) :
    x ∈ points A ↔ tag x ∈ A.vertices := by
  classical
  simp only [points, Finset.mem_image, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨p,hp,rfl⟩; simpa only [tag_val] using hp
  · intro h; exact ⟨tag x,h,rfl⟩

noncomputable def indexBound (B C : Finset Point) : ℕ := (B ∪ C).sup Point.n + 1

theorem index_lt_bound {B C : Finset Point} {x : Point} (hx : x ∈ B ∪ C) :
    x.n < indexBound B C := Nat.lt_succ_of_le (Finset.le_sup hx)

noncomputable def freshen (B C : Finset Point) (x : Point) : Point := by
  classical
  exact if x ∈ C then x else { x with n := indexBound B C + x.n }

@[simp] theorem freshen_fixed {B C : Finset Point} {x : Point} (hx : x ∈ C) :
    freshen B C x = x := by
  classical
  simp [freshen,hx]
@[simp] theorem freshen_owner (B C : Finset Point) (x : Point) :
    owner (freshen B C x) = owner x := by
  classical
  unfold freshen
  split_ifs <;> rfl
@[simp] theorem freshen_p (B C : Finset Point) (x : Point) :
    (freshen B C x).p = x.p := congrArg (fun a : Owner => a.1.2) (freshen_owner B C x)
@[simp] theorem freshen_q (B C : Finset Point) (x : Point) :
    (freshen B C x).q = x.q := congrArg (fun a : Owner => a.2.2) (freshen_owner B C x)

theorem freshen_n {B C : Finset Point} {x : Point} (hx : x ∉ C) :
    (freshen B C x).n = indexBound B C + x.n := by
  classical
  simp [freshen,hx]

theorem freshen_injective (B C : Finset Point) : Function.Injective (freshen B C) := by
  classical
  intro x y h
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
  · simpa only [freshen_fixed hx, freshen_fixed hy] using h
  · have hi := congrArg Point.n h
    rw [freshen_fixed hx, freshen_n hy] at hi
    have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_right B hx)
    omega
  · have hi := congrArg Point.n h
    rw [freshen_n hx, freshen_fixed hy] at hi
    have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_right B hy)
    omega
  · apply pointEquiv.injective
    have ho := congrArg owner h
    simp only [freshen_owner] at ho
    have hn := congrArg Point.n h
    rw [freshen_n hx, freshen_n hy] at hn
    exact Prod.ext ho (Nat.add_left_cancel hn)

theorem pattern_of_owner {x y x' y' : Point} (hx : owner x = owner x')
    (hy : owner y = owner y') : pattern x y = pattern x' y' := by
  have hu := congrArg (fun a : Owner => a.1.1) hx
  have hp := congrArg (fun a : Owner => a.1.2) hx
  have hv := congrArg (fun a : Owner => a.2.1) hx
  have hq := congrArg (fun a : Owner => a.2.2) hx
  have hu' := congrArg (fun a : Owner => a.1.1) hy
  have hp' := congrArg (fun a : Owner => a.1.2) hy
  have hv' := congrArg (fun a : Owner => a.2.1) hy
  have hq' := congrArg (fun a : Owner => a.2.2) hy
  dsimp only [owner] at hu hp hv hq hu' hp' hv' hq'
  simp only [pattern, hu, hp, hv, hq, hu', hp', hv', hq']

theorem freshen_colour (B C : Finset Point) (x y : Point) :
    colour (freshen B C x) (freshen B C y) = colour x y := by
  unfold colour
  simp only [(freshen_injective B C).eq_iff,
    pattern_of_owner (freshen_owner B C x) (freshen_owner B C y)]

theorem freshen_mem_right {B C : Finset Point} {x : Point}
    (h : freshen B C x ∈ B) : x ∈ C := by
  classical
  by_contra hx
  have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_left C h)
  rw [freshen_n hx] at hl
  omega

/-- Strong amalgamation in the actual infinite source, using ordinary
homogeneous alignment followed by fresh original clone indices. -/
theorem strongAmalgamation : AgeSAP source where
  strong_amalgamate := by
    classical
    intro C A B eCA eCB
    letI : Finite ↥C.vertices := C.finite_vertices.to_subtype
    letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
    letI : Fintype ↥C.vertices := Fintype.ofFinite _
    have hc : ∀ c d : ↥C.vertices,
        colour (eCA.toEmbedding c).val.2 (eCA.toEmbedding d).val.2 =
          colour (eCB.toEmbedding c).val.2 (eCB.toEmbedding d).val.2 := by
      intro c d
      exact (tagged_colour_eq _ _ _ _).mp
        ((eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d))
    obtain ⟨g,hg⟩ := finite_extension
      (fun c : ↥C.vertices => (eCA.toEmbedding c).val.2)
      (fun c => (eCB.toEmbedding c).val.2) hc
    let base : Finset Point := Finset.univ.image (fun c : ↥C.vertices => (eCB.toEmbedding c).val.2)
    let move (x : Point) := freshen (points B) base (g • x)
    have hmove : Function.Injective move := (freshen_injective _ _).comp (MulAction.injective g)
    have hbase (c : ↥C.vertices) : move (eCA.toEmbedding c).val.2 =
        (eCB.toEmbedding c).val.2 := by
      dsimp only [move]
      rw [hg c, freshen_fixed (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,rfl⟩)]
    let fa : ↥A.vertices → TaggedPoint := fun a => tag (move a.val.2)
    let D : FiniteInduced (X := fun _ : Unit => Point) :=
      ⟨Set.range fa ∪ B.vertices, (Set.finite_range fa).union B.finite_vertices⟩
    let eAD : InducedEmbedding source A D := {
      toEmbedding := {
        toFun := fun a => ⟨fa a,Or.inl ⟨a,rfl⟩⟩
        inj' := by
          intro a b h
          have hv := congrArg (fun p : ↥D.vertices => p.val.2) h
          apply Subtype.ext
          exact (tag_val a.val).symm.trans ((congrArg tag (hmove hv)).trans (tag_val b.val)) }
      preserves_sort := by intro a; exact Subsingleton.elim _ _
      preserves_colours := by
        intro a b
        apply (tagged_colour_eq _ _ _ _).mpr
        exact ((freshen_colour _ _ _ _).trans (aut_colour g a.val.2 b.val.2)).symm }
    let eBD : InducedEmbedding source B D := {
      toEmbedding := {
        toFun := fun b => ⟨b.val,Or.inr b.2⟩
        inj' := by
          intro a b h
          apply Subtype.ext
          exact congrArg (fun p : ↥D.vertices => p.val) h }
      preserves_sort := by intro b; rfl
      preserves_colours := by intro a b; rfl }
    refine ⟨D,eAD,eBD,?_,?_⟩
    · intro c
      apply Subtype.ext
      exact (congrArg tag (hbase c)).trans (tag_val _)
    · intro a b hab
      have he : move a.val.2 = b.val.2 := congrArg (fun p : ↥D.vertices => p.val.2) hab
      have hb : move a.val.2 ∈ points B := by
        rw [he]
        exact (mem_points B _).mpr (by simpa only [tag_val] using b.2)
      have hc' : g • a.val.2 ∈ base := freshen_mem_right hb
      rcases Finset.mem_image.mp hc' with ⟨c,_,hc'⟩
      have hm : move a.val.2 = g • a.val.2 := freshen_fixed (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,hc'⟩)
      refine ⟨c,?_,?_⟩
      · apply Subtype.ext
        have hh : g • (eCA.toEmbedding c).val.2 = g • a.val.2 := (hg c).trans hc'
        exact (tag_val _).symm.trans ((congrArg tag (MulAction.injective g hh)).trans (tag_val _))
      · apply Subtype.ext
        exact (tag_val _).symm.trans ((congrArg tag (hc'.trans (hm.symm.trans he))).trans (tag_val _))

end CCO.OrbitalCover.Example
