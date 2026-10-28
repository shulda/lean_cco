import CCO.SIR.Positive.Direct.Independence

namespace CCO.SIR.Positive.Direct

abbrev TaggedPoint := Sigma (fun _ : Unit => Point)
def tag (x : Point) : TaggedPoint := ⟨(),x⟩

@[simp] theorem tag_val (p : TaggedPoint) : tag p.2 = p := by
  rcases p with ⟨i,p⟩; cases i; rfl
@[simp] theorem tag_injective : Function.Injective tag := by
  intro x y h
  exact congrArg Sigma.snd h

@[simp] theorem tagged_colour_eq (p q r s : TaggedPoint) :
    taggedColour source p q = taggedColour source r s ↔ colour p.2 q.2 = colour r.2 s.2 := by
  rcases p with ⟨i,p⟩; rcases q with ⟨j,q⟩
  rcases r with ⟨k,r⟩; rcases s with ⟨l,s⟩
  cases i; cases j; cases k; cases l
  simp only [taggedColour, source_colour,Sigma.mk.injEq,heq_eq_eq,true_and]
  constructor
  · exact fun h => congrArg (fun z : Σ _ : Unit, Option Colour => z.2) h
  · exact fun h => congrArg (fun c : Option Colour => (⟨(),c⟩ : Σ _ : Unit, Option Colour)) h

noncomputable def points (A : FiniteInduced (X := fun _ : Unit => Point)) : Finset Point :=
  A.finite_vertices.toFinset.image Sigma.snd

@[simp] theorem mem_points (A : FiniteInduced (X := fun _ : Unit => Point)) (x : Point) :
    x ∈ points A ↔ tag x ∈ A.vertices := by
  classical
  simp only [points,Finset.mem_image,Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa only [tag_val] using hp
  · intro h
    exact ⟨tag x,h,rfl⟩

/-- Genuine strong amalgamation of the actual old finite age. Off-base
points remain distinct even inside parents represented by the base. -/
theorem strongAmalgamation : AgeSAP source where
  strong_amalgamate := by
    classical
    intro C A B eCA eCB
    letI : Finite ↥C.vertices := C.finite_vertices.to_subtype
    letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
    letI : Fintype ↥C.vertices := Fintype.ofFinite _
    have hcol : ∀ c d : ↥C.vertices,
        colour (eCA.toEmbedding c).val.2 (eCA.toEmbedding d).val.2 =
          colour (eCB.toEmbedding c).val.2 (eCB.toEmbedding d).val.2 := by
      intro c d
      exact (tagged_colour_eq _ _ _ _).mp
        ((eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d))
    obtain ⟨g₀,hg₀⟩ := finite_extension
      (fun c : ↥C.vertices => (eCA.toEmbedding c).val.2)
      (fun c => (eCB.toEmbedding c).val.2) hcol
    let base : Finset Point := Finset.univ.image (fun c : ↥C.vertices => (eCB.toEmbedding c).val.2)
    let movedA : Finset Point := (points A).image (fun x => g₀ • x)
    obtain ⟨g₁,hg₁,hI⟩ := independent_existence movedA (points B) base
    let g : Aut := g₁ * g₀
    have hbase (c : ↥C.vertices) : g • (eCA.toEmbedding c).val.2 =
        (eCB.toEmbedding c).val.2 := by
      change g₁ • (g₀ • (eCA.toEmbedding c).val.2) = _
      rw [hg₀ c]
      exact hg₁ _ (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,rfl⟩)
    let fa : ↥A.vertices → TaggedPoint := fun a => tag (g • a.val.2)
    let D : FiniteInduced (X := fun _ : Unit => Point) :=
      ⟨Set.range fa ∪ B.vertices, (Set.finite_range fa).union B.finite_vertices⟩
    let eAD : InducedEmbedding source A D := {
      toEmbedding := {
        toFun := fun a => ⟨fa a,Or.inl ⟨a,rfl⟩⟩
        inj' := by
          intro a b h
          have hv : g • a.val.2 = g • b.val.2 := congrArg (fun p : ↥D.vertices => p.val.2) h
          apply Subtype.ext
          exact (tag_val a.val).symm.trans ((congrArg tag (MulAction.injective g hv)).trans (tag_val b.val)) }
      preserves_sort := by intro a; exact Subsingleton.elim _ _
      preserves_colours := by
        intro a b
        apply (tagged_colour_eq _ _ _ _).mpr
        exact (aut_colour g a.val.2 b.val.2).symm }
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
      have he : g • a.val.2 = b.val.2 := congrArg (fun p : ↥D.vertices => p.val.2) hab
      have ha : g₀ • a.val.2 ∈ movedA := by
        exact Finset.mem_image.mpr ⟨a.val.2,(mem_points A _).mpr (by simpa only [tag_val] using a.2),rfl⟩
      have hm : g • a.val.2 ∈ transport g₁ movedA := by
        exact (smul_mem_transport g₁ movedA (g₀ • a.val.2)).mpr ha
      have hb : g • a.val.2 ∈ points B := by
        rw [he]
        exact (mem_points B _).mpr (by simpa only [tag_val] using b.2)
      have hc : g • a.val.2 ∈ base := hI.1 _ hm hb
      rcases Finset.mem_image.mp hc with ⟨c,_,hc⟩
      refine ⟨c,?_,?_⟩
      · apply Subtype.ext
        have hh : g • (eCA.toEmbedding c).val.2 = g • a.val.2 := (hbase c).trans hc
        exact (tag_val _).symm.trans ((congrArg tag (MulAction.injective g hh)).trans (tag_val _))
      · apply Subtype.ext
        exact (tag_val _).symm.trans ((congrArg tag (hc.trans he)).trans (tag_val _))

end CCO.SIR.Positive.Direct
