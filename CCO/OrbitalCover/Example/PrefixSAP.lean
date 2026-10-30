import CCO.OrbitalCover.Example.PrefixCCO

namespace CCO.OrbitalCover.Example.Prefix
noncomputable section

def freshen (k : Stage) (B C : Finset (Sigma (carrier k))) (x : Sigma (carrier k)) :
    Sigma (carrier k) := by
  classical
  let y := Example.freshen (B.image (erase k)) (C.image (erase k)) (erase k x)
  have hm : mark k y = mark k (erase k x) := by
    cases k with
    | first => exact Example.freshen_p _ _ _
    | both => exact Prod.ext (Example.freshen_p _ _ _) (Example.freshen_q _ _ _)
  exact ⟨x.1,⟨y,hm.trans x.2.property⟩⟩

@[simp] theorem freshen_sort (k : Stage) (B C : Finset (Sigma (carrier k)))
    (x : Sigma (carrier k)) : (freshen k B C x).1 = x.1 := rfl

@[simp] theorem erase_freshen (k : Stage) (B C : Finset (Sigma (carrier k)))
    (x : Sigma (carrier k)) :
    erase k (freshen k B C x) = Example.freshen (B.image (erase k)) (C.image (erase k)) (erase k x) := rfl

theorem freshen_injective (k : Stage) (B C : Finset (Sigma (carrier k))) :
    Function.Injective (freshen k B C) := by
  intro x y h
  apply erase_injective k
  exact Example.freshen_injective _ _ (congrArg (erase k) h)

theorem freshen_fixed (k : Stage) {B C : Finset (Sigma (carrier k))}
    {x : Sigma (carrier k)} (hx : x ∈ C) : freshen k B C x = x := by
  classical
  apply erase_injective k
  exact Example.freshen_fixed (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

theorem freshen_mem_right (k : Stage) {B C : Finset (Sigma (carrier k))}
    {x : Sigma (carrier k)} (hx : freshen k B C x ∈ B) : x ∈ C := by
  classical
  have hh : Example.freshen (B.image (erase k)) (C.image (erase k)) (erase k x) ∈
      B.image (erase k) := Finset.mem_image.mpr ⟨freshen k B C x,hx,rfl⟩
  obtain ⟨c,hc,he⟩ := Finset.mem_image.mp (Example.freshen_mem_right hh)
  exact erase_injective k he ▸ hc

theorem freshen_colours (k : Stage) (B C : Finset (Sigma (carrier k)))
    (x y : Sigma (carrier k)) :
    taggedColour (source k) (freshen k B C x) (freshen k B C y) =
      taggedColour (source k) x y := by
  rcases x with ⟨c,x⟩
  rcases y with ⟨d,y⟩
  apply congrArg (fun a => (⟨c,d,a⟩ : Σ c, Σ d, Option ((source k).Atom c d)))
  apply Option.map_injective Subtype.val_injective
  exact (colour_map k _ _).trans
    ((Example.freshen_colour _ _ _ _).trans (colour_map k x y).symm)

/-- Both concrete unary prefixes have genuine SAP. All named predicates
are retained while the original infinite clone index separates the legs. -/
theorem strongAmalgamation (k : Stage) : AgeSAP (source k) where
  strong_amalgamate := by
    classical
    intro C A B eCA eCB
    letI : Finite ↥C.vertices := C.finite_vertices.to_subtype
    letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
    letI : Fintype ↥C.vertices := Fintype.ofFinite _
    obtain ⟨g,hg⟩ := (homogeneous k).extends_finite_diagram
      (fun c : ↥C.vertices => (eCA.toEmbedding c).val)
      (fun c => (eCB.toEmbedding c).val)
      (fun c d => (eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d))
    let base : Finset (Sigma (carrier k)) :=
      Finset.univ.image (fun c : ↥C.vertices => (eCB.toEmbedding c).val)
    let move (x : Sigma (carrier k)) := freshen k B.finite_vertices.toFinset base (g • x)
    have hmove : Function.Injective move := (freshen_injective k _ _).comp (MulAction.injective g)
    have hbase (c : ↥C.vertices) : move (eCA.toEmbedding c).val = (eCB.toEmbedding c).val := by
      dsimp only [move]
      rw [hg c, freshen_fixed k (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,rfl⟩)]
    let fa : ↥A.vertices → Sigma (carrier k) := fun a => move a.val
    let D : FiniteInduced (X := carrier k) :=
      ⟨Set.range fa ∪ B.vertices, (Set.finite_range fa).union B.finite_vertices⟩
    let eAD : InducedEmbedding (source k) A D := {
      toEmbedding := {
        toFun := fun a => ⟨fa a,Or.inl ⟨a,rfl⟩⟩
        inj' := by
          intro a b h
          exact Subtype.ext (hmove (congrArg (fun p : ↥D.vertices => p.val) h)) }
      preserves_sort := fun a => (homogeneous k).preserves_sort g a.val
      preserves_colours := by
        intro a b
        exact ((freshen_colours k _ _ _ _).trans
          ((homogeneous k).preserves_colours g a.val b.val)).symm }
    let eBD : InducedEmbedding (source k) B D := {
      toEmbedding := {
        toFun := fun b => ⟨b.val,Or.inr b.2⟩
        inj' := fun a b h => Subtype.ext (congrArg (fun p : ↥D.vertices => p.val) h) }
      preserves_sort := fun _ => rfl
      preserves_colours := fun _ _ => rfl }
    refine ⟨D,eAD,eBD,?_,?_⟩
    · intro c
      exact Subtype.ext (hbase c)
    · intro a b hab
      have he : move a.val = b.val := congrArg (fun p : ↥D.vertices => p.val) hab
      have hb : move a.val ∈ B.finite_vertices.toFinset :=
        B.finite_vertices.mem_toFinset.mpr (he.symm ▸ b.property)
      have hc : g • a.val ∈ base := freshen_mem_right k hb
      obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hc
      have hm : move a.val = g • a.val :=
        freshen_fixed k (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,hc⟩)
      refine ⟨c,?_,?_⟩
      · exact Subtype.ext (MulAction.injective g ((hg c).trans hc))
      · exact Subtype.ext (hc.trans (hm.symm.trans he))

end
end CCO.OrbitalCover.Example.Prefix
