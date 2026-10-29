import CCO.OwnerTransversal.AnchoredFrame

/-! The finite protected frame is built from the ACTUAL anchor images
and the ACTUAL desired owner representatives.  New formal points index
only distinct real points not already in the anchor image. -/
universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

include H in
/-- C07 with the original homomorphism already aligned on its complete
anchor.  There is no extra finite-frame/provider assumption. -/
theorem anchored_completion_of_aligned {V : Type} [Finite V]
    (D : RawRecords S V) (cco : SemanticCCO.{0,v,0,w} S)
    (E : ColourEq S ()) (hne : E ≠ ⊥) (word : RawWord S () ())
    (hword : RawWord.relation S word = E.val.r)
    (A : Finset V) (complete : RawRecords.CompleteOn S D A)
    (owner base : V → M) (hbase : RawRecords.Hom S D base)
    (hOwner : ∀ x y a, D.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner x) (owner y))
    (hA : ∀ x ∈ A, E (owner x) (base x)) :
    ∃ f : V → M, RawRecords.Hom S D f ∧ (∀ x, E (owner x) (f x)) ∧
      ∀ x ∈ A, f x = base x := by
  classical
  letI := Fintype.ofFinite V
  let U : Finset M := Finset.univ.image owner \ A.image base
  let e := Fintype.equivFin ↥U
  let New := Fin (Fintype.card ↥U)
  let point : New → M := fun i => (e.symm i).val
  have point_mem (i : New) : point i ∈ U := (e.symm i).property
  have point_not (i : New) : point i ∉ A.image base := (Finset.mem_sdiff.mp (point_mem i)).2
  let W := V ⊕ New
  let base' : W → M := Sum.elim base point
  let owner' : W → M := Sum.elim owner point
  let isAnchor : W → Prop := Sum.elim (fun x => x ∈ A) (fun _ => True)
  let T : Finset W := Finset.univ.filter isAnchor
  have memT (x : W) : x ∈ T ↔ isAnchor x := by simp only [T,Finset.mem_filter,Finset.mem_univ,true_and]
  have hInj : ∀ x ∈ T, ∀ y ∈ T, base' x = base' y → x = y := by
    intro x hx y hy hxy
    have hx' := (memT x).mp hx
    have hy' := (memT y).mp hy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        congr 1
        by_contra hne
        obtain ⟨a,ha⟩ := complete x hx' y hy' hne
        have hh := hbase x y a ha
        change base x = base y at hxy
        rw [hxy,(S.colour_none_iff _ _).mpr rfl] at hh
        cases hh
      | inr j =>
        apply False.elim
        apply point_not j
        exact Finset.mem_image.mpr ⟨x,hx',hxy⟩
    | inr i =>
      cases y with
      | inl y =>
        apply False.elim
        apply point_not i
        exact Finset.mem_image.mpr ⟨y,hy',hxy.symm⟩
      | inr j =>
        congr 1
        apply e.symm.injective
        exact Subtype.ext hxy
  let D' : RawRecords S W := {
    edge := fun x y => match x,y with
      | .inl x,.inl y => D.edge x y
      | x,y => if isAnchor x ∧ isAnchor y then S.colour (i := ()) (j := ()) (base' x) (base' y) else none
    diagonal := by
      intro x
      cases x with
      | inl x => exact D.diagonal x
      | inr i =>
        simp only [isAnchor,Sum.elim_inr,true_and,ite_true]
        exact (S.colour_none_iff _ _).mpr rfl
    symmetric := by
      intro x y
      cases x <;> cases y
      · exact D.symmetric _ _
      · simp only [and_comm,colour_symmetric S]
      · simp only [and_comm,colour_symmetric S]
      · simp only [and_comm,colour_symmetric S] }
  have hbase' : RawRecords.Hom S D' base' := by
    intro x y a ha
    cases x with
    | inl x =>
      cases y with
      | inl y => exact hbase x y a ha
      | inr j =>
        simp only [D',isAnchor,Sum.elim_inl,Sum.elim_inr,and_true] at ha
        split_ifs at ha with hx
        exact ha
    | inr i =>
      cases y with
      | inl y =>
        simp only [D',isAnchor,Sum.elim_inl,Sum.elim_inr,true_and] at ha
        split_ifs at ha with hy
        exact ha
      | inr j => simpa only [D',isAnchor,Sum.elim_inr,true_and,ite_true] using ha
  have hT : ∀ x ∈ T, E (owner' x) (base' x) := by
    intro x hx
    have hx' := (memT x).mp hx
    cases x with
    | inl x => exact hA x hx'
    | inr i => exact E.val.refl _
  have hComplete : RawRecords.CompleteOn S D' T := by
    intro x hx y hy hxy
    have hx' := (memT x).mp hx
    have hy' := (memT y).mp hy
    have hne : base' x ≠ base' y := fun hh => hxy (hInj x hx y hy hh)
    have hcol : ∃ a, S.colour (i := ()) (j := ()) (base' x) (base' y) = some a := by
      cases hc : S.colour (i := ()) (j := ()) (base' x) (base' y) with
      | none =>
        have he : base' x = base' y := by
          simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff _ _).mp hc
        exact (hne he).elim
      | some a => exact ⟨a,rfl⟩
    cases x with
    | inl x =>
      cases y with
      | inl y => exact complete x hx' y hy' (fun hh => hxy (congrArg Sum.inl hh))
      | inr j =>
        simpa only [D',if_pos (show isAnchor (.inl x) ∧ isAnchor (.inr j) from ⟨hx',hy'⟩)] using hcol
    | inr i =>
      cases y with
      | inl y =>
        simpa only [D',if_pos (show isAnchor (.inr i) ∧ isAnchor (.inl y) from ⟨hx',hy'⟩)] using hcol
      | inr j =>
        simpa only [D',if_pos (show isAnchor (.inr i) ∧ isAnchor (.inr j) from ⟨hx',hy'⟩)] using hcol
  have hOwner' : ∀ x y a, D'.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner' x) (owner' y) := by
    intro x y a ha
    cases x with
    | inl x =>
      cases y with
      | inl y => exact hOwner x y a ha
      | inr j =>
        have hx : Sum.inl x ∈ T := by
          apply (memT _).mpr
          by_contra hn
          simp only [D',isAnchor,Sum.elim_inl,Sum.elim_inr,hn,false_and,if_neg] at ha
          cases ha
        exact ⟨_,⟨_,hT _ hx,hbase' _ _ a ha⟩,E.val.refl _⟩
    | inr i =>
      cases y with
      | inl y =>
        have hy : Sum.inl y ∈ T := by
          apply (memT _).mpr
          by_contra hn
          simp only [D',isAnchor,Sum.elim_inl,Sum.elim_inr,hn,and_false,if_neg] at ha
          cases ha
        exact ⟨_,⟨_,E.val.refl _,hbase' _ _ a ha⟩,E.val.symm (hT _ hy)⟩
      | inr j => exact ⟨_,⟨_,E.val.refl _,hbase' _ _ a ha⟩,E.val.refl _⟩
  have findAnchor (x : V) (h : owner x ∈ A.image base) :
      ∃ a, a ∈ A ∧ base a = owner x := Finset.mem_image.mp h
  have memNew (x : V) (h : owner x ∉ A.image base) : owner x ∈ U :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩,h⟩
  let rep : W → W := fun x => match x with
    | .inl x => if h : owner x ∈ A.image base then
        .inl (findAnchor x h).choose
      else .inr (e ⟨owner x,memNew x h⟩)
    | .inr i => .inr i
  have hRep : ∀ x, rep x ∈ T ∧ E (owner' x) (base' (rep x)) := by
    intro x
    cases x with
    | inl x =>
      by_cases hx : owner x ∈ A.image base
      · simp only [rep,dif_pos hx]
        refine ⟨(memT _).mpr (findAnchor x hx).choose_spec.1,?_⟩
        change E (owner x) (base (findAnchor x hx).choose)
        rw [(findAnchor x hx).choose_spec.2]
      · simp only [rep,dif_neg hx]
        refine ⟨(memT _).mpr trivial,?_⟩
        change E (owner x) (e.symm (e ⟨owner x,memNew x hx⟩)).val
        rw [Equiv.symm_apply_apply]
    | inr i => exact ⟨(memT _).mpr trivial,E.val.refl _⟩
  obtain ⟨f,hf,hOwn,hfix⟩ := protected_finite_frame_completion S H D' rep cco E hne word
    hword T hComplete owner' base' hbase' hOwner' hT hRep
  refine ⟨fun x => f (.inl x),fun x y a ha => hf _ _ a ha,fun x => hOwn (.inl x),?_⟩
  intro x hx
  exact hfix (.inl x) ((memT _).mpr hx)

end CCO.OwnerTransversal
