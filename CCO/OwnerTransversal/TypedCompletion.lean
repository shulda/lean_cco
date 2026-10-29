import CCO.OwnerTransversal.TypedTriangle
import CCO.OwnerTransversal.TypedHomogeneity

universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (E : ColourEq S ()) {B : Type} [Fintype B] (q : B → Quotient E.val)

include H in
/-- Finite literal fine-record realization in the ACTUAL owner fibres. -/
theorem typed_realize_raw_records {V : Type} [Finite V]
    (cco : SemanticCCO.{0,v,0,w} S) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
    (D : RawRecords S V) (sort : V → B)
    (hPalette : ∀ x y a, D.edge x y = some a →
      ∃ (u : OwnerCarrier S E q (sort x)) (v : OwnerCarrier S E q (sort y)),
        S.atomRel a u.val v.val)
    (raw : V → M) (hraw : RawRecords.Hom S D raw) :
    ∃ point : ∀ x, OwnerCarrier S E q (sort x),
      ∀ x y a, D.edge x y = some a → S.atomRel a (point x).val (point y).val := by
  let owner : V → M := fun x => (q (sort x)).out
  have hc : ∀ x y a, D.edge x y = some a →
      ownerSaturate E.val (S.atomRel a) (owner x) (owner y) := by
    intro x y a ha
    obtain ⟨u,v,huv⟩ := hPalette x y a ha
    have hxu : E (owner x) u.val := Quotient.exact ((Quotient.out_eq _).trans u.property.symm)
    have hvy : E v.val (owner y) := Quotient.exact (v.property.trans (Quotient.out_eq _).symm)
    exact ⟨v.val,⟨u.val,hxu,huv⟩,hvy⟩
  obtain ⟨f,hf,hown,_⟩ := anchored_completion_of_aligned S H D cco E hne word hword ∅
    (by simp [RawRecords.CompleteOn]) owner raw hraw hc (by simp)
  refine ⟨fun x => ⟨f x,?_⟩,hf⟩
  exact (Quotient.sound (hown x)).symm.trans (Quotient.out_eq _)

include H in
/-- C15: triangle-defined complete fine diagrams with actual owner
palettes are exactly the finite induced typed age.  The raw triangle
provider is instantiated independently before owner completion. -/
theorem typed_triangle_age_iff {V : Type} [Finite V]
    (cco : SemanticCCO.{0,v,0,w} S) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
    (D : RawRecords S V) (sort : V → B)
    (complete : ∀ x y, x ≠ y → ∃ a, D.edge x y = some a) :
    (∃ point : ∀ x, OwnerCarrier S E q (sort x),
      Function.Injective (fun x => (point x).val) ∧
      ∀ x y, S.colour (i := ()) (j := ()) (point x).val (point y).val = D.edge x y) ↔
    RawRecords.TrianglesLegal S D ∧
      (∀ x y a, D.edge x y = some a →
        ∃ (u : OwnerCarrier S E q (sort x)) (v : OwnerCarrier S E q (sort y)),
          S.atomRel a u.val v.val) := by
  constructor
  · rintro ⟨point,hinj,hcol⟩
    exact ⟨fun x y z => ⟨_,_,_,hcol x y,hcol x z,hcol y z⟩,
      fun x y a ha => ⟨point x,point y,(hcol x y).trans ha⟩⟩
  · rintro ⟨hTriangles,hPalette⟩
    obtain ⟨raw,hraw,_⟩ := raw_triangle_fullness S H cco D complete hTriangles
    obtain ⟨point,hpoint⟩ := typed_realize_raw_records S H E q cco hne word hword
      D sort hPalette raw hraw
    refine ⟨point,?_,?_⟩
    · intro x y hxy
      by_contra hneXY
      obtain ⟨a,ha⟩ := complete x y hneXY
      have hc := hpoint x y a ha
      change (point x).val = (point y).val at hxy
      change S.colour (i := ()) (j := ()) (point x).val (point y).val = some a at hc
      rw [hxy,(S.colour_none_iff _ _).mpr rfl] at hc
      cases hc
    · intro x y
      by_cases hxy : x = y
      · subst y
        rw [D.diagonal]
        exact (S.colour_none_iff _ _).mpr rfl
      · obtain ⟨a,ha⟩ := complete x y hxy
        exact (hpoint x y a ha).trans ha.symm

variable (hq : Function.Injective q)

noncomputable def typedRawRecords {V : Type} (D : PartialDiagram (typedOwnerSource S E q hq) V) :
    RawRecords S V := by
  classical
  exact {
  edge := fun x y => if h : x = y then none else (D.edge x y h).map Subtype.val
  diagonal := fun x => by simp
  symmetric := by
    intro x y
    by_cases hxy : x = y
    · subst y; simp
    · simp only [dif_neg hxy,dif_neg (Ne.symm hxy)]
      cases hc : D.edge x y hxy with
      | none =>
        cases hd : D.edge y x (Ne.symm hxy) with
        | none => rfl
        | some a =>
          have hr := (D.edge_reverse y x (Ne.symm hxy) a).mp hd
          rw [hc] at hr
          cases hr
      | some a =>
        rw [(D.edge_reverse x y hxy a).mp hc]
        rfl
  }

theorem typedRaw_edge {V : Type} (D : PartialDiagram (typedOwnerSource S E q hq) V)
    (x y : V) (hxy : x ≠ y) (a : S.Atom () ()) :
    (typedRawRecords S E q hq D).edge x y = some a ↔
      ∃ b, D.edge x y hxy = some b ∧ b.val = a := by
  classical
  simp only [typedRawRecords,dif_neg hxy]
  exact Option.map_eq_some_iff

include H in
/-- C15's semantic typed CCO. Every cycle is first forgotten into the
original raw language, then the ACTUAL owner assignment is restored. -/
theorem typedOwner_CCO (cco : SemanticCCO.{0,v,0,w} S) (hne : E ≠ ⊥)
    (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r) :
    SemanticCCO.{0,v,0,w} (typedOwnerSource S E q hq) := by
  intro V D hCycles
  letI := D.finite_type
  let R := typedRawRecords S E q hq D
  have hRawCycles : ∀ C : SimpleCycle (RawRecords.diagram S R), CycleHom C := by
    intro C
    let C' : SimpleCycle D := {
      length := C.length
      length_ge_three := C.length_ge_three
      length_pos := C.length_pos
      vertices := C.vertices
      next_ne := C.next_ne
      specified := by
        intro k
        obtain ⟨a,ha⟩ := C.specified k
        obtain ⟨b,hb,_⟩ := (typedRaw_edge S E q hq D _ _ (C.next_ne k) a).mp ha
        exact ⟨b,hb⟩ }
    obtain ⟨point,hpoint⟩ := hCycles C'
    refine ⟨fun k => (point k).val,?_⟩
    intro k a ha
    obtain ⟨b,hb,hba⟩ := (typedRaw_edge S E q hq D _ _ (C.next_ne k) a).mp ha
    have hh := (ownerColour_some_iff S E q (point k) (point (cyclicNext C.length_pos k)) b).mp
      (hpoint k b hb)
    exact hh.trans (congrArg some hba)
  obtain ⟨raw,hraw⟩ := (RawRecords.diagramHom_iff S R).mp (cco V (RawRecords.diagram S R) hRawCycles)
  have hPalette : ∀ x y a, R.edge x y = some a →
      ∃ (u : OwnerCarrier S E q (D.vertexSort x)) (v : OwnerCarrier S E q (D.vertexSort y)),
        S.atomRel a u.val v.val := by
    intro x y a ha
    have hxy : x ≠ y := by intro hh; subst y; rw [R.diagonal] at ha; cases ha
    obtain ⟨b,hb,hba⟩ := (typedRaw_edge S E q hq D x y hxy a).mp ha
    obtain ⟨u,v,huv⟩ := b.property
    exact ⟨u,v,huv.trans (congrArg some hba)⟩
  obtain ⟨point,hpoint⟩ := typed_realize_raw_records S H E q cco hne word hword
    R D.vertexSort hPalette raw hraw
  refine ⟨⟨point,?_⟩⟩
  intro x y hxy a ha
  apply (ownerColour_some_iff S E q (point x) (point y) a).mpr
  apply hpoint x y a.val
  exact (typedRaw_edge S E q hq D x y hxy a.val).mpr ⟨a,ha,rfl⟩

end CCO.OwnerTransversal
