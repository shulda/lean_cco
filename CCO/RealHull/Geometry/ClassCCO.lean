import CCO.RealHull.Geometry.ClassHomogeneity
import CCO.RawExact.DiagramReindex
import CCO.StrongExact.TriangleFullness
import Mathlib.Logic.Relation

/-!
# CCO of an actual invariant class

Original CCO first realizes the diagram in the ambient real source. Each
specified-edge component lies in one original equivalence class. A separate
actual ambient motion sends that component into the designated class. Distinct
components may overlap after this homomorphic construction.
-/

universe u v w z t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι) (Z : Set (X i)) [Nonempty Z]

def forgetInducedDiagram {V : Type z} (D : PartialDiagram (inducedSource S i Z) V) :
    PartialDiagram S V where
  finite_type := D.finite_type
  vertexSort _ := i
  edge x y h := (D.edge x y h).map Subtype.val
  edge_reverse := by
    intro x y h c
    constructor
    · intro hc
      cases hd : D.edge x y h with
      | none => simp only [hd,Option.map_none] at hc; cases hc
      | some d =>
        have he : d.val = c := by
          rw [hd] at hc
          exact Option.some.inj hc
        have hr := (D.edge_reverse x y h d).mp hd
        change D.edge y x h.symm = some d at hr
        rw [hr]
        change some d.val = some (S.conv c)
        rw [he,S.symmetricLoop]
    · intro hc
      cases hd : D.edge y x h.symm with
      | none => simp only [hd,Option.map_none] at hc; cases hc
      | some d =>
        have he : d.val = c := by
          have hh : some d.val = some (S.conv c) := by rw [hd] at hc; exact hc
          simpa only [S.symmetricLoop] using Option.some.inj hh
        have hr := (D.edge_reverse y x h.symm d).mp hd
        change D.edge x y h = some d at hr
        rw [hr]
        change some d.val = some c
        rw [he]

def cycleFromForget {V : Type z} (D : PartialDiagram (inducedSource S i Z) V)
    (C : SimpleCycle (forgetInducedDiagram S i Z D)) : SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := C.vertices
  next_ne := C.next_ne
  specified := by
    intro p
    obtain ⟨c,hc⟩ := C.specified p
    change (D.edge _ _ _).map Subtype.val = some c at hc
    cases hd : D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) with
    | none => rw [hd] at hc; cases hc
    | some d => exact ⟨d,rfl⟩

theorem forgotten_cycles {V : Type z} (D : PartialDiagram (inducedSource S i Z) V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∀ C : SimpleCycle (forgetInducedDiagram S i Z D), CycleHom C := by
  intro C
  obtain ⟨f,hf⟩ := hcycles (cycleFromForget S i Z D C)
  refine ⟨fun p => (f p).val,?_⟩
  intro p c hc
  change (D.edge _ _ _).map Subtype.val = some c at hc
  cases hd : D.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) with
  | none => rw [hd] at hc; cases hc
  | some d =>
    have he : d.val = c := by
      rw [hd] at hc
      exact Option.some.inj hc
    have hh := hf p d hd
    have ho := (inducedColour_some_iff S i Z (f p) (f (cyclicNext C.length_pos p)) d).mp hh
    exact ho.trans (congrArg some he)

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)
include H

theorem class_semanticCCO (cco : SemanticCCO.{u,v,0,w} S)
    (E : ColourEq S i) (a : X i) : SemanticCCO.{0,v,z,w} (classSource S i E a) := by
  classical
  let Z : Set (X i) := {x | E a x}
  letI : Nonempty Z := ⟨⟨a,E.val.refl a⟩⟩
  intro V D hcycles
  obtain ⟨f⟩ := (semanticCCO_change_universe S cco) V (forgetInducedDiagram S i Z D)
    (forgotten_cycles S i Z D hcycles)
  let R : V → V → Prop := fun x y => ∃ (h : x ≠ y), ∃ c, D.edge x y h = some c
  let Q := Quotient (Relation.EqvGen.setoid R)
  let q : V → Q := Quotient.mk _
  have hR : ∀ x y, R x y → E (f.point x) (f.point y) := by
    rintro x y ⟨h,c,hc⟩
    have he := f.preserves_edge x y h c.val (by
      change (D.edge x y h).map Subtype.val = some c.val
      rw [hc]
      rfl)
    exact (class_atom_occurs_iff S i H E a c.val).mp c.property _ _ he
  have hcomponent : ∀ x y, Relation.EqvGen R x y → E (f.point x) (f.point y) := by
    intro x y hxy
    induction hxy with
    | rel x y h => exact hR x y h
    | refl x => exact E.val.refl _
    | symm _ _ _ ih => exact E.val.symm ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact E.val.trans ih₁ ih₂
  let rep : Q → V := Quotient.out
  have hrep (x : V) : E (f.point (rep (q x))) (f.point x) :=
    hcomponent _ _ (Quotient.exact (Quotient.out_eq (q x)))
  have hmove : ∀ c : Q, ∃ g : G, g • f.point (rep c) = a :=
    fun c => S.original_sort_transitive_of_homogeneous H i _ a
  choose motion hmotion using hmove
  let point (x : V) : Z := ⟨motion (q x) • f.point x,by
    have hh := (class_group_invariant S i H E (motion (q x)) _ _).mpr (hrep x)
    change E a (motion (q x) • f.point x)
    exact Eq.mp (congrArg (fun z : X i => E z (motion (q x) • f.point x))
      (hmotion (q x))) hh⟩
  refine ⟨⟨point,?_⟩⟩
  intro x y h c hc
  have hq : q x = q y := Quotient.sound (Relation.EqvGen.rel _ _ ⟨h,c,hc⟩)
  apply (inducedColour_some_iff S i Z (point x) (point y) c).mpr
  change S.colour (motion (q x) • f.point x) (motion (q y) • f.point y) = some c.val
  rw [← hq,S.colourInvariant_of_homogeneous H]
  exact f.preserves_edge x y h c.val (by
    change (D.edge x y h).map Subtype.val = some c.val
    rw [hc]
    rfl)

theorem class_triangleFullness (cco : SemanticCCO.{u,v,0,w} S)
    (E : ColourEq S i) (a : X i) {V : Type z}
    (D : CompleteDiagram (S := classSource S i E a) V) (htri : D.TrianglesRealizable) :
    ∃ f : DiagramHom D.diagram, f.IsInjective := by
  let HC := class_homogeneous S i H E a
  obtain ⟨f⟩ := class_semanticCCO S i H cco E a V D.diagram
    (D.cycleHom_of_AP_triangles (AtomicSource.ageAP_of_homogeneous HC) htri)
  exact ⟨f,f.injective_of_complete D.complete⟩

end CCO.RealHull.Geometry
