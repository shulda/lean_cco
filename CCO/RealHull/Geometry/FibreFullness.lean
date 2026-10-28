import CCO.RealHull.Geometry.FibreAnchor

/-! Complete fibre diagrams are realised over the SAME whole actual anchor.
The input triangle test uses ORIGINAL colours, so this also transfers an
original legal triangle to the fibre; it does not assume internal legality.
-/

universe v w z t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)] {V : Type z}

def FibreOriginalTriangles (D : CompleteDiagram (S := fibreSource S A q) V) : Prop :=
  ∀ x y z (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    a b c, D.diagram.edge x y hxy = some a → D.diagram.edge y z hyz = some b →
      D.diagram.edge x z hxz = some c → S.Triangle a.val b.val c.val

noncomputable def fibreAnchorComplete (D : CompleteDiagram (S := fibreSource S A q) V) :
    CompleteDiagram (S := S) (V ⊕ ↥A) :=
  ⟨fibreAnchorDiagram S A q D.diagram, fibreAnchor_complete S A q D⟩

theorem fibreAnchor_triangles (D : CompleteDiagram (S := fibreSource S A q) V)
    (htri : FibreOriginalTriangles S A q D) :
    (fibreAnchorComplete S A q D).TrianglesRealizable := by
  intro x y z hxy hyz hxz a b c ha hb hc
  obtain ⟨u⟩ := ‹Nonempty (FibreSet S A q)›
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases z with
      | inl z =>
        obtain ⟨a',ha',hea⟩ := Option.map_eq_some_iff.mp ha
        obtain ⟨b',hb',heb⟩ := Option.map_eq_some_iff.mp hb
        obtain ⟨c',hc',hec⟩ := Option.map_eq_some_iff.mp hc
        rw [← hea,← heb,← hec]
        exact htri x y z _ _ _ a' b' c' ha' hb' hc'
      | inr z =>
        obtain ⟨a',ha',hea⟩ := Option.map_eq_some_iff.mp ha
        have hb' : q z = b := Option.some.inj hb
        have hc' : q z = c := Option.some.inj hc
        rw [← hea,← hb',← hc']
        simpa only [S.symmetricLoop] using
          S.triangle_rotate ((mem_row S _ _ _).mp (fibre_atom_square S A q a' z))
    | inr y =>
      cases z with
      | inl z =>
        obtain ⟨c',hc',hec⟩ := Option.map_eq_some_iff.mp hc
        have ha' : q y = a := Option.some.inj ha
        have hb' : q y = b := Option.some.inj hb
        rw [← ha',← hb',← hec]
        exact (mem_row S _ _ _).mp (fibre_atom_square S A q c' y)
      | inr z =>
        have ha' : q y = a := Option.some.inj ha
        have hc' : q z = c := Option.some.inj hc
        rw [← ha',← hc']
        exact ⟨u.val,y.val,z.val,u.property y,hb,u.property z⟩
  | inr x =>
    cases y with
    | inl y =>
      cases z with
      | inl z =>
        obtain ⟨b',hb',heb⟩ := Option.map_eq_some_iff.mp hb
        have ha' : q x = a := Option.some.inj ha
        have hc' : q x = c := Option.some.inj hc
        rw [← ha',← heb,← hc']
        exact triangle_cycle S ((mem_row S _ _ _).mp (fibre_atom_square S A q b' x))
      | inr z =>
        have ha' : q x = a := Option.some.inj ha
        have hb' : q z = b := Option.some.inj hb
        rw [← ha',← hb']
        exact ⟨x.val,u.val,z.val,(col_symm S _ _).trans (u.property x),u.property z,hc⟩
    | inr y =>
      cases z with
      | inl z =>
        have hb' : q y = b := Option.some.inj hb
        have hc' : q x = c := Option.some.inj hc
        rw [← hb',← hc']
        exact ⟨x.val,y.val,u.val,ha,(col_symm S _ _).trans (u.property y),
          (col_symm S _ _).trans (u.property x)⟩
      | inr z => exact ⟨x.val,y.val,z.val,ha,hb,hc⟩

variable {G : Type t} [Group G] [MulAction G M]

theorem original_complete_in_fibre (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S)
    (D : CompleteDiagram (S := fibreSource S A q) V)
    (htri : FibreOriginalTriangles S A q D) :
    ∃ point : V → FibreSet S A q, Function.Injective point ∧
      ∀ x y (hxy : x ≠ y) c, D.diagram.edge x y hxy = some c →
        col S (point x).val (point y).val = some c.val := by
  let E := fibreAnchorComplete S A q D
  obtain ⟨f⟩ := (CCO.semanticCCO_change_universe S cco) _ E.diagram
    (E.cycleHom_of_AP_triangles (AtomicSource.ageAP_of_homogeneous H)
      (fibreAnchor_triangles S A q D htri))
  obtain ⟨point,hpoint,hinj⟩ := align_fibre_anchor S A q H D.diagram f
  exact ⟨point,hinj (f.injective_of_complete E.complete),hpoint⟩

theorem fibre_triangle_fullness (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S)
    (D : CompleteDiagram (S := fibreSource S A q) V)
    (htri : D.TrianglesRealizable) : ∃ f : DiagramHom D.diagram, f.IsInjective := by
  have hOriginal : FibreOriginalTriangles S A q D := by
    intro x y z hxy hyz hxz a b c ha hb hc
    obtain ⟨p,r,s,hpr,hrs,hps⟩ := htri x y z hxy hyz hxz a b c ha hb hc
    exact ⟨p.val,r.val,s.val,(inducedColour_some_iff S () _ _ _ a).mp hpr,
      (inducedColour_some_iff S () _ _ _ b).mp hrs,
      (inducedColour_some_iff S () _ _ _ c).mp hps⟩
  obtain ⟨point,hinj,hpoint⟩ := original_complete_in_fibre S A q H cco D hOriginal
  let f : DiagramHom D.diagram := {
    point := point
    preserves_edge := by
      intro x y hxy c hc
      exact (inducedColour_some_iff S () _ _ _ c).mpr (hpoint x y hxy c hc)
  }
  refine ⟨f,?_⟩
  intro x y hxy
  exact hinj (by simpa only [DiagramHom.image,Sigma.mk.injEq,heq_eq_eq,true_and] using hxy)

end CCO.RealHull.Geometry
