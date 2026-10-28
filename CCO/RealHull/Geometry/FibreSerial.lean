import CCO.RealHull.Geometry.FibreAnchor

/-! Every actual fibre atom is serial at every fibre point. In an anchored
diagram, moving along any one specified edge preserves the corresponding
vertex condition: fibre membership for new vertices, literal equality for
anchors. A mixed cycle may therefore restart at each actual anchor. -/

universe v w z t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)] {V : Type z}
variable {G : Type t} [Group G] [MulAction G M]

theorem fibre_atom_serial (H : HomogeneousSource S G)
    (c : InducedAtom S () (FibreSet S A q)) (p : FibreSet S A q) :
    ∃ r : FibreSet S A q, col S p.val r.val = some c.val := by
  obtain ⟨x,y,hxy⟩ := c.property
  obtain ⟨g,hfix,hg⟩ := fibre_transitive_ambient S A q H x p
  let r : FibreSet S A q :=
    ⟨g • y.val,(fibre_motion_membership S A q H g hfix y.val).mpr y.property⟩
  refine ⟨r,?_⟩
  have hh := col_invariant S H g x.val y.val
  rw [hg] at hh
  exact hh.trans hxy

def FibreVertexRealizes : (V ⊕ ↥A) → M → Prop
  | .inl _,p => p ∈ FibreSet S A q
  | .inr a,p => p = a.val

theorem fibreAnchor_edge_serial (H : HomogeneousSource S G)
    (D : PartialDiagram (fibreSource S A q) V)
    (x y : V ⊕ ↥A) (hxy : x ≠ y) (a : Atom S)
    (ha : (fibreAnchorDiagram S A q D).edge x y hxy = some a)
    (p : M) (hp : FibreVertexRealizes S A q x p) :
    ∃ r : M, FibreVertexRealizes S A q y r ∧ col S p r = some a := by
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      obtain ⟨c,hc,hca⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨r,hr⟩ := fibre_atom_serial S A q H c ⟨p,hp⟩
      exact ⟨r.val,r.property,hr.trans (congrArg some hca)⟩
    | inr b =>
      have hqa : q b = a := Option.some.inj ha
      exact ⟨b.val,rfl,(hp b).trans (congrArg some hqa)⟩
  | inr b =>
    cases y with
    | inl y =>
      obtain ⟨r⟩ := ‹Nonempty (FibreSet S A q)›
      have hqa : q b = a := Option.some.inj ha
      refine ⟨r.val,r.property,?_⟩
      rw [hp]
      exact (col_symm S _ _).trans ((r.property b).trans (congrArg some hqa))
    | inr c =>
      exact ⟨c.val,rfl,hp ▸ ha⟩

end CCO.RealHull.Geometry
