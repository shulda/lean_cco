import CCO.RealHull.Geometry.FibreTriangle
import CCO.RealHull.Geometry.FibreCCO

/-! Actual original-source consumers, including empty anchors and singleton
fibres. Equality remains real equality; no diversity atom represents it. -/

universe v w t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]

theorem fibre_empty_anchor (q : ↥(∅ : Finset M) → Atom S) :
    FibreSet S ∅ q = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _ a
    have ha : a.val ∈ (∅ : Finset M) := a.property
    exact False.elim (Finset.notMem_empty a.val ha)

theorem fibre_empty_nonempty (q : ↥(∅ : Finset M) → Atom S) :
    Nonempty (FibreSet S ∅ q) := by
  obtain ⟨x⟩ := S.nonemptySort ()
  exact ⟨⟨x,by rw [fibre_empty_anchor S q]; trivial⟩⟩

theorem fibre_singleton_no_diversity (A : Finset M) (q : ↥A → Atom S)
    [Subsingleton (FibreSet S A q)] : IsEmpty (InducedAtom S () (FibreSet S A q)) := by
  refine ⟨?_⟩
  intro c
  obtain ⟨x,y,hxy⟩ := c.property
  have he : x = y := Subsingleton.elim _ _
  subst y
  change col S x.val x.val = some c.val at hxy
  rw [(col_none S x.val x.val).mpr rfl] at hxy
  cases hxy

variable {G : Type t} [Group G] [MulAction G M]

theorem fibre_actual_stabilizer_orbit (A : Finset M) (q : ↥A → Atom S)
    (H : HomogeneousSource S G) (x : FibreSet S A q) :
    MulAction.orbit (AnchorStabilizer (G := G) A) x.val = FibreSet S A q := by
  ext y
  constructor
  · intro hy
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hy
    have hh := (fibre_motion_membership S A q H g.val g.property x.val).mpr x.property
    exact hg ▸ hh
  · intro hy
    obtain ⟨g,hfix,hg⟩ := fibre_transitive_ambient S A q H x ⟨y,hy⟩
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g,hfix⟩,hg⟩

/-- These are the ACTUAL source premises supplied to the internal Hasse
consumer, before any finite-fibre globalisation theorem has been used.
-/
theorem fibre_standing_source (A : Finset M) (q : ↥A → Atom S)
    [Nonempty (FibreSet S A q)] (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) :
    HomogeneousSource (fibreSource S A q) (inducedAut S () (FibreSet S A q)) ∧
      SemanticCCO.{0,v,0,w} (fibreSource S A q) :=
  ⟨fibre_homogeneous S A q H, fibre_semanticCCO S A q H cco⟩

end CCO.RealHull.Geometry
