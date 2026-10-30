import CCO.PairSafeSplit.Strong.NormalForm
import CCO.StrongExact.TriangleFullness
import CCO.APCharacter.SourceAge.UnarySourceCCO

/-! The WHOLE canonical child age is exactly its FULL lifted triangle
class. Child labels retain unary validity; child atoms are exactly allowed
old atoms. All finite complete inputs, including fewer than three vertices,
are covered by actual source homogeneity and HOM CCO. -/

universe u v w t z
namespace CCO.PairSafeSplit.Strong
open APCharacter RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : Identification S H (P.completion_property cco))

/-- All three masks are carried by actual occurring child atoms. The
actual marked triangle has precisely the OLD full triangle type. -/
theorem triangle_iff_old {c d e : Rank.Child (β I)}
    (a : (source I).Atom c d) (b : (source I).Atom d e) (q : (source I).Atom c e) :
    (source I).Triangle a b q ↔ S.Triangle a.val b.val q.val := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    exact ⟨x.val,y.val,z.val,
      (Rank.colour_some_iff S (β I) (tag I) x y a).mp hxy,
      (Rank.colour_some_iff S (β I) (tag I) y z b).mp hyz,
      (Rank.colour_some_iff S (β I) (tag I) x z q).mp hxz⟩
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    obtain ⟨p,r,hpr⟩ := (source I).realized q
    have hprOld := (Rank.colour_some_iff S (β I) (tag I) p r q).mp hpr
    obtain ⟨g,hgx,hgz⟩ := S.pair_homogeneous_of_homogeneous H x p.val z r.val
      (hxz.trans hprOld.symm)
    have hword : PositiveWord.represented S
        (forgetWord I (.cons a (.single b))) p.val r.val := by
      refine ⟨g • y,?_,?_⟩
      · change S.colour p.val (g • y) = some a.val
        simpa only [hgx] using (S.colourInvariant_of_homogeneous H g x y).trans hxy
      · change S.colour (g • y) r.val = some b.val
        simpa only [hgz] using (S.colourInvariant_of_homogeneous H g y z).trans hyz
    obtain ⟨m,hpm,hmr⟩ := (represented_normal_form P cco I (.cons a (.single b)) p r).mpr hword
    exact ⟨p,m,r,hpm,hmr,hpr⟩

/-- Local FULL lifted-table legality on an arbitrary finite complete
network. Unary validity and pair occurrence are literal parts of its child
sorts and atoms, rather than additional vacuous triangle conditions. -/
def FullTriangleLegal {V : Type z} (D : CompleteDiagram (S := source I) V) : Prop :=
  ∀ (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (a : (source I).Atom (D.diagram.vertexSort x) (D.diagram.vertexSort y))
    (b : (source I).Atom (D.diagram.vertexSort y) (D.diagram.vertexSort z))
    (q : (source I).Atom (D.diagram.vertexSort x) (D.diagram.vertexSort z)),
    D.diagram.edge x y hxy = some a → D.diagram.edge y z hyz = some b →
    D.diagram.edge x z hxz = some q → S.Triangle a.val b.val q.val

theorem fullTriangleLegal_iff {V : Type z} (D : CompleteDiagram (S := source I) V) :
    FullTriangleLegal P cco I D ↔ D.TrianglesRealizable := by
  constructor
  · intro h x y z hxy hyz hxz a b q ha hb hq
    exact (triangle_iff_old P cco I a b q).mpr (h x y z hxy hyz hxz a b q ha hb hq)
  · intro h x y z hxy hyz hxz a b q ha hb hq
    exact (triangle_iff_old P cco I a b q).mp (h x y z hxy hyz hxz a b q ha hb hq)

/-- Exact finite-age membership, not merely agreement of binary tables.
The realization is injective into the SAME whole canonical source. There
is no cardinality lower bound; empty, unary and pair inputs are included. -/
theorem full_lifted_triangle_class {V : Type z} (D : CompleteDiagram (S := source I) V) :
    FullTriangleLegal P cco I D ↔ ∃ f : DiagramHom D.diagram, f.IsInjective := by
  constructor
  · intro h
    have ht := (fullTriangleLegal_iff P cco I D).mp h
    obtain ⟨f⟩ := (semanticCCO I) V D.diagram
      (D.cycleHom_of_AP_triangles (AtomicSource.ageAP_of_homogeneous (homogeneous I)) ht)
    exact ⟨f,f.injective_of_complete D.complete⟩
  · rintro ⟨f,_⟩
    apply (fullTriangleLegal_iff P cco I D).mpr
    intro x y z hxy hyz hxz a b q ha hb hq
    exact ⟨f.point x,f.point y,f.point z,
      f.preserves_edge x y hxy a ha,f.preserves_edge y z hyz b hb,
      f.preserves_edge x z hxz q hq⟩

end
end CCO.PairSafeSplit.Strong
