import CCO.AutomaticEPCore.OriginalTypes
import CCO.ExactEPGeometry.OriginalExactOccupancy
import CCO.ParityHasse.Original.OrbitalBipartite
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! B063 C21–C25: real old endpoint choices in actual exact occupancy
classes and lifting of a bipartite quotient graph to one ORIGINAL atom.
Only I01 occupancy is used; no rank, terminal/core or gate/phase argument
supplies a separator. The actual quotient source adapter must discharge
all projection/action clauses before using this conditional geometry. -/

universe u v w r z
namespace CCO.AutomaticEPCore

open CCO.ParityHasse.Original CCO.APCharacter.Towers CCO.ExactEPGeometry

/-- Original pair homogeneity makes the WHOLE old atom lie in the same
invariant pullback as the one witnessed old pair. Pullback of a genuine
bipartition is a genuine old-atom bipartition. -/
theorem original_bipartite_pullback_atom
    {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) {i : ι}
    {Q : Type z} [MulAction G Q]
    (pi : X i → Q) (equivariant : ∀ (g : G) x, pi (g • x) = g • pi x)
    (graph : SimpleGraph Q)
    (invariant : ∀ (g : G) x y, graph.Adj x y → graph.Adj (g • x) (g • y))
    (bipartite : graph.IsBipartite)
    (x y : X i) (hxy : graph.Adj (pi x) (pi y)) :
    ∃ a : S.Atom i i, S.atomRel a x y ∧
      (atomGraph S a).IsBipartite ∧
      ∀ x' y', S.atomRel a x' y' → graph.Adj (pi x') (pi y') := by
  have hne : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
    intro heq
    have he : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using heq
    exact graph.ne_of_adj hxy (congrArg pi he)
  obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hne
  have allPairs : ∀ x' y', S.atomRel a x' y' → graph.Adj (pi x') (pi y') := by
    intro x' y' h'
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y'
      (ha.trans h'.symm)
    have h := invariant g (pi x) (pi y) hxy
    rw [← equivariant g x,← equivariant g y,hgx,hgy] at h
    exact h
  let pullback : (atomGraph S a) →g graph :=
    { toFun := pi, map_rel' := fun {x' y'} h => allPairs x' y' h }
  exact ⟨a,ha,SimpleGraph.Colorable.of_hom pullback bipartite,allPairs⟩

/-- C21–C25 with prescribed actual old terminal types. The initial
quotient-edge endpoints may occupy different current names p,q; actual
I01 occupancy chooses the exact requested s,t INSIDE THOSE SAME E-classes.
No representative section, common order or quotient SAP is assumed. -/
theorem original_bipartite_separator_from_occupancy
    (A B : CurrentSource.{u,v,w,r}) (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {Q : Type z} [MulAction A.G Q]
    (pi : A.Point base → Q)
    (equivariant : ∀ (g : A.G) x, pi (g • x) = g • pi x)
    (class_fixed : ∀ x y, E x y → pi x = pi y)
    (graph : SimpleGraph Q)
    (invariant : ∀ (g : A.G) x y, graph.Adj x y → graph.Adj (g • x) (g • y))
    (bipartite : graph.IsBipartite)
    (p q s t : B.Sorts) (x : B.Point p) (y : B.Point q)
    (hs : prefixSupport P (originalExactGlobalRelation A base hOne E) p s)
    (ht : prefixSupport P (originalExactGlobalRelation A base hOne E) q t)
    (edge : graph.Adj
      (pi (originalPointEquiv A base hOne (P.project ⟨p,x⟩)))
      (pi (originalPointEquiv A base hOne (P.project ⟨q,y⟩)))) :
    ∃ a : A.source.Atom base base,
      (atomGraph A.source a).IsBipartite ∧ originalAtomTable A B P base hOne a s t := by
  obtain ⟨xs,hxs⟩ :=
    (originalExactClass_occupies_supported_type A B P base hOne E p s x).mp hs
  obtain ⟨yt,hyt⟩ :=
    (originalExactClass_occupies_supported_type A B P base hOne E q t y).mp ht
  have hsPoint :
      pi (originalPointEquiv A base hOne (P.project ⟨p,x⟩)) =
        pi (originalPointEquiv A base hOne (P.project ⟨s,xs⟩)) :=
    class_fixed _ _ hxs
  have htPoint :
      pi (originalPointEquiv A base hOne (P.project ⟨q,y⟩)) =
        pi (originalPointEquiv A base hOne (P.project ⟨t,yt⟩)) :=
    class_fixed _ _ hyt
  rw [hsPoint,htPoint] at edge
  obtain ⟨a,ha,hBP,_⟩ := original_bipartite_pullback_atom A.source A.homogeneous
    pi equivariant graph invariant bipartite
    (originalPointEquiv A base hOne (P.project ⟨s,xs⟩))
    (originalPointEquiv A base hOne (P.project ⟨t,yt⟩)) edge
  exact ⟨a,hBP,xs,yt,ha⟩

end CCO.AutomaticEPCore
