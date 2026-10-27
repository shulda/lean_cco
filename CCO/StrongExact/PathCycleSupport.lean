import CCO.StrongExact.PCSoundness
import CCO.StrongExact.ProfileSemantics

/-!
# STRONG C12: an old edge is supported by every specified positive path

An actual strong PC fixed point with a nonempty domain on a prescribed
edge can retain ONLY that edge's literal diversity atom. C11 then puts
this same atom in the genuine STRONG profile of every specified
endpoint-separated path between the edge's endpoints. Under original
homogeneous SAP this atom has a represented real path witness whose
endpoints are genuinely distinct.

This is the cycle-cut path witness needed in the homomorphic CCO
part of C12. It does not claim yet that every abstract SimpleCycle has
been converted to a cut path or that each surviving nonspecified
atom extends to a whole-diagram completion.
-/

universe u v w z

namespace CCO.StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- Intersection of the STRONG profiles of *all* specified positive
endpoint-separated walks between x and y. This can be an infinite
family of walks, even though V is finite, so finiteness of its
presentation needs a separate finite-palette argument. -/
def positivePathBound (x y : V) :
    S.Menu (D.vertexSort x) (D.vertexSort y) :=
  {a | ∀ p : SpecifiedPath D x y,
    a ∈ PositiveWord.profile S p.word}

/-- Full C11 sound inclusion in an arbitrary endpoint-separated path
intersection, with the actual named sort of each endpoint retained. -/
theorem fixedNetwork_subset_positivePathBound
    {x y : V} (hxy : x ≠ y) :
    fixedNetwork D ⟨x, y, hxy⟩ ⊆
      positivePathBound D x y := by
  intro a ha p
  exact fixedNetwork_subset_path_profile D p ha

/-- The correct old fine atom is in EVERY positive specified path
profile whenever its own fixed PC domain remains nonempty.
No source CCO, SAP or word-exactness is needed for this implication. -/
theorem specified_edge_in_each_path_profile
    {x y : V} (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y hxy = some a)
    (hne : (fixedNetwork D ⟨x, y, hxy⟩).Nonempty)
    (p : SpecifiedPath D x y) :
    a ∈ PositiveWord.profile S p.word := by
  have hFixed : fixedNetwork D ⟨x, y, hxy⟩ =
      ({a} : S.Menu (D.vertexSort x) (D.vertexSort y)) :=
    fixedNetwork_eq_specified_singleton_of_nonempty D hxy a ha hne
  have hMem : a ∈ fixedNetwork D ⟨x, y, hxy⟩ := by
    rw [hFixed]
    exact Set.mem_singleton_iff.mpr rfl
  exact fixedNetwork_subset_path_profile D p hMem

/-- C12 cycle-cut semantic witness: the prescribed closing-edge atom
occurs on the endpoints of an ACTUAL represented path realization.
Since it is a diversity atom, the endpoints cannot collide, even
if the two named sorts are equal. This uses accepted original SAP
word semantics, not RAW equality as a STRONG menu. -/
theorem specified_edge_path_realizable_of_nonempty
    {G : Type*} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {x y : V} (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y hxy = some a)
    (hne : (fixedNetwork D ⟨x, y, hxy⟩).Nonempty)
    (p : SpecifiedPath D x y) :
    ∃ rx : X (D.vertexSort x), ∃ ry : X (D.vertexSort y),
      PositiveWord.represented S p.word rx ry ∧
      S.colour rx ry = some a := by
  exact (StrongExact.positive_profile_iff_represented S H sap
    p.word a).mp
      (specified_edge_in_each_path_profile D hxy a ha hne p)

/-- Every displayed fine edge has all its specified positive paths
jointly supported by that same old fine atom once PC has no zero. -/
theorem specified_edge_in_positivePathBound
    (hAll : ∀ p : DistinctPair V,
      (fixedNetwork D p).Nonempty)
    {x y : V} (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y hxy = some a) :
    a ∈ positivePathBound D x y := by
  intro p
  exact specified_edge_in_each_path_profile D
    hxy a ha (hAll ⟨x, y, hxy⟩) p

end CCO.StrongPC
