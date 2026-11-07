import CCO.OldIdempotentForest.VisibleDiagram

/-! Each actual local theta already has its original common-atom seed.
A specified cycle contained in that theta therefore has an actual
colour-preserving homomorphism, even if the WHOLE source is not completable. -/

universe u v w p q
namespace CCO.OldIdempotentForest
open CCO.StrongExact CCO.GuardedOldSeams CCO.GuardedTwoRoot
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {P : Type p} {K : Type q} [Finite P] [Finite K]
namespace RootWordGeometry
variable (R : RootWordSystem S P K) (seed : RootWordSeeds S R)

private theorem cast_symm_cancel {i j : ι} (h : i = j) (x : X j) :
    h ▸ (h.symm ▸ x) = x := by
  cases h
  rfl

noncomputable def seedReading (k : K) (z : thetaVertices S (R.words k)) :
    X (R.vertexSort (R.embed k z)) :=
  (R.embed_sort k z).symm ▸
    thetaFamilyLinePoint S (R.words k) (seed.left k) (seed.right k) (seed.lines k) z

theorem seedReading_colour (k : K) (z t : thetaVertices S (R.words k))
    (hzt : R.embed k z ≠ R.embed k t)
    (a : S.Atom (R.vertexSort (R.embed k z)) (R.vertexSort (R.embed k t)))
    (ha : (R.diagram seed).edge (R.embed k z) (R.embed k t) hzt = some a) :
    S.colour (seedReading R seed k z) (seedReading R seed k t) = some a := by
  let D := R.gluing seed
  have hLocal := (D.unionEdge_on_piece k z t hzt).symm.trans ha
  have hne : z ≠ t := fun h => hzt (congrArg (R.embed k) h)
  change transportAtomOption S (R.embed_sort k z) (R.embed_sort k t)
    ((thetaEdgesOfLiteralLines S (R.words k) (seed.left k) (seed.right k) (seed.lines k)).edge z t hne) =
      some a at hLocal
  apply transportAtomOption_colour S (R.embed_sort k z) (R.embed_sort k t) _
    (seedReading R seed k z) (seedReading R seed k t) ?_ a hLocal
  intro b hb
  have h := (thetaHomOfLiteralLines S (R.words k) (seed.left k) (seed.right k)
    (seed.lines k)).preserves_edge z t hne b hb
  change S.colour
    (thetaFamilyLinePoint S (R.words k) (seed.left k) (seed.right k) (seed.lines k) z)
    (thetaFamilyLinePoint S (R.words k) (seed.left k) (seed.right k) (seed.lines k) t) = some b at h
  simpa only [seedReading,cast_symm_cancel] using h

theorem seedReading_at_vertices (k : K) (z t : thetaVertices S (R.words k))
    {x y : R.Vertex} (hx : R.embed k z = x) (hy : R.embed k t = y) (hxy : x ≠ y)
    (a : S.Atom (R.vertexSort x) (R.vertexSort y))
    (ha : (R.diagram seed).edge x y hxy = some a) :
    S.colour ((congrArg R.vertexSort hx) ▸ seedReading R seed k z)
      ((congrArg R.vertexSort hy) ▸ seedReading R seed k t) = some a := by
  subst x
  subst y
  exact seedReading_colour R seed k z t hxy a ha

/-- A local preimage is chosen only for reading the already specified
cycle. Its exact original labels are retained via the actual gluing edge. -/
theorem cycleHom_of_piece_cover (k : K) (C : SimpleCycle (R.diagram seed))
    (cover : ∀ p : Fin C.length, ∃ z, R.embed k z = C.vertices p) : CycleHom C := by
  classical
  let z (p : Fin C.length) := (cover p).choose
  have hz (p : Fin C.length) : R.embed k (z p) = C.vertices p := (cover p).choose_spec
  let point (p : Fin C.length) : X (R.vertexSort (C.vertices p)) :=
    (congrArg R.vertexSort (hz p)) ▸ seedReading R seed k (z p)
  refine ⟨point,?_⟩
  intro p a ha
  exact seedReading_at_vertices R seed k (z p) (z (cyclicNext C.length_pos p))
    (hz p) (hz (cyclicNext C.length_pos p)) (C.next_ne p) a ha

/-- In the ACTUAL seeded graph, the one-template bad-cycle branch is
impossible. This proves the source's bounded-template case without adding
any assumption that the surrounding hidden source is completable. -/
theorem bad_cycle_not_internal (C : SimpleCycle (R.diagram seed)) (hBad : ¬ CycleHom C) :
    ¬ ∃ k : K, (cycleOfSpecified R seed C).ContainedInTheta k := by
  rintro ⟨k,hk⟩
  apply hBad
  apply cycleHom_of_piece_cover R seed k C
  intro p
  obtain ⟨⟨l,b⟩,hOwner,j,hj⟩ := hk p
  change l = k at hOwner
  subst l
  exact ⟨thetaBranchPosition S (R.words k) b
    ((wordPositionEquiv S ((R.words k).get b)).symm j),hj⟩

end RootWordGeometry
end CCO.OldIdempotentForest
