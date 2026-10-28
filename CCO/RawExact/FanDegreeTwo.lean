import CCO.RawExact.FanInteriorIsolation

/-!
# B002 C12/C26: exact degree two of private fan interiors

A private vertex has precisely the preceding and following position
of its own occurrence as its two graph neighbours, and those are
distinct. This is the direct fan-graph counterpart of the elementary
private-path theorem used in the pinned N05 and N10 cycle arguments.
In particular a simple cycle cannot switch to another word path
at a private interior.

The result concerns FORMAL vertices, not injectivity of real walks.
No source CCO or Helly provider appears in the hypotheses.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Every true private interior has exactly two distinct neighbours
and all adjacent fan vertices lie among those two. -/
theorem privateFanInterior_exactly_two_neighbours
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o) :
    ∃ before after : PathPosition S (occurrenceWord S D o),
      before ≠ after ∧
      privateFanAdjacent S D centres
        (privateFanInterior S D centres o p)
        (privateFanAtWordPosition S D centres o before) ∧
      privateFanAdjacent S D centres
        (privateFanInterior S D centres o p)
        (privateFanAtWordPosition S D centres o after) ∧
      (∀ v : PrivateFanVertex S D centres,
        privateFanAdjacent S D centres
          (privateFanInterior S D centres o p) v →
        v = privateFanAtWordPosition S D centres o before ∨
        v = privateFanAtWordPosition S D centres o after) := by
  have hStart : 0 < p.1.val := by
    have hpNonzero : p.1.val ≠ 0 := p.property.1
    omega
  have hFinish : p.1.val < diversityLength S (occurrenceWord S D o) := by
    have hpLt := p.1.isLt
    have hpNeEnd := p.property.2
    omega
  obtain ⟨before, after, _, _, hDistinct, hBefore, hAfter, hOnly⟩ :=
    pathInterior_exactly_two_neighbours S
      (occurrenceWord S D o) p.1 hStart hFinish
  refine ⟨before, after, hDistinct, ?_, ?_, ?_⟩
  · have hAdj :=
      privateFan_path_edge S D centres o before p.1 hBefore
    have hP : privateFanAtWordPosition S D centres o p.1 =
      privateFanInterior S D centres o p := by
      simpa using privateFanAt_interior S D centres o p.1
        p.property.1 p.property.2
    rw [hP] at hAdj
    exact (privateFanAdjacent_symm S D centres _ _).mp hAdj
  · have hAdj :=
      privateFan_path_edge S D centres o p.1 after hAfter
    have hP : privateFanAtWordPosition S D centres o p.1 =
      privateFanInterior S D centres o p := by
      simpa using privateFanAt_interior S D centres o p.1
        p.property.1 p.property.2
    rwa [hP] at hAdj
  · intro v hAdj
    obtain ⟨q, hpq, hv⟩ :=
      privateFanInterior_neighbours_only_own_path S D centres o p v hAdj
    rcases hOnly q hpq with hq | hq
    · left
      rw [hv, hq]
    · right
      rw [hv, hq]

end CCO.RawExact
