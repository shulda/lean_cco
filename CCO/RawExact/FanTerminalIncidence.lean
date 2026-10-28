import CCO.RawExact.FanCentreBoundary
import CCO.RawExact.FanDegreeTwo
import Mathlib.Tactic

/-!
# B002 C12: complete terminal incidence for private fan interiors

Private RAW word interiors do not touch other words or the old-centre
graph. This module refines that isolation: a private interior is
adjacent to the global fan root exactly at its first interior
position and to an actual marked centre exactly at its LAST interior
position, provided the marked centre is its own literal tagged
old centre.

In particular no private word edge can connect two old marked
centres. The ONLY such edges come from the complete old real
centre diagram. Identity letters are not made into graph edges.
These are unconditional formal combinatorial facts, not a source
CCO or Helly hypothesis.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- A genuine interior of occurrence `o` sees the one formal root
iff it is at diversity position 1. All other positions are too far
away, even when the real source walk revisits an earlier point. -/
theorem privateFan_interior_root_adjacent_iff_first
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o) :
    privateFanAdjacent S D centres
      (privateFanInterior S D centres o p)
      (privateFanRoot S D centres) ↔ p.1.val = 1 := by
  constructor
  · intro hGraph
    obtain ⟨q, hStep, hRoot⟩ :=
      privateFanInterior_neighbours_only_own_path S D centres o p
        (privateFanRoot S D centres) hGraph
    have hq : q = pathStart S (occurrenceWord S D o) :=
      (privateFanAt_is_root_iff_start S D centres o q).mp hRoot.symm
    rw [hq] at hStep
    have hBack : pathAdjacent S (occurrenceWord S D o)
        (pathStart S (occurrenceWord S D o)) p.1 :=
      (pathAdjacent_symm S (occurrenceWord S D o) _ _).mp hStep
    exact (pathAdjacent_start_iff S (occurrenceWord S D o) p.1).mp hBack
  · intro hFirst
    have hStep : pathAdjacent S (occurrenceWord S D o)
        (pathStart S (occurrenceWord S D o)) p.1 :=
      (pathAdjacent_start_iff S (occurrenceWord S D o) p.1).mpr hFirst
    have hGraph := privateFan_path_edge S D centres o
      (pathStart S (occurrenceWord S D o)) p.1 hStep
    rw [privateFanAt_start S D centres o,
      privateFanAt_interior S D centres o p.1
        p.property.1 p.property.2] at hGraph
    exact (privateFanAdjacent_symm S D centres _ _).mp hGraph

/-- A private interior only touches an old centre on the
penultimate path position, and that centre MUST be this
occurrence's literal actual tagged centre. No other old centre
can acquire an accidental edge through repeated sort names. -/
theorem privateFan_interior_centre_adjacent_iff_last
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o)
    (c : DistinctCentres sort centres) :
    privateFanAdjacent S D centres
      (privateFanInterior S D centres o p)
      (privateFanCentre S D centres c) ↔
      toDistinctCentre sort centres o.1 = c ∧
        p.1.val + 1 =
          diversityLength S (occurrenceWord S D o) := by
  constructor
  · intro hGraph
    obtain ⟨q, hStep, hCentre⟩ :=
      privateFanInterior_neighbours_only_own_path S D centres o p
        (privateFanCentre S D centres c) hGraph
    obtain ⟨_, hLast, hc⟩ :=
      privateFanAt_old_centre_only_at_finish S D centres o q c
        hCentre.symm
    rw [hLast] at hStep
    exact ⟨hc, (pathAdjacent_finish_iff S
      (occurrenceWord S D o) p.1).mp hStep⟩
  · rintro ⟨hc, hLast⟩
    have hPositive :
        0 < diversityLength S (occurrenceWord S D o) := by
      omega
    have hStep : pathAdjacent S (occurrenceWord S D o)
        p.1 (pathFinish S (occurrenceWord S D o)) :=
      (pathAdjacent_finish_iff S (occurrenceWord S D o) p.1).mpr hLast
    have hGraph := privateFan_path_edge S D centres o p.1
      (pathFinish S (occurrenceWord S D o)) hStep
    rw [privateFanAt_interior S D centres o p.1
      p.property.1 p.property.2,
      privateFanAt_finish S D centres o hPositive, hc] at hGraph
    exact hGraph

/-- There are NO direct private-word edges between two marked old
centres. Their entire graph is the actual induced old-colour
diagram; only root--centre direct private spokes can overlap. -/
theorem privateFan_path_not_between_centres
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c d : DistinctCentres sort centres) :
    ¬ privateFanPathAdjacent S D centres
      (privateFanCentre S D centres c)
      (privateFanCentre S D centres d) := by
  rintro ⟨o, p, q, hStep, hc, hd⟩
  obtain ⟨_, hp, _⟩ :=
    privateFanAt_old_centre_only_at_finish S D centres o p c hc.symm
  obtain ⟨_, hq, _⟩ :=
    privateFanAt_old_centre_only_at_finish S D centres o q d hd.symm
  rw [hp, hq] at hStep
  exact (pathAdjacent_irrefl S (occurrenceWord S D o)
    (pathFinish S (occurrenceWord S D o))) hStep

end CCO.RawExact
