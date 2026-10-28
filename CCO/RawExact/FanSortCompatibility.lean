import CCO.RawExact.PrivateFanGluing
import CCO.RawExact.ReferencePositions
import CCO.RawExact.PathEndpoints
import Mathlib.Tactic

/-!
# B002 C12: original-sort compatibility of glued private fan paths

Each formal path vertex retains precisely the original named sort
at its position of the RAW word. At the start the sort is the
global target sort; at the finish it is the centre's ORIGINAL sort.
The internal positions use their actual old typed word traces.
Consequently reference old point colours have exactly the endpoint
sorts required to label finite fan edges. No quotient sorts or
independent liftings are introduced.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- The quotient identifying only the path endpoints, NOT the
internal private vertices, preserves every original vertex sort. -/
theorem privateFanAtWordPosition_sort
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o)) :
    privateFanSort S D centres
      (privateFanAtWordPosition S D centres o p) =
    pathSortAt S (occurrenceWord S D o) p := by
  by_cases hStart : p.val = 0
  · have hp : p = pathStart S (occurrenceWord S D o) :=
      Fin.ext hStart
    rw [hp, privateFanAt_start S D centres o,
        privateFanSort_root S D centres]
    exact (pathSortAt_start S (occurrenceWord S D o)).symm
  · by_cases hFinish :
        p.val = diversityLength S (occurrenceWord S D o)
    · have hp : p = pathFinish S (occurrenceWord S D o) :=
        Fin.ext hFinish
      have hPositive : 0 < diversityLength S (occurrenceWord S D o) := by
        omega
      rw [hp, privateFanAt_finish S D centres o hPositive,
          privateFanSort_occurrence_centre S D centres o.1]
      exact (pathSortAt_finish S (occurrenceWord S D o)).symm
    · rw [privateFanAt_interior S D centres o p hStart hFinish]
      rfl

/-- The original sort of an independently chosen actual real
reference point matches the FORMAL sort of its glued fan vertex.
Thus edge colours in the source's real atomic palette are typed
correctly even when the centre sorts vary. -/
theorem privateFan_referencePoint_sort
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o)) :
    privateFanSort S D centres
      (privateFanAtWordPosition S D centres o p) =
    (referencePointAt S H D centres o p).1 := by
  calc
    privateFanSort S D centres
        (privateFanAtWordPosition S D centres o p) =
      pathSortAt S (occurrenceWord S D o) p :=
        privateFanAtWordPosition_sort S D centres o p
    _ = (referencePointAt S H D centres o p).1 :=
      (referencePointAt_sort S H D centres o p).symm

end CCO.RawExact
