import CCO.RawExact.FanHomWordTrace
import CCO.RawExact.RealTraceEndpoints
import Lean.Elab.Tactic.Omega

/-!
# B002 C13: literal original endpoints of completed private-fan word traces

The full source CCO homomorphism maps the one formal fan root
and every distinct tagged old centre to actual original-sort points.
For any positive-length occurrence, its finite trace starts at
the global root image and ENDS at that occurrence's actual
marked-centre image. Equality letters have already disappeared
as edges; a positive walk may still have a diagonal output.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem privateFanHomWordTrace_start
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D) :
    (privateFanHomWordTrace S H D centres f o)[0]'(by
      rw [privateFanHomWordTrace_length S H D centres f o]
      omega) =
      (⟨root, f.point (privateFanRoot S D centres)⟩ : Sigma X) := by
  have hAt := privateFanHomWordTrace_get S H D centres f o
    (pathStart S (occurrenceWord S D o))
  rw [privateFanAt_start S D centres o] at hAt
  simpa only [pathStart, privateFanSort_root S D centres] using hAt

theorem privateFanHomWordTrace_finish
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D)
    (hPos : 0 < diversityLength S (occurrenceWord S D o)) :
    (privateFanHomWordTrace S H D centres f o)[diversityLength S (occurrenceWord S D o)]'(by
        rw [privateFanHomWordTrace_length S H D centres f o]
        omega) =
      (⟨sort o.1,
        f.point (privateFanCentre S D centres
          (toDistinctCentre sort centres o.1))⟩ : Sigma X) := by
  have hAt := privateFanHomWordTrace_get S H D centres f o
    (pathFinish S (occurrenceWord S D o))
  rw [privateFanAt_finish S D centres o hPos] at hAt
  simpa only [pathFinish, privateFanSort_occurrence_centre S D centres o.1]
    using hAt

end CCO.RawExact
