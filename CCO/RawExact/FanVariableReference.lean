import CCO.RawExact.FanTwoWalkReplacement
import CCO.RawExact.FanNonrootRealization
import Mathlib.Tactic

/-!
# B002 C12: actual old-point map from arbitrary per-occurrence RAW walks

A finite family of actual represented word walks gives genuine old
points for every private interior and literal old values for every
marked centre. The ONE formal root is given an independently chosen
source point. No condition that every private walk start there is
assumed: only walks specifically selected for a cycle need share it.

Every genuine edge wholly away from the formal root is represented
by a genuine original source diversity atom under this map, even if
the word witnesses are different from those chosen for the permanent
fan diagram. Comparing their exact atom labels is a separate theorem.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Original point assignment determined by a family of true RAW
word-walk witnesses plus a specified value for the one formal root. -/
def privateFanVariableReference
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root) :
    PrivateFanVertex S D centres → Sigma X
  | .inl none => ⟨root, xRoot⟩
  | .inl (some c) => c.val
  | .inr ⟨o,p⟩ => wordPathPointAt S (choice o).2 p.1

/-- The named original sort of every formal private-fan vertex
is preserved by any family of actual typed RAW word paths. -/
theorem privateFanVariableReference_sort
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (v : PrivateFanVertex S D centres) :
    (privateFanVariableReference S D centres choice xRoot v).1 =
      privateFanSort S D centres v := by
  cases v with
  | inl oc =>
      cases oc with
      | none => rfl
      | some c => rfl
  | inr op =>
      rcases op with ⟨o,p⟩
      exact wordPathPointAt_sort S (choice o).2 p.1

/-- Every original marked centre is kept literally fixed. -/
theorem privateFanVariableReference_centre
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (c : DistinctCentres sort centres) :
    privateFanVariableReference S D centres choice xRoot
      (privateFanCentre S D centres c) = c.val := rfl

/-- On every nonroot path position, the fan variable assignment
is exactly the corresponding old real point of that occurrence's
independently selected represented RAW walk. -/
theorem privateFanVariableReference_at_nonroot
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o))
    (hp : p.val ≠ 0) :
    privateFanVariableReference S D centres choice xRoot
      (privateFanAtWordPosition S D centres o p) =
      wordPathPointAt S (choice o).2 p := by
  by_cases hEnd : p.val = diversityLength S (occurrenceWord S D o)
  · have hpFin : p = pathFinish S (occurrenceWord S D o) :=
      Fin.ext hEnd
    have hPos : 0 < diversityLength S (occurrenceWord S D o) := by
      omega
    rw [hpFin, privateFanAt_finish S D centres o hPos]
    change taggedCentre sort centres o.1 =
      wordPathPointAt S (choice o).2
        (pathFinish S (occurrenceWord S D o))
    exact (wordPathPointAt_finish S (choice o).2).symm
  · rw [privateFanAt_interior S D centres o p hp hEnd]
    rfl

/-- Genuine old diversity edges of any chosen word path remain
genuine in the single variable fan reference assignment, as long
as neither endpoint is the formal root. -/
theorem privateFanVariableReference_nonroot_edge_genuine
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hp : p.val ≠ 0) (hq : q.val ≠ 0)
    (hpq : pathAdjacent S (occurrenceWord S D o) p q) :
    GenuineEdge S
      (privateFanVariableReference S D centres choice xRoot
        (privateFanAtWordPosition S D centres o p))
      (privateFanVariableReference S D centres choice xRoot
        (privateFanAtWordPosition S D centres o q)) := by
  rw [privateFanVariableReference_at_nonroot S D centres choice xRoot o p hp,
    privateFanVariableReference_at_nonroot S D centres choice xRoot o q hq]
  exact wordPathPointAt_genuine_adjacent S (choice o).2 p q hpq

/-- A selected occurrence whose old RAW walk starts at the
chosen global root has its first formal path position mapped
to precisely that global original point (no assertion is made
about the first positions of any other word occurrence). -/
theorem privateFanVariableReference_at_start
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (o : WordOccurrence S D)
    (hRoot : (choice o).1 = xRoot) :
    privateFanVariableReference S D centres choice xRoot
      (privateFanAtWordPosition S D centres o
        (pathStart S (occurrenceWord S D o))) =
      wordPathPointAt S (choice o).2
        (pathStart S (occurrenceWord S D o)) := by
  rw [privateFanAt_start S D centres o]
  change (⟨root, xRoot⟩ : Sigma X) =
    wordPathPointAt S (choice o).2
      (pathStart S (occurrenceWord S D o))
  rw [wordPathPointAt_start S (choice o).2, hRoot]

end CCO.RawExact
