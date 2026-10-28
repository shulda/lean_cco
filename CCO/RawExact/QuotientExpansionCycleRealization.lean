import CCO.RawExact.QuotientExpansionDiagram
import CCO.RawExact.WalkReferenceColourTransport

/-!
# Actual raw cycle homomorphisms from marked quotient-edge witnesses

Choose real walks between the given marked representatives for every
word occurrence of every marked edge used by the cycle. Other words
retain their independent reference walks. The literal actual reference
colours are unchanged along each path, so the cycle is homomorphic in
the original source. No global quotient realization is assumed.
-/

universe u v w

namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))
variable (C : SimpleCycle (diagram S sort P hNonempty))

/-- The cycle traverses an actual private path edge belonging to the
indicated marked edge. Orientation of the formal cyclic traversal is
retained; words remain private independent occurrences. -/
def CycleUsesEdge (e : Edge n) : Prop :=
  ∃ (k : Fin C.length) (o : Occurrence S sort P)
    (p q : PathPosition S (word S sort P o)),
    pathAdjacent S (word S sort P o) p q ∧
    C.vertices k = atPosition S sort P o p ∧
    C.vertices (cyclicNext C.length_pos k) = atPosition S sort P o q ∧ o.1 = e

variable (b : ∀ m : Fin n, X (sort m))

private noncomputable def chosenLeft (o : Occurrence S sort P) : X (sort (left o.1)) := by
  classical
  exact if CycleUsesEdge S sort P hNonempty C o.1 then b (left o.1)
    else referenceLeft S sort P hNonempty o.1

private noncomputable def chosenRight (o : Occurrence S sort P) : X (sort (right o.1)) := by
  classical
  exact if CycleUsesEdge S sort P hNonempty C o.1 then b (right o.1)
    else referenceRight S sort P hNonempty o.1

variable (hEval : ∀ e, CycleUsesEdge S sort P hNonempty C e →
  evaluate S (P e) (b (left e)) (b (right e)))

private noncomputable def chosenWalk (o : Occurrence S sort P) :
    WordPath S (word S sort P o)
      (chosenLeft S sort P hNonempty C b o) (chosenRight S sort P hNonempty C b o) := by
  classical
  by_cases hUsed : CycleUsesEdge S sort P hNonempty C o.1
  · have hRelation := hEval o.1 hUsed (word S sort P o) (List.get_mem (P o.1) o.2)
    have path := Classical.choice ((wordPath_iff_relation S (word S sort P o) _ _).mpr hRelation)
    simpa only [chosenLeft, chosenRight, ite_eq_left hUsed] using path
  · simpa only [chosenLeft, chosenRight, ite_eq_right hUsed] using
      referenceWalk S sort P hNonempty o

private noncomputable def realizationImage : Vertex S sort P → Sigma X
  | .inl m => ⟨sort m, b m⟩
  | .inr ⟨o, p⟩ => wordPathPointAt S (chosenWalk S sort P hNonempty C b hEval o) p.1

private theorem realizationImage_sort (v : Vertex S sort P) :
    (realizationImage S sort P hNonempty C b hEval v).1 = vertexSort S sort P v := by
  cases v with
  | inl m => rfl
  | inr op =>
    rcases op with ⟨o, p⟩
    exact wordPathPointAt_sort S (chosenWalk S sort P hNonempty C b hEval o) p.1

private noncomputable def realizationPoint (v : Vertex S sort P) : X (vertexSort S sort P v) :=
  realizationImage_sort S sort P hNonempty C b hEval v ▸
    (realizationImage S sort P hNonempty C b hEval v).2

private theorem cast_point_tag {i : ι} (p : Sigma X) (h : p.1 = i) :
    (⟨i, h ▸ p.2⟩ : Sigma X) = p := by
  cases p with
  | mk j x =>
    change j = i at h
    cases h
    rfl

private theorem realizationPoint_tag (v : Vertex S sort P) :
    (⟨vertexSort S sort P v, realizationPoint S sort P hNonempty C b hEval v⟩ : Sigma X) =
      realizationImage S sort P hNonempty C b hEval v :=
  cast_point_tag _ (realizationImage_sort S sort P hNonempty C b hEval v)

private theorem realizationImage_atPosition
    (hPositive : ∀ o, 0 < diversityLength S (word S sort P o))
    (o : Occurrence S sort P)
    (hUsed : CycleUsesEdge S sort P hNonempty C o.1)
    (p : PathPosition S (word S sort P o)) :
    realizationImage S sort P hNonempty C b hEval (atPosition S sort P o p) =
      wordPathPointAt S (chosenWalk S sort P hNonempty C b hEval o) p := by
  classical
  by_cases hp0 : p.val = 0
  · have hp : p = pathStart S (word S sort P o) := Fin.ext hp0
    subst p
    rw [at_start, wordPathPointAt_start]
    simp only [realizationImage, mark, chosenLeft, ite_eq_left hUsed]
  · by_cases hpEnd : p.val = diversityLength S (word S sort P o)
    · have hp : p = pathFinish S (word S sort P o) := Fin.ext hpEnd
      subst p
      rw [at_finish S sort P o (hPositive o), wordPathPointAt_finish]
      simp only [realizationImage, mark, chosenRight, ite_eq_left hUsed]
    · rw [show atPosition S sort P o p = interior S sort P o ⟨p, hp0, hpEnd⟩ by
        simp only [atPosition, dite_eq_right hp0, dite_eq_right hpEnd]]
      rfl

include b hEval

/-- All source-coloured edges of this cycle are realized by the chosen
actual word walks. Source positivity is supplied by the canonical
quotient zero-word exclusion in the final C26/C27 instantiation. -/
theorem cycleHom_of_marked_edge_realization
    (hPositive : ∀ o, 0 < diversityLength S (word S sort P o)) : CycleHom C := by
  classical
  refine ⟨fun k => realizationPoint S sort P hNonempty C b hEval (C.vertices k), ?_⟩
  intro k a hEdge
  obtain ⟨o, p, q, hpq, hv, hw, hColour⟩ :=
    (diagram_edge_iff S sort P hNonempty _ _ (C.next_ne k) a).mp hEdge
  have hUsed : CycleUsesEdge S sort P hNonempty C o.1 :=
    ⟨k, o, p, q, hpq, hv, hw, rfl⟩
  have hTag :
      taggedColour S
        (⟨vertexSort S sort P (C.vertices k),
          realizationPoint S sort P hNonempty C b hEval (C.vertices k)⟩ : Sigma X)
        (⟨vertexSort S sort P (C.vertices (cyclicNext C.length_pos k)),
          realizationPoint S sort P hNonempty C b hEval
            (C.vertices (cyclicNext C.length_pos k))⟩ : Sigma X) =
        (⟨vertexSort S sort P (C.vertices k),
          vertexSort S sort P (C.vertices (cyclicNext C.length_pos k)), some a⟩ :
          Σ i : ι, Σ j : ι, Option (S.Atom i j)) := by
    rw [realizationPoint_tag, realizationPoint_tag]
    have hpImage := (congrArg (realizationImage S sort P hNonempty C b hEval) hv).trans
      (realizationImage_atPosition S sort P hNonempty C b hEval hPositive o hUsed p)
    have hqImage := (congrArg (realizationImage S sort P hNonempty C b hEval) hw).trans
      (realizationImage_atPosition S sort P hNonempty C b hEval hPositive o hUsed q)
    exact ((congrArg₂ (taggedColour S) hpImage hqImage).trans
      (wordPathPointAt_adjacent_colour_independent S (word S sort P o)
        (chosenWalk S sort P hNonempty C b hEval o)
        (referenceWalk S sort P hNonempty o) p q hpq)).trans hColour
  simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq, true_and,
    diagram, TypedAtomEdgeData.toPartialDiagram] using hTag

end CCO.RawExact.QuotientExpansion
