import CCO.StrongExact.ThetaArcs

/-!
# C07 theta arc candidates are closed under actual atomic converse

The finite list of theta arcs contains every private forward
positive-word letter AND its original converse, never any fake
equality or diagonal edge. Double reversal is an involution by
the accepted `AtomicSource.conv_invol` law.

This is the concrete reversal half of the B001 PartialDiagram
edge-reverse obligation. Turning the list into a single-valued edge
function still requires the separate no-conflicting-parallel-arcs
theorem on the long private theta graph.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Converse is a genuine involution on typed irreflexive atomic arcs. -/
theorem ThetaArc.reverse_reverse
    {ws : List (PositiveWord S i j)}
    (arc : ThetaArc S ws) :
    arc.reverse.reverse = arc := by
  cases arc with
  | mk src dst ne atom =>
      simp [ThetaArc.reverse, S.conv_invol]

/-- Every private forward original diversity edge appears in the
complete finite theta arc list. -/
theorem thetaForwardArc_mem_theta
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) :
    thetaForwardArc S ws b e ∈ thetaArcs S ws := by
  unfold thetaArcs
  apply List.mem_flatMap.mpr
  refine ⟨b, ?_, ?_⟩
  · simp
  · apply List.mem_flatMap.mpr
    refine ⟨thetaForwardArc S ws b e,
      thetaForwardArc_mem_branch S ws b e, ?_⟩
    simp

/-- The ENTIRE finite candidate list, not only one branch, remains
closed under actual converse. A future B001 diagram constructed
from this list must reuse precisely that converse law. -/
theorem thetaArcs_reverse_closed
    (ws : List (PositiveWord S i j))
    (arc : ThetaArc S ws)
    (hArc : arc ∈ thetaArcs S ws) :
    arc.reverse ∈ thetaArcs S ws := by
  unfold thetaArcs at hArc ⊢
  obtain ⟨b, hb, hBranch⟩ := List.mem_flatMap.mp hArc
  obtain ⟨candidate, hCandidate, hMember⟩ :=
    List.mem_flatMap.mp hBranch
  have hCases : arc = candidate ∨ arc = candidate.reverse := by
    simpa only [List.mem_cons, List.mem_singleton, or_false]
      using hMember
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨candidate, hCandidate, ?_⟩
  rcases hCases with hForward | hBackward
  · subst arc
    simp
  · subst arc
    rw [ThetaArc.reverse_reverse S candidate]
    simp

end CCO.StrongExact
