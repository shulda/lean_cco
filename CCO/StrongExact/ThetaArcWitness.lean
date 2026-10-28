import CCO.StrongExact.ThetaArcClosure
import CCO.StrongExact.ThetaDisjoint

/-!
# C07: every theta arc belongs to one private branch

The literal finite candidate list cannot contain an edge joining
two private interior vertices of *different* word occurrences.
This is independent of source SAP, homomorphic CCO, and profiles:
a private point is tagged by its unique word-occurrence index.

The theorem does not yet classify simple cycles or assert that the
candidate arc list is a single-valued B001 PartialDiagram.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- An arc enumerated in one private branch is genuinely the arc of
one original positive word letter. -/
theorem thetaBranchArc_exists_edge
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (candidate : ThetaArc S ws)
    (h : candidate ∈ thetaBranchArcs S ws b) :
    ∃ e : wordEdgeIndex S (ws.get b),
      candidate = thetaForwardArc S ws b e := by
  classical
  unfold thetaBranchArcs at h
  obtain ⟨e, _, heq⟩ := List.mem_map.mp h
  exact ⟨e, heq.symm⟩

/-- Exhaustive representation of every finite candidate:
one genuine private letter or its actual original converse. -/
theorem thetaArc_exists_edge
    (ws : List (PositiveWord S i j))
    (arc : ThetaArc S ws) (h : arc ∈ thetaArcs S ws) :
    ∃ b : Fin ws.length, ∃ e : wordEdgeIndex S (ws.get b),
      arc = thetaForwardArc S ws b e ∨
      arc = (thetaForwardArc S ws b e).reverse := by
  unfold thetaArcs at h
  obtain ⟨b, _, hBranch⟩ := List.mem_flatMap.mp h
  obtain ⟨candidate, hc, hPick⟩ := List.mem_flatMap.mp hBranch
  obtain ⟨e, heq⟩ := thetaBranchArc_exists_edge S ws b candidate hc
  have hCases : arc = candidate ∨ arc = candidate.reverse := by
    simpa using hPick
  refine ⟨b, e, ?_⟩
  rcases hCases with hh | hh
  · exact Or.inl (hh.trans heq)
  · exact Or.inr (hh.trans (congrArg (fun t : ThetaArc S ws => t.reverse) heq))

/-- The two endpoints of an enumerated directed arc lie on one and
the SAME originally indexed private word line, either forward or
backwards. -/
theorem thetaArc_endpoints_on_branch
    (ws : List (PositiveWord S i j))
    (arc : ThetaArc S ws) (h : arc ∈ thetaArcs S ws) :
    ∃ b : Fin ws.length, ∃ e : wordEdgeIndex S (ws.get b),
      ((arc.src = thetaBranchEdgeSource S ws b e ∧
        arc.dst = thetaBranchEdgeTarget S ws b e) ∨
       (arc.src = thetaBranchEdgeTarget S ws b e ∧
        arc.dst = thetaBranchEdgeSource S ws b e)) := by
  obtain ⟨b, e, he | he⟩ := thetaArc_exists_edge S ws arc h
  · exact ⟨b, e, Or.inl ⟨congrArg ThetaArc.src he,
      congrArg ThetaArc.dst he⟩⟩
  · exact ⟨b, e, Or.inr ⟨by simpa [ThetaArc.reverse] using
        congrArg ThetaArc.src he,
      by simpa [ThetaArc.reverse] using congrArg ThetaArc.dst he⟩⟩

/-- A private interior point can lie in a different branch's embedded
formal line only when the indices agree. It cannot masquerade as
either of that line's two global roots. -/
theorem private_embedded_position_same_branch
    (ws : List (PositiveWord S i j))
    (b c : Fin ws.length) (p : wordInterior S (ws.get b))
    (q : wordPositions S (ws.get c))
    (he : thetaBranchPosition S ws b p.val =
      thetaBranchPosition S ws c q) : b = c := by
  classical
  by_cases hSource : q = wordSource S (ws.get c)
  · rw [hSource, thetaBranchPosition_source S ws c,
      thetaBranchPosition_interior S ws b p] at he
    cases he
  · by_cases hTarget : q = wordTarget S (ws.get c)
    · rw [hTarget, thetaBranchPosition_target S ws c,
        thetaBranchPosition_interior S ws b p] at he
      cases he
    · let q' : wordInterior S (ws.get c) :=
        ⟨q, hSource, hTarget⟩
      have hpos : thetaBranchPosition S ws c q =
          (.inr ⟨c, q'⟩ : thetaVertices S ws) :=
        thetaBranchPosition_interior S ws c q'
      rw [thetaBranchPosition_interior S ws b p, hpos] at he
      have hSigma : (⟨b, p⟩ :
          Σ d : Fin ws.length, wordInterior S (ws.get d)) =
          ⟨c, q'⟩ := Sum.inr.inj he
      exact congrArg Sigma.fst hSigma

/-- An old specified edge can never connect interiors from two
different private branches, even if their sort tags agree. -/
theorem thetaArc_no_cross_private
    (ws : List (PositiveWord S i j))
    (arc : ThetaArc S ws) (h : arc ∈ thetaArcs S ws)
    (b c : Fin ws.length) (hbc : b ≠ c)
    (p : wordInterior S (ws.get b))
    (q : wordInterior S (ws.get c)) :
    ¬ (arc.src = thetaBranchPosition S ws b p.val ∧
       arc.dst = thetaBranchPosition S ws c q.val) := by
  rintro ⟨hs, ht⟩
  obtain ⟨d, e, hForward | hReverse⟩ :=
    thetaArc_endpoints_on_branch S ws arc h
  · have hbd : b = d :=
      private_embedded_position_same_branch S ws b d p
        (wordEdgeSource S (ws.get d) e) (by
          calc
            thetaBranchPosition S ws b p.val = arc.src := hs.symm
            _ = thetaBranchEdgeSource S ws d e := hForward.1
            _ = _ := rfl)
    have hcd : c = d :=
      private_embedded_position_same_branch S ws c d q
        (wordEdgeTarget S (ws.get d) e) (by
          calc
            thetaBranchPosition S ws c q.val = arc.dst := ht.symm
            _ = thetaBranchEdgeTarget S ws d e := hForward.2
            _ = _ := rfl)
    exact hbc (hbd.trans hcd.symm)
  · have hbd : b = d :=
      private_embedded_position_same_branch S ws b d p
        (wordEdgeTarget S (ws.get d) e) (by
          calc
            thetaBranchPosition S ws b p.val = arc.src := hs.symm
            _ = thetaBranchEdgeTarget S ws d e := hReverse.1
            _ = _ := rfl)
    have hcd : c = d :=
      private_embedded_position_same_branch S ws c d q
        (wordEdgeSource S (ws.get d) e) (by
          calc
            thetaBranchPosition S ws c q.val = arc.dst := ht.symm
            _ = thetaBranchEdgeSource S ws d e := hReverse.2
            _ = _ := rfl)
    exact hbc (hbd.trans hcd.symm)

end CCO.StrongExact
