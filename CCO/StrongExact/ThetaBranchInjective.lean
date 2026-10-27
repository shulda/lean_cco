import CCO.StrongExact.ThetaDisjoint

/-!
# C07: each private typed positive-word branch embeds injectively

Only the FIRST and LAST positions of a branch map to the two
shared theta roots; every intermediate position has its own
branch-indexed private point. This map must be injective even if
the two endpoint SORT LABELS coincide. The proof uses the
accepted finite dependent vertex construction and its concrete
private-interior disjointness lemmas, without any CCO/SAP axioms.

Injectivity immediately guarantees that each typed diversity letter
remains an edge between genuinely distinct FORMAL vertices in the
partial theta diagram, rather than a fake identity edge.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- The literal embedding of a single branch has no collisions,
including on positive words that start and end in the same named sort. -/
theorem thetaBranchPosition_injective
    (ws : List (PositiveWord S i j)) (b : Fin ws.length) :
    Function.Injective (thetaBranchPosition S ws b) := by
  classical
  let w := ws.get b
  have hCases (p : wordPositions S w) :
      p = wordSource S w ∨
      p = wordTarget S w ∨
      ∃ t : wordInterior S w, t.val = p := by
    by_cases hs : p = wordSource S w
    · exact Or.inl hs
    · by_cases ht : p = wordTarget S w
      · exact Or.inr (Or.inl ht)
      · exact Or.inr (Or.inr ⟨⟨p, hs, ht⟩, rfl⟩)
  intro p q he
  rcases hCases p with hp0 | hp1 | ⟨tp, htp⟩
  · rcases hCases q with hq0 | hq1 | ⟨tq, htq⟩
    · exact hp0.trans hq0.symm
    · exfalso
      rw [hp0, thetaBranchPosition_source S ws b,
        hq1, thetaBranchPosition_target S ws b] at he
      exact (thetaLeft_ne_right S ws) he
    · exfalso
      rw [hp0, thetaBranchPosition_source S ws b,
        ← htq, thetaBranchPosition_interior S ws b tq] at he
      exact (thetaLeft_ne_private S ws b tq) he
  · rcases hCases q with hq0 | hq1 | ⟨tq, htq⟩
    · exfalso
      rw [hp1, thetaBranchPosition_target S ws b,
        hq0, thetaBranchPosition_source S ws b] at he
      exact (thetaLeft_ne_right S ws) he.symm
    · exact hp1.trans hq1.symm
    · exfalso
      rw [hp1, thetaBranchPosition_target S ws b,
        ← htq, thetaBranchPosition_interior S ws b tq] at he
      exact (thetaRight_ne_private S ws b tq) he
  · rcases hCases q with hq0 | hq1 | ⟨tq, htq⟩
    · exfalso
      rw [← htp, thetaBranchPosition_interior S ws b tp,
        hq0, thetaBranchPosition_source S ws b] at he
      exact (thetaLeft_ne_private S ws b tp) he.symm
    · exfalso
      rw [← htp, thetaBranchPosition_interior S ws b tp,
        hq1, thetaBranchPosition_target S ws b] at he
      exact (thetaRight_ne_private S ws b tp) he.symm
    · rw [← htp, thetaBranchPosition_interior S ws b tp,
        ← htq, thetaBranchPosition_interior S ws b tq] at he
      have hSig :
          (⟨b, tp⟩ : Σ t : Fin ws.length,
            wordInterior S (ws.get t)) =
          (⟨b, tq⟩ : Σ t : Fin ws.length,
            wordInterior S (ws.get t)) := Sum.inr.inj he
      have hpq : tp = tq := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and]
          using hSig
      exact htp.symm.trans ((congrArg Subtype.val hpq).trans htq)

end CCO.StrongExact
