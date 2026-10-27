import CCO.StrongExact.ThetaVertices

/-!
# C07 pure theta geometry: distinct private interiors and fixed roots

The two shared theta roots are distinct even if they have the same
named sort. Every internal vertex carries its original branch
index and therefore is distinct from both roots and every
internal vertex belonging to a DIFFERENT branch. No spurious
collision, shared extra vertex, diagonal pseudoedge or assumption
about original group action is introduced.

These are purely formal vertex facts. The specified edge and
simple-cycle classification follows in separate modules.
-/

universe u v a

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, a} ι X)
variable {i j : ι}

/-- Every genuine private interior point is distinct from the
literal left theta root (which may have the same named sort). -/
theorem thetaLeft_ne_private
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length) (p : wordInterior S (ws.get b)) :
    thetaLeft S ws ≠ thetaBranchPosition S ws b p.val := by
  rw [thetaBranchPosition_interior S ws b p]
  intro h
  cases h

/-- Every genuine private interior point is distinct from the
literal right theta root. -/
theorem thetaRight_ne_private
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length) (p : wordInterior S (ws.get b)) :
    thetaRight S ws ≠ thetaBranchPosition S ws b p.val := by
  rw [thetaBranchPosition_interior S ws b p]
  intro h
  cases h

/-- Two private points from different formal word occurrences are
distinct, even if the positive words and named sorts happen
to be syntactically identical. -/
theorem thetaDifferentBranches_disjoint
    (ws : List (PositiveWord S i j))
    (b c : Fin ws.length) (hbc : b ≠ c)
    (p : wordInterior S (ws.get b))
    (q : wordInterior S (ws.get c)) :
    thetaBranchPosition S ws b p.val ≠
      thetaBranchPosition S ws c q.val := by
  rw [thetaBranchPosition_interior S ws b p,
    thetaBranchPosition_interior S ws c q]
  intro h
  have heq : (⟨b, p⟩ : Σ t : Fin ws.length,
      wordInterior S (ws.get t)) = ⟨c, q⟩ :=
    Sum.inr.inj h
  exact hbc (congrArg Sigma.fst heq)

end CCO.StrongExact
