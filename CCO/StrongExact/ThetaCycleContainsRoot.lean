import Mathlib.Data.Finset.Max
import CCO.StrongExact.ThetaCycleLocal
import CCO.StrongExact.ThetaPrivateRankReadout
import CCO.StrongExact.ThetaPrivateConnectivity

/-!
# C07: a hard-theta simple cycle must visit a shared root

Assume a specified simple cycle misses both formal roots. Every
cycle position is then an original private theta vertex with a
well-defined finite word rank. Pick a vertex of minimum such rank.
The independently PROVED local cycle rule forces either its cyclic
predecessor or its cyclic successor to have strictly smaller rank,
contradicting minimality.

This is the first genuinely global finite simple-cycle theorem of
the hard theta, but does not yet claim both roots or precisely two
whole positive-word branches.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_contains_root
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    ∃ p : Fin C.length,
      C.vertices p = thetaLeft S ws ∨
        C.vertices p = thetaRight S ws := by
  classical
  by_contra hNo
  have hNoRoot (p : Fin C.length) :
      C.vertices p ≠ thetaLeft S ws ∧
      C.vertices p ≠ thetaRight S ws := by
    constructor
    · intro h
      exact hNo ⟨p, Or.inl h⟩
    · intro h
      exact hNo ⟨p, Or.inr h⟩
  have hPrivate (p : Fin C.length) :
      ∃ x : PrivateThetaVertex S ws,
        C.vertices p = (.inr x : thetaVertices S ws) := by
    cases hp : C.vertices p with
    | inl x =>
        cases x with
        | false =>
            exact False.elim ((hNoRoot p).1 (by simpa [thetaLeft] using hp))
        | true =>
            exact False.elim ((hNoRoot p).2 (by simpa [thetaRight] using hp))
    | inr x => exact ⟨x,rfl⟩
  let priv (p : Fin C.length) : PrivateThetaVertex S ws :=
    Classical.choose (hPrivate p)
  have hPrivVal (p : Fin C.length) :
      C.vertices p = (.inr (priv p) : thetaVertices S ws) :=
    Classical.choose_spec (hPrivate p)
  let R : Fin C.length → Nat := fun p =>
    wordPositionRank S (ws.get (priv p).1) (priv p).2.val
  have hFin : (Finset.univ : Finset (Fin C.length)).Nonempty :=
    ⟨⟨0,C.length_pos⟩, Finset.mem_univ _⟩
  obtain ⟨p,_,hmin⟩ :=
    (Finset.univ : Finset (Fin C.length)).exists_min_image R hFin
  obtain ⟨q,r,hSucc,hPrev,hDir⟩ :=
    thetaCycle_private_two_sided S ws hLong C p
      (priv p).1 (priv p).2 (hPrivVal p)
  have hEqSucc := thetaBranchPosition_eq_private_rank S ws
    (priv p).1 (priv (cyclicNext C.length_pos p)).1 q
    (priv (cyclicNext C.length_pos p)).2
    (hSucc.symm.trans (hPrivVal (cyclicNext C.length_pos p)))
  have hEqPrev := thetaBranchPosition_eq_private_rank S ws
    (priv p).1 (priv (cyclicPrev C.length_pos p)).1 r
    (priv (cyclicPrev C.length_pos p)).2
    (hPrev.symm.trans (hPrivVal (cyclicPrev C.length_pos p)))
  have hSuccRank : R (cyclicNext C.length_pos p) =
      wordPositionRank S (ws.get (priv p).1) q := hEqSucc.2.symm
  have hPrevRank : R (cyclicPrev C.length_pos p) =
      wordPositionRank S (ws.get (priv p).1) r := hEqPrev.2.symm
  have hBaseRank : R p =
      wordPositionRank S (ws.get (priv p).1) (priv p).2.val := rfl
  have hmSucc : R p ≤ R (cyclicNext C.length_pos p) :=
    hmin _ (Finset.mem_univ _)
  have hmPrev : R p ≤ R (cyclicPrev C.length_pos p) :=
    hmin _ (Finset.mem_univ _)
  rcases hDir with hForward | hBackward
  · omega
  · omega

end CCO.StrongExact
