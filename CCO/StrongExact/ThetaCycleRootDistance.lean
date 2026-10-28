import CCO.StrongExact.ThetaCycleIndexInjectivity
import CCO.StrongExact.ThetaCycleRootPositions

/-!
# C07: the two literal theta roots cut every simple cycle into arcs

Repeated finite successor reaches the right root from the left in
a unique positive distance < cycle length. Every strict intermediate
position in that arc avoids both formal roots, independently of any
coincidence of their named sort labels.

The theorem is only about exact cycle indices and original formal
theta vertices. It neither assumes nor asserts a complete private
word decomposition.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Choose the unique nonzero successor distance from left root
to right root in any genuine long-theta simple cycle. -/
theorem thetaCycle_roots_have_forward_distance
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    ∃ p q : Fin C.length, ∃ k : Nat,
      0 < k ∧ k < C.length ∧
      thetaCycleAdvance C.length_pos p k = q ∧
      C.vertices p = thetaLeft S ws ∧
      C.vertices q = thetaRight S ws := by
  obtain ⟨p,q,hpq,hp,hq⟩ :=
    thetaCycle_root_indices_distinct S ws hLong C
  obtain ⟨k,hk,hReached⟩ :=
    thetaCycleAdvance_reaches C.length_pos p q
  have hPositive : 0 < k := by
    by_contra hn
    have hZero : k = 0 := by omega
    subst k
    have hpeq : p = q := by
      simpa only [thetaCycleAdvance] using hReached
    exact hpq hpeq
  exact ⟨p,q,k,hPositive,hk,hReached,hp,hq⟩

/-- A strict intermediate cyclic index in the forward left-to-right
arc is neither original root, by injectivity of the finite orbit.
No private-branch tag or palette is added here. -/
theorem thetaCycle_between_roots_avoids_roots
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p q : Fin C.length) (k m : Nat)
    (hp : C.vertices p = thetaLeft S ws)
    (hq : C.vertices q = thetaRight S ws)
    (hk : k < C.length)
    (hReached : thetaCycleAdvance C.length_pos p k = q)
    (hm : 0 < m) (hmk : m < k) :
    C.vertices (thetaCycleAdvance C.length_pos p m) ≠
        thetaLeft S ws ∧
    C.vertices (thetaCycleAdvance C.length_pos p m) ≠
        thetaRight S ws := by
  constructor
  · intro h
    have hIndex : thetaCycleAdvance C.length_pos p m = p :=
      C.vertices.injective (h.trans hp.symm)
    have hEq : thetaCycleAdvance C.length_pos p m =
        thetaCycleAdvance C.length_pos p 0 := by
      simpa only [thetaCycleAdvance] using hIndex
    have hmzero := thetaCycleAdvance_injective_lt
      C.length_pos p m 0 (by omega) C.length_pos hEq
    omega
  · intro h
    have hIndex : thetaCycleAdvance C.length_pos p m = q :=
      C.vertices.injective (h.trans hq.symm)
    have hmk := thetaCycleAdvance_injective_lt
      C.length_pos p m k (by omega) hk
      (hIndex.trans hReached.symm)
    omega

end CCO.StrongExact
