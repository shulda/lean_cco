import CCO.StrongExact.ThetaCycleContainsLeft

/-! Finite-cycle root indices for the hard theta, with original typed labels. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Both shared roots occur at unique cycle positions, regardless
of whether their named sort labels coincide. -/
theorem thetaCycle_roots_unique
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    (∃! p : Fin C.length, C.vertices p = thetaLeft S ws) ∧
      (∃! q : Fin C.length, C.vertices q = thetaRight S ws) := by
  constructor
  · obtain ⟨p, hp⟩ := thetaCycle_contains_left S ws hLong C
    refine ⟨p, hp, ?_⟩
    intro q hq
    exact C.vertices.injective (hq.trans hp.symm)
  · obtain ⟨q, hq⟩ := thetaCycle_contains_right S ws hLong C
    refine ⟨q, hq, ?_⟩
    intro r hr
    exact C.vertices.injective (hr.trans hq.symm)

/-- The two unique root indices are distinct formal cycle positions. -/
theorem thetaCycle_root_indices_distinct
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram)) :
    ∃ p q : Fin C.length,
      p ≠ q ∧ C.vertices p = thetaLeft S ws ∧
        C.vertices q = thetaRight S ws := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ :=
    thetaCycle_contains_both_roots S ws hLong C
  refine ⟨p, q, ?_, hp, hq⟩
  intro heq
  apply thetaLeft_ne_right S ws
  calc
    thetaLeft S ws = C.vertices p := hp.symm
    _ = C.vertices q := congrArg C.vertices heq
    _ = thetaRight S ws := hq

/-- All other vertices of a genuine simple theta cycle are tagged
private interiors, rather than either formal root. -/
theorem thetaCycle_nonroot_is_private
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p q r : Fin C.length)
    (hp : C.vertices p = thetaLeft S ws)
    (hq : C.vertices q = thetaRight S ws)
    (hrp : r ≠ p) (hrq : r ≠ q) :
    ∃ b : Fin ws.length, ∃ t : wordInterior S (ws.get b),
      C.vertices r = (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  have hnLeft : C.vertices r ≠ thetaLeft S ws := by
    intro h
    exact hrp (C.vertices.injective (h.trans hp.symm))
  have hnRight : C.vertices r ≠ thetaRight S ws := by
    intro h
    exact hrq (C.vertices.injective (h.trans hq.symm))
  cases hr : C.vertices r with
  | inl tag =>
      cases tag with
      | false =>
          exact False.elim (hnLeft (by simpa only [thetaLeft] using hr))
      | true =>
          exact False.elim (hnRight (by simpa only [thetaRight] using hr))
  | inr z =>
      cases z with
      | mk b t =>
          exact ⟨b,t,hr⟩

end CCO.StrongExact
