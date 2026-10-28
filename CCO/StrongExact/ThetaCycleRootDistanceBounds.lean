import CCO.StrongExact.ThetaCycleTwoArcs

/-!
# C07: theta root-to-root cycle arcs have at least two edges

The constructed LONG theta graph has no direct old diversity edge
between its two shared roots. A specified simple cycle therefore
cannot travel from either root to the other in zero or one forward
cyclic successor step. This is pure finite original-colour geometry.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- A finite specified cycle step across an actually absent old
theta edge cannot have length zero or one. -/
theorem thetaCycle_nonadjacent_distance_ge_two
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p q : Fin C.length)
    (x y : thetaVertices S ws)
    (hx : C.vertices p = x) (hy : C.vertices q = y)
    (hne : x ≠ y)
    (hNoAdj : ¬ thetaAdjacent S ws x y)
    (k : Nat)
    (hReached : thetaCycleAdvance C.length_pos p k = q) :
    2 ≤ k := by
  have hk0 : k ≠ 0 := by
    intro hk
    subst k
    have he : p = q := by
      simpa only [thetaCycleAdvance] using hReached
    apply hne
    calc
      x = C.vertices p := hx.symm
      _ = C.vertices q := congrArg C.vertices he
      _ = y := hy
  have hk1 : k ≠ 1 := by
    intro hk
    subst k
    have he : cyclicNext C.length_pos p = q := by
      simpa only [thetaCycleAdvance] using hReached
    have hAdj : thetaAdjacent S ws
        (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) :=
      (thetaEdgesOfLong_edge_iff_arc S ws hLong
        (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
        (C.next_ne p)).mp (C.specified p)
    rw [hx, he, hy] at hAdj
    exact hNoAdj hAdj
  omega

/-- Forward left-to-right arc distance is at least two steps. -/
theorem thetaCycle_left_right_distance_ge_two
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p q : Fin C.length) (k : Nat)
    (hp : C.vertices p = thetaLeft S ws)
    (hq : C.vertices q = thetaRight S ws)
    (hReached : thetaCycleAdvance C.length_pos p k = q) :
    2 ≤ k :=
  thetaCycle_nonadjacent_distance_ge_two S ws hLong C p q
    (thetaLeft S ws) (thetaRight S ws) hp hq
    (thetaLeft_ne_right S ws)
    (thetaAdjacent_no_root_pair S ws hLong) k hReached

/-- Complementary right-to-left arc distance is at least two. -/
theorem thetaCycle_right_left_distance_ge_two
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (q p : Fin C.length) (l : Nat)
    (hq : C.vertices q = thetaRight S ws)
    (hp : C.vertices p = thetaLeft S ws)
    (hReached : thetaCycleAdvance C.length_pos q l = p) :
    2 ≤ l :=
  thetaCycle_nonadjacent_distance_ge_two S ws hLong C q p
    (thetaRight S ws) (thetaLeft S ws) hq hp
    (thetaLeft_ne_right S ws).symm
    (by
      intro h
      exact thetaAdjacent_no_root_pair S ws hLong
        (thetaAdjacent_symmetric S ws h)) l hReached

end CCO.StrongExact
