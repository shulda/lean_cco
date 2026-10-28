import CCO.RawExact.FanTwoRootSpokes
import CCO.RawExact.FanFullNonrootPreservation
import CCO.RawExact.FanTwoRootCycleEdges
import Mathlib.Tactic

/-!
# B002 C12: a cycle through the real full-fan root uses only TWO walks

For a simple cycle through the unique formal fan root, the cycle's
outgoing and incoming spokes carry original source atoms certified
by two actual RAW word occurrences. Pairwise exact-ball intersection
supplies genuine old walks for JUST these two occurrences starting
at the same old real root, with their literal old centres fixed.

Every other cycle edge avoids the root and is preserved by the
independent reference walk for its own occurrence (or by the actual
complete centre diagram). This gives a real cycle homomorphism
without any full-family Helly hypothesis or global path-shape
classification, even with repeated centres and identity-bearing words.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem privateFanFull_cycle_through_root
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (C : SimpleCycle (privateFanFullDiagram S H D centres))
    (p0 : Fin C.length)
    (hp0 : C.vertices p0 = privateFanRoot S D centres) :
    CycleHom C := by
  classical
  let R := privateFanRoot S D centres
  let nxt := cyclicNext C.length_pos p0
  obtain ⟨prev, hprev, _, _⟩ :=
    cycle_root_incidences C R p0 hp0
  have hNext : R ≠ C.vertices nxt := by
    intro h
    apply C.next_ne p0
    rw [hp0]
    exact h
  have hPrev : R ≠ C.vertices prev := by
    intro h
    apply C.next_ne prev
    rw [hprev, hp0]
    exact h.symm
  have hOutSpec :
      ∃ a : S.Atom root (privateFanSort S D centres (C.vertices nxt)),
        (privateFanFullDiagram S H D centres).edge
          R (C.vertices nxt) hNext = some a := by
    have hSpec := C.specified p0
    change ∃ a : S.Atom
        (privateFanSort S D centres (C.vertices p0))
        (privateFanSort S D centres (C.vertices nxt)),
      (privateFanFullDiagram S H D centres).edge
        (C.vertices p0) (C.vertices nxt) (C.next_ne p0) = some a at hSpec
    rw [hp0] at hSpec
    simpa only [R, nxt, privateFanSort_root] using hSpec
  have hInSpec :
      ∃ a : S.Atom (privateFanSort S D centres (C.vertices prev)) root,
        (privateFanFullDiagram S H D centres).edge
          (C.vertices prev) R hPrev.symm = some a := by
    have hSpec := C.specified prev
    change ∃ a : S.Atom
        (privateFanSort S D centres (C.vertices prev))
        (privateFanSort S D centres
          (C.vertices (cyclicNext C.length_pos prev))),
      (privateFanFullDiagram S H D centres).edge
        (C.vertices prev) (C.vertices (cyclicNext C.length_pos prev))
          (C.next_ne prev) = some a at hSpec
    rw [hprev, hp0] at hSpec
    simpa only [R, privateFanSort_root] using hSpec
  obtain ⟨aOut, hOut⟩ := hOutSpec
  obtain ⟨aIn, hIn⟩ := hInSpec
  have hInReverse :
      (privateFanFullDiagram S H D centres).edge
        R (C.vertices prev) hPrev = some (S.conv aIn) :=
    ((privateFanFullDiagram S H D centres).edge_reverse
      (C.vertices prev) R hPrev.symm aIn).mp hIn
  obtain ⟨x, choice, hOutColour, hInColourReverse⟩ :=
    privateFan_two_root_spokes_realizable S H D centres hPair
      (C.vertices nxt) (C.vertices prev)
      hNext hPrev aOut (S.conv aIn) hOut hInReverse
  let point := privateFanVariableTypedPoint S D centres choice x
  have hIncomingColour :
      S.colour (point (C.vertices prev)) (point R) = some aIn := by
    have hReverse :=
      (S.colour_swap (point R) (point (C.vertices prev)) (S.conv aIn)).mp
        hInColourReverse
    rw [S.conv_invol aIn] at hReverse
    exact hReverse
  have hOutFullColour :
      S.colour (point R) (point (C.vertices nxt)) =
        (privateFanFullDiagram S H D centres).edge
          R (C.vertices nxt) hNext :=
    hOutColour.trans hOut.symm
  have hIncomingFullColour :
      S.colour (point (C.vertices prev)) (point R) =
        (privateFanFullDiagram S H D centres).edge
          (C.vertices prev) R hPrev.symm :=
    hIncomingColour.trans hIn.symm
  refine ⟨fun p => point (C.vertices p), ?_⟩
  intro p a ha
  by_cases hFirst : p = p0
  · subst p
    have hColFull :
        S.colour (point (C.vertices p0))
          (point (C.vertices (cyclicNext C.length_pos p0))) =
        (privateFanFullDiagram S H D centres).edge
          (C.vertices p0)
          (C.vertices (cyclicNext C.length_pos p0))
          (C.next_ne p0) := by
      simpa only [R, nxt, hp0] using hOutFullColour
    exact hColFull.trans ha
  · by_cases hLast : p = prev
    · subst p
      have hColFull :
          S.colour (point (C.vertices prev))
            (point (C.vertices (cyclicNext C.length_pos prev))) =
          (privateFanFullDiagram S H D centres).edge
            (C.vertices prev)
            (C.vertices (cyclicNext C.length_pos prev))
            (C.next_ne prev) := by
        simpa only [R, hprev, hp0] using hIncomingFullColour
      exact hColFull.trans ha
    · have hAway :=
        cycle_edges_away_from_root_except_two C R p0 hp0
          prev hprev p hFirst hLast
      exact privateFanVariable_preserves_full_nonroot_edge
        S H D centres choice x
        (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
        hAway.1 hAway.2 (C.next_ne p) a ha

end CCO.RawExact
