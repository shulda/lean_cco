import CCO.RawExact.AtomicFans
import CCO.RawExact.CycleIncidence

/-!
# B002 C12: cycle witnesses for the literal finite atomic anchored fan

An actual root-to-centre diversity atom is prescribed at each spoke.
The remaining edges are the COMPLETE actual pair-colour diagram of the
original centres. A specified simple cycle avoiding the root is
realized by its actual centres. A cycle through the root has exactly two
root incidents: its witness uses precisely the pairwise-compatible two
atom balls, and uses all other real centres unchanged.

This is the source's real cycle-witness mechanism, restricted to
single-atom rather than arbitrary private-word spokes.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

def fanPoint {I : Type (max u v)} [Finite I]
    (root : ι) (sort : I → ι)
    (centres : ∀ t : I, X (sort t))
    (atoms : ∀ t : I, S.Atom root (sort t))
    (x : X root) :
    (v : Option I) →
      X ((atomicFan S root sort centres atoms).vertexSort v)
  | none => x
  | some t => centres t

/-- A genuine atomic fan's point assignment preserves an individual
specified edge as soon as the two possible root orientations are
covered. Splitting on the *formal Option vertices*, rather than on a
dependent cycle-expression, keeps all sort indices definitional. -/
theorem fanPoint_preserves_edge
    {I : Type (max u v)} [Finite I]
    (root : ι) (sort : I → ι)
    (centres : ∀ t : I, X (sort t))
    (atoms : ∀ t : I, S.Atom root (sort t))
    (x : X root) (p q : Option I) (hpq : p ≠ q)
    (c : S.Atom
      ((atomicFan S root sort centres atoms).vertexSort p)
      ((atomicFan S root sort centres atoms).vertexSort q))
    (hc : (atomicFan S root sort centres atoms).edge p q hpq = some c)
    (hLeft : ∀ t : I, p = none → q = some t →
      S.atomRel (atoms t) x (centres t))
    (hRight : ∀ t : I, p = some t → q = none →
      S.atomRel (atoms t) x (centres t)) :
    S.colour (fanPoint S root sort centres atoms x p)
      (fanPoint S root sort centres atoms x q) = some c := by
  cases p with
  | none =>
      cases q with
      | none => exact False.elim (hpq rfl)
      | some t =>
          have hAtom := hLeft t rfl rfl
          change some (atoms t) = some c at hc
          change S.colour x (centres t) = some c
          exact hAtom.trans hc
  | some t =>
      cases q with
      | none =>
          have hAtom := hRight t rfl rfl
          have hRev : S.colour (centres t) x =
              some (S.conv (atoms t)) :=
            (S.colour_swap x (centres t) (atoms t)).mp hAtom
          change some (S.conv (atoms t)) = some c at hc
          change S.colour (centres t) x = some c
          exact hRev.trans hc
      | some s =>
          change S.colour (centres t) (centres s) = some c at hc
          exact hc

/-- The literal atomic star is locally cycle-realizable whenever every
pair of its spokes has an ACTUAL simultaneous real-root witness.
No original SAP or assumed Helly conclusion is used. -/
theorem atomicFan_cycleHom_of_pairwise
    {I : Type (max u v)} [Finite I]
    (root : ι) (sort : I → ι)
    (centres : ∀ t : I, X (sort t))
    (atoms : ∀ t : I, S.Atom root (sort t))
    (hPair : ∀ a b : I, ∃ x : X root,
      S.atomRel (atoms a) x (centres a) ∧
      S.atomRel (atoms b) x (centres b)) :
    ∀ C : SimpleCycle (atomicFan S root sort centres atoms),
      CycleHom C := by
  classical
  intro C
  by_cases hRoot : ∃ p : Fin C.length, C.vertices p = none
  · obtain ⟨p0, hp0⟩ := hRoot
    obtain ⟨prev, hprev, hOnlyRoot, hOnlyIncoming⟩ :=
      cycle_root_incidences C (none : Option I) p0 hp0
    have hNextNonroot :
        C.vertices (cyclicNext C.length_pos p0) ≠ none := by
      intro hh
      exact C.next_ne p0 (hp0.trans hh.symm)
    have hPrevNonroot : C.vertices prev ≠ none := by
      intro hh
      apply C.next_ne prev
      rw [hh, hprev, hp0]
    cases hNext : C.vertices (cyclicNext C.length_pos p0) with
    | none => exact False.elim (hNextNonroot hNext)
    | some a =>
      cases hPrev : C.vertices prev with
      | none => exact False.elim (hPrevNonroot hPrev)
      | some b =>
        obtain ⟨x, hxA, hxB⟩ := hPair a b
        refine ⟨fun p => fanPoint S root sort centres atoms x (C.vertices p), ?_⟩
        intro p c hc
        apply fanPoint_preserves_edge S root sort centres atoms x
          (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
          (C.next_ne p) c hc
        · intro t hp hq
          have heq : p = p0 := hOnlyRoot p hp
          subst p
          have ht : a = t := Option.some.inj (hNext.symm.trans hq)
          subst t
          exact hxA
        · intro t hp hq
          have heq : p = prev := hOnlyIncoming p hq
          subst p
          have ht : b = t := Option.some.inj (hPrev.symm.trans hp)
          subst t
          exact hxB
  · obtain ⟨arbitrary⟩ := S.nonemptySort root
    refine ⟨fun p => fanPoint S root sort centres atoms arbitrary (C.vertices p), ?_⟩
    intro p c hc
    apply fanPoint_preserves_edge S root sort centres atoms arbitrary
      (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
      (C.next_ne p) c hc
    · intro t hp _
      exact False.elim (hRoot ⟨p, hp⟩)
    · intro t _ hq
      exact False.elim (hRoot ⟨cyclicNext C.length_pos p, hq⟩)

/-- A genuine CCO-to-Helly theorem for every FINITE family of
single-atom balls with pairwise intersection and distinct actual
centres of arbitrary original sorts. CCO is used exactly once after
the cycle-witness theorem above; one ambient automorphism aligns
the whole complete centre diagram, not the balls individually. -/
theorem heterogeneous_atomic_ball_helly_of_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {I : Type (max u v)} [Finite I]
    (root : ι) (sort : I → ι)
    (centres : ∀ t : I, X (sort t))
    (atoms : ∀ t : I, S.Atom root (sort t))
    (hDistinct : Function.Injective
      (fun t : I => (⟨sort t, centres t⟩ : Sigma X)))
    (hPair : ∀ a b : I, ∃ x : X root,
      S.atomRel (atoms a) x (centres a) ∧
      S.atomRel (atoms b) x (centres b)) :
    ∃ x : X root, ∀ t : I, S.atomRel (atoms t) x (centres t) :=
  atomic_fan_helly_of_cycle_checks S H cco root sort centres atoms
    hDistinct (atomicFan_cycleHom_of_pairwise S root sort centres atoms hPair)

end CCO.RawExact
