import CCO.RawExact.FanNoRootCycles
import CCO.RawExact.FanCycleThroughRoot

/-!
# B002 RAW C12: every simple cycle in the ACTUAL full private fan

The original source provides genuinely coloured RAW word edges and
all old pair colours of its literal marked centres. Each root-avoiding
simple cycle is already realized by independent original reference
walks. A root-containing simple cycle is realized by replacing JUST
the two root-incident word occurrences with a pair of original
walks based at a single actual old root.

The proof makes no assertion that all words simultaneously have a
common old root: that is precisely the subsequent C13 Helly conclusion.
No quotient-lift, SAP, STRONG or unproved CCO theorem is assumed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Every real RAW private-fan simple cycle is homomorphically
realizable using only the literal pairwise ball witnesses and
homogeneity of the original source. This is the C12 input to
the original source's semantic CCO axiom/interface. -/
theorem privateFanFull_cycleHom_of_pairwise
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty) :
    ∀ C : SimpleCycle (privateFanFullDiagram S H D centres),
      CycleHom C := by
  intro C
  by_cases hRoot : ∃ p : Fin C.length,
      C.vertices p = privateFanRoot S D centres
  · obtain ⟨p, hp⟩ := hRoot
    exact privateFanFull_cycle_through_root S H D centres hPair C p hp
  · exact privateFanFull_cycles_avoiding_root S H D centres C
      (fun p hp => hRoot ⟨p,hp⟩)

end CCO.RawExact
