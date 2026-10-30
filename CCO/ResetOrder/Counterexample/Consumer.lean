import CCO.ResetOrder.Counterexample.PaddedEP
import CCO.ResetOrder.Counterexample.Boundary
import CCO.ResetOrder.Counterexample.FinalSegments
import CCO.ResetOrder.Counterexample.JointEmbedding
import CCO.ResetOrder.Counterexample.Relabel

/-! B036/C54: the literal displayed EP quantifiers do not compose when a
new unary function is added. The three concrete ages are ALL finite nested
Q⊆P diagrams, ALL P/Q-convex linear orders, then the UNIQUE within-P next
function fixing each maximum. There is no restriction to canonical orders
or rectangular proposed counterexample hosts.

Source map (formalization/reset_order/PROOF_NOTES.md, N07):
* Basic/Relabel give actual full-symbol induced restrictions and transports.
* Successor/FinalSegments prove existence, uniqueness and final-segment
  closedness, so the added-function age is hereditary in the induced sense.
* JointEmbedding constructs disjoint unions of entire P-components at all
  three levels, including their unchanged functions.
* ConvexRanks/Rectangular/PaddedEP prove lower EP for every finite source
  and every allowed order of the fixed padded host; the empty case is explicit.
* Failure proves the upper EP quantifier by actual uniqueness and the
  composite failure against EVERY finite base host.
* Boundary gives an actual old induced embedding that cannot lift, proving
  the upper expansion is not reasonable. No claim about a reasonable
  added-function variant is made.
-/
universe u
namespace CCO.ResetOrder.Counterexample

/-- Reduct surjectivity of the first concrete age expansion. -/
theorem every_base_has_convex_order {X : Type u} [Finite X] (A : Nested X) :
    Nonempty A.ConvexOrder := ⟨A.adversarialOrder⟩

/-- Reduct surjectivity of the added-function expansion, including empty
objects. The preceding uniqueness theorem says these are all its expansions. -/
theorem every_order_has_successor {X : Type u} [Finite X] {A : Nested X}
    (a : A.ConvexOrder) : Nonempty a.Successor :=
  ⟨Nested.ConvexOrder.finiteSuccessor a⟩

/-- A closed induced restriction is precisely the canonical successor
expansion of its own ordered reduct, not merely a graph satisfying an
unrelated weaker condition. -/
theorem restricted_successor_is_canonical {X : Type u} [Finite X]
    {A : Nested X} {a : A.ConvexOrder} (s : a.Successor)
    (S : Set X) (hS : s.IsClosed S) :
    s.induce S hS = Nested.ConvexOrder.finiteSuccessor (a.induce S) :=
  (s.induce S hS).unique _

/-- Both actual EP quantifiers hold, while the composite fails for one
fixed source against every finite base host. Every field is discharged by
the concrete constructions above. -/
theorem C54_all_sizes :
    (∀ (X : Type u) [Finite X] (A : Nested X) (a : A.ConvexOrder),
      ∀ o : (rectangleBase (Nat.card X)).ConvexOrder,
        Nonempty (Nested.ConvexOrder.Embedding a o)) ∧
    (∀ (X : Type u) [Finite X] (A : Nested X) (a : A.ConvexOrder)
      (s t : a.Successor), Nonempty (Nested.ConvexOrder.Successor.Embedding s t)) ∧
    (∀ (X : Type u) [Finite X] (A : Nested X),
      ∃ (o : A.ConvexOrder) (s : o.Successor),
        ¬ Nonempty (Nested.ConvexOrder.Successor.Embedding patternSuccessor s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X _ A a
    exact lower_EP_quantifier a
  · intro X _ A a s t
    exact upper_EP_quantifier a s t
  · intro X _ A
    exact composite_EP_fails A

end CCO.ResetOrder.Counterexample
