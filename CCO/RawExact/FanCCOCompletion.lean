import CCO.RawExact.FanAllCycles

/-!
# B002 RAW C12: original semantic CCO completes the genuine private fan

The entire finite private-word anchored fan is a correctly typed
source partial diagram, with real old centre colours and actual
RAW-word diversity atoms. Pairwise exact-ball intersections give
a source homomorphism for EVERY simple cycle via the proved
two-root-spoke replacement theorem.

The original semantic homomorphic CCO hypothesis therefore supplies
one homomorphism of the whole fan. This is NOT already a proof of
C13: the next obligations are to reconstruct each RAW word from the
completed fan's atomic edges, and align its complete marked-centre
diagram by a single original automorphism.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A single original-source CCO application gives a homomorphism
of ALL words and centre vertices' combined finite fan, without
assuming a source Helly theorem or quotient homogeneity. -/
theorem privateFanFull_completion_of_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty) :
    Nonempty (DiagramHom (privateFanFullDiagram S H D centres)) :=
  cco (PrivateFanVertex S D centres)
    (privateFanFullDiagram S H D centres)
    (privateFanFull_cycleHom_of_pairwise S H D centres hPair)

end CCO.RawExact
