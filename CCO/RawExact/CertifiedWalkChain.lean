import CCO.RawExact.WalkGeometry
import Mathlib.Data.List.Chain

/-!
# B002 C12: genuine old-colour chains of represented RAW walks

The proof that a WordPath gives a finite REAL point list carrying
exactly its recorded original diversity atoms also yields an ordinary
List.IsChain of genuine old diversity relations. The chain may revisit
nonconsecutive old points; the original homomorphic CCO interface
needs no stronger injectivity assumption.

This is independent of semantic CCO and full exact-ball Helly.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Existence of one true diversity atom connecting two ACTUAL
tagged original-sort points, not a synthetic equality colour. -/
def GenuineEdge (p q : Sigma X) : Prop :=
  ∃ a : S.Atom p.1 q.1, S.colour p.2 q.2 = some a

/-- Every adjacent pair of the certified list carries a genuine
old atomic diversity colour. -/
theorem typedWalkCertificate_isChain
    {points : List (Sigma X)}
    {steps : List (TypedAtomicStep S)}
    (h : TypedWalkCertificate S points steps) :
    points.IsChain (GenuineEdge S) := by
  induction h with
  | singleton p =>
      exact List.IsChain.singleton _
  | step x y a edge rest ih =>
      exact List.IsChain.cons_cons ⟨a, edge⟩ ih

/-- Directly consume any represented typed RAW word witness,
including equality-bearing words with possible diagonal OUTPUTS. -/
theorem realWordPath_isChain
    {i j : ι} {word : RawWord S i j}
    {x : X i} {y : X j}
    (path : WordPath S word x y) :
    (realWalkTrace S path).IsChain (GenuineEdge S) :=
  typedWalkCertificate_isChain S
    (realWalkTrace_certified S path)

end CCO.RawExact
