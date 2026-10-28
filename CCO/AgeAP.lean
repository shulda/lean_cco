import CCO.Finite

/-!
# Ordinary amalgamation of the actual finite induced age

This shared evidence type imposes a commuting amalgamation square only.
There is no freshness or exact-overlap condition, unlike `AgeSAP`.
The source proofs using it remain in their respective package modules.
-/

universe u v w

namespace CCO

variable {ι : Type u} {X : ι → Type v}

/-- Ordinary amalgamation of the actual finite induced age. -/
structure AgeAP (S : AtomicSource.{u,v,w} ι X) : Prop where
  amalgamate : ∀ (C A B : FiniteInduced (X := X))
      (eCA : InducedEmbedding S C A) (eCB : InducedEmbedding S C B),
    ∃ (D : FiniteInduced (X := X)) (eAD : InducedEmbedding S A D)
      (eBD : InducedEmbedding S B D),
      ∀ c : ↥C.vertices,
        eAD.toEmbedding (eCA.toEmbedding c) = eBD.toEmbedding (eCB.toEmbedding c)

end CCO
