import CCO.TerminalLattice.OriginalQuotientStatePowers
import CCO.TerminalLattice.OriginalCCOUniverseBridge
import CCO.StrongExact.ThetaCycleHom

/-!
# B050 source09 OWL finite escape: ORIGINAL positive STRONG word 2-Helly

The accepted B001/B002 STRONG theta construction has already proved
finite 2-Helly for genuine positive OLD typed atomic word profiles
using original SAP and ONE original semantic CCO. This module exposes
that proved source instance for the pinned source09 external-orbital
finite-escape argument.

In contrast, RAW word profile Helly alone could return only diagonal
OLD endpoints and is NOT enough for positive STRONG menu
intersection. We explicitly use the genuine theorem
StrongExact.wordHelly_of_SAP_CCO, never a conditional WordHelly axiom.
No quotient-redacted automorphism action, hidden quotient CCO,
and no assumption of exactness of arbitrary invariant menus.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Source09: the actual original homogeneous SAP+CCO assumptions
discharge the full strong finite 2-Helly for every ORIGINAL
positive typed diversity word family. The original CCO universe
conversion is a proved finite-vertex interface, not an extra axiom.
-/
theorem original_positive_word_helly_of_SAP_CCO
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    StrongExact.WordHelly S := by
  have ccoZero : SemanticCCO.{u,v,0,w} S :=
    originalSemanticCCO_finite_universe_zero S cco
  exact StrongExact.wordHelly_of_SAP_CCO S H sap ccoZero

/-- Literal source09 finite positive STRONG family consequence:
pairwise intersections of the actual OLD word palettes force ONE
fine old diversity atom in their TOTAL intersection, including
empty/singleton/duplicate families exactly as the accepted source
theorem requires. No RAW diagonal return is substituted. -/
theorem original_positive_profiles_helly_of_SAP_CCO
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι}
    (words : List (PositiveWord S i j))
    (hPair : ∀ p ∈ words, ∀ q ∈ words,
      (PositiveWord.profile S p ∩
        PositiveWord.profile S q).Nonempty) :
    (StrongExact.present S words).Nonempty :=
  (original_positive_word_helly_of_SAP_CCO S H sap cco)
    words hPair

end CCO.TerminalLattice
