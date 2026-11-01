import CCO.TransitionClosure.TypedExactPCDomains
import CCO.StrongExact.SourceExactCalculus
import CCO.StrongExact.ThetaCycleHom

/-!
# B049 source07 C10: direct ORIGINAL typed positive-word 2-Helly

This source theorem is NOT derived from exact-PC domain products,
Set-Pasch or hidden quotient SAP. The accepted B003/B038 original
private-theta proof explicitly handles equal direct branches, all
long private typed paths, each actual old-colour simple cycle, and
ONE original source semantic CCO completion followed by visible
AgeSAP injectivisation of its two marked roots.

The original homomorphic CCO input is transported from the source's
standard vertex universe to the accepted finite old private-theta
universe by B050's proved equivalence; no second CCO assumption or
missing generic Helly provider is postulated. Empty word lists give
true original diversity Top, not a new STRONG identity atom.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

/-- SOURCE07 C10: an arbitrary finite family of REAL positive OLD
typed words between any pair of original named sorts has ONE common
genuine diversity fine atom as soon as ALL pairs of their STRONG
profiles intersect. The words may visit other old sorts internally.

This consumes the accepted SOURCE-level private theta construction,
not an abstract conditional `WordHelly` or exact-PC inference. -/
theorem original_positive_word_two_helly
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (ws : List (PositiveWord S i j))
    (hPair : StrongExact.PairwiseWordProfiles S ws) :
    (StrongExact.present S ws).Nonempty := by
  have ccoZero : SemanticCCO.{u,v,0,w} S :=
    TerminalLattice.originalSemanticCCO_finite_universe_zero S cco
  exact StrongExact.wordHelly_of_SAP_CCO S H sap ccoZero ws hPair

/-- SOURCE07 C09/C10 finite-menu Helly: EVERY pairwise-intersecting
list of actual nonempty STRONG EXACT menus on one original typed
endpoint pair has ONE common real old diversity atom.

All exact menus are finite positive-profile meets by definition.
The family may be empty, and Top remains genuine diversity Top.
This proof uses original theta/CCO/visible SAP, not a PC-product
closure assumption or any quotient/hidden SAP. -/
theorem original_exact_menus_two_helly
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (menus : List (S.Menu i j))
    (hExact : ∀ A ∈ menus, StrongExact.Exact S A)
    (hPair : ∀ A ∈ menus, ∀ B ∈ menus,
      (A ∩ B).Nonempty) :
    (StrongExact.meetMenus S menus).Nonempty := by
  have ccoZero : SemanticCCO.{u,v,0,w} S :=
    TerminalLattice.originalSemanticCCO_finite_universe_zero S cco
  exact StrongExact.exact_helly_of_SAP_CCO
    S H sap ccoZero menus hExact hPair

end CCO.TransitionClosure
