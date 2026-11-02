import CCO.StrongExact.CanonicalDomains
import CCO.TerminalLattice.OriginalCCOUniverseBridge

/-!
# B049 source07 C09: ORIGINAL typed fixed-point PC exact-domain calculus

The frozen source's `Dat^{ij}` is the family of NONEMPTY menus which
are finite meets of positive old typed STRONG word profiles, with
an empty defining family evaluating to true diversity Top.

Accepted B003 proves that precisely these menus are ACTUAL canonical
fixed-point PC domains of strongly completable finite old typed
private-word diagrams. It also proves the full three-root
support-consistency ↔ simultaneous canonical-PC-realization criterion.

The original source's semantic CCO is at its standard old universe.
We transport this very SAME assumption to the finite diagram universe
via accepted B050, rather than adding a second `SemanticCCO` premise.
No Set-Pasch, quotient CCO, new axiom, hidden SAP or replacement of
fixed-point PC by a weaker abstract formal-domain condition.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ k : ι, MulAction G (X k)]

/-- Exact SOURCE07 TED, including all OLD named-sort pairs:
actual canonical stable PC domains of completable typed networks
are precisely NONEMPTY finite meets of original positive STRONG
typed word profiles. The empty list equals genuine diversity Top.

`CanonicalThetaDomain` records the REAL private-word diagram and
its complete `HasStrongCompletion`, not a hypothetical abstract PC. -/
theorem original_typed_PC_fixed_domain_iff_exact
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (A : S.Menu i j) :
    StrongExact.CanonicalThetaDomain S A ↔
      A.Nonempty ∧
      ∃ ws : List (PositiveWord S i j),
        A = StrongExact.present S ws := by
  have ccoZero : SemanticCCO.{u,v,0,w} S :=
    TerminalLattice.originalSemanticCCO_finite_universe_zero S cco
  change StrongExact.CanonicalThetaDomain S A ↔
    StrongExact.Exact S A
  exact (StrongExact.exact_iff_canonicalThetaDomain_of_SAP_CCO
    S H sap ccoZero).symm

/-- The source07 support-consistent THREE-domain criterion.
The required EXACT menus are source-07 genuine finite positive
profile meets, each nonempty. The CONCLUSION asserts ONE actual
strongly completable old private triple-word diagram whose three
literal fixed-point PC domains are the given menus.

Repeated old original sorts and arbitrary mixed-sort typed paths
are allowed; no quotient or hidden SAP assumption is imported. -/
theorem original_typed_PC_three_domains_iff_support
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j k : ι}
    (A : S.Menu i j) (B : S.Menu j k) (C : S.Menu i k)
    (hA : StrongExact.Exact S A)
    (hB : StrongExact.Exact S B)
    (hC : StrongExact.Exact S C) :
    StrongExact.ThreeRootCanonicalOccurrence S A B C ↔
      S.PC A B C := by
  have ccoZero : SemanticCCO.{u,v,0,w} S :=
    TerminalLattice.originalSemanticCCO_finite_universe_zero S cco
  exact StrongExact.threeRootCanonicalOccurrence_iff_PC_of_SAP_CCO
    S H sap ccoZero hA hB hC

end CCO.TransitionClosure
