import CCO.FullCode.CofinalEP

/-!
# The independent four-contract tuple EP implication

This is the standalone C72 branch. It retains exactly the old generated
support, cofinal root hosts, every-competitor same-host lift and all-map
full-code correspondence from the established B035 theorem. The actual
terminal application is separate and must discharge these contracts.
-/

universe u v a
namespace CCO.UnfilteredEP
open CCO.FullCode
variable {L₀ L₁ : Language.{u}} (expansion : LanguageExpansion L₀ L₁)

/-- The abstract source implication, with its exact quantifier order:
for every expanded target there is one old root-generated host before
ANY allowed full-code competitor is received. Hidden EP is an input of
this independent abstract branch, rather than inferred from Ramsey. -/
theorem cofinal_finite_tuple_EP
    (ages : ExpansionAges.{u,v} expansion.toReduct)
    (oldNormal : NormalForms L₀) (expandedNormal : NormalForms L₁)
    (scheme : RootScheme L₀)
    (hiddenEP : ages.HiddenEP) (commutes : ages.SupportsCommute scheme)
    (cofinal : CofinalRootHosts ages.oldAge scheme)
    (sameHost : ∀ (B : FiniteHidden.{u,v} L₀), ages.oldAge B →
      RootGenerated B.model scheme →
      ∀ competitor : SameHostRepresentation expansion oldNormal scheme ages.expandedAge B,
        Nonempty (SameHostLift expansion expandedNormal competitor)) :
    VisibleFullCodeEP.{u,v,a} expansion ages oldNormal expandedNormal scheme :=
  cofinal_tuple_EP expansion ages oldNormal expandedNormal scheme
    hiddenEP commutes cofinal sameHost

end CCO.UnfilteredEP
