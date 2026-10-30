import CCO.UnaryFreshFrames.Quotient.System
import CCO.UnaryFreshFrames.Quotient.NamedNecessity
import CCO.UnaryFreshFrames.SAPAlgebraicity

/-! Both source kernel clauses are discharged from actual HEREDITARY SAP.
The converse never assumes the clauses it proves or a separate real-base
orbit premise. Actual subgroup and full automorphism actions stay distinct. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

/-- The actual projection's strict kernel provides a real point even when
some unrelated named sort is empty. No extra nonemptiness hypothesis. -/
theorem NamedProjection.source_nonempty (p : H.NamedProjection) :
    Nonempty (H.Carrier p.source) := by
  classical
  by_contra h
  apply p.strict
  intro x y _
  exact False.elim (h ⟨x⟩)

/-- C37–C44: SAP alone yields actual named forced factors and infinite
unforced relative indices for every registered existing named quotient. -/
theorem kernel_clauses_of_ageSAP {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (G : Subgroup H.Aut) (ht : S.SourceTransitive G) (hfin : H.LocallyFinite)
    (hom : H.Homogeneous) (sap : H.AgeSAP) : S.KernelClauses := by
  have hinf := H.infiniteClosedOrbits_of_ageSAP hfin hom sap
  have hacl : ∀ b : V, Acl H.Aut {b} = H.closureAt b :=
    fun b => H.full_acl_eq_closure hfin hinf (Set.finite_singleton b)
  intro q
  let p := S.projection q
  obtain ⟨x₀⟩ := p.source_nonempty
  exact ⟨H.forcedNamedFactors_of_acl G (ht q) p.term x₀ hacl,
    H.infiniteUnforcedIndex_of_acl G (ht q) p.term p.surjective hacl⟩

end CCO.UnaryFreshFrames.Structure
