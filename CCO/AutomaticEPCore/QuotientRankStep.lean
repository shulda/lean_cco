import CCO.AutomaticEPCore.IsoGateSeparation
import CCO.AutomaticEPCore.QuotientRootCode
import CCO.AutomaticEPCore.NamedIsoEndTransfer

/-! The actual lower-rank source is the literal initial selected
quotient. Its genuine safe tower and full terminality are discharged,
and its separator returns on the SAME prescribed target occupancy names
with the SAME fixed original binary predicate value. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

/-- The induction conclusion quantifies over ALL actual original sources
and every genuine finite maximal-character tower in the receiving category.
This is a mathematical induction assertion, not an added source provider. -/
def ActualTowerSeparation (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) : Prop :=
  ∀ next : CertifiedGateTower.ExactPrefix A,
    History IsoGateTower.Step (CertifiedGateTower.initial A) next →
    next.current.Terminal → ∀ s t : next.current.Sorts, s ≠ t →
      ∃ a : A.source.Atom base base, (atomGraph A.source a).IsBipartite ∧
        originalAtomTable A next.current next.reduct base hOne a s t

/-- C30/C52 receiving half of the outer induction. The sole induction
premise is separation on the ACTUAL smaller original source. Source,
history, code names, terminality and exact endpoints are constructed. -/
theorem actual_quotient_rank_step_code_separator
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History IsoGateTower.Step (CertifiedGateTower.initial A) next)
    (terminal : next.current.Terminal)
    (s t : next.current.Sorts)
    (different : ¬prefixSupport next.reduct (originalExactGlobalRelation A base hOne E) s t)
    (smaller :
      let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
      ActualTowerSeparation Q.current (Quotient.mk'' base)
        (original_initial_selected_quotient_one_sort A base hOne E)) :
    let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
    let i : Q.current.Sorts := Quotient.mk'' base
    let one := original_initial_selected_quotient_one_sort A base hOne E
    ∃ b : Q.current.source.Atom i i, (atomGraph Q.current.source b).IsBipartite ∧
      ∃ code : Age.Colour A.source → Prop,
        (∀ p q : Sigma Q.current.Point, Q.code p q = code ↔
          originalRelation Q.current i one (Q.current.source.atomRel b) p q) ∧
        codedPredicateSupport (originalCodedQuotient A base hOne E next)
          (fun value => value = code) (Quotient.mk'' s) (Quotient.mk'' t) := by
  let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
  let Y := originalCodedQuotient A base hOne E next
  let i : Q.current.Sorts := Quotient.mk'' base
  let one : ∀ j : Q.current.Sorts, i = j :=
    original_initial_selected_quotient_one_sort A base hOne E
  obtain ⟨projected,_⟩ := IsoGateTower.quotient_safe_history A base hOne E history
  obtain ⟨received,⟨receivedHistory⟩,receivedClass⟩ :=
    coded_safe_history_exact_prefix_receiving Q.current Q.code projected
      (CertifiedGateTower.initial Q.current) rfl
  obtain ⟨I⟩ : Nonempty (CodedCurrentSourceIso (codedExactPrefix Q.code received) Y) :=
    Quotient.exact receivedClass
  have targetTerminal : Y.current.Terminal :=
    originalExactSelectedQuotient_terminal A next.current next.reduct next.transport
      base hOne E terminal
  have receivedTerminal : received.current.Terminal :=
    (namedIso_terminal_iff I.toNamedCurrentSourceIso).mpr targetTerminal
  have targetDifferent : (Quotient.mk'' s : Y.current.Sorts) ≠ Quotient.mk'' t := by
    intro same
    exact different (Quotient.exact same)
  have receivedDifferent : I.sorts.symm (Quotient.mk'' s) ≠ I.sorts.symm (Quotient.mk'' t) := by
    intro same
    exact targetDifferent (I.sorts.symm.injective same)
  obtain ⟨b,bipartite,support⟩ := smaller received receivedHistory receivedTerminal
    (I.sorts.symm (Quotient.mk'' s)) (I.sorts.symm (Quotient.mk'' t)) receivedDifferent
  obtain ⟨code,codeGraph⟩ := original_initial_quotient_atom_code A base hOne E b
  refine ⟨b,bipartite,code,codeGraph,?_⟩
  apply (codedExactPrefix_support_target_iff Q.code received I
    (fun value => value = code) (Quotient.mk'' s) (Quotient.mk'' t)).mpr
  obtain ⟨x,y,related⟩ := support
  exact ⟨x,y,(codeGraph _ _).mpr related⟩

end
end CCO.AutomaticEPCore
