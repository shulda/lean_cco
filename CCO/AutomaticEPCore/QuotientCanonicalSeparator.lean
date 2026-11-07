import CCO.AutomaticEPCore.QuotientRankStep
import CCO.AutomaticEPCore.QuotientCodeEdge

/-! A genuinely recursive lower-rank separator, when supplied by the
strong-induction hypothesis on the actual smaller selected quotient source,
produces a bipartite canonical ORIGINAL E-quotient atom on two real selected
classes with their exact prescribed terminal occupancy labels.
This is an induction STEP, not a recursive separation axiom or a completed
original-source theorem. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

/-- The actual smaller-source bipartite witness becomes a canonical
original-quotient atom and an ACTUAL selected-prefix pair at the exact
quotient occupancies of s and t. Old-type endpoint lifting remains
a subsequent explicit C25 application. -/
theorem actual_quotient_rank_step_canonical_edge
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    {next : CertifiedGateTower.ExactPrefix A}
    (history : History IsoGateTower.Step (CertifiedGateTower.initial A) next)
    (terminal : next.current.Terminal)
    (s t : next.current.Sorts)
    (different : ¬prefixSupport next.reduct
      (originalExactGlobalRelation A base hOne E) s t)
    (smaller :
      let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
      ActualTowerSeparation Q.current (Quotient.mk'' base)
        (original_initial_selected_quotient_one_sort A base hOne E)) :
    ∃ a : (originalCoreQuotient A base hOne E).Atom base base,
      (atomGraph (originalCoreQuotient A base hOne E) a).IsBipartite ∧
      ∃ p q : Sigma (originalExactSelectedQuotientCurrentSource
        A next.current next.reduct next.transport base hOne E).Point,
        p.1 = (Quotient.mk'' s) ∧ q.1 = (Quotient.mk'' t) ∧
        (originalCoreQuotient A base hOne E).atomRel a
          (selectedOriginalClassEquiv A next.current next.reduct
            next.transport base hOne E p)
          (selectedOriginalClassEquiv A next.current next.reduct
            next.transport base hOne E q) := by
  let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
  let Y := originalCodedQuotient A base hOne E next
  let i : Q.current.Sorts := Quotient.mk'' base
  let one : ∀ j : Q.current.Sorts, i = j :=
    original_initial_selected_quotient_one_sort A base hOne E
  obtain ⟨b,bip,code,codeGraph,codeSupport⟩ :=
    actual_quotient_rank_step_code_separator A base hOne E history
      terminal s t different smaller
  obtain ⟨x,y,hxy⟩ := Q.current.source.realized b
  have hAt : Q.code ⟨i,x⟩ ⟨i,y⟩ = code := by
    apply (codeGraph ⟨i,x⟩ ⟨i,y⟩).mpr
    simpa only [originalRelation, originalPointEquiv, Equiv.coe_fn_mk,
      AtomicSource.atomRel] using hxy
  have hInitial :
      ∃ x y : Q.current.Point i,
        Q.current.source.colour x y = some b ∧
        Q.code ⟨i,x⟩ ⟨i,y⟩ = code := ⟨x,y,hxy,hAt⟩
  obtain ⟨xp,yp,hCode⟩ := codeSupport
  let p : Sigma Y.current.Point := ⟨Quotient.mk'' s,xp⟩
  let q : Sigma Y.current.Point := ⟨Quotient.mk'' t,yp⟩
  have target : originalQuotientRootCode A next.current next.reduct
      next.transport base hOne E p q = code := hCode
  obtain ⟨a,hBP,hEdge⟩ :=
    original_selected_root_code_canonical_bipartite_edge
      A next.current next.reduct next.transport base hOne E
      b bip code hInitial p q target
  exact ⟨a,hBP,p,q,rfl,rfl,hEdge⟩

end
end CCO.AutomaticEPCore
