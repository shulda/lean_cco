import CCO.AutomaticEPCore.QuotientSource
import CCO.ExactEPGeometry.OriginalCodedQuotientSafeHistory
import CCO.AutomaticEPCore.FunctionalTypes

/-! The fixed original E-saturated predicate code at the ACTUAL initial
selected quotient names exactly its complete original quotient orbitals.
Thus an actual recursively obtained old bipartite atom is recoverable
through the SAME predicate code at the receiving endpoint. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
noncomputable section

theorem original_initial_quotient_code_complete
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (q s q' s' : Sigma (originalCodedQuotient A base hOne E
      (CertifiedGateTower.initial A)).current.Point) :
    (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)).code q' s' =
        (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)).code q s ↔
      taggedColour
        (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)).current.source q' s' =
      taggedColour
        (originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)).current.source q s := by
  let P := UnaryReduct.identity A.source
  let transport := ExactTraceTransport.identity A.source
  let rep := originalSelectedTaggedRepresentative A A P transport base hOne E
  let S := currentOriginalExactSetoid A A P base hOne E
  constructor
  · intro codes
    apply (originalExactSelectedTaggedColour_iff_globalBlock
      A A P transport base hOne E q s q' s').mpr
    refine ⟨?_,?_,?_⟩
    · exact (original_initial_selected_quotient_one_sort A base hOne E q'.1).symm.trans
        (original_initial_selected_quotient_one_sort A base hOne E q.1)
    · exact (original_initial_selected_quotient_one_sort A base hOne E s'.1).symm.trans
        (original_initial_selected_quotient_one_sort A base hOne E s.1)
    · have seed : originalCurrentExactSaturatedColour A A P base hOne E
          (taggedColour A.source (rep q) (rep s)) (rep q) (rep s) :=
        ⟨rep q,rep s,S.refl _,rfl,S.refl _⟩
      have atSeed := congrFun codes (taggedColour A.source (rep q) (rep s))
      exact Eq.mpr atSeed seed
  · intro colours
    exact originalQuotientRootCode_colour A A P transport base hOne E q' s' q s colours

/-- Each ACTUAL original quotient atom has one literal fixed-code value,
recognized on every tagged original quotient pair. The real diversity
atom is never confused with the quotient diagonal or a new unary name. -/
theorem original_initial_quotient_atom_code
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base) :
    let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
    let i : Q.current.Sorts := Quotient.mk'' base
    let one : ∀ j : Q.current.Sorts, i = j :=
      original_initial_selected_quotient_one_sort A base hOne E
    ∀ b : Q.current.source.Atom i i,
      ∃ code : Age.Colour A.source → Prop,
        ∀ p q : Sigma Q.current.Point,
          Q.code p q = code ↔
            originalRelation Q.current i one (Q.current.source.atomRel b) p q := by
  dsimp only
  let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
  let i : Q.current.Sorts := Quotient.mk'' base
  let one : ∀ j : Q.current.Sorts, i = j :=
    original_initial_selected_quotient_one_sort A base hOne E
  intro b
  obtain ⟨x,y,hxy⟩ := Q.current.source.realized b
  refine ⟨Q.code ⟨i,x⟩ ⟨i,y⟩,?_⟩
  intro p q
  have complete := original_initial_quotient_code_complete A base hOne E
    ⟨i,x⟩ ⟨i,y⟩ p q
  rw [original_tagged_colour_one_sort Q.current i one p q,
    original_tagged_colour_one_sort Q.current i one ⟨i,x⟩ ⟨i,y⟩] at complete
  simpa only [originalRelation,originalPointEquiv,Equiv.coe_fn_mk,hxy,AtomicSource.atomRel,
    Sigma.mk.injEq,heq_eq_eq,true_and] using complete

end
end CCO.AutomaticEPCore
