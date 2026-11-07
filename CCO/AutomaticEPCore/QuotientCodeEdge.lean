import CCO.AutomaticEPCore.QuotientAtomTransport
import CCO.AutomaticEPCore.QuotientRootCode

/-! An actual fixed ROOT predicate code produced by a real bipartite
initial selected quotient atom recognizes the SAME canonical old E-quotient
atom on later selected source classes. This is a conditional code-to-edge
interface; it does NOT manufacture the lower-rank recursive separator. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

theorem original_selected_root_code_canonical_bipartite_edge
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (hP : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (b : (originalCodedQuotient A base hOne E
      (CertifiedGateTower.initial A)).current.source.Atom
        (Quotient.mk'' base) (Quotient.mk'' base))
    (bip : (atomGraph (originalCodedQuotient A base hOne E
      (CertifiedGateTower.initial A)).current.source b).IsBipartite)
    (code : Age.Colour A.source → Prop)
    (initial :
      ∃ x y : (originalCodedQuotient A base hOne E
        (CertifiedGateTower.initial A)).current.Point (Quotient.mk'' base),
        (originalCodedQuotient A base hOne E
          (CertifiedGateTower.initial A)).current.source.colour x y = some b ∧
        (originalCodedQuotient A base hOne E
          (CertifiedGateTower.initial A)).code
          ⟨Quotient.mk'' base,x⟩ ⟨Quotient.mk'' base,y⟩ = code)
    (p q : Sigma (originalExactSelectedQuotientCurrentSource
      A B P hP base hOne E).Point)
    (targetCode : originalQuotientRootCode
      A B P hP base hOne E p q = code) :
    ∃ a : (originalCoreQuotient A base hOne E).Atom base base,
      (atomGraph (originalCoreQuotient A base hOne E) a).IsBipartite ∧
      (originalCoreQuotient A base hOne E).atomRel a
        (selectedOriginalClassEquiv A B P hP base hOne E p)
        (selectedOriginalClassEquiv A B P hP base hOne E q) := by
  let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
  let i : Q.current.Sorts := Quotient.mk'' base
  obtain ⟨x,y,hxy,hxyCode⟩ := initial
  obtain ⟨a,hBP,hPairs⟩ :=
    initial_selected_bipartite_atom_to_original_quotient A base hOne E b bip
  have hCanonInitial :
      (originalCoreQuotient A base hOne E).colour
        (initialSelectedQuotientPointEquiv A base hOne E x)
        (initialSelectedQuotientPointEquiv A base hOne E y) = some a :=
    (hPairs x y).mp hxy
  have hCodes :
      originalQuotientRootCode A B P hP base hOne E p q =
        originalQuotientRootCode A A (UnaryReduct.identity A.source)
          (ExactTraceTransport.identity A.source) base hOne E
          ⟨i,x⟩ ⟨i,y⟩ :=
    targetCode.trans hxyCode.symm
  have hCanon :=
    selected_root_code_canonical_colour A A B
      (UnaryReduct.identity A.source) P
      (ExactTraceTransport.identity A.source) hP
      base hOne E ⟨i,x⟩ ⟨i,y⟩ p q hCodes
  refine ⟨a,hBP,?_⟩
  change (originalCoreQuotient A base hOne E).colour
    (selectedOriginalClassEquiv A B P hP base hOne E p)
    (selectedOriginalClassEquiv A B P hP base hOne E q) = some a
  exact hCanon.trans hCanonInitial

end
end CCO.AutomaticEPCore
