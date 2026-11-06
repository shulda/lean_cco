import CCO.AutomaticEPCore.QuotientAtomReadback
import CCO.AutomaticEPCore.QuotientSeparator

/-! An initial selected quotient diversity atom with a bipartite graph
corresponds to one ACTUAL canonical original E-quotient diversity atom.
The canonical map is the previously proved full, onto E-class equivalence,
not a representative section. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ParityHasse.Original
noncomputable section

/-- Transfer a bipartite diversity atom through the actual bijection of
initial selected quotient points with old E-classes. All PAIR colours
are preserved and reflected via the full original quotient readback. -/
theorem initial_selected_bipartite_atom_to_original_quotient
    (A : CurrentSource.{u,v,w,t}) (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) (E : ExactEq A.source base)
    (b : (originalCodedQuotient A base hOne E
      (CertifiedGateTower.initial A)).current.source.Atom
        (Quotient.mk'' base) (Quotient.mk'' base))
    (hb : (atomGraph
      (originalCodedQuotient A base hOne E
        (CertifiedGateTower.initial A)).current.source b).IsBipartite) :
    ∃ a : (originalCoreQuotient A base hOne E).Atom base base,
      (atomGraph (originalCoreQuotient A base hOne E) a).IsBipartite ∧
      ∀ x y : (originalCodedQuotient A base hOne E
        (CertifiedGateTower.initial A)).current.Point (Quotient.mk'' base),
        (originalCodedQuotient A base hOne E
          (CertifiedGateTower.initial A)).current.source.colour x y = some b ↔
        (originalCoreQuotient A base hOne E).colour
          (initialSelectedQuotientPointEquiv A base hOne E x)
          (initialSelectedQuotientPointEquiv A base hOne E y) = some a := by
  let Q := originalCodedQuotient A base hOne E (CertifiedGateTower.initial A)
  let U := originalCoreQuotientCurrentSource A base hOne E
  let i : Q.current.Sorts := Quotient.mk'' base
  let e := initialSelectedQuotientPointEquiv A base hOne E
  obtain ⟨x,y,hxy⟩ := Q.current.source.realized b
  have hne : x ≠ y := by
    intro h
    have same : (⟨i,x⟩ : Sigma Q.current.Point) = ⟨i,y⟩ :=
      congrArg (Sigma.mk i) h
    have hn : Q.current.source.colour x y = none :=
      (Q.current.source.colour_none_iff x y).mpr same
    rw [hxy] at hn
    cases hn
  have hneE : (⟨base,e x⟩ : Sigma U.Point) ≠ ⟨base,e y⟩ := by
    intro h
    have same : e x = e y := by
      exact eq_of_heq (Sigma.mk.inj h).2
    exact hne (e.injective same)
  obtain ⟨a,ha⟩ := U.source.some_colour_of_ne (e x) (e y) hneE
  have readback (p q : Q.current.Point i) :
      Q.current.source.colour p q = some b ↔
        U.source.colour (e p) (e q) = some a := by
    have h := initial_selected_quotient_colour_iff_canonical A base hOne E x y p q
    change Q.current.source.colour p q = Q.current.source.colour x y ↔
      U.source.colour (e p) (e q) = U.source.colour (e x) (e y) at h
    simpa only [hxy,ha] using h
  let pull : (atomGraph U.source a) →g (atomGraph Q.current.source b) :=
    { toFun := e.symm
      map_rel' := by
        intro p q hpq
        change U.source.colour p q = some a at hpq
        change Q.current.source.colour (e.symm p) (e.symm q) = some b
        apply (readback (e.symm p) (e.symm q)).mpr
        simpa only [e.apply_symm_apply] using hpq }
  exact ⟨a, SimpleGraph.Colorable.of_hom pull hb,readback⟩

end
end CCO.AutomaticEPCore
