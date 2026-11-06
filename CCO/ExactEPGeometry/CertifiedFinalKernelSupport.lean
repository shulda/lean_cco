import CCO.ExactEPGeometry.CertifiedHistoryLabels
import CCO.ExactEPGeometry.ActualPrefixSupport

/-!
# B062 C63: final support of the ACTUAL common original exact kernel is ID

For the ORIGINAL one-sort source and a TRUE finite gate-certified
full-character history, K_com is the genuine finite meet of ALL
selected original full RAW-exact gates. Its full label-preservation
theorem has already been proved by actual history induction.

Consequently, if there is a REAL current pair of final unary types
carrying K_com, those two types are equal. Conversely every actual
terminal unary type is inhabited by its true AtomicSource provider
and the logical diagonal is contained in K_com. Thus its entire
ACTUAL support on final realized names is exactly identity.

This is the source's equality Phi_m(K_com) = Id_T, not a claim that
K_com itself is logical identity on original points, nor a false
unconditional law about intersections of empty diversity atoms.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open CCO.ExactEPGeometry.CertifiedGateTower
open RigidGroupoid.Geometry

noncomputable section

/-- C63 at genuine REALIZED terminal-type strength. There are real
points in every displayed type, and every gate relation is a real
FULL-exact original equivalence, including empty-history original Top. -/
theorem certifiedHistoryCommonOriginalKernel_support_identity
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    {terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step
      (CertifiedGateTower.initial A) terminal)
    (i j : terminal.current.Sorts) :
    prefixSupport terminal.reduct
      (originalExactGlobalRelation A base hOne
        (certifiedHistoryCommonOriginalKernel A base hOne history))
      i j ↔ i = j := by
  let E := certifiedHistoryCommonOriginalKernel A base hOne history
  have hLabels : OriginalRelationRespectsLabels terminal.reduct
      (originalExactGlobalRelation A base hOne E) :=
    certifiedHistoryCommonOriginalKernel_preserves_final_labels
      A base hOne history
  constructor
  · rintro ⟨x,y,hxy⟩
    exact hLabels ⟨i,x⟩ ⟨j,y⟩ hxy
  · intro hij
    subst j
    let x : terminal.current.Point i :=
      Classical.choice (terminal.current.source.nonemptySort i)
    refine ⟨x,x,?_⟩
    change E
      ((hOne (terminal.reduct.parent i)).symm ▸
        terminal.reduct.point i x)
      ((hOne (terminal.reduct.parent i)).symm ▸
        terminal.reduct.point i x)
    exact E.val.val.refl _

end
end CCO.ExactEPGeometry
