import CCO.UnfilteredEP.HiddenAgeTransport
import CCO.APRamseyReadout.RamseyReadout

/-! The entire canonical support read from an arbitrary host embeds
back into that same host. No root-generation assumption is used. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w p z
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable {W : Type z} {C : CCO.UnarySupport.Structure (Sig B ht) W} [LinearOrder W]
variable (R : HostReadout B ht F C)
local notation "Γ" => actualTupleInterpretation B ht F

/-- All partial domains, fine cylinders and complete support order
comparisons use the SAME canonical support point map. -/
def hostReadoutTemplateMap :
    Structure.Embedding (actualOrderedTemplate B ht F R.readout).model
      (OrderedCoordinateModel B ht C) where
  point := R.support.point
  injective := R.support.injective
  sort_eq := R.support.sort_eq
  map_func := R.support.map_func
  reflect_func := R.support.reflect_func
  unary_iff U := PEmpty.elim U
  binary_iff predicate x y := by
    cases predicate with
    | inl predicate =>
      have hh := R.support.binary_iff predicate x y
      have hb := congrArg (fun M : Structure (CoordinateLanguage B ht) ((Γ).support R.old) =>
        M.binary predicate x y) (actualTemplateRaw_binary B ht F R.old).symm
      exact hh.trans (Iff.of_eq hb)
    | inr sorts =>
      change ((CoordinateModel B ht C).sort (R.support.point x) = sorts.1 ∧
        (CoordinateModel B ht C).sort (R.support.point y) = sorts.2 ∧
        R.support.point x < R.support.point y) ↔
        (((Γ).supportStructure R.old).sort x = sorts.1 ∧
          ((Γ).supportStructure R.old).sort y = sorts.2 ∧
          @LT.lt _ R.readout.order.toLT x y)
      rw [R.support.sort_eq,R.support.sort_eq]
      exact and_congr Iff.rfl (and_congr Iff.rfl (R.order_iff x y).symm)

end
end CCO.UnfilteredEP
