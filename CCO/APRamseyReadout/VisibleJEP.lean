import CCO.APRamseyReadout.RamseyReadout
import CCO.APRamseyReadout.ProperHiddenJEP
import CCO.APRamseyReadout.VisibleAmalgamation

/-! C29: actual visible JEP is read back from the proved JEP of the
entire proper ordered hidden age. Both maps use ONE host packet and its
actual support order. The block variant normalizes only that host order;
it keeps the same old maps and makes no strong-intersection assertion. -/

universe u v w p
namespace CCO.APRamseyReadout
open CCO.FullCode CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
local notation "Γ" => actualTupleInterpretation B ht F

/-- The source hidden JEP provider is instantiated internally on the
actual two templates. All host tuples are read together through ONE
actual HostReadout, with original fine colours and full support orders. -/
theorem actual_full_readout_jep : ExpandedJEP (actualFullReadoutData B ht F) := by
  intro A E a b
  obtain ⟨D,hD,⟨l⟩,⟨r⟩⟩ := proper_ordered_jep B ht
    (actualOrderedTemplate B ht F a) (actualOrderedTemplate B ht F b)
    (actualOrderedTemplate_mem B ht F a) (actualOrderedTemplate_mem B ht F b)
  rcases D with ⟨W,M,hW⟩
  rcases hD.1 with ⟨C,o,hC,hM⟩
  change M = @OrderedCoordinateModel B ht W C o at hM
  change Structure.Embedding _ M at l r
  rw [hM] at l r
  letI : Finite W := hW
  letI : LinearOrder W := o
  let R := actualHostReadout B ht F C hC
  refine ⟨R.old,R.readout,?_,?_⟩
  · exact ⟨(Γ).readoutToRelational B.homogeneous
      (actualHiddenToReadout B ht F a R l)⟩
  · exact ⟨(Γ).readoutToRelational B.homogeneous
      (actualHiddenToReadout B ht F b R r)⟩

/-- Normalize only a target support order; all literal old points,
coordinates, partial domains and non-order codes stay in the same host. -/
def normalizeActualReadout
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts)
    {E : CCO.FiniteInduced (X := B.Point)}
    (c : (actualFullReadoutData B ht F).Expansion E) :
    (Γ).BlockReadoutOn priority E :=
  ⟨⟨sortBlockOrder ((Γ).supportStructure E).sort priority c.order⟩,
    sortBlockOrder_idempotent _ _ _⟩

/-- A prescribed block source keeps the SAME original induced map into
the normalized target, because the canonical support map preserves sorts. -/
def normalizeActualReadoutEmbedding
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts)
    {A E : CCO.FiniteInduced (X := B.Point)}
    (a : (Γ).BlockReadoutOn priority A)
    (c : (actualFullReadoutData B ht F).Expansion E)
    (f : (Γ).ReadoutEmbedding B.homogeneous a.val c) :
    (Γ).ReadoutEmbedding B.homogeneous a.val
      (normalizeActualReadout B ht F priority c).val where
  old := f.old
  order_iff x y := by
    have h := sortBlockOrder_map_iff ((Γ).supportStructure A).sort
      ((Γ).supportStructure E).sort priority a.val.order c.order
      ((Γ).supportEmbedding B.homogeneous f.old).point
      ((Γ).supportEmbedding B.homogeneous f.old).sort_eq f.order_iff x y
    exact h.trans (Iff.of_eq (congrArg (fun o : LinearOrder ((Γ).support A) =>
      @LT.lt _ o.toLT x y) a.property))

/-- C29 also holds for the source's smaller block language. The actual
full JEP is proved above; it is not an assumed visible JEP callback. -/
theorem actual_small_readout_jep
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    ExpandedJEP (actualSmallReadoutData B ht F priority) := by
  intro A E a b
  obtain ⟨J,c,⟨l⟩,⟨r⟩⟩ := actual_full_readout_jep B ht F A E a.val b.val
  refine ⟨J,normalizeActualReadout B ht F priority c,?_,?_⟩
  · exact ⟨(Γ).smallReadoutToRelational priority B.homogeneous
      (normalizeActualReadoutEmbedding B ht F priority a c
        ((Γ).relationalToReadout B.homogeneous l))⟩
  · exact ⟨(Γ).smallReadoutToRelational priority B.homogeneous
      (normalizeActualReadoutEmbedding B ht F priority b c
        ((Γ).relationalToReadout B.homogeneous r))⟩

end
end CCO.APRamseyReadout
