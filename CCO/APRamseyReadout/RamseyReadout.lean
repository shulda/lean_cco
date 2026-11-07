import CCO.APRamseyReadout.ReadoutHiddenMaps
import CCO.APRamseyReadout.HostReadout
import CCO.APRamseyReadout.SmallerLanguage

/-! The actual all-host Ramsey readback. Every hidden host is realized
by ONE embedding into the same terminal target. All its valid tuples,
including those newly compatible on a generated support, are retained.
Only marked source maps are extended on support; no inverse into a
previously selected target root set is used. -/

universe u v w p z
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.FullCode
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
local notation "Γ" => actualTupleInterpretation B ht F
variable {W : Type z} {C : CCO.UnarySupport.Structure (Sig B ht) W} [LinearOrder W]

/-- Forget only the order symbols of an actual ordered template map.
Its full unary domains and literal support point map are unchanged. -/
def actualTemplateBinaryMap {A : CCO.FiniteInduced (X := B.Point)}
    (a : (actualFullReadoutData B ht F).Expansion A)
    (f : Structure.Embedding (actualOrderedTemplate B ht F a).model
      (OrderedCoordinateModel B ht C)) :
    Structure.Embedding ((Γ).supportStructure A) (CoordinateModel B ht C) where
  point := f.point
  injective := f.injective
  sort_eq := f.sort_eq
  map_func := f.map_func
  reflect_func := f.reflect_func
  unary_iff U := PEmpty.elim U
  binary_iff R x y := by
    have hh := f.binary_iff (.inl R) x y
    change (CoordinateModel B ht C).binary R (f.point x) (f.point y) ↔
      (CoordinateModel B ht (actualTemplateRaw B ht F A)).binary R x y at hh
    rw [actualTemplateRaw_binary B ht F A] at hh
    exact hh

def actualHiddenRootMap {A : CCO.FiniteInduced (X := B.Point)}
    (a : (actualFullReadoutData B ht F).Expansion A)
    (f : Structure.Embedding (actualOrderedTemplate B ht F a).model
      (OrderedCoordinateModel B ht C)) :=
  Object.fromHidden (Γ).normal ((Γ).object A) (actualTemplateBinaryMap B ht F a f)

/-- The canonical old support map agrees on every marked root with the
specified hidden embedding, and therefore on the entire generated support. -/
theorem actualHidden_support {A : CCO.FiniteInduced (X := B.Point)}
    (a : (actualFullReadoutData B ht F).Expansion A) (R : HostReadout B ht F C)
    (f : Structure.Embedding (actualOrderedTemplate B ht F a).model
      (OrderedCoordinateModel B ht C)) :
    R.support.comp ((Γ).supportEmbedding B.homogeneous
      (R.fineEmbedding B ht F (actualHiddenRootMap B ht F a f))) =
        actualTemplateBinaryMap B ht F a f := by
  apply ((Γ).object A).embedding_unique_on_coordinates
  intro x j
  have hr : (((Γ).object A).markedRoot x).map
      (R.support.comp ((Γ).supportEmbedding B.homogeneous
        (R.fineEmbedding B ht F (actualHiddenRootMap B ht F a f)))) =
      (((Γ).object A).markedRoot x).map (actualTemplateBinaryMap B ht F a f) := by
    calc
      _ = ((((Γ).object A).markedRoot x).map ((Γ).supportEmbedding B.homogeneous
          (R.fineEmbedding B ht F (actualHiddenRootMap B ht F a f)))).map R.support := rfl
      _ = (((Γ).object R.old).markedRoot
          ((R.fineEmbedding B ht F (actualHiddenRootMap B ht F a f)).toEmbedding x)).map
            R.support := congrArg (fun r => r.map R.support)
              ((Γ).supportEmbedding_root B.homogeneous _ x)
      _ = _ := R.support_root (actualHiddenRootMap B ht F a f |>.point x)
  have hc := congrArg (fun r => (⟨r.tag,r.coordinate⟩ :
    Σ t : (tupleScheme B ht F).Tag, Fin ((tupleScheme B ht F).arity t) → W)) hr
  exact congrFun (eq_of_heq (Sigma.mk.inj hc).2) j

/-- Any full hidden embedding is read back into ALL actual host owners,
with original fine colours and the entire support order reflected. -/
def actualHiddenToReadout {A : CCO.FiniteInduced (X := B.Point)}
    (a : (actualFullReadoutData B ht F).Expansion A) (R : HostReadout B ht F C)
    (f : Structure.Embedding (actualOrderedTemplate B ht F a).model
      (OrderedCoordinateModel B ht C)) :
    (Γ).ReadoutEmbedding B.homogeneous a R.readout where
  old := R.fineEmbedding B ht F (actualHiddenRootMap B ht F a f)
  order_iff x y := by
    have he := actualHidden_support B ht F a R f
    have hx := congrArg (fun g => g.point x) he
    have hy := congrArg (fun g => g.point y) he
    change R.support.point ((Γ).supportEmbedding B.homogeneous _ |>.point x) = f.point x at hx
    change R.support.point ((Γ).supportEmbedding B.homogeneous _ |>.point y) = f.point y at hy
    change (Γ).ReadoutComparison R.readout _ _ ↔ _
    rw [R.order_iff,hx,hy]
    have hh := f.binary_iff (.inr (((Γ).supportStructure A).sort x,
      ((Γ).supportStructure A).sort y)) x y
    change ((CoordinateModel B ht C).sort (f.point x) = _ ∧
      (CoordinateModel B ht C).sort (f.point y) = _ ∧ f.point x < f.point y) ↔
      (((Γ).supportStructure A).sort x = _ ∧ ((Γ).supportStructure A).sort y = _ ∧
        @LT.lt _ a.order.toLT x y) at hh
    have hsx : (CoordinateModel B ht C).sort (f.point x) = ((Γ).supportStructure A).sort x :=
      f.sort_eq x
    have hsy : (CoordinateModel B ht C).sort (f.point y) = ((Γ).supportStructure A).sort y :=
      f.sort_eq y
    simpa only [hsx,hsy,true_and] using hh

/-- Naturality retains the prescribed selected original map exactly. -/
theorem actualHiddenToReadout_comp
    {A E : CCO.FiniteInduced (X := B.Point)}
    {a : (actualFullReadoutData B ht F).Expansion A}
    {b : (actualFullReadoutData B ht F).Expansion E}
    (R : HostReadout B ht F C)
    (g : Structure.Embedding (actualOrderedTemplate B ht F b).model
      (OrderedCoordinateModel B ht C))
    (f : (Γ).ReadoutEmbedding B.homogeneous a b) :
    actualHiddenToReadout B ht F a R (g.comp (actualTemplateEmbedding B ht F f)) =
      (actualHiddenToReadout B ht F b R g).comp B.homogeneous f := by
  apply TupleInterpretation.ReadoutEmbedding.ext B.homogeneous
  intro x
  apply congrArg R.roots
  change (((Γ).object A).markedRoot x).map
      (actualTemplateBinaryMap B ht F a (g.comp (actualTemplateEmbedding B ht F f))) =
    (((Γ).object E).markedRoot (f.old.toEmbedding x)).map
      (actualTemplateBinaryMap B ht F b g)
  calc
    _ = ((((Γ).object A).markedRoot x).map
        ((Γ).supportEmbedding B.homogeneous f.old)).map
          (actualTemplateBinaryMap B ht F b g) := rfl
    _ = _ := congrArg (fun r => r.map (actualTemplateBinaryMap B ht F b g))
      ((Γ).supportEmbedding_root B.homogeneous f.old x)

/-- The actual correspondence pulls colours back along ALL hidden maps.
The source instance below supplies the hidden arrow itself. -/
theorem actualReadout_arrow
    {A E : CCO.FiniteInduced (X := B.Point)}
    (a : (actualFullReadoutData B ht F).Expansion A)
    (b : (actualFullReadoutData B ht F).Expansion E)
    (R : HostReadout B ht F C) {n : ℕ}
    (hidden : HiddenArrow (actualOrderedTemplate B ht F a).model
      (actualOrderedTemplate B ht F b).model (OrderedCoordinateModel B ht C) n) :
    ∀ color : (Γ).ReadoutEmbedding B.homogeneous a R.readout → Fin n,
      ∃ g : (Γ).ReadoutEmbedding B.homogeneous b R.readout, ∃ shade : Fin n,
        ∀ f : (Γ).ReadoutEmbedding B.homogeneous a b,
          color (g.comp B.homogeneous f) = shade := by
  intro color
  obtain ⟨g,shade,hg⟩ := hidden (fun f => color (actualHiddenToReadout B ht F a R f))
  refine ⟨actualHiddenToReadout B ht F b R g,shade,?_⟩
  intro f
  rw [← actualHiddenToReadout_comp]
  exact hg (actualTemplateEmbedding B ht F f)

/-- The full source Ramsey theorem, with every provider discharged at
the same terminal clone and every arbitrary host tuple read back. -/
theorem actual_full_readout_ramsey : (actualFullReadoutData B ht F).Ramsey := by
  intro A E a b n hn
  obtain ⟨D,hD,arrow⟩ := proper_ordered_ramsey B ht
    (actualOrderedTemplate B ht F a) (actualOrderedTemplate B ht F b)
    (actualOrderedTemplate_mem B ht F a) (actualOrderedTemplate_mem B ht F b) n hn
  rcases D with ⟨W,M,hW⟩
  rcases hD.1 with ⟨C,o,hC,hM⟩
  change M = @OrderedCoordinateModel B ht W C o at hM
  change HiddenArrow _ _ M n at arrow
  rw [hM] at arrow
  letI : Finite W := hW
  letI : LinearOrder W := o
  let R := actualHostReadout B ht F C hC
  refine ⟨R.old,R.readout,?_⟩
  intro color
  obtain ⟨g,shade,hg⟩ := actualReadout_arrow B ht F a b R arrow
    (fun f => color ((Γ).readoutToRelational B.homogeneous f))
  refine ⟨(Γ).readoutToRelational B.homogeneous g,?_⟩
  have mono (f : (actualFullReadoutData B ht F).Embedding a b) :
      color (((Γ).readoutToRelational B.homogeneous g).comp f) = shade := by
    have he : ((Γ).readoutToRelational B.homogeneous g).comp f =
        (Γ).readoutToRelational B.homogeneous
          (g.comp B.homogeneous ((Γ).relationalToReadout B.homogeneous f)) :=
      CCO.TerminalHiddenHN.RealExpansionData.Embedding.ext (fun _ => rfl)
    exact (congrArg color he).trans (hg ((Γ).relationalToReadout B.homogeneous f))
  exact fun f g => (mono f).trans (mono g).symm

/-- A prescribed block order stays a block order on the exact actual
support read back through the one whole host embedding. -/
theorem actualHostReadout_block (R : HostReadout B ht F C)
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts)
    (fixed : sortBlockOrder C.sort priority (inferInstance : LinearOrder W) =
      (inferInstance : LinearOrder W)) :
    sortBlockOrder ((Γ).supportStructure R.old).sort priority R.readout.order =
      R.readout.order := by
  apply LinearOrder.ext_lt
  intro x y
  have hh := sortBlockOrder_map_iff ((Γ).supportStructure R.old).sort
    (CoordinateModel B ht C).sort priority R.readout.order (inferInstance : LinearOrder W)
    R.support.point R.support.sort_eq (fun u v => (R.order_iff u v).symm) x y
  change @LT.lt W (sortBlockOrder C.sort priority (inferInstance : LinearOrder W)).toLT
    (R.support.point x) (R.support.point y) ↔ _ at hh
  rw [fixed] at hh
  exact hh.symm.trans (R.order_iff x y).symm

theorem actualOrderedBlockTemplate_mem
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts)
    {A : CCO.FiniteInduced (X := B.Point)} (a : (Γ).BlockReadoutOn priority A) :
    ProperBlockOrderedAge B ht priority (actualOrderedTemplate B ht F a.val) := by
  refine ⟨actualOrderedTemplate_mem B ht F a.val,?_⟩
  exact coordinateBlock_order_fixed B ht (actualTemplateRaw B ht F A) a.val.order priority a.property

/-- The source's smaller-language Ramsey arrow is obtained from the
actual proper block hidden age, with no assumed readout-arrow callback. -/
theorem actual_block_readout_ramsey
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    (Γ).BlockReadoutRamsey priority B.homogeneous := by
  intro A E a b n hn
  obtain ⟨D,hD,arrow⟩ := proper_block_ordered_ramsey B ht priority
    (actualOrderedTemplate B ht F a.val) (actualOrderedTemplate B ht F b.val)
    (actualOrderedBlockTemplate_mem B ht F priority a)
    (actualOrderedBlockTemplate_mem B ht F priority b) n hn
  rcases D with ⟨W,M,hW⟩
  rcases hD.1.1 with ⟨C,o,hC,hM⟩
  change M = @OrderedCoordinateModel B ht W C o at hM
  change HiddenArrow _ _ M n at arrow
  rw [hM] at arrow
  letI : Finite W := hW
  letI : LinearOrder W := o
  let R := actualHostReadout B ht F C hC
  have hfixed := hD.2
  change blockNormalize (CoordinateLanguage B ht) priority
    (M.reduct (coordinateBlockReduct B ht)) = M.reduct (coordinateBlockReduct B ht) at hfixed
  rw [hM] at hfixed
  have hblock := coordinateBlock_fixed_order B ht C o priority hfixed
  let c : (Γ).BlockReadoutOn priority R.old :=
    ⟨R.readout,actualHostReadout_block B ht F R priority hblock⟩
  refine ⟨R.old,c,?_⟩
  exact actualReadout_arrow B ht F a.val b.val R arrow

/-- The finite smaller language retains precisely equal-hidden-target
comparisons, with all non-order data defined in the original fine age. -/
abbrev actualSmallReadoutData (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    CCO.TerminalHiddenHN.RealExpansionData.{u,v,w,max u v w,max u v} B.source :=
  (Γ).smallReadoutExpansion priority B.homogeneous

theorem actualSmallReadoutData_reasonable
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    (actualSmallReadoutData B ht F priority).Reasonable :=
  (Γ).smallReadoutExpansion_reasonable priority B.homogeneous

theorem actual_small_readout_ramsey
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    (actualSmallReadoutData B ht F priority).Ramsey :=
  (Γ).smallReadoutExpansion_ramsey priority B.homogeneous
    (actual_block_readout_ramsey B ht F priority)

end
end CCO.APRamseyReadout
