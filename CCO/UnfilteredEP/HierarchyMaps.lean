import CCO.UnfilteredEP.HierarchyOrders

/-!
# B064 C44/C46: actual induced maps commute with synchronized normalization

All upward-key and chart commutation laws are proved from preservation of
existing named unary terms. The normalized comparison is preserved on the
SAME old point map. No extra embedding-extension or chart oracle enters.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z a
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ResetOrder.Hierarchy
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable {V : Type z} {W : Type a}
variable {C : CCO.UnarySupport.Structure (Sig B ht) V}
variable {D : CCO.UnarySupport.Structure (Sig B ht) W}
variable (hC : ActualAge B ht C) (hD : ActualAge B ht D) (e : C.Embedding D)

/-- The old induced map, on actual proper-sort fibres. -/
def cutGeometryMap : (actualCutSystem B ht C hC).Map (actualCutSystem B ht D hD) where
  point i x := ⟨e.point x.val,(e.sort_eq x.val).trans x.property⟩
  injective i := by
    intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  up_commute i a x := Subtype.ext (actual_upward_embedding_commutes B ht C hC hD e i a x).symm

private theorem dependent_cast_map {I : Type*} {X Y : I → Type*}
    (f : ∀ i, X i → Y i) {i j : I} (h : i = j) (x : X i) :
    Equiv.cast (congrArg Y h) (f i x) = f j (Equiv.cast (congrArg X h) x) := by
  cases h
  rfl

/-- The actual orbit reindexing changes neither points nor the commuting
upward-key maps. -/
def orbitGeometryMap :
    (reindexedCutSystem B ht C hC).Map (reindexedCutSystem B ht D hD) where
  point i := (cutGeometryMap B ht hC hD e).point (cutOrbitEquiv B ht i)
  injective i := (cutGeometryMap B ht hC hD e).injective (cutOrbitEquiv B ht i)
  up_commute i a x := by
    let f := cutGeometryMap B ht hC hD e
    let heq := (cutOrbitEquiv B ht).apply_symm_apply
      ((actualCutSchedule B).coordinate (cutOrbitEquiv B ht i) a)
    change Equiv.cast (congrArg (HiddenCutCarrier B ht D) heq.symm)
      ((actualCutSystem B ht D hD).up (cutOrbitEquiv B ht i) a (f.point _ x)) =
        f.point _ (Equiv.cast (congrArg (HiddenCutCarrier B ht C) heq.symm)
          ((actualCutSystem B ht C hC).up (cutOrbitEquiv B ht i) a x))
    rw [f.up_commute]
    exact dependent_cast_map f.point heq.symm _

/-- All chart maps are named inverse paths. Thus old inducedness proves
commutation with the chosen chart, at EVERY actual finite input point. -/
theorem actual_chart_back_commutes (r : CutOrbit B ht) (j : CutInOrbit B ht r)
    (x : HiddenCutCarrier B ht C j.val) :
    (actualCutCharting B ht D hD).back r j ((orbitGeometryMap B ht hC hD e).point ⟨r,j⟩ x) =
      (orbitGeometryMap B ht hC hD e).point ⟨r,cutRepresentative B ht r⟩
        ((actualCutCharting B ht C hC).back r j x) := by
  let p := (NamedCutPath.ambientPaths (B := B) (ht := ht)).representativePath
    (cutRepresentative B ht) r j
  change finitePathValue B ht D hD p.inverse
      ⟨e.point x.val,(e.sort_eq x.val).trans x.property⟩ =
    ⟨e.point (finitePathValue B ht C hC p.inverse x).val,_⟩
  exact Subtype.ext (finitePathValue_embedding_commutes B ht C hC hD e p.inverse x).symm

variable (oC : LinearOrder V) (oD : LinearOrder W)
variable (ordered : ∀ x y, @LT.lt _ oD.toLT (e.point x) (e.point y) ↔ @LT.lt _ oC.toLT x y)

include ordered in
/-- The independent representative-fibre tasks are preserved before the
coarse-first recursion is run. -/
theorem actual_localTasks_preserve (i : Sigma (CutInOrbit B ht))
    (x y : HiddenCutCarrier B ht C (cutOrbitEquiv B ht i))
    (h : ((actualCutCharting B ht C hC).localTasks (cutInputOrders B ht C hC oC) i).lt x y) :
    ((actualCutCharting B ht D hD).localTasks (cutInputOrders B ht D hD oD) i).lt
      ((orbitGeometryMap B ht hC hD e).point i x) ((orbitGeometryMap B ht hC hD e).point i y) := by
  rcases i with ⟨r,j⟩
  refine ⟨((orbitGeometryMap B ht hC hD e).parent_iff _ x y).mpr h.1,?_⟩
  change @LT.lt _ oD.toLT
    ((actualCutCharting B ht D hD).back r j ((orbitGeometryMap B ht hC hD e).point ⟨r,j⟩ x)).val
    ((actualCutCharting B ht D hD).back r j ((orbitGeometryMap B ht hC hD e).point ⟨r,j⟩ y)).val
  rw [actual_chart_back_commutes B ht hC hD e,actual_chart_back_commutes B ht hC hD e]
  exact (ordered _ _).mpr h.2

include ordered in
/-- Actual normalized sort comparisons are preserved and reflected by
every original ordered induced map. -/
theorem normalizedCutOrders_map_iff (i : Sigma (CutInOrbit B ht))
    (x y : HiddenCutCarrier B ht C (cutOrbitEquiv B ht i)) :
    (normalizedCutOrders B ht D hD oD i).lt
      ((orbitGeometryMap B ht hC hD e).point i x) ((orbitGeometryMap B ht hC hD e).point i y) ↔
      (normalizedCutOrders B ht C hC oC i).lt x y :=
  (orbitGeometryMap B ht hC hD e).normalize_reflects _ _
    (actual_localTasks_preserve B ht hC hD e oC oD ordered) i x y

variable (properC : ∀ x, ProperSort B ht (C.sort x))
variable (properD : ∀ x, ProperSort B ht (D.sort x))

/-- Carrier decomposition is natural on the same old point map. -/
theorem orbitCarrierEquiv_natural (x : V) :
    orbitCarrierEquiv B ht D properD (e.point x) =
      ⟨(orbitCarrierEquiv B ht C properC x).1,
        (orbitGeometryMap B ht hC hD e).point _ (orbitCarrierEquiv B ht C properC x).2⟩ := by
  apply (orbitCarrierEquiv B ht D properD).symm.injective
  rw [Equiv.symm_apply_apply,orbitCarrierEquiv_symm]
  exact congrArg e.point ((orbitCarrierEquiv B ht C properC).symm_apply_apply x).symm

include ordered in
/-- The global fixed-priority hierarchical comparison is preserved and
reflected on the SAME entire finite carrier. -/
theorem hierarchicalOrder_map_iff (priority : LinearOrder (Sig B ht).Sorts) (x y : V) :
    @LT.lt _ (hierarchicalOrder B ht D properD hD priority oD).toLT (e.point x) (e.point y) ↔
      @LT.lt _ (hierarchicalOrder B ht C properC hC priority oC).toLT x y := by
  let f := orbitGeometryMap B ht hC hD e
  have preserve : ∀ x y,
      @LT.lt _ (hierarchicalOrder B ht C properC hC priority oC).toLT x y →
      @LT.lt _ (hierarchicalOrder B ht D properD hD priority oD).toLT (e.point x) (e.point y) := by
    intro x y hxy
    change (sortOrder (orbitSortPriority B ht priority) (normalizedCutOrders B ht D hD oD)).lt
      (orbitCarrierEquiv B ht D properD (e.point x)) (orbitCarrierEquiv B ht D properD (e.point y))
    rw [orbitCarrierEquiv_natural B ht hC hD e properC properD,
      orbitCarrierEquiv_natural B ht hC hD e properC properD]
    exact sortOrder_map (orbitSortPriority B ht priority) _ _ f.point
      (fun i x y h => (normalizedCutOrders_map_iff B ht hC hD e oC oD ordered i x y).mpr h) _ _ hxy
  constructor
  · intro h
    by_cases he : x = y
    · subst y
      exact False.elim (@lt_irrefl _ (hierarchicalOrder B ht D properD hD priority oD).toPreorder _ h)
    · letI := hierarchicalOrder B ht C properC hC priority oC
      rcases lt_or_gt_of_ne he with hxy | hyx
      · exact hxy
      · exact False.elim (@lt_asymm _ (hierarchicalOrder B ht D properD hD priority oD).toPreorder _ _ h (preserve y x hyx))
  · exact preserve x y

end
end CCO.UnfilteredEP
