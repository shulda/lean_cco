import CCO.HKNReservoir.PacketOrigins
import CCO.HKNReservoir.SourcePacketRecovery
import CCO.HKNReservoir.SourceAutomorphisms
import CCO.HKNReservoir.NamedPairPalette

universe v w t y
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y}
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)

def sourceOrigin (i : PacketRecovery.PacketIndex E) : Z :=
  PacketRecovery.origin (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) E hLocal
    (finiteSource_regularData S H R B hB A hA) i

def sourceOriginOwner (i : PacketRecovery.PacketIndex E) : ↥B :=
  PacketRecovery.owner (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) E hLocal
    (sourceOrigin S H R B hB Δ A hA E hLocal i)

def sourceOriginEdge (i j : PacketRecovery.PacketIndex E) : Option (S.Atom () ()) :=
  PacketRecovery.originEdge (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) E hLocal
    (finiteSource_regularData S H R B hB A hA) i j

theorem sourceOriginEdge_some (i j : PacketRecovery.PacketIndex E) (a : S.Atom () ()) :
    sourceOriginEdge S H R B hB Δ A hA E hLocal i j = some a ↔
    E.rel (.fine a) (![sourceOrigin S H R B hB Δ A hA E hLocal i,sourceOrigin S H R B hB Δ A hA E hLocal j]) :=
  PacketRecovery.originEdge_some _ _ E hLocal (finiteSource_regularData S H R B hB A hA)
    (finiteSource_fineData S H R B hB A hA) i j a

/-- The actual origin partial diagram retains exactly the original
reservoir records; no hole is completed by this definition. -/
def sourceOriginPattern : OriginPattern S H R (PacketRecovery.PacketIndex E) where
  owner i := (sourceOriginOwner S H R B hB Δ A hA E hLocal i).val
  edge := sourceOriginEdge S H R B hB Δ A hA E hLocal
  symmetric := PacketRecovery.originEdge_symmetric _ _ E hLocal
    (finiteSource_regularData S H R B hB A hA) (finiteSource_fineData S H R B hB A hA)
  diagonal := PacketRecovery.originEdge_diagonal _ _ E hLocal
    (finiteSource_regularData S H R B hB A hA) (finiteSource_fineData S H R B hB A hA)
  nonthin := by
    intro i j a ha
    let D := finiteSourceData S H R B hB A hA
    let tag := sourceTag S H R B Δ
    let hD := finiteSource_regularData S H R B hB A hA
    let hFine := finiteSource_fineData S H R B hB A hA
    let x := sourceOrigin S H R B hB Δ A hA E hLocal i
    let y := sourceOrigin S H R B hB Δ A hA E hLocal j
    have hEdge := (sourceOriginEdge_some S H R B hB Δ A hA E hLocal i j a).mp ha
    have hij : i ≠ j := by
      intro he
      subst j
      exact PacketRecovery.fine_irreflexive tag D E hLocal hFine x a hEdge
    have hne : E.closureAtSet x ≠ E.closureAtSet y :=
      PacketRecovery.origin_closures_distinct tag D E hLocal hD hij
    have hm : E.rel (.fine a) (![PacketRecovery.move tag D E hLocal 1 x,PacketRecovery.move tag D E hLocal 1 y]) := by
      simpa only [PacketRecovery.move_one tag D E hLocal hD] using hEdge
    exact recovered_recorded_nonthin S H R B hB tag A hA E hLocal x y a hEdge hne 1 1 a hm

theorem sourceOriginPattern_edge (i j : PacketRecovery.PacketIndex E) (a : S.Atom () ()) :
    (sourceOriginPattern S H R B hB Δ A hA E hLocal).edge i j = some a ↔
      E.rel (.fine a) (![sourceOrigin S H R B hB Δ A hA E hLocal i,
        sourceOrigin S H R B hB Δ A hA E hLocal j]) :=
  sourceOriginEdge_some S H R B hB Δ A hA E hLocal i j a

/-- ONE global inverse language lift unlabels BOTH faithful pair images,
so the palette witness has the actual recovered origin owners. -/
theorem sourceOriginPalette (i j : PacketRecovery.PacketIndex E) (a : S.Atom () ())
    (ha : (sourceOriginPattern S H R B hB Δ A hA E hLocal).edge i j = some a) :
    ∃ p : SafeReadings.TransversalSource.Palette S H R B
      (sourceOriginOwner S H R B hB Δ A hA E hLocal i)
      (sourceOriginOwner S H R B hB Δ A hA E hLocal j), p.val = a := by
  let tag := sourceTag S H R B Δ
  let D := finiteSourceData S H R B hB A hA
  let x := sourceOrigin S H R B hB Δ A hA E hLocal i
  let y := sourceOrigin S H R B hB Δ A hA E hLocal j
  have hEdge := (sourceOriginPattern_edge S H R B hB Δ A hA E hLocal i j a).mp ha
  let e := PacketRecovery.pairEmbedding tag D E hLocal x y a hEdge
  let p := PacketRecovery.leftPoint E x y
  let q := PacketRecovery.rightPoint E x y
  have hx : D.owner (e p) = tag e.lang (PacketRecovery.owner tag D E hLocal x) := by
    exact (e.map_rel_iff (.owner (PacketRecovery.owner tag D E hLocal x)) (fun _ => p)).mpr
      ((PacketRecovery.owner_iff tag D E hLocal x _).mpr rfl)
  have hy : D.owner (e q) = tag e.lang (PacketRecovery.owner tag D E hLocal y) := by
    exact (e.map_rel_iff (.owner (PacketRecovery.owner tag D E hLocal y)) (fun _ => q)).mpr
      ((PacketRecovery.owner_iff tag D E hLocal y _).mpr rfl)
  have hbase := (PacketRecovery.embedding_fine tag D E (PacketRecovery.pair_closed E x y) e a p q).mp hEdge
  obtain ⟨σ,hσ⟩ := ambientLift S H R B hB Δ e.lang⁻¹
  let f := automorphismEmbedding tag σ
  have hox := source_embedding_owner f (e p).val
  have hoy := source_embedding_owner f (e q).val
  change (sourceData S H R B hB).owner (f (e p).val) = tag σ.lang (D.owner (e p)) at hox
  change (sourceData S H R B hB).owner (f (e q).val) = tag σ.lang (D.owner (e q)) at hoy
  rw [hσ,hx,map_inv] at hox
  rw [hσ,hy,map_inv] at hoy
  have hox' : ownerLabel S H R B (f (e p).val).down = PacketRecovery.owner tag D E hLocal x := by
    exact hox.trans ((tag e.lang).symm_apply_apply _)
  have hoy' : ownerLabel S H R B (f (e q).val).down = PacketRecovery.owner tag D E hLocal y := by
    exact hoy.trans ((tag e.lang).symm_apply_apply _)
  have hcol : col S (f (e p).val).down.val (f (e q).val).down.val = some a :=
    (source_embedding_colour f (e p).val (e q).val).trans hbase
  exact named_pair_palette S H R B a (f (e p).val).down (f (e q).val).down hox' hoy' hcol
    ((sourceOriginPattern S H R B hB Δ A hA E hLocal).nonthin i j a ha)

/-- The recovered real action has the ACTUAL possibly nonfaithful owner
translation, using centrality of every allowed owner-language component. -/
theorem recovered_owner_move (g : ResidualData.PacketGroup S H) (x : Z) :
    PacketRecovery.owner (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) E hLocal
      (PacketRecovery.move (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) E hLocal g x) =
    SafeReadings.TransversalGauge.moveOwner S H R B hB g
      (PacketRecovery.owner (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) E hLocal x) := by
  let tag := sourceTag S H R B Δ
  let D := finiteSourceData S H R B hB A hA
  let hP : E.IsClosed (E.closureAtSet x) := E.isClosed_closureSet {x}
  let e := PacketRecovery.closureEmbedding tag D E hLocal x
  let p : E.closureAtSet x := ⟨x,E.mem_closureAtSet x⟩
  let pg : E.closureAtSet x := ⟨PacketRecovery.move tag D E hLocal g x,
    PacketRecovery.move_closed tag D E hLocal hP g p.property⟩
  have hx := PacketRecovery.embedding_owner tag D E hLocal hP e p
  have hg := PacketRecovery.embedding_owner tag D E hLocal hP e pg
  apply (tag e.lang).injective
  calc
    _ = D.owner (e pg) := hg.symm
    _ = D.owner (D.move g (e p)) := congrArg D.owner (PacketRecovery.embedding_move tag D E hLocal hP e g p)
    _ = SafeReadings.TransversalGauge.moveOwner S H R B hB g (D.owner (e p)) := rfl
    _ = SafeReadings.TransversalGauge.moveOwner S H R B hB g (tag e.lang (PacketRecovery.owner tag D E hLocal x)) :=
      congrArg (SafeReadings.TransversalGauge.moveOwner S H R B hB g) hx
    _ = _ := (SafeReadings.TransversalPure.commute S H R B hB e.lang.val g _).symm

/-- Recover the origin object directly from ACTUAL HKN faithfulness. -/
def faithfulOriginPattern
    (ψ : Structure.Embedding (sourceAction S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
    (hf : Structure.IsIrreducibleStructureFaithful (sourceAction S H R B Δ) ψ) :
    OriginPattern S H R (PacketRecovery.PacketIndex E) :=
  sourceOriginPattern S H R B hB Δ A hA E (locallyInSource_of_faithful (sourceTag S H R B Δ) ψ hf)

end
end CCO.HKNReservoir
