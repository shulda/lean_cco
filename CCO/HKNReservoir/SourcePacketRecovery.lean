import CCO.HKNReservoir.PacketMatrices
import CCO.HKNReservoir.SourceEncoding

universe u v w z x y t
namespace CCO.HKNReservoir
open AllThoseEPPA

namespace RegularData
variable {B : Type u} {K : Type v} [Group K] {Atom : Type w} {V : Type x}
theorem restrict {D : Data B K Atom V} (hD : RegularData D)
    (A : Set V) (hA : (encode D).IsClosed A) : RegularData (D.restrict A hA) where
  one x := Subtype.ext (hD.one x.val)
  mul g h x := Subtype.ext (hD.mul g h x.val)
  free x := by
    intro g h he
    exact hD.free x.val (congrArg Subtype.val he)
end RegularData

namespace FineData
variable {B : Type u} {K : Type v} [Group K] {Atom : Type w} {V : Type x}
theorem restrict {D : Data B K Atom V} (hD : FineData D)
    (A : Set V) (hA : (encode D).IsClosed A) : FineData (D.restrict A hA) where
  irreflexive a x := hD.irreflexive a x.val
  unique a b x y := hD.unique a b x.val y.val
  symmetric a x y := hD.symmetric a x.val y.val
  complete x y hxy := hD.complete x.val y.val (fun he => hxy (Subtype.ext he))
end FineData

noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

theorem source_regularData : RegularData (sourceData S H R B hB) where
  one := source_move_one S H R B hB
  mul := source_move_mul S H R B hB
  free := source_move_free S H R B hB

theorem source_fineData : FineData (sourceData S H R B hB) where
  irreflexive a x ha := by
    have hd : col S x.down.val x.down.val = none := (col_none S _ _).mpr rfl
    change col S x.down.val x.down.val = some a at ha
    rw [hd] at ha
    cases ha
  unique a b x y ha hb := Option.some.inj (ha.symm.trans hb)
  symmetric a x y ha := (col_symm S y.down.val x.down.val).trans ha
  complete x y := source_fine_complete S H R B hB

theorem finiteSource_regularData (A : Set (SourceCarrier S H R B))
    (hA : (sourceStructure S H R B hB).IsClosed A) :
    RegularData (finiteSourceData S H R B hB A hA) :=
  (source_regularData S H R B hB).restrict A hA

theorem finiteSource_fineData (A : Set (SourceCarrier S H R B))
    (hA : (sourceStructure S H R B hB).IsClosed A) :
    FineData (finiteSourceData S H R B hB A hA) :=
  (source_fineData S H R B hB).restrict A hA

variable {Γ : Type z} [Group Γ] (tag : Γ →* Equiv.Perm ↥B)
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y}
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource tag (encode (finiteSourceData S H R B hB A hA)) E)

/-- Actual internal old thin colours, recovered from unrestricted output. -/
theorem recovered_internal_fine (x : Z) (g h : ResidualData.PacketGroup S H) (a : S.Atom () ()) :
    E.rel (.fine a) (![PacketRecovery.move tag (finiteSourceData S H R B hB A hA) E hLocal g x,
      PacketRecovery.move tag (finiteSourceData S H R B hB A hA) E hLocal h x]) ↔
      switchColour S (finitePacket S H) (g*h) none = some a := by
  have hr := PacketRecovery.internal_matrix_reflection tag (finiteSourceData S H R B hB A hA) E hLocal x g h a
  apply hr.trans
  change col S (g.val _) (h.val _) = some a ↔ _
  rw [two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H)]
  rw [(col_none S _ _).mpr rfl]

/-- Reflection recovers the literal ENTIRE matrix from a single origin edge. -/
theorem recovered_matrix_law (x y : Z) (a : S.Atom () ()) (ha : E.rel (.fine a) (![x,y]))
    (g h : ResidualData.PacketGroup S H) (c : S.Atom () ()) :
    E.rel (.fine c) (![PacketRecovery.move tag (finiteSourceData S H R B hB A hA) E hLocal g x,
      PacketRecovery.move tag (finiteSourceData S H R B hB A hA) E hLocal h y]) ↔
      switchColour S (finitePacket S H) (g*h) (some a) = some c := by
  let D := finiteSourceData S H R B hB A hA
  let e := PacketRecovery.pairEmbedding tag D E hLocal x y a ha
  let p := PacketRecovery.leftPoint E x y
  let q := PacketRecovery.rightPoint E x y
  have hbase := (PacketRecovery.embedding_fine tag D E (PacketRecovery.pair_closed E x y) e a p q).mp ha
  have hr := PacketRecovery.recorded_matrix_reflection tag D E hLocal x y a ha g h c
  apply hr.trans
  change col S (g.val (e p).val.down.val) (h.val (e q).val.down.val) = some c ↔ _
  rw [two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H)]
  change col S (e p).val.down.val (e q).val.down.val = some a at hbase
  rw [hbase]

/-- The two faithful source packet images are genuinely distinct F-classes. -/
theorem recovered_pair_source_nonthin (x y : Z) (a : S.Atom () ())
    (ha : E.rel (.fine a) (![x,y])) (hne : E.closureAtSet x ≠ E.closureAtSet y) :
    let e := PacketRecovery.pairEmbedding tag (finiteSourceData S H R B hB A hA) E hLocal x y a ha
    ¬finitePacket S H (e (PacketRecovery.leftPoint E x y)).val.down.val
      (e (PacketRecovery.rightPoint E x y)).val.down.val := by
  let D := finiteSourceData S H R B hB A hA
  let e := PacketRecovery.pairEmbedding tag D E hLocal x y a ha
  let p := PacketRecovery.leftPoint E x y
  let q := PacketRecovery.rightPoint E x y
  change ¬finitePacket S H (e p).val.down.val (e q).val.down.val
  intro hF
  obtain ⟨g,hg,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
    (e p).val.down.val (e q).val.down.val hF
  apply PacketRecovery.pair_source_orbits_distinct tag D E hLocal
    (finiteSource_regularData S H R B hB A hA) x y a ha hne g
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  exact hg

/-- Every recovered cross-entry is a genuinely nonthin original atom. -/
theorem recovered_recorded_nonthin (x y : Z) (a : S.Atom () ())
    (ha : E.rel (.fine a) (![x,y])) (hne : E.closureAtSet x ≠ E.closureAtSet y)
    (g h : ResidualData.PacketGroup S H) (c : S.Atom () ())
    (hc : E.rel (.fine c) (![PacketRecovery.move tag (finiteSourceData S H R B hB A hA) E hLocal g x,
      PacketRecovery.move tag (finiteSourceData S H R B hB A hA) E hLocal h y])) :
    ∀ u v : M, col S u v = some c → ¬finitePacket S H u v := by
  let D := finiteSourceData S H R B hB A hA
  let e := PacketRecovery.pairEmbedding tag D E hLocal x y a ha
  let p := PacketRecovery.leftPoint E x y
  let q := PacketRecovery.rightPoint E x y
  have hbase := recovered_pair_source_nonthin S H R B hB tag A hA E hLocal x y a ha hne
  have hcol := (PacketRecovery.recorded_matrix_reflection tag D E hLocal x y a ha g h c).mp hc
  change col S (g.val (e p).val.down.val) (h.val (e q).val.down.val) = some c at hcol
  have hnp : ¬finitePacket S H (g.val (e p).val.down.val) (h.val (e q).val.down.val) := by
    intro hF
    exact hbase ((finitePacket S H).val.trans
      (translation_in_packet S (finitePacket S H) G g (e p).val.down.val)
      ((finitePacket S H).val.trans hF ((finitePacket S H).val.symm
        (translation_in_packet S (finitePacket S H) G h (e q).val.down.val))))
  intro u v huv hF
  exact hnp (((finitePacket S H).property _ _ _ _ (hcol.trans huv.symm)).mpr hF)

end
end CCO.HKNReservoir
