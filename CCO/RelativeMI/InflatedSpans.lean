import CCO.SafeReadings.TransversalSAP
import CCO.OwnerTransversal.Inflation
import CCO.OwnerTransversal.ClosedAvoidance

/-! An arbitrary actual typed transversal span is first placed by SAP,
then inflated through ONE actual recovery. Both its complete fine matrices
and its exact common base survive on literal whole-packet finite sets. -/
universe v w t z
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "N" => NamedCarrier S H R B
local notation "T" => TransversalSource.source S H R B
local notation "V" => TransversalSource.Carrier S H R B
local notation "U₀" => TransversalAge.U S H R B
local notation "tbl" => TransversalAge.limitTable S H R B

/-- Actual SAP coordinates and ONE original-source inflation recovery.
Origin indices are full real packet labels, never owner labels. -/
structure InflatedSpan (C L P : FiniteInduced (X := V))
    (eCL : InducedEmbedding T C L) (eCP : InducedEmbedding T C P) where
  recovery : Inflation.Carrier S H R B ≃ N
  recovery_owner : ∀ x : Inflation.Carrier S H R B,
    ownerLabel S H R B (recovery x) = (Inflation.table S H R B hB).owner x
  recovery_colour : ∀ x y : Inflation.Carrier S H R B,
    col S (recovery x).val (recovery y).val = (Inflation.table S H R B hB).colour x y
  recovery_move : ∀ (g : K) (x : Inflation.Carrier S H R B), recovery ((Inflation.action S H R B).smul g x) =
    packetPoint S H R B hB g (recovery x)
  leftIndex : ↥L.vertices ↪ U₀
  rightIndex : ↥P.vertices ↪ U₀
  left_index_owner : ∀ x : ↥L.vertices, (tbl).owner (leftIndex x) = x.val.1
  right_index_owner : ∀ x : ↥P.vertices, (tbl).owner (rightIndex x) = x.val.1
  left_index_colour : ∀ x y : ↥L.vertices, (tbl).colour (leftIndex x) (leftIndex y) =
    (tbl).colour x.val.2.val y.val.2.val
  right_index_colour : ∀ x y : ↥P.vertices, (tbl).colour (rightIndex x) (rightIndex y) =
    (tbl).colour x.val.2.val y.val.2.val
  index_commutes : ∀ c : ↥C.vertices, leftIndex (eCL.toEmbedding c) = rightIndex (eCP.toEmbedding c)
  index_cross : ∀ (x : ↥L.vertices) (y : ↥P.vertices), leftIndex x = rightIndex y ↔
    ∃ c : ↥C.vertices, eCL.toEmbedding c = x ∧ eCP.toEmbedding c = y

/-- The actual transversal SAP and actual countable recovery discharge
every field. No original-age SAP or safe amalgamation is presumed here. -/
theorem inflatedSpan_exists (C L P : FiniteInduced (X := V))
    (eCL : InducedEmbedding T C L) (eCP : InducedEmbedding T C P) :
    Nonempty (InflatedSpan S H R B hB C L P eCL eCP) := by
  classical
  obtain ⟨D,l,r,hcomm,hcross⟩ := (TransversalSource.ageSAP S H R B).strong_amalgamate C L P eCL eCP
  obtain ⟨e,heo,hec,hem⟩ := Inflation.recovery_readout S H R B hB
  let li : ↥L.vertices ↪ U₀ := {
    toFun x := (l.toEmbedding x).val.2.val
    inj' := by
      intro x y he
      apply l.toEmbedding.injective
      apply Subtype.ext
      exact (TransversalSource.sigmaEquiv S H R B).injective he }
  let ri : ↥P.vertices ↪ U₀ := {
    toFun x := (r.toEmbedding x).val.2.val
    inj' := by
      intro x y he
      apply r.toEmbedding.injective
      apply Subtype.ext
      exact (TransversalSource.sigmaEquiv S H R B).injective he }
  refine ⟨⟨e,heo,hec,hem,li,ri,?_,?_,?_,?_,?_,?_⟩⟩
  · intro x
    exact (l.toEmbedding x).val.2.property.trans (l.preserves_sort x)
  · intro x
    exact (r.toEmbedding x).val.2.property.trans (r.preserves_sort x)
  · intro x y
    have hc := congrArg (TransversalSource.forgetColour S H R B) (l.preserves_colours x y)
    change (tbl).colour (l.toEmbedding x).val.2.val (l.toEmbedding y).val.2.val = _
    simpa only [TransversalSource.forget_tagged] using hc.symm
  · intro x y
    have hc := congrArg (TransversalSource.forgetColour S H R B) (r.preserves_colours x y)
    change (tbl).colour (r.toEmbedding x).val.2.val (r.toEmbedding y).val.2.val = _
    simpa only [TransversalSource.forget_tagged] using hc.symm
  · intro c
    exact congrArg (fun x : ↥D.vertices => x.val.2.val) (hcomm c)
  · intro x y
    constructor
    · intro he
      apply hcross
      apply Subtype.ext
      exact (TransversalSource.sigmaEquiv S H R B).injective he
    · rintro ⟨c,hc,hc'⟩
      rw [← hc,← hc']
      exact congrArg (fun x : ↥D.vertices => x.val.2.val) (hcomm c)

def inflatedSpan (C L P : FiniteInduced (X := V))
    (eCL : InducedEmbedding T C L) (eCP : InducedEmbedding T C P) :
    InflatedSpan S H R B hB C L P eCL eCP :=
  (inflatedSpan_exists S H R B hB C L P eCL eCP).some

namespace InflatedSpan
variable {S H R B hB}

def leftPoint {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (p : ↥L.vertices × K) : N := d.recovery (d.leftIndex p.1,p.2)
def rightPoint {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (p : ↥P.vertices × K) : N := d.recovery (d.rightIndex p.1,p.2)
def basePoint {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (p : ↥C.vertices × K) : N := d.leftPoint (eCL.toEmbedding p.1,p.2)
def leftOrigin {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥L.vertices) : N := d.leftPoint (x,1)
def rightOrigin {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥P.vertices) : N := d.rightPoint (x,1)

theorem leftPoint_move {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥L.vertices) (g h : K) :
    d.leftPoint (x,g*h) = packetPoint S H R B hB g (d.leftPoint (x,h)) :=
  d.recovery_move g (d.leftIndex x,h)

theorem rightPoint_move {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥P.vertices) (g h : K) :
    d.rightPoint (x,g*h) = packetPoint S H R B hB g (d.rightPoint (x,h)) :=
  d.recovery_move g (d.rightIndex x,h)

theorem basePoint_move {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥C.vertices) (g h : K) :
    d.basePoint (x,g*h) = packetPoint S H R B hB g (d.basePoint (x,h)) :=
  d.leftPoint_move (eCL.toEmbedding x) g h

theorem leftPoint_eq {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥L.vertices) (g : K) :
    d.leftPoint (x,g) = packetPoint S H R B hB g (d.leftOrigin x) := by
  simpa only [mul_one,leftOrigin] using d.leftPoint_move x g 1

theorem rightPoint_eq {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥P.vertices) (g : K) :
    d.rightPoint (x,g) = packetPoint S H R B hB g (d.rightOrigin x) := by
  simpa only [mul_one,rightOrigin] using d.rightPoint_move x g 1

theorem leftOrigin_owner {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥L.vertices) : ownerLabel S H R B (d.leftOrigin x) = x.val.1 :=
  (d.recovery_owner (d.leftIndex x,1)).trans
    ((Inflation.table_owner_one S H R B hB _).trans (d.left_index_owner x))

theorem rightOrigin_owner {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥P.vertices) : ownerLabel S H R B (d.rightOrigin x) = x.val.1 :=
  (d.recovery_owner (d.rightIndex x,1)).trans
    ((Inflation.table_owner_one S H R B hB _).trans (d.right_index_owner x))

theorem leftOrigin_colour {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x y : ↥L.vertices) :
    col S (d.leftOrigin x).val (d.leftOrigin y).val = (tbl).colour x.val.2.val y.val.2.val :=
  (d.recovery_colour (d.leftIndex x,1) (d.leftIndex y,1)).trans
    ((Inflation.table_colour_one S H R B hB _ _).trans (d.left_index_colour x y))

theorem rightOrigin_colour {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x y : ↥P.vertices) :
    col S (d.rightOrigin x).val (d.rightOrigin y).val = (tbl).colour x.val.2.val y.val.2.val :=
  (d.recovery_colour (d.rightIndex x,1) (d.rightIndex y,1)).trans
    ((Inflation.table_colour_one S H R B hB _ _).trans (d.right_index_colour x y))

theorem leftPoint_injective {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) : Function.Injective d.leftPoint := by
  intro x y he
  have hh := d.recovery.injective he
  apply Prod.ext
  · exact d.leftIndex.injective (congrArg (fun p : U₀ × K => p.1) hh)
  · exact congrArg (fun p : U₀ × K => p.2) hh

theorem rightPoint_injective {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) : Function.Injective d.rightPoint := by
  intro x y he
  have hh := d.recovery.injective he
  apply Prod.ext
  · exact d.rightIndex.injective (congrArg (fun p : U₀ × K => p.1) hh)
  · exact congrArg (fun p : U₀ × K => p.2) hh

/-- Real phase equality is separate from origin equality, even when the
owner action has stabilizers. This is the whole exact intersection law. -/
theorem point_cross {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (x : ↥L.vertices) (y : ↥P.vertices) (g h : K) :
    d.leftPoint (x,g) = d.rightPoint (y,h) ↔
      (∃ c : ↥C.vertices, eCL.toEmbedding c = x ∧ eCP.toEmbedding c = y) ∧ g = h := by
  constructor
  · intro he
    have hh := d.recovery.injective he
    exact ⟨(d.index_cross x y).mp (congrArg Prod.fst hh),congrArg Prod.snd hh⟩
  · rintro ⟨hc,hg⟩
    exact congrArg d.recovery (Prod.ext ((d.index_cross x y).mpr hc) hg)

theorem basePoint_right {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (c : ↥C.vertices) (g : K) :
    d.basePoint (c,g) = d.rightPoint (eCP.toEmbedding c,g) :=
  (d.point_cross _ _ g g).mpr ⟨⟨c,rfl,rfl⟩,rfl⟩

theorem origin_commutes {C L P : FiniteInduced (X := V)}
    {eCL : InducedEmbedding T C L} {eCP : InducedEmbedding T C P}
    (d : InflatedSpan S H R B hB C L P eCL eCP) (c : ↥C.vertices) :
    d.leftOrigin (eCL.toEmbedding c) = d.rightOrigin (eCP.toEmbedding c) := d.basePoint_right c 1

end InflatedSpan
end
end CCO.RelativeMI
