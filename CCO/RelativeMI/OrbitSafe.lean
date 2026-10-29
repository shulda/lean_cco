import CCO.SafeReadings.TransversalConsumer
import CCO.OwnerTransversal.PacketAction

/-! Orbit safety is a condition on ALL literal thin translates of the
original fine atom. Original safety is not assumed translation invariant. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (U : Finset (Owner S H R)) (hU : PacketInvariant S H R U)
variable (safe : Set (S.Atom () ()))
local notation "K" => ResidualData.PacketGroup S H
local notation "T" => TransversalSource.source S H R U

/-- The given original palette is tested after EVERY actual thin switch. -/
def orbitSafe (i j : ↥U) : Set (TransversalSource.Palette S H R U i j) :=
  {a | ∀ g : K, (TransversalGauge.leftEquiv S H R U hU g i j a).val ∈ safe}

/-- Orbit safety depends on the literal original name, while types may
move independently and owner actions may have stabilizers. -/
theorem orbitSafe_raw_congr {i j k l : ↥U} (a : TransversalSource.Palette S H R U i j) (b : TransversalSource.Palette S H R U k l)
    (hab : a.val = b.val) :
    a ∈ orbitSafe S H R U hU safe i j ↔ b ∈ orbitSafe S H R U hU safe k l := by
  have he (g : K) : (TransversalGauge.leftEquiv S H R U hU g i j a).val =
      (TransversalGauge.leftEquiv S H R U hU g k l b).val := by
    apply Option.some.inj
    rw [TransversalGauge.leftEquiv_label,TransversalGauge.leftEquiv_label,hab]
  constructor
  · intro ha g
    rw [← he g]
    exact ha g
  · intro hb g
    rw [he g]
    exact hb g

theorem orbitSafe_subset {i j : ↥U} {a : TransversalSource.Palette S H R U i j}
    (ha : a ∈ orbitSafe S H R U hU safe i j) : a.val ∈ safe := by
  have he : (TransversalGauge.leftEquiv S H R U hU 1 i j a).val = a.val := by
    apply Option.some.inj
    rw [TransversalGauge.leftEquiv_label,switchColour_one]
  rw [← he]
  exact ha 1

theorem orbitSafe_matrix_iff {i j : ↥U} (a : TransversalSource.Palette S H R U i j) :
    a ∈ orbitSafe S H R U hU safe i j ↔
      ∀ g h : K, ∃ c ∈ safe,
        switchColour S (finitePacket S H) (g*h) (some a.val) = some c := by
  constructor
  · intro ha g h
    exact ⟨_,ha (g*h),(TransversalGauge.leftEquiv_label S H R U hU (g*h) a).symm⟩
  · intro ha g
    obtain ⟨c,hc,hcol⟩ := ha g 1
    have he : (TransversalGauge.leftEquiv S H R U hU g i j a).val = c := by
      apply Option.some.inj
      rw [TransversalGauge.leftEquiv_label]
      simpa only [mul_one] using hcol
    rw [he]
    exact hc

private theorem left_left_val (g h : K) {i j : ↥U} (a : TransversalSource.Palette S H R U i j) :
    (TransversalGauge.leftEquiv S H R U hU g _ _
      (TransversalGauge.leftEquiv S H R U hU h i j a)).val =
    (TransversalGauge.leftEquiv S H R U hU (g*h) i j a).val := by
  apply Option.some.inj
  rw [TransversalGauge.leftEquiv_label,TransversalGauge.leftEquiv_label,
    TransversalGauge.leftEquiv_label,switchColour_mul S (finitePacket S H) H]

private theorem left_right_val (g h : K) {i j : ↥U} (a : TransversalSource.Palette S H R U i j) :
    (TransversalGauge.leftEquiv S H R U hU g _ _
      (TransversalGauge.rightEquiv S H R U hU h i j a)).val =
    (TransversalGauge.leftEquiv S H R U hU (g*h) i j a).val := by
  apply Option.some.inj
  rw [TransversalGauge.leftEquiv_label,TransversalGauge.rightEquiv_label,
    TransversalGauge.leftEquiv_label,switchColour_mul S (finitePacket S H) H]

theorem orbitSafe_left_iff (g : K) {i j : ↥U} (a : TransversalSource.Palette S H R U i j) :
    TransversalGauge.leftEquiv S H R U hU g i j a ∈
      orbitSafe S H R U hU safe (TransversalGauge.moveOwner S H R U hU g i) j ↔
    a ∈ orbitSafe S H R U hU safe i j := by
  constructor
  · intro ha h
    have hh := ha (h*g⁻¹)
    rw [left_left_val, mul_assoc,inv_mul_cancel,mul_one] at hh
    exact hh
  · intro ha h
    rw [left_left_val]
    exact ha (h*g)

theorem orbitSafe_right_iff (g : K) {i j : ↥U} (a : TransversalSource.Palette S H R U i j) :
    TransversalGauge.rightEquiv S H R U hU g i j a ∈
      orbitSafe S H R U hU safe i (TransversalGauge.moveOwner S H R U hU g j) ↔
    a ∈ orbitSafe S H R U hU safe i j := by
  constructor
  · intro ha h
    have hh := ha (h*g⁻¹)
    rw [left_right_val, mul_assoc,inv_mul_cancel,mul_one] at hh
    exact hh
  · intro ha h
    rw [left_right_val]
    exact ha (h*g)

theorem orbitSafe_left_image (g : K) (i j : ↥U) :
    TransversalGauge.leftEquiv S H R U hU g i j '' orbitSafe S H R U hU safe i j =
      orbitSafe S H R U hU safe (TransversalGauge.moveOwner S H R U hU g i) j := by
  ext b
  obtain ⟨a,rfl⟩ := (TransversalGauge.leftEquiv S H R U hU g i j).surjective b
  rw [(TransversalGauge.leftEquiv S H R U hU g i j).injective.mem_set_image]
  exact (orbitSafe_left_iff S H R U hU safe g a).symm

theorem orbitSafe_right_image (g : K) (i j : ↥U) :
    TransversalGauge.rightEquiv S H R U hU g i j '' orbitSafe S H R U hU safe i j =
      orbitSafe S H R U hU safe i (TransversalGauge.moveOwner S H R U hU g j) := by
  ext b
  obtain ⟨a,rfl⟩ := (TransversalGauge.rightEquiv S H R U hU g i j).surjective b
  rw [(TransversalGauge.rightEquiv S H R U hU g i j).injective.mem_set_image]
  exact (orbitSafe_right_iff S H R U hU safe g a).symm

theorem orbitSafe_opposite (i j : ↥U) :
    (T).opposite (orbitSafe S H R U hU safe i j) = orbitSafe S H R U hU safe j i := by
  ext a
  exact orbitSafe_raw_congr S H R U hU safe ((T).conv a) a rfl

theorem orbitSafe_invariant (Δ : Subgroup (TransversalPure.Gamma S H R U)) :
    SafeInvariant T (orbitSafe S H R U hU safe) (TransversalPure.subgroupAction S H R U hU Δ) := by
  intro γ i j
  let P := TransversalPure.subgroupRelabelling S H R U hU Δ
  change (⟨P.owner γ i,P.owner γ j,P.atomEquiv γ i j '' orbitSafe S H R U hU safe i j⟩ :
      Selectors.TaggedMenu T) = ⟨_,_,_⟩
  apply congrArg (fun A => (⟨P.owner γ i,P.owner γ j,A⟩ : Selectors.TaggedMenu T))
  ext b
  obtain ⟨a,rfl⟩ := (P.atomEquiv γ i j).surjective b
  have hRaw : a.val = (P.atomEquiv γ i j a).val :=
    Option.some.inj (P.atomMove_label γ a).symm
  exact (P.atomEquiv γ i j).injective.mem_set_image.trans
    (orbitSafe_raw_congr S H R U hU safe a (P.atomEquiv γ i j a) hRaw)

end
end CCO.RelativeMI
