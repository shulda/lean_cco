import CCO.RelativeMI.RecordedPackets
import CCO.RelativeMI.SafeRows
import CCO.RelativeMI.DecodedStructure

/-! Unsafe sets meet at most one row per structural index. Their ENTIRE
touched structural packet union is closed and irreducible, so one faithful
structural map and ONE legal full-row correction send the set into A.
No chosen completion is assumed invariant under that structural map. -/
universe v w t y
namespace CCO.RelativeMI
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings Selectors FullRows
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (readingData : JointReading S H R B hB Δ)
variable (hΔ : ∀ g, TransversalPure.diagonal S H R B hB g ∈ Δ)
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
variable (c : PacketCertificate S H R B hB Δ A hA E hLocal)
variable (safe : Set (S.Atom () ()))
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "V" => Vertex I K
local notation "T" => TransversalSource.source S H R B
local notation "SG" => orbitSafe S H R B hB safe
local notation "P₀" => sourceOriginPattern S H R B hB Δ A hA E hLocal
local notation "act" => sourceAction S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "W₀" => encode (decodedData S H R B hB Δ readingData hΔ A hA E hLocal c)
local notation "coords" => reservoirCoordinates S H R B hB Δ A hA E hLocal

def DecodedUnsafe (X : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
    ¬ ∃ a ∈ safe, decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y = some a

def touchedIndices (X : Set V) : Set I := {i | ∃ x ∈ X, x.1.1 = i}

theorem unsafe_one_row_per_index (hs : SafeSystem T SG)
    (hq : readingData.SafeOn S H R B hB Δ SG) (X : Set V)
    (hX : DecodedUnsafe S H R B hB Δ readingData hΔ A hA E hLocal c safe X)
    (x : V) (hx : x ∈ X) (y : V) (hy : y ∈ X) (hindex : x.1.1 = y.1.1) :
    x.1 = y.1 := by
  by_contra hp
  have hne : x ≠ y := fun he => hp (congrArg Prod.fst he)
  have hh : (P₀).edge x.1.1 y.1.1 = none := by rw [hindex]; exact (P₀).diagonal _
  exact hX x hx y hy hne (decodedColour_hole_safe S H R B hB Δ readingData hΔ A hA E hLocal c safe hs hq x y hp hh)

theorem unsafe_indices_recorded (hs : SafeSystem T SG)
    (hq : readingData.SafeOn S H R B hB Δ SG) (X : Set V)
    (hX : DecodedUnsafe S H R B hB Δ readingData hΔ A hA E hLocal c safe X) :
    ∀ i ∈ touchedIndices S H R B E X, ∀ j ∈ touchedIndices S H R B E X,
      i ≠ j → ∃ a, (P₀).edge i j = some a := by
  rintro i ⟨x,hx,rfl⟩ j ⟨y,hy,rfl⟩ hij
  cases he : (P₀).edge x.1.1 y.1.1 with
  | some a => exact ⟨a,rfl⟩
  | none =>
    have hp : x.1 ≠ y.1 := fun h => hij (congrArg Prod.fst h)
    have hne : x ≠ y := fun h => hp (congrArg Prod.fst h)
    exact False.elim (hX x hx y hy hne
      (decodedColour_hole_safe S H R B hB Δ readingData hΔ A hA E hLocal c safe hs hq x y hp he))

theorem faithful_recorded_clique
    (j : Structure.Embedding act (encode D₀) E)
    (faithful : Structure.IsIrreducibleStructureFaithful act j)
    (J : Set I) (hJ : ∀ i ∈ J, ∀ k ∈ J, i ≠ k → ∃ a, (P₀).edge i k = some a) :
    ∃ s : Structure.Automorphism act E,
      ∀ x : Z, PacketRecovery.packet E x ∈ J → ∃ a : A, s x = j a := by
  exact faithful (recordedPacketSet S H R B E J)
    (recordedPacketSet_closed S H R B hB Δ A hA E hLocal J)
    (recordedPacketSet_irreducible S H R B hB Δ A hA E hLocal J hJ)

def selectedRows (X : Set V) (i : I) : Row I K := by
  classical
  exact if h : ∃ x ∈ X, x.1.1 = i then h.choose.1.2 else 1

theorem selectedRows_eq (hs : SafeSystem T SG)
    (hq : readingData.SafeOn S H R B hB Δ SG) (X : Set V)
    (hX : DecodedUnsafe S H R B hB Δ readingData hΔ A hA E hLocal c safe X)
    (x : V) (hx : x ∈ X) : selectedRows S H R B E X x.1.1 = x.1.2 := by
  classical
  have h : ∃ y ∈ X, y.1.1 = x.1.1 := ⟨x,hx,rfl⟩
  rw [selectedRows,dif_pos h]
  exact congrArg Prod.snd (unsafe_one_row_per_index S H R B hB Δ readingData hΔ A hA E hLocal c safe
    hs hq X hX h.choose h.choose_spec.1 x hx h.choose_spec.2)

/-- C21–C22: the structural motion is used only on the partial reservoir.
Its legal correction is an actual automorphism of THIS fixed decoder. -/
theorem unsafe_into_zero_source (hs : SafeSystem T SG)
    (hq : readingData.SafeOn S H R B hB Δ SG)
    (j : Structure.Embedding act (encode D₀) E)
    (faithful : Structure.IsIrreducibleStructureFaithful act j)
    (X : Set V) (hX : DecodedUnsafe S H R B hB Δ readingData hΔ A hA E hLocal c safe X) :
    ∃ g : Structure.Automorphism act W₀,
      ∀ x ∈ X, ∃ a : A, g x = zeroRowEmbed S H R B hB Δ A hA E hLocal j a := by
  classical
  letI := TransversalPure.thinCommGroup S H R
  let J := touchedIndices S H R B E X
  have hJ := unsafe_indices_recorded S H R B hB Δ readingData hΔ A hA E hLocal c safe hs hq X hX
  obtain ⟨s₀,hs₀⟩ := faithful_recorded_clique S H R B hB Δ A hA E hLocal j faithful J hJ
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  obtain ⟨C,hC,hzero,_⟩ := recorded_clique_zeroing
    (fun g => translation_square S (finitePacket S H) H (R.packet_thin S H) g)
    s (recordedPairs S H R B hB Δ A hA E hLocal)
    (recordedPairs_symmetric S H R B hB Δ A hA E hLocal) J hJ (selectedRows S H R B E X)
  refine ⟨decodedLiftAut S H R B hB Δ readingData hΔ A hA E hLocal c s₀ C hC,?_⟩
  intro x hx
  have hxi : x.1.1 ∈ J := ⟨x,hx,rfl⟩
  have hz := hzero x.1.1 hxi
  rw [selectedRows_eq S H R B hB Δ readingData hΔ A hA E hLocal c safe hs hq X hX x hx] at hz
  let z := (coords).symm (projection x)
  have hzi : PacketRecovery.packet E z = x.1.1 := by
    rw [← reservoirCoordinates_fst S H R B hB Δ A hA E hLocal z]
    exact congrArg Prod.fst ((coords).apply_symm_apply (projection x))
  obtain ⟨a,ha⟩ := hs₀ z (hzi.symm ▸ hxi)
  refine ⟨a,?_⟩
  have he := rowStructural_coordinates S H R B hB Δ A hA E hLocal s₀ (projection x)
  change coords (s₀ z) = baseMap s (projection x) at he
  rw [ha] at he
  change ((s.sigma x.1.1,rowImage s C x.1.1 x.1.2),x.2*s.offset x.1.1) = _
  rw [hz]
  exact congrArg (fun p : I × K => ((p.1,(1 : Row I K)),p.2)) he.symm

end
end CCO.RelativeMI
