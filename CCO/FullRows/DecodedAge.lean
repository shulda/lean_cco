import CCO.FullRows.FixedDecoder
import CCO.OwnerTransversal.Inflation

/-! The fixed decoded colouring has an ACTUAL injective realization.
A choice of its age certificate does not enter the definition of colours. -/
universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
open SafeReadings Selectors
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (hΔ : ∀ g, TransversalPure.diagonal S H R B hB g ∈ Δ)
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
variable (c : PacketCertificate S H R B hB Δ A hA E hLocal)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "J" => Packet I K
local notation "U₀" => TransversalSource.source S H R B
local notation "D" => decodedOrigins S H R B hB Δ hΔ A hA E hLocal c

/-- The literal full fine matrix forced by the fixed origin decoder. -/
def decodedColour (x y : Vertex I K) : FullColour S := by
  classical
  exact if h : x.1 = y.1 then switchColour S (finitePacket S H) (x.2*y.2) none else
    switchColour S (finitePacket S H) (x.2*y.2)
      (some (originAtom S H R B hB Δ hΔ A hA E hLocal c ⟨x.1,y.1,h⟩).val)

theorem decodedColour_internal (x y : Vertex I K) (hxy : x.1 = y.1) :
    decodedColour S H R B hB Δ hΔ A hA E hLocal c x y =
      switchColour S (finitePacket S H) (x.2*y.2) none := by
  classical
  exact dif_pos hxy

def decodedOriginHom : DiagramHom D :=
  (decodedOrigins_strongCompletion S H R B hB Δ hΔ A hA E hLocal c).choose

theorem decodedOriginHom_injective : (decodedOriginHom S H R B hB Δ hΔ A hA E hLocal c).IsInjective :=
  (decodedOrigins_strongCompletion S H R B hB Δ hΔ A hA E hLocal c).choose_spec

def decodedU (p : J) : U S H R B := (decodedOriginHom S H R B hB Δ hΔ A hA E hLocal c).point p |>.val

theorem decodedU_injective : Function.Injective (decodedU S H R B hB Δ hΔ A hA E hLocal c) := by
  intro p q he
  apply decodedOriginHom_injective S H R B hB Δ hΔ A hA E hLocal c
  apply (TransversalSource.sigmaEquiv S H R B).injective
  exact he

def decoderRecovery : Inflation.Carrier S H R B ≃ NamedCarrier S H R B :=
  (Inflation.recovery_readout S H R B hB).choose

def decodedPoint (x : Vertex I K) : NamedCarrier S H R B :=
  decoderRecovery S H R B hB (decodedU S H R B hB Δ hΔ A hA E hLocal c x.1,x.2)

theorem decodedPoint_injective : Function.Injective (decodedPoint S H R B hB Δ hΔ A hA E hLocal c) := by
  intro x y he
  have hh := (decoderRecovery S H R B hB).injective he
  have hi := congrArg (fun z : Inflation.Carrier S H R B => z.1) hh
  have hz := congrArg (fun z : Inflation.Carrier S H R B => z.2) hh
  exact Prod.ext (decodedU_injective S H R B hB Δ hΔ A hA E hLocal c hi) hz

theorem decodedPoint_owner (x : Vertex I K) :
    ownerLabel S H R B (decodedPoint S H R B hB Δ hΔ A hA E hLocal c x) =
      vertexOwner S H R B hB Δ A hA E hLocal x := by
  have hh := (Inflation.recovery_readout S H R B hB).choose_spec.1
    (decodedU S H R B hB Δ hΔ A hA E hLocal c x.1,x.2)
  exact hh.trans (congrArg (TransversalGauge.moveOwner S H R B hB x.2)
    (decodedOriginHom S H R B hB Δ hΔ A hA E hLocal c |>.point x.1 |>.property))

/-- C22/C23: inflation recovers every decoded internal/two-packet matrix,
so the WHOLE finite colouring, not just its origin table, is in Age(N). -/
theorem decodedPoint_colour (x y : Vertex I K) :
    col S (decodedPoint S H R B hB Δ hΔ A hA E hLocal c x).val
      (decodedPoint S H R B hB Δ hΔ A hA E hLocal c y).val =
    decodedColour S H R B hB Δ hΔ A hA E hLocal c x y := by
  classical
  have hh := (Inflation.recovery_readout S H R B hB).choose_spec.2.1
    (decodedU S H R B hB Δ hΔ A hA E hLocal c x.1,x.2)
    (decodedU S H R B hB Δ hΔ A hA E hLocal c y.1,y.2)
  apply hh.trans
  change switchColour S (finitePacket S H) (x.2*y.2) ((limitTable S H R B).colour _ _) = _
  by_cases hxy : x.1 = y.1
  · simp only [decodedColour,hxy,TransversalAge.colour_diag,dite_true]
  · have he := (decodedOriginHom S H R B hB Δ hΔ A hA E hLocal c).preserves_edge x.1 y.1 hxy
      (originAtom S H R B hB Δ hΔ A hA E hLocal c ⟨x.1,y.1,hxy⟩) rfl
    have hc := (TransversalSource.colour_some_iff S H R B _ _ _).mp he
    change (limitTable S H R B).colour
      (decodedU S H R B hB Δ hΔ A hA E hLocal c x.1)
      (decodedU S H R B hB Δ hΔ A hA E hLocal c y.1) = _ at hc
    rw [hc]
    exact if_neg hxy |>.symm

theorem decodedPoint_translate (g : K) (x : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    decodedPoint S H R B hB Δ hΔ A hA E hLocal c (translate g x) =
      packetPoint S H R B hB g (decodedPoint S H R B hB Δ hΔ A hA E hLocal c x) :=
  (Inflation.recovery_readout S H R B hB).choose_spec.2.2 g
    (decodedU S H R B hB Δ hΔ A hA E hLocal c x.1,x.2)
end
end CCO.FullRows
