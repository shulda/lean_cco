import CCO.RelativeMI.ParametricReadings

/-! ONE decoder is fixed before any structural map or correction matrix.
Its origin readings use ALL independent rectangular parameters. -/
universe v w t y
namespace CCO.RelativeMI
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
open SafeReadings Selectors FullRows
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
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "J" => Packet I K
local notation "U₀" => TransversalSource.source S H R B
local notation "D" => rowDiagram S H R B hB Δ A hA E hLocal

def originAtom (p : DistinctPair J) : (U₀).Atom ((D).vertexSort p.src) ((D).vertexSort p.dst) := by
  letI := TransversalPure.thinCommGroup S H R
  exact parametricReading S H R B hB Δ readingData hΔ (parameter (p.src,1) (p.dst,1))
    (rowFixedMenu S H R B hB Δ A hA E hLocal p) (rowFixed_exact S H R B hB Δ A hA E hLocal c p)

theorem originAtom_converse (p q : J) (hpq : p ≠ q) :
    originAtom S H R B hB Δ readingData hΔ A hA E hLocal c ⟨q,p,hpq.symm⟩ =
      (U₀).conv (originAtom S H R B hB Δ readingData hΔ A hA E hLocal c ⟨p,q,hpq⟩) := by
  letI := TransversalPure.thinCommGroup S H R
  have hm := StrongPC.fixedNetwork_converse D ⟨p,q,hpq⟩
  have hu := parameter_symm ((p,1) : J × K) (q,1)
  have he := parametricReading_converse S H R B hB Δ readingData hΔ
    (parameter (p,1) (q,1)) (StrongPC.fixedNetwork D ⟨p,q,hpq⟩)
    (rowFixed_exact S H R B hB Δ A hA E hLocal c ⟨p,q,hpq⟩)
    (by rw [←hm]; exact rowFixed_exact S H R B hB Δ A hA E hLocal c ⟨q,p,hpq.symm⟩)
  simpa only [originAtom,rowFixedMenu,hu,hm] using he

/-- Complete typed diagram of the decoded actual packet origins. -/
def decodedOrigins : PartialDiagram U₀ J where
  finite_type := (D).finite_type
  vertexSort := (D).vertexSort
  edge p q h := some (originAtom S H R B hB Δ readingData hΔ A hA E hLocal c ⟨p,q,h⟩)
  edge_reverse := by
    intro p q hpq a
    constructor
    · intro ha
      have he := Option.some.inj ha
      rw [←he]
      exact congrArg some (originAtom_converse S H R B hB Δ readingData hΔ A hA E hLocal c p q hpq)
    · intro ha
      have he := Option.some.inj ha
      have hc := originAtom_converse S H R B hB Δ readingData hΔ A hA E hLocal c p q hpq
      have hh := congrArg (U₀).conv (hc.symm.trans he)
      simpa only [(U₀).conv_invol] using congrArg some hh

theorem originAtom_triangle (p q r : J) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    (U₀).Triangle (originAtom S H R B hB Δ readingData hΔ A hA E hLocal c ⟨p,q,hpq⟩)
      (originAtom S H R B hB Δ readingData hΔ A hA E hLocal c ⟨q,r,hqr⟩)
      (originAtom S H R B hB Δ readingData hΔ A hA E hLocal c ⟨p,r,hpr⟩) := by
  letI := TransversalPure.thinCommGroup S H R
  exact parametricReading_triangle S H R B hB Δ readingData hΔ _ _ _ _ _ _
    (rowFixed_exact S H R B hB Δ A hA E hLocal c ⟨p,q,hpq⟩)
    (rowFixed_exact S H R B hB Δ A hA E hLocal c ⟨q,r,hqr⟩)
    (rowFixed_exact S H R B hB Δ A hA E hLocal c ⟨p,r,hpr⟩)
    (StrongPC.fixedNetwork_PC D hpq hqr hpr)

/-- C21/C23: actual triangle-defined U age realizes ONE complete decoded
origin table, independently of all later correction matrices. -/
theorem decodedOrigins_strongCompletion :
    (decodedOrigins S H R B hB Δ readingData hΔ A hA E hLocal c).HasStrongCompletion := by
  apply TransversalSource.triangle_completion S H R B
  · intro p q hpq
    exact ⟨_,rfl⟩
  · intro p q r hpq hqr hpr a b d ha hb hd
    cases Option.some.inj ha
    cases Option.some.inj hb
    cases Option.some.inj hd
    exact originAtom_triangle S H R B hB Δ readingData hΔ A hA E hLocal c p q r hpq hqr hpr
end
end CCO.RelativeMI
