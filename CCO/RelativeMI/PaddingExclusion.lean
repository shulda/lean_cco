import CCO.RelativeMI.FaithfulTransport
import CCO.RelativeMI.OwnerLanguage

/-! The whole unsafe clique first enters the padded source. If it meets
two packets, literal fine-colour preservation excludes EVERY padding point.
The transporter has no separately prescribed owner component. -/
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
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "V" => Vertex I K
local notation "T" => TransversalSource.source S H R B
local notation "act" => sourceAction S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "W₀" => encode (decodedData S H R B hB Δ readingData hΔ A hA E hLocal c)

theorem decodedAut_colour (g : Structure.Automorphism act W₀) (x y : V) :
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c (g x) (g y) =
      decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y :=
  (decodedAutPair S H R B hB Δ readingData hΔ A hA E hLocal c g).property.2 x y

theorem decodedAut_move (g : Structure.Automorphism act W₀) (k : K) (x : V) :
    letI := TransversalPure.thinCommGroup S H R
    g (translate k x) = translate k (g x) := by
  letI := TransversalPure.thinCommGroup S H R
  exact (exactMapOfEmbedding (sourceTag S H R B Δ)
    (automorphismEmbedding (sourceTag S H R B Δ) g)).move k x

theorem decodedAut_packet_iff (g : Structure.Automorphism act W₀) (x y : V) :
    (g x).1 = (g y).1 ↔ x.1 = y.1 := by
  letI := TransversalPure.thinCommGroup S H R
  constructor
  · intro hp
    let k : K := (g y).2 * ((g x).2)⁻¹
    have ht : translate k (g x) = g y := by
      change ((g x).1,k*(g x).2) = g y
      apply Prod.ext
      · exact hp
      · change ((g y).2 * ((g x).2)⁻¹) * (g x).2 = (g y).2
        simp only [mul_assoc,inv_mul_cancel,mul_one]
    have he := (automorphismPerm (sourceTag S H R B Δ) g).injective
      ((decodedAut_move S H R B hB Δ readingData hΔ A hA E hLocal c g k x).trans ht)
    simpa only [translate] using congrArg (fun p : V => p.1) he
  · intro hp
    let k : K := y.2*x.2⁻¹
    have ht : translate k x = y := by
      change (x.1,k*x.2) = y
      apply Prod.ext
      · exact hp
      · change (y.2*x.2⁻¹)*x.2 = y.2
        simp only [mul_assoc,inv_mul_cancel,mul_one]
    have he := (decodedAut_move S H R B hB Δ readingData hΔ A hA E hLocal c g k x).symm.trans
      (congrArg g ht)
    simpa only [translate] using congrArg (fun p : V => p.1) he

theorem zeroRow_packet_of_finitePacket
    (j : Structure.Embedding act (encode D₀) E) (a b : A)
    (hab : finitePacket S H a.val.down.val b.val.down.val) :
    (zeroRowEmbed S H R B hB Δ A hA E hLocal j a).1 =
      (zeroRowEmbed S H R B hB Δ A hA E hLocal j b).1 := by
  letI := TransversalPure.thinCommGroup S H R
  obtain ⟨k,hk,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
    a.val.down.val b.val.down.val hab
  have he : (D₀).move k a = b := by
    apply Subtype.ext
    apply ULift.ext
    exact Subtype.ext hk
  have hh := zeroRowEmbed_move S H R B hB Δ A hA E hLocal j k a
  rw [he] at hh
  exact (congrArg Prod.fst hh).symm

/-- C23: padding-to-old AND padding-to-padding cross matrices are safe.
No claim is made that unrelated old zero rows remain fixed. -/
theorem unsafe_into_original_seed (safe : Set (S.Atom () ()))
    (hs : SafeSystem T (orbitSafe S H R B hB safe))
    (hq : readingData.SafeOn S H R B hB Δ (orbitSafe S H R B hB safe))
    (j : Structure.Embedding act (encode D₀) E)
    (faithful : Structure.IsIrreducibleStructureFaithful act j)
    (Old : Set A)
    (padding : ∀ a : A, a ∉ Old → ∀ b : A,
      ¬ finitePacket S H a.val.down.val b.val.down.val →
        ∃ d ∈ safe, col S a.val.down.val b.val.down.val = some d)
    (X : Set V) (hX : DecodedUnsafe S H R B hB Δ readingData hΔ A hA E hLocal c safe X)
    (multi : ∃ x ∈ X, ∃ y ∈ X, x.1 ≠ y.1) :
    ∃ g : Structure.Automorphism act W₀,
      ∀ x ∈ X, ∃ a : A, a ∈ Old ∧ g x = zeroRowEmbed S H R B hB Δ A hA E hLocal j a := by
  obtain ⟨g,hg⟩ := unsafe_into_zero_source S H R B hB Δ readingData hΔ A hA E hLocal c safe hs hq j faithful X hX
  refine ⟨g,?_⟩
  intro x hx
  obtain ⟨a,ha⟩ := hg x hx
  refine ⟨a,?_,ha⟩
  by_contra hold
  have other : ∃ y ∈ X, x.1 ≠ y.1 := by
    obtain ⟨u,hu,v,hv,huv⟩ := multi
    by_cases hxu : x.1 = u.1
    · exact ⟨v,hv,fun he => huv (hxu.symm.trans he)⟩
    · exact ⟨u,hu,hxu⟩
  obtain ⟨y,hy,hxy⟩ := other
  obtain ⟨b,hb⟩ := hg y hy
  have hab : ¬ finitePacket S H a.val.down.val b.val.down.val := by
    intro hF
    apply hxy
    apply (decodedAut_packet_iff S H R B hB Δ readingData hΔ A hA E hLocal c g x y).mp
    rw [ha,hb]
    exact zeroRow_packet_of_finitePacket S H R B hB Δ A hA E hLocal j a b hF
  obtain ⟨d,hd,hcol⟩ := padding a hold b hab
  have hc : decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c (g x) (g y) = some d := by
    rw [ha,hb]
    exact zeroRow_decoded_fine S H R B hB Δ readingData hΔ A hA E hLocal c j a b d hcol
  exact hX x hx y hy (fun he => hxy (congrArg Prod.fst he))
    ⟨d,hd,(decodedAut_colour S H R B hB Δ readingData hΔ A hA E hLocal c g x y).symm.trans hc⟩

end
end CCO.RelativeMI
