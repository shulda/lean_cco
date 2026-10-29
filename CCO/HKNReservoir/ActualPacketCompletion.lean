import CCO.HKNReservoir.SourcePacketOrigins
import CCO.HKNReservoir.PacketCompletion

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
set_option quotPrecheck false
local notation "tag" => sourceTag S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "act" => sourceAction S H R B Δ
local notation "N" => sourceStructure S H R B hB
local notation "move" => PacketRecovery.move tag D₀ E hLocal
local notation "own" => PacketRecovery.owner tag D₀ E hLocal

/-- An actual normalized source homomorphism reads literal owners, ALL
named functions and EVERY recorded fine edge from unrestricted output. -/
theorem source_hom_readout (q : Structure.Homomorphism act E N) (hq : q.lang = 1) :
    (∀ x, ownerLabel S H R B (q x).down = own x) ∧
    (∀ g x, (q (move g x)).down = packetPoint S H R B hB g (q x).down) ∧
    ∀ x y a, E.rel (.fine a) (![x,y]) → col S (q x).down.val (q y).down.val = some a := by
  refine ⟨?_,?_,?_⟩
  · intro x
    have hh := q.map_rel (.owner (own x)) (fun _ => x)
      ((PacketRecovery.owner_iff tag D₀ E hLocal x _).mpr rfl)
    change (sourceData S H R B hB).owner (q x) = tag q.lang (own x) at hh
    change (sourceData S H R B hB).owner (q x) = own x
    simpa only [hq,map_one,Equiv.Perm.one_apply] using hh
  · intro g x
    have hh := q.map_func (.translate g) (fun _ => x)
      ⟨move g x,PacketRecovery.move_mem tag D₀ E hLocal g x,rfl⟩
    change q (move g x) = ULift.up (packetPoint S H R B hB g (q x).down) at hh
    exact congrArg ULift.down hh
  · intro x y a ha
    exact q.map_rel (.fine a) (![x,y]) ha

/-- Actual protected collision repair, on the SAME unrestricted carrier.
All raw records survive, including chords and their full packet matrices. -/
theorem actual_protected_packet_completion [Finite Z]
    (q : Structure.Homomorphism act E N) (hq : q.lang = 1)
    (P : Finset (PacketRecovery.PacketIndex E))
    (hinj : Set.InjOn (fun x => (q x).down) {x | PacketRecovery.packet E x ∈ P}) :
    ∃ q' : Z → NamedCarrier S H R B, Function.Injective q' ∧
      (∀ g x, q' (move g x) = packetPoint S H R B hB g (q' x)) ∧
      (∀ x, PacketRecovery.packet E x ∈ P → q' x = (q x).down) ∧
      (∀ x, ownerLabel S H R B (q' x) = own x) ∧
      ∀ x y a, E.rel (.fine a) (![x,y]) → col S (q' x).val (q' y).val = some a := by
  classical
  let hD := finiteSource_regularData S H R B hB A hA
  let hFine := finiteSource_fineData S H R B hB A hA
  letI := PacketRecovery.action tag D₀ E hLocal hD
  letI : Fintype (PacketRecovery.PacketIndex E) := Fintype.ofFinite _
  let packets := PacketRecovery.packets tag D₀ E hLocal hD
  let origins := sourceOriginPattern S H R B hB Δ A hA E hLocal
  let old : Z → NamedCarrier S H R B := fun x => (q x).down
  obtain ⟨hown,hmove,hfine⟩ := source_hom_readout S H R B hB Δ A hA E hLocal q hq
  have ho (i) : owner S H R (old (packets.origin i)).val = origins.owner i :=
    congrArg Subtype.val (hown (packets.origin i))
  have hr (i j a) (ha : origins.edge i j = some a) :
      col S (old (packets.origin i)).val (old (packets.origin j)).val = some a :=
    hfine _ _ a ((sourceOriginPattern_edge S H R B hB Δ A hA E hLocal i j a).mp ha)
  obtain ⟨q',hqi,hqm,hfix,hqo,hint,hcross⟩ := protected_packet_completion S H R B hB packets origins old
    hmove ho hr P hinj
  refine ⟨q',hqi,hqm,hfix,?_,?_⟩
  · intro x
    exact Subtype.ext ((hqo x).trans (congrArg Subtype.val (hown x)))
  · intro x y a ha
    let i := (packets.coordinates x).1
    let j := (packets.coordinates y).1
    let g := (packets.coordinates x).2
    let h := (packets.coordinates y).2
    have hx : g • packets.origin i = x := packets.coordinates.symm_apply_apply x
    have hy : h • packets.origin j = y := packets.coordinates.symm_apply_apply y
    have hcol : col S (q' x).val (q' y).val = col S (old x).val (old y).val := by
      by_cases hij : i = j
      · have hc := hint i g h
        have hy' : h • packets.origin i = y := hij.symm ▸ hy
        exact (congrArg₂ (fun u v => col S (q' u).val (q' v).val) hx hy').symm.trans
          (hc.trans (congrArg₂ (fun u v => col S (old u).val (old v).val) hx hy'))
      · have hp : PacketRecovery.packet E x ≠ PacketRecovery.packet E y := by
          intro he
          exact hij ((packets.coordinates_fst x).trans (he.trans (packets.coordinates_fst y).symm))
        obtain ⟨c,hc⟩ := PacketRecovery.origin_record_of_record tag D₀ E hLocal hD hFine x y a ha hp
        have hc' : origins.edge i j = some c := by
          change PacketRecovery.originEdge tag D₀ E hLocal hD i j = some c
          have hi : i = PacketRecovery.packet E x := packets.coordinates_fst x
          have hj : j = PacketRecovery.packet E y := packets.coordinates_fst y
          rw [hi,hj]
          exact hc
        have hm := hcross i j c hc' g h
        exact (congrArg₂ (fun u v => col S (q' u).val (q' v).val) hx hy).symm.trans
          (hm.trans (congrArg₂ (fun u v => col S (old u).val (old v).val) hx hy))
    exact hcol.trans (hfine x y a ha)

end
end CCO.HKNReservoir
