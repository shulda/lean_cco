import CCO.RelativeMI.SafePaddingNative
import CCO.RelativeMI.AnchoredSafe

/-! Literal safe padding is read through ONE actual inflation recovery.
The seed remains pointwise present and all newly added packet matrices,
including padding against padding, are original-safe. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (U : Finset (Owner S H R))
local notation "K" => ResidualData.PacketGroup S H
local notation "N" => NamedCarrier S H R U
local notation "V" => TransversalSource.Carrier S H R U
local notation "T" => TransversalSource.source S H R U
local notation "U₀" => TransversalAge.U S H R U

/-- A finite literal whole-packet extension, with safety for EVERY new
point against every point in a different real packet. -/
structure SafePadding (hU : PacketInvariant S H R U)
    (safe : Set (S.Atom () ())) (seed : Finset N) where
  carrier : Finset N
  closed : PacketClosed S H R U carrier
  contains : seed ⊆ carrier
  covers : ∀ s : ↥U, ∃ a ∈ carrier, ownerLabel S H R U a = s
  safe_cross : ∀ a ∈ carrier, a ∉ seed → ∀ b ∈ carrier,
    ¬ finitePacket S H a.val b.val → ∃ d ∈ safe, col S a.val b.val = some d

variable (hU : PacketInvariant S H R U)

private def inflateNative (e : Inflation.Carrier S H R U ≃ N)
    (A : Finset (Sigma V)) : Finset N := by
  classical
  letI : Finite K := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  exact ((A.finite_toSet.prod (Set.toFinite (Set.univ : Set K))).image
    (fun p : Sigma V × K => e (p.1.2.val,p.2))).toFinset

private theorem mem_inflateNative (e : Inflation.Carrier S H R U ≃ N)
    (A : Finset (Sigma V)) (a : N) :
    a ∈ inflateNative S H R U e A ↔
      ∃ p ∈ A, ∃ k : K, e (p.2.val,k) = a := by
  classical
  let : Finite K := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  change a ∈ ((A.finite_toSet.prod (Set.toFinite (Set.univ : Set K))).image
    (fun p : Sigma V × K => e (p.1.2.val,p.2))).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨p,k⟩,⟨hp,_⟩,he⟩
    exact ⟨p,hp,k,he⟩
  · rintro ⟨p,hp,k,he⟩
    exact ⟨(p,k),⟨hp,Set.mem_univ _⟩,he⟩

private theorem recovery_phase_in_packet (e : Inflation.Carrier S H R U ≃ N)
    (hm : ∀ (g : K) x, e ((Inflation.action S H R U).smul g x) =
      packetPoint S H R U hU g (e x))
    (u : U₀) (g h : K) : finitePacket S H (e (u,g)).val (e (u,h)).val := by
  have hh : e (u,h) = packetPoint S H R U hU (h*g⁻¹) (e (u,g)) := by
    have hm' := hm (h*g⁻¹) (u,g)
    change e (u,(h*g⁻¹)*g) = _ at hm'
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm'
  rw [hh]
  exact translation_in_packet S (finitePacket S H) G (h*g⁻¹) (e (u,g)).val

private theorem recovery_packet_fst (e : Inflation.Carrier S H R U ≃ N)
    (hm : ∀ (g : K) x, e ((Inflation.action S H R U).smul g x) =
      packetPoint S H R U hU g (e x))
    (u v : U₀) (g h : K)
    (hF : finitePacket S H (e (u,g)).val (e (v,h)).val) : u = v := by
  obtain ⟨k,hk,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
    (e (u,g)).val (e (v,h)).val hF
  have he : e (u,k*g) = e (v,h) := (hm k (u,g)).trans (Subtype.ext hk)
  exact congrArg Prod.fst (e.injective he)

private theorem inflateNative_closed (e : Inflation.Carrier S H R U ≃ N)
    (hm : ∀ (g : K) x, e ((Inflation.action S H R U).smul g x) =
      packetPoint S H R U hU g (e x)) (A : Finset (Sigma V)) :
    PacketClosed S H R U (inflateNative S H R U e A) := by
  intro a ha b hF
  obtain ⟨p,hp,k,rfl⟩ := (mem_inflateNative S H R U e A a).mp ha
  let c := e.symm b
  have hc : e c = b := e.apply_symm_apply b
  have he : p.2.val = c.1 := recovery_packet_fst S H R U hU e hm
    p.2.val c.1 k c.2 (by simpa only [hc] using hF)
  apply (mem_inflateNative S H R U e A b).mpr
  exact ⟨p,hp,c.2,(congrArg (fun u => e (u,c.2)) he).trans hc⟩


include hU in
/-- Actual all-owner safe padding is built from the DERIVED all-span
orbit-safe amalgamation. One recovery retains the complete literal seed
and converts every new-old and new-new safe atom to its whole real matrix. -/
theorem safePadding_exists (safe : Set (S.Atom () ()))
    (hSafe : AclOwners.StrongClosedAmalgamation S G safe)
    (seed : Finset N) (hseed : PacketClosed S H R U seed) :
    Nonempty (SafePadding S H R U hU safe seed) := by
  classical
  obtain ⟨e,heo,hec,hem⟩ := Inflation.recovery_readout S H R U hU
  let σ := TransversalSource.sigmaEquiv S H R U
  let old : Finset (Sigma V) := seed.image (fun x => σ.symm (e.symm x).1)
  obtain ⟨E,hOld,hCovers,hCross⟩ := native_safe_padding T
    (TransversalSource.homogeneous S H R U) (orbitSafe S H R U hU safe)
    (orbitSafe_system S H R U hU safe hSafe) old
  let D := inflateNative S H R U e E
  refine ⟨⟨D,inflateNative_closed S H R U hU e hem E,?_,?_,?_⟩⟩
  · intro a ha
    let p := σ.symm (e.symm a).1
    have hp : p ∈ old := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    apply (mem_inflateNative S H R U e E a).mpr
    exact ⟨p,hOld hp,(e.symm a).2,e.apply_symm_apply a⟩
  · intro s
    obtain ⟨p,hp,hps⟩ := hCovers s
    refine ⟨e (p.2.val,1),(mem_inflateNative S H R U e E _).mpr ⟨p,hp,1,rfl⟩,?_⟩
    exact (heo _).trans ((Inflation.table_owner_one S H R U hU _).trans
      (p.2.property.trans hps))
  · intro a ha haOld b hb hF
    obtain ⟨p,hp,g,rfl⟩ := (mem_inflateNative S H R U e E a).mp ha
    obtain ⟨q,hq,h,rfl⟩ := (mem_inflateNative S H R U e E b).mp hb
    have hpOld : p ∉ old := by
      intro hm
      obtain ⟨x,hx,hxp⟩ := Finset.mem_image.mp hm
      subst p
      apply haOld
      apply hseed x hx
      have hh := recovery_phase_in_packet S H R U hU e hem
        (e.symm x).1 (e.symm x).2 g
      change finitePacket S H x.val (e ((e.symm x).1,g)).val
      simpa only [Prod.eta,Equiv.apply_symm_apply] using hh
    have hpq : p ≠ q := by
      intro he
      subst q
      exact hF (recovery_phase_in_packet S H R U hU e hem p.2.val g h)
    obtain ⟨atom,hAtom,hColour⟩ := hCross p hp hpOld q hq hpq
    have hraw := (TransversalSource.colour_some_iff S H R U _ _ atom).mp hColour
    obtain ⟨c,hc,hswitch⟩ := (orbitSafe_matrix_iff S H R U hU safe atom).mp hAtom g h
    refine ⟨c,hc,(hec _ _).trans ?_⟩
    change switchColour S (finitePacket S H) (g*h)
      ((TransversalAge.limitTable S H R U).colour p.2.val q.2.val) = some c
    rw [hraw]
    exact hswitch

/-- A concrete literal source for the fixed faithful reservoir. -/
def safePadding (safe : Set (S.Atom () ()))
    (hSafe : AclOwners.StrongClosedAmalgamation S G safe)
    (seed : Finset N) (hseed : PacketClosed S H R U seed) :
    SafePadding S H R U hU safe seed :=
  (safePadding_exists S H R U hU safe hSafe seed hseed).some

end
end CCO.RelativeMI
