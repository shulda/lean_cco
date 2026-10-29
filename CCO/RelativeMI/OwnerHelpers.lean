import CCO.OwnerTransversal.ClosedSAP
import CCO.OwnerTransversal.TransversalAge
import CCO.OwnerTransversal.InflationBasic
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Actual real packets are regular; their owner labels need not be.
One full packet for each owner orbit supplies every named owner. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (U : Finset (Owner S H R)) (hU : PacketInvariant S H R U)
local notation "K" => ResidualData.PacketGroup S H
local notation "N" => NamedCarrier S H R U

/-- The actual owner action, allowing arbitrary stabilizers. -/
def ownerOrbit (s : ↥U) : Set ↥U := by
  letI := packetOwnerSetAction S H R U hU
  exact MulAction.orbit K s

def ownerStabilizer (s : ↥U) : Subgroup K := by
  letI := packetOwnerSetAction S H R U hU
  exact MulAction.stabilizer K s

/-- Exact actual real packet fibres, with literal named owners. -/
def packetOwnerFibre (x : N) (s : ↥U) : Type v :=
  {y : N // finitePacket S H x.val y.val ∧ ownerLabel S H R U y = s}

def packetPhaseFibreEquiv (x : N) (s : ↥U) :
    {g : K // (packetOwnerSetAction S H R U hU).smul g (ownerLabel S H R U x) = s} ≃
      packetOwnerFibre S H R U x s := by
  apply Equiv.ofBijective (fun g =>
    ⟨packetPoint S H R U hU g.val x,
      translation_in_packet S (finitePacket S H) G g.val x.val,
      (named_owner_equivariant S H R U hU g.val x).trans g.property⟩)
  constructor
  · intro g h he
    apply Subtype.ext
    exact Inflation.named_action_free S H R U hU x (congrArg Subtype.val he)
  · intro y
    obtain ⟨g,hg,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
      x.val y.val.val y.property.1
    have he : packetPoint S H R U hU g x = y.val := Subtype.ext hg
    have ho : (packetOwnerSetAction S H R U hU).smul g (ownerLabel S H R U x) = s :=
      (named_owner_equivariant S H R U hU g x).symm.trans
        ((congrArg (ownerLabel S H R U) he).trans y.property.2)
    exact ⟨⟨g,ho⟩,Subtype.ext he⟩

private def phaseStabilizerEquiv (s t : ↥U) (g₀ : K)
    (hg₀ : (packetOwnerSetAction S H R U hU).smul g₀ s = t) :
    {g : K // (packetOwnerSetAction S H R U hU).smul g s = t} ≃
      ownerStabilizer S H R U hU s := by
  letI := packetOwnerSetAction S H R U hU
  change {g : K // g • s = t} ≃ MulAction.stabilizer K s
  change g₀ • s = t at hg₀
  exact {
    toFun := fun g => ⟨g₀⁻¹*g.val,by
      change (g₀⁻¹*g.val) • s = s
      rw [mul_smul,g.property,← hg₀,inv_smul_smul]⟩
    invFun := fun g => ⟨g₀*g.val,by rw [mul_smul,g.property,hg₀]⟩
    left_inv := fun g => Subtype.ext (by simp)
    right_inv := fun g => Subtype.ext (by simp) }

/-- OH: every real owner fibre has the stabilizer multiplicity, not one
point per owner. Distinct thin phases are distinct real points. -/
theorem packet_owner_multiplicity (x : N) (s : ↥U)
    (hs : s ∈ ownerOrbit S H R U hU (ownerLabel S H R U x)) :
    Nat.card (packetOwnerFibre S H R U x s) =
      Nat.card (ownerStabilizer S H R U hU (ownerLabel S H R U x)) := by
  let := packetOwnerSetAction S H R U hU
  obtain ⟨g₀,hg₀⟩ := hs
  exact Nat.card_congr ((packetPhaseFibreEquiv S H R U hU x s).symm.trans
    (phaseStabilizerEquiv S H R U hU _ _ g₀ hg₀))

omit [Infinite M] in
theorem packet_owner_orbit (x : N) :
    ownerLabel S H R U '' {y : N | finitePacket S H x.val y.val} =
      ownerOrbit S H R U hU (ownerLabel S H R U x) := by
  let := packetOwnerSetAction S H R U hU
  ext s
  constructor
  · rintro ⟨y,hxy,rfl⟩
    obtain ⟨g,hg,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H) x.val y.val hxy
    exact ⟨g,(named_owner_equivariant S H R U hU g x).symm.trans
      (congrArg (ownerLabel S H R U) (Subtype.ext hg))⟩
  · rintro ⟨g,hg⟩
    exact ⟨packetPoint S H R U hU g x,translation_in_packet S (finitePacket S H) G g x.val,
      (named_owner_equivariant S H R U hU g x).trans hg⟩

def ownerOrbitSetoid : Setoid ↥U := by
  letI := packetOwnerSetAction S H R U hU
  exact MulAction.orbitRel K ↥U

abbrev OwnerOrbitIndex := Quotient (ownerOrbitSetoid S H R U hU)

def ownerOrigin (s : ↥U) : N :=
  ⟨s.val.out,by simpa only [owner,Quotient.out_eq] using s.property⟩

omit [Infinite M] in
@[simp] theorem ownerOrigin_owner (s : ↥U) : ownerLabel S H R U (ownerOrigin S H R U s) = s := by
  apply Subtype.ext
  exact Quotient.out_eq s.val

/-- Precisely one chosen real packet for each owner-orbit index. -/
def ownerHelper : Finset N := by
  classical
  exact Finset.univ.biUnion (fun q : OwnerOrbitIndex S H R U hU => namedPacketFinset S H R U {ownerOrigin S H R U q.out})

theorem ownerHelper_closed : PacketClosed S H R U (ownerHelper S H R U hU) := by
  classical
  intro x hx y hxy
  obtain ⟨q,_,hx⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,
    packetClosed_namedPacketFinset S H R U _ x hx y hxy⟩

theorem ownerHelper_covers (s : ↥U) :
    ∃ x ∈ ownerHelper S H R U hU, ownerLabel S H R U x = s := by
  classical
  let := packetOwnerSetAction S H R U hU
  let q : OwnerOrbitIndex S H R U hU := Quotient.mk _ s
  have hrel : q.out ∈ MulAction.orbit K s := Quotient.exact (Quotient.out_eq q)
  have hs : s ∈ ownerOrbit S H R U hU (ownerLabel S H R U (ownerOrigin S H R U q.out)) := by
    rw [ownerOrigin_owner]
    exact MulAction.mem_orbit_symm.mp hrel
  rw [← packet_owner_orbit S H R U hU (ownerOrigin S H R U q.out)] at hs
  obtain ⟨x,hx,hown⟩ := hs
  refine ⟨x,Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,?_⟩,hown⟩
  exact (mem_namedPacketFinset S H R U _ x).mpr
    ⟨(ownerOrigin S H R U q.out).val,by simp [realBase],hx⟩

omit [Infinite M] in
/-- Different owner-orbit choices cannot be the same real packet. -/
theorem ownerHelper_packets_distinct (q r : OwnerOrbitIndex S H R U hU)
    (hqr : q ≠ r) :
    ¬ finitePacket S H (ownerOrigin S H R U q.out).val (ownerOrigin S H R U r.out).val := by
  let := packetOwnerSetAction S H R U hU
  intro hF
  have hmem : ownerLabel S H R U (ownerOrigin S H R U r.out) ∈
      ownerLabel S H R U '' {y : N | finitePacket S H (ownerOrigin S H R U q.out).val y.val} :=
    ⟨ownerOrigin S H R U r.out,hF,rfl⟩
  rw [packet_owner_orbit S H R U hU] at hmem
  rw [ownerOrigin_owner,ownerOrigin_owner] at hmem
  have hRel : ownerOrbitSetoid S H R U hU r.out q.out := hmem
  have he : r = q := (Quotient.out_eq r).symm.trans
    ((Quotient.sound hRel).trans (Quotient.out_eq q))
  exact hqr he.symm

include hU in
/-- The prescribed old set is retained literally. The whole helper is
moved at once by an actual named automorphism, preserving every owner. -/
theorem disjoint_owner_helper (V : Finset N) :
    ∃ T : Finset N, PacketClosed S H R U T ∧ Disjoint T V ∧
      ∀ s : ↥U, ∃ x ∈ T, ownerLabel S H R U x = s := by
  classical
  obtain ⟨f,_,hdis⟩ := closed_disjoint_copy S H R U ∅ (ownerHelper S H R U hU) V
    (by intro x hx; exact False.elim (Finset.notMem_empty x hx))
  let T := (ownerHelper S H R U hU).image f.val
  refine ⟨T,packetClosed_image S H R U _ (ownerHelper_closed S H R U hU) f,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hxV
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.notMem_empty _ (hdis y hy (f.val y) hxV rfl)
  · intro s
    obtain ⟨x,hx,hown⟩ := ownerHelper_covers S H R U hU s
    exact ⟨f.val x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,
      (Subtype.ext (NamedAut.owner_fixed f x)).trans hown⟩

end
end CCO.RelativeMI
