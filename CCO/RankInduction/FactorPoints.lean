import CCO.RelativeMI.OrbitWitness
import CCO.Owners.Provider.PointTransfer
import CCO.Owners.Provider.PacketMotion

/-! C19: rooted SINGLETON transport supplies real orbit coverage in the
actual relative-MI witness. Singleton original requests and conjugation
then retain every prescribed ENTIRE owner component. Full packet images
are literal ambient packets, not merely their selected representatives. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization Owners.Product Owners.Provider RelativeMI

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (J : ColourEq S ()) (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B)
variable {safe : Set (S.Atom () ())}
variable (W : OriginalWitness S H J A0 B overA0 safe)
local instance factorPointsCoarseAction : MulAction G (Coarse S H J) :=
  originalQuotientAction S H J

/-- The actual recognizable coarse quotient of this fixed witness. -/
def factorQuotient := inducedQuotient (G := G) (coarseOwner S H J) (fun _ _ => rfl)
  W.carrier (↑B) W.over W.onto

/-- The old ORIGINAL real seed meets every real automorphism orbit.
Owner transitivity alone would not establish this statement. -/
theorem real_orbit_cover (x : W.carrier) :
    ∃ β : OrbitalAut G M (Subtype.val : W.carrier → M), (β.val x).val ∈ A0 := by
  have unsafeSingleton : UnsafeSet S (Subtype.val : W.carrier → M) safe {x} := by
    intro a ha b hb ne _ _
    exact False.elim (ne ((Set.mem_singleton_iff.mp ha).trans
      (Set.mem_singleton_iff.mp hb).symm))
  obtain ⟨β, _, root⟩ := W.rooted {x} unsafeSingleton x (Set.mem_singleton x)
  exact ⟨β, root⟩

/-- Every compatible entire owner permutation and every actual real point
motion lift together. Both conjugating root transports use this SAME W. -/
theorem prescribed_points :
    GroupActions.PrescribedLift (factorQuotient S H J A0 B overA0 W).action
      (factorQuotient S H J A0 B overA0 W).projection := by
  let Q := factorQuotient S H J A0 B overA0 W
  let seed : Set W.carrier := {x | x.val ∈ A0}
  apply prescribedLift_of_seed Q.action Q.projection
    (fun β x => (Q.action_projection β x).symm) seed
  · intro x
    exact real_orbit_cover S H J A0 B overA0 W x
  · intro a ha a' ha' γ compatible
    let a0 : ↥A0 := ⟨a.val, ha⟩
    let a0' : ↥A0 := ⟨a'.val, ha'⟩
    have compatible0 : γ.val (ownerProjection (coarseOwner S H J) (↑A0) (↑B) overA0 a0) =
        ownerProjection (coarseOwner S H J) (↑A0) (↑B) overA0 a0' := compatible
    let request := singletonRequest (S.original_sort_transitive_of_homogeneous H ())
      (coarseOwner S H J) (↑A0) (↑B) overA0 a0 a0' γ compatible0
    obtain ⟨β, owner, extend⟩ := W.extensions request
    refine ⟨β, owner, Subtype.ext ?_⟩
    exact extend ⟨a0, Set.mem_singleton a0⟩

/-- All original finite automorphisms preserve the recognizable packet
relation. This makes no claim that the quotient owner action is faithful. -/
theorem packet_iff (β : OrbitalAut G M (Subtype.val : W.carrier → M))
    (x y : W.carrier) :
    finitePacket S H (β.val x).val (β.val y).val ↔ finitePacket S H x.val y.val :=
  induced_packet_iff S H W.carrier β x y

/-- Full F-closure of W turns restricted packet preservation into equality
with the ENTIRE ambient packet above the transported point. -/
theorem packet_image (β : OrbitalAut G M (Subtype.val : W.carrier → M))
    (x : W.carrier) :
    (fun z : W.carrier => (β.val z).val) ''
        {z : W.carrier | finitePacket S H x.val z.val} =
      {y : M | finitePacket S H (β.val x).val y} :=
  full_packet_image S H W.carrier W.closed β x

/-- The prescribed point and full-packet conclusions use ONE automorphism
with the exact requested action on ALL named finite coarse owners. -/
theorem prescribed_point_and_packet (x y : W.carrier)
    (γ : OrbitalAut G (Coarse S H J) (Subtype.val : ↥B → Coarse S H J))
    (compatible : γ • (factorQuotient S H J A0 B overA0 W).projection x =
      (factorQuotient S H J A0 B overA0 W).projection y) :
    ∃ β : OrbitalAut G M (Subtype.val : W.carrier → M),
      (factorQuotient S H J A0 B overA0 W).action β = γ ∧ β.val x = y ∧
      (fun z : W.carrier => (β.val z).val) ''
          {z : W.carrier | finitePacket S H x.val z.val} =
        {z : M | finitePacket S H y.val z} := by
  obtain ⟨β, owner, move⟩ := prescribed_points S H J A0 B overA0 W x y γ compatible
  have motion : β.val x = y := move
  refine ⟨β, owner, motion, ?_⟩
  rw [← motion]
  exact packet_image S H J A0 B overA0 W β x

end
end CCO.RankInduction.Factors
