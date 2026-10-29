import CCO.Owners.Provider.PacketClosure
import CCO.Owners.Provider.ExactLift

/-! Actual finite automorphisms preserve restricted original packets.
They act on whole ambient packets exactly when the finite domain contains
those packets. This is C30, separate from pure point conjugation. -/
namespace CCO.Owners.Provider
open Product ParityHasse.Original RealHull.Geometry
variable {A G : Type*} [Group G] [MulAction G A]
variable (S : AtomicSource Unit (fun _ => A)) (H : HomogeneousSource S G)

include S H in
theorem extend_induced_aut (D : Set A) (hD : D.Finite)
    (β : OrbitalAut G A (Subtype.val : D → A)) :
    ∃ g : G, ∀ x : D, g • x.val = (β.val x).val := by
  have hh (x y : D) : GroupActions.orbital (G := G)
      (β⁻¹.val x).val (β⁻¹.val y).val x.val y.val := by
    simpa using orbitalAut_pair β (β⁻¹.val x) (β⁻¹.val y)
  obtain ⟨g,hg⟩ := source_orbital_homogeneous S H D hD
    (fun x => (β⁻¹.val x).val) hh
  refine ⟨g,?_⟩
  intro x
  simpa using hg (β.val x)

theorem induced_packet_iff (D : Set A)
    (β : OrbitalAut G A (Subtype.val : D → A)) (x y : D) :
    RealClosure.Bounds.finitePacket S H (β.val x).val (β.val y).val ↔
      RealClosure.Bounds.finitePacket S H x.val y.val := by
  let F := RealClosure.Bounds.finitePacket S H
  obtain ⟨g,hgx,hgy⟩ := orbitalAut_pair β x y
  have hg := class_group_invariant S () H F g x.val y.val
  simpa only [hgx,hgy] using hg

/-- The finite-domain statement never applies beta outside its domain. -/
theorem packet_subset_motion (D : Set A)
    (β : OrbitalAut G A (Subtype.val : D → A)) (x y : D)
    (hxy : β.val x = y) (U : Set A) (hUD : U ⊆ D)
    (hU : ∀ z ∈ U, RealClosure.Bounds.finitePacket S H x.val z) :
    ∀ z : U, RealClosure.Bounds.finitePacket S H y.val
      (β.val ⟨z.val,hUD z.property⟩).val := by
  intro z
  rw [← hxy]
  exact (induced_packet_iff S H D β x ⟨z.val,hUD z.property⟩).mpr (hU z.val z.property)

/-- On a full-packet-closed finite domain these are complete AMBIENT
packets, and beta maps one onto the other. -/
theorem full_packet_image (D : Set A) (closed : FullPacketClosed S H D)
    (β : OrbitalAut G A (Subtype.val : D → A)) (x : D) :
    (fun z : D => (β.val z).val) ''
        {z : D | RealClosure.Bounds.finitePacket S H x.val z.val} =
      {y : A | RealClosure.Bounds.finitePacket S H (β.val x).val y} := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (induced_packet_iff S H D β x z).mpr hz
  · intro hy
    have hyD : y ∈ D := closed (β.val x).val (β.val x).property y hy
    let z : D := β⁻¹.val ⟨y,hyD⟩
    have hz : RealClosure.Bounds.finitePacket S H x.val z.val := by
      apply (induced_packet_iff S H D β x z).mp
      simpa [z] using hy
    exact ⟨z,hz,by simp [z]⟩

end CCO.Owners.Provider
