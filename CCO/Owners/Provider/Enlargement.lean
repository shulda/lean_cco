import CCO.Owners.Provider.PacketMotion

/-! Every selected finite-base action extends to the full-packet
enlargement with its action on the ENTIRE owner base retained (C10). -/
namespace CCO.Owners.Provider
open Product ParityHasse.Original RealHull.Geometry
variable {A O G R : Type*} [Group G] [MulAction G A] [MulAction G O]
variable (S : AtomicSource Unit (fun _ => A)) (H : HomogeneousSource S G)

def ambientAut (g : G) : OrbitalAut G A (id : A → A) :=
  ⟨MulAction.toPerm g,(mem_orbitalAut_iff _).mpr (fun _ _ => ⟨g,rfl,rfl⟩)⟩

theorem packet_enlargement (π : A → O) (onto : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (B : Set O)
    (closedB : ∀ u ∈ B, ∀ v, ownerPacket S H π onto equivπ u v → v ∈ B)
    (D₀ : Set A) (hD₀ : D₀.Finite) (over₀ : ∀ x : D₀, π x.val ∈ B)
    (onto₀ : Function.Surjective (ownerProjection π D₀ B over₀))
    (β : R → OrbitalAut G A (Subtype.val : D₀ → A))
    (γ : R → OrbitalAut G O (Subtype.val : B → O))
    (owners₀ : ∀ r (x : D₀), π ((β r).val x).val =
      ((γ r).val (ownerProjection π D₀ B over₀ x)).val) :
    ∃ D₁ : Set A, D₁.Finite ∧ ∃ inc : D₀ ⊆ D₁,
      FullPacketClosed S H D₁ ∧ ∃ over₁ : ∀ x : D₁, π x.val ∈ B,
      Function.Surjective (ownerProjection π D₁ B over₁) ∧
      ∃ α : R → OrbitalAut G A (Subtype.val : D₁ → A),
        (∀ r (x : D₀), ((α r).val ⟨x.val,inc x.property⟩).val = ((β r).val x).val) ∧
        (∀ r (x : D₁), π ((α r).val x).val =
          ((γ r).val (ownerProjection π D₁ B over₁ x)).val) := by
  classical
  let D₁ := packetClosure S H D₀
  have fin₁ : D₁.Finite := packetClosure_finite S H D₀ hD₀
  letI : Finite D₁ := fin₁.to_subtype
  have inc : D₀ ⊆ D₁ := subset_packetClosure S H D₀
  have over₁ : ∀ x : D₁, π x.val ∈ B := fun x =>
    packetClosure_over S H π onto equivπ B closedB D₀
      (fun a ha => over₀ ⟨a,ha⟩) x.val x.property
  have onto₁ : Function.Surjective (ownerProjection π D₁ B over₁) := by
    intro b
    obtain ⟨x,hx⟩ := onto₀ b
    exact ⟨⟨x.val,inc x.property⟩,hx⟩
  have lifts (r : R) := extend_induced_aut S H D₀ hD₀ (β r)
  let g : R → G := fun r => (lifts r).choose
  have gext (r : R) (x : D₀) : g r • x.val = ((β r).val x).val :=
    (lifts r).choose_spec x
  have preserves (r : R) (x : D₁) : g r • x.val ∈ D₁ := by
    obtain ⟨a,ha,hax⟩ := x.property
    have hgF := colourInvariant_groupInvariant S H
      (RealClosure.Bounds.finitePacket S H).property (g r) a x.val hax
    refine ⟨g r • a,?_,hgF⟩
    rw [gext r ⟨a,ha⟩]
    exact ((β r).val ⟨a,ha⟩).property
  let α : R → OrbitalAut G A (Subtype.val : D₁ → A) :=
    fun r => restrictAut (ambientAut (A := A) (g r)) D₁ (preserves r)
  have αext (r : R) (x : D₀) :
      ((α r).val ⟨x.val,inc x.property⟩).val = ((β r).val x).val := gext r x
  have owners₁ (r : R) (x : D₁) :
      π ((α r).val x).val = ((γ r).val (ownerProjection π D₁ B over₁ x)).val := by
    obtain ⟨s,hs⟩ := onto₀ (ownerProjection π D₁ B over₁ x)
    have hπs : π s.val = π x.val := congrArg Subtype.val hs
    change π (g r • x.val) = _
    calc
      _ = g r • π x.val := equivπ (g r) x.val
      _ = g r • π s.val := congrArg (fun o : O => g r • o) hπs.symm
      _ = π (g r • s.val) := (equivπ (g r) s.val).symm
      _ = π ((β r).val s).val := congrArg π (gext r s)
      _ = ((γ r).val (ownerProjection π D₀ B over₀ s)).val := owners₀ r s
      _ = _ := congrArg (fun b : B => ((γ r).val b).val) hs
  exact ⟨D₁,fin₁,inc,packetClosure_closed S H D₀,over₁,onto₁,α,αext,owners₁⟩

end CCO.Owners.Provider
