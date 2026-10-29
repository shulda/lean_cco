import CCO.Owners.Provider.PacketProjection
import CCO.Owners.Provider.Induced

/-! Finite full-packet closures and actual nonempty owner seeds (C08).
Every member of every ambient packet is retained. -/
namespace CCO.Owners.Provider
open Product ParityHasse.Original RealHull.Geometry
variable {A O G : Type*} [Group G] [MulAction G A] [MulAction G O]
variable (S : AtomicSource Unit (fun _ => A)) (H : HomogeneousSource S G)

def packetClosure (T : Set A) : Set A :=
  {y | ∃ x ∈ T, RealClosure.Bounds.finitePacket S H x y}

def FullPacketClosed (T : Set A) : Prop :=
  ∀ x ∈ T, ∀ y, RealClosure.Bounds.finitePacket S H x y → y ∈ T

theorem subset_packetClosure (T : Set A) : T ⊆ packetClosure S H T :=
  fun x hx => ⟨x,hx,(RealClosure.Bounds.finitePacket S H).val.refl x⟩

theorem packetClosure_finite (T : Set A) (hT : T.Finite) :
    (packetClosure S H T).Finite := by
  let F := RealClosure.Bounds.finitePacket S H
  letI : Finite T := hT.to_subtype
  letI : ∀ x : T, Finite (ClassPoint S () F x.val) :=
    fun x => RealClosure.Bounds.finitePacket_finite S H x.val
  let f : (Σ x : T, ClassPoint S () F x.val) → packetClosure S H T :=
    fun p => ⟨p.2.val,⟨p.1.val,p.1.property,p.2.property⟩⟩
  have onto : Function.Surjective f := by
    intro y
    obtain ⟨x,hx,hxy⟩ := y.property
    exact ⟨⟨⟨x,hx⟩,⟨y.val,hxy⟩⟩,rfl⟩
  letI := Finite.of_surjective f onto
  exact Set.toFinite _

theorem packetClosure_closed (T : Set A) : FullPacketClosed S H (packetClosure S H T) := by
  rintro x ⟨a,ha,hax⟩ y hxy
  exact ⟨a,ha,(RealClosure.Bounds.finitePacket S H).val.trans hax hxy⟩

theorem packetClosure_over (π : A → O) (onto : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (B : Set O)
    (closed : ∀ u ∈ B, ∀ v, ownerPacket S H π onto equivπ u v → v ∈ B)
    (T : Set A) (over : ∀ x ∈ T, π x ∈ B) :
    ∀ y ∈ packetClosure S H T, π y ∈ B :=
  packet_closure_over_base S H π onto equivπ B closed T over

/-- Add one actual representative of EVERY owner, then take whole packets.
Nonempty B therefore gives a nonempty seed even when A is empty. -/
theorem packet_seed (π : A → O) (onto : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (B : Set O) (hB : B.Finite) (nonemptyB : B.Nonempty)
    (closed : ∀ u ∈ B, ∀ v, ownerPacket S H π onto equivπ u v → v ∈ B)
    (T : Set A) (hT : T.Finite) (over : ∀ x ∈ T, π x ∈ B) :
    ∃ U : Set A, U.Finite ∧ T ⊆ U ∧ U.Nonempty ∧ FullPacketClosed S H U ∧
      ∃ overU : ∀ x : U, π x.val ∈ B,
        Function.Surjective (ownerProjection π U B overU) := by
  classical
  letI : Finite B := hB.to_subtype
  let s : B → A := fun b => Classical.choose (onto b.val)
  have hs (b : B) : π (s b) = b.val := Classical.choose_spec (onto b.val)
  let V : Set A := T ∪ Set.range s
  let U := packetClosure S H V
  have hV : V.Finite := hT.union (Set.finite_range s)
  have hVU : V ⊆ U := subset_packetClosure S H V
  have overV : ∀ x ∈ V, π x ∈ B := by
    rintro x (hx | ⟨b,rfl⟩)
    · exact over x hx
    · rw [hs b]; exact b.property
  have overU : ∀ x : U, π x.val ∈ B := fun x =>
    packetClosure_over S H π onto equivπ B closed V overV x.val x.property
  refine ⟨U,packetClosure_finite S H V hV,fun x hx => hVU (Or.inl hx),?_,
    packetClosure_closed S H V,overU,?_⟩
  · obtain ⟨b,hb⟩ := nonemptyB
    exact ⟨s ⟨b,hb⟩,hVU (Or.inr ⟨⟨b,hb⟩,rfl⟩)⟩
  · intro b
    exact ⟨⟨s b,hVU (Or.inr ⟨b,rfl⟩)⟩,Subtype.ext (hs b)⟩

end CCO.Owners.Provider
