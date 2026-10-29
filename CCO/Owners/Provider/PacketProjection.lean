import CCO.Owners.Provider.OrbitalPackets
import CCO.RawExact.QuotientSourcePalette

/-!
# Actual greatest owner packets and projection of real packets

The canonical owner palette is the genuine induced pair-orbital palette.
It is used to prove invariance under FULL structural automorphisms, without
assuming that they extend globally to the original source (B018 C06--C07).
-/

namespace CCO.Owners.Provider

open ParityHasse.Original RealHull.Geometry OrbitalPackets

variable {M O G : Type*} [Group G] [MulAction G M] [MulAction G O]
variable (S : AtomicSource Unit (fun _ => M)) (H : HomogeneousSource S G)
variable (π : M → O) (onto : Function.Surjective π)
variable (equivariant : ∀ (g : G) x, π (g • x) = g • π x)

noncomputable abbrev ownerSource : AtomicSource Unit (fun _ => O) :=
  RawExact.QuotientPalette.actualQuotientAtomicSource (i := ())
    (fun _ : Unit => O) S H (fun _ => π) (fun _ => onto) (fun _ => equivariant)

noncomputable def ownerPairAction : PairAction (ownerSource S H π onto equivariant) (G := G) where
  invariant g x y := RawExact.QuotientPalette.actualQuotientAtomicSource_colour_invariant
    (i := ()) (fun _ : Unit => O) S H (fun _ => π) (fun _ => onto)
    (fun _ => equivariant) g x y
  homogeneous x y x' y' hc :=
    (RawExact.QuotientPalette.actualQuotientAtomicSource_colour_eq_iff_orbital
      (i := ()) (fun _ : Unit => O) S H (fun _ => π) (fun _ => onto)
      (fun _ => equivariant) x y x' y').mp hc

/-- The greatest finite equivalence in the FULL owner-invariant lattice. -/
noncomputable def ownerPacket : ColourEq (ownerSource S H π onto equivariant) () :=
  (ownerPairAction S H π onto equivariant).packet

theorem ownerPacket_finite : RealClosure.Bounds.FiniteClasses
    (ownerSource S H π onto equivariant) (ownerPacket S H π onto equivariant) :=
  (ownerPairAction S H π onto equivariant).packet_finite

theorem ownerPacket_greatest
    (E : ColourEq (ownerSource S H π onto equivariant) ())
    (hE : RealClosure.Bounds.FiniteClasses (ownerSource S H π onto equivariant) E) :
    E ≤ ownerPacket S H π onto equivariant :=
  (ownerPairAction S H π onto equivariant).le_packet E hE

theorem ownerPacket_fullAut_invariant (f : Equiv.Perm O)
    (hf : ∀ x y : O,
      (ownerSource S H π onto equivariant).colour (i := ()) (j := ()) (f x) (f y) =
        (ownerSource S H π onto equivariant).colour (i := ()) (j := ()) x y)
    (x y : O) :
    ownerPacket S H π onto equivariant (f x) (f y) ↔
      ownerPacket S H π onto equivariant x y :=
  (ownerPairAction S H π onto equivariant).packet_fullAut_invariant f hf x y

theorem fullOwnerInvariant_colour (E : Setoid O)
    (hE : ∀ f : Equiv.Perm O,
      (∀ x y : O,
        (ownerSource S H π onto equivariant).colour (i := ()) (j := ()) (f x) (f y) =
          (ownerSource S H π onto equivariant).colour (i := ()) (j := ()) x y) →
      ∀ x y, E x y → E (f x) (f y)) :
    ColourInvariant (ownerSource S H π onto equivariant) () E :=
  (ownerPairAction S H π onto equivariant).fullAut_invariant_colour E hE

/-- The literal projection kernel, not an imaginary replacement. -/
def projectionKernel : ColourEq S () :=
  ⟨Setoid.ker π, groupInvariant_colourInvariant S H (by
    intro g x y hxy
    change π (g • x) = π (g • y)
    rw [equivariant, equivariant, hxy])⟩

noncomputable def packetJoinKernel : ColourEq S () :=
  ColourEq.join S H (RealClosure.Bounds.finitePacket S H)
    (projectionKernel S H π equivariant)

theorem kernel_le_packetJoinKernel : Setoid.ker π ≤ (packetJoinKernel S H π equivariant).val := by
  change (Setoid.ker π) ≤ (RealClosure.Bounds.finitePacket S H).val ⊔ (Setoid.ker π)
  exact le_sup_right

/-- `(F_Q join ker pi)/ker pi` as an actual owner equivalence. -/
noncomputable def projectedPacket : ColourEq (ownerSource S H π onto equivariant) () := by
  let J := packetJoinKernel S H π equivariant
  refine ⟨Setoid.mapOfSurjective J.val π (kernel_le_packetJoinKernel S H π equivariant) onto, ?_⟩
  apply (ownerPairAction S H π onto equivariant).colour_invariant
  rintro g u v ⟨a, b, hab, ha, hb⟩
  refine ⟨g • a, g • b,
    colourInvariant_groupInvariant S H J.property g a b hab, ?_, ?_⟩
  · exact (equivariant g a).trans (congrArg (fun x : O => g • x) ha)
  · exact (equivariant g b).trans (congrArg (fun x : O => g • x) hb)

theorem projectedPacket_pullback (x y : M) :
    projectedPacket S H π onto equivariant (π x) (π y) ↔
      packetJoinKernel S H π equivariant x y := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hxa := kernel_le_packetJoinKernel S H π equivariant ha.symm
    have hby := kernel_le_packetJoinKernel S H π equivariant hb
    exact (packetJoinKernel S H π equivariant).val.trans hxa
      ((packetJoinKernel S H π equivariant).val.trans hab hby)
  · intro hxy
    exact ⟨x, y, hxy, rfl, rfl⟩

/-- Every reached owner has a representative in ONE finite real packet. -/
theorem projectedPacket_class_iff (x : M) (v : O) :
    projectedPacket S H π onto equivariant (π x) v ↔
      ∃ z : M, RealClosure.Bounds.finitePacket S H x z ∧ π z = v := by
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := onto v
    have hxy := (projectedPacket_pullback S H π onto equivariant x y).mp h
    obtain ⟨z, hxz, hzy⟩ := (sup_relation_iff S H
      (RealClosure.Bounds.finitePacket S H) (projectionKernel S H π equivariant) x y).mp hxy
    exact ⟨z, hxz, hzy⟩
  · rintro ⟨z, hxz, rfl⟩
    apply (projectedPacket_pullback S H π onto equivariant x z).mpr
    apply (sup_relation_iff S H (RealClosure.Bounds.finitePacket S H)
      (projectionKernel S H π equivariant) x z).mpr
    exact ⟨z, hxz, rfl⟩

theorem projectedPacket_finite : RealClosure.Bounds.FiniteClasses
    (ownerSource S H π onto equivariant) (projectedPacket S H π onto equivariant) := by
  intro u
  obtain ⟨x, rfl⟩ := onto u
  let F := RealClosure.Bounds.finitePacket S H
  letI := RealClosure.Bounds.finitePacket_finite S H x
  let f : ClassPoint S () F x →
      ClassPoint (ownerSource S H π onto equivariant) () (projectedPacket S H π onto equivariant) (π x) :=
    fun z => ⟨π z.val, (projectedPacket_class_iff S H π onto equivariant x (π z.val)).mpr
      ⟨z.val, z.property, rfl⟩⟩
  apply Finite.of_surjective f
  intro v
  obtain ⟨z, hz, hπ⟩ := (projectedPacket_class_iff S H π onto equivariant x v.val).mp v.property
  exact ⟨⟨z, hz⟩, Subtype.ext hπ⟩

theorem packet_projection (x y : M)
    (hxy : RealClosure.Bounds.finitePacket S H x y) :
    ownerPacket S H π onto equivariant (π x) (π y) := by
  apply ownerPacket_greatest S H π onto equivariant _
    (projectedPacket_finite S H π onto equivariant)
  exact (projectedPacket_class_iff S H π onto equivariant x (π y)).mpr ⟨y, hxy, rfl⟩

/-- Closing a real seed by full packets introduces no owner outside a
packet-closed owner base. -/
theorem packet_closure_over_base (B₀ : Set O)
    (closed : ∀ u ∈ B₀, ∀ v, ownerPacket S H π onto equivariant u v → v ∈ B₀)
    (A : Set M) (over : ∀ x ∈ A, π x ∈ B₀) :
    ∀ y, (∃ x ∈ A, RealClosure.Bounds.finitePacket S H x y) → π y ∈ B₀ := by
  rintro y ⟨x, hx, hxy⟩
  exact closed (π x) (over x hx) (π y) (packet_projection S H π onto equivariant x y hxy)

end CCO.Owners.Provider
