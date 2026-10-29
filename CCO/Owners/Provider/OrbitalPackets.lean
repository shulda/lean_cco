import CCO.RealClosure.Bounds.Packet

/-!
# The elementary finite-packet construction with only pair homogeneity

This is the pair-action specialization of the accepted finite-coarsening
construction: it reuses its full colour-invariant poset and its actual
finite-coarsening family. No homogeneity of longer quotient tuples is needed.
-/

namespace CCO.Owners.Provider.OrbitalPackets

open ParityHasse.Original RealHull.Geometry

variable {M G : Type*} [Group G] [MulAction G M]
variable (S : AtomicSource Unit (fun _ => M))

/-- Exactly the actual pair-action facts; no higher-tuple extension provider. -/
structure PairAction where
  invariant : ∀ (g : G) (x y : M), S.colour (i := ()) (j := ()) (g • x) (g • y) = S.colour (i := ()) (j := ()) x y
  homogeneous : ∀ (x y x' y' : M), S.colour (i := ()) (j := ()) x y = S.colour (i := ()) (j := ()) x' y' →
    ∃ g : G, g • x = x' ∧ g • y = y'

namespace PairAction

variable {S} (P : PairAction S (G := G))
include P

theorem group_invariant {R : M → M → Prop} (hR : ColourInvariant S () R) :
    ∀ (g : G) x y, R x y → R (g • x) (g • y) := by
  intro g x y hxy
  exact (hR _ _ _ _ (P.invariant g x y).symm).mp hxy

theorem colour_invariant {R : M → M → Prop}
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y)) :
    ColourInvariant S () R := by
  intro x y x' y' hc
  obtain ⟨g, hgx, hgy⟩ := P.homogeneous x y x' y' hc
  constructor
  · intro h
    simpa only [hgx, hgy] using hR g x y h
  · intro h
    have hh := hR g⁻¹ x' y' h
    rw [← hgx, ← hgy] at hh
    simpa only [inv_smul_smul] using hh

theorem pair_flip (x y : M) : ∃ g : G, g • x = y ∧ g • y = x :=
  P.homogeneous x y y x (colour_symmetric S x y)

theorem comp_colour_invariant {R T : M → M → Prop}
    (hR : ColourInvariant S () R) (hT : ColourInvariant S () T) :
    ColourInvariant S () (RawSymmetric.compose R T) := by
  apply P.colour_invariant
  rintro g x y ⟨z, hxz, hzy⟩
  exact ⟨g • z, P.group_invariant hR g x z hxz, P.group_invariant hT g z y hzy⟩

def join (E F : ColourEq S ()) : ColourEq S () := by
  have h := RawSymmetric.comp_equivalences_is_join E F
    ⟨E.val.refl, fun _ _ h => E.val.symm h, fun _ _ _ h k => E.val.trans h k⟩
    ⟨F.val.refl, fun _ _ h => F.val.symm h, fun _ _ _ h k => F.val.trans h k⟩
    (P.group_invariant E.2) (P.group_invariant F.2) P.pair_flip
  exact ⟨{ r := RawSymmetric.compose E F
           iseqv := ⟨h.1.refl, fun hxy => h.1.symm _ _ hxy,
             fun hxy hyz => h.1.trans _ _ _ hxy hyz⟩ }, P.comp_colour_invariant E.2 F.2⟩

@[instance_reducible] def lattice : Lattice (ColourEq S ()) where
  __ := (inferInstance : SemilatticeInf (ColourEq S ()))
  sup := P.join
  le_sup_left E F x y hxy := ⟨y, hxy, F.val.refl y⟩
  le_sup_right E F x y hxy := ⟨x, E.val.refl x, hxy⟩
  sup_le E F K hE hF x y hxy := by
    obtain ⟨z, hxz, hzy⟩ := hxy
    exact K.val.trans (hE hxz) (hF hzy)

theorem finite_join (E F : ColourEq S ())
    (hE : RealClosure.Bounds.FiniteClasses S E)
    (hF : RealClosure.Bounds.FiniteClasses S F) :
    RealClosure.Bounds.FiniteClasses S (P.join E F) := by
  intro x
  letI := hE x
  letI : ∀ y : ClassPoint S () E x, Finite (ClassPoint S () F y.val) := fun y => hF y.val
  let f : (Σ y : ClassPoint S () E x, ClassPoint S () F y.val) →
      ClassPoint S () (P.join E F) x :=
    fun p => ⟨p.2.val, p.1.val, p.1.property, p.2.property⟩
  apply Finite.of_surjective f
  rintro ⟨z, y, hxy, hyz⟩
  exact ⟨⟨⟨y, hxy⟩, ⟨z, hyz⟩⟩, rfl⟩

theorem finiteIndex_bot_iff (E : ColourEq S ()) :
    FinitePackets.Geometry.FiniteIndex S ⊥ E ↔ RealClosure.Bounds.FiniteClasses S E := by
  constructor
  · intro h x
    letI := h x
    exact Finite.of_equiv _ (bottomClassEquiv S () E x)
  · intro h x
    letI := h x
    exact Finite.of_equiv _ (bottomClassEquiv S () E x).symm

/-- The accepted finite-coarsening family, folded in the actual pair lattice. -/
noncomputable def packet : ColourEq S () :=
  letI := P.lattice
  (FinitePackets.Geometry.finiteCoarsenings S ⊥).sup id

theorem packet_finite : RealClosure.Bounds.FiniteClasses S P.packet := by
  classical
  letI := P.lattice
  have step (s : Finset (ColourEq S ()))
      (hs : ∀ E ∈ s, RealClosure.Bounds.FiniteClasses S E) :
      RealClosure.Bounds.FiniteClasses S (s.sup id) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty] using RealClosure.Bounds.finiteClasses_bot S
    | @insert E s he ih =>
      rw [Finset.sup_insert]
      exact P.finite_join E (s.sup id) (hs E (Finset.mem_insert_self E s))
        (ih (fun F hF => hs F (Finset.mem_insert_of_mem hF)))
  exact step _ (fun E hE => (P.finiteIndex_bot_iff E).mp
    ((FinitePackets.Geometry.mem_finiteCoarsenings S ⊥ E).mp hE).2)

theorem le_packet (E : ColourEq S ())
    (hE : RealClosure.Bounds.FiniteClasses S E) : E ≤ P.packet := by
  letI := P.lattice
  apply Finset.le_sup (f := id)
  exact (FinitePackets.Geometry.mem_finiteCoarsenings S ⊥ E).mpr
    ⟨bot_le, (P.finiteIndex_bot_iff E).mpr hE⟩

/-- Every structural automorphism preserves the actual packet, whether or
not it belongs to the originally induced action group. -/
theorem packet_fullAut_invariant (f : Equiv.Perm M)
    (hf : ∀ x y : M, S.colour (i := ()) (j := ()) (f x) (f y) = S.colour (i := ()) (j := ()) x y) (x y : M) :
    P.packet (f x) (f y) ↔ P.packet x y :=
  P.packet.property _ _ _ _ (hf x y)

/-- Every equivalence invariant under ALL structural automorphisms is in
the same finite colour lattice, since each original action is structural. -/
theorem fullAut_invariant_colour (E : Setoid M)
    (hE : ∀ f : Equiv.Perm M,
      (∀ x y : M, S.colour (i := ()) (j := ()) (f x) (f y) = S.colour (i := ()) (j := ()) x y) →
      ∀ x y, E x y → E (f x) (f y)) : ColourInvariant S () E := by
  apply P.colour_invariant
  intro g x y hxy
  let f : Equiv.Perm M := {
    toFun := fun x => g • x
    invFun := fun x => g⁻¹ • x
    left_inv := inv_smul_smul g
    right_inv := smul_inv_smul g }
  exact hE f (P.invariant g) x y hxy

/-- The weaker pair-action construction agrees literally with accepted
Sigma(Id) whenever full source homogeneity is available. -/
theorem packet_eq_accepted (H : HomogeneousSource S G) :
    P.packet = RealClosure.Bounds.finitePacket S H := by
  apply le_antisymm
  · exact RealClosure.Bounds.le_finitePacket S H _ P.packet_finite
  · exact P.le_packet _ (RealClosure.Bounds.finitePacket_finite S H)

end PairAction

end CCO.Owners.Provider.OrbitalPackets
