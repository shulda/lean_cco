import CCO.RealClosure.Bounds.Algebraicity
import CCO.RealClosure.Bounds.Palette
import CCO.RealHull.Geometry.Globalisation
import CCO.RealHull.Geometry.ClassSizes

/-! Actual finite one-point fibres lie in the greatest ORIGINAL finite
packet. No RAW-exactness of that packet enters uniform size or definability.
-/
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

noncomputable def basePoint : M := Classical.choice (S.nonemptySort ())
noncomputable def packetSize : ℕ := Nat.card (ClassPoint S () (finitePacket S H) (basePoint S))
noncomputable def internalAtomCount : ℕ := Nat.card (diversitySupport S (finitePacket S H))

theorem packetSize_eq (x : M) : packetSize S H =
    Nat.card (ClassPoint S () (finitePacket S H) x) := packet_class_card S H _ x

theorem packetSize_pos : 0 < packetSize S H := by
  letI := finitePacket_finite S H (basePoint S)
  exact Nat.card_pos

/-- Every actual induced old atom of a class belongs to its literal old-atom
support. This counts original names, not an arbitrary quotient palette. -/
def classAtomToSupport (E : ColourEq S ()) (x : M) :
    InducedAtom S () {y | E x y} ↪ diversitySupport S E where
  toFun c := ⟨c.val,by
    obtain ⟨y,z,hyz⟩ := c.property
    exact ⟨y.val,z.val,E.val.trans (E.val.symm y.property) z.property,hyz⟩⟩
  inj' _ _ h := Subtype.ext (congrArg (fun z : diversitySupport S E => z.val) h)

/-- C13: the full finite-class theorem is used on F without exactness of F. -/
theorem packet_size_power_two (cco : SemanticCCO.{0,v,0,w} S) :
    ∃ n : ℕ, packetSize S H = 2^n ∧ n ≤ internalAtomCount S H := by
  classical
  letI := S.finiteAtom () ()
  letI := finitePacket_finite S H (basePoint S)
  obtain ⟨n,hn,hbound⟩ := finite_class_size_power_two S () H cco (finitePacket S H) (basePoint S)
  exact ⟨n,hn,hbound.trans (Nat.card_le_card_of_injective
    (classAtomToSupport S (finitePacket S H) (basePoint S))
    (classAtomToSupport S (finitePacket S H) (basePoint S)).injective)⟩

theorem packet_size_le_power (cco : SemanticCCO.{0,v,0,w} S) :
    packetSize S H ≤ 2^(internalAtomCount S H) := by
  obtain ⟨n,hn,hbound⟩ := packet_size_power_two S H cco
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hbound

variable [DecidableEq M]

/-- C12: globalise a FINITE ACTUAL fibre, then use full finite-packet maximality. -/
theorem finite_fibre_in_packet (cco : SemanticCCO.{0,v,0,w} S)
    (A : Finset M) (q : ↥A → Atom S) [Nonempty (FibreSet S A q)] [Finite (FibreSet S A q)]
    (x y : FibreSet S A q) : finitePacket S H x.val y.val := by
  let R := supportEquiv S (fibreSpokeFixer S A q H)
  have hRfin : FiniteClasses S R := by
    apply (finiteClasses_iff_at S H R x.val).mpr
    exact Finite.of_equiv (FibreSet S A q) (finiteFibreClassEquiv S A q H cco x)
  exact le_finitePacket S H R hRfin
    ((finite_fibre_global_class S A q H cco x y.val).mp y.property)

theorem finite_fibre_card_le_packet (cco : SemanticCCO.{0,v,0,w} S)
    (A : Finset M) (q : ↥A → Atom S) [Nonempty (FibreSet S A q)] [Finite (FibreSet S A q)] :
    Nat.card (FibreSet S A q) ≤ packetSize S H := by
  classical
  obtain ⟨x⟩ := ‹Nonempty (FibreSet S A q)›
  letI := finitePacket_finite S H x.val
  let e : FibreSet S A q → ClassPoint S () (finitePacket S H) x.val :=
    fun y => ⟨y.val,finite_fibre_in_packet S H cco A q x y⟩
  have he : Function.Injective e := fun _ _ h =>
    Subtype.ext (congrArg (fun z : ClassPoint S () (finitePacket S H) x.val => z.val) h)
  rw [packetSize_eq S H x.val]
  exact Nat.card_le_card_of_injective e he

def packetClosure (A : Finset M) : Set M :=
  {x | ∃ a ∈ A, finitePacket S H a x}

theorem packetClosure_finite (A : Finset M) : (packetClosure S H A).Finite := by
  have hf : ∀ a ∈ A, {y : M | finitePacket S H a y}.Finite := by
    intro a _
    letI := finitePacket_finite S H a
    exact Set.finite_coe_iff.mpr (show Finite (ClassPoint S () (finitePacket S H) a) from inferInstance)
  have hu := Set.Finite.biUnion A.finite_toSet hf
  exact hu.subset (by rintro y ⟨a,ha,hay⟩; exact Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨ha,hay⟩⟩)

/-- C15: direct orbit argument, independent of model-theoretic transitivity
of acl. Images of y lie in finitely many COMPLETE finite F-classes. -/
theorem acl_packet_saturated (A : Finset M) {x y : M}
    (hx : x ∈ Acl G A) (hxy : finitePacket S H x y) : y ∈ Acl G A := by
  classical
  let B := (show (orbitOver G A x).Finite from hx).toFinset
  apply (packetClosure_finite S H B).subset
  rintro z ⟨g,hg,rfl⟩
  exact ⟨g • x,(Set.Finite.mem_toFinset hx).mpr ⟨g,hg,rfl⟩,
    (class_group_invariant S () H _ g x y).mpr hxy⟩

theorem packetClosure_subset_acl (A : Finset M) : packetClosure S H A ⊆ Acl G A := by
  rintro x ⟨a,ha,hax⟩
  exact acl_packet_saturated S H A (parameter_mem_acl A ha) hax

/-- C16, as an explicit unique finite complete spoke formula. -/
theorem unique_spoke_realisation_of_packet_identity
    (cco : SemanticCCO.{0,v,0,w} S) (hF : finitePacket S H = ⊥)
    (A : Finset M) (q : ↥A → Atom S) [Nonempty (FibreSet S A q)] [Finite (FibreSet S A q)]
    (x : FibreSet S A q) (y : M) : (∀ a : ↥A, col S y a.val = some (q a)) ↔ y = x.val := by
  constructor
  · intro hy
    have hh := finite_fibre_in_packet S H cco A q x ⟨y,hy⟩
    rw [hF] at hh
    exact hh.symm
  · rintro rfl
    exact x.property

theorem acl_eq_dcl_of_packet_identity (cco : SemanticCCO.{0,v,0,w} S)
    (hF : finitePacket S H = ⊥) (A : Finset M) : Acl G A = Dcl G A := by
  classical
  apply Set.Subset.antisymm
  · intro x hx g hg
    by_cases hxA : x ∈ A
    · exact hg x hxA
    · let q := actualSpokes S A x hxA
      let xp : FibreSet S A q := actualFibrePoint S A x hxA
      letI : Nonempty (FibreSet S A q) := ⟨xp⟩
      letI := algebraic_fibre_finite S H A x hxA hx
      have hyo : g • x ∈ FibreSet S A q := by
        exact (fibre_motion_membership S A q H g hg x).mpr xp.property
      exact (unique_spoke_realisation_of_packet_identity S H cco hF A q xp (g • x)).mp hyo
  · exact dcl_subset_acl A
end CCO.RealClosure.Bounds
