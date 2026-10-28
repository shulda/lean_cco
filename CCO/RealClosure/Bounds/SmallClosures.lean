import CCO.RealClosure.Bounds.PacketBounds
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual finite type counting, using only OLD atoms outside the ORIGINAL
finite packet. Unrealisable or nonalgebraic tuples contribute the empty set.
Every cardinal estimate follows a genuine finiteness construction. -/
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
open scoped BigOperators
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

def offPacketAcl (B : Finset M) : Set M := Acl G B \ packetClosure S H B

def algebraicTypeFibre (B : Finset M) (q : ↥B → OutsideAtom S H) : Set M :=
  {x | x ∈ FibreSet S B (fun b => (q b).val) ∧ x ∈ Acl G B}

theorem algebraicTypeFibre_finite_bound (cco : SemanticCCO.{0,v,0,w} S)
    (B : Finset M) (q : ↥B → OutsideAtom S H) :
    Finite (algebraicTypeFibre S H B q) ∧
      Nat.card (algebraicTypeFibre S H B q) ≤ packetSize S H := by
  classical
  by_cases hn : Nonempty (algebraicTypeFibre S H B q)
  · obtain ⟨x⟩ := hn
    let xp : FibreSet S B (fun b => (q b).val) := ⟨x.val,x.property.1⟩
    letI : Nonempty (FibreSet S B (fun b => (q b).val)) := ⟨xp⟩
    have heq : orbitOver G B x.val = FibreSet S B (fun b => (q b).val) :=
      fibre_orbit_eq S B _ H xp
    have hf : (FibreSet S B (fun b => (q b).val)).Finite := heq ▸ x.property.2
    letI : Finite (FibreSet S B (fun b => (q b).val)) := hf.to_subtype
    let e : algebraicTypeFibre S H B q → FibreSet S B (fun b => (q b).val) :=
      fun y => ⟨y.val,y.property.1⟩
    have he : Function.Injective e := fun _ _ h =>
      Subtype.ext (congrArg (fun z : FibreSet S B (fun b => (q b).val) => z.val) h)
    exact ⟨Finite.of_injective e he,(Nat.card_le_card_of_injective e he).trans
      (finite_fibre_card_le_packet S H cco B (fun b => (q b).val))⟩
  · letI : IsEmpty (algebraicTypeFibre S H B q) := ⟨fun x => hn ⟨x⟩⟩
    exact ⟨inferInstance,by rw [Nat.card_of_isEmpty]; exact Nat.zero_le _⟩

theorem offPacket_not_parameter (B : Finset M) (x : offPacketAcl S H B) : x.val ∉ B := by
  intro hx
  exact x.property.2 ⟨x.val,hx,(finitePacket S H).val.refl _⟩

noncomputable def outsideSpokes (B : Finset M) (x : offPacketAcl S H B) : ↥B → OutsideAtom S H :=
  fun b => ⟨actualSpokes S B x.val (offPacket_not_parameter S H B x) b,by
    intro hp
    have hxb := (mem_diversitySupport S (finitePacket S H)
      (actualSpokes_colour S B x.val (offPacket_not_parameter S H B x) b)).mp hp
    exact x.property.2 ⟨b.val,b.property,(finitePacket S H).val.symm hxb⟩⟩

noncomputable def offPacketTypeEmbedding (B : Finset M) :
    offPacketAcl S H B ↪ Σ q : ↥B → OutsideAtom S H, algebraicTypeFibre S H B q where
  toFun x := ⟨outsideSpokes S H B x,⟨x.val,
    (fun b => actualSpokes_colour S B x.val (offPacket_not_parameter S H B x) b),x.property.1⟩⟩
  inj' _ _ h := Subtype.ext (congrArg
    (fun z : Σ q : ↥B → OutsideAtom S H, algebraicTypeFibre S H B q => z.2.val) h)

/-- The actual off-packet algebraic points over a j-set have at most d∞^j
complete outside-packet OLD spoke types, each finite fibre of size <=c. -/
theorem offPacketAcl_finite_bound (cco : SemanticCCO.{0,v,0,w} S) (B : Finset M) :
    Finite (offPacketAcl S H B) ∧
      Nat.card (offPacketAcl S H B) ≤ packetSize S H * (outsideAtomCount S H)^B.card := by
  classical
  letI := S.finiteAtom () ()
  letI : Fintype (OutsideAtom S H) := Fintype.ofFinite _
  letI : ∀ q : ↥B → OutsideAtom S H, Finite (algebraicTypeFibre S H B q) :=
    fun q => (algebraicTypeFibre_finite_bound S H cco B q).1
  let e := offPacketTypeEmbedding S H B
  refine ⟨Finite.of_injective e e.injective,?_⟩
  calc
    _ ≤ Nat.card (Σ q : ↥B → OutsideAtom S H, algebraicTypeFibre S H B q) :=
      Nat.card_le_card_of_injective e e.injective
    _ = ∑ q : ↥B → OutsideAtom S H, Nat.card (algebraicTypeFibre S H B q) := Nat.card_sigma
    _ ≤ ∑ _q : ↥B → OutsideAtom S H, packetSize S H :=
      Finset.sum_le_sum (fun q _ => (algebraicTypeFibre_finite_bound S H cco B q).2)
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ]
      simp only [nsmul_eq_mul,← Nat.card_eq_fintype_card,Nat.card_fun,Nat.card_eq_finsetCard,Nat.cast_id,outsideAtomCount]
      exact Nat.mul_comm _ _

/-- Finite packet closure is a genuine image of a finite disjoint sum of
whole packets. Uniformity yields its c|A| upper bound. -/
theorem packetClosure_card_le (A : Finset M) :
    Nat.card (packetClosure S H A) ≤ packetSize S H * A.card := by
  classical
  letI : ∀ a : ↥A, Finite (ClassPoint S () (finitePacket S H) a.val) :=
    fun a => finitePacket_finite S H a.val
  let f : (Σ a : ↥A, ClassPoint S () (finitePacket S H) a.val) → packetClosure S H A :=
    fun p => ⟨p.2.val,p.1.val,p.1.property,p.2.property⟩
  have hf : Function.Surjective f := by
    rintro ⟨x,a,ha,hax⟩
    exact ⟨⟨⟨a,ha⟩,⟨x,hax⟩⟩,rfl⟩
  calc
    _ ≤ Nat.card (Σ a : ↥A, ClassPoint S () (finitePacket S H) a.val) :=
      Nat.card_le_card_of_surjective f hf
    _ = ∑ a : ↥A, Nat.card (ClassPoint S () (finitePacket S H) a.val) := Nat.card_sigma
    _ = ∑ _a : ↥A, packetSize S H := by
      apply Finset.sum_congr rfl
      intro a _
      exact (packetSize_eq S H a.val).symm
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]; exact Nat.mul_comm _ _
end CCO.RealClosure.Bounds
