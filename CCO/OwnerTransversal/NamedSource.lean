import CCO.OwnerTransversal.SourceData
import CCO.FiniteKernel.BinarySource
import CCO.AclOwners.Avoidance

/-! The actual preimage of a finite set of E-owners, with every owner
named individually and every original fine colour retained.  Its full
automorphisms are defined before any homogeneity or amalgamation proof. -/

universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)

abbrev Owner := Quotient R.E.val

def owner (x : M) : Owner S H R := Quotient.mk'' x

abbrev NamedCarrier (B : Finset (Owner S H R)) := {x : M // owner S H R x ∈ B}

/-- Literal old colour names, with one unary predicate per actual owner.
This is the FULL induced named-owner language, including loops. -/
def namedStructure (B : Finset (Owner S H R)) :
    FiniteKernel.BinaryStructure (NamedCarrier S H R B) where
  Unary := Owner S H R
  Binary := FullColour S
  unary q x := owner S H R x.val = q
  binary c x y := col S x.val y.val = c

abbrev NamedAut (B : Finset (Owner S H R)) := (namedStructure S H R B).Aut

def PacketInvariant (B : Finset (Owner S H R)) : Prop :=
  ∀ (e : ResidualData.PacketGroup S H) (x : M), owner S H R x ∈ B →
    owner S H R (e.val x) ∈ B

namespace NamedAut
variable {S H R} {B : Finset (Owner S H R)}

theorem owner_fixed (f : NamedAut S H R B) (x : NamedCarrier S H R B) :
    owner S H R (f.val x).val = owner S H R x.val :=
  (f.property.1 (owner S H R x.val) x).mpr rfl

theorem colour_fixed (f : NamedAut S H R B) (x y : NamedCarrier S H R B) :
    col S (f.val x).val (f.val y).val = col S x.val y.val :=
  (f.property.2 (col S x.val y.val) x y).mpr rfl

end NamedAut

local instance : MulAction G (Owner S H R) := originalQuotientAction S H R.E

/-- An original motion fixing ALL displayed owners restricts to an
automorphism of the actual named preimage. -/
def restrictMotion (B : Finset (Owner S H R)) (g : G)
    (hg : ∀ q ∈ B, g • q = q) : NamedAut S H R B := by
  have ho (x : M) : owner S H R (g • x) = g • owner S H R x := rfl
  have hi (x : M) : owner S H R (g⁻¹ • x) = g⁻¹ • owner S H R x := rfl
  have hginv (q : Owner S H R) (hq : q ∈ B) : g⁻¹ • q = q := by
    exact (congrArg (fun z => g⁻¹ • z) (hg q hq).symm).trans (inv_smul_smul g q)
  let e : Equiv.Perm (NamedCarrier S H R B) := {
    toFun x := ⟨g • x.val, by rw [ho,hg _ x.property]; exact x.property⟩
    invFun x := ⟨g⁻¹ • x.val, by rw [hi,hginv _ x.property]; exact x.property⟩
    left_inv x := Subtype.ext (inv_smul_smul g x.val)
    right_inv x := Subtype.ext (smul_inv_smul g x.val) }
  refine ⟨e, ?_, ?_⟩
  · intro q x
    change owner S H R (g • x.val) = q ↔ owner S H R x.val = q
    rw [ho,hg _ x.property]
  · intro c x y
    change col S (g • x.val) (g • y.val) = c ↔ col S x.val y.val = c
    rw [col_invariant S H]

@[simp] theorem restrictMotion_apply (B : Finset (Owner S H R)) (g : G)
    (hg : ∀ q ∈ B, g • q = q) (x : NamedCarrier S H R B) :
    ((restrictMotion S H R B g hg).val x).val = g • x.val := rfl

/-- Actual real parameters of a finite subset of the named preimage. -/
def realBase (B : Finset (Owner S H R)) (A : Finset (NamedCarrier S H R B)) : Finset M :=
  A.image Subtype.val

@[simp] theorem mem_realBase (B : Finset (Owner S H R))
    (A : Finset (NamedCarrier S H R B)) (x : NamedCarrier S H R B) :
    x.val ∈ realBase S H R B A ↔ x ∈ A := by
  simp only [realBase, Finset.mem_image]
  constructor
  · rintro ⟨y,hy,he⟩
    exact (Subtype.ext he) ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

/-- The packet closure is taken in the actual ambient source. -/
def namedPacketClosure (B : Finset (Owner S H R))
    (A : Finset (NamedCarrier S H R B)) : Set (NamedCarrier S H R B) :=
  {x | x.val ∈ packetClosure S H (realBase S H R B A)}

/-- C23: a packet-invariant owner collection contains every real point
of each packet meeting it. -/
theorem packet_mem_named (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
    (x : NamedCarrier S H R B) (y : M) (hxy : finitePacket S H x.val y) :
    owner S H R y ∈ B := by
  obtain ⟨e,he,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
    x.val y hxy
  exact he ▸ hB e x.val x.property

def packetPoint (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
    (e : ResidualData.PacketGroup S H) (x : NamedCarrier S H R B) :
    NamedCarrier S H R B := ⟨e.val x.val,hB e x.val x.property⟩

/-- All automorphisms of the FULL named language commute with every
literal packet function, by uniqueness of a thin-colour neighbour. -/
theorem namedAut_commutes (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
    (f : NamedAut S H R B) (e : ResidualData.PacketGroup S H)
    (x : NamedCarrier S H R B) :
    f.val (packetPoint S H R B hB e x) = packetPoint S H R B hB e (f.val x) := by
  apply Subtype.ext
  apply (R.packet_thin S H _ (translationColour_below S (finitePacket S H) H e)
    (f.val x).val).unique
  · exact (NamedAut.colour_fixed f x (packetPoint S H R B hB e x)).trans
      (translationColour_at S (finitePacket S H) H e x.val)
  · exact translationColour_at S (finitePacket S H) H e (f.val x).val

theorem packetClosure_subset_dcl (B : Finset (Owner S H R))
    (hB : PacketInvariant S H R B) (A : Finset (NamedCarrier S H R B)) :
    namedPacketClosure S H R B A ⊆ Dcl (NamedAut S H R B) A := by
  classical
  rintro x ⟨a,ha,hax⟩ f hf
  obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp ha
  obtain ⟨e,he,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
    a x.val hax
  have hx : packetPoint S H R B hB e b = x := Subtype.ext (by
    change e.val b.val = x.val
    rw [hba,he])
  change f.val x = x
  rw [← hx, namedAut_commutes S H R B hB f e b]
  have hfb : f.val b = b := hf b hb
  rw [hfb]

variable [Infinite M]

/-- Restriction of the actual original owner stabilizer gives enough
automorphisms of N_B to witness every nonalgebraic orbit.  This lemma
precedes, and does not assume, named-source homogeneity. -/
theorem named_acl_subset_packetClosure (B : Finset (Owner S H R))
    (A : Finset (NamedCarrier S H R B)) :
    Acl (NamedAut S H R B) A ⊆ namedPacketClosure S H R B A := by
  classical
  intro x hx
  let q : ↥B → Quotient R.E.val := Subtype.val
  have howners : OwnerAcl S (G := G) (realBase S H R B A)
      (fun _ : ↥B => R.E) q = packetClosure S H (realBase S H R B A) := by
    rw [mixed_harmless_owners S H R.cco (fun _ : ↥B => R.E)
      (fun _ => R.owner_containsDirections S H) q, R.real_acl S H]
  apply show x.val ∈ packetClosure S H (realBase S H R B A) from ?_
  rw [← howners]
  apply (hx.image Subtype.val).subset
  rintro y ⟨g,hA,hK,rfl⟩
  have hg : ∀ z ∈ B, g • z = z := by
    intro z hz
    exact (fixesOwner_iff_quotient_fixed S H R.E z g).mp (hK ⟨z,hz⟩)
  let f := restrictMotion S H R B g hg
  refine ⟨f.val x,?_,rfl⟩
  refine ⟨f,?_,rfl⟩
  intro a ha
  apply Subtype.ext
  exact hA a.val ((mem_realBase S H R B A a).mpr ha)

/-- C22: actual named-source acl is exactly the original full packet
closure.  The reverse inclusion is even definability by the named thin
functions. No named homogeneity or joint-lifting theorem is used. -/
theorem named_acl (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
    (A : Finset (NamedCarrier S H R B)) :
    Acl (NamedAut S H R B) A = namedPacketClosure S H R B A := by
  apply Set.Subset.antisymm (named_acl_subset_packetClosure S H R B A)
  exact (packetClosure_subset_dcl S H R B hB A).trans (dcl_subset_acl A)

/-- The orbit form needed by both finite avoidance and collision repair. -/
theorem named_orbit_infinite (B : Finset (Owner S H R))
    (A : Finset (NamedCarrier S H R B)) (x : NamedCarrier S H R B)
    (hx : x ∉ namedPacketClosure S H R B A) :
    (orbitOver (NamedAut S H R B) A x).Infinite := by
  intro hf
  exact hx (named_acl_subset_packetClosure S H R B A hf)

end
end CCO.OwnerTransversal
