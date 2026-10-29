import CCO.FullRows.DecodedStructure

/-! The actual global thin translations are automorphisms of the SAME
complete decoder. They keep the entire row unchanged and act regularly on
each real packet, even when their owner-language action has a kernel. -/
universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (hΔ : ∀ g, TransversalPure.diagonal S H R B hB g ∈ Δ)
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
variable (c : PacketCertificate S H R B hB Δ A hA E hLocal)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "tags" => sourceTag S H R B Δ
local notation "act" => sourceAction S H R B Δ

/-- The actual thin owner action, restricted to the given language group.
No injectivity on owners or homomorphic choice of ambient lifts is used. -/
def decodedThinOwnerHom : K →* Δ where
  toFun g := ⟨TransversalPure.diagonal S H R B hB g,hΔ g⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact (TransversalGauge.ownerHom S H R B hB).map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact (TransversalGauge.ownerHom S H R B hB).map_mul g h

/-- The real permutation action retains each full pair `(i,f)`. -/
def decodedThinPerm : K →* Equiv.Perm (Vertex I K) := by
  letI := TransversalPure.thinCommGroup S H R
  exact {
    toFun := fun g => {
      toFun := translate g
      invFun := translate g⁻¹
      left_inv := by
        intro x
        exact Prod.ext rfl (inv_mul_cancel_left g x.2)
      right_inv := by
        intro x
        exact Prod.ext rfl (mul_inv_cancel_left g x.2) }
    map_one' := by
      apply Equiv.ext
      intro x
      exact Prod.ext rfl (one_mul x.2)
    map_mul' := by
      intro g h
      apply Equiv.ext
      intro x
      exact Prod.ext rfl (mul_assoc g h x.2) }

@[simp] theorem decodedThinPerm_apply (g : K) (x : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    decodedThinPerm S H R B E g x = translate g x := rfl

/-- Simultaneous actual thin translation fixes every optional fine colour
of the decoder, including equality, through its actual-age embedding. -/
theorem decodedColour_translate (g : K) (x y : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    decodedColour S H R B hB Δ hΔ A hA E hLocal c (translate g x) (translate g y) =
      decodedColour S H R B hB Δ hΔ A hA E hLocal c x y := by
  letI := TransversalPure.thinCommGroup S H R
  rw [← decodedPoint_colour S H R B hB Δ hΔ A hA E hLocal c,
    ← decodedPoint_colour S H R B hB Δ hΔ A hA E hLocal c,
    decodedPoint_translate,decodedPoint_translate]
  exact translation_preserves_colour S (finitePacket S H) H (R.packet_thin S H) g _ _

theorem vertexOwner_translate (g : K) (x : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    vertexOwner S H R B hB Δ A hA E hLocal (translate g x) =
      tags (decodedThinOwnerHom S H R B hB Δ hΔ g)
        (vertexOwner S H R B hB Δ A hA E hLocal x) := by
  letI := TransversalPure.thinCommGroup S H R
  exact congrArg (fun e : Equiv.Perm ↥B =>
    e (sourceOriginOwner S H R B hB Δ A hA E hLocal x.1.1))
    ((TransversalGauge.ownerHom S H R B hB).map_mul g x.2)

/-- A genuine external-language automorphism of the fixed complete
decoder, with precisely the actual diagonal owner-language component. -/
def decodedThinAut (g : K) :
    Structure.Automorphism act (encode (decodedData S H R B hB Δ hΔ A hA E hLocal c)) := by
  letI := TransversalPure.thinCommGroup S H R
  refine (ExactAut.mk (tag := tags)
    (D := decodedData S H R B hB Δ hΔ A hA E hLocal c)
    (decodedThinOwnerHom S H R B hB Δ hΔ g) (decodedThinPerm S H R B E g)
    (vertexOwner_translate S H R B hB Δ hΔ A hA E hLocal g) ?_ ?_).toAutomorphism
  · intro a x y
    exact Iff.of_eq (congrArg (· = some a)
      (decodedColour_translate S H R B hB Δ hΔ A hA E hLocal c g x y))
  · intro k x
    change translate g (translate k x) = translate k (translate g x)
    exact Prod.ext rfl (mul_left_comm g k x.2)

@[simp] theorem decodedThinAut_lang (g : K) :
    (decodedThinAut S H R B hB Δ hΔ A hA E hLocal c g).lang =
      ⟨TransversalPure.diagonal S H R B hB g,hΔ g⟩ := rfl

@[simp] theorem decodedThinAut_apply (g : K) (x : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    decodedThinAut S H R B hB Δ hΔ A hA E hLocal c g x = translate g x := rfl

theorem decodedThinAut_one (x : Vertex I K) :
    decodedThinAut S H R B hB Δ hΔ A hA E hLocal c 1 x = x := by
  letI := TransversalPure.thinCommGroup S H R
  change (x.1,1*x.2) = x
  simp

theorem decodedThinAut_mul (g h : K) (x : Vertex I K) :
    decodedThinAut S H R B hB Δ hΔ A hA E hLocal c (g*h) x =
      decodedThinAut S H R B hB Δ hΔ A hA E hLocal c g
        (decodedThinAut S H R B hB Δ hΔ A hA E hLocal c h x) := by
  letI := TransversalPure.thinCommGroup S H R
  change (x.1,(g*h)*x.2) = (x.1,g*(h*x.2))
  rw [mul_assoc]

/-- Both the structural index and the ENTIRE full row remain unchanged. -/
theorem decodedThinAut_packet (g : K) (x : Vertex I K) :
    (decodedThinAut S H R B hB Δ hΔ A hA E hLocal c g x).1 = x.1 := rfl

theorem decodedThinAut_row (g : K) (x : Vertex I K) :
    (decodedThinAut S H R B hB Δ hΔ A hA E hLocal c g x).1.2 = x.1.2 := rfl

/-- Real freeness is independent of any kernel in the owner action. -/
theorem decodedThinAut_free (x : Vertex I K) :
    Function.Injective (fun g : K => decodedThinAut S H R B hB Δ hΔ A hA E hLocal c g x) := by
  letI := TransversalPure.thinCommGroup S H R
  intro g h he
  have hh : g*x.2 = h*x.2 := congrArg Prod.snd he
  have hc := congrArg (fun a : K => a*x.2⁻¹) hh
  exact (mul_inv_cancel_right g x.2).symm.trans
    (hc.trans (mul_inv_cancel_right h x.2))

/-- On every actual packet the action is transitive as well as free. -/
theorem decodedThinAut_regular (x y : Vertex I K) (hxy : x.1 = y.1) :
    ∃! g : K, decodedThinAut S H R B hB Δ hΔ A hA E hLocal c g x = y := by
  letI := TransversalPure.thinCommGroup S H R
  refine ⟨y.2*x.2⁻¹,?_,?_⟩
  · change (x.1,(y.2*x.2⁻¹)*x.2) = y
    apply Prod.ext
    · exact hxy
    · exact inv_mul_cancel_right y.2 x.2
  · intro g hg
    have hh : g*x.2 = y.2 := congrArg Prod.snd hg
    exact (mul_inv_cancel_right g x.2).symm.trans
      (congrArg (fun a : K => a*x.2⁻¹) hh)
end
end CCO.FullRows
