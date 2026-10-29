import CCO.OwnerTransversal.NamedHomogeneity
import CCO.OwnerTransversal.PacketAction

/-! Entire finite owner permutations lift to actual permutations of
the named preimage. They fix all fine names and commute with all packet
functions, although they may permute the individually named owners. -/
universe v w t z
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization Owners.Product
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
local instance : MulAction G (Owner S H R) := originalQuotientAction S H R.E

/-- C24 including the ENTIRE given owner component and actual restriction
to N_B. Empty real domains and unused owners remain in the finite lift. -/
theorem prescribed_named_action {I : Type z} [Finite I]
    (source target : I → NamedCarrier S H R B)
    (gamma : OrbitalAut G (Owner S H R) (Subtype.val : ↥B → Owner S H R))
    (hReal : ∀ i j, col S (source i).val (source j).val = col S (target i).val (target j).val)
    (hOwner : ∀ i, owner S H R (target i).val =
      (gamma.val ⟨owner S H R (source i).val,(source i).property⟩).val) :
    ∃ (g : G) (e : Equiv.Perm (NamedCarrier S H R B)),
      (∀ i, e (source i) = target i) ∧
      (∀ q : ↥B, g • q.val = (gamma.val q).val) ∧
      (∀ x, (e x).val = g • x.val) ∧
      (∀ x, owner S H R (e x).val = (gamma.val ⟨owner S H R x.val,x.property⟩).val) ∧
      (∀ x y, col S (e x).val (e y).val = col S x.val y.val) ∧
      ∀ t x, e (packetPoint S H R B hB t x) = packetPoint S H R B hB t (e x) := by
  let q : ↥B → Owner S H R := Subtype.val
  let q' : ↥B → Owner S H R := fun b => (gamma.val b).val
  have cover (i : I) : ∃ j, q j = owner S H R (source i).val ∧
      q' j = owner S H R (target i).val :=
    ⟨⟨owner S H R (source i).val,(source i).property⟩,rfl,(hOwner i).symm⟩
  obtain ⟨g,hg,hq⟩ := residual_joint_lifting S H R
    (fun i => (source i).val) (fun i => (target i).val) q q' hReal
    (fun b c => orbitalAut_pair gamma b c) cover
  have hmap (x : NamedCarrier S H R B) : owner S H R (g • x.val) ∈ B := by
    change g • owner S H R x.val ∈ B
    rw [hq ⟨owner S H R x.val,x.property⟩]
    exact (gamma.val ⟨owner S H R x.val,x.property⟩).property
  have hinverse (x : NamedCarrier S H R B) : owner S H R (g⁻¹ • x.val) ∈ B := by
    let b := gamma.val.symm ⟨owner S H R x.val,x.property⟩
    have hb : g • b.val = owner S H R x.val :=
      (hq b).trans (congrArg Subtype.val (gamma.val.apply_symm_apply _))
    change g⁻¹ • owner S H R x.val ∈ B
    rw [← hb,inv_smul_smul]
    exact b.property
  let e : Equiv.Perm (NamedCarrier S H R B) := {
    toFun x := ⟨g • x.val,hmap x⟩
    invFun x := ⟨g⁻¹ • x.val,hinverse x⟩
    left_inv x := Subtype.ext (inv_smul_smul g x.val)
    right_inv x := Subtype.ext (smul_inv_smul g x.val) }
  refine ⟨g,e,(fun i => Subtype.ext (hg i)),hq,(fun _ => rfl),?_,?_,?_⟩
  · intro x
    exact hq ⟨owner S H R x.val,x.property⟩
  · intro x y
    exact col_invariant S H g x.val y.val
  · intro t x
    apply Subtype.ext
    exact (translation_equivariant S (finitePacket S H) G t g x.val).symm

end
end CCO.OwnerTransversal
