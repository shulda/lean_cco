import CCO.APCharacter.MaskReadout
import CCO.RigidGroupoid.Geometry.QuotientBijection

/-!
# B060 N03: rigid character has zero phase on a real triangle loop

If a genuine rigid arrow R admits real pairs (x,y), (y,z), (x,z),
its actual quotient composition R;R and R share (x,z); the accepted
original homogeneous-source uniqueness forces R;R=R. Applying the
genuine groupoid character and cancelling gives character(R)=0.

For a single realized same-sort old atom a with a true (a,a,a)
triangle, homogeneity transports the rigid arrow's old a-pair to
each of its three sides, hence every such arrow has zero phase.
Therefore the B047 actual source masks allow the same valid bit
at the endpoints of ANY a-pair.

This proves the algebraic part of B060 N03 (same-bit legality).
The infinite monochromatic clique, actual finite-seed simultaneous
extension, and infinite new owner types are still open.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

open APCharacter
open RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A)

/-- An actual OLD rigid arrow's character vanishes when its
same-arrow real relation contains a triangle. No assumed
functional quotient homogeneity or nonrigid phase table. -/
theorem phase_rigid_triangle_zero
    (b : Reached S A)
    (R : Arrow S (Reached.kernel H C b) (Reached.kernel H C b))
    (x y z : X b.val)
    (hxy : R.rel x y) (hyz : R.rel y z) (hxz : R.rel x z) :
    letI := Reached.groupoid H C (A := A)
    P.character.value R = 0 := by
  letI := Reached.groupoid H C (A := A)
  have hc : (R.comp C R).rel x z := ⟨y,hxy,hyz⟩
  have heq : R.comp C R = R :=
    (R.comp C R).eq_of_common_real_pair H R hc hxz
  have hvalue : P.character.value (R.comp C R) = P.character.value R :=
    congrArg (fun T : Arrow S (Reached.kernel H C b) (Reached.kernel H C b) =>
      P.character.value T) heq
  have hadd : P.character.value R + P.character.value R =
      P.character.value R := (P.character.map_comp R R).symm.trans hvalue
  have hadd' : P.character.value R + P.character.value R =
      P.character.value R + 0 := by
    simpa only [add_zero] using hadd
  exact add_left_cancel hadd'

/-- Real old homogeneous pair orbitals have ONE truth value in
any actual B047 rigid bridge relation, by genuine old
pair-homogeneity and the bridge's original exact invariance. -/
private theorem arrow_rel_of_same_colour
    (H : HomogeneousSource S G)
    {i : ι} {K : Kernel S i} (R : Arrow S K K)
    (x y u v : X i)
    (hxy : R.rel x y)
    (hcol : S.colour x y = S.colour u v) :
    R.rel u v := by
  obtain ⟨g,hgx,hgy⟩ :=
    S.pair_homogeneous_of_homogeneous H x u y v hcol
  have hr := R.exact.invariant S H g x y hxy
  simpa only [hgx,hgy] using hr

/-- An actual old a-triangle forces zero character on ANY
old same-sort rigid arrow which contains an a-pair. All
three pieces are genuine represented old orbitals. -/
theorem phase_loop_atom_zero
    (b : Reached S A) (a : S.Atom b.val b.val)
    (hTri : S.Triangle a a a)
    (R : Arrow S (Reached.kernel H C b) (Reached.kernel H C b))
    (x y : X b.val) (hR : R.rel x y)
    (hAtom : S.colour x y = some a) :
    letI := Reached.groupoid H C (A := A)
    P.character.value R = 0 := by
  obtain ⟨p,q,z,hpq,hqz,hpz⟩ := hTri
  have hpqR : R.rel p q :=
    arrow_rel_of_same_colour S H R x y p q hR (hAtom.trans hpq.symm)
  have hqzR : R.rel q z :=
    arrow_rel_of_same_colour S H R x y q z hR (hAtom.trans hqz.symm)
  have hpzR : R.rel p z :=
    arrow_rel_of_same_colour S H R x y p z hR (hAtom.trans hpz.symm)
  exact phase_rigid_triangle_zero S H C P b R p q z hpqR hqzR hpzR

/-- The SAME valid old bit is compatible with every genuine a-pair,
whenever a has one real monochromatic triangle. No extra
clique-extension hypothesis is hidden inside this statement. -/
theorem phase_loop_atom_same_bit_allowed
    {i : ι} (a : S.Atom i i)
    (hTri : S.Triangle a a a)
    (ε : Bit) (hε : P.validBit i ε) :
    P.allows (some a) ε ε := by
  refine ⟨hε,hε,?_⟩
  intro x y hcol hi hj R hR
  have hproof : hi = hj := Subsingleton.elim _ _
  cases hproof
  letI := Reached.groupoid H C (A := A)
  have hz : P.character.value R = 0 :=
    phase_loop_atom_zero S H C P ⟨i,hi⟩ a hTri R x y hR hcol
  rw [hz]
  exact (add_zero ε).symm

end
end CCO.CloneTupleGeometry
