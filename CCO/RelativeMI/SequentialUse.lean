import CCO.RelativeMI.OrbitWitness

/-! Two prescribed extensions and a selected-root transport are used on
ONE actual original-language witness. Composition retains the canonical
coarse quotient action; no coherent choice of extensions is assumed. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization Owners.Product Owners.Provider RawExact
variable {M : Type v} {S : AtomicSource.{0,v,w} Unit (fun _ => M)}
variable {G : Type t} [Group G] [MulAction G M] {H : HomogeneousSource S G}
variable {J : ColourEq S ()} {A0 : Finset M} {B : Finset (Coarse S H J)}
variable {overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B}
variable {safe : Set (S.Atom () ())}
local instance sequentialCoarseAction : MulAction G (Coarse S H J) := originalQuotientAction S H J

namespace OriginalWitness

/-- The literal original seed point, in the very same actual carrier. -/
def sourcePoint (W : OriginalWitness S H J A0 B overA0 safe) (a : ↥A0) : W.carrier :=
  ⟨a.val,W.contains ⟨a.val,a.property,(finitePacket S H).val.refl _⟩⟩

@[simp] theorem sourcePoint_val (W : OriginalWitness S H J A0 B overA0 safe) (a : ↥A0) :
    (W.sourcePoint a).val = a.val := rfl

/-- The same finite actual witness supports two extensions in succession
and an independent rooted transport. Their composition acts on ALL coarse
owners by the indicated product, and follows the prescribed chain point. -/
theorem sequential_and_rooted (W : OriginalWitness S H J A0 B overA0 safe)
    (r1 r2 : OriginalRequest S H J A0 B overA0)
    (x : r1.part.domain) (y : r2.part.domain) (hxy : r1.part.map x = y.val)
    (Z : Set W.carrier) (unsafeZ : UnsafeSet S (Subtype.val : W.carrier → M) safe Z)
    (z : W.carrier) (hz : z ∈ Z) :
    let q := (inducedQuotient (coarseOwner S H J) (fun _ _ => rfl)
      W.carrier (↑B) W.over W.onto).action
    ∃ β1 β2 β0 : OrbitalAut G M (Subtype.val : W.carrier → M),
      (q β1 = r1.owner ∧ ∀ a : r1.part.domain,
        (β1.val (W.sourcePoint a.val)).val = (r1.part.map a).val) ∧
      (q β2 = r2.owner ∧ ∀ a : r2.part.domain,
        (β2.val (W.sourcePoint a.val)).val = (r2.part.map a).val) ∧
      q (β2*β1) = r2.owner*r1.owner ∧
      ((β2*β1).val (W.sourcePoint x.val)).val = (r2.part.map y).val ∧
      (∀ a ∈ Z, (β0.val a).val ∈ RealClosure.Bounds.packetClosure S H A0) ∧
      (β0.val z).val ∈ A0 := by
  let q : OrbitalAut G M (Subtype.val : W.carrier → M) →*
      OrbitalAut G (Coarse S H J) (Subtype.val : ↥B → Coarse S H J) :=
    (inducedQuotient (coarseOwner S H J) (fun _ _ => rfl)
    W.carrier (↑B) W.over W.onto).action
  obtain ⟨β1,hβ1,h1⟩ := W.extensions r1
  obtain ⟨β2,hβ2,h2⟩ := W.extensions r2
  obtain ⟨β0,h0,hz0⟩ := W.rooted Z unsafeZ z hz
  have hpoint : β1.val (W.sourcePoint x.val) = W.sourcePoint y.val := by
    apply Subtype.ext
    exact (h1 x).trans (congrArg Subtype.val hxy)
  have howner : q (β2*β1) = r2.owner*r1.owner := by
    rw [map_mul,hβ2,hβ1]
  refine ⟨β1,β2,β0,⟨hβ1,h1⟩,⟨hβ2,h2⟩,howner,?_,h0,hz0⟩
  change (β2.val (β1.val (W.sourcePoint x.val))).val = _
  rw [hpoint]
  exact h2 y
end OriginalWitness
end
end CCO.RelativeMI
