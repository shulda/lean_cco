import CCO.RigidGroupoid.Phase.ActualPhase
import Mathlib.Data.Finset.Image

/-! Finite indexed prescribed bits descend to the actual quotient-point set.
The identity arrow proves consistency when different indices name one point. -/
universe u v w z t
namespace CCO.APCharacter
open CategoryTheory RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section

namespace IndexedSeeds
variable {J : Type u} [Groupoid.{v} J] (F : J ⥤ Type w) (χ : Abstract.Character J)

def PairCompatible (p q : Abstract.Point F) (a b : Abstract.Bit) : Prop :=
  ∀ R : p.1 ⟶ q.1, F.map R p.2 = q.2 → b = a + χ.value R

theorem same_point_bits (p : Abstract.Point F) (a b : Abstract.Bit)
    (h : PairCompatible F χ p p a b) : b = a := by
  have he := h (𝟙 p.1) (F.map_id_apply p.1 p.2)
  simpa only [χ.map_id,add_zero] using he

theorem extension_iff (free : Abstract.Free F) {I : Type z} [Finite I]
    (p : I → Abstract.Point F) (bits : I → Abstract.Bit) :
    (∃ mark, Abstract.IsMarking F χ mark ∧ ∀ i, mark (p i) = bits i) ↔
      ∀ i j, PairCompatible F χ (p i) (p j) (bits i) (bits j) := by
  classical
  letI := Fintype.ofFinite I
  constructor
  · rintro ⟨mark,hm,hbits⟩ i j R hR
    have hpt : (⟨(p j).1,F.map R (p i).2⟩ : Abstract.Point F) = p j :=
      congrArg (Sigma.mk (p j).1) hR
    have h := hm R (p i).2
    rw [hpt,hbits,hbits] at h
    exact h
  · intro tests
    let s : Finset (Abstract.Point F) := Finset.univ.image p
    have pre (q : s) : ∃ i, p i = q.val := by
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp q.property
      exact ⟨i,hi⟩
    let rep : s → I := fun q => Classical.choose (pre q)
    have rep_spec (q : s) : p (rep q) = q.val := Classical.choose_spec (pre q)
    let ε : s → Abstract.Bit := fun q => bits (rep q)
    have compatible : ∀ a b : s, PairCompatible F χ a.val b.val (ε a) (ε b) := by
      intro a b
      have h := tests (rep a) (rep b)
      rw [rep_spec,rep_spec] at h
      exact h
    obtain ⟨mark,hm,hmark⟩ :=
      (Abstract.finite_seed_extension_iff F free χ s ε).mpr compatible
    refine ⟨mark,hm,?_⟩
    intro i
    let q : s := ⟨p i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
    have h := tests i (rep q)
    rw [rep_spec] at h
    have he : bits (rep q) = bits i := same_point_bits F χ (p i) _ _ h
    exact (hmark q).trans he

end IndexedSeeds

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)

/-- Indexed form of the accepted actual I10 provider, retaining repeated
quotient points, all original arrow tests, and a SINGLE global marking. -/
theorem indexed_actual_seed_extension_iff {r : ι} (A : Kernel S r)
    (χ : letI := Reached.groupoid H C (A := A); Abstract.Character (Reached S A))
    {I : Type z} [Finite I] (p : I → Reached.Point H C A) (bits : I → Abstract.Bit) :
    letI := Reached.groupoid H C (A := A)
    (∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark ∧
      ∀ i, mark (p i) = bits i) ↔
    ∀ i j (R : Arrow S (Reached.kernel H C (p i).1) (Reached.kernel H C (p j).1)),
      R.quotientMap H (p i).2 = (p j).2 → bits j = bits i + χ.value R := by
  letI := Reached.groupoid H C (A := A)
  exact IndexedSeeds.extension_iff (Reached.pointFunctor H C A) χ
    (actual_action_free S H C A) p bits

end
end CCO.APCharacter
