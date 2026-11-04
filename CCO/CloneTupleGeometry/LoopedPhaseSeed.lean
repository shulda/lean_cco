import CCO.CloneTupleGeometry.LoopedPhaseZero
import CCO.APCharacter.SeedSource

/-!
# B060 N03: a real looped monochromatic seed extends globally

A genuine current SourcePhase is used, together with its exact old
character masks and the proved B047 finite free-action seed extension.
If the old source realizes a looped (a,a,a) triangle, assigning the same
valid character bit to every point of ANY finite monochromatic a-clique
is compatible, including the repeated-point diagonal. Hence these
simultaneous prescriptions extend to ONE actual global marking.

This is not a proof that such cliques have arbitrary size, nor that
the resulting marked child contains infinitely many different owners.
Those are separate B060 N03 obligations.
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

/-- B060 N03 C12–C20, actual finite compatible seed for one looped atom.
For any finite indexed monochromatic family (possibly empty), all
prescribed copies of one valid bit arise from a SINGLE global character
marking of the original homogeneous source. No arbitrary unary age
or quotient phase condition is substituted for the B047 extension. -/
theorem phase_loop_mono_seed_global
    (b : Reached S A) (a : S.Atom b.val b.val)
    (hTri : S.Triangle a a a)
    (ε : Bit) (hε : P.validBit b.val ε)
    {V : Type (max u v)} [Finite V]
    (points : V → X b.val)
    (hmono : ∀ x y : V, x ≠ y →
      S.colour (points x) (points y) = some a) :
    ∃ mark : Sigma X → Bit,
      P.masks.GlobalMarking mark ∧
        ∀ x : V, mark ⟨b.val,points x⟩ = ε := by
  have hlocal : ∀ x y : V,
      P.allows (S.colour (points x) (points y)) ε ε := by
    intro x y
    by_cases hxy : x = y
    · subst y
      have hc : S.colour (points x) (points x) = none :=
        (S.colour_none_iff (points x) (points x)).mpr rfl
      rw [hc]
      exact (P.allows_identity b.val ε ε).mpr ⟨rfl,hε⟩
    · rw [hmono x y hxy]
      exact phase_loop_atom_same_bit_allowed S H C P a hTri ε hε
  have hseed : P.masks.FiniteSeedExtension := P.finite_seed_extension
  exact hseed (fun _ : V => b.val) points
    (fun _ : V => ε) (fun _ => hε) hlocal

end
end CCO.CloneTupleGeometry
