import CCO.FiniteLift.Kernel
import CCO.FiniteLift.ClosureOrbit

/-! The original homogeneous witness group and the FULL original orbital
structure group have the same finite-base stabilizer orbits. This does not
identify a quotient full automorphism group with any old ambient image. -/

universe v w t
namespace CCO.FiniteLift
open Owners.Product
variable {A : Type v} {G : Type t} [Group G] [MulAction G A]
variable (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable (H : HomogeneousSource S G)
include H

/-- Every finite restriction of a FULL original automorphism is realized by
one element of the homogeneous original witness group. -/
theorem full_finite_lift (B : Set A) (finiteB : B.Finite) (β : FullAut G A) :
    ∃ g : G, ∀ a ∈ B, g • a = β.val a := by
  letI : Finite B := finiteB.to_subtype
  let src : B → Sigma (fun _ : Unit => A) := fun a => ⟨(), a.val⟩
  let dst : B → Sigma (fun _ : Unit => A) := fun a => ⟨(), β.val a.val⟩
  have hp : ∀ a b, taggedColour S (src a) (src b) = taggedColour S (dst a) (dst b) := by
    intro a b
    obtain ⟨g, hg, hg'⟩ := orbitalAut_pair β a.val b.val
    have he := S.colourInvariant_of_homogeneous H (i := ()) (j := ()) g a.val b.val
    change g • a.val = β.val a.val at hg
    change g • b.val = β.val b.val at hg'
    rw [hg, hg'] at he
    exact congrArg (fun c => (⟨(), (), c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j))) he.symm
  obtain ⟨g, hg⟩ := H.extends_finite_diagram src dst hp
  refine ⟨g, ?_⟩
  intro a ha
  have he := hg (⟨a, ha⟩ : B)
  simpa only [src, dst, Sigma.smul_mk, Sigma.mk.injEq, heq_eq_eq, true_and] using he

theorem orbitSet_full_eq (B : Set A) (finiteB : B.Finite) (x : A) :
    orbitSet (FullAut G A) B x = orbitSet G B x := by
  ext y
  constructor
  · rintro ⟨β, hβ, hβx⟩
    obtain ⟨g, hg⟩ := full_finite_lift S H (insert x B) (finiteB.insert x) β
    refine ⟨g, ?_, ?_⟩
    · intro a ha
      exact (hg a (Set.mem_insert_of_mem x ha)).trans (hβ a ha)
    · exact (hg x (Set.mem_insert x B)).trans hβx
  · rintro ⟨g, hg, hgy⟩
    exact ⟨ambientAut g, hg, hgy⟩

/-- Actual original acl may therefore be written with the accepted G-orbit
API while retaining its precise FULL-structure-stabilizer meaning. -/
theorem aclSet_full_eq (B : Set A) (finiteB : B.Finite) :
    aclSet (FullAut G A) B = aclSet G B := by
  ext x
  change (orbitSet (FullAut G A) B x).Finite ↔ (orbitSet G B x).Finite
  rw [orbitSet_full_eq S H B finiteB x]

end CCO.FiniteLift
