import CCO.CloneTupleGeometry.LoopedPhaseSeed
import CCO.APCharacter.SourceAge.Identification

/-!
# B060 N03: finite looped cliques occur in the ACTUAL marked Fraisse limit

For one genuine B047 SourcePhase and a real (a,a,a) triangle, any finite
injective old a-monochromatic configuration admits a constant VALID bit.
By the actual Age.Legal and Age.embed_realized source the whole marked
configuration embeds into the genuine homogeneous marked limit, retaining
both its child bits and all named fine pair colours.

No arbitrary expanded Fraisse limit, unproved source homogeneity, or
identification of the marked limit with a single global marking is assumed.
Existence of arbitrarily large *owner* monochromatic cliques, owner
separation in terminal sorts, and iteration remain open.
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

/-- An actual finite old monochromatic clique, when its atom admits a
real loop triangle, embeds with ONE prescribed valid child bit into the
same B047 marked homogeneous limit. The full colours are carried by
the accepted actual-age embedding, even for empty/singleton families. -/
theorem phase_loop_mono_marked_age_embeds
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (b : Reached S A) (a : S.Atom b.val b.val)
    (hTri : S.Triangle a a a)
    (ε : Bit) (hε : P.validBit b.val ε)
    (n : ℕ) (points : Fin n → X b.val)
    (hinj : Function.Injective points)
    (hmono : ∀ x y : Fin n, x ≠ y →
      S.colour (points x) (points y) = some a) :
    ∃ f : Fin n ↪ Age.Limit S H (P.completion_property cco),
      (∀ x : Fin n,
        (Age.ownerEquiv S).symm
          ((Age.limitCoding S H (P.completion_property cco)).table.owner (f x)) =
          (b.val,ε)) ∧
      (∀ x y : Fin n,
        (Age.limitCoding S H (P.completion_property cco)).table.colour (f x) (f y) =
          Age.colourEquiv S (taggedColour S
            (⟨b.val,points x⟩ : Sigma X)
            (⟨b.val,points y⟩ : Sigma X))) := by
  let old : Fin n → Sigma X := fun i => ⟨b.val,points i⟩
  have hOldInj : Function.Injective old := by
    intro x y h
    apply hinj
    have he : points x = points y := by
      simpa only [old,Sigma.mk.injEq,heq_eq_eq,true_and] using h
    exact he
  have hlegal : Age.Legal S P.masks old (fun _ : Fin n => ε) := by
    refine ⟨fun _ => hε,?_⟩
    intro x y
    change P.allows (S.colour (points x) (points y)) ε ε
    by_cases hxy : x = y
    · subst y
      have hc : S.colour (points x) (points x) = none :=
        (S.colour_none_iff (points x) (points x)).mpr rfl
      rw [hc]
      exact (P.allows_identity b.val ε ε).mpr ⟨rfl,hε⟩
    · rw [hmono x y hxy]
      exact phase_loop_atom_same_bit_allowed S H C P a hTri ε hε
  obtain ⟨f,howner,hcolour⟩ :=
    Age.embed_realized S H (P.completion_property cco)
      old (fun _ : Fin n => ε) hOldInj hlegal
  refine ⟨f,?_,?_⟩
  · intro x
    have h := congrArg (Age.ownerEquiv S).symm (howner x)
    simpa only [old,Equiv.symm_apply_apply] using h
  · intro x y
    exact hcolour x y

end
end CCO.CloneTupleGeometry
