import CCO.RigidGroupoid.Geometry.ProjectedKernels
import CCO.RigidGroupoid.Geometry.Quotient.Blocks

/-! Exact bridge descent uses EXACT PROJECTED GATES as an explicit hypothesis.
Its proof factors the bridge through ONE actual quotient atomic colour, then
uses the genuinely proved quotient convolution. The reverse uses only safe
full exact pullback. No arbitrary mixed-sort exact descent is inferred. -/

universe u v w q r t
namespace CCO.RigidGroupoid.Geometry.Projected
open RawExact
variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, MulAction G (Q i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (π : ∀ i, X i → Q i) (surjπ : ∀ i, Function.Surjective (π i))
variable (equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀ i, NonemptyExact S i i)
variable (hE : ∀ i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')
variable (A : ∀ i, Kernel S i)
variable (nested : ∀ i x y, π i x = π i y → (A i).rel x y)
variable (projectedExact : ∀ i,
  FullExact T ((A i).projectedSetoid (π i) (surjπ i) (nested i)).r)

include surjπ in
private theorem pullback_comp_typed {i j k : ι} (D : TRel Q i j) (F : TRel Q j k) :
    GroupActions.pullback (π i) (π k) (TRel.comp D F) =
      TRel.comp (GroupActions.pullback (π i) (π j) D) (GroupActions.pullback (π j) (π k) F) :=
  ExactCRT.pullback_comp (π i) (π j) (π k) (surjπ j) D F

def gate (i : ι) : Kernel T i :=
  (A i).projectedKernel T (π i) (surjπ i) (nested i) (projectedExact i)

theorem gate_pullback (i : ι) :
    GroupActions.pullback (π i) (π i) (gate S T π surjπ A nested projectedExact i).rel = (A i).rel :=
  (A i).projected_pullback (π i) (surjπ i) (nested i)

include H equivπ E hE hT surjπ nested projectedExact

/-- The exact bridge image is literally a product of the two projected gates
and ONE actual quotient atomic letter, even if the old colour projects to Id.
-/
theorem image_rectangular {i j : ι} (R : Arrow S (A i) (A j))
    {x : X i} {y : X j} (hxy : R.rel x y) :
    Quotient.image (π i) (π j) R.rel =
      TRel.comp (TRel.comp (gate S T π surjπ A nested projectedExact i).rel
        (T.rawAtomRel (T.colour (π i x) (π j y))))
        (gate S T π surjπ A nested projectedExact j).rel := by
  apply ExactCRT.pullback_injective (π i) (π j) (surjπ i) (surjπ j)
  rw [R.image_pullback_nested (π i) (π j) (nested i) (nested j)]
  rw [pullback_comp_typed π surjπ,
    pullback_comp_typed π surjπ]
  rw [gate_pullback,gate_pullback,
    ExactCRT.quotient_pair_block S T H π equivπ E hE hT x y,R.rectangular H hxy]
  have hi : TRel.comp (A i).rel (evaluate S (E i).words) = (A i).rel := by
    rw [← hE i]
    exact (A i).right_kernel (π i) (nested i)
  have hj : TRel.comp (evaluate S (E j).words) (A j).rel = (A j).rel := by
    rw [← hE j]
    exact (A j).left_kernel (π j) (nested j)
  dsimp only [saturate]
  simp only [← TRel.comp_assoc]
  rw [hi,TRel.comp_assoc (TRel.comp (A i).rel (S.rawAtomRel (S.colour x y)))
    (evaluate S (E j).words) (A j).rel,hj]

include cco
theorem image_fullExact {i j : ι} (R : Arrow S (A i) (A j)) :
    FullExact T (Quotient.image (π i) (π j) R.rel) := by
  obtain ⟨x,y,hxy⟩ := R.exact.nonempty S
  rw [image_rectangular S T H π surjπ equivπ E hE hT A nested projectedExact R hxy]
  let Cq := Quotient.quotientExactCalculus S T H cco π surjπ equivπ E hE hT
  exact Cq.comp (Cq.comp (projectedExact i) (fullExact_actual_atom T (π i x) (π j y)))
    (projectedExact j)

noncomputable def push {i j : ι} (R : Arrow S (A i) (A j)) :
    Arrow T (gate S T π surjπ A nested projectedExact i) (gate S T π surjπ A nested projectedExact j) where
  rel := Quotient.image (π i) (π j) R.rel
  exact := image_fullExact S T H cco π surjπ equivπ E hE hT A nested projectedExact R
  left := by
    apply ExactCRT.pullback_injective (π i) (π j) (surjπ i) (surjπ j)
    rw [pullback_comp_typed π surjπ,gate_pullback,
      R.image_pullback_nested (π i) (π j) (nested i) (nested j),R.left]
  right := by
    apply ExactCRT.pullback_injective (π i) (π j) (surjπ i) (surjπ j)
    rw [pullback_comp_typed π surjπ,gate_pullback,
      R.image_pullback_nested (π i) (π j) (nested i) (nested j),R.right]
  source := by
    apply ExactCRT.pullback_injective (π i) (π i) (surjπ i) (surjπ i)
    rw [pullback_comp_typed π surjπ,gate_pullback]
    change TRel.comp _ (TRel.converse (GroupActions.pullback (π i) (π j)
      (Quotient.image (π i) (π j) R.rel))) = _
    rw [R.image_pullback_nested (π i) (π j) (nested i) (nested j),R.source]
  target := by
    apply ExactCRT.pullback_injective (π j) (π j) (surjπ j) (surjπ j)
    rw [pullback_comp_typed π surjπ,gate_pullback]
    change TRel.comp (TRel.converse (GroupActions.pullback (π i) (π j)
      (Quotient.image (π i) (π j) R.rel))) _ = _
    rw [R.image_pullback_nested (π i) (π j) (nested i) (nested j),R.target]

noncomputable def pull {i j : ι}
    (R : Arrow T (gate S T π surjπ A nested projectedExact i) (gate S T π surjπ A nested projectedExact j)) :
    Arrow S (A i) (A j) where
  rel := GroupActions.pullback (π i) (π j) R.rel
  exact := Quotient.fullExactPullback S T H cco π surjπ equivπ E hE hT R.exact
  left := by
    have h := congrArg (GroupActions.pullback (π i) (π j)) R.left
    rw [pullback_comp_typed π surjπ,gate_pullback] at h
    exact h
  right := by
    have h := congrArg (GroupActions.pullback (π i) (π j)) R.right
    rw [pullback_comp_typed π surjπ,gate_pullback] at h
    exact h
  source := by
    have h := congrArg (GroupActions.pullback (π i) (π i)) R.source
    rw [pullback_comp_typed π surjπ,gate_pullback] at h
    exact h
  target := by
    have h := congrArg (GroupActions.pullback (π j) (π j)) R.target
    rw [pullback_comp_typed π surjπ,gate_pullback] at h
    exact h

noncomputable def arrowEquiv (i j : ι) :
    Arrow S (A i) (A j) ≃
      Arrow T (gate S T π surjπ A nested projectedExact i) (gate S T π surjπ A nested projectedExact j) where
  toFun := push S T H cco π surjπ equivπ E hE hT A nested projectedExact
  invFun := pull S T H cco π surjπ equivπ E hE hT A nested projectedExact
  left_inv R := Arrow.ext (R.image_pullback_nested (π i) (π j) (nested i) (nested j))
  right_inv R := Arrow.ext (Quotient.image_pullback (π i) (π j) (surjπ i) (surjπ j) R.rel)

theorem push_id (i : ι) :
    push S T H cco π surjπ equivπ E hE hT A nested projectedExact (Arrow.id (A i)) =
      Arrow.id (gate S T π surjπ A nested projectedExact i) := Arrow.ext rfl

theorem push_inv {i j : ι} (R : Arrow S (A i) (A j)) :
    push S T H cco π surjπ equivπ E hE hT A nested projectedExact R.inv =
      (push S T H cco π surjπ equivπ E hE hT A nested projectedExact R).inv :=
  Arrow.ext (Quotient.image_converse (π i) (π j) R.rel)

theorem push_comp (C : ExactCalculus S) {i j k : ι}
    (R : Arrow S (A i) (A j)) (U : Arrow S (A j) (A k)) :
    push S T H cco π surjπ equivπ E hE hT A nested projectedExact (R.comp C U) =
      (push S T H cco π surjπ equivπ E hE hT A nested projectedExact R).comp
        (Quotient.quotientExactCalculus S T H cco π surjπ equivπ E hE hT)
        (push S T H cco π surjπ equivπ E hE hT A nested projectedExact U) :=
  Arrow.ext (Quotient.image_comp (π i) (π j) (π k) (surjπ i) (surjπ j) (surjπ k) R.rel U.rel
    (R.nested_bisaturated (π i) (π j) (nested i) (nested j))
    (U.nested_bisaturated (π j) (π k) (nested j) (nested k)))

end CCO.RigidGroupoid.Geometry.Projected

namespace CCO.RigidGroupoid.Geometry

/-- A groupoid isomorphism over the unchanged named object indices. The
hom-sets are ACTUAL represented exact bridges; bijectivity and all three
groupoid operations are retained, not merely a numerical correspondence. -/
structure BridgeGroupoidIso {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
    (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
    (A : ∀ i, Kernel S i) (B : ∀ i, Kernel T i)
    (C : ExactCalculus S) (D : ExactCalculus T) where
  homEquiv : ∀ i j, Arrow S (A i) (A j) ≃ Arrow T (B i) (B j)
  map_id : ∀ i, homEquiv i i (Arrow.id (A i)) = Arrow.id (B i)
  map_inv : ∀ {i j} (R : Arrow S (A i) (A j)),
    homEquiv j i R.inv = (homEquiv i j R).inv
  map_comp : ∀ {i j k} (R : Arrow S (A i) (A j)) (U : Arrow S (A j) (A k)),
    homEquiv i k (R.comp C U) = (homEquiv i j R).comp D (homEquiv j k U)

namespace Projected
open RawExact
variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, MulAction G (Q i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (π : ∀ i, X i → Q i) (surjπ : ∀ i, Function.Surjective (π i))
variable (equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀ i, NonemptyExact S i i)
variable (hE : ∀ i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')
variable (A : ∀ i, Kernel S i)
variable (nested : ∀ i x y, π i x = π i y → (A i).rel x y)
variable (projectedExact : ∀ i,
  FullExact T ((A i).projectedSetoid (π i) (surjπ i) (nested i)).r)

noncomputable def groupoidIso (C : ExactCalculus S) :
    BridgeGroupoidIso S T A (gate S T π surjπ A nested projectedExact) C
      (Quotient.quotientExactCalculus S T H cco π surjπ equivπ E hE hT) where
  homEquiv := arrowEquiv S T H cco π surjπ equivπ E hE hT A nested projectedExact
  map_id := push_id S T H cco π surjπ equivπ E hE hT A nested projectedExact
  map_inv := push_inv S T H cco π surjπ equivπ E hE hT A nested projectedExact
  map_comp := push_comp S T H cco π surjπ equivπ E hE hT A nested projectedExact C

end Projected
end CCO.RigidGroupoid.Geometry
