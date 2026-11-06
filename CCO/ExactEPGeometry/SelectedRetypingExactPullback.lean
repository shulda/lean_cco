import CCO.ExactEPGeometry.SelectedSortRawInclusion
import CCO.ExactEPGeometry.SelectedSortExactRetyping

/-!
# Full exact pullback along the actual selected equivariant carriers

The graph of a genuine equivariant map between two named transitive
source carriers is ONE actual complete pair orbital, including equality.
Consequently endpoint pullback of a full exact relation is composition
with two genuine full exact graphs. After literal selected-word inclusion,
this proves reverse full exactness along every original-to-selected carrier
equivalence, not just along the canonically selected old parent.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

include H

/-- The whole graph of an actual equivariant map is a realized atomic
orbital of the same source; it is never a fictitious diversity identity. -/
theorem equivariantMapGraph_fullExact
    {i j : ι} (f : X i → X j)
    (hf : ∀ (g : G) (x : X i), f (g • x) = g • f x) :
    FullExact S (fun x y => f x = y) := by
  let a : X i := Classical.choice (S.nonemptySort i)
  have hGraph : S.rawAtomRel (S.colour a (f a)) = (fun x y => f x = y) := by
    funext x y
    apply propext
    constructor
    · intro h
      obtain ⟨g,hgx,hgy⟩ := (S.pair_homogeneous_of_homogeneous H) a x (f a) y h.symm
      exact (congrArg f hgx).symm.trans ((hf g a).trans hgy)
    · intro h
      obtain ⟨g,hgx⟩ := S.original_sort_transitive_of_homogeneous H i a x
      have hgy : g • f a = y := (hf g a).symm.trans ((congrArg f hgx).trans h)
      have hc := S.colourInvariant_of_homogeneous H g a (f a)
      change S.colour x y = S.colour a (f a)
      simpa only [hgx,hgy] using hc
  rw [←hGraph]
  exact fullExact_actual_atom S a (f a)

/-- Pullback along actual equivariant endpoint maps is full RAW exact,
by composition with their exact graphs in the SAME source calculus. -/
theorem equivariantEndpoints_fullExact_pullback
    (C : ExactCalculus S) {i j k l : ι}
    (f : X i → X k) (g : X j → X l)
    (hf : ∀ (s : G) (x : X i), f (s • x) = s • f x)
    (hg : ∀ (s : G) (y : X j), g (s • y) = s • g y)
    (R : TRel X k l) (hR : FullExact S R) :
    FullExact S (GroupActions.pullback f g R) := by
  have hComposite := C.comp
    (C.comp (equivariantMapGraph_fullExact S H f hf) hR)
    (fullExact_converse S (equivariantMapGraph_fullExact S H g hg))
  have hEq : TRel.comp (TRel.comp (fun x y => f x = y) R)
      (TRel.converse (fun x y => g x = y)) = GroupActions.pullback f g R := by
    funext x y
    apply propext
    constructor
    · rintro ⟨b,⟨a,hfa,hR⟩,hgb⟩
      change R (f x) (g y)
      exact hfa.symm ▸ hgb.symm ▸ hR
    · intro h
      exact ⟨g y,⟨f x,rfl,h⟩,rfl⟩
  exact hEq ▸ hComposite

variable {κ : Type u} [Fintype κ] {σ : κ ↪ ι}

/-- Reverse FULL exactness from the selected source at ANY original
endpoint sorts, using its real equivariant carrier maps and old CCO
calculus. Selected RAW words are first included literally; no arbitrary
mixed quotient reverse descent or sort-deletion assumption is made. -/
theorem SelectedRetyping.pullbackFullExact
    (D : SelectedRetyping (X := X) σ (G := G)) (C : ExactCalculus S)
    {i j : ι}
    (R : TRel (fun k => X (σ k)) (D.target i) (D.target j))
    (hR : FullExact (selectedSortAtomicSource S σ) R) :
    FullExact S (GroupActions.pullback (D.pointEquiv i) (D.pointEquiv j) R) :=
  equivariantEndpoints_fullExact_pullback S H C
    (D.pointEquiv i) (D.pointEquiv j) (D.equivariant i) (D.equivariant j) R
    (selectedSortFullExact_inclusion S σ R hR)

end
end CCO.ExactEPGeometry
