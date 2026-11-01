import CCO.APCharacter.Towers.CurrentSource

/-!
# B062 C67: genuine restriction of finite named source sorts

A source with an actual finite complete orbital language is restricted
along an INJECTIVE selection of its named sorts, keeping its original
points, binary colours and original group action literally unchanged
on those sorts. No new binary atom or imaginary point is created.

The actual finite tuple homogeneity and semantic homomorphic simple-cycle
CCO of this full SUBLANGUAGE are proved by translating its finite
diagrams to the original source and back. The original homomorphism
may identify nonadjacent formal vertices, exactly as CCO permits.
Ordinary AP/JEP follow from the inherited homogeneous source; SAP is
not assumed. The result works for finite sources and empty sort sets.

This lemma is necessary for selecting ONE actual occupied current parent
per E-occupancy class AFTER applying the full typed simultaneous exact
quotient provider to all current parent sorts. It does not attempt
reverse exact-word descent into a sort-restricted language.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

variable {ι κ : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable [Fintype κ] (σ : κ ↪ ι)

/-- Actual tagged-point inclusion along an injective selection of
named sorts, with precisely the same underlying real point. -/
include S in
def selectedSortPoint (p : Sigma (fun k : κ => X (σ k))) : Sigma X :=
  ⟨σ p.1, p.2⟩

theorem selectedSortPoint_injective :
    Function.Injective (selectedSortPoint S σ) := by
  rintro ⟨k,x⟩ ⟨l,y⟩ h
  have hk : k = l := σ.injective (congrArg Sigma.fst h)
  subst l
  have hxy : x = y := by
    simpa only [selectedSortPoint, Sigma.mk.injEq, heq_eq_eq,
      true_and] using h
  exact congrArg (Sigma.mk k) hxy

/-- Exact binary palette of the genuine selected named sorts:
no additional colour distinction or fictitious diagonal. -/
include S in
def selectedSortAtomicSource :
    AtomicSource.{u,v,w} κ (fun k => X (σ k)) := by
  refine {
    Atom := fun k l => S.Atom (σ k) (σ l)
    finiteSort := inferInstance
    finiteAtom := fun k l => S.finiteAtom (σ k) (σ l)
    nonemptySort := fun k => S.nonemptySort (σ k)
    conv := fun a => S.conv a
    conv_invol := fun a => S.conv_invol a
    symmetricLoop := fun a => S.symmetricLoop a
    colour := fun x y => S.colour x y
    colour_none_iff := ?_
    colour_swap := ?_
    realized := ?_
  }
  · intro k l x y
    constructor
    · intro hc
      have hOld : (⟨σ k,x⟩ : Sigma X) = ⟨σ l,y⟩ :=
        (S.colour_none_iff x y).mp hc
      have hk : k = l := σ.injective (congrArg Sigma.fst hOld)
      subst l
      have hxy : x = y := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hOld
      exact congrArg (Sigma.mk k) hxy
    · intro h
      have hOld : (⟨σ k,x⟩ : Sigma X) = ⟨σ l,y⟩ :=
        congrArg (selectedSortPoint S σ) h
      exact (S.colour_none_iff x y).mpr hOld
  · intro k l x y a
    exact S.colour_swap x y a
  · intro k l a
    exact S.realized a

/-- Reindex the ENTIRE actual tagged optional pair colour along the
selected named-sort embedding. The old and new point pairs are
unchanged, including original logical identity. -/
def selectedSortTaggedColour
    (c : Σ k : κ, Σ l : κ, Option (S.Atom (σ k) (σ l))) :
    Σ i : ι, Σ j : ι, Option (S.Atom i j) :=
  ⟨σ c.1, σ c.2.1, c.2.2⟩

theorem selectedSortTaggedColour_spec
    (p q : Sigma (fun k : κ => X (σ k))) :
    selectedSortTaggedColour S σ
      (taggedColour (selectedSortAtomicSource S σ) p q) =
      taggedColour S (selectedSortPoint S σ p)
        (selectedSortPoint S σ q) := rfl

/-- The ACTUAL original group still gives finite tuple homogeneity on
the selected named-sort family. The proof lifts real tagged tuples into
the original source, uses its TRUE finite extension, and pulls back
through the INJECTIVE sort embedding. -/
theorem selectedSortHomogeneous
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) :
    HomogeneousSource (selectedSortAtomicSource S σ) G := by
  refine ⟨?_,?_,?_⟩
  · intro g p
    cases p
    rfl
  · intro g p q
    cases p with
    | mk k x =>
      cases q with
      | mk l y =>
        have h := S.colourInvariant_of_homogeneous H g x y
        change (⟨k,l,S.colour (g • x) (g • y)⟩ :
          Σ k : κ, Σ l : κ, Option (S.Atom (σ k) (σ l))) =
          ⟨k,l,S.colour x y⟩
        rw [h]
  · intro V _ source target hColour
    let left : V → Sigma X :=
      fun a => selectedSortPoint S σ (source a)
    let right : V → Sigma X :=
      fun a => selectedSortPoint S σ (target a)
    have hOld : ∀ a b, taggedColour S (left a) (left b) =
        taggedColour S (right a) (right b) := by
      intro a b
      exact congrArg (selectedSortTaggedColour S σ) (hColour a b)
    obtain ⟨g,hg⟩ := H.extends_finite_diagram left right hOld
    refine ⟨g,?_⟩
    intro a
    apply selectedSortPoint_injective S σ
    exact hg a

/-- Homomorphic simple-cycle completion is inherited by the ACTUAL
selected sort sublanguage: the old diagram has the same formal
vertices and the same specified edges, merely with renamed sorts.
No extra injective CCO or SAP premise is used. -/
theorem selectedSortSemanticCCO
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    SemanticCCO.{u,v,max u v,w} (selectedSortAtomicSource S σ) := by
  intro V D hCycles
  let Dold : PartialDiagram S V := {
    finite_type := D.finite_type
    vertexSort := fun a => σ (D.vertexSort a)
    edge := fun a b h => D.edge a b h
    edge_reverse := fun a b h c => D.edge_reverse a b h c
  }
  have hOldCycles : ∀ C : SimpleCycle Dold, CycleHom C := by
    intro C
    exact hCycles C
  obtain ⟨f⟩ := cco V Dold hOldCycles
  exact ⟨{
    point := f.point
    preserves_edge := fun a b h c hc => f.preserves_edge a b h c hc
  }⟩

/-- The genuine selected sort subsource is a COMPLETE
CurrentSource: real finite orbital palette, original action,
finite-tuple homogeneity, countable carriers and source HOM CCO.
We do not treat a sublanguage as a new hypothetical provider. -/
def selectedSortCurrentSource
    (B : CurrentSource.{u,v,w,t}) {K : Type u} [Fintype K]
    (f : K ↪ B.Sorts) :
    CurrentSource.{u,v,w,t} := by
  letI : ∀ k : K, MulAction B.G (B.Point (f k)) :=
    fun k => B.action (f k)
  exact {
    Sorts := K
    Point := fun k => B.Point (f k)
    source := selectedSortAtomicSource B.source f
    G := B.G
    group := B.group
    action := fun k => B.action (f k)
    homogeneous := selectedSortHomogeneous B.source f B.homogeneous
    countable := fun k => B.countable (f k)
    cco := selectedSortSemanticCCO B.source f B.cco
  }

end
end CCO.ExactEPGeometry
