import CCO.ExactEPGeometry.OriginalGlobalEclassHistoryPairs
import CCO.ExactEPGeometry.OriginalCurrentExactColourInvariance

/-!
# B062 C96: original E-saturated old orbital blocks are invariant on fine charts

For ANY original-current B atomic pair colour, the TRUE E;D;E
saturation is preserved under B's actual complete pair orbital
homogeneity. The original E was proved B.G-invariant at the prefix.
The E-saturated old pair BLOCK is therefore determined by the full
old B colour, including logical equality and all current named sorts.

This is a necessary OLD pair-block piece of the full C96 new
quotient age comparison, not a claim about NEW marked atom names,
quotient SAP, group sections, or a future quotient tower.
-/

universe u v w t z
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The literal simultaneous action on tagged current source
points, preserving their actual unary sort. -/
def originalCurrentTaggedMove
    (B : CurrentSource.{u,v,w,t}) (g : B.G)
    (p : Sigma B.Point) : Sigma B.Point :=
  ⟨p.1, g • p.2⟩

/-- The pulled-back ORIGINAL global E is invariant under each
actual current automorphism; no automorphism-group section
or extra quotient invariance assumption is needed. -/
theorem originalCurrentExactE_move
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (g : B.G) (p q : Sigma B.Point)
    (h : (currentOriginalExactSetoid A B P base hOne E).r p q) :
    (currentOriginalExactSetoid A B P base hOne E).r
      (originalCurrentTaggedMove B g p)
      (originalCurrentTaggedMove B g q) := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  exact (originalExactGlobalRelation_prefix_invariant
    A B P base hOne E) g x y h

/-- E-saturation of ANY actual-current group-invariant binary
predicate remains invariant. No arbitrary predicate D is presumed
definable or to be an atomic source orbital. -/
theorem originalCurrentExactSaturation_move
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (D : Sigma B.Point → Sigma B.Point → Prop)
    (hD : ∀ (g : B.G) (p q : Sigma B.Point),
      D p q → D (originalCurrentTaggedMove B g p)
        (originalCurrentTaggedMove B g q))
    (g : B.G) (p q : Sigma B.Point)
    (h : setoidSaturation
      (currentOriginalExactSetoid A B P base hOne E) D p q) :
    setoidSaturation
      (currentOriginalExactSetoid A B P base hOne E) D
      (originalCurrentTaggedMove B g p)
      (originalCurrentTaggedMove B g q) := by
  obtain ⟨x,y,hpx,hxy,hyq⟩ := h
  exact ⟨originalCurrentTaggedMove B g x,
    originalCurrentTaggedMove B g y,
    originalCurrentExactE_move A B P base hOne E g p x hpx,
    hD g x y hxy,
    originalCurrentExactE_move A B P base hOne E g y q hyq⟩

/-- Saturated old pair-block membership is invariant under changing
a whole current PAIR within its COMPLETE actual atomic colour. -/
theorem originalCurrentExactSaturation_pairColour_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (D : Sigma B.Point → Sigma B.Point → Prop)
    (hD : ∀ (g : B.G) (p q : Sigma B.Point),
      D p q → D (originalCurrentTaggedMove B g p)
        (originalCurrentTaggedMove B g q))
    (i j : B.Sorts)
    (x x' : B.Point i) (y y' : B.Point j)
    (hColour : B.source.colour x y = B.source.colour x' y') :
    setoidSaturation (currentOriginalExactSetoid A B P base hOne E)
      D ⟨i,x⟩ ⟨j,y⟩ ↔
    setoidSaturation (currentOriginalExactSetoid A B P base hOne E)
      D ⟨i,x'⟩ ⟨j,y'⟩ := by
  constructor
  · intro h
    obtain ⟨g,hgx,hgy⟩ :=
      (B.source.pair_homogeneous_of_homogeneous B.homogeneous)
        x x' y y' hColour
    have hh := originalCurrentExactSaturation_move
      A B P base hOne E D hD g ⟨i,x⟩ ⟨j,y⟩ h
    simpa only [originalCurrentTaggedMove,hgx,hgy] using hh
  · intro h
    obtain ⟨g,hgx,hgy⟩ :=
      (B.source.pair_homogeneous_of_homogeneous B.homogeneous)
        x' x y' y hColour.symm
    have hh := originalCurrentExactSaturation_move
      A B P base hOne E D hD g ⟨i,x'⟩ ⟨j,y'⟩ h
    simpa only [originalCurrentTaggedMove,hgx,hgy] using hh

/-- The same statement with TRUE tagged current colours, including
different original/current unary parent names and literal diagonal. -/
theorem originalCurrentExactSaturation_taggedColour_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (D : Sigma B.Point → Sigma B.Point → Prop)
    (hD : ∀ (g : B.G) (p q : Sigma B.Point),
      D p q → D (originalCurrentTaggedMove B g p)
        (originalCurrentTaggedMove B g q))
    (p q p' q' : Sigma B.Point)
    (hColour : taggedColour B.source p q =
      taggedColour B.source p' q') :
    setoidSaturation (currentOriginalExactSetoid A B P base hOne E)
      D p q ↔
    setoidSaturation (currentOriginalExactSetoid A B P base hOne E)
      D p' q' := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  rcases p' with ⟨k,x'⟩
  rcases q' with ⟨l,y'⟩
  have hi : i = k :=
    congrArg (fun a : Σ i : B.Sorts,
      Σ j : B.Sorts, Option (B.source.Atom i j) => a.1) hColour
  have hj : j = l :=
    congrArg (fun a : Σ i : B.Sorts,
      Σ j : B.Sorts, Option (B.source.Atom i j) => a.2.1) hColour
  cases hi
  cases hj
  have hc : B.source.colour x y = B.source.colour x' y' := by
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and]
      using hColour
  exact originalCurrentExactSaturation_pairColour_iff
    A B P base hOne E D hD i j x x' y y' hc

/-- E;colour;E is the FULL actual original E-bisaturation of one
complete old B pair colour, not an arbitrary synthetic quotient atom. -/
def originalCurrentExactSaturatedColour
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (a : Age.Colour B.source) (p q : Sigma B.Point) : Prop :=
  setoidSaturation (currentOriginalExactSetoid A B P base hOne E)
    (fun x y => taggedColour B.source x y = a) p q

/-- Every genuine old E-saturated *atomic pair-colour block*
is preserved and reflected by any complete old tagged pair colour
equality, without supplying a quotient action or quotient SAP. -/
theorem originalCurrentExactSaturatedColour_taggedColour_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (a : Age.Colour B.source)
    (p q p' q' : Sigma B.Point)
    (hColour : taggedColour B.source p q =
      taggedColour B.source p' q') :
    originalCurrentExactSaturatedColour A B P base hOne E a p q ↔
    originalCurrentExactSaturatedColour A B P base hOne E a p' q' := by
  have hD : ∀ (g : B.G) (p q : Sigma B.Point),
      taggedColour B.source p q = a →
      taggedColour B.source
        (originalCurrentTaggedMove B g p)
        (originalCurrentTaggedMove B g q) = a := by
    intro g p q h
    rcases p with ⟨i,x⟩
    rcases q with ⟨j,y⟩
    have hg : B.source.colour (g • x) (g • y) =
        B.source.colour x y :=
      B.source.colourInvariant_of_homogeneous B.homogeneous g x y
    exact (congrArg (fun c : Option (B.source.Atom i j) =>
      (⟨i,j,c⟩ : Age.Colour B.source)) hg).trans h
  exact originalCurrentExactSaturation_taggedColour_iff
    A B P base hOne E
      (fun x y => taggedColour B.source x y = a)
      hD p q p' q' hColour

/-- All true old E-saturated pair-orbital blocks are preserved
simultaneously on any indexed finite fine-colour old chart.
Distinct original E-class equality is separately in C96's
`OriginalCurrentExactColourInvariance`. -/
theorem originalCurrentExactSaturatedColour_fullChart_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {V : Type z} (old new : V → Sigma B.Point)
    (hColours : ∀ i j : V,
      taggedColour B.source (old i) (old j) =
      taggedColour B.source (new i) (new j)) :
    ∀ (a : Age.Colour B.source) (i j : V),
      originalCurrentExactSaturatedColour
        A B P base hOne E a (old i) (old j) ↔
      originalCurrentExactSaturatedColour
        A B P base hOne E a (new i) (new j) := by
  intro a i j
  exact originalCurrentExactSaturatedColour_taggedColour_iff
    A B P base hOne E a (old i) (old j)
      (new i) (new j) (hColours i j)

end
end CCO.ExactEPGeometry
