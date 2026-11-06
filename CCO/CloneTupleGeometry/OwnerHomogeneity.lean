import CCO.CloneSAP.Quotient
import CCO.RawExact.QuotientAgeAP

/-!
# B060 N02: whole finite-diagram homogeneity descends from clones to owners

Lift every real owner point to clone index zero. The FULL tagged pair code,
including logical equality and mixed sort tags, determines the complete
clone code of these lifts. One actual whole clone automorphism therefore
extends the lifted finite diagram. The already proved actual automorphism
`CloneSAP.descendAut` projects it to the original owners, retaining every
original fine colour. No quotient-action section, SAP or CCO is assumed.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

open TerminalPowers
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A fixed-index lift of a real owner point, retaining its original sort. -/
def zeroClonePoint (p : Sigma X) : Sigma (CloneSAP.Carrier X) :=
  ⟨p.1,(p.2,0)⟩

@[simp] theorem owner_zeroClonePoint (p : Sigma X) :
    CloneSAP.owner (zeroClonePoint p) = p := by
  cases p
  rfl

theorem zeroClonePoint_injective :
    Function.Injective (zeroClonePoint (X := X)) := by
  intro p q hpq
  simpa only [owner_zeroClonePoint] using congrArg CloneSAP.owner hpq

/-- Real complete owner pair codes lift to complete clone pair codes.
The same index on both endpoints keeps real equality as equality;
it does not introduce a new clone diversity edge on the diagonal. -/
theorem zeroClonePoint_tagged {p q r s : Sigma X}
    (hc : taggedColour S p q = taggedColour S r s) :
    taggedColour (CloneSAP.source S) (zeroClonePoint p) (zeroClonePoint q) =
      taggedColour (CloneSAP.source S) (zeroClonePoint r) (zeroClonePoint s) := by
  apply CloneSAP.tagged_reconstruct S
    (by simpa only [owner_zeroClonePoint] using hc)
  constructor
  · intro he
    exact congrArg zeroClonePoint
      ((CloneSAP.tagged_diagonal S hc).mp (zeroClonePoint_injective he))
  · intro he
    exact congrArg zeroClonePoint
      ((CloneSAP.tagged_diagonal S hc).mpr (zeroClonePoint_injective he))

/-- The actual quotient-induced owner action agrees with projecting
the whole clone action on the fixed-index lifts. -/
theorem descendAut_zeroClonePoint (g : FullAut (CloneSAP.source S))
    (p : Sigma X) :
    CloneSAP.descendAut S g • p = CloneSAP.owner (g • zeroClonePoint p) := by
  rcases p with ⟨i,x⟩
  rfl

/-- Any actual homogeneous action on the infinite pure clone source
gives homogeneity of the genuine owner source under its FULL group.
This uses one whole extending automorphism, not separate pair motions. -/
theorem owner_homogeneous_of_clone
    {G : Type t} [Group G]
    [∀ i : ι, MulAction G (CloneSAP.Carrier X i)]
    (H : HomogeneousSource (CloneSAP.source S) G) :
    HomogeneousSource S (FullAut S) := by
  have Hfull : HomogeneousSource (CloneSAP.source S)
      (FullAut (CloneSAP.source S)) :=
    full_homogeneous (CloneSAP.source S) H
  refine ⟨?_,?_,?_⟩
  · intro g p
    rfl
  · rintro g ⟨i,x⟩ ⟨j,y⟩
    exact congrArg
      (fun c : Option (S.Atom i j) =>
        (⟨i,j,c⟩ : Σ i, Σ j, Option (S.Atom i j)))
      (fullAut_colour S g i j x y)
  · intro V _ f h hc
    obtain ⟨g,hg⟩ := Hfull.extends_finite_diagram
      (fun a => zeroClonePoint (f a))
      (fun a => zeroClonePoint (h a))
      (fun a b => zeroClonePoint_tagged S (hc a b))
    refine ⟨CloneSAP.descendAut S g,?_⟩
    intro a
    have ho := congrArg CloneSAP.owner (hg a)
    rw [descendAut_zeroClonePoint]
    exact ho.trans (owner_zeroClonePoint (h a))

/-- Ordinary AP of the ACTUAL owner age follows by the usual finite
homogeneity argument. This makes no claim of owner SAP. -/
theorem owner_ageAP_of_clone
    {G : Type t} [Group G]
    [∀ i : ι, MulAction G (CloneSAP.Carrier X i)]
    (H : HomogeneousSource (CloneSAP.source S) G) : AgeAP S :=
  ageAP_of_homogeneous S (owner_homogeneous_of_clone S H)

end CCO.CloneTupleGeometry
