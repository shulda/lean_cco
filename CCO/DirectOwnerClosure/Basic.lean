import CCO.FinitePackets.Geometry.MinimalCutBasic
import CCO.FinitePackets.Geometry.Sigma
import CCO.RealHull.Canonical.Source
import CCO.FiniteKernel.BinarySource
import Mathlib.Algebra.Group.Subgroup.Actions

/-! Actual real and individually named imaginary stabilizers.  The induced
owner union is allowed to be empty.  These definitions impose no countability,
normalization, homogeneity of the union, or restriction-surjectivity premise. -/
universe v w t
namespace CCO.DirectOwnerClosure
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
open FinitePackets.Geometry FiniteKernel

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

/-- The complete original fine-colour language and its FULL group. -/
def realStructure : BinaryStructure M where
  Unary := Empty
  Binary := FullColour S
  unary e := nomatch e
  binary c x y := col S x y = c

abbrev FullAut := (realStructure S).Aut

theorem fullAut_colour (g : FullAut S) (x y : M) :
    col S (g.val x) (g.val y) = col S x y :=
  (g.property.2 (col S x y) x y).mpr rfl

theorem fullAut_equivalence (E : ColourEq S ()) (g : FullAut S) (x y : M) :
    E (g.val x) (g.val y) ↔ E x y :=
  E.property _ _ _ _ (fullAut_colour S g x y)

variable {G : Type t} [Group G] [MulAction G M]

def motionAut (H : HomogeneousSource S G) (g : G) : FullAut S :=
  ⟨MulAction.toPerm g, by
    constructor
    · intro e; cases e
    · intro c x y
      change col S (g • x) (g • y) = c ↔ col S x y = c
      rw [col_invariant S H]⟩

theorem full_homogeneous (H : HomogeneousSource S G) :
    HomogeneousSource S (FullAut S) where
  preserves_sort := by intro g p; cases p with | mk i x => cases i; rfl
  preserves_colours := by
    intro g p q
    rcases p with ⟨⟨⟩,x⟩
    rcases q with ⟨⟨⟩,y⟩
    exact congrArg (fun c : FullColour S => (⟨(),(),c⟩ : Σ i : Unit, Σ j : Unit,
      Option (S.Atom i j))) (fullAut_colour S g _ _)
  extends_finite_diagram := by
    intro V _ f h hc
    obtain ⟨g,hg⟩ := H.extends_finite_diagram f h hc
    exact ⟨motionAut S H g,hg⟩

/-- The finite-orbit semantics used in the three closure conclusions. -/
def orbitOver (K : Type*) [Group K] [MulAction K M] (A : Finset M) (x : M) : Set M :=
  {y | ∃ g : K, (∀ a ∈ A, g • a = a) ∧ g • x = y}

def algebraicClosure (K : Type*) [Group K] [MulAction K M] (A : Finset M) : Set M :=
  {x | (orbitOver K A x).Finite}

def definableClosure (K : Type*) [Group K] [MulAction K M] (A : Finset M) : Set M :=
  {x | ∀ g : K, (∀ a ∈ A, g • a = a) → g • x = x}

theorem definable_subset_algebraic (K : Type*) [Group K] [MulAction K M] (A : Finset M) :
    definableClosure K A ⊆ algebraicClosure K A := by
  intro x hx
  apply (Set.finite_singleton x).subset
  rintro y ⟨g,hg,rfl⟩
  exact Set.mem_singleton_iff.mpr (hx g hg)

/-- B013's greatest finite-class equivalence, with no exactness assertion. -/
noncomputable abbrev packet (H : HomogeneousSource S G) : ColourEq S () := sigma S H ⊥

def packetHull (H : HomogeneousSource S G) (A : Finset M) : Set M :=
  {x | ∃ a ∈ A, packet S H a x}

def UniqueDirection (E : ColourEq S ()) : Prop :=
  MinimalInfiniteCut S E ∧ ∀ D : ColourEq S (), MinimalInfiniteCut S D → D = E

abbrev Owner (E : ColourEq S ()) := Quotient E.val

def owner (E : ColourEq S ()) (x : M) : Owner S E := Quotient.mk E.val x

def OwnerUnion (E : ColourEq S ()) (B : Finset (Owner S E)) :=
  {x : M // owner S E x ∈ B}

def namedStructure (E : ColourEq S ()) (B : Finset (Owner S E)) :
    BinaryStructure (OwnerUnion S E B) where
  Unary := Owner S E
  Binary := FullColour S
  unary b x := owner S E x.val = b
  binary c x y := col S x.val y.val = c

abbrev NamedAut (E : ColourEq S ()) (B : Finset (Owner S E)) :=
  (namedStructure S E B).Aut

theorem namedAut_owner (E : ColourEq S ()) (B : Finset (Owner S E))
    (g : NamedAut S E B) (x : OwnerUnion S E B) :
    owner S E (g.val x).val = owner S E x.val :=
  (g.property.1 (owner S E x.val) x).mpr rfl

theorem namedAut_colour (E : ColourEq S ()) (B : Finset (Owner S E))
    (g : NamedAut S E B) (x y : OwnerUnion S E B) :
    col S (g.val x).val (g.val y).val = col S x.val y.val :=
  (g.property.2 (col S x.val y.val) x y).mpr rfl

def FixesOwner (E : ColourEq S ()) (b : Owner S E) (g : FullAut S) : Prop :=
  E b.out (g.val b.out)

theorem fixesOwner_iff (E : ColourEq S ()) (b : Owner S E) (g : FullAut S)
    (x : M) (hx : owner S E x = b) :
    FixesOwner S E b g ↔ owner S E (g.val x) = b := by
  have hxo : E x b.out := Quotient.exact (hx.trans (Quotient.out_eq b).symm)
  have hgxo : E (g.val x) (g.val b.out) :=
    (fullAut_equivalence S E g x b.out).mpr hxo
  constructor
  · intro h
    apply (Quotient.sound (E.val.trans hgxo (E.val.symm h))).trans
    exact Quotient.out_eq b
  · intro h
    have hox : E (g.val x) b.out := Quotient.exact (h.trans (Quotient.out_eq b).symm)
    exact E.val.trans (E.val.symm hox) hgxo

def ownerOrbit (E : ColourEq S ()) (B : Finset (Owner S E)) (A : Finset M) (x : M) : Set M :=
  {y | ∃ g : FullAut S, (∀ a ∈ A, g.val a = a) ∧
    (∀ b ∈ B, FixesOwner S E b g) ∧ g.val x = y}

def ownerClosure (E : ColourEq S ()) (B : Finset (Owner S E)) (A : Finset M) : Set M :=
  {x | (ownerOrbit S E B A x).Finite}

noncomputable def realBase [DecidableEq M] (E : ColourEq S ()) (B : Finset (Owner S E))
    (A : Finset (OwnerUnion S E B)) : Finset M := A.image Subtype.val

end CCO.DirectOwnerClosure
