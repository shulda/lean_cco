import CCO.CloneSAP.Amalgamation
import CCO.CloneSAP.CCO.Lift
import CCO.CloneSAP.Homogeneity
import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Fintype.Sigma

/-! The actual pure-set pair shadow for B048 C32. A one-point source has
no old diversity atoms. Its infinite pure clone has exactly one distinct
pair type and proves genuine SAP and semantic CCO by accepted constructions. -/

universe z
namespace CCO.FullPhaseLift.Boundary
noncomputable section

local instance : Subsingleton (Sigma (fun _ : Unit => Unit)) where
  allEq a b := by
    rcases a with ⟨i,x⟩
    rcases b with ⟨j,y⟩
    cases i; cases j; cases x; cases y; rfl

def onePoint : AtomicSource Unit (fun _ => Unit) where
  Atom _ _ := Empty
  finiteSort := inferInstance
  finiteAtom _ _ := inferInstance
  nonemptySort _ := inferInstance
  conv := Empty.elim
  conv_invol := by intro _ _ a; exact Empty.elim a
  symmetricLoop := by intro _ a; exact Empty.elim a
  colour _ _ := none
  colour_none_iff _ _ := ⟨fun _ => Subsingleton.elim _ _,fun _ => rfl⟩
  colour_swap _ _ a := Empty.elim a
  realized a := Empty.elim a

def onePointObject : FiniteInduced (X := fun _ : Unit => Unit) where
  vertices := Set.univ
  finite_vertices := Set.toFinite _

def onePointInto (A : FiniteInduced (X := fun _ : Unit => Unit)) :
    InducedEmbedding onePoint A onePointObject where
  toEmbedding := ⟨fun a => ⟨a.val,Set.mem_univ _⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : onePointObject.vertices => z.val) h)⟩
  preserves_sort _ := rfl
  preserves_colours _ _ := rfl

theorem onePoint_ageAP : AgeAP onePoint where
  amalgamate := by
    intro C A B _ _
    exact ⟨onePointObject,onePointInto A,onePointInto B,
      fun _ => Subsingleton.elim _ _⟩

theorem onePoint_homogeneous : HomogeneousSource onePoint (Equiv.Perm Unit) where
  preserves_sort _ _ := Subsingleton.elim _ _
  preserves_colours _ _ _ := rfl
  extends_finite_diagram := by
    intro V _ f h _
    exact ⟨1,fun _ => Subsingleton.elim _ _⟩

abbrev purePair := CloneSAP.source onePoint

theorem purePair_ageSAP : AgeSAP purePair :=
  CloneSAP.strong_amalgamation onePoint onePoint_ageAP

theorem purePair_homogeneous :
    HomogeneousSource purePair (TerminalPowers.FullAut purePair) :=
  CloneSAP.homogeneous onePoint onePoint_homogeneous

/-- Every finite pure-set partial diagram has an injective realization;
the simple-cycle premise is therefore unnecessary for this actual source. -/
theorem purePair_injective (V : Type z) (D : PartialDiagram purePair V) :
    ∃ f : DiagramHom D, f.IsInjective := by
  apply CloneSAP.CCO.lift_owner_assignment onePoint D (fun _ => ())
  · intro _ _ _ a
    exact Empty.elim a
  · intro _ _ _ _ _
    exact Subsingleton.elim _ _

theorem purePair_cco : SemanticCCO.{0,0,z,0} purePair := by
  intro V D _
  obtain ⟨f,_⟩ := purePair_injective V D
  exact ⟨f⟩

/-- There is one actual diversity name; the logical diagonal is separate. -/
theorem purePair_atom_unique (i j : Unit) (a b : purePair.Atom i j) : a = b := by
  cases a with
  | inl a => exact Empty.elim a
  | inr a =>
    cases b with
    | inl b => exact Empty.elim b
    | inr b => exact congrArg Sum.inr (Subsingleton.elim a b)

end
end CCO.FullPhaseLift.Boundary
