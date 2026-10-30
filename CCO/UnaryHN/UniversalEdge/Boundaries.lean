import CCO.UnaryHN.UniversalEdge.SameMap
import Mathlib.Data.Fin.VecNotation

/-! Concrete finite structures, maps and full irreducible tests distinguish
rigidity, global injectivity and global inducedness. -/

namespace CCO.UnaryHN.Native.UniversalEdgeBoundaries

open StructuralRamsey
open StructuralRamsey.Structure

def isolated (L : Language) [IsEmpty L.FuncSymbol] (V : Type) : Structure L V where
  rel _ _ := False
  func F := isEmptyElim F

def isolatedEmbedding (L : Language) [IsEmpty L.FuncSymbol]
    {V W : Type} (f : V → W) (hf : Function.Injective f) :
    Embedding (isolated L V) (isolated L W) where
  toFun := f
  injective := hf
  map_rel_iff _ _ := Iff.rfl
  map_func F := isEmptyElim F

def splitRoot (L : Language) [IsEmpty L.FuncSymbol] :=
  isolatedEmbedding L (Empty.elim : Empty → Unit) (by intro x; exact Empty.elim x)

def splitLeft (L : Language) [IsEmpty L.FuncSymbol] :=
  isolatedEmbedding L (fun _ : Unit => false) (fun _ _ _ => Subsingleton.elim _ _)

def splitRight (L : Language) [IsEmpty L.FuncSymbol] :=
  isolatedEmbedding L (fun _ : Unit => true) (fun _ _ _ => Subsingleton.elim _ _)

theorem isolatedSplit (L : Language) [IsEmpty L.FuncSymbol] :
    IsFreeAmalgam (splitRoot L) (splitRoot L) (splitLeft L) (splitRight L) where
  covers := by
    intro b
    cases b
    · exact Or.inl ⟨(), rfl⟩
    · exact Or.inr ⟨(), rfl⟩
  overlap := by
    intro a b
    constructor
    · intro h
      cases h
    · rintro ⟨x, _, _⟩
      exact Empty.elim x
  rel_iff := by intro R xs; simp [isolated]
  func_iff F := isEmptyElim F

theorem irreducible_in_isolatedBool_subsingleton
    {L : Language} [IsEmpty L.FuncSymbol] {X : Type}
    (E : Structure L X) (hE : E.Irreducible)
    (e : Embedding E (isolated L Bool)) : Subsingleton X := by
  rcases hE (isolatedSplit L) e with hLeft | hRight
  · refine ⟨?_⟩
    intro x y
    apply e.injective
    obtain ⟨a, ha⟩ := hLeft x
    obtain ⟨b, hb⟩ := hLeft y
    change e x = false at ha
    change e y = false at hb
    exact ha.trans hb.symm
  · refine ⟨?_⟩
    intro x y
    apply e.injective
    obtain ⟨a, ha⟩ := hRight x
    obtain ⟨b, hb⟩ := hRight y
    change e x = true at ha
    change e y = true at hb
    exact ha.trans hb.symm

theorem isolated_constant_HE (L : Language) [IsEmpty L.FuncSymbol] :
    HE (isolated L Bool) (isolated L Unit) (fun _ => ()) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro R xs h
    exact False.elim h
  · intro F
    exact isEmptyElim F
  · intro X E hE e
    letI : Subsingleton X := irreducible_in_isolatedBool_subsingleton E hE e
    refine ⟨{ toFun := fun _ => (), injective := fun _ _ _ => Subsingleton.elim _ _,
               map_rel_iff := ?_, map_func := ?_ }, fun _ => rfl⟩
    · intro R xs
      change False ↔ E.rel R xs
      exact ⟨False.elim, fun h => (e.map_rel_iff R xs).mpr h⟩
    · intro F
      exact isEmptyElim F

abbrev emptyLanguage : Language where
  RelSymbol := Empty
  FuncSymbol := Empty
  relArity := Empty.elim
  funcArity := Empty.elim

def finiteEmptyClass : Class.{0,0} emptyLanguage := fun {X} _ => Finite X

theorem complete_edge_local_membership :
    IrreduciblesIn (ExpandedClass finiteEmptyClass)
      (expandEdge (isolated emptyLanguage Bool)) := by
  intro X E _ e
  apply ExpandedClass.of_edge_iff
  · exact Finite.of_injective e e.injective
  · intro xs
    have h := e.map_rel_iff (.inr ()) xs
    change (e (xs 0) ≠ e (xs 1)) ↔ E.rel (.inr ()) xs at h
    exact h.symm.trans e.injective.ne_iff

/-- C43: actual local completed membership and an old HE do not preserve
the universal edge without completed-map rigidity. -/
theorem rigidity_cannot_be_omitted :
    HE (isolated emptyLanguage Bool) (isolated emptyLanguage Unit) (fun _ => ()) ∧
    IrreduciblesIn (ExpandedClass finiteEmptyClass)
      (expandEdge (isolated emptyLanguage Bool)) ∧
    ¬ HE (expandEdge (isolated emptyLanguage Bool))
      (expandEdge (isolated emptyLanguage Unit)) (fun _ => ()) := by
  refine ⟨isolated_constant_HE _, complete_edge_local_membership, ?_⟩
  intro h
  have bad := h.1.1 (.inr ()) ![false, true] (by change false ≠ true; decide)
  exact bad rfl

abbrev graphLanguage : Language where
  RelSymbol := Unit
  FuncSymbol := Empty
  relArity _ := 2
  funcArity := Empty.elim

def completeGraph (V : Type) : Structure graphLanguage V where
  rel _ xs := xs 0 ≠ xs 1
  func F := Empty.elim F

/-- C45's globally injective HE can add the missing binary relation. -/
theorem injective_HE_not_globally_induced :
    HE (isolated graphLanguage Bool) (completeGraph Bool) id ∧
    Function.Injective (id : Bool → Bool) ∧
    ¬ Nonempty (Embedding (isolated graphLanguage Bool) (completeGraph Bool)) := by
  refine ⟨?_, Function.injective_id, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro R xs h
      exact False.elim h
    · intro F
      exact Empty.elim F
    · intro X E hE e
      letI : Subsingleton X := irreducible_in_isolatedBool_subsingleton E hE e
      refine ⟨{ toFun := e, injective := e.injective,
                 map_rel_iff := ?_, map_func := ?_ }, fun _ => rfl⟩
      · intro R xs
        change (e (xs 0) ≠ e (xs 1)) ↔ E.rel R xs
        constructor
        · intro h
          exact False.elim (h (congrArg e (Subsingleton.elim _ _)))
        · intro h
          exact False.elim ((e.map_rel_iff R xs).mpr h)
      · intro F
        exact Empty.elim F
  · rintro ⟨g⟩
    have positive : (completeGraph Bool).rel () (g ∘ ![false, true]) := by
      change g false ≠ g true
      exact g.injective.ne (by decide)
    exact (g.map_rel_iff () ![false, true]).mp positive

end CCO.UnaryHN.Native.UniversalEdgeBoundaries
