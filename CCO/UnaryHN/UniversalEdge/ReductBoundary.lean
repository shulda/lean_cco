import CCO.UnaryHN.UniversalEdge.GlobalCollapse

/-! Two named sorts with at most one point each give rigid completed maps
while the actual two-point old member is reducible. Its universal-edge
expansion is irreducible; forgetting the edge is not an irreducibility rule. -/

namespace CCO.UnaryHN.Native.UniversalEdgeBoundaries

open StructuralRamsey
open StructuralRamsey.Structure

abbrev sortLanguage : Language where
  RelSymbol := Bool
  FuncSymbol := Empty
  relArity _ := 1
  funcArity := Empty.elim

def sortModel {V : Type} (color : V → Bool) : Structure sortLanguage V where
  rel b xs := color (xs 0) = b
  func F := Empty.elim F

def sortClass : Class.{0,0} sortLanguage :=
  fun {V} C => ∃ color : V → Bool, Function.Injective color ∧ C = sortModel color

theorem sort_class_rigid : CompletedMapRigidity sortClass := by
  apply completedMapRigidity_of_homomorphisms
  intro V W C D hC hD f hf
  obtain ⟨c, hc, rfl⟩ := hC
  obtain ⟨d, _, rfl⟩ := hD
  have hColor (x : V) : d (f x) = c x :=
    hf.1 (c x) (fun _ => x) rfl
  refine ⟨{ toFun := f, injective := ?_, map_rel_iff := ?_, map_func := ?_ },
    fun _ => rfl⟩
  · intro x y h
    apply hc
    exact (hColor x).symm.trans ((congrArg d h).trans (hColor y))
  · intro R xs
    change d (f (xs 0)) = R ↔ c (xs 0) = R
    rw [hColor]
  · intro F
    exact Empty.elim F

def sortRoot (b : Bool) :
    Embedding (sortModel (Empty.elim : Empty → Bool))
      (sortModel (fun _ : Unit => b)) where
  toFun := Empty.elim
  injective := by intro x; exact Empty.elim x
  map_rel_iff _ xs := Empty.elim (xs 0)
  map_func F := Empty.elim F

def sortSide (b : Bool) :
    Embedding (sortModel (fun _ : Unit => b)) (sortModel (id : Bool → Bool)) where
  toFun _ := b
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel_iff _ _ := Iff.rfl
  map_func F := Empty.elim F

theorem sortBoolSplit :
    IsFreeAmalgam (sortRoot false) (sortRoot true) (sortSide false) (sortSide true) where
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
  rel_iff := by
    intro R xs
    constructor
    · intro h
      change xs 0 = R at h
      cases hx : xs 0
      · left
        refine ⟨fun _ => (), hx.symm.trans h, ?_⟩
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact hx
      · right
        refine ⟨fun _ => (), hx.symm.trans h, ?_⟩
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact hx
    · rintro (⟨ys, h, hEq⟩ | ⟨ys, h, hEq⟩)
      · exact (congrFun hEq 0).trans h
      · exact (congrFun hEq 0).trans h
  func_iff F := Empty.elim F

theorem old_sortBool_reducible : ¬ (sortModel (id : Bool → Bool)).Irreducible := by
  intro h
  rcases h sortBoolSplit (Embedding.id _) with hLeft | hRight
  · obtain ⟨a, ha⟩ := hLeft true
    change true = false at ha
    cases ha
  · obtain ⟨a, ha⟩ := hRight false
    change false = true at ha
    cases ha

theorem bool_expansion_irreducible {L : Language} (old : Structure L Bool) :
    (expandEdge old).Irreducible := by
  let C := expandEdge old
  let xs : Fin 2 → Bool := ![false, true]
  let S := C.functionClosure (Set.range xs)
  have hS := C.functionClosure_isClosed (Set.range xs)
  have hHull : (C.induce S hS).Irreducible :=
    relation_tuple_hull_irreducible C (.inr ()) xs (by change false ≠ true; decide)
  let inc := inclusion C S hS
  have hSurj : Function.Surjective inc := by
    intro b
    have hb : b ∈ S := by
      apply C.subset_functionClosure (Set.range xs)
      cases b
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩
  intro G E F Z Root Left Right Whole sL sR iL iR hFree e
  rcases hHull hFree (e.comp inc) with hLeft | hRight
  · left
    intro b
    obtain ⟨a, rfl⟩ := hSurj b
    exact hLeft a
  · right
    intro b
    obtain ⟨a, rfl⟩ := hSurj b
    exact hRight a

/-- C44's other boundary: even with completed-map rigidity and actual old
class membership, irreducibility can be lost by forgetting the edge. -/
theorem forgetting_edge_can_destroy_irreducibility :
    CompletedMapRigidity sortClass ∧ sortClass (sortModel (id : Bool → Bool)) ∧
    (expandEdge (sortModel (id : Bool → Bool))).Irreducible ∧
    ¬ (edgeReduct (expandEdge (sortModel (id : Bool → Bool)))).Irreducible :=
  ⟨sort_class_rigid, ⟨id, Function.injective_id, rfl⟩,
    bool_expansion_irreducible _, old_sortBool_reducible⟩

end CCO.UnaryHN.Native.UniversalEdgeBoundaries
