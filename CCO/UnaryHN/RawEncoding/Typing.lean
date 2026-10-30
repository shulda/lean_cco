import CCO.UnaryHN.TypedTransferBasis
import CCO.UnaryHN.UniversalEdge.TupleSupport

/-! Recover typing from ACTUAL completed irreducible diagrams in a raw
one-sorted candidate, before applying any typed obstruction theorem. -/
universe u v
namespace CCO.UnaryHN.Raw
open CCO.UnarySupport (Signature)
open StructuralRamsey.Structure
variable {L : Signature.{u}} {V : Type v}

theorem point_hull_irreducible (D : Diagram L V) (x : V) :
    (D.induce (D.functionClosure {x}) (D.functionClosure_isClosed {x})).Irreducible := by
  have h : (D.induce (D.functionClosure (Set.range (fun _ : PUnit.{v+1} => x)))
      (D.functionClosure_isClosed (Set.range (fun _ : PUnit.{v+1} => x)))).Irreducible :=
    Native.one_point_hull_irreducible D x
  have hr : Set.range (fun _ : PUnit.{v+1} => x) = {x} := by
    ext y
    simp
  rw [← hr]
  exact @h

theorem part_sort_iff (D : Diagram L V) (S : Set V) (hS : D.IsClosed S)
    (T : Typed L S) (hT : encode T = D.induce S hS) (x : S) (s : L.Sorts) :
    D.rel (.inr s) (fun _ => x.val) ↔ T.sort x = s := by
  change (D.induce S hS).rel (.inr s) (fun _ => x) ↔ _
  rw [← hT]
  rfl

theorem part_func_iff (D : Diagram L V) (S : Set V) (hS : D.IsClosed S)
    (T : Typed L S) (hT : encode T = D.induce S hS) (F : L.Func) (x y : S) :
    y.val ∈ D.func F (fun _ => x.val) ↔ y ∈ T.func F x := by
  change y ∈ (D.induce S hS).func F (fun _ => x) ↔ _
  rw [← hT]
  rfl

theorem part_rel_iff (D : Diagram L V) (S : Set V) (hS : D.IsClosed S)
    (T : Typed L S) (hT : encode T = D.induce S hS) (R : L.Rel)
    (xs : Fin (L.arity R) → S) :
    D.rel (.inl R) (Subtype.val ∘ xs) ↔ T.rel R xs := by
  change (D.induce S hS).rel (.inl R) xs ↔ _
  rw [← hT]
  rfl

/-- C18–C22: no correct-type premise on D is assumed. Singleton and positive
tuple supports independently force every piece of its actual typed diagram. -/
theorem typed_of_irreducibles {K : Class.{u,v} L} (hCompleted : CompletedClass K)
    [Finite V] (D : Diagram L V) (hPieces : Native.IrreduciblesIn (EncodedClass K) D) :
    ∃ C : Typed L V, encode C = D ∧ C.Total := by
  classical
  have point (x : V) :
      ∃ T : Typed L (D.functionClosure {x}), K T ∧
        encode T = D.induce (D.functionClosure {x}) (D.functionClosure_isClosed {x}) :=
    hPieces _ (point_hull_irreducible D x)
      (inclusion D (D.functionClosure {x}) (D.functionClosure_isClosed {x}))
  let root (x : V) : D.functionClosure {x} :=
    ⟨x, D.subset_functionClosure {x} (by rfl)⟩
  have hExists (x : V) : ∃ s : L.Sorts, D.rel (.inr s) (fun _ => x) := by
    obtain ⟨T, _, hT⟩ := point x
    exact ⟨T.sort (root x),
      (part_sort_iff D _ _ T hT (root x) _).mpr rfl⟩
  let sort : V → L.Sorts := fun x => Classical.choose (hExists x)
  have hsort (x : V) (s : L.Sorts) : D.rel (.inr s) (fun _ => x) ↔ sort x = s := by
    obtain ⟨T, _, hT⟩ := point x
    have hx := Classical.choose_spec (hExists x)
    have ht : T.sort (root x) = sort x :=
      (part_sort_iff D _ _ T hT (root x) _).mp hx
    rw [part_sort_iff D _ _ T hT (root x) s, ht]
  have localSort (S : Set V) (hS : D.IsClosed S) (T : Typed L S)
      (hT : encode T = D.induce S hS) (x : S) : sort x.val = T.sort x :=
    (hsort x.val (T.sort x)).mp ((part_sort_iff D S hS T hT x _).mpr rfl)
  let C : Typed L V := {
    sort := sort
    func F x := D.func F (fun _ => x)
    functional := by
      intro F x y z hy hz
      obtain ⟨T, _, hT⟩ := point x
      have hyS : y ∈ D.functionClosure {x} :=
        D.functionClosure_isClosed {x} F (fun _ => x) (fun _ => (root x).property) hy
      have hzS : z ∈ D.functionClosure {x} :=
        D.functionClosure_isClosed {x} F (fun _ => x) (fun _ => (root x).property) hz
      have he := T.functional F (root x) ⟨y, hyS⟩ ⟨z, hzS⟩
        ((part_func_iff D _ _ T hT F (root x) ⟨y, hyS⟩).mp hy)
        ((part_func_iff D _ _ T hT F (root x) ⟨z, hzS⟩).mp hz)
      exact congrArg (fun t : D.functionClosure {x} => t.val) he
    func_sorted := by
      intro F x y hy
      obtain ⟨T, _, hT⟩ := point x
      have hyS : y ∈ D.functionClosure {x} :=
        D.functionClosure_isClosed {x} F (fun _ => x) (fun _ => (root x).property) hy
      have ht := T.func_sorted F (root x) ⟨y, hyS⟩
        ((part_func_iff D _ _ T hT F (root x) ⟨y, hyS⟩).mp hy)
      exact ⟨(localSort _ _ T hT (root x)).trans ht.1,
        (localSort _ _ T hT ⟨y, hyS⟩).trans ht.2⟩
    rel R xs := D.rel (.inl R) xs
    rel_sorted := by
      intro R xs hx i
      let S := D.functionClosure (Set.range xs)
      have hS : D.IsClosed S := D.functionClosure_isClosed (Set.range xs)
      obtain ⟨T, _, hT⟩ := hPieces _
        (Native.relation_tuple_hull_irreducible D (.inl R) xs hx)
        (inclusion D S hS)
      let xt : Fin (L.arity R) → S :=
        fun j => ⟨xs j, D.subset_functionClosure (Set.range xs) ⟨j, rfl⟩⟩
      have ht : T.rel R xt := (part_rel_iff D S hS T hT R xt).mp hx
      exact (localSort S hS T hT (xt i)).trans (T.rel_sorted R xt ht i) }
  have one_eta {X : Type v} (xs : Fin 1 → X) : (fun _ : Fin 1 => xs 0) = xs := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have hEncode : encode C = D := by
    apply diagram_ext
    · funext R xs
      apply propext
      cases R with
      | inl R => exact Iff.rfl
      | inr s =>
        change sort (xs 0) = s ↔ D.rel (.inr s) xs
        rw [← hsort (xs 0) s, one_eta xs]
    · funext F xs
      change D.func F (fun _ => xs 0) = D.func F xs
      rw [one_eta xs]
  refine ⟨C, hEncode, ?_⟩
  intro F x hx
  obtain ⟨T, hK, hT⟩ := point x
  have ht : T.sort (root x) = L.input F := (localSort _ _ T hT (root x)).symm.trans hx
  obtain ⟨y, hy⟩ := hCompleted T hK F (root x) ht
  exact ⟨y.val, (part_func_iff D _ _ T hT F (root x) y).mpr hy⟩

theorem domain_exactly_input {V : Type v} (C : Typed L V) (hTotal : C.Total)
    (F : L.Func) (x : V) : (C.func F x).Nonempty ↔ C.sort x = L.input F := by
  constructor
  · rintro ⟨y, hy⟩
    exact (C.func_sorted F x y hy).1
  · exact hTotal F x

end CCO.UnaryHN.Raw
