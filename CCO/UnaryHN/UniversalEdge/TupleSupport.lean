import CCO.UnaryHN.NativeTransferBasis

/-! A displayed positive relation tuple generates an ACTUAL closed
irreducible source. Repeated entries and arity zero are included. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

/-- Every positive tuple's entire functional hull is irreducible.
No pair-coverage, unary-function or nonempty-tuple premise is used. -/
theorem relation_tuple_hull_irreducible {L : Language.{u}} {V : Type v}
    (C : Structure L V) (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → V) (hRel : C.rel R xs) :
    (C.induce (C.functionClosure (Set.range xs))
      (C.functionClosure_isClosed (Set.range xs))).Irreducible := by
  let q : ULift.{v} (Fin (L.relArity R)) → V := fun j => xs j.down
  have hRange : Set.range q = Set.range xs := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.down, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨ULift.up j, rfl⟩
  rw [← hRange]
  let H := C.induce (C.functionClosure (Set.range q))
    (C.functionClosure_isClosed (Set.range q))
  have hGen : H.Generates (closureLift C q) := closureLift_generates C q
  let xH : Fin (L.relArity R) → C.functionClosure (Set.range q) :=
    fun j => closureLift C q (ULift.up j)
  intro G E F Z Root Left Right Whole sL sR iL iR hFree e
  have hTuple : Whole.rel R (e ∘ xH) :=
    (e.map_rel_iff R _).mpr hRel
  rcases (hFree.rel_iff R _).mp hTuple with ⟨ys, _, hEq⟩ | ⟨ys, _, hEq⟩
  · left
    intro a
    have hClosed : H.IsClosed {a | e a ∈ Set.range iL} :=
      e.preimage_isClosed (Set.range iL) iL.range_isClosed
    have hSeed : ∀ j, e (closureLift C q j) ∈ Set.range iL :=
      fun j => ⟨ys j.down, (congrFun hEq j.down).symm⟩
    obtain ⟨y, hy⟩ := hGen _ hClosed hSeed a
    exact ⟨y, hy.symm⟩
  · right
    intro a
    have hClosed : H.IsClosed {a | e a ∈ Set.range iR} :=
      e.preimage_isClosed (Set.range iR) iR.range_isClosed
    have hSeed : ∀ j, e (closureLift C q j) ∈ Set.range iR :=
      fun j => ⟨ys j.down, (congrFun hEq j.down).symm⟩
    obtain ⟨y, hy⟩ := hGen _ hClosed hSeed a
    exact ⟨y, hy.symm⟩

end CCO.UnaryHN.Native
