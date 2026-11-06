import CCO.HiddenSAPReadings.SourceSupport
import CCO.UnaryFreshFrames.UniformBounds

/-! Source14 C01--C06. Unary admissibility is a literal induced embedding
of the FULL source singleton closure into the actual completed target.
The image is its whole actual singleton closure. No completion of the
ambient partial source is included in this hypothesis or conclusion. -/

universe u v w r z
namespace CCO.GuardedTwoRoot
open CCO.UnarySupport CCO.UnarySupport.Structure

section Partial
variable {L : Signature.{u}} {V : Type v} {W : Type w}
variable {C : Structure L V} {A : Structure L W}

/-- Every complete one-generated source diagram is an actual induced
closed subobject. Missing source function domains are reflected too. -/
def UnaryAdmissible (C : Structure L V) (A : Structure L W) : Prop :=
  ∀ x, Nonempty (Embedding (C.singletonStructure x) A)

/-- The complete-pattern test is imposed on the ACTUAL irreducible closed
support, with all its relations, inequalities, unary domains and values. -/
def JoinedAdmissible (C : Structure L V) (A : Structure L W) : Prop :=
  ∀ D (hD : C.IsClosed D), (C.induce D hD).Irreducible →
    Nonempty (Embedding (C.induce D hD) A)

theorem joined_admissible_unary (h : JoinedAdmissible C A) :
    UnaryAdmissible C A := fun x => h _ (C.isClosed_closure {x}) (C.singleton_irreducible x)

/-- Domain reflection makes the image of a closure exactly the closure
of the image. This is about the displayed partial unary graphs. -/
theorem embedding_closure_image (e : Embedding C A) (B : Set V) :
    e.point '' C.closure B = A.closure (e.point '' B) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply C.closure_minimal (S := e.point ⁻¹' A.closure (e.point '' B)) ?_ ?_ hx
    · intro F y hy z hz
      exact A.isClosed_closure _ F (e.point y) hy (e.map_func F y z hz)
    · intro y hy
      exact A.subset_closure _ ⟨y,hy,rfl⟩
  · apply A.closure_minimal ?_ ?_
    · rintro F _ ⟨x,hx,rfl⟩ y hy
      obtain ⟨z,hz,rfl⟩ := e.reflect_func F x y hy
      exact ⟨z,C.isClosed_closure _ F x hx hz,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨x,C.subset_closure _ hx,rfl⟩

theorem singleton_embedding_image (x : V)
    (e : Embedding (C.singletonStructure x) A) :
    Set.range e.point = A.closureAt (e.point ⟨x,C.mem_closureAt x⟩) := by
  have h := embedding_closure_image e {⟨x,C.mem_closureAt x⟩}
  rw [C.singleton_generated,Set.image_univ,Set.image_singleton] at h
  exact h

/-- Actual total one-generated witnesses supply the displayed domains
already in the source. They do not add a missing function value. -/
theorem total_of_unary_admissible (h : UnaryAdmissible C A) (hA : A.Total) :
    C.Total := by
  intro F x hx
  obtain ⟨e⟩ := h x
  let root : C.closureAt x := ⟨x,C.mem_closureAt x⟩
  have hs : A.sort (e.point root) = L.input F := (e.sort_eq root).trans hx
  obtain ⟨y,hy⟩ := hA F (e.point root) hs
  obtain ⟨z,hz,_⟩ := e.reflect_func F root y hy
  exact ⟨z.val,hz⟩

theorem singleton_bound_of_unary_admissible [Finite V]
    (h : UnaryAdmissible C A) {m : ℕ}
    (hm : ∀ y, (A.closureAt y).Finite ∧ Nat.card (A.closureAt y) ≤ m) :
    ∀ x, Nat.card (C.closureAt x) ≤ m := by
  intro x
  obtain ⟨e⟩ := h x
  letI : Finite (A.closureAt (e.point ⟨x,C.mem_closureAt x⟩)) := (hm _).1.to_subtype
  let f : C.closureAt x → A.closureAt (e.point ⟨x,C.mem_closureAt x⟩) :=
    fun y => ⟨e.point y,(singleton_embedding_image x e) ▸ Set.mem_range_self y⟩
  have hf : Function.Injective f := fun y z he => e.injective (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective f hf).trans (hm _).2

/-- An explicitly displayed binary tuple joins precisely its OWN two
endpoints. Nothing here makes ancestors of those endpoints joined. -/
theorem displayed_binary_pair_irreducible (C : Structure L V)
    (R : L.Rel) (hR : L.arity R = 2) (b c : V)
    (hr : C.rel R (fun i => if i.val = 0 then b else c)) :
    (C.closureStructure {b,c}).Irreducible := by
  have h := CCO.HiddenSAPReadings.SourceSupport.displayed_tuple_closure_irreducible C R
    (fun i => if i.val = 0 then b else c) hr
  have he : Set.range (fun i : Fin (L.arity R) => if i.val = 0 then b else c) = {b,c} := by
    ext y
    constructor
    · rintro ⟨i,rfl⟩
      dsimp only
      split <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨0,by omega⟩,by simp⟩
      · exact ⟨⟨1,by omega⟩,by simp⟩
  rwa [he] at h

/-- The source pair uses one complete joined factor, rather than an
independent witness for each comparison in its diagram. -/
theorem joined_pair_witness (h : JoinedAdmissible C A) (b c : V)
    (hirr : (C.closureStructure {b,c}).Irreducible) :
    Nonempty (Embedding (C.closureStructure {b,c}) A) := h _ _ hirr

theorem pair_support_bound [Finite V] (h : UnaryAdmissible C A) {m : ℕ}
    (hm : ∀ y, (A.closureAt y).Finite ∧ Nat.card (A.closureAt y) ≤ m) (b c : V) :
    Nat.card (C.closure {b,c}) ≤ 2 * m := by
  classical
  simpa only [Finset.coe_insert,Finset.coe_singleton] using
    CCO.HiddenSAPReadings.SourceSupport.generated_support_card C {b,c}
    (show ({b,c} : Finset V).card ≤ 2 by simpa using (Finset.card_insert_le b ({c} : Finset V)))
    (fun x _ => singleton_bound_of_unary_admissible h hm x)

end Partial

section Actual
open CCO.HiddenSAPReadings CCO.UnaryFreshFrames
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.TerminalLattice
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

/-- Exact bridge: the partial-domain encoding and the accepted total
bookkeeping encoding have the same closure. Off-sort identities add no
vertex and are not displayed partial graphs. -/
theorem partialTarget_closure {L : Language.{u}} [Finite L.Sorts]
    [Finite L.Func] [Finite L.Rel] {Y : Type v}
    (D : CCO.UnaryFreshFrames.Structure L Y) (B : Set Y) :
    (partialTarget D).closure B = D.closure B := by
  apply Set.Subset.antisymm
  · exact (partialTarget D).closure_minimal
      ((partialTarget_closed_iff D _).mpr (D.closure_closed B)) (D.subset_closure B)
  · exact D.closure_minimal
      ((partialTarget_closed_iff D _).mp ((partialTarget D).isClosed_closure B))
      ((partialTarget D).subset_closure B)

theorem originalPartialTarget_total (nr2 : Selectors.OriginalNR2 S) :
    (originalPartialTarget S H sap nr2).Total := by
  classical
  intro F x hx
  change (originalCompletedStructure S H sap nr2).sort x =
    (originalCompletedLanguage S H sap nr2).input F at hx
  exact ⟨(originalCompletedStructure S H sap nr2).func F x,by
    change _ ∈ if _ then {_} else ∅
    rw [if_pos hx]
    rfl⟩

/-- Source14 C01 uses the actual accepted all-generator normal-code
budget, including orphan proper quotient generators. -/
theorem actual_unary_admissible_bound
    (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
    {P : Type z} [Finite P]
    (C : CCO.UnarySupport.Structure
      (originalPartialSignature S H sap (CCO.HereditaryHiddenOrbits.terminalNR2 S hCover)) P)
    (h : UnaryAdmissible C
      (originalPartialTarget S H sap (CCO.HereditaryHiddenOrbits.terminalNR2 S hCover))) :
    ∀ x, Nat.card (C.closureAt x) ≤ originalSourceUniformNormalCodeBudget S H := by
  apply singleton_bound_of_unary_admissible h
  intro y
  constructor
  · have he := partialTarget_closure
      (CCO.HereditaryHiddenOrbits.hidden S H sap hCover) {y}
    change ((originalPartialTarget S H sap
      (CCO.HereditaryHiddenOrbits.terminalNR2 S hCover)).closure {y}).Finite
    change (originalPartialTarget S H sap
      (CCO.HereditaryHiddenOrbits.terminalNR2 S hCover)).closure {y} = _ at he
    rw [he]
    exact CCO.HereditaryHiddenOrbits.locally_finite S H sap hCover {y} (Set.finite_singleton y)
  · have he := partialTarget_closure
      (CCO.HereditaryHiddenOrbits.hidden S H sap hCover) {y}
    change Nat.card ((originalPartialTarget S H sap
      (CCO.HereditaryHiddenOrbits.terminalNR2 S hCover)).closure {y}) ≤ _
    change (originalPartialTarget S H sap
      (CCO.HereditaryHiddenOrbits.terminalNR2 S hCover)).closure {y} = _ at he
    rw [he]
    exact CCO.HereditaryHiddenOrbits.singleton_bound S H sap hCover y

end Actual
end CCO.GuardedTwoRoot
