import CCO.ExactCRT.TypedPalette
import CCO.RawExact.ActualQuotientSource
import CCO.RawExact.MeetHelly

/-!
# Actual typed quotient-word pullbacks, without intertwining

C19 and C20 retain every intermediate kernel. The quotient palette is
constructed from the actual original group action. Quotient homogeneity,
SAP, countability and a group section are not premises.
-/
universe u v w q r t
namespace CCO.ExactCRT
open RawExact

/-- Pullback commutes with represented composition because the intermediate
quotient projection is onto. The discrepancy of real representatives is
already included in the two pulled-back relations. -/
theorem pullback_comp {A B C Q R U : Type*}
    (π : A → Q) (σ : B → R) (τ : C → U)
    (surjσ : Function.Surjective σ) (D : Q → R → Prop) (F : R → U → Prop) :
    GroupActions.pullback π τ (fun x z => ∃ y, D x y ∧ F y z) =
      (fun x z => ∃ y, GroupActions.pullback π σ D x y ∧
        GroupActions.pullback σ τ F y z) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hyD, hyF⟩
    obtain ⟨b, rfl⟩ := surjσ y
    exact ⟨b, hyD, hyF⟩
  · rintro ⟨b, hyD, hyF⟩
    exact ⟨σ b, hyD, hyF⟩

theorem pullback_injective {A B Q R : Type*} (π : A → Q) (σ : B → R)
    (surjπ : Function.Surjective π) (surjσ : Function.Surjective σ) :
    Function.Injective (GroupActions.pullback π σ) := by
  intro D F h
  funext q r
  obtain ⟨a, rfl⟩ := surjπ q
  obtain ⟨b, rfl⟩ := surjσ r
  exact congrFun (congrFun h a) b

section General
variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable {G : Type t} [Group G] [∀i, MulAction G (X i)] [∀i, MulAction G (Q i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (π : ∀i, X i → Q i) (surjπ : ∀i, Function.Surjective (π i))
variable (equivπ : ∀i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀i, NonemptyExact S i i)
variable (hE : ∀i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')

include hT

/-- The complete optional atomic relation at an actual quotient pair is
its actual original-group orbital, including the logical diagonal. -/
theorem quotient_pair_colour_orbit {i j : ι} (x : Q i) (y : Q j) :
    T.rawAtomRel (T.colour x y) = GroupActions.orbital (G := G) x y := by
  funext x' y'
  apply propext
  change T.colour x' y' = T.colour x y ↔ _
  exact eq_comm.trans (hT x y x' y')

include H equivπ hE

/-- C19's atomic block is the actual E_i;a;E_j inverse image. -/
theorem quotient_pair_block {i j : ι} (x : X i) (y : X j) :
    GroupActions.pullback (π i) (π j)
      (T.rawAtomRel (T.colour (π i x) (π j y))) =
      saturate (evaluate S (E i).words) (S.rawAtomRel (S.colour x y))
        (evaluate S (E j).words) := by
  rw [quotient_pair_colour_orbit T hT]
  rw [equivariant_orbit_pullback (π i) (π j) (equivπ i) (equivπ j) x y,
    hE i, hE j, actual_pair_orbital_of_homogeneous S H x y]

include cco surjπ

/-- C20 atomic exactness is constructed from the actual original orbital;
it is not supplied by an abstract quotient-colour table. -/
theorem quotient_atom_pullback_exact {i j : ι} (a : T.Atom i j) :
    ∃ D : NonemptyExact S i j, evaluate S D.words =
      GroupActions.pullback (π i) (π j) (T.atomRel a) := by
  obtain ⟨x, y, hxy⟩ := T.realized a
  obtain ⟨x', rfl⟩ := surjπ i x
  obtain ⟨y', rfl⟩ := surjπ j y
  obtain ⟨D, hD⟩ := exact_actual_orbit_pullback_of_CCO S H cco
    (π i) (π j) (equivπ i) (equivπ j) (E i) (E j) (hE i) (hE j) x' y'
  refine ⟨D, hD.trans ?_⟩
  apply congrArg (GroupActions.pullback (π i) (π j))
  have h := quotient_pair_colour_orbit T hT (π i x') (π j y')
  rw [hxy] at h
  exact h.symm

/-- An explicit original exact presentation for a quotient RAW word.
The nil case is the kernel E_i, rather than original real equality. -/
noncomputable def liftQuotientWord {i j : ι} : RawWord T i j → NonemptyExact S i j
  | .nil i => E i
  | .identity tail => liftQuotientWord tail
  | .atom a tail => convolutionExact S H
      (Classical.choose (quotient_atom_pullback_exact S T H cco π surjπ equivπ E hE hT a))
      (liftQuotientWord tail)

theorem liftQuotientWord_relation {i j : ι} (word : RawWord T i j) :
    evaluate S (liftQuotientWord S T H cco π surjπ equivπ E hE hT word).words =
      GroupActions.pullback (π i) (π j) (RawWord.relation T word) := by
  induction word with
  | nil i => exact (hE i).symm
  | identity tail ih => exact ih
  | @atom i j k a tail ih =>
      change evaluate S (convolutionExact S H _ _).words = _
      rw [convolutionExact_represents S H (heterogeneousExactBallHelly_of_CCO S H cco)]
      rw [Classical.choose_spec (quotient_atom_pullback_exact S T H cco π surjπ equivπ E hE hT a), ih]
      exact (pullback_comp (π i) (π j) (π k) (surjπ j)
        (T.atomRel a) (RawWord.relation T tail)).symm

/-- C20: arbitrary full exact quotient relations have original full exact
inverse images; finite intersections and the EMPTY restriction list are
retained literally. There is no intertwining premise in this theorem. -/
noncomputable def liftQuotientExact {i j : ι} (D : NonemptyExact T i j) :
    NonemptyExact S i j := by
  let L := D.words.map (liftQuotientWord S T H cco π surjπ equivπ E hE hT)
  refine ⟨flattenExact S L, ?_⟩
  obtain ⟨q, r, hqr⟩ := D.nonempty
  obtain ⟨x, rfl⟩ := surjπ i q
  obtain ⟨y, rfl⟩ := surjπ j r
  refine ⟨x, y, (flattenExact_evaluate S L x y).mpr ?_⟩
  intro d hd
  obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hd
  rw [liftQuotientWord_relation S T H cco π surjπ equivπ E hE hT]
  exact hqr word hw

theorem liftQuotientExact_relation {i j : ι} (D : NonemptyExact T i j) :
    evaluate S (liftQuotientExact S T H cco π surjπ equivπ E hE hT D).words =
      GroupActions.pullback (π i) (π j) (evaluate T D.words) := by
  funext x y
  apply propext
  change evaluate S (flattenExact S _) x y ↔ _
  rw [flattenExact_evaluate S]
  constructor
  · intro h word hw
    have hword := h (liftQuotientWord S T H cco π surjπ equivπ E hE hT word)
      (List.mem_map.mpr ⟨word, hw, rfl⟩)
    rw [liftQuotientWord_relation S T H cco π surjπ equivπ E hE hT] at hword
    exact hword
  · intro h d hd
    obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hd
    rw [liftQuotientWord_relation S T H cco π surjπ equivπ E hE hT]
    exact h word hw
end General

section Actual
variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀i, MulAction G (X i)] [∀i, MulAction G (Q i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (π : ∀i, X i → Q i) (surjπ : ∀i, Function.Surjective (π i))
variable (equivπ : ∀i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀i, NonemptyExact S i i)
variable (hE : ∀i, GroupActions.kernel (π i) = evaluate S (E i).words)

include hE

/-- Source-complete typed quotient pullback in the ACTUAL constructed
orbital language. Its colour-orbit interface is proved by TypedPalette. -/
noncomputable def actualQuotientExactPullback {i j : ι}
    (D : letI := S.finiteSort
      NonemptyExact (TypedPalette.source Q S H id π surjπ equivπ) i j) :
    NonemptyExact S i j := by
  letI := S.finiteSort
  exact liftQuotientExact S (TypedPalette.source Q S H id π surjπ equivπ)
    H cco π surjπ equivπ E hE
    (TypedPalette.source_colour_eq_iff_orbital Q S H id π surjπ equivπ) D

theorem actualQuotientExactPullback_relation {i j : ι}
    (D : letI := S.finiteSort
      NonemptyExact (TypedPalette.source Q S H id π surjπ equivπ) i j) :
    letI := S.finiteSort
    evaluate S (actualQuotientExactPullback S H cco π surjπ equivπ E hE D).words =
      GroupActions.pullback (π i) (π j)
        (evaluate (TypedPalette.source Q S H id π surjπ equivπ) D.words) := by
  letI := S.finiteSort
  exact liftQuotientExact_relation S (TypedPalette.source Q S H id π surjπ equivπ)
    H cco π surjπ equivπ E hE
    (TypedPalette.source_colour_eq_iff_orbital Q S H id π surjπ equivπ) D

/-- The genuine zero-letter quotient word pulls back to the supplied
actual kernel, even when this kernel is larger than real equality. -/
theorem quotient_empty_word_pullback (i : ι) :
    GroupActions.pullback (π i) (π i)
      (TRel.ident Q i) = evaluate S (E i).words := hE i

end Actual
end CCO.ExactCRT
