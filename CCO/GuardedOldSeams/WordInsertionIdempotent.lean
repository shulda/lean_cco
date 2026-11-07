import CCO.GuardedOldSeams.Envelope
import CCO.GuardedOldSeams.Simultaneous

/-! The off-diagonal idempotent interval specialization inserts the
specified ORIGINAL word.  Its envelope supplies the actual fine pair
colour, and the proved SAP construction supplies one finite complete old
extension.  Neither CCO nor NR2 nor exactness of arbitrary invariants is
an input. -/

universe u v a t

namespace CCO.GuardedOldSeams

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,a} ι X)

/-- C55: distinct actual roots remove the identity alternative from the
equivalence envelope; what remains is their true fine diversity atom. -/
theorem idempotent_distinct_endpoint_atom {i : ι} (w : PositiveWord S i i)
    (he : S.product (PositiveWord.profile S w) (PositiveWord.profile S w) =
      PositiveWord.profile S w) {x y : X i} (hne : x ≠ y)
    (hE : envelope S (PositiveWord.profile S w) he x y) :
    ∃ b ∈ PositiveWord.profile S w, S.colour x y = some b :=
  (envelope_distinct_iff S (PositiveWord.profile S w) he hne).mp hE

/-- A single complete-base insertion records the same literal old points,
all of their inherited colours, and every position of the original word. -/
structure CompleteWordInsertion (A : FiniteInduced (X := X)) {i j : ι}
    (w : PositiveWord S i j) (x : X i) (y : X j) where
  base : FiniteInduced (X := X)
  endpoints_old : (⟨i, x⟩ : Sigma X) ∈ A.vertices ∧
    (⟨j, y⟩ : Sigma X) ∈ A.vertices
  old_subset : A.vertices ⊆ base.vertices
  line : FreshWordLine S w x y A.vertices
  line_subset : lineRange S line.toLiteralLine ⊆ base.vertices

def CompleteWordInsertion.old_embedding (A : FiniteInduced (X := X)) {i j : ι}
    {w : PositiveWord S i j} {x : X i} {y : X j}
    (out : CompleteWordInsertion S A w x y) : InducedEmbedding S A out.base where
  toEmbedding := {
    toFun := fun p => ⟨p.val, out.old_subset p.property⟩
    inj' := fun _ _ h => Subtype.ext
      (congrArg (fun p : ↥out.base.vertices => p.val) h) }
  preserves_sort _ := rfl
  preserves_colours _ _ := rfl

/-- The generic exact-word/complete-base theorem needs only the actual
specified endpoint-profile premise and visible SAP. -/
theorem word_insertion_over_complete_base
    {G : Type t} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (A : FiniteInduced (X := X)) {i j : ι} (w : PositiveWord S i j)
    (b : S.Atom i j) (hb : b ∈ PositiveWord.profile S w)
    (x : X i) (y : X j) (hxy : S.colour x y = some b)
    (endpoints : (⟨i, x⟩ : Sigma X) ∈ A.vertices ∧
      (⟨j, y⟩ : Sigma X) ∈ A.vertices) :
    Nonempty (CompleteWordInsertion S A w x y) := by
  obtain ⟨line⟩ := fresh_word_line_of_profile S H sap w b hb x y hxy
    A.vertices A.finite_vertices
  exact ⟨{
    base := extendBase S A line.toLiteralLine
    endpoints_old := endpoints
    old_subset := old_subset_extendBase S A line.toLiteralLine
    line := line
    line_subset := fun _ h => Or.inr h }⟩

/-- C55--C58: the whole original positive idempotent word is reinserted
between its prescribed DISTINCT roots, private over the entire old base. -/
theorem idempotent_word_reinsertion
    {G : Type t} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (A : FiniteInduced (X := X)) {i : ι} (w : PositiveWord S i i)
    (he : S.product (PositiveWord.profile S w) (PositiveWord.profile S w) =
      PositiveWord.profile S w)
    (x y : X i) (hne : x ≠ y)
    (hE : envelope S (PositiveWord.profile S w) he x y)
    (endpoints : (⟨i, x⟩ : Sigma X) ∈ A.vertices ∧
      (⟨i, y⟩ : Sigma X) ∈ A.vertices) :
    Nonempty (CompleteWordInsertion S A w x y) := by
  obtain ⟨b, hb, hxy⟩ := idempotent_distinct_endpoint_atom S w he hne hE
  exact word_insertion_over_complete_base S H sap A w b hb x y hxy endpoints

end CCO.GuardedOldSeams
