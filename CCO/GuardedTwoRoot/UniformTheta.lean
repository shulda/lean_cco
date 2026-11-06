import CCO.GuardedTwoRoot.TypedPrefixBounds
import CCO.StrongExact.ThetaVertices
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Uniform formal vertex counts and one fixed theta per actual exact
menu. The old source/SAP discharges the positive prefix algebra. The
remaining comparison and anchor bounds are finite counts supplied by
the actual named-language consumer, not completion/Helly providers. -/

universe u v w r z
namespace CCO.GuardedTwoRoot
open CCO.StrongExact
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

theorem word_positions_card {i j : ι} (word : PositiveWord S i j) :
    Nat.card (wordPositions S word) = TypedPrefix.length S word + 1 := by
  induction word with
  | single a =>
    simp only [wordPositions, TypedPrefix.length, Nat.card_eq_fintype_card,
      Fintype.card_bool]
  | cons a rest ih =>
    letI : Finite (wordPositions S rest) := finite_wordPositions S rest
    letI : Fintype (wordPositions S rest) := Fintype.ofFinite _
    simpa only [wordPositions, TypedPrefix.length, Nat.card_eq_fintype_card,
      Fintype.card_option] using congrArg (fun n : ℕ => n + 1) ih

/-- A positive line has exactly length−1 STRICT private positions. -/
theorem word_interior_card {i j : ι} (word : PositiveWord S i j) :
    Nat.card (wordInterior S word) = TypedPrefix.length S word - 1 := by
  classical
  letI : Finite (wordPositions S word) := finite_wordPositions S word
  letI : Fintype (wordPositions S word) := Fintype.ofFinite _
  letI : Finite (wordInterior S word) := finite_wordInterior S word
  letI : Fintype (wordInterior S word) := by
    dsimp only [wordInterior]
    infer_instance
  have hEnds := Fintype.card_subtype_eq_or_eq_of_ne (wordSource_ne_target S word)
  have hCompl := Fintype.card_subtype_compl
    (fun p : wordPositions S word => p = wordSource S word ∨ p = wordTarget S word)
  simp only [not_or] at hCompl
  change Fintype.card (wordInterior S word) = Fintype.card (wordPositions S word) -
    Fintype.card {p : wordPositions S word // p = wordSource S word ∨ p = wordTarget S word} at hCompl
  rw [hEnds] at hCompl
  rw [Nat.card_eq_fintype_card,hCompl,← Nat.card_eq_fintype_card,word_positions_card]
  have := TypedPrefix.length_pos S word
  omega

/-- The ACTUAL accepted B003 theta carrier, not a proxy cardinal. -/
theorem theta_vertices_card {i j : ι} (words : List (PositiveWord S i j)) :
    Nat.card (thetaVertices S words) =
      2 + ∑ k : Fin words.length, (TypedPrefix.length S (words.get k) - 1) := by
  letI (k : Fin words.length) := finite_wordInterior S (words.get k)
  change Nat.card (Bool ⊕ (Σ k : Fin words.length, wordInterior S (words.get k))) = _
  rw [Nat.card_sum,Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, Fintype.card_bool, word_interior_card]

/-- C28's explicit path-vertex bound. Direct words contribute zero
interior vertices, and the two formal roots always remain distinct. -/
theorem theta_vertices_le {i j : ι} (words : List (PositiveWord S i j))
    (L s : ℕ) (hCount : words.length ≤ L)
    (hLength : ∀ word ∈ words, TypedPrefix.length S word ≤ s) :
    Nat.card (thetaVertices S words) ≤ 2 + L * (s - 1) := by
  rw [theta_vertices_card]
  calc
    2 + ∑ k : Fin words.length, (TypedPrefix.length S (words.get k) - 1) ≤
        2 + ∑ _k : Fin words.length, (s - 1) :=
      Nat.add_le_add_left (Finset.sum_le_sum (fun k _ =>
        Nat.sub_le_sub_right (hLength _ (List.get_mem words k)) 1)) 2
    _ = 2 + words.length * (s - 1) := by simp
    _ ≤ 2 + L * (s - 1) := Nat.add_le_add_left (Nat.mul_le_mul_right (s - 1) hCount) 2

def comparisonBound (u R : ℕ) : ℕ := R * (2 * u) ^ 2

/-- C23: the finite actual value-pair/record count. The consumer must
derive u and R from its actual singleton closures and named records. -/
theorem comparison_records_bound {Values : Type z} [Finite Values]
    (u R : ℕ) (hValues : Nat.card Values ≤ 2 * u) :
    Nat.card ((Values × Values) × Fin R) ≤ comparisonBound u R := by
  have h := Nat.mul_le_mul_right R (Nat.mul_le_mul hValues hValues)
  simpa only [Nat.card_prod,Nat.card_fin,comparisonBound,Nat.pow_two,Nat.mul_comm] using h

abbrev ExactMenu := Σ i : ι, Σ j : ι, {D : S.Menu i j // Exact S D}

instance exactMenu_finite : Finite (ExactMenu S) := by
  classical
  letI : Fintype ι := S.finiteSort
  letI (i j : ι) : Fintype (S.Atom i j) := S.finiteAtom i j
  letI (i j : ι) : Fintype (S.Menu i j) := Fintype.ofFinite _
  infer_instance

section Source
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

def shortWord {i j : ι} (word : PositiveWord S i j) : PositiveWord S i j :=
  (TypedPrefix.bounded_positive_presentation S H sap (PositiveWord.profile S word) ⟨word,rfl⟩).choose

theorem shortWord_profile {i j : ι} (word : PositiveWord S i j) :
    PositiveWord.profile S (shortWord S H sap word) = PositiveWord.profile S word :=
  (TypedPrefix.bounded_positive_presentation S H sap (PositiveWord.profile S word) ⟨word,rfl⟩).choose_spec.1

theorem shortWord_length {i j : ι} (word : PositiveWord S i j) :
    TypedPrefix.length S (shortWord S H sap word) ≤ Nat.card (TypedPrefix.State S) :=
  (TypedPrefix.bounded_positive_presentation S H sap (PositiveWord.profile S word) ⟨word,rfl⟩).choose_spec.2.2

theorem present_short_words {i j : ι} (words : List (PositiveWord S i j)) :
    present S (words.map (shortWord S H sap)) = present S words := by
  ext a
  constructor
  · intro h word hWord
    have hm := h (shortWord S H sap word) (List.mem_map.mpr ⟨word,hWord,rfl⟩)
    rwa [shortWord_profile] at hm
  · rintro h word hWord
    obtain ⟨original,hOriginal,rfl⟩ := List.mem_map.mp hWord
    rw [shortWord_profile]
    exact h original hOriginal

/-- C27: one fixed finite presentation per actual nonempty exact
typed menu. It is chosen ONCE, independently of C or representatives. -/
def fixedTheta (D : ExactMenu S) : List (PositiveWord S D.1 D.2.1) :=
  D.2.2.property.2.choose.map (shortWord S H sap)

theorem fixedTheta_menu (D : ExactMenu S) : present S (fixedTheta S H sap D) = D.2.2.val := by
  rw [fixedTheta,present_short_words]
  exact D.2.2.property.2.choose_spec.symm

theorem fixedTheta_word_length (D : ExactMenu S) :
    ∀ word ∈ fixedTheta S H sap D,
      TypedPrefix.length S word ≤ Nat.card (TypedPrefix.State S) := by
  intro word hWord
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp hWord
  exact shortWord_length S H sap original

/-- A finite maximum over the fixed language's actual exact-menu
family; this is independent of unbounded input syntax. -/
def canonicalThetaBudget : ℕ :=
  letI : Fintype (ExactMenu S) := Fintype.ofFinite _
  Finset.univ.sup (fun D : ExactMenu S => Nat.card (thetaVertices S (fixedTheta S H sap D)))

theorem fixedTheta_vertices_le (D : ExactMenu S) :
    Nat.card (thetaVertices S (fixedTheta S H sap D)) ≤ canonicalThetaBudget S H sap := by
  classical
  letI : Fintype (ExactMenu S) := Fintype.ofFinite _
  change Nat.card (thetaVertices S (fixedTheta S H sap D)) ≤
    (Finset.univ : Finset (ExactMenu S)).sup
      (fun E : ExactMenu S => Nat.card (thetaVertices S (fixedTheta S H sap E)))
  exact Finset.le_sup (Finset.mem_univ D)

/-- The pair bound includes either the direct bounded comparison list
or its fixed exact-menu presentation, plus the actual root anchor budget. -/
def pairBudget (u R anchorBudget : ℕ) : ℕ :=
  max (2 + comparisonBound u R * (Nat.card (TypedPrefix.State S) - 1))
    (canonicalThetaBudget S H sap) + anchorBudget

theorem uniform_pair_gadget_bound {i j : ι} (words : List (PositiveWord S i j))
    (D : ExactMenu S) (u R anchorBudget anchors : ℕ)
    (hCount : words.length ≤ comparisonBound u R)
    (hLength : ∀ word ∈ words, TypedPrefix.length S word ≤ Nat.card (TypedPrefix.State S))
    (hAnchors : anchors ≤ anchorBudget) :
    Nat.card (thetaVertices S words) + anchors ≤ pairBudget S H sap u R anchorBudget ∧
      Nat.card (thetaVertices S (fixedTheta S H sap D)) + anchors ≤
        pairBudget S H sap u R anchorBudget := by
  constructor
  · have hFirst := theta_vertices_le S words _ _ hCount hLength
    have hMax : 2 + comparisonBound u R * (Nat.card (TypedPrefix.State S) - 1) ≤
        max (2 + comparisonBound u R * (Nat.card (TypedPrefix.State S) - 1))
          (canonicalThetaBudget S H sap) := le_max_left _ _
    exact Nat.add_le_add (hFirst.trans hMax) hAnchors
  · have hMax : canonicalThetaBudget S H sap ≤
        max (2 + comparisonBound u R * (Nat.card (TypedPrefix.State S) - 1))
          (canonicalThetaBudget S H sap) := le_max_right _ _
    exact Nat.add_le_add ((fixedTheta_vertices_le S H sap D).trans hMax) hAnchors

end Source
end
end CCO.GuardedTwoRoot
