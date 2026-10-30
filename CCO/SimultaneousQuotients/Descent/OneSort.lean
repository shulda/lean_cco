import CCO.ExactCRT.CanonicalTypedQuotients
import CCO.RigidGroupoid.Geometry.Quotient.Blocks
import Mathlib.Data.Setoid.Basic

/-! One-original-sort reverse exact descent. No containment E≤D is required:
actual E-bisaturation is the precise hypothesis. The word-intertwining proof
comes from symmetric original orbitals and is not supplied by a caller. -/

universe v w t
namespace CCO.SimultaneousQuotients.Descent
open RawExact RigidGroupoid.Geometry

variable {X : Unit → Type v} (S : AtomicSource.{0,v,w} Unit X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)

include H

/-- C01-C02: pair flips make every invariant relation symmetric and make
actual represented products commute. This uses one original sort only. -/
theorem invariant_commute (R U : TRel X () ())
    (hR : TRel.Invariant (G := G) R) (hU : TRel.Invariant (G := G) U) :
    TRel.comp R U = TRel.comp U R :=
  RawSymmetric.invariant_commute R U hR hU (S.pair_flip_of_homogeneous H)

/-- Every invariant original one-sort relation is symmetric. -/
theorem invariant_symmetric (R : TRel X () ())
    (hR : TRel.Invariant (G := G) R) : TRel.converse R = R := by
  funext x y
  apply propext
  constructor
  · intro hyx
    obtain ⟨g,hgy,hgx⟩ := S.pair_flip_of_homogeneous H y x
    simpa only [hgy,hgx] using hR g y x hyx
  · intro hxy
    change R y x
    obtain ⟨g,hgx,hgy⟩ := S.pair_flip_of_homogeneous H x y
    simpa only [hgx,hgy] using hR g x y hxy

/-- TQ5 retains nonemptiness of the entire old exact meet. -/
theorem saturation_formula (cco : SemanticCCO.{0,v,v,w} S) {i : Unit}
    (D : NonemptyExact S i i)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E i).words) = evaluate S D.words) :
    evaluate S D.words = (fun x y => ∀ word, word ∈ D.words →
      saturate (evaluate S (E i).words) (RawWord.relation S word)
        (evaluate S (E i).words) x y) := by
  rw [←hSat]
  exact ExactCRT.saturation_evaluate_words S H cco (E i) (E i) D

/-- C03-C07, including the empty old word: projecting each actual old
letter gives one quotient word whose inverse image is E;word;E. -/
theorem word_pullback {i j : Unit} (word : RawWord S i j) :
    letI : ∀ i, MulAction G (Quotient (J i)) :=
      ExactCRT.CanonicalTyped.action S H J E represents
    GroupActions.pullback (ExactCRT.CanonicalTyped.projection J i)
      (ExactCRT.CanonicalTyped.projection J j)
      (RawWord.relation (ExactCRT.CanonicalTyped.source S H J E represents)
        (ExactCRT.projectedWord S (ExactCRT.CanonicalTyped.source S H J E represents)
          (ExactCRT.CanonicalTyped.projection J) word)) =
      saturate (evaluate S (E i).words) (RawWord.relation S word)
        (evaluate S (E j).words) := by
  letI := S.finiteSort
  letI : ∀ i, MulAction G (Quotient (J i)) :=
    ExactCRT.CanonicalTyped.action S H J E represents
  exact ExactCRT.sameSort_projected_word_pullback S _ H E
    (ExactCRT.CanonicalTyped.projection J)
    (ExactCRT.CanonicalTyped.projection_surjective J)
    (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents)
    (ExactCRT.CanonicalTyped.projection_kernel S J E represents)
    (ExactCRT.TypedPalette.source_colour_eq_iff_orbital _ S H id
      (ExactCRT.CanonicalTyped.projection J)
      (ExactCRT.CanonicalTyped.projection_surjective J)
      (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents)) word

/-- C08-C09 / TQ5: every nonempty bisaturated old exact relation descends.
The empty restriction list is top. This is a theorem on literal quotient
carriers and their constructed finite actual orbital language. -/
theorem exact_descent (cco : SemanticCCO.{0,v,v,w} S) {i : Unit}
    (D : NonemptyExact S i i)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E i).words) = evaluate S D.words) :
    ∃ F : NonemptyExact (ExactCRT.CanonicalTyped.source S H J E represents) i i,
      evaluate (ExactCRT.CanonicalTyped.source S H J E represents) F.words =
        ExactCRT.quotientRelation (ExactCRT.CanonicalTyped.projection J i)
          (ExactCRT.CanonicalTyped.projection J i) (evaluate S D.words) := by
  apply ExactCRT.CanonicalTyped.typed_exact_descent S H J E represents cco D hSat
  intro word _
  exact ExactCRT.oneSort_wordTI S H E word

/-- C10: an exact equivalence K≥E satisfies the saturation hypothesis;
its actual quotient relation is both an equivalence and full exact. -/
theorem equivalence_descent (cco : SemanticCCO.{0,v,v,w} S) {i : Unit}
    (K : Setoid (X i)) (D : NonemptyExact S i i)
    (hD : evaluate S D.words = K.r) (hJK : J i ≤ K) :
    ∃ L : Setoid (Quotient (J i)),
      L.r = ExactCRT.quotientRelation (ExactCRT.CanonicalTyped.projection J i)
        (ExactCRT.CanonicalTyped.projection J i) K.r ∧
      FullExact (ExactCRT.CanonicalTyped.source S H J E represents) L.r := by
  let π := ExactCRT.CanonicalTyped.projection J i
  have hk : Setoid.ker π ≤ K := by
    intro x y hxy
    exact hJK (Quotient.exact hxy)
  let L := K.mapOfSurjective π hk (ExactCRT.CanonicalTyped.projection_surjective J i)
  have hL : L.r = ExactCRT.quotientRelation π π K.r := by
    funext q r
    apply propext
    constructor <;> rintro ⟨x,y,h₁,h₂,h₃⟩
    · exact ⟨x,y,h₂,h₃,h₁⟩
    · exact ⟨x,y,h₃,h₁,h₂⟩
  have hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E i).words) = evaluate S D.words := by
    rw [represents i,hD]
    funext x y
    apply propext
    constructor
    · rintro ⟨b,⟨a,hxa,hab⟩,hby⟩
      exact K.trans (K.trans (hJK hxa) hab) (hJK hby)
    · intro hxy
      exact ⟨y,⟨x,(J i).refl x,hxy⟩,(J i).refl y⟩
  obtain ⟨F,hF⟩ := exact_descent S H J E represents cco D hSat
  refine ⟨L,hL,⟨F,?_⟩⟩
  rw [hL,←hD]
  exact hF

end CCO.SimultaneousQuotients.Descent
