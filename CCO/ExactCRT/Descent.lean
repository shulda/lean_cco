import CCO.ExactCRT.ProjectedWords
import CCO.ExactCRT.ExactWordDistribution

/-!
# Actual full exact descent under presentation-local intertwining

C23 removes intermediate kernels only for letters in the chosen finite
presentation. C24 keeps endpoint saturation explicitly. The converse
pullback theorem in TypedPullback requires no intertwining whatsoever.
-/
universe u v w q r t
namespace CCO.ExactCRT
open RawExact

/-- The actual relation induced on two surjective quotient sorts. -/
def quotientRelation {A B Q R : Type*} (π : A → Q) (σ : B → R)
    (D : A → B → Prop) : Q → R → Prop :=
  fun q r => ∃ x y, π x = q ∧ σ y = r ∧ D x y

/-- The literal inverse image of the induced relation is its two-sided
kernel saturation. This statement uses no exactness or group action. -/
theorem pullback_quotientRelation {ι : Type*} {X : ι → Type*}
    {i j : ι} {Q R : Type*} (π : X i → Q) (σ : X j → R)
    (D : TRel X i j) :
    GroupActions.pullback π σ (quotientRelation π σ D) =
      saturate (GroupActions.kernel π) D (GroupActions.kernel σ) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨b, ⟨a, ha.symm, hab⟩, hb⟩
  · rintro ⟨b, ⟨a, ha, hab⟩, hb⟩
    exact ⟨a, b, ha.symm, hb, hab⟩

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
include H cco surjπ equivπ hE hT

/-- The exact meet distribution is applied only with its actual NONEMPTY
result. The empty list remains typed Top, handled by the source serial laws. -/
theorem projectedPresentation_pullback {i j : ι} (D : NonemptyExact S i j)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E j).words) = evaluate S D.words)
    (hTI : ∀ word, word ∈ D.words → WordTI S (fun i => evaluate S (E i).words) word) :
    GroupActions.pullback (π i) (π j)
      (evaluate T (D.words.map (projectedWord S T π))) = evaluate S D.words := by
  calc
    GroupActions.pullback (π i) (π j)
        (evaluate T (D.words.map (projectedWord S T π))) =
        (fun x y => ∀ word, word ∈ D.words →
          saturate (evaluate S (E i).words) (RawWord.relation S word)
            (evaluate S (E j).words) x y) := by
      funext x y
      apply propext
      constructor
      · intro h word hw
        have hp := h (projectedWord S T π word) (List.mem_map.mpr ⟨word, hw, rfl⟩)
        have heq := projectedWord_pullback_of_TI S T π H equivπ E hE hT surjπ word (hTI word hw)
        exact Eq.mp (congrArg (fun R => R x y) heq) hp
      · intro h word hw
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hw
        have heq := projectedWord_pullback_of_TI S T π H equivπ E hE hT surjπ old (hTI old hold)
        exact Eq.mpr (congrArg (fun R => R x y) heq) (h old hold)
    _ = saturate (evaluate S (E i).words) (evaluate S D.words)
        (evaluate S (E j).words) := (saturation_evaluate_words S H cco (E i) (E j) D).symm
    _ = evaluate S D.words := hSat

/-- The descended full exact relation is constructed by projecting each
old word to ONE quotient word. It is not an extra descent provider. -/
noncomputable def descendExact {i j : ι} (D : NonemptyExact S i j)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E j).words) = evaluate S D.words)
    (hTI : ∀ word, word ∈ D.words → WordTI S (fun i => evaluate S (E i).words) word) :
    NonemptyExact T i j := by
  refine ⟨D.words.map (projectedWord S T π), ?_⟩
  obtain ⟨x, y, hxy⟩ := D.nonempty
  refine ⟨π i x, π j y, ?_⟩
  have heq := projectedPresentation_pullback S T H cco π surjπ equivπ E hE hT D hSat hTI
  exact Eq.mpr (congrArg (fun R => R x y) heq) hxy

/-- C24 in the actual supplied orbital language, with all source providers
except the explicitly displayed colour-orbit interface already proved. -/
theorem descendExact_relation {i j : ι} (D : NonemptyExact S i j)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E j).words) = evaluate S D.words)
    (hTI : ∀ word, word ∈ D.words → WordTI S (fun i => evaluate S (E i).words) word) :
    evaluate T (descendExact S T H cco π surjπ equivπ E hE hT D hSat hTI).words =
      quotientRelation (π i) (π j) (evaluate S D.words) := by
  apply pullback_injective (π i) (π j) (surjπ i) (surjπ j)
  change GroupActions.pullback (π i) (π j)
    (evaluate T (D.words.map (projectedWord S T π))) = _
  rw [projectedPresentation_pullback S T H cco π surjπ equivπ E hE hT D hSat hTI,
    pullback_quotientRelation (π i) (π j), hE i, hE j, hSat]

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
include H cco surjπ equivπ hE

/-- Source-complete C24: the quotient language and its real orbital
interface are constructed, so no descent/representation provider remains. -/
theorem actual_typed_exact_descent {i j : ι} (D : NonemptyExact S i j)
    (hSat : saturate (evaluate S (E i).words) (evaluate S D.words)
      (evaluate S (E j).words) = evaluate S D.words)
    (hTI : ∀ word, word ∈ D.words → WordTI S (fun i => evaluate S (E i).words) word) :
    letI := S.finiteSort
    ∃ F : NonemptyExact (TypedPalette.source Q S H id π surjπ equivπ) i j,
      evaluate (TypedPalette.source Q S H id π surjπ equivπ) F.words =
        quotientRelation (π i) (π j) (evaluate S D.words) := by
  letI := S.finiteSort
  let T := TypedPalette.source Q S H id π surjπ equivπ
  let hT : ∀ {k l} (x : Q k) (y : Q l) (x' : Q k) (y' : Q l),
      T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y' :=
    TypedPalette.source_colour_eq_iff_orbital Q S H id π surjπ equivπ
  exact ⟨descendExact S T H cco π surjπ equivπ E hE hT D hSat hTI,
    descendExact_relation S T H cco π surjπ equivπ E hE hT D hSat hTI⟩
end Actual
end CCO.ExactCRT
