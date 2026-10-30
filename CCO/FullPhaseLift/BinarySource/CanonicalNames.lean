import CCO.FullPhaseLift.Canonical.Source
import CCO.FullPhaseLift.BinarySource.SmallProfiles
import CCO.FullPhaseLift.BinarySource.AtomicHomogeneity

/-! The actual binary table is on the SAME old carrier. Its full old
automorphisms preserve all canonical pair names, but its own homogeneous
group is constructed separately by countable finite extension. -/

universe u v
namespace CCO.FullPhaseLift.BinarySource
open Canonical OwnerTransversal.CountableColour
open APCharacter.SourceAge
noncomputable section

def pairTable {L : Signature} {M : Type u} (U : BoolTable L M)
    (hsym : SameSortSymmetric U) :
    Table (UnaryName U)
      (Σ i, Σ j, Option ((source U hsym).Atom i j)) M where
  owner x := (pack U x).1
  colour x y := taggedColour (source U hsym) (pack U x) (pack U y)

theorem pairTable_invariant {L : Signature} {M : Type u} (U : BoolTable L M)
    (hsym : SameSortSymmetric U) (a : Iso U U) :
    (∀ x, (pairTable U hsym).owner (a.point x) = (pairTable U hsym).owner x) ∧
      ∀ x y, (pairTable U hsym).colour (a.point x) (a.point y) =
        (pairTable U hsym).colour x y := by
  constructor
  · intro x
    exact pack_owner_embedding a.toEmbedding (.identity (toRelational U)) x
  · intro x y
    exact pack_taggedColour_embedding hsym a.toEmbedding (.identity (toRelational U)) x y

theorem small_truth_of_pair_names {L : Signature} {M : Type u} {V : Type v}
    (U : BoolTable L M) (hsym : SameSortSymmetric U) (p q : V → M)
    (pairs : ∀ x y, (pairTable U hsym).colour (p x) (p y) =
      (pairTable U hsym).colour (q x) (q y))
    (r : Fin L.size) (xs : Fin (L.arity r) → V)
    (small : ∀ i j k, xs i = xs j ∨ xs i = xs k ∨ xs j = xs k) :
    U r (p ∘ xs) = U r (q ∘ xs) := by
  apply small_truth_of_pair_profiles U p q _ r xs small
  intro x y
  exact pairProfile_of_taggedColour_eq U hsym (pairs x y)

/-- The same actual finite extension, transported along the literal old
carrier/typed-carrier equivalence. No binary model is replaced by an
unrelated homogeneous realization. -/
theorem source_finiteExtension {L : Signature} {M : Type u} (U : BoolTable L M)
    (hsym : SameSortSymmetric U)
    (ext : FiniteExtension (pairTable U hsym) (pairTable U hsym)) :
    FiniteExtension (sourceTable (source U hsym)) (sourceTable (source U hsym)) := by
  intro n m j p q hnames
  let p' : Fin m ↪ M := p.trans (pack U).symm.toEmbedding
  let q' : Fin n ↪ M := q.trans (pack U).symm.toEmbedding
  have hn : (∀ x, (pairTable U hsym).owner (q' x) =
      (pairTable U hsym).owner (p' (j x))) ∧
      (∀ x y, (pairTable U hsym).colour (q' x) (q' y) =
        (pairTable U hsym).colour (p' (j x)) (p' (j y))) := by
    constructor
    · intro x
      change (pack U ((pack U).symm (q x))).1 =
        (pack U ((pack U).symm (p (j x)))).1
      simpa only [sourceTable,Equiv.apply_symm_apply] using hnames.1 x
    · intro x y
      change taggedColour (source U hsym) (pack U ((pack U).symm (q x)))
        (pack U ((pack U).symm (q y))) =
        taggedColour (source U hsym) (pack U ((pack U).symm (p (j x))))
          (pack U ((pack U).symm (p (j y))))
      simpa only [sourceTable,Equiv.apply_symm_apply] using hnames.2 x y
  obtain ⟨r,ho,hc,he⟩ := ext n m j p' q' hn
  let s : Fin m ↪ Sigma (Carrier U) := r.trans (pack U).toEmbedding
  refine ⟨s,?_,?_,?_⟩
  · intro x
    change (pack U (r x)).1 = (p x).1
    exact (ho x).trans (congrArg Sigma.fst ((pack U).apply_symm_apply (p x)))
  · intro x y
    change taggedColour (source U hsym) (pack U (r x)) (pack U (r y)) =
      taggedColour (source U hsym) (p x) (p y)
    have h := hc x y
    change taggedColour (source U hsym) (pack U (r x)) (pack U (r y)) =
      taggedColour (source U hsym) (pack U ((pack U).symm (p x)))
        (pack U ((pack U).symm (p y))) at h
    simpa only [Equiv.apply_symm_apply] using h
  · intro x
    change pack U (r (j x)) = q x
    rw [he]
    exact (pack U).apply_symm_apply _

theorem canonical_homogeneous {L : Signature} {M : Type u} [Countable M]
    (U : BoolTable L M) (hsym : SameSortSymmetric U)
    (ext : FiniteExtension (pairTable U hsym) (pairTable U hsym)) :
    HomogeneousSource (source U hsym) (TerminalPowers.FullAut (source U hsym)) := by
  letI : Countable (Sigma (Carrier U)) := (pack U).symm.injective.countable
  exact homogeneous_of_finiteExtension _ (source_finiteExtension U hsym ext)

end
end CCO.FullPhaseLift.BinarySource
