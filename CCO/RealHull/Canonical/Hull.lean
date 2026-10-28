import CCO.RealHull.Canonical.Carrier
import CCO.RealHull.Canonical.EvenWalk
import CCO.RealHull.Canonical.Loopless
import CCO.RealHull.Geometry.ClassSizes

/-! The canonical hull is the ORIGINAL intersection of generated connectivity
classes. It contains the actual stabilizer orbit but need not equal that fibre.
Its finiteness is proved by Ramsey BEFORE any Nat.card/two-power argument. -/
universe v w t
namespace CCO.RealHull.Canonical
open Geometry ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)

def canonicalSupport : Support S :=
  ⟨{r | ∀ a : ↥A, r ∈ (gamma S (q a)).val}, by
    rintro c hc
    cases c with
    | none => exact none_mem_plus S _
    | some r =>
      apply (some_mem_plus S _ r).mpr
      intro a
      apply (some_mem_plus S _ r).mp
      apply (gamma S (q a)).property
      apply prod_mono S (B := plus S {r | ∀ a : ↥A, r ∈ (gamma S (q a)).val}) _ _ hc
      all_goals
        intro d hd
        cases d with
        | none => exact none_mem_plus S _
        | some d => exact (some_mem_plus S _ d).mpr (((some_mem_plus S _ d).mp hd) a)⟩

theorem canonical_equiv_iff (x y : M) :
    supportEquiv S (canonicalSupport S A q) x y ↔
      ∀ a : ↥A, supportEquiv S (gamma S (q a)) x y := by
  change col S x y ∈ plus S (canonicalSupport S A q).val ↔ _
  cases hc : col S x y with
  | none =>
    constructor
    · intro _ a
      change col S x y ∈ plus S (gamma S (q a)).val
      rw [hc]
      exact none_mem_plus S _
    · intro _
      exact none_mem_plus S _
  | some r =>
    constructor
    · intro hr a
      change col S x y ∈ plus S (gamma S (q a)).val
      rw [hc]
      exact (some_mem_plus S _ r).mpr (((some_mem_plus S _ r).mp hr) a)
    · intro hr
      exact (some_mem_plus S _ r).mpr (fun a =>
        (some_mem_plus S _ r).mp (show some r ∈ plus S (gamma S (q a)).val from hc ▸ hr a))

def canonicalHull : Set M :=
  {y | ∀ a : ↥A, supportEquiv S (gamma S (q a)) a.val y}

theorem fibre_anchor_connected (x : FibreSet S A q) (a : ↥A) :
    supportEquiv S (gamma S (q a)) x.val a.val := by
  change col S x.val a.val ∈ plus S (gamma S (q a)).val
  rw [x.property a]
  exact (some_mem_plus S _ _).mpr (subset_generated S {q a} (Set.mem_singleton _))

/-- C34: this is a whole J-class, with no assertion equating it to a fibre. -/
theorem canonicalHull_eq_class (x : FibreSet S A q) :
    canonicalHull S A q = {y : M | supportEquiv S (canonicalSupport S A q) x.val y} := by
  ext y
  rw [Set.mem_setOf_eq,canonical_equiv_iff]
  constructor
  · intro hy a
    exact (supportEquiv S _).val.trans (fibre_anchor_connected S A q x a) (hy a)
  · intro hy a
    exact (supportEquiv S _).val.trans
      ((supportEquiv S _).val.symm (fibre_anchor_connected S A q x a)) (hy a)

theorem fibre_subset_canonicalHull : FibreSet S A q ⊆ canonicalHull S A q := by
  intro y hy a
  exact (supportEquiv S _).val.symm (fibre_anchor_connected S A q ⟨y,hy⟩ a)

variable {G : Type t} [Group G] [MulAction G M]

/-- Combining actual even connectivity and actual looped diagonal Helly
would put a looped colour in the finite fibre, forbidden by real cliques. -/
theorem canonical_support_loopless (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Nonempty (FibreSet S A q)]
    [Finite (FibreSet S A q)] {r : Atom S} (hr : r ∈ (canonicalSupport S A q).val) :
    ¬ Looped S r := by
  classical
  intro hl
  let P : Finset (Atom S) := Finset.univ.image q
  have hgen : ∀ p ∈ P, r ∈ (generatedSupport S (square S p)).val := by
    intro p hp
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
    exact looped_mem_even S H hl (hr a)
  obtain ⟨l,hl,hP⟩ := looped_diagonal_helly S H cco P ⟨r,hl,hgen⟩
  exact finite_fibre_excludes_looped S A q H cco l
    (fun a => hP (q a) (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)) hl

/-- C33: EVERY actual J-class is finite and uniformly below the ORIGINAL
palette Ramsey number. In particular the Nat.card bound is nonvacuous. -/
theorem canonical_class_finite_bound (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Nonempty (FibreSet S A q)]
    [Finite (FibreSet S A q)] (z : M) :
    Finite (ClassPoint S () (supportEquiv S (canonicalSupport S A q)) z) ∧
      Nat.card (ClassPoint S () (supportEquiv S (canonicalSupport S A q)) z) <
        sourceTriangleRamsey S := by
  apply finite_subset_of_no_looped S
  intro r hr
  obtain ⟨x,y,hxy⟩ := hr
  have he := (supportEquiv S (canonicalSupport S A q)).val.trans
    ((supportEquiv S _).val.symm x.property) y.property
  change col S x.val y.val ∈ plus S (canonicalSupport S A q).val at he
  rw [hxy,some_mem_plus] at he
  exact canonical_support_loopless S A q H cco he

theorem canonical_hull_finite_bound (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Nonempty (FibreSet S A q)]
    [Finite (FibreSet S A q)] (x : FibreSet S A q) :
    Finite (canonicalHull S A q) ∧ Nat.card (canonicalHull S A q) < sourceTriangleRamsey S := by
  rw [canonicalHull_eq_class S A q x]
  exact canonical_class_finite_bound S A q H cco x.val

/-- Actual internal colours inject into the literal original J support. -/
def canonicalClassAtomEmbedding (z : M) :
    InducedAtom S () {y | supportEquiv S (canonicalSupport S A q) z y} ↪
      (canonicalSupport S A q).val where
  toFun c := ⟨c.val,by
    obtain ⟨x,y,hxy⟩ := c.property
    have he := (supportEquiv S (canonicalSupport S A q)).val.trans
      ((supportEquiv S _).val.symm x.property) y.property
    change col S x.val y.val = some c.val at hxy
    change col S x.val y.val ∈ plus S (canonicalSupport S A q).val at he
    rw [hxy,some_mem_plus] at he
    exact he⟩
  inj' _ _ h := Subtype.ext (congrArg (fun x : (canonicalSupport S A q).val => x.val) h)

/-- C36: the full invariant-class two-power theorem is applied ONLY after
C33 has proved that actual whole J-class finite. -/
theorem canonical_class_two_power (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Nonempty (FibreSet S A q)]
    [Finite (FibreSet S A q)] (z : M) :
    ∃ n : ℕ, Nat.card (ClassPoint S () (supportEquiv S (canonicalSupport S A q)) z) = 2^n ∧
      n ≤ Nat.card (canonicalSupport S A q).val ∧
      2^n ≤ 2^(Nat.card (canonicalSupport S A q).val) ∧
      2^(Nat.card (canonicalSupport S A q).val) ≤ 2^(Nat.card (Atom S)) := by
  classical
  letI := S.finiteAtom () ()
  letI := (canonical_class_finite_bound S A q H cco z).1
  obtain ⟨n,hn,hbound⟩ := finite_class_size_power_two S () H cco
    (supportEquiv S (canonicalSupport S A q)) z
  have hnJ := hbound.trans (Nat.card_le_card_of_injective
    (canonicalClassAtomEmbedding S A q z) (canonicalClassAtomEmbedding S A q z).injective)
  have hJD : Nat.card (canonicalSupport S A q).val ≤ Nat.card (Atom S) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact ⟨n,hn,hnJ,Nat.pow_le_pow_right (by decide) hnJ,Nat.pow_le_pow_right (by decide) hJD⟩

theorem canonical_hull_two_power (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Nonempty (FibreSet S A q)]
    [Finite (FibreSet S A q)] (x : FibreSet S A q) :
    ∃ n : ℕ, Nat.card (canonicalHull S A q) = 2^n ∧
      n ≤ Nat.card (canonicalSupport S A q).val ∧
      2^n ≤ 2^(Nat.card (canonicalSupport S A q).val) ∧
      2^(Nat.card (canonicalSupport S A q).val) ≤ 2^(Nat.card (Atom S)) := by
  rw [canonicalHull_eq_class S A q x]
  exact canonical_class_two_power S A q H cco x.val
end CCO.RealHull.Canonical
