import CCO.RealHull.Canonical.Pseudocomplement
import CCO.RealHull.Canonical.Star
import CCO.RealHull.Canonical.RamseySubset
import CCO.RealHull.Geometry.Globalisation

/-! A literal realised finite star gives the carrier. Its finite loop-free
fibre is globalised only AFTER finite Ramsey has proved its finiteness. -/
universe v w t
namespace CCO.RealHull.Canonical
open Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M]
variable {G : Type t} [Group G] [MulAction G M]

/-- C28: the actual carrier palette and its finite bound, including C empty. -/
theorem finite_fibre_of_no_looped_palette (A : Finset M) (q : ↥A → Atom S)
    (hloop : ∀ r : Atom S, (∀ a : ↥A, r ∈ square S (q a)) → ¬ Looped S r) :
    Finite (FibreSet S A q) ∧ Nat.card (FibreSet S A q) < sourceTriangleRamsey S := by
  apply finite_subset_of_no_looped S
  intro r hr
  obtain ⟨x,y,hxy⟩ := hr
  apply hloop r
  intro a
  exact (mem_row S _ _ _).mpr
    ⟨x.val,a.val,y.val,x.property a,(col_symm S _ _).trans (y.property a),hxy⟩

/-- C29. There is no uninstantiated star/finite-fibre/globalisation provider. -/
theorem carrier_insertion (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (P : Finset (Atom S)) (_hP : P.Nonempty) (b r : Atom S)
    (hr : Looped S r) (hrP : r ∈ squareMeet S P)
    (hrb : r ∈ (generatedSupport S (square S b)).val) :
    ∃ l : Atom S, Looped S l ∧ l ∈ squareMeet S P ∧ l ∈ square S b := by
  classical
  by_cases hbP : b ∈ P
  · exact ⟨r,hr,hrP,hrP b hbP⟩
  by_contra hn
  let star := starOfFinset S H (insert b P)
  let A := star.anchor
  let q := star.spoke
  letI : Nonempty (FibreSet S A q) := ⟨star.centre⟩
  have hpalette : {c : Atom S | ∀ a : ↥A, c ∈ square S (q a)} =
      squareMeet S P ∩ square S b := by
    rw [show {c : Atom S | ∀ a : ↥A, c ∈ square S (q a)} =
      squareMeet S (insert b P) from star.palette_eq S]
    ext c
    simp only [squareMeet,Set.mem_setOf_eq,Finset.mem_insert,forall_eq_or_imp,Set.mem_inter_iff]
    exact and_comm
  have hloop : ∀ c : Atom S, (∀ a : ↥A, c ∈ square S (q a)) → ¬ Looped S c := by
    intro c hc hl
    have hm : c ∈ squareMeet S P ∩ square S b := by
      rw [← hpalette]
      exact hc
    exact hn ⟨c,hl,hm.1,hm.2⟩
  letI : Finite (FibreSet S A q) := (finite_fibre_of_no_looped_palette S A q hloop).1
  let R : Support S := fibreSpokeFixer S A q H
  have hR : R.val = squareMeet S P ∩ square S b :=
    (finite_fibre_palette_eq S A q H cco).symm.trans hpalette
  have hfix : ∀ p ∈ P, Fixed S R p := by
    intro p hp
    have hp' : p ∈ Set.range q := by
      change p ∈ Set.range star.spoke
      rw [star.range_spoke]
      exact Finset.mem_insert_of_mem hp
    obtain ⟨a,rfl⟩ := hp'
    exact fibreSpokeFixer_fixed S A q H a
  let W := pseudoSupport S H cco R P hfix
  have hbW : b ∈ W.val := by
    intro c hc
    rw [hR]
    exact ⟨hc.2,hc.1⟩
  have hgen : (generatedSupport S (square S b)).val ⊆ W.val :=
    generated_le S (square S b) W (square_le_support S W hbW)
  have hrW := hgen hrb
  have hrR : r ∈ R.val := hrW ⟨hr,hrP⟩
  have hrC : r ∈ squareMeet S P ∩ square S b := hR ▸ hrR
  exact hn ⟨r,hr,hrC.1,hrC.2⟩

/-- C30. The induction inserts the EXTRA current looped row, which preserves
all unprocessed generated-support constraints. The empty family is literal. -/
theorem looped_diagonal_helly (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (P : Finset (Atom S))
    (h : ∃ r : Atom S, Looped S r ∧ ∀ p ∈ P, r ∈ (generatedSupport S (square S p)).val) :
    ∃ r : Atom S, Looped S r ∧ r ∈ squareMeet S P := by
  classical
  suffices aux : ∀ (Q : Finset (Atom S)) (r : Atom S), Looped S r →
      (∀ p ∈ Q, r ∈ (generatedSupport S (square S p)).val) →
      ∃ r' : Atom S, Looped S r' ∧ r' ∈ squareMeet S Q ∧
        r' ∈ (generatedSupport S {r}).val by
    obtain ⟨r,hr,hP⟩ := h
    obtain ⟨r',hr',hQ,_⟩ := aux P r hr hP
    exact ⟨r',hr',hQ⟩
  intro Q
  induction Q using Finset.induction_on with
  | empty =>
    intro r hr _
    exact ⟨r,hr,fun p hp => False.elim (Finset.notMem_empty _ hp),
      subset_generated S {r} (Set.mem_singleton _)⟩
  | @insert b Q hb ih =>
    intro r hr hgen
    obtain ⟨r',hr',hrQ,hrr'⟩ := ih r hr (fun p hp => hgen p (Finset.mem_insert_of_mem hp))
    have hr'b : r' ∈ (generatedSupport S (square S b)).val := by
      exact generated_le S {r} _
        (Set.singleton_subset_iff.mpr (hgen b (Finset.mem_insert_self _ _))) hrr'
    have hrExtra : r' ∈ squareMeet S (insert r' Q) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hr'
      · exact hrQ p hp
    obtain ⟨r'',hr'',hr''P,hr''b⟩ := carrier_insertion S H cco (insert r' Q)
      (Finset.insert_nonempty _ _) b r' hr' hrExtra hr'b
    have hr''gen : r'' ∈ (generatedSupport S {r}).val := by
      have hr''sq : r'' ∈ square S r' := hr''P r' (Finset.mem_insert_self _ _)
      exact square_le_support S (generatedSupport S {r}) hrr' hr''sq
    refine ⟨r'',hr'',?_,hr''gen⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hr''b
    · exact hr''P p (Finset.mem_insert_of_mem hp)
end CCO.RealHull.Canonical
