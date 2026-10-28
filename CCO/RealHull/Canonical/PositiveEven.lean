import CCO.RealHull.Canonical.EvenWalk
import Mathlib.Data.Finset.Lattice.Fold

/-! Finite stabilization tracks positive EVEN p-word profiles. The resulting
profile is the even-connectivity support, not the full connected support. -/
universe v w t
namespace CCO.RealHull.Canonical
open CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def twoProfile (p : Atom S) : Set (FullColour S) := prod S {some p} {some p}
def positiveEvenProfile (p : Atom S) : ℕ → Set (FullColour S)
  | 0 => twoProfile S p
  | n+1 => prod S (positiveEvenProfile p n) (twoProfile S p)

theorem none_twoProfile (p : Atom S) : none ∈ twoProfile S p :=
  (none_mem_prod S _ _).mpr ⟨some p,Set.mem_singleton (some p),Set.mem_singleton (some p)⟩

theorem twoProfile_eq_plus_square (p : Atom S) :
    twoProfile S p = plus S (square S p) := by
  ext c
  cases c with
  | none => exact iff_of_true (none_twoProfile S p) (none_mem_plus S _)
  | some a => exact (some_mem_plus S (square S p) a).symm

theorem none_positiveEvenProfile (p : Atom S) (n : ℕ) :
    none ∈ positiveEvenProfile S p n := by
  induction n with
  | zero => exact none_twoProfile S p
  | succ n ih => exact (none_mem_prod S _ _).mpr ⟨none,ih,none_twoProfile S p⟩

theorem positiveEvenProfile_step (p : Atom S) (n : ℕ) :
    positiveEvenProfile S p n ⊆ positiveEvenProfile S p (n+1) := by
  have hi : ({none} : Set (FullColour S)) ⊆ twoProfile S p :=
    fun _ h => (Set.mem_singleton_iff.mp h) ▸ none_twoProfile S p
  have hm := prod_mono S (A := positiveEvenProfile S p n) Set.Subset.rfl hi
  rw [prod_none_right] at hm
  exact hm

theorem positiveEvenProfile_mono (p : Atom S) : Monotone (positiveEvenProfile S p) :=
  monotone_nat_of_le_succ (positiveEvenProfile_step S p)

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)
include H

theorem prod_positiveEvenProfile (p : Atom S) (n m : ℕ) :
    prod S (positiveEvenProfile S p n) (positiveEvenProfile S p m) =
      positiveEvenProfile S p (n+m+1) := by
  induction n generalizing m with
  | zero =>
    simpa only [Nat.zero_add,positiveEvenProfile] using
      (prod_comm S (twoProfile S p) (positiveEvenProfile S p m))
  | succ n ih =>
    change prod S (prod S (positiveEvenProfile S p n) (twoProfile S p)) _ = _
    rw [prod_assoc S H,prod_comm S (twoProfile S p)]
    change prod S (positiveEvenProfile S p n) (positiveEvenProfile S p (m+1)) = _
    rw [ih]
    congr 1
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def evenUnion (p : Atom S) : Set (FullColour S) :=
  {c | ∃ n, c ∈ positiveEvenProfile S p n}
def evenUnionDiversity (p : Atom S) : Set (Atom S) :=
  {a | some a ∈ evenUnion S p}

omit H in
theorem evenUnion_eq_plus (p : Atom S) :
    evenUnion S p = plus S (evenUnionDiversity S p) := by
  ext c
  cases c with
  | none => exact iff_of_true ⟨0,none_twoProfile S p⟩ (none_mem_plus S _)
  | some a => exact (some_mem_plus S (evenUnionDiversity S p) a).symm

def evenUnionSupport (p : Atom S) : Support S :=
  ⟨evenUnionDiversity S p,by
    rintro c ⟨x,y,z,hxy,hyz,hxz⟩
    rw [← evenUnion_eq_plus S p] at hxy hyz ⊢
    obtain ⟨n,hn⟩ := hxy
    obtain ⟨m,hm⟩ := hyz
    refine ⟨n+m+1,?_⟩
    rw [← prod_positiveEvenProfile S H p n m]
    exact ⟨x,y,z,hn,hm,hxz⟩⟩

omit H in
theorem positiveEvenProfile_le_even (p : Atom S) (n : ℕ) :
    positiveEvenProfile S p n ⊆ plus S (evenSupport S p).val := by
  have hq : twoProfile S p ⊆ plus S (evenSupport S p).val := by
    rw [twoProfile_eq_plus_square]
    intro c hc
    cases c with
    | none => exact none_mem_plus S _
    | some a =>
      apply (some_mem_plus S _ a).mpr
      exact subset_generated S (square S p) ((some_mem_plus S _ a).mp hc)
  induction n with
  | zero => exact hq
  | succ n ih => exact fun _ h => (evenSupport S p).property (prod_mono S ih hq h)

theorem evenUnion_eq_even (p : Atom S) : evenUnion S p = plus S (evenSupport S p).val := by
  apply Set.Subset.antisymm
  · rintro c ⟨n,hn⟩
    exact positiveEvenProfile_le_even S p n hn
  · have hg := generated_plus_le S (square S p) (evenUnionSupport S H p) (by
      intro a ha
      change ∃ n, some a ∈ positiveEvenProfile S p n
      exact ⟨0,ha⟩)
    intro c hc
    rw [evenUnion_eq_plus S p]
    exact hg hc

omit H in
/-- Finite palette: choose the largest of the first-occurrence indices of
all colours in the increasing union. This proves attainment explicitly. -/
theorem positiveEvenProfile_attains_union (p : Atom S) :
    ∃ N, evenUnion S p ⊆ positiveEvenProfile S p N := by
  classical
  letI := S.finiteAtom () ()
  let level : FullColour S → ℕ := fun c =>
    if h : c ∈ evenUnion S p then Classical.choose h else 0
  refine ⟨Finset.univ.sup level,?_⟩
  intro c hc
  have hlevel : c ∈ positiveEvenProfile S p (level c) := by
    dsimp only [level]
    rw [dif_pos hc]
    exact Classical.choose_spec hc
  exact positiveEvenProfile_mono S p (Finset.le_sup (Finset.mem_univ c)) hlevel

/-- All sufficiently long positive EVEN profiles are exactly B(p)^+.
Neither an odd profile nor Gamma(p)^+ is claimed to be RAW exact. -/
theorem positiveEvenProfile_stabilizes (p : Atom S) :
    ∃ N, ∀ n, N ≤ n → positiveEvenProfile S p n = plus S (evenSupport S p).val := by
  obtain ⟨N,hN⟩ := positiveEvenProfile_attains_union S p
  refine ⟨N,fun n hn => Set.Subset.antisymm (positiveEvenProfile_le_even S p n) ?_⟩
  intro c hc
  have hu : c ∈ evenUnion S p := (evenUnion_eq_even S H p) ▸ hc
  exact positiveEvenProfile_mono S p hn (hN hu)

/-- A literal positive RAW word with 2(n+1) diversity letters. -/
def positiveEvenWord (p : Atom S) : ℕ → RawWord S () ()
  | 0 => .atom p (.atom p (.nil ()))
  | n+1 => RawWord.append S (positiveEvenWord p n) (.atom p (.atom p (.nil ())))

theorem positiveEvenWord_relation (p : Atom S) (n : ℕ) :
    RawWord.relation S (positiveEvenWord S p n) =
      S.representedSupport (positiveEvenProfile S p n) := by
  have hbase : RawWord.relation S (.atom p (.atom p (.nil ()))) =
      S.representedSupport (twoProfile S p) := by
    rw [show twoProfile S p = prod S {some p} {some p} from rfl,represented_prod S H]
    change TRel.comp (S.atomRel p) (TRel.comp (S.atomRel p) (TRel.ident _ ())) = _
    rw [TRel.comp_ident]
    rfl
  induction n with
  | zero => exact hbase
  | succ n ih =>
    rw [positiveEvenWord,RawWord.relation_append,ih,hbase]
    exact (represented_prod S H _ _).symm

/-- The stable even support has an actual positive even-word representative. -/
theorem exists_positive_even_word (p : Atom S) :
    ∃ n, RawWord.relation S (positiveEvenWord S p n) =
      fun x y => supportEquiv S (evenSupport S p) x y := by
  obtain ⟨N,hN⟩ := positiveEvenProfile_stabilizes S H p
  refine ⟨N,?_⟩
  rw [positiveEvenWord_relation S H,hN N le_rfl]
  rfl

end CCO.RealHull.Canonical
