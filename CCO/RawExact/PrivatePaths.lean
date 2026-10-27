import CCO.RawExact.Convolution
import CCO.RawExact.QuotientDescent

/-!
# B002 C18: independent actual private RAW path witnesses

A WordPath contains all intermediate real vertices for an actual
equality-inclusive typed word. A PrivatePaths certificate has a separate
constructor for EACH occurrence of a word, including duplicated words.
It is the semantic core of representative-independent cycle expansion:
the finite formal graph and its simple-cycle decomposition (C26) are
different, still-open obligations.
-/

universe u v w

namespace CCO.RawExact

/-- Actual internal vertex choices for one typed RAW walk.
Identity letters do not introduce an artificial diversity edge. -/
inductive WordPath {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) :
    {i j : ι} → RawWord S i j → X i → X j → Type (max u (max v w)) where
  | nil {i : ι} (x : X i) :
      WordPath S (.nil i) x x
  | identity {i j : ι} {tail : RawWord S i j}
      {x : X i} {z : X j}
      (path : WordPath S tail x z) :
      WordPath S (.identity tail) x z
  | atom {i j k : ι} (a : S.Atom i j)
      {tail : RawWord S j k} {x : X i}
      {middle : X j} {z : X k}
      (edge : S.atomRel a x middle)
      (rest : WordPath S tail middle z) :
      WordPath S (.atom a tail) x z

/-- A different private path witness for every LIST OCCURRENCE.
This still has only a semantic witness; disjoint formal internal
graph vertices for the CCO expansion are constructed separately. -/
inductive PrivatePaths {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) {i j : ι}
    (x : X i) (z : X j) :
    Presentation S i j → Type (max u (max v w)) where
  | nil : PrivatePaths S x z []
  | cons {word : RawWord S i j} {tail : Presentation S i j}
      (head : WordPath S word x z)
      (rest : PrivatePaths S x z tail) :
      PrivatePaths S x z (word :: tail)

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem wordPath_iff_relation {i j : ι}
    (word : RawWord S i j) (x : X i) (z : X j) :
    Nonempty (WordPath S word x z) ↔
      RawWord.relation S word x z := by
  induction word generalizing x z with
  | nil i =>
      constructor
      · rintro ⟨p⟩
        cases p
        rfl
      · intro h
        change x = z at h
        subst z
        exact ⟨WordPath.nil x⟩
  | identity tail ih =>
      constructor
      · rintro ⟨p⟩
        cases p with
        | identity pTail => exact (ih x z).mp ⟨pTail⟩
      · intro h
        obtain ⟨pTail⟩ := (ih x z).mpr h
        exact ⟨WordPath.identity pTail⟩
  | atom a tail ih =>
      constructor
      · rintro ⟨p⟩
        cases p with
        | atom _ hEdge pTail =>
            exact ⟨_, hEdge, (ih _ z).mp ⟨pTail⟩⟩
      · rintro ⟨middle, hEdge, hTail⟩
        obtain ⟨pTail⟩ := (ih middle z).mpr hTail
        exact ⟨WordPath.atom a hEdge pTail⟩

/-- Finite simultaneous path choices are equivalent to satisfaction
of EVERY exact word restriction, not just one. In particular duplicate
word entries have independent private witnesses. -/
theorem privatePaths_iff_evaluate {i j : ι}
    (P : Presentation S i j) (x : X i) (z : X j) :
    Nonempty (PrivatePaths S x z P) ↔ evaluate S P x z := by
  induction P with
  | nil =>
      constructor
      · intro _ word h
        cases h
      · intro _
        exact ⟨PrivatePaths.nil⟩
  | cons word tail ih =>
      constructor
      · rintro ⟨p⟩
        cases p with
        | cons pHead pTail =>
            intro w hw
            have hmem : w = word ∨ w ∈ tail := by
              simpa only [List.mem_cons] using hw
            rcases hmem with rfl | hTail
            · exact (wordPath_iff_relation S word x z).mp ⟨pHead⟩
            · exact (ih.mp ⟨pTail⟩) w hTail
      · intro h
        obtain ⟨pHead⟩ := (wordPath_iff_relation S word x z).mpr
          (h word (by simp))
        have hRest : evaluate S tail x z := by
          intro w hw
          exact h w (by simp [hw])
        obtain ⟨pTail⟩ := ih.mpr hRest
        exact ⟨PrivatePaths.cons pHead pTail⟩

/-- Core of C18: any chosen representatives of two quotient elements
belonging to a named pair orbit carry ALL private word-path witnesses
simultaneously, provided the exact represented pullback presentation
is already proved. The hPresentation premise will be supplied by C09.
No quotient section, CCO on quotient sorts or joint lifting is used. -/
theorem private_paths_of_quotient_pair
    {i j : ι} {Q R : Type*}
    (τ : X i → Q) (σ : X j → R)
    (Θ : Q → R → Prop)
    (P : Presentation S i j)
    (hPresentation :
      evaluate S P = GroupActions.pullback τ σ Θ)
    (q : Q) (r : R) (hqr : Θ q r)
    (x : X i) (y : X j)
    (hx : τ x = q) (hy : σ y = r) :
    Nonempty (PrivatePaths S x y P) := by
  apply (privatePaths_iff_evaluate S P x y).mpr
  rw [hPresentation]
  change Θ (τ x) (σ y)
  rw [hx, hy]
  exact hqr

/-- The actual quotient-pair-orbital version, applied to every arbitrary
pair of real representatives of the same actual quotient orbit. -/
theorem orbital_private_paths_of_quotient_pair
    {i j : ι} {Q R G : Type*} [Group G]
    [MulAction G Q] [MulAction G R]
    (τ : X i → Q) (σ : X j → R)
    (a : Q) (b : R)
    (P : Presentation S i j)
    (hPresentation : evaluate S P =
      GroupActions.pullback τ σ
        (GroupActions.orbital (G := G) a b))
    (q : Q) (r : R)
    (hqr : GroupActions.orbital (G := G) a b q r)
    (x : X i) (y : X j)
    (hx : τ x = q) (hy : σ y = r) :
    Nonempty (PrivatePaths S x y P) :=
  private_paths_of_quotient_pair S τ σ
    (GroupActions.orbital (G := G) a b)
    P hPresentation q r hqr x y hx hy

end CCO.RawExact
