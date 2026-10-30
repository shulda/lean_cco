import CCO.OrbitalCover.Example.Products
import Mathlib.Tactic.NormNum

namespace CCO.OrbitalCover.Example

def coordProduct (A B : Set CoordColour) : Set CoordColour :=
  {c | ∃ a ∈ A, ∃ b ∈ B, coordTriangle a b c}

theorem product_boxes {i j k : Unit} (A B C D : Set CoordColour) :
    source.product (i := i) (j := j) (k := k) (A.prod B) (C.prod D) =
      (coordProduct A C).prod (coordProduct B D) := by
  ext c
  constructor
  · rintro ⟨a,ha,b,hb,htri⟩
    have ht := (triangle_iff a b c).mp htri
    exact ⟨⟨a.1,ha.1,b.1,hb.1,ht.1⟩,⟨a.2,ha.2,b.2,hb.2,ht.2⟩⟩
  · rintro ⟨⟨a1,ha1,b1,hb1,h1⟩,⟨a2,ha2,b2,hb2,h2⟩⟩
    exact ⟨(a1,a2),⟨ha1,ha2⟩,(b1,b2),⟨hb1,hb2⟩,
      (triangle_iff _ _ _).mpr ⟨h1,h2⟩⟩

@[simp] theorem coordProduct_some_some (i j : Bit) :
    coordProduct {some i} {some j} = {some (i+j)} := by
  ext c
  simp [coordProduct,coordTriangle]

@[simp] theorem coordProduct_some_none (i : Bit) :
    coordProduct {some i} {none} = {none} := by
  ext c
  simp [coordProduct,coordTriangle]

@[simp] theorem coordProduct_none_some (i : Bit) :
    coordProduct {none} {some i} = {none} := by
  ext c
  simp [coordProduct,coordTriangle]

@[simp] theorem coordProduct_none_none :
    coordProduct {none} {none} = Set.univ := by
  ext c
  simp [coordProduct,coordTriangle]

theorem coordTriangle_partner (a c : CoordColour) : ∃ b, coordTriangle a b c := by
  cases a with
  | none => exact ⟨none,trivial⟩
  | some i =>
    cases c with
    | none => exact ⟨none,rfl⟩
    | some k =>
      refine ⟨some (i+k),?_⟩
      change some k = some (i+(i+k))
      rw [← add_assoc,CharTwo.add_self_eq_zero,zero_add]

@[simp] theorem coordProduct_univ (a : CoordColour) :
    coordProduct {a} Set.univ = Set.univ := by
  ext c
  simp only [coordProduct,Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left,
    Set.mem_univ,true_and,iff_true]
  exact coordTriangle_partner a c

/-- The actual one-coordinate reachable profiles have only these four forms. -/
inductive CoordProfile where
  | single (a : CoordColour)
  | top

namespace CoordProfile

def menu : CoordProfile → Set CoordColour
  | .single a => {a}
  | .top => Set.univ

def step (a : CoordColour) : CoordProfile → CoordProfile
  | .top => .top
  | .single b => match a,b with
    | some i,some j => .single (some (i+j))
    | none,none => .top
    | _,_ => .single none

theorem menu_step (a : CoordColour) (P : CoordProfile) :
    coordProduct {a} P.menu = (P.step a).menu := by
  cases P with
  | top => exact coordProduct_univ a
  | single b =>
    cases a <;> cases b <;>
      simp only [menu,step,coordProduct_some_some,coordProduct_some_none,
        coordProduct_none_some,coordProduct_none_none]

theorem menu_nonempty (P : CoordProfile) : P.menu.Nonempty := by
  cases P with
  | single a => exact ⟨a,rfl⟩
  | top => exact ⟨none,trivial⟩

/-- In fact any, not just finite, pairwise-intersecting family of these
singleton/Top profiles has a common point. -/
theorem helly {I : Type*} (F : I → CoordProfile)
    (hp : ∀ i j, ((F i).menu ∩ (F j).menu).Nonempty) :
    ∃ c : CoordColour, ∀ i, c ∈ (F i).menu := by
  classical
  by_cases hs : ∃ i c, F i = .single c
  · obtain ⟨i,c,hi⟩ := hs
    refine ⟨c,fun j => ?_⟩
    obtain ⟨a,ha,hj⟩ := hp i j
    have he : a = c := by simpa only [hi,menu,Set.mem_singleton_iff] using ha
    simpa only [he] using hj
  · refine ⟨none,fun i => ?_⟩
    cases hi : F i with
    | top => trivial
    | single c => exact (hs ⟨i,c,hi⟩).elim

end CoordProfile

/-- Fold the actual typed positive word in each literal coordinate. -/
def wordFactors {i j : Unit} : PositiveWord source i j → CoordProfile × CoordProfile
  | .single a => (.single a.1,.single a.2)
  | .cons a rest => ((wordFactors rest).1.step a.1,(wordFactors rest).2.step a.2)

theorem positive_profile_box {i j : Unit} (w : PositiveWord source i j) :
    PositiveWord.profile source w =
      (wordFactors w).1.menu.prod (wordFactors w).2.menu := by
  induction w with
  | @single i j a =>
    cases i; cases j
    ext c
    change c = a ↔ c.1 = a.1 ∧ c.2 = a.2
    exact Prod.ext_iff
  | @cons i j k a rest ih =>
    cases i; cases j; cases k
    change source.product {a} (PositiveWord.profile source rest) = _
    rw [ih]
    have ha : ({a} : source.Menu () ()) = ({a.1} : Set CoordColour).prod {a.2} := by
      ext c
      change c = a ↔ c.1 = a.1 ∧ c.2 = a.2
      exact Prod.ext_iff
    rw [ha,product_boxes,CoordProfile.menu_step,CoordProfile.menu_step]
    rfl

/-- Every one of the four coordinate forms actually occurs in a positive
word; Top already occurs after two n-letters in that coordinate. -/
theorem every_coordProfile_reachable (P : CoordProfile) :
    ∃ w : PositiveWord source () (), (wordFactors w).1 = P := by
  cases P with
  | single a => exact ⟨.single (a,some 0),rfl⟩
  | top =>
    refine ⟨.cons (j := ()) (none,some 0) (.single (none,some 0)),?_⟩
    simp only [wordFactors,CoordProfile.step]

theorem positive_profile_nonempty {i j : Unit} (w : PositiveWord source i j) :
    (PositiveWord.profile source w).Nonempty := by
  rw [positive_profile_box]
  obtain ⟨a,ha⟩ := (wordFactors w).1.menu_nonempty
  obtain ⟨b,hb⟩ := (wordFactors w).2.menu_nonempty
  exact ⟨(a,b),ha,hb⟩

theorem positive_profiles_helly {I : Type*} (F : I → PositiveWord source () ())
    (hp : ∀ i j, (PositiveWord.profile source (F i) ∩
      PositiveWord.profile source (F j)).Nonempty) :
    ∃ a : Colour, ∀ i, a ∈ PositiveWord.profile source (F i) := by
  have h1 : ∀ i j, ((wordFactors (F i)).1.menu ∩ (wordFactors (F j)).1.menu).Nonempty := by
    intro i j
    obtain ⟨a,ha,hb⟩ := hp i j
    rw [positive_profile_box] at ha hb
    exact ⟨a.1,ha.1,hb.1⟩
  have h2 : ∀ i j, ((wordFactors (F i)).2.menu ∩ (wordFactors (F j)).2.menu).Nonempty := by
    intro i j
    obtain ⟨a,ha,hb⟩ := hp i j
    rw [positive_profile_box] at ha hb
    exact ⟨a.2,ha.2,hb.2⟩
  obtain ⟨a,ha⟩ := CoordProfile.helly (fun i => (wordFactors (F i)).1) h1
  obtain ⟨b,hb⟩ := CoordProfile.helly (fun i => (wordFactors (F i)).2) h2
  refine ⟨(a,b),fun i => ?_⟩
  rw [positive_profile_box]
  exact ⟨ha i,hb i⟩

def diagonalPalette : Set Colour := {(some 0,some 0),(some 1,some 1)}

theorem diagonal_not_box : ¬ ∃ A B : Set CoordColour, diagonalPalette = A.prod B := by
  rintro ⟨A,B,h⟩
  have h0 : (some 0,some 0) ∈ A.prod B := by rw [← h]; simp [diagonalPalette]
  have h1 : (some 1,some 1) ∈ A.prod B := by rw [← h]; simp [diagonalPalette]
  have hm : (some 0,some 1) ∈ diagonalPalette := by rw [h]; exact ⟨h0.1,h1.2⟩
  norm_num [diagonalPalette,Prod.ext_iff] at hm

theorem diagonal_not_positive_profile {i j : Unit} (w : PositiveWord source i j) :
    diagonalPalette ≠ PositiveWord.profile source w := by
  intro h
  exact diagonal_not_box ⟨(wordFactors w).1.menu,(wordFactors w).2.menu,
    h.trans (positive_profile_box w)⟩

end CCO.OrbitalCover.Example
