import CCO.GuardedTwoRoot.G1OldSAP
import CCO.UnaryFreshFrames.ClosureActions

/-! The ACTUAL coarse hidden FG1 expansion. The original p/q/r real
relations are retained. Both mixed orientations and both quotient
orbitals are named; the only function is the coarse block projection.
No fine-bit quotient vertex or operation is added. -/

namespace CCO.GuardedTwoRoot.G1.Hidden
open CCO.UnaryFreshFrames
noncomputable section

abbrev Point := Real ⊕ ℕ
abbrev RelationName := Atom ⊕ (Bool ⊕ (Bool × Bool))

def sort : Point → Bool
  | .inl _ => false
  | .inr _ => true

def owner : Point → ℕ
  | .inl x => block x
  | .inr b => b

def realValue : Point → Real
  | .inl x => x
  | .inr b => ((b,false),0)

def projection (x : Point) : Point := .inr (owner x)

def leftSort : RelationName → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (direction,_)) => direction

def rightSort : RelationName → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (direction,_)) => !direction

abbrev language : Language where
  Sorts := Bool
  Func := Unit
  Rel := RelationName
  input _ := false
  output _ := true
  arity _ := 2
  argument R i := if i = 0 then leftSort R else rightSort R

def relationData : RelationName → Point → Point → Prop
  | .inl a, x,y => colour (realValue x) (realValue y) = some a
  | .inr (.inl same),x,y => (owner x = owner y ↔ same = true)
  | .inr (.inr (_,same)),x,y => (owner x = owner y ↔ same = true)

def model : Structure language Point where
  sort := sort
  func _ := projection
  func_sort := by
    rintro _ (x | b) h
    · rfl
    · cases h
  func_offsort := by
    rintro _ (x | b) h
    · exact False.elim (h rfl)
    · rfl
  rel R xs := sort (xs 0) = leftSort R ∧ sort (xs 1) = rightSort R ∧
    relationData R (xs 0) (xs 1)
  rel_sort := by
    intro R xs h i
    fin_cases i
    · exact h.1
    · exact h.2.1

def wreath (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) : Equiv.Perm Point :=
  Equiv.sumCongr (G1.wreath a c b) a

theorem wreath_sort (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Point) :
    sort (wreath a c b x) = sort x := by cases x <;> rfl

theorem wreath_owner (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Point) :
    owner (wreath a c b x) = a (owner x) := by cases x <;> rfl

def wreathAut (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) : model.Aut := by
  refine ⟨wreath a c b,wreath_sort a c b,?_,?_⟩
  · rintro F (x | q) <;> rfl
  · intro R xs
    change (sort (wreath a c b (xs 0)) = leftSort R ∧
      sort (wreath a c b (xs 1)) = rightSort R ∧
      relationData R (wreath a c b (xs 0)) (wreath a c b (xs 1))) ↔
        (sort (xs 0) = leftSort R ∧ sort (xs 1) = rightSort R ∧
          relationData R (xs 0) (xs 1))
    rw [wreath_sort,wreath_sort]
    cases R with
    | inl atom =>
      cases hx : xs 0 <;> cases hy : xs 1
      all_goals simp [leftSort,rightSort,sort,relationData,realValue,wreath,
        hx,hy,G1.wreath_colour]
    | inr name =>
      cases name with
      | inl same =>
        simp only [relationData,wreath_owner,a.injective.eq_iff]
      | inr pair =>
        simp only [relationData,wreath_owner,a.injective.eq_iff]

/-- The literal real restriction is the entire old three-atom source. -/
theorem real_relation (a : Atom) (x y : Real) :
    model.rel (.inl a) ![.inl x,.inl y] ↔ colour x y = some a := by
  simp [model,leftSort,rightSort,sort,relationData,realValue]

theorem projection_real (x : Real) : model.func () (.inl x) = .inr (block x) := rfl

theorem quotient_diagonal (q t : ℕ) :
    model.rel (.inr (.inl true)) ![.inr q,.inr t] ↔ q = t := by
  simp [model,relationData,leftSort,rightSort,sort,owner]

theorem quotient_offdiagonal (q t : ℕ) :
    model.rel (.inr (.inl false)) ![.inr q,.inr t] ↔ q ≠ t := by
  simp [model,relationData,leftSort,rightSort,sort,owner]

theorem mixed_forward (same : Bool) (x : Real) (q : ℕ) :
    model.rel (.inr (.inr (false,same))) ![.inl x,.inr q] ↔
      (block x = q ↔ same = true) := by
  simp [model,relationData,leftSort,rightSort,sort,owner]

theorem mixed_reverse (same : Bool) (x : Real) (q : ℕ) :
    model.rel (.inr (.inr (true,same))) ![.inr q,.inl x] ↔
      (q = block x ↔ same = true) := by
  simp [model,relationData,leftSort,rightSort,sort,owner]

theorem point_ext {x y : Point} (hs : sort x = sort y) (ho : owner x = owner y)
    (hb : sort x = false → bit (realValue x) = bit (realValue y))
    (hn : sort x = false → clone (realValue x) = clone (realValue y)) : x = y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (G1.real_ext ho (hb rfl) (hn rfl))
    | inr q => cases hs
  | inr q =>
    cases y with
    | inl y => cases hs
    | inr t => exact congrArg Sum.inr ho

theorem owner_realValue (x : Point) (hx : sort x = false) :
    block (realValue x) = owner x := by cases x <;> simp_all [sort,realValue,owner]

theorem wreath_realValue (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Point) (hx : sort x = false) :
    realValue (wreath a c b x) = G1.wreath a c b (realValue x) := by
  cases x <;> simp_all [sort,realValue,wreath]

/-- Explicit finite extension for the ACTUAL coarse expansion. Owner
permutations also align orphan quotient vertices; bit and clone maps
are selected only on real positions, so no fine quotient is named. -/
theorem finite_extension {P : Type*} [Finite P] (f h : P → Point)
    (hSort : ∀ v, sort (f v) = sort (h v))
    (hOwner : ∀ v w, owner (f v) = owner (f w) ↔ owner (h v) = owner (h w))
    (hColour : ∀ v w, sort (f v) = false → sort (f w) = false →
      colour (realValue (f v)) (realValue (f w)) =
        colour (realValue (h v)) (realValue (h w))) :
    ∃ g : model.Aut, ∀ v, g • f v = h v := by
  classical
  obtain ⟨a,ha⟩ := CCO.UnaryFreshFrames.Examples.extend_equal_kernels
    (fun v => owner (f v)) (fun v => owner (h v)) hOwner
  let I (q : ℕ) := {v : P // sort (f v) = false ∧ owner (f v) = q}
  have hC (q : ℕ) : ∃ c : Equiv.Perm Bool, ∀ v : I q,
      c (bit (realValue (f v.val))) = bit (realValue (h v.val)) := by
    apply CCO.UnaryFreshFrames.Examples.extend_equal_kernels
    intro v w
    have hbf : block (realValue (f v.val)) = block (realValue (f w.val)) := by
      rw [owner_realValue _ v.property.1,owner_realValue _ w.property.1]
      exact v.property.2.trans w.property.2.symm
    have hbh : block (realValue (h v.val)) = block (realValue (h w.val)) := by
      rw [owner_realValue _ ((hSort v.val).symm.trans v.property.1),
        owner_realValue _ ((hSort w.val).symm.trans w.property.1)]
      exact (hOwner v.val w.val).mp (v.property.2.trans w.property.2.symm)
    have hh := G1.fine_of_colour (hColour v.val w.val v.property.1 w.property.1)
    exact ⟨fun hd => (hh.mp ⟨hbf,hd⟩).2,fun hd => (hh.mpr ⟨hbh,hd⟩).2⟩
  let c : ℕ → Equiv.Perm Bool := fun q => (hC q).choose
  have hbit (v : P) (hv : sort (f v) = false) :
      c (owner (f v)) (bit (realValue (f v))) = bit (realValue (h v)) :=
    (hC (owner (f v))).choose_spec ⟨v,hv,rfl⟩
  let J (t : ℕ × Bool) := {v : P // sort (f v) = false ∧
    owner (f v) = t.1 ∧ bit (realValue (f v)) = t.2}
  have hB (t : ℕ × Bool) : ∃ b : Equiv.Perm ℕ, ∀ v : J t,
      b (clone (realValue (f v.val))) = clone (realValue (h v.val)) := by
    apply CCO.UnaryFreshFrames.Examples.extend_equal_kernels
    intro v w
    have hbf : block (realValue (f v.val)) = block (realValue (f w.val)) := by
      rw [owner_realValue _ v.property.1,owner_realValue _ w.property.1]
      exact v.property.2.1.trans w.property.2.1.symm
    have hdf : bit (realValue (f v.val)) = bit (realValue (f w.val)) :=
      v.property.2.2.trans w.property.2.2.symm
    have hbh : block (realValue (h v.val)) = block (realValue (h w.val)) := by
      rw [owner_realValue _ ((hSort v.val).symm.trans v.property.1),
        owner_realValue _ ((hSort w.val).symm.trans w.property.1)]
      exact (hOwner v.val w.val).mp (v.property.2.1.trans w.property.2.1.symm)
    have hdh : bit (realValue (h v.val)) = bit (realValue (h w.val)) := by
      rw [← hbit v.val v.property.1,← hbit w.val w.property.1,
        v.property.2.1,w.property.2.1,hdf]
    have he : realValue (f v.val) = realValue (f w.val) ↔
        realValue (h v.val) = realValue (h w.val) := by
      rw [← colour_none,← colour_none,hColour v.val w.val v.property.1 w.property.1]
    exact (show clone (realValue (f v.val)) = clone (realValue (f w.val)) ↔
        realValue (f v.val) = realValue (f w.val) from
      ⟨fun hn => G1.real_ext hbf hdf hn,congrArg clone⟩).trans
        (he.trans ⟨congrArg clone,fun hn => G1.real_ext hbh hdh hn⟩)
  let b : (ℕ × Bool) → Equiv.Perm ℕ := fun t => (hB t).choose
  refine ⟨wreathAut a c b,fun v => point_ext ?_ ?_ ?_ ?_⟩
  · exact (wreath_sort a c b _).trans (hSort v)
  · exact (wreath_owner a c b _).trans (ha v)
  · intro hs
    have hv : sort (f v) = false := (wreath_sort a c b _).symm.trans hs
    change bit (realValue (wreath a c b (f v))) = bit (realValue (h v))
    rw [wreath_realValue a c b _ hv,G1.wreath_bit,owner_realValue _ hv]
    exact hbit v hv
  · intro hs
    have hv : sort (f v) = false := (wreath_sort a c b _).symm.trans hs
    change clone (realValue (wreath a c b (f v))) = clone (realValue (h v))
    rw [wreath_realValue a c b _ hv,G1.wreath_clone,owner_realValue _ hv]
    exact (hB (owner (f v),bit (realValue (f v)))).choose_spec ⟨v,hv,rfl,rfl⟩

theorem embedding_owner_iff (A : model.Piece) (f : A.Embedding Set.univ)
    (x y : A.points) : owner (f.point x) = owner (f.point y) ↔
      owner x.val = owner y.val := by
  constructor
  · intro he
    have hm : f.point (A.func () x) = f.point (A.func () y) :=
      (f.func_eq () x).trans ((congrArg Sum.inr he).trans (f.func_eq () y).symm)
    exact Sum.inr.inj (congrArg Subtype.val (f.injective hm))
  · intro he
    have hm : A.func () x = A.func () y := Subtype.ext (congrArg Sum.inr he)
    exact Sum.inr.inj ((f.func_eq () x).symm.trans
      ((congrArg f.point hm).trans (f.func_eq () y)))

theorem embedding_real_colour (A : model.Piece) (f : A.Embedding Set.univ)
    (x y : A.points) (hx : sort x.val = false) (hy : sort y.val = false) :
    colour (realValue (f.point x)) (realValue (f.point y)) =
      colour (realValue x.val) (realValue y.val) := by
  cases ha : colour (realValue x.val) (realValue y.val) with
  | none =>
    have he := (colour_none _ _).mp ha
    have hxy : x = y := Subtype.ext (point_ext (hx.trans hy.symm)
      (by rw [← owner_realValue _ hx,← owner_realValue _ hy,he])
      (fun _ => congrArg bit he) (fun _ => congrArg clone he))
    subst y
    exact (colour_none _ _).mpr rfl
  | some a =>
    have hrel : model.rel (.inl a) ![x.val,y.val] := ⟨hx,hy,ha⟩
    exact ((f.rel_iff (.inl a) ![x,y]).mpr hrel).2.2

/-- Actual hidden homogeneity includes arbitrary orphan quotient
positions. All source p/q/r labels and all displayed orbitals remain
the interpretations of the same explicit original wreath action. -/
theorem homogeneous : model.Homogeneous := by
  intro A f g
  letI : Finite A.points := A.finite.to_subtype
  exact finite_extension f.point g.point
    (fun x => (f.sort_eq x).trans (g.sort_eq x).symm)
    (fun x y => (embedding_owner_iff A f x y).trans (embedding_owner_iff A g x y).symm)
    (fun x y hx hy =>
      (embedding_real_colour A f x y ((f.sort_eq x).symm.trans hx)
        ((f.sort_eq y).symm.trans hy)).trans
      (embedding_real_colour A g x y ((f.sort_eq x).symm.trans hx)
        ((f.sort_eq y).symm.trans hy)).symm)

end
end CCO.GuardedTwoRoot.G1.Hidden
