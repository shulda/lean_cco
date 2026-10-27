import CCO.TypedRelation

/-!
# Actual finite atomic colourings and diversity menus

The optional atomic colour is `none` exactly on the *real* diagonal.
Only `some a` is a diversity edge.  In particular no element of the
diversity palette is a fake identity; different named sorts are disjoint
as points of the dependent sum `Sigma X`.
-/

universe u v w

namespace CCO

structure AtomicSource (ι : Type u) (X : ι → Type v) where
  Atom : ι → ι → Type w
  finiteSort : Fintype ι
  finiteAtom : ∀ i j, Fintype (Atom i j)
  nonemptySort : ∀ i, _root_.Nonempty (X i)
  conv : ∀ {i j}, Atom i j → Atom j i
  conv_invol : ∀ {i j} (a : Atom i j), conv (conv a) = a
  colour : ∀ {i j}, X i → X j → Option (Atom i j)
  colour_none_iff : ∀ {i j} (x : X i) (y : X j),
    colour x y = none ↔ (⟨i, x⟩ : Sigma X) = ⟨j, y⟩
  colour_swap : ∀ {i j} (x : X i) (y : X j) (a : Atom i j),
    colour x y = some a ↔ colour y x = some (conv a)
  realized : ∀ {i j} (a : Atom i j), ∃ x y, colour x y = some a

namespace AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {i j k : ι}

abbrev Menu (i j : ι) : Type w := Set (S.Atom i j)

def atomRel (a : S.Atom i j) : TRel X i j :=
  fun x y => S.colour x y = some a

def menuRel (A : S.Menu i j) : TRel X i j :=
  fun x y => ∃ a ∈ A, S.colour x y = some a

theorem atomRel_ne {a : S.Atom i j} {x : X i} {y : X j}
    (h : S.atomRel a x y) :
    (⟨i, x⟩ : Sigma X) ≠ ⟨j, y⟩ := by
  intro heq
  have hn : S.colour x y = none := (S.colour_none_iff x y).2 heq
  change S.colour x y = some a at h
  rw [hn] at h
  cases h

theorem menuRel_ne {A : S.Menu i j} {x : X i} {y : X j}
    (h : S.menuRel A x y) :
    (⟨i, x⟩ : Sigma X) ≠ ⟨j, y⟩ := by
  rcases h with ⟨a, _, ha⟩
  exact S.atomRel_ne ha

/-- An actual three-vertex triangle: all three diversity atom relations
hold, so pairwise distinctness follows from `colour_none_iff`. -/
def Triangle (a : S.Atom i j) (b : S.Atom j k)
    (c : S.Atom i k) : Prop :=
  ∃ (x : X i) (y : X j) (z : X k),
    S.atomRel a x y ∧ S.atomRel b y z ∧ S.atomRel c x z

theorem triangle_distinct {a : S.Atom i j} {b : S.Atom j k}
    {c : S.Atom i k} (h : S.Triangle a b c) :
    ∃ (x : X i) (y : X j) (z : X k),
      (⟨i, x⟩ : Sigma X) ≠ ⟨j, y⟩ ∧
      (⟨j, y⟩ : Sigma X) ≠ ⟨k, z⟩ ∧
      (⟨i, x⟩ : Sigma X) ≠ ⟨k, z⟩ := by
  rcases h with ⟨x, y, z, hxy, hyz, hxz⟩
  exact ⟨x, y, z, S.atomRel_ne hxy, S.atomRel_ne hyz, S.atomRel_ne hxz⟩

theorem triangle_rotate {a : S.Atom i j} {b : S.Atom j k}
    {c : S.Atom i k} (h : S.Triangle a b c) :
    S.Triangle c (S.conv b) a := by
  rcases h with ⟨x, y, z, hxy, hyz, hxz⟩
  exact ⟨x, z, y, hxz, (S.colour_swap y z b).mp hyz, hxy⟩

theorem triangle_rotate_back {a : S.Atom i j} {b : S.Atom j k}
    {c : S.Atom i k} (h : S.Triangle c (S.conv b) a) :
    S.Triangle a b c := by
  rcases h with ⟨x, z, y, hxz, hzy, hxy⟩
  refine ⟨x, y, z, hxy, ?_, hxz⟩
  have h : S.colour y z = some (S.conv (S.conv b)) :=
    (S.colour_swap z y (S.conv b)).mp hzy
  change S.colour y z = some b
  simpa only [S.conv_invol] using h

theorem triangle_reverse {a : S.Atom i j} {b : S.Atom j k}
    {c : S.Atom i k} (h : S.Triangle a b c) :
    S.Triangle (S.conv b) (S.conv a) (S.conv c) := by
  rcases h with ⟨x, y, z, hxy, hyz, hxz⟩
  exact ⟨z, y, x, (S.colour_swap y z b).mp hyz,
    (S.colour_swap x y a).mp hxy, (S.colour_swap x z c).mp hxz⟩

/-- The STRONG product uses only actual, three-distinct-vertex triangles.
It never inherits a logical identity from RAW composition. -/
def product (A : S.Menu i j) (B : S.Menu j k) : S.Menu i k :=
  { c | ∃ a ∈ A, ∃ b ∈ B, S.Triangle a b c }

def opposite (A : S.Menu i j) : S.Menu j i :=
  { b | S.conv b ∈ A }

theorem opposite_opposite (A : S.Menu i j) :
    S.opposite (S.opposite A) = A := by
  ext a
  simp only [opposite, Set.mem_setOf_eq, S.conv_invol]

theorem mem_opposite {A : S.Menu i j} {a : S.Atom i j}
    (ha : a ∈ A) : S.conv a ∈ S.opposite A := by
  change S.conv (S.conv a) ∈ A
  simpa only [S.conv_invol] using ha

theorem product_mono {A A' : S.Menu i j} {B B' : S.Menu j k}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    S.product A B ⊆ S.product A' B' := by
  rintro c ⟨a, ha, b, hb, htri⟩
  exact ⟨a, hA ha, b, hB hb, htri⟩

theorem product_union_left (A A' : S.Menu i j) (B : S.Menu j k) :
    S.product (A ∪ A') B = S.product A B ∪ S.product A' B := by
  ext c
  constructor
  · rintro ⟨a, ha, b, hb, htri⟩
    rcases ha with ha | ha
    · exact Or.inl ⟨a, ha, b, hb, htri⟩
    · exact Or.inr ⟨a, ha, b, hb, htri⟩
  · intro hc
    rcases hc with ⟨a, ha, b, hb, htri⟩ | ⟨a, ha, b, hb, htri⟩
    · exact ⟨a, Or.inl ha, b, hb, htri⟩
    · exact ⟨a, Or.inr ha, b, hb, htri⟩

theorem product_union_right (A : S.Menu i j) (B B' : S.Menu j k) :
    S.product A (B ∪ B') = S.product A B ∪ S.product A B' := by
  ext c
  constructor
  · rintro ⟨a, ha, b, hb, htri⟩
    rcases hb with hb | hb
    · exact Or.inl ⟨a, ha, b, hb, htri⟩
    · exact Or.inr ⟨a, ha, b, hb, htri⟩
  · intro hc
    rcases hc with ⟨a, ha, b, hb, htri⟩ | ⟨a, ha, b, hb, htri⟩
    · exact ⟨a, ha, b, Or.inl hb, htri⟩
    · exact ⟨a, ha, b, Or.inr hb, htri⟩

theorem product_opposite (A : S.Menu i j) (B : S.Menu j k) :
    S.opposite (S.product A B) =
      S.product (S.opposite B) (S.opposite A) := by
  ext c
  constructor
  · rintro ⟨a, ha, b, hb, htri⟩
    refine ⟨S.conv b, S.mem_opposite hb, S.conv a,
      S.mem_opposite ha, ?_⟩
    simpa only [S.conv_invol] using S.triangle_reverse htri
  · rintro ⟨b, hb, a, ha, htri⟩
    change S.conv c ∈ S.product A B
    exact ⟨S.conv a, ha, S.conv b, hb, S.triangle_reverse htri⟩

/-- Typed atomic Peirce: it is a permutation of actual triangle witnesses,
not a formal algebraic axiom. -/
theorem triangle_peirce (a : S.Atom i j) (b : S.Atom j k)
    (c : S.Atom i k) :
    S.Triangle a b c ↔ S.Triangle c (S.conv b) a :=
  ⟨S.triangle_rotate, S.triangle_rotate_back⟩

end AtomicSource

end CCO
