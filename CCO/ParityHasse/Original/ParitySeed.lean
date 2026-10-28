import CCO.ParityHasse.Original.ParityPowers
import CCO.ParityHasse.Original.RelativeIndices
import CCO.RawExact.Presentations

/-!
# The actual parity connectivity seed

Even walks and all walks give full original invariant equivalences. In
the absence of odd closed walks, each connectivity class has exactly two
even-walk classes. Positive stabilized original RAW words represent the
even and odd profiles; the connectivity union need not itself be exact.
-/

universe u v w t
namespace CCO.ParityHasse.Original

section Walks
variable {A : Type v} (R : A → A → Prop)

def EvenWalk (x y : A) : Prop := ∃ n, Even n ∧ relPow R n x y
def OddWalk (x y : A) : Prop := ∃ n, Odd n ∧ relPow R n x y
def ConnectedWalk (x y : A) : Prop := ∃ n, relPow R n x y

@[simp] theorem relPow_one (x y : A) : relPow R 1 x y ↔ R x y := by
  simp [relPow, RawSymmetric.compose]

theorem relPow_symmetric (hs : ∀ x y, R x y → R y x) :
    ∀ n x y, relPow R n x y → relPow R n y x := by
  intro n
  induction n with
  | zero => exact fun _ _ h => h.symm
  | succ n ih =>
    rintro x y ⟨z, hxz, hzy⟩
    rw [relPow_add]
    exact ⟨z, ih z y hzy, (relPow_one R z x).mpr (hs x z hxz)⟩

theorem connectedWalk_iff_even_or_odd (x y : A) :
    ConnectedWalk R x y ↔ EvenWalk R x y ∨ OddWalk R x y := by
  constructor
  · rintro ⟨n, hn⟩
    rcases Nat.even_or_odd n with he | ho
    · exact Or.inl ⟨n, he, hn⟩
    · exact Or.inr ⟨n, ho, hn⟩
  · rintro (⟨n, _, hn⟩ | ⟨n, _, hn⟩) <;> exact ⟨n, hn⟩

def evenSetoid (hs : ∀ x y, R x y → R y x) : Setoid A where
  r := EvenWalk R
  iseqv := ⟨fun x => ⟨0, ⟨0, rfl⟩, rfl⟩,
    fun {x y} ⟨n, hn, hxy⟩ => ⟨n, hn, relPow_symmetric R hs n x y hxy⟩,
    by
      rintro x y z ⟨n, hn, hxy⟩ ⟨m, hm, hyz⟩
      refine ⟨n+m, hn.add hm, ?_⟩
      rw [relPow_add]
      exact ⟨y, hxy, hyz⟩⟩

def connectivitySetoid (hs : ∀ x y, R x y → R y x) : Setoid A where
  r := ConnectedWalk R
  iseqv := ⟨fun x => ⟨0, rfl⟩,
    fun {x y} ⟨n, hxy⟩ => ⟨n, relPow_symmetric R hs n x y hxy⟩,
    by
      rintro x y z ⟨n, hxy⟩ ⟨m, hyz⟩
      refine ⟨n+m, ?_⟩
      rw [relPow_add]
      exact ⟨y, hxy, hyz⟩⟩

theorem even_odd_disjoint (hs : ∀ x y, R x y → R y x)
    (noOdd : ∀ x n, Odd n → ¬ relPow R n x x) (x y : A) :
    ¬ (EvenWalk R x y ∧ OddWalk R x y) := by
  rintro ⟨⟨n, hn, hxy⟩, ⟨m, hm, hxy'⟩⟩
  apply noOdd x (m+n) (hm.add_even hn)
  rw [relPow_add]
  exact ⟨y, hxy', relPow_symmetric R hs n x y hxy⟩

theorem relPow_le_setoid (F : Setoid A) (hRF : ∀ x y, R x y → F x y) :
    ∀ n x y, relPow R n x y → F x y := by
  intro n
  induction n with
  | zero => intro x y h; subst y; exact F.refl x
  | succ n ih =>
    rintro x y ⟨z, hxz, hzy⟩
    exact F.trans (hRF x z hxz) (ih z y hzy)

end Walks

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

private theorem atom_colourInvariant (c : S.Atom i i) : ColourInvariant S i (S.atomRel c) := by
  intro x y x' y' hcol
  change S.colour x y = some c ↔ S.colour x' y' = some c
  rw [hcol]

private theorem atom_symmetric (c : S.Atom i i) :
    ∀ x y, S.atomRel c x y → S.atomRel c y x :=
  colourInvariant_symmetric S (atom_colourInvariant S c)

private theorem atom_serial (H : HomogeneousSource S G) (c : S.Atom i i) :
    ∀ x, ∃ y, S.atomRel c x y :=
  invariant_nonempty_serial S H (atom_colourInvariant S c) (S.realized c)

/-- The actual full even-walk equivalence. -/
def evenColourEq (H : HomogeneousSource S G) (c : S.Atom i i) : ColourEq S i :=
  ⟨evenSetoid (S.atomRel c) (atom_symmetric S c), by
    intro x y x' y' hcol
    constructor
    · rintro ⟨n, hn, hxy⟩
      exact ⟨n, hn, (colourInvariant_relPow S H (atom_colourInvariant S c) n _ _ _ _ hcol).mp hxy⟩
    · rintro ⟨n, hn, hxy⟩
      exact ⟨n, hn, (colourInvariant_relPow S H (atom_colourInvariant S c) n _ _ _ _ hcol).mpr hxy⟩⟩

/-- The actual full connectivity equivalence. No exactness is asserted. -/
def connectivityColourEq (H : HomogeneousSource S G) (c : S.Atom i i) : ColourEq S i :=
  ⟨connectivitySetoid (S.atomRel c) (atom_symmetric S c), by
    intro x y x' y' hcol
    constructor
    · rintro ⟨n, hxy⟩
      exact ⟨n, (colourInvariant_relPow S H (atom_colourInvariant S c) n _ _ _ _ hcol).mp hxy⟩
    · rintro ⟨n, hxy⟩
      exact ⟨n, (colourInvariant_relPow S H (atom_colourInvariant S c) n _ _ _ _ hcol).mpr hxy⟩⟩

theorem even_le_connectivity (H : HomogeneousSource S G) (c : S.Atom i i) :
    evenColourEq S H c ≤ connectivityColourEq S H c :=
  fun _ _ ⟨n, _, hn⟩ => ⟨n, hn⟩

/-- The parity union describes X using the even equivalence and odd profile. -/
theorem connectivity_eq_even_union_odd (H : HomogeneousSource S G)
    (c : S.Atom i i) (x y : X i) :
    connectivityColourEq S H c x y ↔
      evenColourEq S H c x y ∨ OddWalk (S.atomRel c) x y :=
  connectedWalk_iff_even_or_odd (S.atomRel c) x y

/-- The actual two relative classes are represented by a and an old
c-neighbour b, in every original connectivity class. -/
theorem parity_seed_index_two (H : HomogeneousSource S G) (c : S.Atom i i)
    (noOdd : ∀ x n, Odd n → ¬ relPow (S.atomRel c) n x x) (a : X i) :
    relativeIndex (evenColourEq S H c).val (connectivityColourEq S H c).val a = 2 := by
  obtain ⟨b, hab⟩ := atom_serial S H c a
  let Y := evenColourEq S H c
  let K := connectivityColourEq S H c
  have hob : OddWalk (S.atomRel c) a b := ⟨1, odd_one, (relPow_one _ _ _).mpr hab⟩
  have hKab : K a b := ⟨1, (relPow_one _ _ _).mpr hab⟩
  let qa : RelativeClass Y.val K.val a := Quotient.mk _ ⟨a, K.val.refl a⟩
  let qb : RelativeClass Y.val K.val a := Quotient.mk _ ⟨b, hKab⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨qa, qb, ?_, ?_⟩
  · intro h
    have hY := Quotient.exact h
    exact even_odd_disjoint (S.atomRel c) (atom_symmetric S c) noOdd a b ⟨hY, hob⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rcases (connectivity_eq_even_union_odd S H c a x.val).mp x.property with he | ho
    · exact Or.inl (Quotient.sound (Y.val.symm he))
    · apply Or.inr
      apply Quotient.sound
      rcases ho with ⟨n, hn, hax⟩
      refine ⟨n+1, hn.add_one, ?_⟩
      rw [relPow_add]
      exact ⟨a, relPow_symmetric (S.atomRel c) (atom_symmetric S c) n a x.val hax,
        (relPow_one _ _ _).mpr hab⟩

theorem parity_seed_cover (H : HomogeneousSource S G) (c : S.Atom i i)
    (noOdd : ∀ x n, Odd n → ¬ relPow (S.atomRel c) n x x) :
    evenColourEq S H c ⋖ connectivityColourEq S H c := by
  obtain ⟨a⟩ := S.nonemptySort i
  exact covBy_of_relativeIndex_two S H _ _ (even_le_connectivity S H c) a
    (parity_seed_index_two S H c noOdd a)

/-- If the old atom is contained in F, all its finite walks stay in F. -/
theorem connectivity_le_of_atom_le (H : HomogeneousSource S G) (c : S.Atom i i)
    (F : ColourEq S i) (hcF : ∀ x y, S.atomRel c x y → F x y) :
    connectivityColourEq S H c ≤ F := by
  rintro x y ⟨n, hn⟩
  exact relPow_le_setoid (S.atomRel c) F.val hcF n x y hn

/-- An atom outside E witnesses that its connectivity is not below E. -/
theorem connectivity_not_le_of_atom_disjoint (H : HomogeneousSource S G)
    (c : S.Atom i i) (E : ColourEq S i)
    (hcE : ∀ x y, S.atomRel c x y → ¬ E x y) :
    ¬ connectivityColourEq S H c ≤ E := by
  intro h
  obtain ⟨x, y, hxy⟩ := S.realized c
  exact hcE x y hxy (h (show connectivityColourEq S H c x y from
    ⟨1, (relPow_one _ _ _).mpr hxy⟩))

/-- C11/C12's profiles are single genuinely positive old-atom RAW words;
the witness N is positive, so neither word is the zero-length identity. -/
theorem parity_profiles_positive_raw (H : HomogeneousSource S G) (c : S.Atom i i) :
    ∃ N : Nat, 0 < N ∧
      (∀ x y, evenColourEq S H c x y ↔ RawWord.relation S (atomWord S c (2*N)) x y) ∧
      (∀ x y, OddWalk (S.atomRel c) x y ↔ RawWord.relation S (atomWord S c (2*N+1)) x y) := by
  obtain ⟨N, hN, he, ho, _, _⟩ := exists_positive_parity_stabilization S H
    (atom_colourInvariant S c) (atom_symmetric S c) (atom_serial S H c)
  refine ⟨N, hN, ?_, ?_⟩
  · intro x y
    rw [atomWord_relation]
    constructor
    · rintro ⟨n, hn, hxy⟩
      obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
      exact he k x y hxy
    · intro hxy
      exact ⟨2*N, by exact even_two.mul_right N, hxy⟩
  · intro x y
    rw [atomWord_relation]
    constructor
    · rintro ⟨n, hn, hxy⟩
      obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hn
      exact ho k x y hxy
    · intro hxy
      exact ⟨2*N+1, (even_two.mul_right N).add_one, hxy⟩

/-- The two profiles are NONEMPTY actual RAW exact presentations. Their
single words are the positive stabilized words exported above. -/
theorem parity_profiles_nonempty_exact (H : HomogeneousSource S G) (c : S.Atom i i) :
    ∃ Y O : RawExact.NonemptyExact S i i,
      (∀ x y, RawExact.evaluate S Y.words x y ↔ evenColourEq S H c x y) ∧
      (∀ x y, RawExact.evaluate S O.words x y ↔ OddWalk (S.atomRel c) x y) := by
  obtain ⟨N, _hN, he, ho⟩ := parity_profiles_positive_raw S H c
  obtain ⟨a⟩ := S.nonemptySort i
  obtain ⟨x, y, hxy⟩ := S.realized c
  let ew := atomWord S c (2*N)
  let ow := atomWord S c (2*N+1)
  have evalE (z t : X i) : RawExact.evaluate S [ew] z t ↔ evenColourEq S H c z t := by
    simpa only [RawExact.evaluate, List.mem_singleton, forall_eq] using (he z t).symm
  have evalO (z t : X i) : RawExact.evaluate S [ow] z t ↔ OddWalk (S.atomRel c) z t := by
    simpa only [RawExact.evaluate, List.mem_singleton, forall_eq] using (ho z t).symm
  let Y : RawExact.NonemptyExact S i i :=
    ⟨[ew], a, a, (evalE a a).mpr ((evenColourEq S H c).val.refl a)⟩
  let O : RawExact.NonemptyExact S i i :=
    ⟨[ow], x, y, (evalO x y).mpr ⟨1, odd_one, (relPow_one _ _ _).mpr hxy⟩⟩
  exact ⟨Y, O, evalE, evalO⟩

/-- C12's source-facing seed package. In particular Y need not contain a
preselected E, and X is admitted as a FULL invariant equivalence. -/
theorem exists_actual_parity_seed (H : HomogeneousSource S G) (c : S.Atom i i)
    (noOdd : ∀ x n, Odd n → ¬ relPow (S.atomRel c) n x x) (a : X i) :
    ∃ Y K : ColourEq S i, Y ≤ K ∧ relativeIndex Y.val K.val a = 2 ∧ Y ⋖ K ∧
      (∀ F : ColourEq S i, (∀ x y, S.atomRel c x y → F x y) → K ≤ F) ∧
      (∀ E : ColourEq S i, (∀ x y, S.atomRel c x y → ¬ E x y) → ¬ K ≤ E) :=
  ⟨evenColourEq S H c, connectivityColourEq S H c,
    even_le_connectivity S H c, parity_seed_index_two S H c noOdd a,
    parity_seed_cover S H c noOdd,
    fun F => connectivity_le_of_atom_le S H c F,
    fun E => connectivity_not_le_of_atom_disjoint S H c E⟩

end CCO.ParityHasse.Original
