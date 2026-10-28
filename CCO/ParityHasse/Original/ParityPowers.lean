import CCO.ParityHasse.Original.OrbitalBipartite
import CCO.RawWords
import Mathlib.Order.OrderIsoNat

/-! Finite-palette stabilization of actual RAW powers, including length
zero. Positive stabilized even/odd powers represent all parity walks. -/
universe u v w t
namespace CCO.ParityHasse.Original

variable {A : Type v}

def relPow (R : A → A → Prop) : Nat → A → A → Prop
  | 0 => Eq
  | n + 1 => RawSymmetric.compose R (relPow R n)

@[simp] theorem relPow_zero (R : A → A → Prop) (x y : A) : relPow R 0 x y ↔ x = y := Iff.rfl
@[simp] theorem relPow_succ (R : A → A → Prop) (n : Nat) (x y : A) :
    relPow R (n+1) x y ↔ ∃ z, R x z ∧ relPow R n z y := Iff.rfl

theorem relPow_add (R : A → A → Prop) (n m : Nat) :
    relPow R (n + m) = RawSymmetric.compose (relPow R n) (relPow R m) := by
  induction n with
  | zero =>
    funext x y
    apply propext
    simp [relPow, RawSymmetric.compose]
  | succ n ih =>
    funext x y
    apply propext
    simp only [Nat.succ_add, relPow_succ, ih, RawSymmetric.compose]
    constructor
    · rintro ⟨a, hxa, b, hab, hby⟩
      exact ⟨b, ⟨a, hxa, hab⟩, hby⟩
    · rintro ⟨b, ⟨a, hxa, hab⟩, hby⟩
      exact ⟨a, hxa, b, hab, hby⟩

theorem relPow_mono_two (R : A → A → Prop)
    (hs : ∀ x y, R x y → R y x) (hserial : ∀ x, ∃ y, R x y) :
    ∀ n x y, relPow R n x y → relPow R (n+2) x y := by
  intro n
  induction n with
  | zero =>
    intro x y hxy
    subst y
    obtain ⟨z, hxz⟩ := hserial x
    exact ⟨z, hxz, x, hs x z hxz, rfl⟩
  | succ n ih =>
    rintro x y ⟨z, hxz, hzy⟩
    exact ⟨z, hxz, ih z y hzy⟩

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

theorem colourInvariant_relPow (H : HomogeneousSource S G)
    {R : X i → X i → Prop} (hR : ColourInvariant S i R) :
    ∀ n, ColourInvariant S i (relPow R n) := by
  intro n
  induction n with
  | zero => exact (⊥ : ColourEq S i).2
  | succ n ih => exact colourInvariant_comp S H hR ih

theorem colour_support_injective : Function.Injective
    (fun R : {R : X i → X i → Prop // ColourInvariant S i R} => S.rawSupport R.val) := by
  intro R T h
  change S.rawSupport R.val = S.rawSupport T.val at h
  apply Subtype.ext
  funext x y
  apply propext
  constructor
  · intro hr
    have hc : S.colour x y ∈ S.rawSupport T.val := by rw [← h]; exact ⟨x,y,hr,rfl⟩
    obtain ⟨a,b,hab,hcol⟩ := hc
    exact (T.2 a b x y hcol).mp hab
  · intro ht
    have hc : S.colour x y ∈ S.rawSupport R.val := by rw [h]; exact ⟨x,y,ht,rfl⟩
    obtain ⟨a,b,hab,hcol⟩ := hc
    exact (R.2 a b x y hcol).mp hab

/-- Finite actual palette, rather than a countability or graph finiteness hypothesis. -/
theorem finite_colour_relations : Finite {R : X i → X i → Prop // ColourInvariant S i R} := by
  letI := S.finiteAtom i i
  exact Finite.of_injective _ (colour_support_injective S)

/-- Both parity chains have positive common stabilized representatives. -/
theorem exists_positive_parity_stabilization (H : HomogeneousSource S G)
    {R : X i → X i → Prop} (hR : ColourInvariant S i R)
    (hs : ∀ x y, R x y → R y x) (hserial : ∀ x, ∃ y, R x y) :
    ∃ N : Nat, 0 < N ∧
      (∀ n, relPow R (2*n) ≤ relPow R (2*N)) ∧
      (∀ n, relPow R (2*n+1) ≤ relPow R (2*N+1)) ∧
      (∀ n, N ≤ n → relPow R (2*N) = relPow R (2*n)) ∧
      (∀ n, N ≤ n → relPow R (2*N+1) = relPow R (2*n+1)) := by
  let C := {R : X i → X i → Prop // ColourInvariant S i R}
  letI : Finite C := finite_colour_relations S
  let even : Nat →o C :=
    { toFun := fun n => ⟨relPow R (2*n), colourInvariant_relPow S H hR _⟩
      monotone' := monotone_nat_of_le_succ (fun n => by
        intro x y hxy
        have h := relPow_mono_two R hs hserial (2*n) x y hxy
        simpa only [Nat.mul_add, Nat.mul_one] using h) }
  let odd : Nat →o C :=
    { toFun := fun n => ⟨relPow R (2*n+1), colourInvariant_relPow S H hR _⟩
      monotone' := monotone_nat_of_le_succ (fun n => by
        intro x y hxy
        have h := relPow_mono_two R hs hserial (2*n+1) x y hxy
        convert h using 1 <;> omega) }
  obtain ⟨ne, he⟩ := WellFoundedGT.monotone_chain_condition even
  obtain ⟨no, ho⟩ := WellFoundedGT.monotone_chain_condition odd
  let N := max ne no + 1
  have hne : ne ≤ N := by omega
  have hno : no ≤ N := by omega
  have ee (n : Nat) (hn : N ≤ n) : even N = even n := (he N hne).symm.trans (he n (by omega))
  have oo (n : Nat) (hn : N ≤ n) : odd N = odd n := (ho N hno).symm.trans (ho n (by omega))
  refine ⟨N, by omega, ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : n ≤ N
    · exact even.monotone hn
    · exact le_of_eq (congrArg Subtype.val (ee n (by omega))).symm
  · intro n
    by_cases hn : n ≤ N
    · exact odd.monotone hn
    · exact le_of_eq (congrArg Subtype.val (oo n (by omega))).symm
  · intro n hn
    exact congrArg Subtype.val (ee n hn)
  · intro n hn
    exact congrArg Subtype.val (oo n hn)

/-- The recursive RAW power is exactly the relation of walks of that
literal length in the actual original atomic graph. -/
theorem relPow_atom_iff_walk (c : S.Atom i i) (n : Nat) (x y : X i) :
    relPow (S.atomRel c) n x y ↔ ∃ p : (atomGraph S c).Walk x y, p.length = n := by
  induction n generalizing x y with
  | zero =>
    constructor
    · intro hxy
      subst y
      exact ⟨.nil, rfl⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => rfl
      | cons h p => simp at hp
  | succ n ih =>
    constructor
    · rintro ⟨z, hxz, hzy⟩
      obtain ⟨p, hp⟩ := (ih z y).mp hzy
      have hg : (atomGraph S c).Adj x z := hxz
      refine ⟨.cons hg p, ?_⟩
      change p.length + 1 = n + 1
      omega
    · rintro ⟨p, hp⟩
      cases p with
      | nil => simp at hp
      | cons h p =>
        refine ⟨_, h, (ih _ _).mpr ⟨p, ?_⟩⟩
        simpa only [SimpleGraph.Walk.length_cons, Nat.succ_inj] using hp

/-- Literal repeated original atomic word, with true equality at zero. -/
def atomWord (c : S.Atom i i) : Nat → RawWord S i i
  | 0 => .nil i
  | n+1 => .atom c (atomWord c n)

@[simp] theorem atomWord_relation (c : S.Atom i i) (n : Nat) :
    RawWord.relation S (atomWord S c n) = relPow (S.atomRel c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TRel.comp (S.atomRel c) (RawWord.relation S (atomWord S c n)) = _
    rw [ih]
    rfl

end CCO.ParityHasse.Original
