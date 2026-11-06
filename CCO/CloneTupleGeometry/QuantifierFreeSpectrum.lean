import CCO.TransitionClosure.OriginalFiniteCylinderPartition
import CCO.TerminalLattice.StrongPaletteBridge

/-! Finite quantifier-free spectrum tests in the actual typed quotient
language. Binary names are the finite complete B049 cylinder names and
their predicates omit exactly the diagonal of the SAME hidden sort.
Equality has a separate branch with its proved actual diagonal support.
The two free variables have the displayed quotient sort tags; hence these
are typed quantifier-free formulas, with no real representative variables. -/

universe u v w t
namespace CCO.CloneTupleGeometry.QuotientPairQF
open ParityHasse.Original TransitionClosure TerminalLattice
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Actual tagged hidden vertices; equality identifies neither different
original sorts nor different FULL quotient-coordinate symbols. -/
abbrev HiddenPoint := (i : ι) × (J : ColourEq S i) × Quotient J.val

def hiddenPoint {i : ι} (J : ColourEq S i) (q : Quotient J.val) : HiddenPoint S :=
  ⟨i,J,q⟩

def hiddenSort (p : HiddenPoint S) : (i : ι) × ColourEq S i := ⟨p.1,p.2.1⟩

theorem hiddenPoint_injective {i : ι} (J : ColourEq S i) :
    Function.Injective (hiddenPoint S J) := by
  intro q r h
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2

/-- A unary hidden-sort tag is exactly membership in that actual quotient
carrier. No real representative is selected by this conversion. -/
theorem hiddenPoint_of_sort {i : ι} (J : ColourEq S i) (p : HiddenPoint S)
    (h : hiddenSort S p = ⟨i,J⟩) : ∃ q, hiddenPoint S J q = p := by
  rcases p with ⟨j,K,q⟩
  have hji : j = i := congrArg Sigma.fst h
  subst j
  have hKJ : K = J := eq_of_heq (Sigma.mk.inj h).2
  subst K
  exact ⟨q,rfl⟩

def HiddenEqual {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (q : Quotient J.val) (r : Quotient K.val) : Prop :=
  hiddenPoint S J q = hiddenPoint S K r

abbrev Name {i j : ι} (J : ColourEq S i) (K : ColourEq S j) :=
  {P : S.Menu i j // P ∈ originalTypedCylinderNames S J K}

instance nameFinite {i j : ι} (J : ColourEq S i) (K : ColourEq S j) :
    Finite (Name S J K) :=
  (originalTypedCylinderNames_finite S J K).to_subtype

/-- Only the genuine named off-diagonal relation is atomic. Its complete
palette is unchanged; hidden equality is handled by its own formula. -/
def NamedRelation {i j : ι} {J : ColourEq S i} {K : ColourEq S j}
    (P : Name S J K) (q : Quotient J.val) (r : Quotient K.val) : Prop :=
  ¬HiddenEqual S J K q r ∧ originalTypedCylinderSemanticRelation S J K P.val q r

inductive Formula {i j : ι} (J : ColourEq S i) (K : ColourEq S j) where
  | falsum : Formula J K
  | truth : Formula J K
  | equal : Formula J K
  | named (P : Name S J K) : Formula J K
  | neg (p : Formula J K) : Formula J K
  | conj (p q : Formula J K) : Formula J K
  | disj (p q : Formula J K) : Formula J K

namespace Formula
variable {S} {i j : ι} {J : ColourEq S i} {K : ColourEq S j}

def eval (q : Quotient J.val) (r : Quotient K.val) : Formula S J K → Prop
  | .falsum => False
  | .truth => True
  | .equal => HiddenEqual S J K q r
  | .named P => NamedRelation S P q r
  | .neg p => ¬p.eval q r
  | .conj p p' => p.eval q r ∧ p'.eval q r
  | .disj p p' => p.eval q r ∨ p'.eval q r

def disjoin : List (Formula S J K) → Formula S J K
  | [] => .falsum
  | p :: ps => .disj p (disjoin ps)

theorem eval_disjoin (ps : List (Formula S J K)) (q : Quotient J.val) (r : Quotient K.val) :
    (disjoin ps).eval q r ↔ ∃ p ∈ ps, p.eval q r := by
  induction ps with
  | nil => simp [disjoin,eval]
  | cons p ps ih => simp [disjoin,eval,ih]
end Formula

variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

include H in
/-- Logical hidden equality has the full diversity support of its actual
quotient kernel. The witness pair consists of DISTINCT real points. -/
theorem diagonal_spectrum {i : ι} (J : ColourEq S i) (q : Quotient J.val) :
    originalTypedQuotientPairSpectrum S J J q q = originalEquivDiversityPalette S J := by
  ext a
  constructor
  · rintro ⟨x,y,hx,hy,hcol⟩
    exact ⟨x,y,Quotient.exact (hx.trans hy.symm),hcol⟩
  · rintro ⟨x,y,hJ,hcol⟩
    obtain ⟨z,hz⟩ := Quotient.exists_rep q
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x z
    have hmove := colourInvariant_groupInvariant S H J.property g x y hJ
    have hzy : J z (g • y) := by simpa only [hg] using hmove
    have hy : Quotient.mk J.val (g • y) = q := (Quotient.sound (J.val.symm hzy)).trans hz
    have hc := (S.colourInvariant_of_homogeneous H g x y).trans hcol
    refine ⟨z,g • y,hz,hy,?_⟩
    change S.colour z (g • y) = some a
    simpa only [hg] using hc

/-- A source coefficient of the finite formula, independent of its free
variables. It is computed from the actual hidden diagonal support. -/
def DiagonalContains {i j : ι} (J : ColourEq S i) (K : ColourEq S j) (a : S.Atom i j) : Prop :=
  ∃ q : Quotient J.val, ∃ r : Quotient K.val,
    HiddenEqual S J K q r ∧ a ∈ originalTypedQuotientPairSpectrum S J K q r

include H in
theorem diagonalContains_iff {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (q : Quotient J.val) (r : Quotient K.val) (a : S.Atom i j)
    (he : HiddenEqual S J K q r) :
    DiagonalContains S J K a ↔ a ∈ originalTypedQuotientPairSpectrum S J K q r := by
  have hs : (⟨i,J⟩ : (i : ι) × ColourEq S i) = ⟨j,K⟩ :=
    congrArg (fun p : HiddenPoint S => (⟨p.1,p.2.1⟩ : (i : ι) × ColourEq S i)) he
  have hij : i = j := congrArg Sigma.fst hs
  subst j
  have hJK : J = K := eq_of_heq (Sigma.mk.inj hs).2
  subst K
  have hqr : q = r := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  subst r
  constructor
  · rintro ⟨q',r',he',ha⟩
    have hqr' : q' = r' := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he').2)).2
    subst r'
    rw [diagonal_spectrum S H J q'] at ha
    rw [diagonal_spectrum S H J q]
    exact ha
  · intro ha
    exact ⟨q,q,rfl,ha⟩

def containingNames {i j : ι} (J : ColourEq S i) (K : ColourEq S j) (a : S.Atom i j) :
    List (Name S J K) := by
  classical
  letI : Fintype (Name S J K) := Fintype.ofFinite _
  exact (Finset.univ.filter (fun P : Name S J K => a ∈ P.val)).toList

theorem mem_containingNames {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (a : S.Atom i j) (P : Name S J K) : P ∈ containingNames S J K a ↔ a ∈ P.val := by
  classical
  simp [containingNames]

/-- The literal finite disjunction of all named complete cylinders
containing a, with a separate equality clause. No quantified real point
or quotient representative occurs in this formula syntax. -/
def membershipFormula {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (a : S.Atom i j) : Formula S J K := by
  classical
  exact .disj (.conj .equal (if DiagonalContains S J K a then .truth else .falsum))
    (Formula.disjoin ((containingNames S J K a).map Formula.named))

include H in
theorem membershipFormula_eval {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (a : S.Atom i j) (q : Quotient J.val) (r : Quotient K.val) :
    (membershipFormula S J K a).eval q r ↔
      a ∈ originalTypedQuotientPairSpectrum S J K q r := by
  classical
  have hd :
      (Formula.conj Formula.equal
        (if DiagonalContains S J K a then Formula.truth else Formula.falsum)).eval q r ↔
        HiddenEqual S J K q r ∧ DiagonalContains S J K a := by
    by_cases h : DiagonalContains S J K a <;> simp [h,Formula.eval]
  have hn :
      (Formula.disjoin ((containingNames S J K a).map Formula.named)).eval q r ↔
        ∃ P : Name S J K, a ∈ P.val ∧ NamedRelation S P q r := by
    rw [Formula.eval_disjoin]
    constructor
    · rintro ⟨f,hf,he⟩
      obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hf
      exact ⟨P,(mem_containingNames S J K a P).mp hP,he⟩
    · rintro ⟨P,hP,he⟩
      exact ⟨Formula.named P,List.mem_map.mpr
        ⟨P,(mem_containingNames S J K a P).mpr hP,rfl⟩,he⟩
  change ((Formula.conj Formula.equal
      (if DiagonalContains S J K a then Formula.truth else Formula.falsum)).eval q r ∨
      (Formula.disjoin ((containingNames S J K a).map Formula.named)).eval q r) ↔ _
  rw [hd,hn]
  constructor
  · rintro (⟨he,ha⟩ | ⟨P,ha,_,hP⟩)
    · exact (diagonalContains_iff S H J K q r a he).mp ha
    · change P.val = originalTypedQuotientPairSpectrum S J K q r at hP
      exact hP ▸ ha
  · intro ha
    by_cases he : HiddenEqual S J K q r
    · exact Or.inl ⟨he,(diagonalContains_iff S H J K q r a he).mpr ha⟩
    · refine Or.inr ⟨⟨originalTypedQuotientPairSpectrum S J K q r,
        originalTypedQuotientPairSpectrum_is_named S H J K q r ⟨a,ha⟩⟩,ha,he,rfl⟩

end
end CCO.CloneTupleGeometry.QuotientPairQF
