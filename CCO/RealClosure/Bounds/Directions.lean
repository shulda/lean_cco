import CCO.RealClosure.Bounds.Packet
import CCO.RealHull.Canonical.Source
import CCO.RealHull.Canonical.PositiveEven
import CCO.ExactCRT.SourceLattice
import CCO.RawExact.ConvolutionFromHelly

/-! Minimal infinite directions are original full-lattice equivalences.
Their exactness is derived from actual Ramsey triangles and actual cliques,
without quotient minimal-cut or a falsely exact greatest finite packet. -/
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def IsDirection (E : ColourEq S ()) : Prop :=
  ¬ FiniteClasses S E ∧ ∀ F : ColourEq S (), F < E → FiniteClasses S F
abbrev Direction := {E : ColourEq S () // IsDirection S E}

noncomputable def directionCount : ℕ := Nat.card (Direction S)

theorem direction_eq_of_le {E F : ColourEq S ()} (hE : IsDirection S E)
    (hF : IsDirection S F) (hle : E ≤ F) : E = F := by
  by_contra hne
  exact hE.1 (hF.2 E (lt_of_le_of_ne hle hne))

theorem distinct_direction_inf_finite {E F : ColourEq S ()}
    (hE : IsDirection S E) (hF : IsDirection S F) (hne : E ≠ F) :
    FiniteClasses S (E ⊓ F) := by
  apply hE.2
  apply lt_of_le_of_ne inf_le_left
  intro he
  have hEF : E ≤ F := by rw [← he]; exact inf_le_right
  exact hne (direction_eq_of_le S hE hF hEF)

theorem exists_direction_le {E : ColourEq S ()} (hE : ¬ FiniteClasses S E) :
    ∃ D : Direction S, D.val ≤ E := by
  obtain ⟨D,hD,hmin⟩ := wellFounded_lt.has_min
    {F : ColourEq S () | F ≤ E ∧ ¬ FiniteClasses S F} ⟨E,le_rfl,hE⟩
  refine ⟨⟨D,hD.2,?_⟩,hD.1⟩
  intro F hFD
  by_contra hF
  exact hmin F ⟨hFD.le.trans hD.1,hF⟩ hFD

theorem finiteClasses_top_iff : FiniteClasses S (⊤ : ColourEq S ()) ↔ Finite M := by
  constructor
  · intro h
    obtain ⟨x⟩ := S.nonemptySort ()
    letI := h x
    exact Finite.of_surjective (fun y : ClassPoint S () (⊤ : ColourEq S ()) x => y.val)
      (fun y => ⟨⟨y,trivial⟩,rfl⟩)
  · intro h x
    letI := h
    exact Finite.of_injective Subtype.val Subtype.val_injective

theorem direction_nonempty_of_infinite [Infinite M] : Nonempty (Direction S) := by
  have htop : ¬ FiniteClasses S (⊤ : ColourEq S ()) := by
    intro h
    letI := (finiteClasses_top_iff S).mp h
    exact not_finite M
  obtain ⟨D,_⟩ := exists_direction_le S htop
  exact ⟨D⟩

theorem directionCount_pos [Infinite M] : 0 < directionCount S := by
  letI := direction_nonempty_of_infinite S
  exact Nat.card_pos

def gammaEq (p : Atom S) : ColourEq S () := supportEquiv S (gamma S p)

theorem gamma_le_of_atom (E : ColourEq S ()) {p : Atom S}
    (hp : p ∈ diversitySupport S E) : gammaEq S p ≤ E := by
  intro x y hxy
  have hgen := generated_plus_le S {p} (equivalenceSupport S E)
    (Set.singleton_subset_iff.mpr hp)
  exact (mem_plus_diversitySupport S E x y).mp (hgen hxy)

variable {G : Type t} [Group G] [MulAction G M]

/-- A finite Ramsey triangle in an actual infinite class supplies a looped
OLD atom inside that original equivalence. -/
theorem infinite_class_looped_atom (H : HomogeneousSource S G) (E : ColourEq S ())
    (hE : ¬ FiniteClasses S E) (x : M) :
    ∃ a : Atom S, Looped S a ∧ a ∈ diversitySupport S E := by
  classical
  have hnot : ¬ Finite (ClassPoint S () E x) :=
    fun h => hE ((finiteClasses_iff_at S H E x).mpr h)
  letI : Infinite (ClassPoint S () E x) := not_finite_iff_infinite.mp hnot
  let e : Fin (sourceTriangleRamsey S) ↪ M := {
    toFun i := (Infinite.natEmbedding (ClassPoint S () E x) i.val).val
    inj' := by
      intro i j h
      exact Fin.ext ((Infinite.natEmbedding _).injective (Subtype.ext h)) }
  obtain ⟨a,ha,i,j,_,hij⟩ := looped_colour_of_embedding S e
  refine ⟨a,ha,?_⟩
  exact ⟨e i,e j,E.val.trans
    (E.val.symm (Infinite.natEmbedding (ClassPoint S () E x) i.val).property)
    (Infinite.natEmbedding (ClassPoint S () E x) j.val).property,hij⟩

/-- A looped atom has infinite connectivity classes, by arbitrarily large
ACTUAL cliques aligned to one fixed real point. -/
theorem looped_gamma_not_finite (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (p : Atom S) (hp : Looped S p) :
    ¬ FiniteClasses S (gammaEq S p) := by
  classical
  intro hfin
  obtain ⟨x⟩ := S.nonemptySort ()
  letI := hfin x
  let q : ↥(∅ : Finset M) → Atom S := fun a => isEmptyElim a
  letI : Nonempty (FibreSet S ∅ q) := ⟨x,fun a => isEmptyElim a⟩
  let n := Nat.card (ClassPoint S () (gammaEq S p) x) + 1
  obtain ⟨f,hf,hcol⟩ := looped_fibre_clique S ∅ q H cco p
    (fun a => isEmptyElim a) hp n
  let zero : Fin n := ⟨0,Nat.zero_lt_succ _⟩
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H () (f zero).val x
  let e : Fin n → ClassPoint S () (gammaEq S p) x := fun i => ⟨g • (f i).val,by
    by_cases he : i = zero
    · subst i
      rw [hg]
    · change col S x (g • (f i).val) ∈ plus S (gamma S p).val
      rw [← hg,col_invariant S H,hcol zero i (Ne.symm he)]
      exact (some_mem_plus S _ p).mpr (subset_generated S {p} (Set.mem_singleton _))⟩
  have hinj : Function.Injective e := by
    intro i j he
    apply hf
    apply Subtype.ext
    have hval := congrArg (fun y : ClassPoint S () (gammaEq S p) x => y.val) he
    exact (MulAction.injective g) hval
  have hc := Nat.card_le_card_of_injective e hinj
  simp only [Nat.card_fin] at hc
  exact Nat.not_succ_le_self _ hc

theorem direction_eq_looped_gamma (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (D : Direction S) :
    ∃ p : Atom S, Looped S p ∧ D.val = gammaEq S p := by
  obtain ⟨x⟩ := S.nonemptySort ()
  obtain ⟨p,hp,hpD⟩ := infinite_class_looped_atom S H D.val D.property.1 x
  have hle := gamma_le_of_atom S D.val hpD
  have he : gammaEq S p = D.val := by
    by_contra hn
    exact looped_gamma_not_finite S H cco p hp (D.property.2 _ (lt_of_le_of_ne hle hn))
  exact ⟨p,hp,he.symm⟩

theorem gamma_eq_even_of_looped (p : Atom S) (hp : Looped S p) :
    gamma S p = evenSupport S p := by
  apply Subtype.ext
  apply Set.Subset.antisymm
  · exact generated_le S {p} (evenSupport S p)
      (Set.singleton_subset_iff.mpr (subset_generated S (square S p) hp))
  · exact generated_le S (square S p) (gamma S p)
      (square_le_support S (gamma S p) (subset_generated S {p} (Set.mem_singleton _)))

theorem isExactEq_of_word (E : ColourEq S ()) (word : RawWord S () ())
    (hw : RawWord.relation S word = E.val.r) : ExactCRT.IsExactEq S (i := ()) E.val := by
  obtain ⟨x⟩ := S.nonemptySort ()
  have hne : TRel.Nonempty (RawWord.relation S word) := by
    refine ⟨x,x,?_⟩
    exact congrFun (congrFun hw.symm x) x ▸ E.val.refl x
  refine ⟨RawExact.singletonExact S word hne,?_⟩
  change RawExact.evaluate S [word] = E.val.r
  exact (RawExact.evaluate_single S word).trans hw

/-- C03: the precise positive even RAW word is retained as a source output. -/
theorem direction_positive_word (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (D : Direction S) :
    ∃ p : Atom S, ∃ n : ℕ, RawWord.relation S (positiveEvenWord S p n) = D.val.val.r := by
  obtain ⟨p,hp,hD⟩ := direction_eq_looped_gamma S H cco D
  obtain ⟨n,hn⟩ := exists_positive_even_word S H p
  refine ⟨p,n,?_⟩
  rw [hD, gammaEq,gamma_eq_even_of_looped S p hp]
  exact hn

theorem direction_exact (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (D : Direction S) : ExactCRT.IsExactEq S (i := ()) D.val.val := by
  obtain ⟨p,n,hn⟩ := direction_positive_word S H cco D
  exact isExactEq_of_word S D.val _ hn
end CCO.RealClosure.Bounds
