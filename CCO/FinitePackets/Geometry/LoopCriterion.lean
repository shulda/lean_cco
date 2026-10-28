import CCO.FinitePackets.Geometry.Basic
import CCO.RealHull.Canonical.Loopless
import CCO.RealHull.Canonical.RamseySubset

/-! The loop criterion on ACTUAL original relative classes. The Ramsey
direction selects only finitely many representatives in one old upper class;
the converse realizes actual cliques and moves them into any prescribed class.
No quotient-source inheritance or endpoint exactness is used. -/

universe v w t
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original CCO.RealHull.Geometry CCO.RealHull.Canonical

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

/-- A single old pair determines containment of its entire diversity orbital. -/
theorem atomBelow_of_colour (E : ColourEq S ()) {a : Atom S} {x y : M}
    (hxy : col S x y = some a) (hE : E x y) : AtomBelow S E a := by
  intro u v huv
  exact (E.property x y u v (hxy.trans huv.symm)).mp hE

/-- The source's finite triangle Ramsey number bounds representatives of
distinct J-classes in ONE K-class, unless K contains a loop outside J. -/
theorem relative_no_looped_no_embedding (J K : ColourEq S ())
    (hloop : ∀ a : Atom S, Looped S a → AtomBelow S K a → AtomBelow S J a)
    (x : M) :
    ¬ Nonempty (Fin (sourceTriangleRamsey S) ↪ RelativeClass J.val K.val x) := by
  classical
  rintro ⟨e⟩
  let rep : Fin (sourceTriangleRamsey S) → M := fun i => (e i).out.val
  have hinj : Function.Injective rep := by
    intro i j hij
    apply e.injective
    apply Quotient.out_injective
    exact Subtype.ext hij
  obtain ⟨a,ha,i,j,hij,hcol⟩ := looped_colour_of_embedding S ⟨rep,hinj⟩
  have hK : K (rep i) (rep j) :=
    K.val.trans (K.val.symm (e i).out.property) (e j).out.property
  have hJ := hloop a ha (atomBelow_of_colour S K hcol hK) _ _ hcol
  exact hij (e.injective (Quotient.out_equiv_out.mp hJ))

/-- Finiteness is established BEFORE the natural-cardinality bound. This
direction uses no homogeneity or CCO, and permits empty diversity palettes. -/
theorem finite_relative_of_no_looped (J K : ColourEq S ())
    (hloop : ∀ a : Atom S, Looped S a → AtomBelow S K a → AtomBelow S J a)
    (x : M) :
    Finite (RelativeClass J.val K.val x) ∧
      relativeIndex J.val K.val x < sourceTriangleRamsey S :=
  TriangleRamsey.finite_card_lt_of_no_embedding _
    (relative_no_looped_no_embedding S J K hloop x)

variable {G : Type t} [Group G] [MulAction G M]

/-- A looped orbital of K outside J gives arbitrarily many ACTUAL distinct
J-classes inside the K-class of any prescribed old real point. -/
theorem looped_relative_clique (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (J K : ColourEq S ()) (a : Atom S)
    (hloop : Looped S a) (hKa : AtomBelow S K a) (hJa : ¬ AtomBelow S J a)
    (x : M) (n : ℕ) : Nonempty (Fin n ↪ RelativeClass J.val K.val x) := by
  classical
  let q : ↥(∅ : Finset M) → Atom S := fun b =>
    False.elim (Finset.notMem_empty b.val b.property)
  letI : Nonempty (FibreSet S ∅ q) :=
    ⟨⟨Classical.choice (S.nonemptySort ()), by
      intro b
      exact False.elim (Finset.notMem_empty b.val b.property)⟩⟩
  obtain ⟨f,_,hf⟩ := looped_fibre_clique S ∅ q H cco a
    (by intro b; exact False.elim (Finset.notMem_empty b.val b.property)) hloop (n+1)
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H () (f (Fin.last n)).val x
  let point : Fin n → M := fun i => g • (f i.castSucc).val
  have hpoint (i : Fin n) : K x (point i) := by
    have hne : Fin.last n ≠ i.castSucc := by
      intro h
      have hh := congrArg Fin.val h
      have hi := i.isLt
      simp only [Fin.val_last, Fin.val_castSucc] at hh
      omega
    have hc := (col_invariant S H g _ _).trans (hf _ _ hne)
    have hK := hKa _ _ hc
    rw [hg] at hK
    exact hK
  let cls : Fin n → RelativeClass J.val K.val x :=
    fun i => Quotient.mk _ ⟨point i,hpoint i⟩
  refine ⟨⟨cls,?_⟩⟩
  intro i j hcls
  by_contra hij
  have hne : i.castSucc ≠ j.castSucc := fun he =>
    hij (Fin.ext (congrArg (fun z : Fin (n+1) => z.val) he))
  have hc : col S (point i) (point j) = some a :=
    (col_invariant S H g _ _).trans (hf _ _ hne)
  have hrel : J (point i) (point j) := by
    change (Quotient.mk _ (⟨point i,hpoint i⟩ : {y // K x y})) =
      Quotient.mk _ (⟨point j,hpoint j⟩ : {y // K x y}) at hcls
    have he := Quotient.exact hcls
    exact he
  exact hJa (atomBelow_of_colour S J hc hrel)

theorem finiteIndex_no_looped (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (J K : ColourEq S ())
    (hfin : FiniteIndex S J K) :
    ∀ a : Atom S, Looped S a → AtomBelow S K a → AtomBelow S J a := by
  intro a hloop hKa
  by_contra hJa
  obtain ⟨x⟩ := S.nonemptySort ()
  letI := hfin x
  obtain ⟨e⟩ := looped_relative_clique S H cco J K a hloop hKa hJa x
    (relativeIndex J.val K.val x + 1)
  have hn := Nat.card_le_card_of_injective e e.injective
  simp only [Nat.card_fin] at hn
  exact Nat.not_succ_le_self _ hn

/-- The source relative loop criterion. All indices are quotients of actual
old classes; neither endpoint is assumed RAW exact. -/
theorem finiteIndex_iff_no_looped (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (J K : ColourEq S ()) (_hJK : J ≤ K) :
    FiniteIndex S J K ↔
      ∀ a : Atom S, Looped S a → AtomBelow S K a → AtomBelow S J a := by
  exact ⟨finiteIndex_no_looped S H cco J K,
    fun h x => (finite_relative_of_no_looped S J K h x).1⟩

/-- The quantitative form uses the ORIGINAL palette's finite Ramsey number. -/
theorem relativeIndex_lt_ramsey_of_finiteIndex (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (J K : ColourEq S ())
    (hfin : FiniteIndex S J K) (x : M) :
    relativeIndex J.val K.val x < sourceTriangleRamsey S :=
  (finite_relative_of_no_looped S J K (finiteIndex_no_looped S H cco J K hfin) x).2

end CCO.FinitePackets.Geometry
