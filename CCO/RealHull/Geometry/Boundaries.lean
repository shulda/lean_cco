import CCO.RealHull.Geometry.UniformFibres
import CCO.RealHull.Geometry.FibreConsumers

/-! Empty bases give the WHOLE real source. Singleton fibres give TRUE
equality globally, never a diversity identity atom. -/
universe v w t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]

def emptyFibreEquiv (q : ↥(∅ : Finset M) → Atom S) : FibreSet S ∅ q ≃ M where
  toFun := Subtype.val
  invFun x := ⟨x,by rw [fibre_empty_anchor S q]; trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem empty_fibre_finite_iff (q : ↥(∅ : Finset M) → Atom S) :
    Finite (FibreSet S ∅ q) ↔ Finite M := by
  constructor
  · intro h
    letI := h
    exact Finite.of_injective (emptyFibreEquiv S q).symm (emptyFibreEquiv S q).symm.injective
  · intro h
    letI := h
    exact Finite.of_injective (emptyFibreEquiv S q) (emptyFibreEquiv S q).injective

variable {G : Type t} [Group G] [MulAction G M]

theorem empty_spokeFixer_universal (H : HomogeneousSource S G)
    (q : ↥(∅ : Finset M) → Atom S) :
    (fibreSpokeFixer S ∅ q H).val = Set.univ := by
  apply Set.ext
  intro d
  constructor
  · intro _; trivial
  · intro _ p hp
    obtain ⟨a,_⟩ := hp
    exact isEmptyElim a

theorem empty_spokeFixer_top (H : HomogeneousSource S G)
    (q : ↥(∅ : Finset M) → Atom S) :
    supportEquiv S (fibreSpokeFixer S ∅ q H) = (⊤ : ColourEq S ()) := by
  apply ColourEq.ext
  intro x y
  change (col S x y ∈ plus S (fibreSpokeFixer S ∅ q H).val) ↔ True
  rw [empty_spokeFixer_universal S H q]
  cases hc : col S x y <;> simp

theorem singleton_fibre_true_equality (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (q : ↥A → Atom S)
    [Nonempty (FibreSet S A q)] [Subsingleton (FibreSet S A q)] :
    supportEquiv S (fibreSpokeFixer S A q H) = (⊥ : ColourEq S ()) := by
  apply supportEquiv_empty S
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hdT := fibreSpokeFixer_le_palette S A q H hd
  obtain ⟨x,y,hxy⟩ := fibre_pair_realize S A q H cco d hdT
  have he : x = y := Subsingleton.elim _ _
  subst y
  rw [(col_none S x.val x.val).mpr rfl] at hxy
  cases hxy

def finiteFibrePaletteSupport (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (q : ↥A → Atom S)
    [Nonempty (FibreSet S A q)] [Finite (FibreSet S A q)] : Support S :=
  ⟨{c : Atom S | ∀ a : ↥A, c ∈ square S (q a)},by
    rw [finite_fibre_palette_eq S A q H cco]
    exact (fibreSpokeFixer S A q H).property⟩

theorem finiteFibrePaletteSupport_eq (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (q : ↥A → Atom S)
    [Nonempty (FibreSet S A q)] [Finite (FibreSet S A q)] :
    finiteFibrePaletteSupport S H cco A q = fibreSpokeFixer S A q H :=
  Subtype.ext (finite_fibre_palette_eq S A q H cco)

theorem finite_fibre_actual_ET_class (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (q : ↥A → Atom S)
    [Nonempty (FibreSet S A q)] [Finite (FibreSet S A q)] (x : FibreSet S A q) (y : M) :
    y ∈ FibreSet S A q ↔ supportEquiv S (finiteFibrePaletteSupport S H cco A q) x.val y := by
  rw [finiteFibrePaletteSupport_eq]
  exact finite_fibre_global_class S A q H cco x y

end CCO.RealHull.Geometry
