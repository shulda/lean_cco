import CCO.RealHull.Geometry.FiniteFibre
import CCO.RealHull.Geometry.Localisation
import CCO.RealHull.Geometry.FibreCCO
import CCO.RealHull.Geometry.ClassConsumers

/-! Full source finite-fibre globalisation. Every conditional provider of the
one-cover core is instantiated here from the actual original source. -/
universe v w t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)]
variable {G : Type t} [Group G] [MulAction G M]

theorem source_spoke_localisation (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) : SpokeLocalisation S := by
  classical
  intro R P hP hfix c hc hcover
  exact (spoke_square_localisation S H cco R P hP hfix c hc
    (fun d hd => hcover d hd.1 hd.2)).2

/-- C15: all finite actual fibres have two-power size before globalisation. -/
theorem finite_fibre_size_power_two (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite (FibreSet S A q)] :
    ∃ n : Nat, Nat.card (FibreSet S A q) = 2^n ∧ n ≤ Nat.card (Atom S) :=
  finite_fibre_size_of_CCO S A q H (fibre_semanticCCO S A q H cco)

/-- C16/17: nonempty anchors use one full INTERNAL cover. Empty anchors give
the whole actual source directly; no diversity atom stands for equality. -/
theorem finite_fibre_palette_eq (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite (FibreSet S A q)] :
    {c : Atom S | ∀ a : ↥A, c ∈ square S (q a)} = (fibreSpokeFixer S A q H).val := by
  classical
  apply Set.Subset.antisymm
  · by_cases hA : A.Nonempty
    · exact finite_fibre_palette_eq_of_localisation S A q H cco
        (fibre_semanticCCO S A q H cco) (source_spoke_localisation S H cco) hA
    · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      subst A
      intro c _ p hp
      obtain ⟨a,_⟩ := hp
      exact isEmptyElim a
  · exact fun _ hd => fibreSpokeFixer_le_palette S A q H hd

/-- The finite fibre is ONE whole original invariant-equivalence class. -/
theorem finite_fibre_global_class (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite (FibreSet S A q)]
    (x : FibreSet S A q) (y : M) :
    y ∈ FibreSet S A q ↔ supportEquiv S (fibreSpokeFixer S A q H) x.val y :=
  fibre_class_of_palette_containment S A q H
    (fun c hc => (finite_fibre_palette_eq S A q H cco).le hc) x y

def fibreClassEquiv_of_palette (H : HomogeneousSource S G)
    (hT : {c : Atom S | ∀ a : ↥A, c ∈ square S (q a)} ⊆ (fibreSpokeFixer S A q H).val)
    (x : FibreSet S A q) :
    FibreSet S A q ≃ ClassPoint S () (supportEquiv S (fibreSpokeFixer S A q H)) x.val where
  toFun y := ⟨y.val,(fibre_class_of_palette_containment S A q H hT x y.val).mp y.property⟩
  invFun y := ⟨y.val,(fibre_class_of_palette_containment S A q H hT x y.val).mpr y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def finiteFibreClassEquiv (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite (FibreSet S A q)] (x : FibreSet S A q) :
    FibreSet S A q ≃ ClassPoint S () (supportEquiv S (fibreSpokeFixer S A q H)) x.val :=
  fibreClassEquiv_of_palette S A q H (finite_fibre_palette_eq S A q H cco).le x

/-- C19: whole-class existence is equivalent to the spoke-set palette equation.
This statement needs no finiteness and makes no assertion moving anchors. -/
theorem fibre_whole_class_iff (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (x : FibreSet S A q) :
    (∀ y : M, y ∈ FibreSet S A q ↔ supportEquiv S (fibreSpokeFixer S A q H) x.val y) ↔
      {c : Atom S | ∀ a : ↥A, c ∈ square S (q a)} = (fibreSpokeFixer S A q H).val := by
  constructor
  · intro hclass
    apply Set.Subset.antisymm
    · intro c hc
      obtain ⟨u,v,huv⟩ := fibre_pair_realize S A q H cco c hc
      have hxu := (hclass u.val).mp u.property
      have hxv := (hclass v.val).mp v.property
      have huvR := (supportEquiv S _).val.trans ((supportEquiv S _).val.symm hxu) hxv
      change col S u.val v.val ∈ plus S _ at huvR
      rwa [huv,some_mem_plus] at huvR
    · exact fun _ hd => fibreSpokeFixer_le_palette S A q H hd
  · intro heq
    exact fibre_class_of_palette_containment S A q H heq.le x

theorem finite_fibre_iff_palette_finite_class (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (x : FibreSet S A q) :
    Finite (FibreSet S A q) ↔
      ({c : Atom S | ∀ a : ↥A, c ∈ square S (q a)} = (fibreSpokeFixer S A q H).val ∧
      Finite (ClassPoint S () (supportEquiv S (fibreSpokeFixer S A q H)) x.val)) := by
  constructor
  · intro hfin
    letI := hfin
    refine ⟨finite_fibre_palette_eq S A q H cco,?_⟩
    exact Finite.of_injective (finiteFibreClassEquiv S A q H cco x).symm
      (finiteFibreClassEquiv S A q H cco x).symm.injective
  · rintro ⟨heq,hfin⟩
    letI := hfin
    exact Finite.of_injective (fibreClassEquiv_of_palette S A q H heq.le x)
      (fibreClassEquiv_of_palette S A q H heq.le x).injective

end CCO.RealHull.Geometry
