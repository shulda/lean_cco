import CCO.APRamseyReadout.TupleReadout

/-! Order comparisons of ALL finite marked term presentations. Their
actual defined values lie in the full generated support. Diagonal
equality codes recover defined source presentations, without an inverse
from arbitrary hidden roots to the selected original root set. -/

universe u v w r l k
namespace CCO.APRamseyReadout.TupleInterpretation
open CCO.FullCode
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable {L : Language.{l}} {V : Type k}
variable {S : CCO.AtomicSource.{u,v,w} ι X} {C : Structure L V} {scheme : RootScheme L}
variable (D : TupleInterpretation (G := G) S C scheme)

/-- Compare actual values of two marked presentations. Both original
roots may coincide; undefined and wrong-tag presentations give false. -/
def TermOrder {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A)
    (x y : A.vertices) (p q : Presentation D.normal scheme) : Prop :=
  ∃ u v : D.support A,
    u.val ∈ (D.eta x.val).presentation D.normal p ∧
    v.val ∈ (D.eta y.val).presentation D.normal q ∧ D.ReadoutComparison a u v

/-- Actual witnesses uniquely determine the two compared values; the
predicate adds no arbitrary bits beyond their prescribed support order. -/
theorem termOrder_iff {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A)
    (x y : A.vertices) (p q : Presentation D.normal scheme) (u v : D.support A)
    (hu : u.val ∈ (D.eta x.val).presentation D.normal p)
    (hv : v.val ∈ (D.eta y.val).presentation D.normal q) :
    D.TermOrder a x y p q ↔ D.ReadoutComparison a u v := by
  constructor
  · rintro ⟨u',v',hu',hv',hlt⟩
    have heU : u' = u := Subtype.ext ((D.eta x.val).presentation_functional D.normal p hu' hu)
    have heV : v' = v := Subtype.ext ((D.eta y.val).presentation_functional D.normal q hv' hv)
    simpa only [heU,heV] using hlt
  · intro hlt
    exact ⟨u,v,hu,hv,hlt⟩

theorem termOrder_undefined_left {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A)
    (x y : A.vertices) (p q : Presentation D.normal scheme)
    (hp : (D.eta x.val).presentation D.normal p = ∅) : ¬ D.TermOrder a x y p q := by
  rintro ⟨u,_,hu,_,_⟩
  exact Set.notMem_empty u.val (hp ▸ hu)

theorem termOrder_undefined_right {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A)
    (x y : A.vertices) (p q : Presentation D.normal scheme)
    (hq : (D.eta y.val).presentation D.normal q = ∅) : ¬ D.TermOrder a x y p q := by
  rintro ⟨_,v,_,hv,_⟩
  exact Set.notMem_empty v.val (hq ▸ hv)

/-- A defined presentation at a selected target root has the actual
source value. Its image is the displayed target value, by functionality.
This is a presentation preimage, not an inverse on all hidden roots. -/
theorem presentation_preimage (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (x : A.vertices) (p : Presentation D.normal scheme) (z : D.support B)
    (hz : z.val ∈ (D.eta (e.toEmbedding x).val).presentation D.normal p) :
    ∃ u : D.support A, u.val ∈ (D.eta x.val).presentation D.normal p ∧
      (D.supportEmbedding H e).point u = z := by
  have hd : EqualityCode D.normal (D.eta (e.toEmbedding x).val)
      (D.eta (e.toEmbedding x).val) p p := ⟨z.val,hz,hz⟩
  obtain ⟨u,hu,_⟩ := ((D.codeEmbedding H e).equality_iff x x p p).mp hd
  let u' : D.support A := ⟨u,(D.object A).presentation_mem_support D.normal x p hu⟩
  refine ⟨u',hu,Subtype.ext ?_⟩
  exact (D.eta (e.toEmbedding x).val).presentation_functional D.normal p
    (D.supportEmbedding_presentation H e x p u' hu) hz

/-- Full preservation and reflection for the actual ordered support
map, retaining every coordinate and same-root/cross-root term pair. -/
theorem termOrder_embedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : D.ReadoutEmbedding H a b) (x y : A.vertices)
    (p q : Presentation D.normal scheme) :
    D.TermOrder b (f.old.toEmbedding x) (f.old.toEmbedding y) p q ↔
      D.TermOrder a x y p q := by
  constructor
  · rintro ⟨u,v,hu,hv,hlt⟩
    obtain ⟨u',hu',heU⟩ := D.presentation_preimage H f.old x p u hu
    obtain ⟨v',hv',heV⟩ := D.presentation_preimage H f.old y q v hv
    refine ⟨u',v',hu',hv',?_⟩
    apply (f.order_iff u' v').mp
    simpa only [ReadoutComparison,heU,heV] using hlt
  · rintro ⟨u,v,hu,hv,hlt⟩
    exact ⟨(D.supportEmbedding H f.old).point u,(D.supportEmbedding H f.old).point v,
      D.supportEmbedding_presentation H f.old x p u hu,
      D.supportEmbedding_presentation H f.old y q v hv,(f.order_iff u v).mpr hlt⟩

theorem termOrder_restrict (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (b : D.ReadoutOn B) (x y : A.vertices) (p q : Presentation D.normal scheme) :
    D.TermOrder (D.restrictReadout H e b) x y p q ↔
      D.TermOrder b (e.toEmbedding x) (e.toEmbedding y) p q :=
  (D.termOrder_embedding H (D.restrictReadoutEmbedding H e b) x y p q).symm

/-- Every support point has an actual marked normal presentation.
Consequently all finite term comparisons determine the WHOLE order. -/
theorem termOrder_faithful {A : CCO.FiniteInduced (X := X)} (a b : D.ReadoutOn A)
    (h : ∀ x y p q, D.TermOrder a x y p q ↔ D.TermOrder b x y p q) : a = b := by
  apply ReadoutOn.ext
  apply LinearOrder.ext_lt
  intro u v
  obtain ⟨x,p,hu⟩ := ((D.object A).mem_support_iff_presentation D.normal D.valid u.val).mp
    u.property
  obtain ⟨y,q,hv⟩ := ((D.object A).mem_support_iff_presentation D.normal D.valid v.val).mp
    v.property
  exact (D.termOrder_iff a x y p q u v hu hv).symm.trans
    ((h x y p q).trans (D.termOrder_iff b x y p q u v hu hv))

/-- An old map preserving and reflecting all finite term-order tables
has exactly its canonical ordered support extension. -/
def readoutEmbedding_of_termOrders (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (e : CCO.InducedEmbedding S A B)
    (h : ∀ x y p q,
      D.TermOrder b (e.toEmbedding x) (e.toEmbedding y) p q ↔ D.TermOrder a x y p q) :
    D.ReadoutEmbedding H a b := by
  refine ⟨e,?_⟩
  intro u v
  obtain ⟨x,p,hu⟩ := ((D.object A).mem_support_iff_presentation D.normal D.valid u.val).mp
    u.property
  obtain ⟨y,q,hv⟩ := ((D.object A).mem_support_iff_presentation D.normal D.valid v.val).mp
    v.property
  have hu' := D.supportEmbedding_presentation H e x p u hu
  have hv' := D.supportEmbedding_presentation H e y q v hv
  exact (D.termOrder_iff b (e.toEmbedding x) (e.toEmbedding y) p q
      ((D.supportEmbedding H e).point u) ((D.supportEmbedding H e).point v) hu' hv').symm.trans
    ((h x y p q).trans (D.termOrder_iff a x y p q u v hu hv))

@[simp] theorem readoutEmbedding_of_termOrders_old (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (e : CCO.InducedEmbedding S A B)
    (h : ∀ x y p q,
      D.TermOrder b (e.toEmbedding x) (e.toEmbedding y) p q ↔ D.TermOrder a x y p q) :
    (D.readoutEmbedding_of_termOrders H e h).old = e := rfl

end
end CCO.APRamseyReadout.TupleInterpretation
