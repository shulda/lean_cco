import CCO.ActionBridge
import CCO.APRamseyReadout.TemplateBounds
import CCO.FullCode.Cofinality
import CCO.FullCode.Naturality

/-! Canonical marked support maps for a genuinely multi-coordinate
interpretation. Original finite homogeneity supplies a map on the whole
hidden interpretation; the complete coordinate code removes that choice
on the generated support. No hidden homogeneity, completion, Ramsey, or
cofinality assumption is used. -/

universe u v w r l k
namespace CCO.APRamseyReadout
open CCO.FullCode
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable {L : Language.{l}} {V : Type k}

/-- Literal interpretation data. The source instance supplies the actual
root tuple and actual action on its entire hidden structure. Finiteness
below is derived from the valid finite semantic normal forms. -/
structure TupleInterpretation (S : CCO.AtomicSource.{u,v,w} ι X)
    (C : Structure L V) (scheme : RootScheme L) where
  normal : NormalForms L
  valid : normal.Valid C
  eta : Sigma X → Root C scheme
  eta_injective : Function.Injective eta
  motion : G → Structure.Embedding C C
  eta_equivariant : ∀ g p, (eta p).map (motion g) = eta (g • p)

namespace TupleInterpretation
variable {S : CCO.AtomicSource.{u,v,w} ι X}
variable {C : Structure L V} {scheme : RootScheme L}
variable (D : TupleInterpretation (G := G) S C scheme)

/-- Mark exactly the supplied old vertices by their full coordinate
tuples. Other compatible roots need not be among these marked roots. -/
def object (A : CCO.FiniteInduced (X := X)) : Object C scheme A.vertices where
  root a := D.eta a.val
  injective := D.eta_injective.comp Subtype.val_injective

abbrev support (A : CCO.FiniteInduced (X := X)) : Set V := (D.object A).support

abbrev supportStructure (A : CCO.FiniteInduced (X := X)) : Structure L (D.support A) :=
  (D.object A).supportStructure

def coordinate {A : CCO.FiniteInduced (X := X)} (a : A.vertices)
    (j : Fin (scheme.arity (D.eta a.val).tag)) : D.support A :=
  ⟨(D.eta a.val).coordinate j,(D.object A).coordinate_mem_support a j⟩

/-- The whole generated support is finite, even when distinct marked
presentations name the same value or some presentations are undefined. -/
theorem support_finite (A : CCO.FiniteInduced (X := X)) : (D.support A).Finite := by
  letI : Finite A.vertices := A.finite_vertices.to_subtype
  exact (D.object A).support_finite D.normal D.valid

instance supportFinite (A : CCO.FiniteInduced (X := X)) : Finite (D.support A) :=
  (D.support_finite A).to_subtype

theorem support_card_bound (A : CCO.FiniteInduced (X := X)) :
    Nat.card (D.support A) ≤ Nat.card (Presentation D.normal scheme) * Nat.card A.vertices := by
  letI : Finite A.vertices := A.finite_vertices.to_subtype
  exact template_card_bound D.normal (D.object A) D.valid

theorem support_valid (A : CCO.FiniteInduced (X := X)) :
    D.normal.Valid (D.supportStructure A) :=
  D.normal.valid_of_embedding (C.inclusion (D.support A) (C.isClosed_closure _)) D.valid

/-- Homogeneity extends this exact old map. Equivariance of all tuple
coordinates gives preservation and reflection of every complete code. -/
def codeEmbedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) :
    Object.Embedding D.normal (D.object A) (D.object B) := by
  let g := Classical.choose (H.extends_partial_iso A B e)
  have hg := Classical.choose_spec (H.extends_partial_iso A B e)
  have roots (a : A.vertices) :
      (D.eta a.val).map (D.motion g) = D.eta (e.toEmbedding a).val :=
    (D.eta_equivariant g a.val).trans (congrArg D.eta (hg a))
  exact {
    point := e.toEmbedding
    injective := e.toEmbedding.injective
    tag_eq := fun a => (congrArg Root.tag (roots a)).symm
    equality_iff := by
      intro a b p q
      change EqualityCode D.normal (D.eta (e.toEmbedding a).val)
        (D.eta (e.toEmbedding b).val) p q ↔ _
      rw [← roots a,← roots b]
      exact equalityCode_map D.normal (D.motion g) _ _ p q
    unary_iff := by
      intro U a p
      change UnaryCode D.normal U (D.eta (e.toEmbedding a).val) p ↔ _
      rw [← roots a]
      exact unaryCode_map D.normal (D.motion g) U _ p
    binary_iff := by
      intro R a b p q
      change BinaryCode D.normal R (D.eta (e.toEmbedding a).val)
        (D.eta (e.toEmbedding b).val) p q ↔ _
      rw [← roots a,← roots b]
      exact binaryCode_map D.normal (D.motion g) R _ _ p q }

@[simp] theorem codeEmbedding_point (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) :
    (D.codeEmbedding H e).point = e.toEmbedding := rfl

/-- The unique full induced map on the entire marked support. It
reflects every partial function domain as well as all unary/binary codes. -/
def supportEmbedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) :
    Structure.Embedding (D.supportStructure A) (D.supportStructure B) :=
  (D.codeEmbedding H e).onSupport D.valid D.valid

theorem supportEmbedding_coordinate (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (a : A.vertices) (j : Fin (scheme.arity (D.eta a.val).tag)) :
    (D.supportEmbedding H e).point (D.coordinate a j) =
      D.coordinate (e.toEmbedding a) (((D.codeEmbedding H e).tag_eq a).symm ▸ j) := by
  apply Subtype.ext
  exact (D.codeEmbedding H e).extendPoint_coordinate D.valid D.valid a j

/-- The image of each marked root is the prescribed full target tuple;
no unselected compatible root is chosen in its place. -/
theorem supportEmbedding_root (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (a : A.vertices) :
    ((D.object A).markedRoot a).map (D.supportEmbedding H e) =
      (D.object B).markedRoot (e.toEmbedding a) := by
  apply Root.ext_coordinates
    (r := ((D.object A).markedRoot a).map (D.supportEmbedding H e))
    (s := (D.object B).markedRoot (e.toEmbedding a))
    ((D.codeEmbedding H e).tag_eq a).symm
  intro j
  exact D.supportEmbedding_coordinate H e a j

/-- Every complete marked presentation is transported, including all
same-root and cross-root terms and the identity-coordinate cases. -/
theorem supportEmbedding_presentation (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (a : A.vertices) (p : Presentation D.normal scheme) (x : D.support A)
    (hx : x.val ∈ (D.eta a.val).presentation D.normal p) :
    ((D.supportEmbedding H e).point x).val ∈
      (D.eta (e.toEmbedding a).val).presentation D.normal p :=
  (D.codeEmbedding H e).extendPoint_presentation D.valid x a p hx

theorem supportEmbedding_presentation_iff (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (a : A.vertices) (p : Presentation D.normal scheme) (x : D.support A) :
    ((D.supportEmbedding H e).point x).val ∈
        (D.eta (e.toEmbedding a).val).presentation D.normal p ↔
      x.val ∈ (D.eta a.val).presentation D.normal p := by
  constructor
  · intro hx
    obtain ⟨b,q,hxb⟩ := ((D.object A).mem_support_iff_presentation D.normal D.valid x.val).mp
      x.property
    have htarget := D.supportEmbedding_presentation H e b q x hxb
    obtain ⟨z,hza,hzb⟩ := ((D.codeEmbedding H e).equality_iff a b p q).mp
      ⟨((D.supportEmbedding H e).point x).val,hx,htarget⟩
    have hz : z = x.val := (D.eta b.val).presentation_functional D.normal q hzb hxb
    exact hz ▸ hza
  · exact D.supportEmbedding_presentation H e a p x

/-- Agreement on ALL marked coordinates determines the entire induced
support map. It does not assert an inverse for arbitrary hidden maps. -/
theorem supportEmbedding_unique (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (f : Structure.Embedding (D.supportStructure A) (D.supportStructure B))
    (hf : ∀ a j, f.point (D.coordinate a j) =
      D.coordinate (e.toEmbedding a) (((D.codeEmbedding H e).tag_eq a).symm ▸ j)) :
    f = D.supportEmbedding H e := by
  apply (D.object A).embedding_unique_on_coordinates
  intro a j
  exact (hf a j).trans (D.supportEmbedding_coordinate H e a j).symm

def oldId (A : CCO.FiniteInduced (X := X)) : CCO.InducedEmbedding S A A :=
  ⟨Function.Embedding.refl _,fun _ => rfl,fun _ _ => rfl⟩

def oldComp {A B E : CCO.FiniteInduced (X := X)}
    (g : CCO.InducedEmbedding S B E) (f : CCO.InducedEmbedding S A B) :
    CCO.InducedEmbedding S A E where
  toEmbedding := ⟨g.toEmbedding ∘ f.toEmbedding,g.toEmbedding.injective.comp f.toEmbedding.injective⟩
  preserves_sort x := (g.preserves_sort _).trans (f.preserves_sort x)
  preserves_colours x y := (f.preserves_colours x y).trans (g.preserves_colours _ _)

theorem codeEmbedding_id (H : CCO.HomogeneousSource S G) (A : CCO.FiniteInduced (X := X)) :
    D.codeEmbedding H (oldId A) = Object.Embedding.id D.normal (D.object A) :=
  Object.Embedding.ext (fun _ => rfl)

theorem codeEmbedding_comp (H : CCO.HomogeneousSource S G)
    {A B E : CCO.FiniteInduced (X := X)}
    (g : CCO.InducedEmbedding S B E) (f : CCO.InducedEmbedding S A B) :
    D.codeEmbedding H (oldComp g f) = (D.codeEmbedding H g).comp (D.codeEmbedding H f) :=
  Object.Embedding.ext (fun _ => rfl)

@[simp] theorem supportEmbedding_id (H : CCO.HomogeneousSource S G)
    (A : CCO.FiniteInduced (X := X)) :
    D.supportEmbedding H (oldId A) = Structure.Embedding.id (D.supportStructure A) := by
  change (D.codeEmbedding H (oldId A)).onSupport D.valid D.valid = _
  rw [D.codeEmbedding_id H A]
  exact Object.onSupport_id D.valid

theorem supportEmbedding_comp (H : CCO.HomogeneousSource S G)
    {A B E : CCO.FiniteInduced (X := X)}
    (g : CCO.InducedEmbedding S B E) (f : CCO.InducedEmbedding S A B) :
    D.supportEmbedding H (oldComp g f) =
      (D.supportEmbedding H g).comp (D.supportEmbedding H f) := by
  change (D.codeEmbedding H (oldComp g f)).onSupport D.valid D.valid = _
  rw [D.codeEmbedding_comp H g f]
  exact Object.onSupport_comp (D.codeEmbedding H f) (D.codeEmbedding H g) D.valid D.valid D.valid

end TupleInterpretation
end
end CCO.APRamseyReadout
