import CCO.ResetOrder.Hierarchy.Structures

/-! Commutation with quotient/chart maps is DERIVED from preservation of
actual old named unary terms, rather than added as an embedding oracle. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy

inductive UnaryTerm {I : Type u} (L : OldLanguage I) : I → I → Type u where
  | identity (i : I) : UnaryTerm L i i
  | function {i j} (F : L.Func i j) : UnaryTerm L i j
  | compose {i j k} (s : UnaryTerm L i j) (t : UnaryTerm L j k) : UnaryTerm L i k

namespace UnaryTerm
variable {I : Type u} {L : OldLanguage I} {X : I → Type v} {Y : I → Type w}
def Eval (A : Diagram L X) : {i j : I} → UnaryTerm L i j → X i → X j → Prop
  | _, _, .identity _, x, y => y = x
  | _, _, .function F, x, y => y ∈ A.func F x
  | _, _, .compose s t, x, y => ∃ z, Eval A s x z ∧ Eval A t z y

theorem map_eval {A : Diagram L X} {B : Diagram L Y} (f : Diagram.Embedding A B)
    {i j} (t : UnaryTerm L i j) {x : X i} {y : X j} (h : t.Eval A x y) :
    t.Eval B (f.point i x) (f.point j y) := by
  induction t with
  | identity i => exact congrArg (f.point i) h
  | function F => exact (f.function_iff F x _).2 ⟨y,h,rfl⟩
  | compose s t ihs iht =>
    obtain ⟨z,hz,hzy⟩ := h
    exact ⟨f.point _ z,ihs hz,iht hzy⟩

theorem commute {A : Diagram L X} {B : Diagram L Y} (f : Diagram.Embedding A B)
    {i j} (t : UnaryTerm L i j) (a : X i → X j) (b : Y i → Y j)
    (ha : ∀ x y, t.Eval A x y ↔ y = a x)
    (hb : ∀ x y, t.Eval B x y ↔ y = b x) (x : X i) :
    b (f.point i x) = f.point j (a x) :=
  ((hb _ _).1 (t.map_eval f ((ha _ _).2 rfl))).symm
end UnaryTerm

namespace Charting
variable {R : Type u} {J : R → Type u} {H : Schedule (Sigma J)}
variable {X : Sigma J → Type v} {Y : Sigma J → Type w}
variable {S : System H X} {T : System H Y} {representative : ∀ r, J r}
variable {C : Charting S representative} {D : Charting T representative}
variable {L : OldLanguage (Sigma J)}

structure NamedTerms where
  upward : ∀ i a, UnaryTerm L i (H.coordinate i a)
  chart : ∀ r j, UnaryTerm L ⟨r,j⟩ ⟨r,representative r⟩

structure RealizesNamedTerms (N : NamedTerms (H := H) (representative := representative) (L := L))
    (A : OrderedStructure C L) : Prop where
  upward : ∀ i a x y, (N.upward i a).Eval A.data x y ↔ y = S.up i a x
  chart : ∀ r j x y, (N.chart r j).Eval A.data x y ↔ y = C.back r j x

def OrderedEmbedding.ofNamedTerms
    (N : NamedTerms (H := H) (representative := representative) (L := L))
    {A : OrderedStructure C L} {B : OrderedStructure D L}
    (hA : RealizesNamedTerms N A) (hB : RealizesNamedTerms N B)
    (f : Diagram.Embedding A.data B.data)
    (ho : ∀ i x y, (A.orders i).lt x y → (B.orders i).lt (f.point i x) (f.point i y)) :
    OrderedEmbedding C D L A B where
  old := f
  up_commute i a x := (N.upward i a).commute f (S.up i a) (T.up i a)
    (hA.upward i a) (hB.upward i a) x
  chart_commute r j x := (N.chart r j).commute f (C.back r j) (D.back r j)
    (hA.chart r j) (hB.chart r j) x
  order_preserve := ho

end Charting
end CCO.ResetOrder.Hierarchy
