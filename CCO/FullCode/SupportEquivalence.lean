import CCO.FullCode.EmbeddingBijection
import CCO.FullCode.Cofinality

universe u v w a b
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type w}

namespace Object
variable {C : Structure L V} {D : Structure L W} {S : RootScheme L}
  {A : Type a} {B : Type b} {N : NormalForms L} {O : Object C S A} {P : Object D S B}

theorem Embedding.onSupport_surjective (f : Embedding N O P) (hC : N.Valid C)
    (hD : N.Valid D) (surj : Function.Surjective f.point) :
    Function.Surjective (f.onSupport hC hD).point := by
  intro y
  obtain ⟨b, p, hy⟩ := (P.mem_support_iff_presentation N hD y.val).mp y.property
  obtain ⟨a, rfl⟩ := surj b
  obtain ⟨x, hx, _⟩ := (f.equality_iff a a p p).mp ⟨y.val, hy, hy⟩
  let x' : O.support := ⟨x, O.presentation_mem_support N a p hx⟩
  refine ⟨x', Subtype.ext ?_⟩
  exact (P.root (f.point a)).presentation_functional N p
    (f.extendPoint_presentation hC x' a p hx) hy

noncomputable def Embedding.supportEquiv (f : Embedding N O P) (hC : N.Valid C)
    (hD : N.Valid D) (surj : Function.Surjective f.point) : O.support ≃ P.support :=
  Equiv.ofBijective (f.onSupport hC hD).point
    ⟨(f.onSupport hC hD).injective, f.onSupport_surjective hC hD surj⟩

end Object

def fullSupportEquiv (C : Structure L V) (S : RootScheme L) (generated : RootGenerated C S) :
    V ≃ (Object.full C S).support where
  toFun x := ⟨x, by rw [generated]; trivial⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

def fullSupportEmbedding (C : Structure L V) (S : RootScheme L) (generated : RootGenerated C S) :
    Structure.Embedding C (Object.full C S).supportStructure where
  point := fullSupportEquiv C S generated
  injective := (fullSupportEquiv C S generated).injective
  sort_eq _ := rfl
  map_func _ _ _ h := h
  reflect_func _F _x y hy := ⟨y.val, hy, rfl⟩
  unary_iff _ _ := Iff.rfl
  binary_iff _ _ _ := Iff.rfl

end CCO.FullCode
