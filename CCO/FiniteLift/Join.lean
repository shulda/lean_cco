import CCO.FiniteLift.Kernel
import CCO.ExactCRT.AbstractRelations
import CCO.RawExact.ExactCalculusSource
import CCO.RawExact.ActualMixedMaps

/-! C19: the actual common owner quotient for K and H. The elementary
represented product of commuting equivalences is their ambient join;
RAW exact convolution supplies a full exact presentation of that join. -/

universe v w t
namespace CCO.FiniteLift
open RawExact
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K H : ExactKernel S G)

include HS

theorem kernel_permutes : ExactCRT.Abstract.Permutes K.rel H.rel :=
  S.same_sort_commute_of_homogeneous HS (i := ()) K.rel.r H.rel.r K.invariant H.invariant

theorem join_relation : (K.rel ⊔ H.rel).r = RawSymmetric.compose K.rel.r H.rel.r :=
  ExactCRT.Abstract.join_eq_comp K.rel H.rel (kernel_permutes S HS K H)

def ExactKernel.join : ExactKernel S G where
  rel := K.rel ⊔ H.rel
  exact := ⟨pairWords S K.exact.words H.exact.words,
    pairWords_nonempty_of_homogeneous S HS K.exact H.exact⟩
  represents := by
    change evaluate S (pairWords S K.exact.words H.exact.words) = (K.rel ⊔ H.rel).r
    rw [← convolution_of_CCO S HS cco K.exact H.exact,K.represents,H.represents]
    exact (join_relation S HS K H).symm
  invariant := by
    intro g x y h
    rw [join_relation S HS K H] at h ⊢
    obtain ⟨z,hxz,hzy⟩ := h
    exact ⟨g • z,K.invariant g x z hxz,H.invariant g z y hzy⟩

def ExactKernel.toJoinK : K.Q → (ExactKernel.join S HS cco K H).Q :=
  ExactCRT.Abstract.quotientMap (show K.rel ≤ K.rel ⊔ H.rel from le_sup_left)

def ExactKernel.toJoinH : H.Q → (ExactKernel.join S HS cco K H).Q :=
  ExactCRT.Abstract.quotientMap (show H.rel ≤ K.rel ⊔ H.rel from le_sup_right)

@[simp] theorem toJoinK_proj (a : A) :
    ExactKernel.toJoinK S HS cco K H (K.proj a) = (ExactKernel.join S HS cco K H).proj a := rfl

@[simp] theorem toJoinH_proj (a : A) :
    ExactKernel.toJoinH S HS cco K H (H.proj a) = (ExactKernel.join S HS cco K H).proj a := rfl

theorem toJoinK_onto : Function.Surjective (ExactKernel.toJoinK S HS cco K H) :=
  ExactCRT.Abstract.quotientMap_surjective _

theorem toJoinH_onto : Function.Surjective (ExactKernel.toJoinH S HS cco K H) :=
  ExactCRT.Abstract.quotientMap_surjective _

@[simp] theorem toJoinK_smul (g : G) (q : K.Q) :
    ExactKernel.toJoinK S HS cco K H (g • q) = g • ExactKernel.toJoinK S HS cco K H q := by
  induction q using Quotient.inductionOn with
  | _ a => rfl

@[simp] theorem toJoinH_smul (g : G) (q : H.Q) :
    ExactKernel.toJoinH S HS cco K H (g • q) = g • ExactKernel.toJoinH S HS cco K H q := by
  induction q using Quotient.inductionOn with
  | _ a => rfl

/-- Every K-class meets EVERY H-class with the same common owner.
This is literal incidence, rather than an assertion about a selected
subfamily or arbitrary finite tuples. -/
theorem class_incidence (q : K.Q) (b : H.Q)
    (h : ExactKernel.toJoinK S HS cco K H q = ExactKernel.toJoinH S HS cco K H b) :
    ∃ a : A, K.proj a = q ∧ H.proj a = b := by
  obtain ⟨x,rfl⟩ := K.onto q
  obtain ⟨y,rfl⟩ := H.onto b
  have hj : (K.rel ⊔ H.rel) x y := Quotient.exact h
  rw [join_relation S HS K H] at hj
  obtain ⟨a,hxa,hay⟩ := hj
  exact ⟨a,(K.proj_eq a x).mpr (K.rel.symm hxa),(H.proj_eq a y).mpr hay⟩

end CCO.FiniteLift
