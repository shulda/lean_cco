import CCO.Selectors.GateImage
import CCO.Selectors.Contraction

universe u v w z t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Ordered endpoints only, with no identification of their palettes. -/
def Parallel (D E : TaggedMenu S) : Prop := D.1 = E.1 ∧ D.2.1 = E.2.1

def names {N : Type t} (label : ∀ {i j}, S.Atom i j → N)
    (D : TaggedMenu S) : Set N := {n | ∃ a ∈ D.2.2, label a = n}

def IsProduct (P Q R : TaggedMenu S) : Prop :=
  ∃ (i j k : ι) (A : S.Menu i j) (B : S.Menu j k),
    P = ⟨i,j,A⟩ ∧ Q = ⟨j,k,B⟩ ∧ R = ⟨i,k,S.product A B⟩

/-- A pure TAG action preserves literal fine-colour names. It is not an
arbitrary permutation of colours. Exactness and original multiplication
transport are precisely the source's displayed pure-action hypotheses. -/
structure PureTagAction (Λ : Type z) [Group Λ] (N : Type t) where
  tag : Λ → ι ≃ ι
  act : Λ → TaggedMenu S ≃ TaggedMenu S
  one : ∀ D, act 1 D = D
  mul : ∀ g h D, act (g*h) D = act g (act h D)
  source : ∀ g D, (act g D).1 = tag g D.1
  target : ∀ g D, (act g D).2.1 = tag g D.2.1
  label : ∀ {i j}, S.Atom i j → N
  label_injective : ∀ i j, Function.Injective (@label i j)
  literal : ∀ g D, names S label (act g D) = names S label D
  exact : ∀ g D, IsExact S (act g D) ↔ IsExact S D
  opposite : ∀ g D, act g (flip S D) = flip S (act g D)
  product : ∀ g {P Q R}, IsProduct S P Q R → IsProduct S (act g P) (act g Q) (act g R)

namespace PureTagAction
variable {S} {Λ : Type z} [Group Λ] {N : Type t} (A : PureTagAction S Λ N)

@[simp] theorem inv_act (g : Λ) (D : TaggedMenu S) : A.act g⁻¹ (A.act g D) = D := by
  rw [← A.mul, inv_mul_cancel, A.one]
@[simp] theorem act_inv (g : Λ) (D : TaggedMenu S) : A.act g (A.act g⁻¹ D) = D := by
  rw [← A.mul, mul_inv_cancel, A.one]

theorem parallel (g : Λ) (D E : TaggedMenu S) :
    Parallel S (A.act g D) (A.act g E) ↔ Parallel S D E := by
  simp only [Parallel,A.source,A.target,Equiv.apply_eq_iff_eq]

theorem names_injective {i j} {D E : S.Menu i j}
    (h : names S A.label ⟨i,j,D⟩ = names S A.label ⟨i,j,E⟩) : D = E := by
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨b,hb,hba⟩ := (h ▸ (show A.label a ∈ names S A.label ⟨i,j,D⟩ from ⟨a,ha,rfl⟩))
    exact (A.label_injective i j hba) ▸ hb
  · intro a ha
    obtain ⟨b,hb,hba⟩ := (h.symm ▸ (show A.label a ∈ names S A.label ⟨i,j,E⟩ from ⟨a,ha,rfl⟩))
    exact (A.label_injective i j hba) ▸ hb

theorem tagged_names_injective {D E : TaggedMenu S} (hP : Parallel S D E)
    (hN : names S A.label D = names S A.label E) : D = E := by
  rcases D with ⟨i,j,D⟩
  rcases E with ⟨i',j',E⟩
  rcases hP with ⟨hi,hj⟩
  cases hi; cases hj
  congr 2
  exact A.names_injective hN

/-- Name-level intersection agrees with the actual intersection on a hom-palette. -/
theorem names_inter {i j} (D E : S.Menu i j) :
    names S A.label ⟨i,j,D ∩ E⟩ = names S A.label ⟨i,j,D⟩ ∩ names S A.label ⟨i,j,E⟩ := by
  ext n
  constructor
  · rintro ⟨a,⟨haD,haE⟩,han⟩
    exact ⟨⟨a,haD,han⟩,⟨a,haE,han⟩⟩
  · rintro ⟨⟨a,ha,han⟩,⟨b,hb,hbn⟩⟩
    have hab : a = b := A.label_injective i j (han.trans hbn.symm)
    subst b
    exact ⟨a,⟨ha,hb⟩,han⟩

def Invariant (J : Family S) : Prop := ∀ g D, D ∈ J → A.act g D ∈ J

/-- All extra symmetry requested of a contraction is explicit and composes. -/
def Covariant {J K : Family S} (R : Contraction S J K) : Prop :=
  ∀ g D, D ∈ J →
    A.act g ⟨D.1,D.2.1,R.toFun D.2.2⟩ =
      ⟨(A.act g D).1,(A.act g D).2.1,R.toFun (A.act g D).2.2⟩

end PureTagAction
end CCO.Selectors
