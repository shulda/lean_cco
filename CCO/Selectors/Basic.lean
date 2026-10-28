import CCO.StrongExact.SourceExactCalculus
import CCO.StrongExact.PCExactness
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma

/-! Original typed exact families and their actual generation rules. -/
universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

abbrev TaggedMenu := Σ i : ι, Σ j : ι, S.Menu i j
abbrev Family := Set (TaggedMenu S)

def flip (D : TaggedMenu S) : TaggedMenu S :=
  ⟨D.2.1, D.1, S.opposite D.2.2⟩

def IsExact (D : TaggedMenu S) : Prop := StrongExact.Exact S D.2.2

noncomputable instance taggedMenuFintype : Fintype (TaggedMenu S) := by
  letI := S.finiteSort
  letI : ∀ i j, Fintype (S.Atom i j) := S.finiteAtom
  exact Fintype.ofFinite _

@[simp] theorem flip_flip (D : TaggedMenu S) : flip S (flip S D) = D := by
  rcases D with ⟨i,j,D⟩
  simp only [flip, S.opposite_opposite]

/-- Generation uses original exact multipliers, with no zero-length menu. -/
inductive Generated (seed : TaggedMenu S) : TaggedMenu S → Prop
  | seed : Generated seed seed
  | opposite {D} : Generated seed D → Generated seed (flip S D)
  | left {i j k} (P : S.Menu i j) (hP : StrongExact.Exact S P)
      {D : S.Menu j k} : Generated seed ⟨j,k,D⟩ →
        Generated seed ⟨i,k,S.product P D⟩
  | right {i j k} {D : S.Menu i j} (P : S.Menu j k)
      (hP : StrongExact.Exact S P) : Generated seed ⟨i,j,D⟩ →
        Generated seed ⟨i,k,S.product D P⟩

def FullNoReturn : Prop :=
  ∀ {i j} (A B : S.Menu i j), StrongExact.Exact S A → StrongExact.Exact S B →
    (∀ D, Generated S ⟨i,j,A⟩ D ↔ Generated S ⟨i,j,B⟩ D) → A = B

structure CurrentFamily (J : Family S) : Prop where
  exact : ∀ {D}, D ∈ J → IsExact S D
  singleton : ∀ {i j} (a : S.Atom i j), (⟨i,j,{a}⟩ : TaggedMenu S) ∈ J
  opposite : ∀ {D}, D ∈ J → flip S D ∈ J
  downward : ∀ {i j} {D E : S.Menu i j},
    (⟨i,j,D⟩ : TaggedMenu S) ∈ J → StrongExact.Exact S E → E ⊆ D → ⟨i,j,E⟩ ∈ J

structure FilterFamily (F : Family S) : Prop where
  exact : ∀ {D}, D ∈ F → IsExact S D
  opposite : ∀ {D}, D ∈ F → flip S D ∈ F
  left : ∀ {i j k} (P : S.Menu i j), StrongExact.Exact S P →
    ∀ {D : S.Menu j k}, (⟨j,k,D⟩ : TaggedMenu S) ∈ F → ⟨i,k,S.product P D⟩ ∈ F
  right : ∀ {i j k} (P : S.Menu j k), StrongExact.Exact S P →
    ∀ {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ F → ⟨i,k,S.product D P⟩ ∈ F

/-- Visibility is relative to CURRENT menus, and allows repeated endpoints/menus. -/
def Visible (F J : Family S) : Prop :=
  ∀ {i j} {D A B : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ J →
    (⟨i,j,A⟩ : TaggedMenu S) ∈ F → (⟨i,j,B⟩ : TaggedMenu S) ∈ F →
    (A ∩ D).Nonempty → (B ∩ D).Nonempty → (A ∩ B).Nonempty

/-- Data proved by the accepted homogeneous SAP+CCO source. -/
structure ExactCalculus : Prop where
  product : ∀ {i j k} {A : S.Menu i j} {B : S.Menu j k},
    StrongExact.Exact S A → StrongExact.Exact S B → StrongExact.Exact S (S.product A B)
  opposite : ∀ {i j} {A : S.Menu i j},
    StrongExact.Exact S A → StrongExact.Exact S (S.opposite A)
  helly : ∀ {i j} (menus : List (S.Menu i j)),
    (∀ A ∈ menus, StrongExact.Exact S A) →
    (∀ A ∈ menus, ∀ B ∈ menus, (A ∩ B).Nonempty) →
    (StrongExact.meetMenus S menus).Nonempty
  distrib : ∀ {i j k} {P : S.Menu i j} {A B : S.Menu j k},
    StrongExact.Exact S P → StrongExact.Exact S A → StrongExact.Exact S B →
    (A ∩ B).Nonempty → S.product P (A ∩ B) = S.product P A ∩ S.product P B

end CCO.Selectors
