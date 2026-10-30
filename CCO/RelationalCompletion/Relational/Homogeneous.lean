import CCO.RelationalCompletion.Relational.Language

universe u v
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {W : Type v}

/-- Actual finite-age membership is embeddability, never an external membership
callback. Finiteness of each source is supplied where the age is used. -/
def Age (U : Structure L W) {V : Type v} (B : Structure L V) : Prop :=
  Nonempty (Embedding B U)

/-- The usual finite induced homogeneity, written using two embeddings of the
SAME finite structure. The resulting automorphism aligns the maps pointwise. -/
def Homogeneous (U : Structure L W) : Prop :=
  ∀ (V : Type v) [Finite V] (B : Structure L V) (f g : Embedding B U),
    ∃ a : Iso U U, ∀ x, a.point (f.point x) = g.point x

/-- Ordinary age AP: the two full induced factors may meet outside the root. -/
def AgeAP (U : Structure L W) : Prop :=
  ∀ (V₀ V₁ V₂ : Type v) [Finite V₀] [Finite V₁] [Finite V₂]
    (A : Structure L V₀) (B : Structure L V₁) (C : Structure L V₂),
    U.Age A → U.Age B → U.Age C →
    ∀ (s : Embedding A B) (t : Embedding A C),
    ∃ (X : Type v) (_ : Finite X) (D : Structure L X), U.Age D ∧
      ∃ (l : Embedding B D) (r : Embedding C D),
        ∀ x, l.point (s.point x) = r.point (t.point x)

/-- Actual strong age amalgamation over an arbitrary finite induced span.
The final clause rules out ALL off-base identifications. -/
def AgeSAP (U : Structure L W) : Prop :=
  ∀ (V₀ V₁ V₂ : Type v) [Finite V₀] [Finite V₁] [Finite V₂]
    (A : Structure L V₀) (B : Structure L V₁) (C : Structure L V₂),
    U.Age A → U.Age B → U.Age C →
    ∀ (s : Embedding A B) (t : Embedding A C),
    ∃ (X : Type v) (_ : Finite X) (D : Structure L X), U.Age D ∧
      ∃ (l : Embedding B D) (r : Embedding C D),
        (∀ x, l.point (s.point x) = r.point (t.point x)) ∧
        ∀ x y, l.point x = r.point y → ∃ a, s.point a = x ∧ t.point a = y

theorem AgeSAP.ap {U : Structure L W} (hs : U.AgeSAP) : U.AgeAP := by
  intro V₀ V₁ V₂ _ _ _ A B C ha hb hc s t
  obtain ⟨X, hX, D, hD, l, r, heq, _⟩ := hs V₀ V₁ V₂ A B C ha hb hc s t
  exact ⟨X, hX, D, hD, l, r, heq⟩

/-- C04/C05: full images and their arbitrary deletions really are age objects;
all relation and nullary data are induced literally from U. -/
theorem induced_mem_age (U : Structure L W) (S : Set W) : U.Age (U.induce S) :=
  ⟨U.inclusion S⟩

end CCO.RelationalCompletion.Relational.Structure
