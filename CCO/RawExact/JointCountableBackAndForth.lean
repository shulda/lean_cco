import CCO.RawExact.JointOrbitalGraph
import Mathlib.Order.Ideal
import Mathlib.Logic.Encodable.Basic

/-!
# Countable back-and-forth in the actual joint orbital language

The output is a family of genuine bijections preserving the complete
pair orbitals. It is not asserted to lie in an arbitrary named group G.
-/

universe z q t

namespace CCO.RawExact.JointBackAndForth

open Order

variable {G : Type t} [Group G] {K : Type z} {Q : K → Type q}
variable [∀ k, MulAction G (Q k)]

/-- A separately proved finite extension property. The source theorem
below supplies it using actual exact kernels and C13. -/
def ExtensionProperty : Prop :=
  ∀ (f : Graph G Q) (a : Sigma Q),
    ∃ (g : Graph G Q) (b : Q a.1),
      (⟨a.1, a.2, b⟩ : Row Q) ∈ g.val ∧ f ≤ g

noncomputable def definedAtLeft (ext : ExtensionProperty (G := G) (Q := Q))
    (a : Sigma Q) : Cofinal (Graph G Q) where
  carrier := {f | ∃ b : Q a.1, (⟨a.1, a.2, b⟩ : Row Q) ∈ f.val}
  isCofinal f := by
    obtain ⟨g, b, hb, hfg⟩ := ext f a
    exact ⟨g, ⟨b, hb⟩, hfg⟩

noncomputable def definedAtRight (ext : ExtensionProperty (G := G) (Q := Q))
    (a : Sigma Q) : Cofinal (Graph G Q) where
  carrier := {f | ∃ b : Q a.1, (⟨a.1, b, a.2⟩ : Row Q) ∈ f.val}
  isCofinal f := by
    obtain ⟨g, b, hb, hfg⟩ := ext f.comm a
    refine ⟨g.comm, ⟨b, ?_⟩, ?_⟩
    · exact (Graph.mem_comm _ _).mpr hb
    · simpa only [Graph.comm_comm] using Graph.comm_mono hfg

/-- The countable actual joint orbital structure is homogeneous once
the proved finite extension property is available in both directions.
The family e consists of actual sortwise bijections, with no claim
that its back-and-forth limit belongs to the witness group G. -/
theorem countable_joint_orbital_automorphism
    [Countable (Sigma Q)]
    (ext : ExtensionProperty (G := G) (Q := Q)) (start : Graph G Q) :
    ∃ e : ∀ k, Q k ≃ Q k,
      (∀ (k l : K) (a : Q k) (b : Q l),
        GroupActions.orbital (G := G) a b (e k a) (e l b)) ∧
      (∀ p ∈ start.val, e p.1 p.2.1 = p.2.2) := by
  classical
  let : Encodable (Sigma Q) := Encodable.ofCountable _
  let D : Sigma Q ⊕ Sigma Q → Cofinal (Graph G Q) :=
    Sum.elim (definedAtLeft ext) (definedAtRight ext)
  let J : Ideal (Graph G Q) := idealOfCofinals start D
  have hLeft : ∀ a : Sigma Q, ∃ b : Q a.1,
      ∃ f : Graph G Q, f ∈ J ∧
        (⟨a.1, a.2, b⟩ : Row Q) ∈ f.val := by
    intro a
    obtain ⟨f, hf, hJ⟩ := cofinal_meets_idealOfCofinals start D (Sum.inl a)
    obtain ⟨b, hb⟩ := hf
    exact ⟨b, f, hJ, hb⟩
  have hRight : ∀ a : Sigma Q, ∃ b : Q a.1,
      ∃ f : Graph G Q, f ∈ J ∧
        (⟨a.1, b, a.2⟩ : Row Q) ∈ f.val := by
    intro a
    obtain ⟨f, hf, hJ⟩ := cofinal_meets_idealOfCofinals start D (Sum.inr a)
    obtain ⟨b, hb⟩ := hf
    exact ⟨b, f, hJ, hb⟩
  let F : ∀ a : Sigma Q, Q a.1 := fun a => (hLeft a).choose
  let B : ∀ a : Sigma Q, Q a.1 := fun a => (hRight a).choose
  have hF : ∀ a : Sigma Q, ∃ f : Graph G Q, f ∈ J ∧
      (⟨a.1, a.2, F a⟩ : Row Q) ∈ f.val :=
    fun a => (hLeft a).choose_spec
  have hB : ∀ a : Sigma Q, ∃ f : Graph G Q, f ∈ J ∧
      (⟨a.1, B a, a.2⟩ : Row Q) ∈ f.val :=
    fun a => (hRight a).choose_spec
  have hLeftInv : ∀ (k : K) (a : Q k), B ⟨k, F ⟨k, a⟩⟩ = a := by
    intro k a
    obtain ⟨f, hf, hfa⟩ := hF ⟨k, a⟩
    obtain ⟨g, hg, hga⟩ := hB ⟨k, F ⟨k, a⟩⟩
    obtain ⟨m, hm, hfm, hgm⟩ := J.directed f hf g hg
    exact (m.injective k a (B ⟨k, F ⟨k, a⟩⟩)
      (F ⟨k, a⟩) (hfm hfa) (hgm hga)).symm
  have hRightInv : ∀ (k : K) (b : Q k), F ⟨k, B ⟨k, b⟩⟩ = b := by
    intro k b
    obtain ⟨f, hf, hfb⟩ := hF ⟨k, B ⟨k, b⟩⟩
    obtain ⟨g, hg, hgb⟩ := hB ⟨k, b⟩
    obtain ⟨m, hm, hfm, hgm⟩ := J.directed f hf g hg
    exact m.functional k (B ⟨k, b⟩)
      (F ⟨k, B ⟨k, b⟩⟩) b (hfm hfb) (hgm hgb)
  let e : ∀ k, Q k ≃ Q k := fun k =>
    ⟨fun a => F ⟨k, a⟩, fun b => B ⟨k, b⟩,
      hLeftInv k, hRightInv k⟩
  refine ⟨e, ?_, ?_⟩
  · intro k l a b
    obtain ⟨f, hf, hfa⟩ := hF ⟨k, a⟩
    obtain ⟨g, hg, hgb⟩ := hF ⟨l, b⟩
    obtain ⟨m, hm, hfm, hgm⟩ := J.directed f hf g hg
    exact m.property _ (hfm hfa) _ (hgm hgb)
  · intro p hp
    obtain ⟨f, hf, hfp⟩ := hF ⟨p.1, p.2.1⟩
    have hStart : start ∈ J := mem_idealOfCofinals start D
    obtain ⟨m, hm, hsm, hfm⟩ := J.directed start hStart f hf
    exact (m.functional p.1 p.2.1 p.2.2
      (F ⟨p.1, p.2.1⟩) (hsm hp) (hfm hfp)).symm

end CCO.RawExact.JointBackAndForth
