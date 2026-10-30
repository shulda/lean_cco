import CCO.APCharacter.Age.Span

/-! Old homogeneity aligns an AP span's original realizations on their
complete common base. Marks are kept on the formal legs; no additional
coincidences of the old realizations are imposed on marked vertices. -/
universe u v w t
namespace CCO.APCharacter.Age
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
include H

/-- Higher-universe finite tuples contain the small finite charts by ULift. -/
theorem align_finite {V : Type} [Finite V] (p q : V → Sigma X)
    (h : ∀ x y, taggedColour S (p x) (p y) = taggedColour S (q x) (q y)) :
    ∃ g : G, ∀ x, g • p x = q x := by
  let V' := ULift.{max u v} V
  obtain ⟨g,hg⟩ := H.extends_finite_diagram
    (fun x : V' => p x.down) (fun x : V' => q x.down)
    (fun x y => h x.down y.down)
  exact ⟨g,fun x => hg ⟨x⟩⟩

theorem legal_translate {V : Type} {M : MaskData S} {p : V → Sigma X}
    {bits : V → Bit} (hp : Legal S M p bits) (g : G) :
    Legal S M (fun x => g • p x) bits := by
  constructor
  · intro x
    simpa only [H.preserves_sort] using hp.1 x
  · intro x y
    have h := H.preserves_colours g (p x) (p y)
    exact Eq.mpr (congrArg (fun z : Colour S => M.allowed z.2.2 (bits x) (bits y)) h)
      (hp.2 x y)

/-- Actual old point alignment; the finite source may be empty or singleton. -/
theorem align_span {M : MaskData S} (A B C : Chart S M)
    (f : @FirstOrder.Language.Embedding (Language S) (Fin A.size) (Fin B.size) A.structure B.structure)
    (g : @FirstOrder.Language.Embedding (Language S) (Fin A.size) (Fin C.size) A.structure C.structure) :
    ∃ h : G, ∀ x, h • C.point (g x) = B.point (f x) := by
  apply align_finite S H (fun x => C.point (g x)) (fun x => B.point (f x))
  intro x y
  exact ((A.embedding_names C g).2 x y).trans ((A.embedding_names B f).2 x y).symm

end
end CCO.APCharacter.Age
