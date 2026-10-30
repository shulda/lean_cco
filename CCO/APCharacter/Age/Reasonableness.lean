import CCO.APCharacter.Age.Limit

/-! Finite phase seeds lift the SAME prescribed old embedding. The target
bits are constructed from one global source marking; the source need not
be closed under any newly added function because all added symbols are unary. -/
universe u v w
namespace CCO.APCharacter.Age
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
noncomputable section
variable (M : MaskData S)

theorem finite_seed_small (seeds : M.FiniteSeedExtension)
    {V : Type} [Finite V] (point : V → Sigma X) (bits : V → Bit)
    (legal : Legal S M point bits) :
    ∃ mark, M.GlobalMarking mark ∧ ∀ x, mark (point x) = bits x := by
  let V' := ULift.{max u v} V
  obtain ⟨mark,hm,he⟩ := seeds (fun x : V' => (point x.down).1)
    (fun x : V' => (point x.down).2) (fun x : V' => bits x.down)
    (fun x => legal.1 x.down) (fun x y => legal.2 x.down y.down)
  exact ⟨mark,hm,fun x => he ⟨x⟩⟩

/-- Literal old colour equality transfers local phase tests; it does not
assume that the old source embeddings preserve a prechosen global marking. -/
theorem legal_of_names {A : Type} {p q : A → Sigma X} {bits : A → Bit}
    (hp : Legal S M p bits)
    (h : ∀ x y, taggedColour S (q x) (q y) = taggedColour S (p x) (p y)) :
    Legal S M q bits := by
  constructor
  · intro x
    exact Eq.mpr (congrArg (fun i => M.validBit i (bits x))
      (congrArg (fun z : Colour S => z.1) (h x x))) (hp.1 x)
  · intro x y
    exact Eq.mpr (congrArg (fun z : Colour S => M.allowed z.2.2 (bits x) (bits y))
      (h x y)) (hp.2 x y)

/-- Every given old finite embedding lifts with its exact source bits.
The newly assigned target bits need not agree with any unrelated seed choice. -/
theorem reasonable (seeds : M.FiniteSeedExtension) {A B : Type} [Finite A]
    (p : A → Sigma X) (q : B → Sigma X) (f : A ↪ B) (bits : A → Bit)
    (legal : Legal S M p bits)
    (oldEmbedding : ∀ x y, taggedColour S (q (f x)) (q (f y)) =
      taggedColour S (p x) (p y)) :
    ∃ targetBits : B → Bit, Legal S M q targetBits ∧
      (∀ x, targetBits (f x) = bits x) ∧
      ∃ mark, M.GlobalMarking mark ∧ ∀ x, targetBits x = mark (q x) := by
  have hlegal := legal_of_names S M legal oldEmbedding
  obtain ⟨mark,hm,he⟩ := finite_seed_small S M seeds (q ∘ f) bits hlegal
  exact ⟨fun x => mark (q x),⟨fun x => hm.1 _,fun x y => hm.2 _ _⟩,
    he,mark,hm,fun _ => rfl⟩

/-- There are finitely many expansions of any fixed finite actual old
object, independently of how its locally legal bits were globally realized. -/
instance precompact {V : Type*} [Finite V] (point : V → Sigma X) :
    Finite {bits : V → Bit // Legal S M point bits} := inferInstance

/-- Reduct surjectivity is obtained by choosing an actual global marking,
including when the old diagram is empty. -/
theorem reduct_surjective (seeds : M.FiniteSeedExtension)
    {V : Type*} (point : V → Sigma X) : ∃ bits, Legal S M point bits := by
  let empty : Fin 0 → Sigma X := Fin.elim0
  obtain ⟨mark,hm,_⟩ := finite_seed_small S M seeds empty Fin.elim0
    ⟨fun x => Fin.elim0 x,fun x => Fin.elim0 x⟩
  exact ⟨fun x => mark (point x),⟨fun x => hm.1 _,fun x y => hm.2 _ _⟩⟩

end
end CCO.APCharacter.Age
