import CCO.FullPhaseLift.Marked.Signature
import CCO.APCharacter.Age.Reasonableness
import CCO.APCharacter.Towers.UnaryComposition

/-! The legal full marked class is defined by the old FULL age and the
actual pair mask. An object retains every old positive and negative tuple,
not just its binary shadow. -/
universe u v w m
namespace CCO.FullPhaseLift.Marked
open Canonical APCharacter CategoryTheory
noncomputable section
variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S)

/-- Correctness of complete canonical names: two FULL realizations of
one table have the same named pairs. The canonical source proves this. -/
def PairFaithful : Prop :=
  ∀ {V : Type} {A : BoolTable L V} (p q : Canonical.Embedding A U) (x y : V),
    taggedColour S (pack (q.point x)) (pack (q.point y)) =
      taggedColour S (pack (p.point x)) (pack (p.point y))

structure OldChart where
  size : ℕ
  full : BoolTable L (Fin size)
  realized : Nonempty (Canonical.Embedding full U)

structure Chart where
  old : OldChart U
  bits : Fin old.size → Bit
  legal : ∃ p : Canonical.Embedding old.full U,
    Age.Legal S mask (pack ∘ p.point) bits

instance oldCountable : Countable (OldChart U) := by
  apply Function.Injective.countable (f := fun C : OldChart U => (⟨C.size,C.full⟩ : Σ n, BoolTable L (Fin n)))
  rintro ⟨n,T,ht⟩ ⟨m,V,hv⟩ h
  cases h
  rfl

instance chartCountable : Countable (Chart U S pack mask) := by
  apply Function.Injective.countable
    (f := fun C : Chart U S pack mask => (⟨C.old,C.bits⟩ : Σ C : OldChart U, Fin C.size → Bit))
  rintro ⟨A,a,ha⟩ ⟨B,b,hb⟩ h
  cases h
  rfl

instance oldCategory : SmallCategory (OldChart U) where
  Hom A B := Canonical.Embedding A.full B.full
  id A := RelationalCompletion.Relational.Structure.Embedding.identity _
  comp f g := g.comp f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

instance chartCategory : SmallCategory (Chart U S pack mask) where
  Hom A B := Canonical.Embedding (table A.old.full A.bits) (table B.old.full B.bits)
  id A := RelationalCompletion.Relational.Structure.Embedding.identity _
  comp f g := g.comp f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- The literal old FULL reduct functor uses the SAME point map. -/
def forget : Chart U S pack mask ⥤ OldChart U where
  obj A := A.old
  map f := oldEmbedding f
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Lift the exact given full embedding. Only the new target unary bits
are selected; ALL higher old tuple truths stay those of its given target. -/
theorem reasonable (names : PairFaithful U S pack) (seeds : mask.FiniteSeedExtension) :
    Towers.Reasonable (forget U S pack mask) := by
  intro A B f
  obtain ⟨p,hp⟩ := A.legal
  let q := B.realized.some
  have hn (x y : Fin A.old.size) :
      taggedColour S ((pack ∘ q.point) (f.point x)) ((pack ∘ q.point) (f.point y)) =
        taggedColour S ((pack ∘ p.point) x) ((pack ∘ p.point) y) :=
    names p (q.comp f) x y
  obtain ⟨b,hlegal,hb,_⟩ := Age.reasonable S mask seeds (pack ∘ p.point)
    (pack ∘ q.point) ⟨f.point,f.injective⟩ A.bits hp hn
  let B' : Chart U S pack mask := ⟨B,b,⟨q,hlegal⟩⟩
  refine ⟨B',embedding f hb,rfl,?_⟩
  exact heq_of_eq (oldEmbedding_embedding f hb)

/-- Every given old full age object has a legal unary expansion. -/
theorem reductSurjective (seeds : mask.FiniteSeedExtension) :
    Towers.ReductSurjective (forget U S pack mask) := by
  intro B
  let q := B.realized.some
  obtain ⟨b,hb⟩ := Age.reduct_surjective S mask seeds (pack ∘ q.point)
  exact ⟨⟨B,b,⟨q,hb⟩⟩,rfl⟩

/-- Finite normalized relation symbols and two possible unary bits give
finitely many marked full objects on each fixed finite carrier. -/
theorem finite_size (n : ℕ) : Finite {C : Chart U S pack mask // C.old.size = n} := by
  let target := Σ i : {k : ℕ // k = n}, BoolTable L (Fin i.val) × (Fin i.val → Bit)
  let code : {C : Chart U S pack mask // C.old.size = n} → target :=
    fun C => ⟨⟨C.val.old.size,C.property⟩,C.val.old.full,C.val.bits⟩
  apply Finite.of_injective code
  rintro ⟨⟨⟨n,T,ht⟩,b,hb⟩,hn⟩ ⟨⟨⟨m,V,hv⟩,c,hc⟩,hm⟩ h
  cases h
  rfl

/-- Expansion fibres are finite on the SAME old object/carrier. -/
theorem precompact : Towers.Precompact (forget U S pack mask) := by
  intro B
  letI := finite_size U S pack mask B.size
  let code : {A : Chart U S pack mask // (forget U S pack mask).obj A = B} →
      {A : Chart U S pack mask // A.old.size = B.size} :=
    fun A => ⟨A.val,congrArg OldChart.size A.property⟩
  apply Finite.of_injective code
  intro A C h
  exact Subtype.ext (congrArg (fun A : {A : Chart U S pack mask // A.old.size = B.size} => A.val) h)

/-- The actual full finite-age unary transition; all three properties
belong to the literal full-relation forgetful functor above. -/
def transition (names : PairFaithful U S pack) (seeds : mask.FiniteSeedExtension) :
    Towers.UnaryTransition ⟨OldChart U,oldCategory U⟩
      ⟨Chart U S pack mask,chartCategory U S pack mask⟩ where
  forget := forget U S pack mask
  reasonable := reasonable U S pack mask names seeds
  reductSurjective := reductSurjective U S pack mask seeds
  precompact := precompact U S pack mask

end
end CCO.FullPhaseLift.Marked
