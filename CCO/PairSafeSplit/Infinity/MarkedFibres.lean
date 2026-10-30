import CCO.PairSafeSplit.Infinity.TypeFibres

/-! C28: any one actual class-constant marking retains infinitely many
points of the old complete one-point type. No homogeneity of the marking
is assumed. -/

universe u v w t z
namespace CCO.PairSafeSplit.Infinity
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

def markedTypeFibre (B : FiniteInduced (X := X)) {i : ι} {Label : Type z}
    (mark : X i → Label) (x : X i) : Set (X i) :=
  typeFibre S B x ∩ {y | mark y = mark x}

/-- On an active sort, old type/gate infinitude applies inside ANY fixed
global marking which is constant on the actual gate classes. -/
theorem markedTypeFibre_infinite (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (E : ColourEq S i) (hE : ⊥ < E)
    (B : FiniteInduced (X := X)) {Label : Type z} (mark : X i → Label)
    (hmark : ∀ a b, E a b → mark a = mark b) (x : X i)
    (hx : (⟨i,x⟩ : Sigma X) ∉ B.vertices) :
    (markedTypeFibre S B mark x).Infinite := by
  apply (type_class_infinite S H sap E hE B x hx).mono
  intro y hy
  exact ⟨hy.1,(hmark x y hy.2).symm⟩

/-- Inactive sorts use their one constant label and the old SAP orbit. -/
theorem constant_markedTypeFibre_infinite (H : HomogeneousSource S G) (sap : AgeSAP S)
    (B : FiniteInduced (X := X)) {i : ι} {Label : Type z}
    (mark : X i → Label) (x : X i) (hmark : ∀ y, mark y = mark x)
    (hx : (⟨i,x⟩ : Sigma X) ∉ B.vertices) :
    (markedTypeFibre S B mark x).Infinite := by
  exact (typeFibre_infinite S H sap B x hx).mono (fun y hy => ⟨hy,hmark y⟩)

/-- Arbitrarily many DISTINCT real same-type, same-mark witnesses. Their
finite union with the original base is an actual finite induced old object. -/
theorem exists_marked_witnesses (B : FiniteInduced (X := X)) {i : ι}
    {Label : Type z} (mark : X i → Label) (x : X i)
    (hinf : (markedTypeFibre S B mark x).Infinite) (n : ℕ) :
    ∃ f : Fin n ↪ X i, ∀ k, f k ∈ markedTypeFibre S B mark x := by
  let U := markedTypeFibre S B mark x
  let e : ℕ ↪ U := hinf.natEmbedding U
  let f : Fin n ↪ X i := (Fin.valEmbedding.trans e).trans (Function.Embedding.subtype U)
  exact ⟨f,fun k => (e k.val).property⟩

end CCO.PairSafeSplit.Infinity
