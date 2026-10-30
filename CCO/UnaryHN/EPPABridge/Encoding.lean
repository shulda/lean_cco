import PartiteConstruction.Structure.Basic
import AllThoseEPPA.MainTheorems

/-! Same-carrier positive-language encoding. Nullary relations are retained
in a fixed actual profile, including structures with empty carriers. -/

universe u v w
namespace CCO.UnaryHN.Native.EPPABridge

open StructuralRamsey

abbrev NullaryProfile (L : Language.{u}) :=
  (R : L.RelSymbol) → L.relArity R = 0 → Prop

def HasProfile {L : Language.{u}} {V : Type v}
    (A : Structure L V) (P : NullaryProfile L) : Prop :=
  ∀ R (h : L.relArity R = 0) (xs : Fin (L.relArity R) → V),
    A.rel R xs ↔ P R h

abbrev positiveLanguage (L : Language.{u}) : AllThoseEPPA.Language.{u} where
  RelSymbol n := {R : L.RelSymbol // L.relArity R = n ∧ 0 < n}
  FuncSymbol n := {F : L.FuncSymbol // L.funcArity F = n}
  relArity_pos R := R.2.2

def trivialAction (L : Language.{u}) :
    (positiveLanguage L).Action PUnit.{1} :=
  AllThoseEPPA.Language.Action.trivial _ _

@[simp] theorem trivial_onRel {L : Language.{u}} {n : ℕ}
    (g : PUnit.{1}) (R : (positiveLanguage L).RelSymbol n) :
    (trivialAction L).onRel g R = R := rfl

@[simp] theorem trivial_onFunc {L : Language.{u}} {n : ℕ}
    (g : PUnit.{1}) (F : (positiveLanguage L).FuncSymbol n) :
    (trivialAction L).onFunc g F = F := rfl

def encode {L : Language.{u}} {V : Type v} (A : Structure L V) :
    AllThoseEPPA.Structure (positiveLanguage L) V where
  rel R xs := A.rel R.1 (fun i => xs (Fin.cast R.2.1 i))
  func F xs := A.func F.1 (fun i => xs (Fin.cast F.2 i))

def decode {L : Language.{u}} {V : Type v}
    (P : NullaryProfile L) (A : AllThoseEPPA.Structure (positiveLanguage L) V) :
    Structure L V where
  rel R xs := if h : 0 < L.relArity R then A.rel ⟨R, rfl, h⟩ xs
    else P R (Nat.eq_zero_of_not_pos h)
  func F xs := A.func ⟨F, rfl⟩ xs

theorem decode_hasProfile {L : Language.{u}} {V : Type v}
    (P : NullaryProfile L) (A : AllThoseEPPA.Structure (positiveLanguage L) V) :
    HasProfile (decode P A) P := by
  intro R h xs
  simp [decode, h]

theorem native_ext {L : Language.{u}} {V : Type v} {A B : Structure L V}
    (hr : ∀ R xs, A.rel R xs ↔ B.rel R xs)
    (hf : ∀ F xs, A.func F xs = B.func F xs) : A = B := by
  cases A with | mk ar af =>
    cases B with | mk br bf =>
      have er : ar = br := funext fun R => funext fun xs => propext (hr R xs)
      have ef : af = bf := funext fun F => funext fun xs => hf F xs
      cases er
      cases ef
      rfl

theorem eppa_ext {L : AllThoseEPPA.Language.{u}} {V : Type v}
    {A B : AllThoseEPPA.Structure L V}
    (hr : ∀ n (R : L.RelSymbol n) xs, A.rel R xs ↔ B.rel R xs)
    (hf : ∀ n (F : L.FuncSymbol n) xs, A.func F xs = B.func F xs) : A = B := by
  cases A with | mk ar af =>
    cases B with | mk br bf =>
      have er : @ar = @br := by funext n R xs; exact propext (hr n R xs)
      have ef : @af = @bf := by funext n F xs; exact hf n F xs
      cases er
      cases ef
      rfl

@[simp] theorem encode_decode {L : Language.{u}} {V : Type v}
    (P : NullaryProfile L) (A : AllThoseEPPA.Structure (positiveLanguage L) V) :
    encode (decode P A) = A := by
  apply eppa_ext
  · intro n ⟨R, hR, hp⟩ xs
    subst n
    simp [encode, decode, hp]
  · intro n ⟨F, hF⟩ xs
    subst n
    rfl

theorem decode_encode {L : Language.{u}} {V : Type v}
    {A : Structure L V} {P : NullaryProfile L} (hP : HasProfile A P) :
    decode P (encode A) = A := by
  apply native_ext
  · intro R xs
    by_cases hp : 0 < L.relArity R
    · simp [decode, encode, hp]
    · simp only [decode, dite_eq_right hp]
      exact (hP R (Nat.eq_zero_of_not_pos hp) xs).symm
  · intro F xs
    rfl

theorem unaryInstance {L : Language.{u}} (hUnary : ∀ F, L.funcArity F = 1) :
    (positiveLanguage L).HasUnaryFunctions where
  arity_eq_one F := F.2.symm.trans (hUnary F.1)

def encodeEmbedding {L : Language.{u}} {V W : Type v}
    {A : Structure L V} {B : Structure L W} (e : Structure.Embedding A B) :
    AllThoseEPPA.Structure.Embedding (trivialAction L) (encode A) (encode B) where
  lang := PUnit.unit
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro n ⟨R, hR, hp⟩ xs
    subst n
    exact e.map_rel_iff R xs
  map_func := by
    intro n ⟨F, hF⟩ xs
    subst n
    exact e.map_func F xs

def decodeEmbedding {L : Language.{u}} {V W : Type v}
    (P : NullaryProfile L)
    {A : AllThoseEPPA.Structure (positiveLanguage L) V}
    {B : AllThoseEPPA.Structure (positiveLanguage L) W}
    (e : AllThoseEPPA.Structure.Embedding (trivialAction L) A B) :
    Structure.Embedding (decode P A) (decode P B) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    by_cases hp : 0 < L.relArity R
    · simp only [decode, dite_eq_left hp]
      convert e.map_rel_iff ⟨R, rfl, hp⟩ xs using 1
      rw [trivial_onRel (L := L)]
    · simp [decode, hp]
  map_func := by
    intro F xs
    exact e.map_func ⟨F, rfl⟩ xs

theorem embedding_profile {L : Language.{u}} {V W : Type v}
    {A : Structure L V} {B : Structure L W} (e : Structure.Embedding A B)
    {P : NullaryProfile L} (hP : HasProfile A P) : HasProfile B P := by
  intro R h xs
  let ys : Fin (L.relArity R) → V := fun i => False.elim (by have := i.2; omega)
  have he : e ∘ ys = xs := by funext i; have := i.2; omega
  rw [← he]
  exact (e.map_rel_iff R ys).trans (hP R h ys)

theorem encode_closed_iff {L : Language.{u}} {V : Type v}
    (A : Structure L V) (S : Set V) : (encode A).IsClosed S ↔ A.IsClosed S := by
  constructor
  · intro h F xs hxs
    exact h ⟨F, rfl⟩ xs hxs
  · intro h n ⟨F, hF⟩ xs hxs
    subst n
    exact h F xs hxs

@[simp] theorem encode_induce {L : Language.{u}} {V : Type v}
    (A : Structure L V) (S : Set V) (hS : A.IsClosed S) :
    encode (A.induce S hS) =
      (encode A).induce S ((encode_closed_iff A S).mpr hS) := rfl

end CCO.UnaryHN.Native.EPPABridge
