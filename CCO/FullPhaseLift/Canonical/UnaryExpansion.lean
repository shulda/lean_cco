import CCO.FullPhaseLift.Canonical.Expansion
import CCO.FullPhaseLift.Marked.Signature

/-! Structural canonical naming after one genuine unary-bit expansion.
Every old tuple, including nullaries and repeated arguments, is retained.
No homogeneous prefix model or history callback is assumed. -/

universe v w
namespace CCO.FullPhaseLift.Canonical
open APCharacter

def oldProfile {L : Signature} {k : ℕ} (p : Profile (Marked.addBit L) k) : Profile L k :=
  fun a => p ⟨a.1.succ,a.2⟩

def profileBit {L : Signature} {k : ℕ} (p : Profile (Marked.addBit L) k) (i : Fin k) : Bit :=
  Marked.boolBit (p ⟨0,fun _ => i⟩)

@[simp] theorem oldProfile_marked {L : Signature} {V : Type v}
    (T : BoolTable L V) (bits : V → Bit) {k : ℕ} (p : Fin k → V) :
    oldProfile (profile (Marked.table T bits) p) = profile T p := rfl

@[simp] theorem profileBit_marked {L : Signature} {V : Type v}
    (T : BoolTable L V) (bits : V → Bit) {k : ℕ} (p : Fin k → V) (i : Fin k) :
    profileBit (profile (Marked.table T bits) p) i = bits (p i) := by
  exact Marked.boolBit_bitBool _

theorem markedProfile_ext {L : Signature} {k : ℕ}
    {p q : Profile (Marked.addBit L) k} (ho : oldProfile p = oldProfile q)
    (hb : ∀ i, profileBit p i = profileBit q i) : p = q := by
  funext a
  rcases a with ⟨r,slots⟩
  cases r using Fin.cases with
  | zero =>
    change Fin 1 → Fin k at slots
    have hs : slots = fun _ => slots 0 := by
      funext i
      exact congrArg slots (Subsingleton.elim _ _)
    have h := congrArg Marked.bitBool (hb (slots 0))
    simp only [profileBit,Marked.bitBool_boolBit] at h
    change p ⟨0,slots⟩ = q ⟨0,slots⟩
    rw [hs]
    exact h
  | succ r => exact congrFun ho ⟨r,slots⟩

/-- All finite atomic profiles after expansion are precisely the complete
old profile and the actual unary bit at every named slot. This includes k=0. -/
theorem marked_profile_eq_iff {L : Signature} {V : Type v} {W : Type w}
    (A : BoolTable L V) (B : BoolTable L W) (a : V → Bit) (b : W → Bit)
    {k : ℕ} (p : Fin k → V) (q : Fin k → W) :
    profile (Marked.table A a) p = profile (Marked.table B b) q ↔
      profile A p = profile B q ∧ ∀ i, a (p i) = b (q i) := by
  constructor
  · intro h
    refine ⟨congrArg oldProfile h,?_⟩
    intro i
    simpa only [profileBit_marked] using congrArg (fun t => profileBit t i) h
  · rintro ⟨ho,hb⟩
    exact markedProfile_ext ho (by simpa only [profileBit_marked] using hb)

theorem marked_unaryProfile_eq_iff {L : Signature} {V : Type v} {W : Type w}
    (A : BoolTable L V) (B : BoolTable L W) (a : V → Bit) (b : W → Bit) (x : V) (y : W) :
    unaryProfile (Marked.table A a) x = unaryProfile (Marked.table B b) y ↔
      unaryProfile A x = unaryProfile B y ∧ a x = b y := by
  simpa only [unaryProfile,forall_const] using
    marked_profile_eq_iff A B a b (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)

theorem marked_pairProfile_eq_iff {L : Signature} {V : Type v} {W : Type w}
    (A : BoolTable L V) (B : BoolTable L W) (a : V → Bit) (b : W → Bit)
    (x y : V) (z t : W) :
    pairProfile (Marked.table A a) x y = pairProfile (Marked.table B b) z t ↔
      pairProfile A x y = pairProfile B z t ∧ a x = b z ∧ a y = b t := by
  simpa only [pairProfile,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one] using
    marked_profile_eq_iff A B a b ![x,y] ![z,t]

theorem sameSortSymmetric_of_iso {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Iso A B)
    (hsym : SameSortSymmetric B) : SameSortSymmetric A := by
  intro x y hxy
  have hu : unaryProfile B (e.point x) = unaryProfile B (e.point y) := by
    exact (unaryProfile_embedding e.toEmbedding x).trans
      (hxy.trans (unaryProfile_embedding e.toEmbedding y).symm)
  have hh := hsym (e.point x) (e.point y) hu
  exact (pairProfile_embedding e.toEmbedding x y).symm.trans
    (hh.trans (pairProfile_embedding e.toEmbedding y x))

theorem sameSortSymmetric_marked {L : Signature} {V : Type v}
    {T : BoolTable L V} (hsym : SameSortSymmetric T) (bits : V → Bit) :
    SameSortSymmetric (Marked.table T bits) := by
  intro x y hxy
  obtain ⟨hold,hbit⟩ := (marked_unaryProfile_eq_iff T T bits bits x y).mp hxy
  exact (marked_pairProfile_eq_iff T T bits bits x y y x).mpr
    ⟨hsym x y hold,hbit,hbit.symm⟩

theorem sameSortSymmetric_decoded {L : Signature} {V : Type v} {W : Type w}
    (T : BoolTable (Marked.addBit L) V) {U : BoolTable L W}
    (e : Iso (Marked.oldTable T) U) (hsym : SameSortSymmetric U) :
    SameSortSymmetric T := by
  have h := sameSortSymmetric_marked (sameSortSymmetric_of_iso e hsym) (Marked.bits T)
  simpa only [Marked.table_oldTable_bits] using h

theorem irreducible_marked {L : Signature} {V : Type v} (T : BoolTable L V)
    (bits : V → Bit) (hirr : (toRelational T).Irreducible) :
    (toRelational (Marked.table T bits)).Irreducible := by
  intro P Q hs
  apply hirr P Q
  refine ⟨hs.1,?_⟩
  intro n R xs hR
  let R' : (Marked.addBit L).language.Rel n := ⟨R.val.succ,R.property⟩
  exact hs.2 R' xs hR

theorem marked_expanded_irreducible {L : Signature} {V : Type v}
    (T : BoolTable L V) (bits : V → Bit) :
    (toRelational (Marked.table (expand T) bits)).Irreducible :=
  irreducible_marked _ _ (expand_irreducible T)

end CCO.FullPhaseLift.Canonical
