import CCO.ParityHasse.Relative.Exact
import CCO.ParityHasse.Relative.Algebra
import CCO.RawExact.ActualQuotientSource

/-! Full exact pullback for words in ACTUAL quotient orbitals. The empty
word is real quotient equality and the empty restriction list is Top.
Surjectivity supplies the intermediate real witness, without any section
of the original automorphism group or any quotient homogeneity premise. -/
universe u v w t q
namespace CCO.ParityHasse.Relative
open Original

section Words
variable (G : Type t) [Group G] (Q : Type q) [MulAction G Q]
/-- A RAW word in actual group orbitals, including genuine empty equality. -/
inductive OrbitalWord where
  | nil : OrbitalWord
  | atom : Q → Q → OrbitalWord → OrbitalWord

def OrbitalWord.relation : OrbitalWord Q → Q → Q → Prop
  | .nil => Eq
  | .atom a b tail => mul (GroupActions.orbital (G := G) a b) (OrbitalWord.relation tail)

def orbitalEvaluate (P : List (OrbitalWord Q)) : Q → Q → Prop :=
  fun x y => ∀ w ∈ P, OrbitalWord.relation G Q w x y

/-- Full exactness in the actual orbital language, with nonempty result.
This is the literal finite-intersection-of-RAW-word definition. -/
def OrbitalExact (R : Q → Q → Prop) : Prop :=
  ∃ P : List (OrbitalWord Q), orbitalEvaluate G Q P = R ∧ ∃ x y, R x y
end Words

section Pullback
variable {A : Type v} {Q : Type q}
def pull (π : A → Q) (R : Q → Q → Prop) : A → A → Prop := fun x y => R (π x) (π y)

 theorem pull_identity (π : A → Q) : pull π Eq = GroupActions.kernel π := rfl

/-- Equality of the ACTUAL represented composition pullback. -/
theorem pull_comp (π : A → Q) (surj : Function.Surjective π) (R T : Q → Q → Prop) :
    pull π (mul R T) = mul (pull π R) (pull π T) := by
  funext x y; apply propext
  constructor
  · rintro ⟨r,hxr,hry⟩
    obtain ⟨z,rfl⟩ := surj r
    exact ⟨z,hxr,hry⟩
  · rintro ⟨z,hxz,hzy⟩; exact ⟨π z,hxz,hzy⟩

 theorem pull_injective (π : A → Q) (surj : Function.Surjective π) :
    Function.Injective (pull π) := by
  intro R T h
  funext x y
  obtain ⟨a,rfl⟩ := surj x
  obtain ⟨b,rfl⟩ := surj y
  exact congrFun (congrFun h a) b
end Pullback

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable {Q : Type q} [MulAction G Q]

include H in
/-- Every actual quotient orbital pulls back to K;a;K for the actual old
orbital a, including the equality case. No lifting assumption is used. -/
theorem actual_quotient_orbital_block (π : X i → Q)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) (K : ColourEq S i)
    (hK : GroupActions.kernel π = K) (x y : X i) :
    pull π (GroupActions.orbital (G := G) (π x) (π y)) =
      mul (mul K (S.rawAtomRel (S.colour x y))) K := by
  have h := GroupActions.orbital_pullback π π equivπ equivπ x y
  change pull π (GroupActions.orbital (G := G) (π x) (π y)) = _ at h
  rw [h]
  have ha := RawExact.actual_pair_orbital_of_homogeneous S H x y
  funext a b; apply propext
  constructor
  · rintro ⟨u,v,hau,huv,hvb⟩
    refine ⟨v,⟨u,?_,?_⟩,?_⟩
    · rwa [← hK]
    · rw [← ha]; exact huv
    · rwa [← hK]
  · rintro ⟨v,⟨u,hau,huv⟩,hvb⟩
    refine ⟨u,v,?_,?_,?_⟩
    · rwa [hK]
    · rw [ha]; exact huv
    · rwa [hK]

include H cco in
 theorem actual_quotient_atom_pullback_exact (π : X i → Q)
    (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (K : ColourEq S i) (hK : GroupActions.kernel π = K) (exK : Exact S K)
    (q r : Q) : Exact S (pull π (GroupActions.orbital (G := G) q r)) := by
  obtain ⟨x,rfl⟩ := surjπ q
  obtain ⟨y,rfl⟩ := surjπ r
  rw [actual_quotient_orbital_block S H π equivπ K hK x y]
  exact exact_comp S H cco (exact_comp S H cco exK (exact_actual_colour S x y)) exK

include H cco in
 theorem actual_quotient_word_pullback_exact (π : X i → Q)
    (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (K : ColourEq S i) (hK : GroupActions.kernel π = K) (exK : Exact S K) :
    ∀ w : OrbitalWord Q, Exact S (pull π (OrbitalWord.relation G Q w))
  | .nil => by simpa only [OrbitalWord.relation,pull_identity,hK] using exK
  | .atom q r tail => by
    rw [OrbitalWord.relation,pull_comp π surjπ]
    exact exact_comp S H cco
      (actual_quotient_atom_pullback_exact S H cco π surjπ equivπ K hK exK q r)
      (actual_quotient_word_pullback_exact π surjπ equivπ K hK exK tail)

include H cco in
/-- C25: full exact pullback, with no general old-to-quotient exact descent
premise and no quotient homogeneity/provider left unproved. -/
theorem actual_quotient_exact_pullback (π : X i → Q)
    (surjπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (K : ColourEq S i) (hK : GroupActions.kernel π = K) (exK : Exact S K)
    (R : Q → Q → Prop) (hR : OrbitalExact G Q R) : Exact S (pull π R) := by
  obtain ⟨P,rfl,q,r,hqr⟩ := hR
  obtain ⟨x,rfl⟩ := surjπ q
  obtain ⟨y,rfl⟩ := surjπ r
  induction P with
  | nil =>
    have hh : pull π (orbitalEvaluate G Q []) = (fun _ _ => True) := by
      funext a b; apply propext; simp [pull,orbitalEvaluate]
    rw [hh]
    exact exact_top S
  | cons w P ih =>
    have hP : orbitalEvaluate G Q P (π x) (π y) := fun z hz => hqr z (by simp [hz])
    have hww := actual_quotient_word_pullback_exact S H cco π surjπ equivπ K hK exK w
    have he := exact_meet S hww (ih hP)
      ⟨x,y,hqr w (by simp),hP⟩
    have hh : pull π (orbitalEvaluate G Q (w::P)) =
        (fun a b => pull π (OrbitalWord.relation G Q w) a b ∧ pull π (orbitalEvaluate G Q P) a b) := by
      funext a b; apply propext; simp [pull,orbitalEvaluate]
    rw [hh]
    exact he

end CCO.ParityHasse.Relative
