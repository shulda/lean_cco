import CCO.FinitePackets.Normalization.SquareKernel
import CCO.RawExact.Convolution
import CCO.ParityHasse.Original.ParityPowers

/-! The square kernel is literally a positive stable power P^n of the
source's single product P of all finite-packet diversity squares. This
identifies the finite-join construction with the pinned algorithm. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.RealHull.Canonical CCO.ParityHasse.Original
open CCO.FinitePackets.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def squaresWord : List (Atom S) → RawWord S () ()
  | [] => .nil ()
  | a :: as => RawWord.append S (atomWord S a 2) (squaresWord as)

def repeatedWord (word : RawWord S () ()) : Nat → RawWord S () ()
  | 0 => .nil ()
  | n+1 => RawWord.append S word (repeatedWord word n)

theorem repeatedWord_relation (word : RawWord S () ()) (n : Nat) :
    RawWord.relation S (repeatedWord S word n) = relPow (RawWord.relation S word) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatedWord,RawWord.relation_append,ih]; rfl

theorem atomWord_two (a : Atom S) : RawWord.relation S (atomWord S a 2) =
    RawSymmetric.compose (S.atomRel a) (S.atomRel a) := by
  rw [atomWord_relation]
  funext x y
  apply propext
  simp only [relPow,RawSymmetric.compose,exists_eq_right]

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)
include H

theorem squaresWord_reflexive (as : List (Atom S)) (x : M) :
    RawWord.relation S (squaresWord S as) x x := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [squaresWord,RawWord.relation_append,atomWord_two]
    obtain ⟨y,hy⟩ := colour_serial S H (some a) x
    exact ⟨x,⟨y,hy,(col_symm S y x).trans hy⟩,ih⟩

theorem atom_square_le_squaresWord {as : List (Atom S)} {a : Atom S} (ha : a ∈ as)
    (x z : M) (h : RawSymmetric.compose (S.atomRel a) (S.atomRel a) x z) :
    RawWord.relation S (squaresWord S as) x z := by
  induction as with
  | nil => simp at ha
  | cons b as ih =>
    rw [squaresWord,RawWord.relation_append,atomWord_two]
    rcases List.mem_cons.mp ha with he | ht
    · subst b
      exact ⟨z,h,squaresWord_reflexive S H as z⟩
    · obtain ⟨y,hy⟩ := colour_serial S H (some b) x
      exact ⟨x,⟨y,hy,(col_symm S y x).trans hy⟩,ih ht⟩

theorem squaresWord_le_equivalence (as : List (Atom S)) (E : ColourEq S ())
    (hE : ∀ a ∈ as, ∀ x z, RawSymmetric.compose (S.atomRel a) (S.atomRel a) x z → E x z) :
    ∀ x z, RawWord.relation S (squaresWord S as) x z → E x z := by
  induction as with
  | nil => intro x z h; exact h ▸ E.val.refl x
  | cons a as ih =>
    intro x z h
    rw [squaresWord,RawWord.relation_append,atomWord_two] at h
    obtain ⟨y,hxy,hyz⟩ := h
    exact E.val.trans (hE a List.mem_cons_self x y hxy)
      (ih (fun b hb => hE b (List.mem_cons_of_mem a hb)) y z hyz)

theorem squareClosure_le_of_square (a : Atom S) (E : ColourEq S ())
    (h : ∀ x z, RawSymmetric.compose (S.atomRel a) (S.atomRel a) x z → E x z) :
    squareClosure S a ≤ E := by
  apply (supportEquiv_le_iff S (evenSupport S a) E).mpr
  apply generated_le S (square S a) (equivalenceSupport S E)
  rintro b ⟨x,y,z,hxy,hyz,hxz⟩
  exact ⟨x,z,h x z ⟨y,hxy,hyz⟩,hxz⟩

theorem squareKernel_le_of_squares (F E : ColourEq S ())
    (h : ∀ a, AtomBelow S F a → ∀ x z,
      RawSymmetric.compose (S.atomRel a) (S.atomRel a) x z → E x z) :
    squareKernel S H F ≤ E := by
  classical
  letI := ColourEq.lattice S H (i := ())
  apply Finset.sup_le
  intro a ha
  exact squareClosure_le_of_square S H a E (h a ((mem_packetAtoms S F a).mp ha))

theorem relPow_mono_of_reflexive {R : M → M → Prop} (hR : ∀ x, R x x) :
    Monotone (relPow R) :=
  monotone_nat_of_le_succ (fun _ x y h => ⟨x,hR x,h⟩)

theorem relPow_reflexive {R : M → M → Prop} (hR : ∀ x, R x x) (n : Nat) :
    ∀ x, relPow R n x x := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ⟨x,hR x,ih x⟩

theorem relPow_le_equivalence {R : M → M → Prop} (E : ColourEq S ())
    (hRE : ∀ x y, R x y → E x y) (n : Nat) :
    ∀ x y, relPow R n x y → E x y := by
  induction n with
  | zero => intro x y h; exact h ▸ E.val.refl x
  | succ n ih => rintro x y ⟨z,hxz,hzy⟩; exact E.val.trans (hRE x z hxz) (ih z y hzy)

theorem reflexive_word_positive_stable_power (word : RawWord S () ())
    (hr : ∀ x, RawWord.relation S word x x) :
    ∃ n : Nat, 0 < n ∧ ∃ E : ColourEq S (),
      relPow (RawWord.relation S word) n = E.val.r ∧
      (∀ x y, RawWord.relation S word x y → E x y) ∧
      (∀ k, n ≤ k → relPow (RawWord.relation S word) n = relPow (RawWord.relation S word) k) := by
  let R := RawWord.relation S word
  have hc : ColourInvariant S () R := groupInvariant_colourInvariant S H
    (RawExact.word_invariant_of_homogeneous S H word)
  let C := {R : M → M → Prop // ColourInvariant S () R}
  letI : Finite C := finite_colour_relations S
  let powers : Nat →o C := {
    toFun := fun n => ⟨relPow R n,colourInvariant_relPow S H hc n⟩
    monotone' := relPow_mono_of_reflexive S H hr }
  obtain ⟨n₀,hn⟩ := WellFoundedGT.monotone_chain_condition powers
  let n := n₀+1
  have hstable (k : Nat) (hk : n ≤ k) : relPow R n = relPow R k :=
    congrArg Subtype.val ((hn n (by omega)).symm.trans (hn k (by omega)))
  have hidem : RawSymmetric.compose (relPow R n) (relPow R n) = relPow R n :=
    (relPow_add R n n).symm.trans (hstable (n+n) (by omega)).symm
  let E : ColourEq S () := ⟨⟨relPow R n,⟨relPow_reflexive S H hr n,
    (fun {x y} h => colourInvariant_symmetric S (colourInvariant_relPow S H hc n) x y h),by
      intro x y z hxy hyz
      rw [← hidem]
      exact ⟨y,hxy,hyz⟩⟩⟩,colourInvariant_relPow S H hc n⟩
  refine ⟨n,by omega,E,rfl,?_,hstable⟩
  intro x y hxy
  exact relPow_mono_of_reflexive S H hr (show 1 ≤ n by omega) x y ⟨y,hxy,rfl⟩

/-- Exactly the source product P, taking the genuine empty word at an
empty diversity list; some positive power is the constructed H0. -/
theorem squareKernel_is_stable_product_power (F : ColourEq S ()) :
    ∃ n : Nat, 0 < n ∧
      RawWord.relation S (repeatedWord S (squaresWord S (packetAtoms S F).toList) n) =
        (squareKernel S H F).val.r ∧
      (∀ k, n ≤ k →
        RawWord.relation S (repeatedWord S (squaresWord S (packetAtoms S F).toList) k) =
          (squareKernel S H F).val.r) := by
  classical
  let as := (packetAtoms S F).toList
  let word := squaresWord S as
  obtain ⟨n,hn,E,hE,hPE,hstable⟩ := reflexive_word_positive_stable_power S H word
    (squaresWord_reflexive S H as)
  have hEK : E ≤ squareKernel S H F := by
    intro x y hxy
    rw [← hE] at hxy
    apply relPow_le_equivalence S H (squareKernel S H F) ?_ n x y hxy
    apply squaresWord_le_equivalence S H as (squareKernel S H F)
    intro a ha x z h
    exact atom_square_le_kernel S H ((mem_packetAtoms S F a).mp (Finset.mem_toList.mp ha)) x z h
  have hKE : squareKernel S H F ≤ E := squareKernel_le_of_squares S H F E (by
    intro a ha x z h
    exact hPE x z (atom_square_le_squaresWord S H
      (Finset.mem_toList.mpr ((mem_packetAtoms S F a).mpr ha)) x z h))
  have heq : E = squareKernel S H F := le_antisymm hEK hKE
  have hr : relPow (RawWord.relation S word) n = (squareKernel S H F).val.r := by
    rw [hE,heq]
  exact ⟨n,hn,(repeatedWord_relation S word n).trans hr,fun k hk =>
    (repeatedWord_relation S word k).trans ((hstable k hk).symm.trans hr)⟩

end CCO.FinitePackets.Normalization
