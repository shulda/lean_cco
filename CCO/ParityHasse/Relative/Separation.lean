import CCO.ParityHasse.Relative.Powers

/-! Least positive witnesses and the outer-saturated three-domain RAW
support-Helly obstruction. The proof does not use ball Helly, Hasse or CRT. -/
universe u v w t
namespace CCO.ParityHasse.Relative
open Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- Actual least exponents; the old optional atom is the colour of (x,y).
Its entire orbital lies in both displayed powers by colour invariance. -/
structure LeastWitness (K : ColourEq S i) (A B : Rel (X i)) where
  x : X i
  y : X i
  n : Nat
  m : Nat
  n_positive : 0 < n
  m_positive : 0 < m
  inA : power K.val A m x y
  inB : power K.val B n x y
  outside : ¬ K x y
  minB : ∀ k, k < n → ∀ a b, power K.val B k a b → closure K.val A a b → K a b
  minA : ∀ k, k < m → ¬ power K.val A k x y

 theorem exists_leastWitness (K : ColourEq S i) (A B : Rel (X i))
    (h : ∃ x y, closure K.val A x y ∧ closure K.val B x y ∧ ¬ K x y) :
    Nonempty (LeastWitness S K A B) := by
  classical
  have exn : ∃ n, ∃ x y, power K.val B n x y ∧ closure K.val A x y ∧ ¬K x y := by
    obtain ⟨x,y,hA,⟨n,hB⟩,hK⟩ := h
    exact ⟨n,x,y,hB,hA,hK⟩
  let n := Nat.find exn
  obtain ⟨x,y,hB,hA,hK⟩ := Nat.find_spec exn
  have hn : 0 < n := by
    by_contra hn
    have hz : n = 0 := by omega
    change power K.val B n x y at hB
    rw [hz] at hB
    exact hK hB
  let m := Nat.find hA
  have hm : 0 < m := by
    by_contra hm
    have hz : m = 0 := by omega
    have hh : power K.val A m x y := Nat.find_spec hA
    rw [hz] at hh
    exact hK hh
  refine ⟨⟨x,y,n,m,hn,hm,Nat.find_spec hA,hB,hK,?_,?_⟩⟩
  · intro k hk a b hBk hAk
    by_contra hab
    exact Nat.find_min exn hk ⟨a,b,hBk,hAk,hab⟩
  · exact fun k hk => Nat.find_min hA hk

include H in
/-- The selected old colour is a genuine diversity atom outside K and
its WHOLE orbital is in both least positive powers. -/
theorem leastWitness_atom (K : ColourEq S i) (A B : Rel (X i))
    (hA : ColourInvariant S i A) (hB : ColourInvariant S i B)
    (W : LeastWitness S K A B) :
    S.colour W.x W.y ≠ none ∧
      S.rawAtomRel (S.colour W.x W.y) ≤ power K.val A W.m ∧
      S.rawAtomRel (S.colour W.x W.y) ≤ power K.val B W.n ∧
      ∀ x y, S.rawAtomRel (S.colour W.x W.y) x y → ¬K x y := by
  refine ⟨?_,?_,?_,?_⟩
  · intro hc
    have he := (S.colour_none_iff W.x W.y).mp hc
    have hxy : W.x = W.y := by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he
    exact W.outside (hxy ▸ K.val.refl W.x)
  · intro x y hc
    exact (power_invariant S H K A hA W.m x y W.x W.y hc).mpr W.inA
  · intro x y hc
    exact (power_invariant S H K B hB W.n x y W.x W.y hc).mpr W.inB
  · intro x y hc hK
    exact W.outside ((K.2 x y W.x W.y hc).mp hK)

include H in
/-- C17, with both m=1 and n=1 handled by the literal K-zero power. -/
theorem leastWitness_exclusion (K : ColourEq S i) (A B : Rel (X i))
    (hA : ColourInvariant S i A) (satA : Bisaturated K.val A)
    (W : LeastWitness S K A B) :
    ¬ mul (power K.val A (W.m-1)) (power K.val B (W.n-1)) W.x W.y := by
  rintro ⟨z,hxz,hzy⟩
  have hs := colourInvariant_symmetric S hA
  have eqv := closure_equivalence K.val A satA hs
  have hAz : closure K.val A z W.y :=
    eqv.trans (eqv.symm ⟨W.m-1,hxz⟩) ⟨W.m,W.inA⟩
  have hK : K z W.y := W.minB (W.n-1) (by have := W.n_positive; omega) z W.y hzy hAz
  have hxy := (power_bisaturated K.val A satA (W.m-1)).right hxz hK
  exact W.minA (W.m-1) (by have := W.m_positive; omega) hxy

/-- The actual obstruction uses a generally non-saturated single old atom;
the OUTER factors, at zero as well, supply both K-saturations. -/
def obstruction (K : ColourEq S i) (A B : Rel (X i))
    (W : LeastWitness S K A B) : Rel (X i) :=
  mul (mul (power K.val A (W.m-1)) (S.rawAtomRel (S.colour W.x W.y)))
    (power K.val B (W.n-1))

 theorem obstruction_bisaturated (K : ColourEq S i) (A B : Rel (X i))
    (satA : Bisaturated K.val A) (satB : Bisaturated K.val B)
    (W : LeastWitness S K A B) : Bisaturated K.val (obstruction S K A B W) := by
  constructor
  · change mul K.val (mul (mul _ _) _) = _
    rw [← mul_assoc, ← mul_assoc, (power_bisaturated K.val A satA _).1]
    rfl
  · change mul (mul (mul _ _) _) K.val = _
    rw [mul_assoc, (power_bisaturated K.val B satB _).2]
    rfl

 theorem obstruction_contains_atom (K : ColourEq S i) (A B : Rel (X i))
    (hKA : K ≤ A) (hKB : K ≤ B) (W : LeastWitness S K A B) :
    S.rawAtomRel (S.colour W.x W.y) ≤ obstruction S K A B W := by
  intro x y hc
  exact ⟨y,⟨x,kernel_le_power K.val A hKA _ _ _ (K.val.refl x),hc⟩,
    kernel_le_power K.val B hKB _ _ _ (K.val.refl y)⟩

include H cco in
 theorem obstruction_exact (K : ColourEq S i) (hK : Exact S K)
    (A B : Rel (X i)) (hA : Exact S A) (hB : Exact S B)
    (W : LeastWitness S K A B) : Exact S (obstruction S K A B W) :=
  exact_comp S H cco
    (exact_comp S H cco (power_exact S H cco K hK A hA _) (exact_actual_colour S W.x W.y))
    (power_exact S H cco K hK B hB _)

include H in
 theorem obstruction_meets_left (K : ColourEq S i) (A B : Rel (X i))
    (hA : ColourInvariant S i A) (hKA : K ≤ A) (hKB : K ≤ B)
    (satA : Bisaturated K.val A) (W : LeastWitness S K A B) :
    ∃ x y, A x y ∧ obstruction S K A B W x y := by
  have hm : W.m = (W.m-1)+1 := by have := W.m_positive; omega
  have hw := W.inA
  rw [hm, power_succ] at hw
  obtain ⟨z,hxz,hzy⟩ := hw
  refine ⟨z,W.y,hzy,W.y,⟨W.x,?_,rfl⟩,?_⟩
  · exact power_symmetric K.val A (colourInvariant_symmetric S hA) satA _ _ _ hxz
  · exact kernel_le_power K.val B hKB _ _ _ (K.val.refl W.y)

 theorem obstruction_meets_right (K : ColourEq S i) (A B : Rel (X i))
    (hKA : K ≤ A) (hKB : K ≤ B) (satB : Bisaturated K.val B)
    (hsB : ∀ x y, B x y → B y x) (W : LeastWitness S K A B) :
    ∃ x y, B x y ∧ obstruction S K A B W x y := by
  have hn : W.n = 1+(W.n-1) := by have := W.n_positive; omega
  have hw := W.inB
  rw [hn, power_add K.val B satB, power_one K.val B satB] at hw
  obtain ⟨z,hxz,hzy⟩ := hw
  refine ⟨W.x,z,hxz,W.y,⟨W.x,?_,rfl⟩,?_⟩
  · exact kernel_le_power K.val A hKA _ _ _ (K.val.refl W.x)
  · exact power_symmetric K.val B hsB satB _ _ _ hzy

include H in
/-- An intersection with K rotates to the excluded smaller product.
This proves avoidance without accidentally saturating the middle atom. -/
theorem obstruction_avoids_kernel (K : ColourEq S i) (A B : Rel (X i))
    (hA : ColourInvariant S i A) (hB : ColourInvariant S i B)
    (satA : Bisaturated K.val A) (satB : Bisaturated K.val B)
    (W : LeastWitness S K A B) :
    ∀ x y, obstruction S K A B W x y → ¬K x y := by
  rintro p q ⟨v,⟨u,hpu,hc⟩,hvq⟩ hpq
  have hup := power_symmetric K.val A (colourInvariant_symmetric S hA) satA _ _ _ hpu
  have hqv := power_symmetric K.val B (colourInvariant_symmetric S hB) satB _ _ _ hvq
  have huv : mul (power K.val A (W.m-1)) (power K.val B (W.n-1)) u v :=
    ⟨q,(power_bisaturated K.val A satA _).right hup hpq,hqv⟩
  have inv := colourInvariant_comp S H (power_invariant S H K A hA (W.m-1))
    (power_invariant S H K B hB (W.n-1))
  exact leastWitness_exclusion S H K A B hA satA W
    ((inv u v W.x W.y hc).mp huv)

include H cco in
/-- C19: the full relative closure separation source theorem, using ONLY
the three-domain support instance of accepted RAW exact Helly. -/
theorem closure_separation (K : ColourEq S i) (hK : Exact S K)
    (A B : Rel (X i)) (hA : Exact S A) (hB : Exact S B)
    (hKA : K ≤ A) (hKB : K ≤ B)
    (satA : Bisaturated K.val A) (satB : Bisaturated K.val B)
    (hAB : (fun x y => A x y ∧ B x y) = K) :
    (fun x y => closure K.val A x y ∧ closure K.val B x y) = K := by
  funext x y; apply propext
  constructor
  · intro hxy
    by_contra hKxy
    obtain ⟨W⟩ := exists_leastWitness S K A B ⟨x,y,hxy.1,hxy.2,hKxy⟩
    have iA := hA.colourInvariant S H
    have iB := hB.colourInvariant S H
    have hab : ∃ x y, A x y ∧ B x y := by
      obtain ⟨p⟩ := S.nonemptySort i
      exact ⟨p,p,hKA p p (K.val.refl p),hKB p p (K.val.refl p)⟩
    obtain ⟨p,q,hAp,hBp,hTp⟩ := exact_three_helly S H cco hA hB
      (obstruction_exact S H cco K hK A B hA hB W) hab
      (obstruction_meets_left S H K A B iA hKA hKB satA W)
      (obstruction_meets_right S K A B hKA hKB satB (colourInvariant_symmetric S iB) W)
    have hpq : K p q := by rw [← hAB]; exact ⟨hAp,hBp⟩
    exact obstruction_avoids_kernel S H K A B iA iB satA satB W p q hTp hpq
  · intro h; exact ⟨⟨0,h⟩,⟨0,h⟩⟩

 theorem identity_bisaturated (R : Rel (X i)) : Bisaturated (⊥ : ColourEq S i).val R := by
  constructor <;> funext x y <;> apply propext
  · exact ⟨fun ⟨z,hxz,hzy⟩ => hxz ▸ hzy,fun h => ⟨x,rfl,h⟩⟩
  · exact ⟨fun ⟨z,hxz,hzy⟩ => hzy ▸ hxz,fun h => ⟨y,h,rfl⟩⟩

include H cco in
/-- C20: literal equality is the genuine zero-letter RAW profile. -/
theorem identity_separation (A B : Rel (X i)) (hA : Exact S A) (hB : Exact S B)
    (hAref : ∀ x, A x x) (hBref : ∀ x, B x x)
    (hAB : (fun x y => A x y ∧ B x y) = Eq) :
    (fun x y => closure (⊥ : ColourEq S i).val A x y ∧
      closure (⊥ : ColourEq S i).val B x y) = Eq := by
  apply closure_separation S H cco (⊥ : ColourEq S i) (exact_identity S) A B hA hB
  · intro x y h; exact h ▸ hAref x
  · intro x y h; exact h ▸ hBref x
  · exact identity_bisaturated S A
  · exact identity_bisaturated S B
  · exact hAB

end CCO.ParityHasse.Relative
