import CCO.ExactEPGeometry.ExactEquivalenceLattice

/-!
# B062 C59–C60: actual largest FULL RAW-exact finite gate meet

The common original kernel is NOT the meet in the larger lattice of all
invariant equivalences. It is the actual finite intersection in the
already proved full RAW-exact equivalence lattice. Each original exact
gate is an `ExactEq`; the finite inf is represented by the real
intersection of its whole pair relations, including logical identity.

The empty gate list gives original Top, not Id. Repetitions and zero
stages are allowed. This is the algebraic core of the original label
kernel; the still-open C61–C64 task is to prove that actual canonical
character bits are preserved exactly by this common kernel.
-/

universe u v w

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

/-- The TRUE finite meet of original FULL RAW-exact equivalences,
including the empty (Top) case. Not an arbitrary colour-invariant meet. -/
def originalExactGateMeet (L : List (ExactEq S i)) : ExactEq S i :=
  L.foldr (fun E F => E ⊓ F) ⊤

@[simp] theorem originalExactGateMeet_nil :
    originalExactGateMeet S i [] = (⊤ : ExactEq S i) := rfl

@[simp] theorem originalExactGateMeet_cons
    (E : ExactEq S i) (L : List (ExactEq S i)) :
    originalExactGateMeet S i (E :: L) =
      E ⊓ originalExactGateMeet S i L := rfl

/-- The common original gate is exactly the ACTUAL intersection of its
listed original represented equivalence relations, at every ordered
pair of real original points. -/
theorem originalExactGateMeet_iff
    (L : List (ExactEq S i)) (x y : X i) :
    originalExactGateMeet S i L x y ↔
      ∀ E ∈ L, E x y := by
  induction L with
  | nil =>
      change True ↔ ∀ E ∈ ([] : List (ExactEq S i)), E x y
      simp
  | cons E tail ih =>
      change (E x y ∧ originalExactGateMeet S i tail x y) ↔
        ∀ F ∈ E :: tail, F x y
      constructor
      · rintro ⟨hE,hTail⟩ F hF
        rcases List.mem_cons.mp hF with rfl | hMem
        · exact hE
        · exact (ih.mp hTail) F hMem
      · intro h
        refine ⟨h E (by simp), ih.mpr ?_⟩
        intro F hMem
        exact h F (by simp [hMem])

/-- EVERY actual member of the original gate list contains the common
finite exact kernel, not just a selected member of an invariant family. -/
theorem originalExactGateMeet_le_member
    (L : List (ExactEq S i)) (E : ExactEq S i)
    (hE : E ∈ L) :
    originalExactGateMeet S i L ≤ E := by
  induction L with
  | nil => cases hE
  | cons F tail ih =>
      rcases List.mem_cons.mp hE with rfl | hMem
      · change E ⊓ originalExactGateMeet S i tail ≤ E
        exact inf_le_left
      · change F ⊓ originalExactGateMeet S i tail ≤ E
        exact le_trans inf_le_right (ih hMem)

/-- The finite original gate meet is the GREATEST true FULL RAW-exact
equivalence lying below every listed original gate. The maximality
quantifies over genuine `ExactEq` objects, not general invariants. -/
theorem originalExactGateMeet_greatest
    (L : List (ExactEq S i)) (K : ExactEq S i) :
    K ≤ originalExactGateMeet S i L ↔
      ∀ E ∈ L, K ≤ E := by
  induction L with
  | nil =>
      constructor
      · intro _ E hE
        cases hE
      · intro _
        exact le_top
  | cons E tail ih =>
      change K ≤ E ⊓ originalExactGateMeet S i tail ↔
        ∀ F ∈ E :: tail, K ≤ F
      constructor
      · intro h F hMem
        rcases List.mem_cons.mp hMem with rfl | hTail
        · exact le_trans h inf_le_left
        · exact (ih.mp (le_trans h inf_le_right)) F hTail
      · intro h
        apply le_inf
        · exact h E (by simp)
        · exact ih.mpr (by
            intro F hMem
            exact h F (by simp [hMem]))

/-- Source C59 is an ACTUAL original FULL exact equivalence, retaining
the real diagonal and its complete RAW presentation, even at zero
steps. -/
theorem originalExactGateMeet_fullExact
    (L : List (ExactEq S i)) :
    FullExact S (fun x y => originalExactGateMeet S i L x y) :=
  (originalExactGateMeet S i L).property

theorem originalExactGateMeet_reflexive
    (L : List (ExactEq S i)) (x : X i) :
    originalExactGateMeet S i L x x :=
  (originalExactGateMeet S i L).val.val.refl x

end
end CCO.ExactEPGeometry
