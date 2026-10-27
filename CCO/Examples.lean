import CCO.BasePaths
import CCO.RawWords

/-!
# Concrete same-sort and cross-sort checks for the shared API

The source has exactly two named sorts, both with carrier Nat, and one
diversity atom on each ordered sort pair. Its optional none is genuine
equality of tagged real points. The examples use three real points with
distinct numerical coordinates, hence remain valid when sort tags repeat.
These are representation sanity tests, not a proof of SAP or CCO.
-/

namespace CCO.Examples

private abbrev U := Sigma (fun _ : Fin 2 => Nat)

private theorem tagged_ne_of_nat_ne {i j : Fin 2} {x y : Nat}
    (h : x ≠ y) : (⟨i, x⟩ : U) ≠ ⟨j, y⟩ := by
  intro hxy
  exact h (congrArg (fun p : U => p.2) hxy)

private def exampleColour {i j : Fin 2} (x y : Nat) : Option Unit :=
  if (⟨i, x⟩ : U) = ⟨j, y⟩ then none else some ()

def trivialPalette : AtomicSource (Fin 2) (fun _ => Nat) where
  Atom := fun _ _ => Unit
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => ⟨0⟩
  conv := fun _ => ()
  conv_invol := by
    intro i j a
    cases a
    rfl
  symmetricLoop := by
    intro i a
    cases a
    rfl
  colour := fun {i j} x y => exampleColour (i := i) (j := j) x y
  colour_none_iff := by
    intro i j x y
    by_cases h : (⟨i, x⟩ : U) = ⟨j, y⟩
    · simp [exampleColour, h]
    · simp [exampleColour, h]
  colour_swap := by
    intro i j x y a
    cases a
    by_cases h : (⟨i, x⟩ : U) = ⟨j, y⟩
    · have ht : (⟨j, y⟩ : U) = ⟨i, x⟩ := h.symm
      simp [exampleColour, h, ht]
    · have ht : (⟨j, y⟩ : U) ≠ ⟨i, x⟩ := Ne.symm h
      simp [exampleColour, h, ht]
  realized := by
    intro i j a
    cases a
    refine ⟨0, 1, ?_⟩
    have hn : (⟨i, (0 : Nat)⟩ : U) ≠ ⟨j, (1 : Nat)⟩ :=
      tagged_ne_of_nat_ne (by omega)
    simp [trivialPalette, exampleColour, hn]

theorem literal_diversity {i j : Fin 2} {x y : Nat} (h : x ≠ y) :
    trivialPalette.colour (i := i) (j := j) x y = some () := by
  have hn : (⟨i, x⟩ : U) ≠ ⟨j, y⟩ := tagged_ne_of_nat_ne h
  simp [trivialPalette, exampleColour, hn]

/-- Even when every sort tag repeats, the STRONG triangle has three
different real vertices (0,1,2). -/
theorem universal_triangle {i j k : Fin 2} :
    trivialPalette.Triangle (i := i) (j := j) (k := k) () () () := by
  exact ⟨0, 1, 2, literal_diversity (by omega),
    literal_diversity (by omega), literal_diversity (by omega)⟩

/-- The single diversity colour composes strongly on repeated sort 0. -/
example : () ∈ trivialPalette.product
    ({()} : trivialPalette.Menu (0 : Fin 2) (0 : Fin 2))
    ({()} : trivialPalette.Menu (0 : Fin 2) (0 : Fin 2)) := by
  exact ⟨(), by simp, (), by simp, universal_triangle⟩

/-- Genuinely typed cross-sort product 0 -> 1 -> 0. -/
example : () ∈ trivialPalette.product
    ({()} : trivialPalette.Menu (0 : Fin 2) (1 : Fin 2))
    ({()} : trivialPalette.Menu (1 : Fin 2) (0 : Fin 2)) := by
  exact ⟨(), by simp, (), by simp, universal_triangle⟩

/-- Logical equality is not the single STRONG diversity atom. -/
example : ¬ trivialPalette.atomRel (i := (0 : Fin 2)) (j := (0 : Fin 2))
    () (0 : Nat) (0 : Nat) := by
  intro h
  have hne := trivialPalette.atomRel_ne h
  exact hne rfl

/-- The RAW empty word evaluates to actual equality. -/
example : RawWord.relation trivialPalette (.nil (0 : Fin 2)) =
    TRel.ident (fun _ : Fin 2 => Nat) 0 :=
  RawWord.empty_word_is_identity trivialPalette 0

/-- Crucial distinction: a NONEMPTY two-letter RAW diversity walk has
a genuine identity OUTPUT, via a middle vertex on a different sort.
No such identity atom is added to any STRONG palette. -/
example :
    RawWord.relation trivialPalette
      (.atom (i := (0 : Fin 2)) (j := (1 : Fin 2)) ()
        (.atom (i := (1 : Fin 2)) (j := (0 : Fin 2)) ()
          (.nil (0 : Fin 2)))) (0 : Nat) (0 : Nat) := by
  change ∃ m : Nat,
      trivialPalette.colour (i := (0 : Fin 2)) (j := (1 : Fin 2))
        (0 : Nat) m = some () ∧
      ∃ n : Nat,
        trivialPalette.colour (i := (1 : Fin 2)) (j := (0 : Fin 2))
          m n = some () ∧ n = 0
  refine ⟨1, literal_diversity (by omega), 0,
    literal_diversity (by omega), rfl⟩

/-- An actual one-point base and two distinct roots of the SAME sort. -/
def sameSortSpan : trivialPalette.ActualSpan
    (i := (0 : Fin 2)) (j := (0 : Fin 2)) Unit where
  finiteBase := inferInstance
  baseSort := fun _ => 0
  point := fun _ => 0
  left := 1
  right := 2
  leftAtom := fun _ => ()
  rightAtom := fun _ => ()
  leftColour := by intro _; exact literal_diversity (by omega)
  rightColour := by intro _; exact literal_diversity (by omega)
  baseInjective := by intro a b h; cases a; cases b; rfl
  distinctRoots := tagged_ne_of_nat_ne (by omega)

/-- An actual one-point base with roots of different named sorts. -/
def crossSortSpan : trivialPalette.ActualSpan
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) Unit where
  finiteBase := inferInstance
  baseSort := fun _ => 0
  point := fun _ => 0
  left := 1
  right := 2
  leftAtom := fun _ => ()
  rightAtom := fun _ => ()
  leftColour := by intro _; exact literal_diversity (by omega)
  rightColour := by intro _; exact literal_diversity (by omega)
  baseInjective := by intro a b h; cases a; cases b; rfl
  distinctRoots := tagged_ne_of_nat_ne (by omega)

end CCO.Examples
