import CCO.PairHomogeneity
import CCO.UnaryFreshFrames.Quotient.Fibres

/-! There are only finitely many equivariant functions between two
surjective equivariant images of original real sorts. Original optional
pair colours include real equality, and pair homogeneity supplies the
required stabilizer motion. No SAP, CCO, NR2 or cover premise is used. -/

universe u v w r q z
namespace CCO.TerminalHiddenHN

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]

/-- The entire equivariant function family is finite, not only a chosen
syntactic term family. Both quotient carriers can inhabit arbitrary
universes, and the true diagonal is included in the finite colour code. -/
theorem finite_equivariant_maps
    (H : HomogeneousSource S G) (a b : ι)
    {Q : Type q} {R : Type z} [MulAction G Q] [MulAction G R]
    (π : X a → Q) (σ : X b → R)
    (ontoπ : Function.Surjective π) (ontoσ : Function.Surjective σ)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y) :
    {f : Q → R | ∀ (g : G) x, f (g • x) = g • f x}.Finite := by
  classical
  letI : Fintype (S.Atom a b) := S.finiteAtom a b
  obtain ⟨x⟩ := S.nonemptySort a
  have transitive : CCO.UnaryFreshFrames.Quotient.Transitive (G := G) (M := Q) := by
    intro p q
    obtain ⟨u,rfl⟩ := ontoπ p
    obtain ⟨v,rfl⟩ := ontoπ q
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H a u v
    exact ⟨g,(equivπ g u).symm.trans (congrArg π hg)⟩
  let T : Set (Q → R) := {f | ∀ (g : G) x, f (g • x) = g • f x}
  let representative (f : T) : X b := Classical.choose (ontoσ (f.val (π x)))
  have representative_eq (f : T) : σ (representative f) = f.val (π x) :=
    Classical.choose_spec (ontoσ (f.val (π x)))
  let code (f : T) : Option (S.Atom a b) := S.colour x (representative f)
  have injective : Function.Injective code := by
    intro f k hcode
    obtain ⟨g,hgx,hgr⟩ := S.pair_homogeneous_of_homogeneous H
      x x (representative f) (representative k) hcode
    have fixes_input : g • π x = π x :=
      (equivπ g x).symm.trans (congrArg π hgx)
    have fixes_output : g • f.val (π x) = f.val (π x) := by
      rw [← f.property g (π x),fixes_input]
    have point_eq : f.val (π x) = k.val (π x) := by
      calc
        f.val (π x) = g • f.val (π x) := fixes_output.symm
        _ = g • σ (representative f) :=
          congrArg (fun y : R => g • y) (representative_eq f).symm
        _ = σ (g • representative f) := (equivσ g (representative f)).symm
        _ = σ (representative k) := congrArg σ hgr
        _ = k.val (π x) := representative_eq k
    apply Subtype.ext
    exact CCO.UnaryFreshFrames.Quotient.equivariant_ext transitive (π x)
      f.property k.property point_eq
  exact Set.finite_coe_iff.mp (Finite.of_injective code injective)

end CCO.TerminalHiddenHN
