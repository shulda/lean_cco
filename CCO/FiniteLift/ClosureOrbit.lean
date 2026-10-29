import CCO.RealClosure.Bounds.Algebraicity
import CCO.Owners.Product.Orbitals
import Mathlib.Data.Set.Finite.Basic

/-! Finite-base closure is the finite ACTUAL pointwise stabilizer orbit.
Finite complete homogeneous binary languages have finite finite-base closures;
no CCO, amalgamation, safe palette, quotient witness or EPPA enters this fact. -/

universe v w t
namespace CCO.FiniteLift

variable {M : Type v} (G : Type t) [Group G] [MulAction G M]

def orbitSet (A : Set M) (x : M) : Set M :=
  {y | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x = y}

def aclSet (A : Set M) : Set M := {x | (orbitSet G A x).Finite}

@[simp] theorem orbitSet_finset (A : Finset M) (x : M) :
    orbitSet G (↑A : Set M) x = RealClosure.Bounds.orbitOver G A x := rfl

@[simp] theorem aclSet_finset (A : Finset M) :
    aclSet G (↑A : Set M) = RealClosure.Bounds.Acl G A := rfl

theorem subset_aclSet (A : Set M) : A ⊆ aclSet G A := by
  intro x hx
  apply (Set.finite_singleton x).subset
  rintro y ⟨g, hg, rfl⟩
  exact Set.mem_singleton_iff.mpr (hg x hx)

theorem aclSet_mono {A B : Set M} (h : A ⊆ B) : aclSet G A ⊆ aclSet G B := by
  intro x hx
  apply hx.subset
  rintro y ⟨g, hg, hgy⟩
  exact ⟨g, fun a ha => hg a (h ha), hgy⟩

variable (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (H : HomogeneousSource S G)
include H

/-- The COMPLETE colour profile over a finite real base determines the whole
pointwise-stabilizer orbit, including logical equality and parameter points. -/
theorem orbitSet_eq_profile (A : Finset M) (x : M) :
    orbitSet G (↑A : Set M) x =
      {y | ∀ a ∈ A, S.colour (i := ()) (j := ()) x a = S.colour y a} := by
  classical
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩ a ha
    have he := S.colourInvariant_of_homogeneous H (i := ()) (j := ()) g x a
    rw [hg a ha] at he
    exact he.symm
  · intro hy
    let src : Option ↥A → Sigma (fun _ : Unit => M)
      | none => ⟨(), x⟩
      | some a => ⟨(), a.val⟩
    let dst : Option ↥A → Sigma (fun _ : Unit => M)
      | none => ⟨(), y⟩
      | some a => ⟨(), a.val⟩
    have hc : ∀ p q, taggedColour S (src p) (src q) = taggedColour S (dst p) (dst q) := by
      intro p q
      cases p with
      | none =>
        cases q with
        | none =>
          change (⟨(), (), S.colour (i := ()) x x⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j)) = ⟨(), (), S.colour y y⟩
          rw [(S.colour_none_iff x x).mpr rfl, (S.colour_none_iff y y).mpr rfl]
        | some a =>
          exact congrArg (fun c => (⟨(), (), c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j)))
            (hy a.val a.property)
      | some a =>
        cases q with
        | none =>
          have hh := S.colour_reverse (i := ()) (j := ()) x a.val
          have hh' := S.colour_reverse (i := ()) (j := ()) y a.val
          change taggedColour S ⟨(), a.val⟩ ⟨(), x⟩ = taggedColour S ⟨(), a.val⟩ ⟨(), y⟩
          apply congrArg (fun c => (⟨(), (), c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j)))
          rw [hh, hh', hy a.val a.property]
        | some b => rfl
    obtain ⟨g, hg⟩ := H.extends_finite_diagram src dst hc
    refine ⟨g, ?_, ?_⟩
    · intro a ha
      have hh := hg (some (⟨a, ha⟩ : ↥A))
      simpa only [src, dst, Sigma.smul_mk, Sigma.mk.injEq, heq_eq_eq, true_and] using hh
    · have hh := hg none
      simpa only [src, dst, Sigma.smul_mk, Sigma.mk.injEq, heq_eq_eq, true_and] using hh

/-- C01: finitely many COMPLETE profiles, and only their finite fibres,
form the actual algebraic closure. This covers finite sources and empty bases. -/
theorem aclSet_finset_finite (A : Finset M) : (aclSet G (↑A : Set M)).Finite := by
  classical
  letI := S.finiteAtom () ()
  let Profile := ↥A → Option (S.Atom () ())
  let profile : M → Profile := fun x a => S.colour x a.val
  let fibres : Profile → Set M := fun p => if h : (profile ⁻¹' {p}).Finite then profile ⁻¹' {p} else ∅
  have hf : ∀ p, (fibres p).Finite := by
    intro p
    dsimp [fibres]
    split
    · assumption
    · exact Set.finite_empty
  apply (Set.finite_iUnion hf).subset
  intro x hx
  have he : orbitSet G (↑A : Set M) x = profile ⁻¹' {profile x} := by
    rw [orbitSet_eq_profile G S H A x]
    ext y
    change (∀ a ∈ A, S.colour x a = S.colour y a) ↔ profile y = profile x
    constructor
    · intro hh
      funext a
      exact (hh a.val a.property).symm
    · intro hh a ha
      exact (congrFun hh (⟨a, ha⟩ : ↥A)).symm
  have hfin : (profile ⁻¹' {profile x}).Finite := he ▸ hx
  apply Set.mem_iUnion.mpr
  refine ⟨profile x, ?_⟩
  simp only [fibres, dif_pos hfin, Set.mem_preimage, Set.mem_singleton_iff]

theorem aclSet_finite (A : Set M) (hA : A.Finite) : (aclSet G A).Finite := by
  simpa only [Set.Finite.coe_toFinset] using aclSet_finset_finite G S H hA.toFinset

end CCO.FiniteLift
