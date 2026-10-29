import CCO.RealClosure.Bounds.Algebraicity
import Mathlib.Data.Set.Finite.Lattice

/-! Finite-base real algebraicity for actual homogeneous finite languages.
The transitivity argument uses the finite orbit of the WHOLE tuple of
algebraic parameters. No CCO, exactness, closure provider or index axiom is
assumed. -/

universe v w t
namespace CCO.AclOwners
open RealClosure.Bounds RealHull.Geometry ParityHasse.Original

variable {M : Type v} {G : Type t} [Group G] [MulAction G M]

/-- Finite-base transitivity, for arbitrary group actions. -/
theorem acl_transitive {A B : Finset M}
    (hB : ∀ b ∈ B, b ∈ Acl G A) : Acl G B ⊆ Acl G A := by
  classical
  intro x hx
  let T := ∀ b : ↥B, orbitOver G A b.val
  letI : ∀ b : ↥B, Finite (orbitOver G A b.val) :=
    fun b => (hB b.val b.property).to_subtype
  let FixA := {g : G // ∀ a ∈ A, g • a = a}
  let tuple : FixA → T := fun g b => ⟨g.val • b.val, g.val, g.property, rfl⟩
  let I := Set.range tuple
  let rep : I → FixA := fun i => Classical.choose i.property
  have hrep : ∀ i : I, tuple (rep i) = i.val :=
    fun i => Classical.choose_spec i.property
  have hfinite : (⋃ i : I, (fun z : M => (rep i).val • z) '' orbitOver G B x).Finite :=
    Set.finite_iUnion fun _ => hx.image _
  apply hfinite.subset
  rintro y ⟨g,hg,rfl⟩
  let i : I := ⟨tuple ⟨g,hg⟩, ⟨⟨g,hg⟩,rfl⟩⟩
  have hagree (b : M) (hb : b ∈ B) : (rep i).val • b = g • b :=
    congrArg (fun f : T => (f ⟨b,hb⟩).val) (hrep i)
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  refine ⟨((rep i).val⁻¹ * g) • x, ?_, ?_⟩
  · refine ⟨(rep i).val⁻¹ * g, ?_, rfl⟩
    intro b hb
    rw [mul_smul, ← hagree b hb, inv_smul_smul]
  · simp only [mul_smul, smul_inv_smul]

variable (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (H : HomogeneousSource S G)

/-- The equality-inclusive complete spoke tuple has a finite range. -/
def spokeSignature (A : Finset M) (x : M) : ↥A → FullColour S :=
  fun a => col S x a.val

include S H

/-- Every complete spoke fibre is one ACTUAL pointwise-base stabilizer orbit,
including fibres containing a named parameter. -/
theorem orbitOver_eq_spokeSignature (A : Finset M) (x : M) :
    orbitOver G A x = {y | spokeSignature S A y = spokeSignature S A x} := by
  classical
  ext y
  constructor
  · rintro ⟨g,hg,rfl⟩
    funext a
    change col S (g • x) a.val = col S x a.val
    exact (congrArg (col S (g • x)) (hg a.val a.property).symm).trans
      (col_invariant S H g x a.val)
  · intro hsig
    let f : Option ↥A → Sigma (fun _ : Unit => M) :=
      fun p => ⟨(), match p with | none => x | some a => a.val⟩
    let f' : Option ↥A → Sigma (fun _ : Unit => M) :=
      fun p => ⟨(), match p with | none => y | some a => a.val⟩
    have hc : ∀ p q, taggedColour S (f p) (f q) = taggedColour S (f' p) (f' q) := by
      intro p q
      apply congrArg (fun c : FullColour S =>
        (⟨(),(),c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j)))
      cases p with
      | none =>
        cases q with
        | none => exact (col_none S x x).mpr rfl |>.trans ((col_none S y y).mpr rfl).symm
        | some a => exact (congrFun hsig a).symm
      | some a =>
        cases q with
        | none => exact (col_symm S a.val x).trans ((congrFun hsig a).symm.trans (col_symm S y a.val))
        | some b => rfl
    obtain ⟨g,hg⟩ := H.extends_finite_diagram f f' hc
    refine ⟨g, ?_, ?_⟩
    · intro a ha
      have hh := hg (some ⟨a,ha⟩)
      exact eq_of_heq (Sigma.mk.inj hh).2
    · exact eq_of_heq (Sigma.mk.inj (hg none)).2

/-- A finite real base has finite real acl by finitely many complete spoke
fibres, retaining exactly the full actual stabilizer-orbit definition. -/
theorem acl_finite (A : Finset M) : (Acl G A).Finite := by
  classical
  letI := S.finiteAtom () ()
  let T := ↥A → FullColour S
  let fibre : T → Set M := fun s => {x | spokeSignature S A x = s}
  let finiteFibre : T → Set M := fun s => if (fibre s).Finite then fibre s else ∅
  have hf : ∀ s, (finiteFibre s).Finite := by
    intro s
    unfold finiteFibre
    split_ifs with hs
    · exact hs
    · exact Set.finite_empty
  apply (Set.finite_iUnion hf).subset
  intro x hx
  have hfin : (fibre (spokeSignature S A x)).Finite := by
    change ({y | spokeSignature S A y = spokeSignature S A x}).Finite
    rw [← orbitOver_eq_spokeSignature S H A x]
    exact hx
  apply Set.mem_iUnion.mpr
  refine ⟨spokeSignature S A x, ?_⟩
  change x ∈ (if (fibre (spokeSignature S A x)).Finite then fibre (spokeSignature S A x) else ∅)
  rw [if_pos hfin]
  rfl

noncomputable def closureFinset (A : Finset M) : Finset M :=
  (acl_finite S H A).toFinset

@[simp] theorem mem_closureFinset (A : Finset M) (x : M) :
    x ∈ closureFinset S H A ↔ x ∈ Acl G A :=
  Set.Finite.mem_toFinset _

theorem subset_closureFinset (A : Finset M) : A ⊆ closureFinset S H A :=
  fun x hx => (mem_closureFinset S H A x).mpr (parameter_mem_acl A hx)

theorem acl_closureFinset (A : Finset M) :
    Acl G (closureFinset S H A) = Acl G A := by
  apply Set.Subset.antisymm
  · exact acl_transitive (fun b hb => (mem_closureFinset S H A b).mp hb)
  · exact acl_mono (subset_closureFinset S H A)

/-- Absolute closure is closure in the ambient real source. -/
def Closed (G : Type t) [Group G] [MulAction G M] (A : Finset M) : Prop :=
  Acl G A = (A : Set M)

theorem closed_closureFinset (A : Finset M) : Closed G (closureFinset S H A) := by
  rw [Closed, acl_closureFinset S H A]
  ext x
  exact (mem_closureFinset S H A x).symm

end CCO.AclOwners
