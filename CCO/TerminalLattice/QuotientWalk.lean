import CCO.TerminalLattice.FibreSAP
import Mathlib.Data.Finset.Basic

/-!
# B050 C12: any finite quotient walk has distinct ORIGINAL representatives

This is stronger than the two-edge semigroup lemma: even if the same
J-quotient class occurs arbitrarily many times, choose a different real
point for EACH formal occurrence, avoiding both pinned OLD endpoints.
It derives the required fresh-fibre interface from *actual original*
homogeneity and AgeSAP via the existing B050 `freshFibre_of_original_SAP`.

This is a finite-walk combinatorial helper, not yet the full
source-09 positive atomic-word profile theorem.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {A : Type u}

/-- Simultaneous fresh real representatives of an arbitrary FINITE list
of quotient classes, avoiding an arbitrarily prescribed finite OLD set.
Repeated quotient positions stay represented by pairwise DISTINCT real
points. -/
theorem distinct_quotient_representatives
    (J : Setoid A) (fresh : FreshFibre J)
    (qs : List (Quotient J)) (forbidden : Finset A) :
    ∃ xs : List A,
      xs.Nodup ∧
      List.Forall₂ (fun a q => Quotient.mk J a = q) xs qs ∧
      ∀ a ∈ xs, a ∉ forbidden := by
  classical
  induction qs generalizing forbidden with
  | nil =>
      exact ⟨[], List.nodup_nil, List.Forall₂.nil, by simp⟩
  | cons q qs ih =>
      obtain ⟨x, hxF, hxQ⟩ := fresh q forbidden
      obtain ⟨xs, hnodup, hqxs, hAvoid⟩ := ih (insert x forbidden)
      refine ⟨x :: xs, ?_, List.Forall₂.cons hxQ hqxs, ?_⟩
      · apply List.nodup_cons.mpr
        constructor
        · intro hx
          exact (hAvoid x hx) (Finset.mem_insert_self x forbidden)
        · exact hnodup
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | hmem
        · exact hxF
        · intro hF
          exact (hAvoid a hmem) (Finset.mem_insert_of_mem hF)

/-- With pinned OLD real endpoints x,z, none of the chosen distinct
intermediate representatives collides with either endpoint. No promise
of distinct quotient classes is made (and none is needed). -/
theorem distinct_quotient_intermediates
    (J : Setoid A) (fresh : FreshFibre J)
    (qs : List (Quotient J)) (x z : A) :
    ∃ mids : List A,
      mids.Nodup ∧
      List.Forall₂ (fun a q => Quotient.mk J a = q) mids qs ∧
      ∀ a ∈ mids, a ≠ x ∧ a ≠ z := by
  classical
  obtain ⟨xs, hnodup, hqs, hAvoid⟩ :=
    distinct_quotient_representatives J fresh qs ({x, z} : Finset A)
  refine ⟨xs, hnodup, hqs, ?_⟩
  intro a ha
  have hF := hAvoid a ha
  constructor
  · intro hax
    exact hF (by simp [hax])
  · intro haz
    exact hF (by simp [haz])

end CCO.TerminalLattice

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Actual original-source B050 C12 instance of arbitrarily many fresh
J-class representatives, including quotient returns and repeated middle
positions. All hypotheses are from ORIGINAL homogeneous SAP source;
no extra infinite-fibre axiom, CCO or FULL cover is introduced. -/
theorem original_distinct_quotient_intermediates
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (qs : List (Quotient J.val)) (x z : X i) :
    ∃ mids : List (X i),
      mids.Nodup ∧
      List.Forall₂ (fun a q => Quotient.mk J.val a = q) mids qs ∧
      ∀ a ∈ mids, a ≠ x ∧ a ≠ z :=
  distinct_quotient_intermediates J.val
    (freshFibre_of_original_SAP S H sap J hJ) qs x z

end CCO.TerminalLattice
