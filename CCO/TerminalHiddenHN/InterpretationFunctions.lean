import CCO.TerminalHiddenHN.Interpretation

/-! Source-facing finite semantic functions for the literal A02
interpretation. Original pair homogeneity and the genuine onto projection
terms suffice at EVERY hidden input. No SAP, CCO, NR2, FULL-cover premise
or later chosen normal-form list is used. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN
namespace RealInterpretation
open CCO.UnaryFreshFrames

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable {U : CCO.UnaryFreshFrames.Language.{max u l}} {V : Type k}
variable {P : CCO.UnaryFreshFrames.Structure U V}
variable (D : RealInterpretation S U P)

/-- The ORIGINAL group acts on each typed interpretation carrier through
the actual named-structure automorphisms specified by A02. -/
abbrev carrierAction (s : U.Sorts) : MulAction G (P.Carrier s) :=
  MulAction.compHom (P.Carrier s) D.motion

theorem typedEval_equivariant {s t : U.Sorts}
    (q : CCO.UnaryFreshFrames.Term U s t) :
    letI := carrierAction S D s
    letI := carrierAction S D t
    ∀ (g : G) x, P.typedEval q (g • x) = g • P.typedEval q x := by
  letI := carrierAction S D s
  letI := carrierAction S D t
  intro g x
  apply Subtype.ext
  change P.eval q ((D.motion g) • x.val) = (D.motion g) • P.eval q x.val
  exact (P.aut_eval (D.motion g) q x.val).symm

/-- A genuine onto real-source projection term is equivariant for the
same original action, not a newly selected quotient action. -/
theorem projection_equivariant (i : ι) {s : U.Sorts}
    (q : CCO.UnaryFreshFrames.Term U (D.realSort i) s) :
    letI := carrierAction S D s
    ∀ (g : G) x,
      P.typedEval q (D.root i (g • x)) = g • P.typedEval q (D.root i x) := by
  letI := carrierAction S D s
  intro g x
  apply Subtype.ext
  change P.eval q (D.root i (g • x)).val =
    (D.motion g) • P.eval q (D.root i x).val
  rw [← D.root_equivariant g i x]
  exact (P.aut_eval (D.motion g) q (D.root i x).val).symm

/-- Fixed input/output sorts retain the entire actual typed function
family. Finiteness is derived before any syntactic representatives are
chosen, and includes proper quotient inputs. -/
theorem typedFunctions_finite (s t : U.Sorts) :
    {f : P.Carrier s → P.Carrier t |
      ∃ q : CCO.UnaryFreshFrames.Term U s t, f = P.typedEval q}.Finite := by
  letI := carrierAction S D s
  letI := carrierAction S D t
  obtain ⟨i,qs,onto_s⟩ := D.projection s
  obtain ⟨j,qt,onto_t⟩ := D.projection t
  have finite_maps := finite_equivariant_maps S H i j
    (fun x => P.typedEval qs (D.root i x))
    (fun y => P.typedEval qt (D.root j y)) onto_s onto_t
    (projection_equivariant S D i qs) (projection_equivariant S D j qt)
  apply finite_maps.subset
  rintro f ⟨q,rfl⟩
  exact typedEval_equivariant S D q

/-- All actual values-valued named functions form a finite family at
every hidden input. The union ranges over the finite hidden sort set. -/
theorem namedFunctions_finite (s : U.Sorts) : (P.NamedFunctions s).Finite := by
  letI : Finite U.Sorts := D.finiteSorts
  let forget (t : U.Sorts) :
      (P.Carrier s → P.Carrier t) → (P.Carrier s → V) :=
    fun f x => (f x).val
  have finite_union :
      (⋃ t : U.Sorts, forget t ''
        {f : P.Carrier s → P.Carrier t |
          ∃ q : CCO.UnaryFreshFrames.Term U s t, f = P.typedEval q}).Finite :=
    Set.finite_iUnion (fun t => (typedFunctions_finite S H D s t).image (forget t))
  apply finite_union.subset
  rintro f ⟨t,q,rfl⟩
  exact Set.mem_iUnion.mpr ⟨t,⟨P.typedEval q,⟨q,rfl⟩,rfl⟩⟩

/-- Singleton closure finiteness is a CONSEQUENCE of finite actual
function families, with no later normal-form or SAP input. -/
theorem singletonClosure_finite (x : V) : (P.closureAt x).Finite := by
  let typed_x : P.Carrier (P.sort x) := ⟨x,rfl⟩
  have finite_values :=
    (namedFunctions_finite S H D (P.sort x)).image
      (fun f : P.Carrier (P.sort x) → V => f typed_x)
  exact (P.namedValues_eq_closureAt typed_x) ▸ finite_values

/-- Unary closure is a union of actual singleton closures; every finite
set, including an orphan-only or empty set, therefore has finite closure. -/
theorem finite_closure (A : Set V) (hA : A.Finite) : (P.closure A).Finite := by
  letI : Finite A := hA.to_subtype
  have finite_union : (⋃ x : A, P.closureAt x.val).Finite :=
    Set.finite_iUnion (fun x => singletonClosure_finite S H D x.val)
  apply finite_union.subset
  intro y hy
  obtain ⟨x,hx,hxy⟩ := (P.mem_closure_iff_singleton).mp hy
  exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hxy⟩

end RealInterpretation
end CCO.TerminalHiddenHN
