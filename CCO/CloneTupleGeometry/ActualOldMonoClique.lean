import CCO.CloneTupleGeometry.InfiniteMonochrome
import CCO.CloneTupleGeometry.LoopedCloneInstance

/-!
# B060 N03: a genuine infinite old owner sort supplies looped old cliques

Use actual AtomicSource symmetric same-sort atom colours and real equality
to eliminate the diagonal `none` in the infinite finite-palette pair Ramsey
theorem. This produces a single actual fine atom with a real (a,a,a)
triangle and an infinite injective monochromatic original sequence.
Its finite prefixes, lifted with clone-index zero, live in the
genuine B047 marked Fraisse limit for every valid character bit.
No old SAP, hidden SAP, quotient-action section or invented unary
expansion is introduced; infinitude of successor owner types is
still a separate next step.
-/

universe u v w t
namespace CCO.CloneTupleGeometry
open APCharacter RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- B060 N03: one fixed genuine original fine atom a, an actual
(a,a,a) triangle and infinitely many distinct a-clique owners. -/
theorem actual_infinite_old_mono_atom
    {i : ι} [Infinite (X i)] :
    ∃ (a : S.Atom i i), S.Triangle a a a ∧
      ∃ f : ℕ ↪ X i,
        ∀ m n : ℕ, m ≠ n → S.colour (f m) (f n) = some a := by
  classical
  letI : Fintype (S.Atom i i) := S.finiteAtom i i
  letI : Finite (Option (S.Atom i i)) := inferInstance
  have hsym : ∀ x y : X i, S.colour x y = S.colour y x := by
    intro x y
    by_cases hnone : S.colour x y = none
    · have htag := (S.colour_none_iff x y).mp hnone
      have hxy : x = y := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using htag
      subst y
      rfl
    · cases hc : S.colour x y with
      | none => exact (hnone hc).elim
      | some a =>
          have hs : S.colour y x = some (S.conv a) :=
            (S.colour_swap x y a).mp hc
          rw [hc, hs, S.symmetricLoop a]
  obtain ⟨c, f, hf⟩ :=
    infinite_monochromatic_pairs
      (fun x y : X i => S.colour x y) hsym
  have h01 : S.colour (f 0) (f 1) = c :=
    hf 0 1 (by decide)
  have hc : c ≠ none := by
    intro hnone
    have htag : (⟨i,f 0⟩ : Sigma X) = ⟨i,f 1⟩ :=
      (S.colour_none_iff (f 0) (f 1)).mp (h01.trans hnone)
    have hpoints : f 0 = f 1 := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using htag
    exact (show (0 : ℕ) ≠ 1 by decide) (f.injective hpoints)
  cases c with
  | none => exact (hc rfl).elim
  | some a =>
      refine ⟨a, ?_, f, ?_⟩
      · exact ⟨f 0, f 1, f 2,
          hf 0 1 (by decide), hf 1 2 (by decide),
          hf 0 2 (by decide)⟩
      · intro m n hmn
        exact hf m n hmn

variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)

/-- Actual B045/B047 source instance of arbitrary finite old monochromatic
owner-clique realizations. The original owner witnesses, represented old
colour, chosen valid phase bit and one genuine limit are all retained.
This does not yet assert the successor owner's Infinite instance. -/
theorem actual_clone_old_mono_marked_age_unbounded
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (b : Reached (CloneSAP.source S) A)
    [Infinite (X b.val)]
    (ε : Bit) (hε : P.validBit b.val ε) :
    ∃ a : S.Atom b.val b.val, S.Triangle a a a ∧
      ∀ n : ℕ, ∃ (points : Fin n ↪ X b.val)
        (f : Fin n ↪ Age.Limit (CloneSAP.source S)
          (CloneSAP.homogeneous S H)
          (P.completion_property (CloneSAP.CCO.cco_forward S cco))),
          (∀ x : Fin n,
            (Age.ownerEquiv (CloneSAP.source S)).symm
              ((Age.limitCoding (CloneSAP.source S)
                (CloneSAP.homogeneous S H)
                (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.owner
                (f x)) = (b.val,ε)) ∧
          (∀ x y : Fin n,
            (Age.limitCoding (CloneSAP.source S) (CloneSAP.homogeneous S H)
              (P.completion_property (CloneSAP.CCO.cco_forward S cco))).table.colour
                (f x) (f y) =
              Age.colourEquiv (CloneSAP.source S)
                (taggedColour (CloneSAP.source S)
                  (⟨b.val,(points x,0)⟩ : Sigma (CloneSAP.Carrier X))
                  (⟨b.val,(points y,0)⟩ : Sigma (CloneSAP.Carrier X)))) := by
  obtain ⟨a,hTri,g,hg⟩ := actual_infinite_old_mono_atom S (i := b.val)
  refine ⟨a,hTri,?_⟩
  intro n
  let e : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  let points : Fin n ↪ X b.val := e.trans g
  have hmono : ∀ x y : Fin n, x ≠ y →
      S.colour (points x) (points y) = some a := by
    intro x y hxy
    exact hg (e x) (e y) (e.injective.ne hxy)
  obtain ⟨f,hbit,hcol⟩ :=
    pure_clone_old_mono_marked_age_embeds S H C P cco b a hTri ε hε
      n points points.injective hmono
  exact ⟨points,f,hbit,hcol⟩

end
end CCO.CloneTupleGeometry
