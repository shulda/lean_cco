import CCO.TransitionClosure.OriginalPositiveWordHelly
import CCO.TerminalLattice.SameJAtomSaturation

/-!
# B049 source07 C11: original positive menu J-sandwich saturation

B050 proved actual same-J RAW/STRONG saturation for EACH
genuine ORIGINAL fine diversity atom. This module extends that
one-atom result to an ARBITRARY original same-sort fine menu P,
by extracting the real middle atom in each witnessed triangle.

The identity-inclusive RAW sandwich is J ; P ; J, with both
outer J occurrences permitted to be logical equality.
The resulting STRONG menu is J^circ star P star J^circ, with all
three letters actual diversity. The original nonzero J plus
homogeneous AgeSAP is the ONLY source assumption; no CCO,
positive-word/PC exactness, quotient/hidden SAP or invented
positive STRONG identity is required.

The next first-hit lemma will instantiate P with one actual
positive typed old endpoint-word profile and identify the
J-bisaturated RAW relation with the full old diversity
preimage of its genuine original J-quotient relation.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- The true OLD original same-sort RAW J ; P ; J relation with
logical equality allowed at each exterior J step, but an actual
diversity OLD fine atom at its central P step. -/
def originalRawJMenuSandwich
    {i : ι} (J : ColourEq S i) (P : S.Menu i i) :
    X i → X i → Prop :=
  fun x y => ∃ u v : X i,
    J x u ∧ S.menuRel P u v ∧ J v y

/-- SOURCE07 C11 original J-saturation for ANY old fine menu P:
the diversity restriction of TRUE equality-inclusive RAW
J ; P ; J equals the genuine THREE-LETTER STRONG product
J° star P star J°, not a RAW unital positive identity.

Proof is by real old atom decomposition of P and accepted
B050's SAP-based original same-J *atom* saturation, retaining
all sorts and actual pinned fine endpoint colours.

No semantic CCO, quotient-SAP, terminality, FULL-cover,
positive-word reachability, MI or exact-domain product is used. -/
theorem original_raw_J_menu_J_guard_eq_strong
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (P : S.Menu i i) :
    S.diversityGuard (originalRawJMenuSandwich S J P) =
      S.product (originalEquivDiversityPalette S J)
        (S.product P (originalEquivDiversityPalette S J)) := by
  classical
  let D : S.Menu i i := originalEquivDiversityPalette S J
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨x,y,⟨u,v,hJxu,hMenu,hJvy⟩,hCol⟩ := hc
    obtain ⟨t,ht,hAtom⟩ := hMenu
    have hSingle :
        c ∈ S.diversityGuard (originalRawJSandwich S J t) :=
      ⟨x,y,⟨u,v,hJxu,hAtom,hJvy⟩,hCol⟩
    rw [original_raw_J_atom_J_guard_eq_strong S H sap J hJ t] at hSingle
    obtain ⟨a,ha,b,hInner,hOuter⟩ := hSingle
    obtain ⟨middle,hMiddle,bLast,hLast,hTriangle⟩ := hInner
    have hMiddleEq : middle = t := Set.mem_singleton_iff.mp hMiddle
    subst middle
    exact ⟨a,ha,b,⟨t,ht,bLast,hLast,hTriangle⟩,hOuter⟩
  · intro c hc
    obtain ⟨a,ha,b,hInner,hOuter⟩ := hc
    obtain ⟨t,ht,k,hk,hTriangle⟩ := hInner
    have hSingle :
        c ∈ S.product D
          (S.product ({t} : S.Menu i i) D) :=
      ⟨a,ha,b,⟨t,by simp,k,hk,hTriangle⟩,hOuter⟩
    rw [← original_raw_J_atom_J_guard_eq_strong S H sap J hJ t] at hSingle
    obtain ⟨x,y,⟨u,v,hJxu,hAtom,hJvy⟩,hCol⟩ := hSingle
    exact ⟨x,y,⟨u,v,hJxu,⟨t,ht,hAtom⟩,hJvy⟩,hCol⟩

end CCO.TransitionClosure
