import CCO.ExactEPGeometry.OriginalCoherentAtomTI
import CCO.ExactCRT.CanonicalTypedQuotients

/-!
# B062 C82: original-coherent current kernel exact descent

A current prefix may have many distinct named unary sorts. We DO
NOT claim arbitrary typed reverse RAW exact descent for independent
quotient kernels. In this module, the selected family is specifically
the family e_p of actual restrictions of ONE ORIGINAL full RAW-exact
equivalence E on the frozen single original symmetric sort.

For EVERY current atomic letter, the two guarded genuine
old-to-current (TP) source instances and original commutativity
give the typed intertwining equation in OriginalCoherentAtomTI.
The existing trusted ExactCRT word recursion then proves TI for
all CURRENT words, including true equality/empty words. The
accepted typed exact descent can therefore be invoked on any
E-bisaturated genuine nonempty current RAW exact relation; no
unproved quotient action, SAP or independent-kernel descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Typed intertwining of the REAL local restrictions of ONE original
exact equivalence, for every CURRENT RAW word at an actual certified
prefix. No missing atomic or hidden quotient algebra assumptions. -/
theorem original_coherent_current_word_TI
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts} (word : RawWord B.source i j) :
    CCO.ExactCRT.WordTI B.source
      (fun k => RawExact.evaluate B.source
        (originalExactCurrentKernelWords
          A B P transport base hOne E k).words) word := by
  apply CCO.ExactCRT.wordTI_of_all_atoms
  intro p q a
  have hOld :=
    original_coherent_current_atom_TI
      A B P transport tp base hOne E p q a
  have hp := originalExactCurrentKernelWords_relation
    A B P transport base hOne E p
  have hq := originalExactCurrentKernelWords_relation
    A B P transport base hOne E q
  rw [hp,hq]
  exact hOld

/-- Actual C82 direct coherent-family scope: a genuine CURRENT
nonempty exact D which is bisaturated by the actual restrictions of
a single ORIGINAL full-RAW exact E descends to one exact relation on
the already constructed NAMED-SORTED simultaneous quotient source.
The necessary TI of every word is PROVED, not an added premise. -/
theorem original_coherent_current_exact_descent
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts}
    (D : RawExact.NonemptyExact B.source i j)
    (hSat : RawExact.saturate
      (RawExact.evaluate B.source
        (originalExactCurrentKernelWords
          A B P transport base hOne E i).words)
      (RawExact.evaluate B.source D.words)
      (RawExact.evaluate B.source
        (originalExactCurrentKernelWords
          A B P transport base hOne E j).words) =
          RawExact.evaluate B.source D.words) :
    ∃ F : RawExact.NonemptyExact
      (CCO.ExactCRT.CanonicalTyped.source B.source B.homogeneous
        (originalExactCurrentKernelFamily
          A B P transport base hOne E)
        (originalExactCurrentKernelWords
          A B P transport base hOne E)
        (originalExactCurrentKernelWords_relation
          A B P transport base hOne E)) i j,
      RawExact.evaluate
        (CCO.ExactCRT.CanonicalTyped.source B.source B.homogeneous
          (originalExactCurrentKernelFamily
            A B P transport base hOne E)
          (originalExactCurrentKernelWords
            A B P transport base hOne E)
          (originalExactCurrentKernelWords_relation
            A B P transport base hOne E))
        F.words =
        CCO.ExactCRT.quotientRelation
          (CCO.ExactCRT.CanonicalTyped.projection
            (originalExactCurrentKernelFamily
              A B P transport base hOne E) i)
          (CCO.ExactCRT.CanonicalTyped.projection
            (originalExactCurrentKernelFamily
              A B P transport base hOne E) j)
          (RawExact.evaluate B.source D.words) := by
  exact CCO.ExactCRT.CanonicalTyped.typed_exact_descent
    B.source B.homogeneous
    (originalExactCurrentKernelFamily
      A B P transport base hOne E)
    (originalExactCurrentKernelWords
      A B P transport base hOne E)
    (originalExactCurrentKernelWords_relation
      A B P transport base hOne E)
    B.cco D hSat
    (fun word _ => original_coherent_current_word_TI
      A B P transport tp base hOne E word)

end
end CCO.ExactEPGeometry
