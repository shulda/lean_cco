import CCO.TransitionClosure.OriginalSAPFunctionalRigidity

/-!
# B049 source07 C24-C30: converse-functional original RAW relations collapse only to OLD identity

An ORIGINAL invariant R:a→b with equality source kernel
R;Rᵒᵖ ⊆ Id_a has at most one source predecessor of each real
target y. Apply original age SAP to the reversed typed relation
Rᵒᵖ:b→a: it is a real functional invariant relation, and therefore
every R-edge must be the LITERAL same-original-sort diagonal.
There is no unproved equality of a transported target kernel,
no hidden quotient SAP or CCO and no artificial STRONG unit.

This is the separate converse direction of the original-source
no-real-algebraic-transition lemma; the prior nonidentity-target
argument instead concerned E>Id and E^R=Id.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

/-- C24-C30: an old invariant R whose literal RAW
R ; Rᵒᵖ is contained in TRUE ORIGINAL equality must have
only real identity edges. This is proved by applying the
old-SAP functional rigidity theorem to the REVERSED typed
relation, not by identifying R with an unproven quotient map. -/
theorem original_SAP_converse_kernel_identity_edges
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (R : QuotientTransport.Rel (X i) (X j))
    (hInvariant : QuotientTransport.Invariant (G := G) R)
    (hKernel : ∀ x z : X i,
      QuotientTransport.compose R (QuotientTransport.converse R) x z →
        x = z)
    (x : X i) (y : X j) (hR : R x y) :
    (⟨i,x⟩ : Sigma X) = ⟨j,y⟩ := by
  have hConverseInvariant :
      QuotientTransport.Invariant (G := G)
        (fun (b : X j) (a : X i) => R a b) := by
    intro g b a h
    exact hInvariant g a b h
  have hConverseFunctional :
      ∀ b : X j, ∀ a c : X i, R a b → R c b → a = c := by
    intro b a c hab hcb
    exact hKernel a c ⟨b,hab,hcb⟩
  exact (original_SAP_invariant_function_edge_is_identity
    S H sap (fun (b : X j) (a : X i) => R a b)
    hConverseInvariant hConverseFunctional y x hR).symm

/-- Source original converse-functional exact identity gate:
on ONE actual original sort, any nonempty G-invariant RAW
relation whose R;Rᵒᵖ has only equality pairs is literally
the OLD identity relation. Seriality comes from the ACTUAL
original homogeneous transitive sort, not from quotient SAP. -/
theorem original_SAP_converse_kernel_identity_same_sort
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (R : QuotientTransport.Rel (X i) (X i))
    (hInvariant : QuotientTransport.Invariant (G := G) R)
    (hNonempty : ∃ x y : X i, R x y)
    (hKernel : ∀ x z : X i,
      QuotientTransport.compose R (QuotientTransport.converse R) x z →
        x = z) :
    R = (fun x y : X i => x = y) := by
  have hSerial : QuotientTransport.Serial R :=
    (QuotientTransport.serial_coserial_of_invariant
      R hInvariant hNonempty
      (S.original_sort_transitive_of_homogeneous H i)
      (S.original_sort_transitive_of_homogeneous H i)).1
  funext x y
  apply propext
  constructor
  · intro hR
    have hTagged :=
      original_SAP_converse_kernel_identity_edges
        S H sap R hInvariant hKernel x y hR
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hTagged
  · intro hEq
    subst y
    obtain ⟨z,hR⟩ := hSerial x
    have hTagged :=
      original_SAP_converse_kernel_identity_edges
        S H sap R hInvariant hKernel x z hR
    have hxz : x = z := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hTagged
    rwa [← hxz] at hR

/-- A nonempty original RAW cross-sort relation can NEVER
have an equality-only source kernel under original SAP.
Different named original sorts cannot be identified by
an invariant real functional inverse. -/
theorem original_SAP_converse_kernel_no_cross_sort
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (hNe : i ≠ j)
    (R : QuotientTransport.Rel (X i) (X j))
    (hInvariant : QuotientTransport.Invariant (G := G) R)
    (hKernel : ∀ x z : X i,
      QuotientTransport.compose R (QuotientTransport.converse R) x z →
        x = z) :
    ¬ ∃ x : X i, ∃ y : X j, R x y := by
  rintro ⟨x,y,hR⟩
  exact hNe (congrArg Sigma.fst
    (original_SAP_converse_kernel_identity_edges
      S H sap R hInvariant hKernel x y hR))

end CCO.TransitionClosure
