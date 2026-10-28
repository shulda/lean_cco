# B019 C27–C29 — explicit finite premise controls

Actual implementation author: `/root/b019_product/controls`.
Base: accepted main `7ccce32d991a83645816bdb6522f6ebbfa8d50f0`.
Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
This helper owns only the three new modules below and this report. It does
not modify root imports, accepted code, mathematical contracts or policy.

## C27 — fullness is essential

`CCO.Owners.Product.Controls.Fullness` uses the literal carrier
`Point = F2 × F2 × F2`, with coordinates `(owner,d,c)` and both factors
`Factor = F2 × F2`. `differenceSource` names every vector difference,
including zero. `flipDAut` is proved to be an ACTUAL automorphism of the
first factor's difference structure and fixes every owner; the second
factor action is the identity. The corresponding full-carrier permutation
`flip` is bijective and preserves both coordinate difference colours.

`full_product` and `full_coordinates_injective` prove the literal full
set-product identification. `sparse_ontoD`, `sparse_ontoC` show that the
proper four-point subset `d=c` projects onto BOTH factors. Nevertheless
`sparse_not_preserved` gives a point in that subset whose d-only flip
leaves it. `nonfull_control` assembles the exact premise-boundary consumer.
`sparse_card` and `full_card` check four and eight points respectively.
No claim is made that the nonfull subset satisfies the source theorem.

## C28 — fullness does not imply fine-colour reconstruction

On the same FULL eight-point carrier, `refinedSource` retains every
original difference predicate and adds the binary predicate
`extra x y := x.d=y.c and x.c=y.d`. The same compatible coordinate
permutation still preserves BOTH coordinate difference colours.
`extra_not_preserved` supplies the literal witness
`x=(0,0,0), y=(1,0,0)`. `flip_not_refined_aut` proves that this permutation
is NOT an actual automorphism of the refined fine structure.
`extra_colour_control` assembles full realization, both coordinate colour
identities and the actual fine-automorphism failure.
The unrefined `flipAut` is separately an actual automorphism.
No exact-readout, CCO or full-automorphism cardinality claim is asserted
for the refinement.

## C29a — prescribed point lifts do not require a section

`CCO.Owners.Product.Controls.NoSection` uses the regular multiplicative
tags of the additive groups ZMod4 and ZMod2. `rho` is the actual reduction
homomorphism, proved onto. `equivariant` proves its actual quotient-action
identity. `point_lifts` constructs the lift `y*x^-1` for EVERY compatible
point pair and EVERY prescribed quotient element. The shared accepted
`prescribed_action_point_lifting` theorem yields `onto_fibre_kernel`.

`no_homomorphic_section` excludes ALL group-homomorphic sections. It is
an algebraic argument: the image of the order-two C2 generator under any
candidate section has square one; every such C4 element has trivial C2
image, contradiction. `order_two_image` checks just the FOUR C4 elements,
not a presumed exhaustive list of candidate maps. No canonical or
coherent lift selection is introduced. This is an action control and
makes no symmetric CCO claim.

## C29b — onto C-owner action alone is insufficient

`CCO.Owners.Product.Controls.MissingPoint` uses D=F2² with all translations,
O its first bit and T its second. The stated C ACTION translates only its
first bit and fixes the second; it is explicitly not labelled the full
automorphism group of the difference language. All actions are explicit
definitions with LOCAL instances; importing this module installs no new
global concrete action instance.

The maps D->O, C->O and D->T are proved onto and equivariant. The first
factor really has the prescribed T-point property and hence onto action
with fibre-transitive kernel. `rhoC` is onto the full displayed O group,
but `c_missing_point` proves that it cannot realize the required point
request between `(0,0)` and `(0,1)` over identity O-motion.

`matchingGroup` is the LITERAL subgroup of GD×GC whose ENTIRE O-components
agree. `fullAction`, `full_D_coordinate`, `full_C_coordinate` prove its
coordinatewise action on the full product. Its map `fullTarget` is onto
ALL of T. Every matching element fixes the second C bit, so
`fullTarget_kernel_not_transitive` disproves kernel transitivity on the
actual common-T fibre containing `(0,0,0)` and `(0,0,1)`.
`complete_control` assembles the true first-factor premise, onto C-owner
and full-target actions, failure of C point lifting and failure of the
conclusion. These are explicit finite ACTION groups, not unproved full
structural automorphism identifications.

## Validation and integration boundary

Pinned Lean 4.34.1 / Lake with the locked manifest and targeted Mathlib
imports compiled all three modules successfully. Final targeted command:

```
lake build CCO.Owners.Product.Controls.Fullness \
  CCO.Owners.Product.Controls.NoSection \
  CCO.Owners.Product.Controls.MissingPoint
```

Result: SUCCESS, 1149 build jobs. The finite universal checks use Lean's
kernel-checked `decide`; there is no `native_decide`, new axiom or sorry.
The complete B019 owner supplies additive root imports, one final complete
project build and official transitive audit/current-source byte guards.
This helper does not repeat those whole-project checks or act as reviewer.

## Follow-up: C25 empty branch and actual action consumers

The same actual helper author additionally owns precisely
`CCO.Owners.Product.Empty` and `CCO.Owners.Product.ActionConsumers`.
The seven owner core modules at `605801a07956826dc5422f4816336722e7617732`
were cherry-picked locally only as dependencies; this follow-up commit
contains no modifications to those modules or root imports.

`empty_quotient_system` derives empty O, D, T and the full W directly
from empty C, the displayed maps and surjectivity of C->O and D->T.
`empty_nested_product` separately covers the optional full nested target.
`empty_actual_aut_subsingleton` and `empty_actual_aut_unique` concern the
FULL `BinaryStructure.Aut` groups, not arbitrary groups acting on empty
sets. `empty_actual_aut_hom_surjective` uses the actual target's triviality
and the source identity to prove every displayed actual automorphism
homomorphism onto. `empty_fibre_transitive` and `empty_point_requests`
are proved separately by eliminating a hypothetical empty-domain point.
`empty_actual_action_result` combines actual group surjectivity and
vacuous fibre transitivity; the nonempty point criterion is never called.
The owner retains responsibility for the direct empty EPPA consumer.

`ActionEquivalence` displays BOTH a group isomorphism and point bijection,
with their precise action compatibility. Its `transportedHom`,
`transportedMap`, commuting identities, surjectivity and
`transported_equivariant` explicitly retain the entire quotient element
and the displayed quotient action on points. `prescribed` and `onto_kernel`
transfer the corresponding generic group-action theorems through source
AND target identities. Their `*_of_commuting` variants retain any original
quotient map that makes the displayed point square commute. These are the
appropriate independent interfaces for the optional nested target A10;
a bare unnamed group isomorphism is not substituted for action data.

`ProductGeometry.fullAutActionEquivalence` is an ACTUAL constructed action
identity: its group map is the already-proved natural `P.fullAutEquiv`,
its point map is identity on the literal full carrier, and compatibility
is proved from the actual coordinate quotient homomorphism formulas.
There is no further action-compatibility provider assumption.

`ProductGeometry.actual_nonnested_onto_kernel` consumes the compiled
matching-pair result and this proved action identity to export onto action
and fibre-transitive kernel for the ACTUAL full fine-coloured automorphism
group. Its only point premises are prescribed D-to-T and prescribed C-to-O
lifting (the former is equivalent to A13 by the accepted criterion), and
its nonempty-carrier premise is retained precisely on this nonempty
branch. It needs no T-to-O map or source section. The owner instantiates
P through the actual exact-source geometry factory and assembles the
nested and empty source consumers.

Final targeted build of these TWO new consumer modules: SUCCESS,
757 jobs, pinned Lean/Lake/manifest. Their source changed after the first
local check, so only their affected dependency targets were compiled;
no complete project build or official audit was repeated by this helper.
