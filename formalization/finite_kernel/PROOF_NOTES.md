# Finite-fibre kernels and hidden finite projections — proof notes

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`. Mathematical preparation for OTHER Lean projects, not Lean proofs. The human TeX remains unchanged. This module covers the three remaining kernel/CSP/duality results and two selected entire-axis/Goursat results; the affine lemma was already prepared in `rigid_groupoid`. No CCO, exactness, SAP or symmetry is imported. Precise quantified contracts and DAG firewalls are in `module.json`.

## N01: Owner action and intrinsic local motion groups

These notes expand `thm:finite-fibre-kernel-csp`,
`cor:finite-kernel-relative-homogeneity`, and the selected neighbouring
`lem:typed-finite-entire-axis-projection` and
`cor:typed-finite-linear-goursat`. The affine translate-Helly lemma in the
same CSP source has already been prepared in `rigid_groupoid`; it is not
reproved, exported again, or needed by N01--N04. No CCO, exactness, SAP,
symmetry, transitivity or finite orbital palette is assumed here.

Let X be a structure in a RELATIONAL language of arity at most two, and
F an Aut(X)-invariant equivalence on its ENTIRE universe. Every actual
F-class is finite and nonempty; write Ccal for the set of these classes.
The language may include unary relations, directed binary relations and
binary loops. Nullary RELATION symbols are harmless fixed truth values.
Function symbols, including named constants as nullary functions, are not
part of this relational hypothesis. Equality is preserved by all the
permutations below. A named many-sorted structure can be treated using
its unary sort predicates; those predicates remain part of every induced
local structure. No finite-language assumption is required.

Put Gamma=Aut(X). Since F is invariant, gamma sends any F-class onto
another F-class, defining a homomorphism Gamma->Sym(Ccal). Its kernel N
fixes every owner/class SETWISE, while allowing arbitrary permitted
permutations of points inside it. The owners need not be named and may
move under Gamma. There is no assertion that the action maps onto all
of Sym(Ccal), and no section of its image is assumed.

For C in Ccal set H_C=Aut(X restricted to C), using the full original
language on this finite induced structure. It is a finite subgroup of
Sym(C), of size at most |C|!. For distinct C,D let H_CD consist of pairs
(h_C,h_D) in H_C times H_D whose union is an automorphism of the induced
structure on C union D, fixing C and D separately. Equivalently, besides
the already checked within-class relations it preserves EVERY ordered
cross-class binary instance in both directions. Unary instances lie
within one class; binary loops also lie within one class. Nullary
relations are unchanged by every permutation. These conditions use
equivalence of relation truth values, not merely a homomorphism condition.
The set H_CD is a subgroup: composition and inverse of the two partial
permutations correspond to composition and inverse on C union D. Swapping
the two coordinate labels gives H_DC. These intrinsic pair groups need
NOT project onto the full H_C or H_D.

For finite S subset Ccal define Sol(S) as the subgroup of the finite
product of H_C, C in S, satisfying all H_CD constraints for distinct
C,D in S. Thus Sol(empty) has one empty tuple, Sol({C})=H_C, and the
two-class solution group is H_CD under its ordered-coordinate
identification. Distinct pairs can be indexed in either order because
H_DC is the coordinate transpose of H_CD, but a directed language must
still check both ordered relation instances inside each H_CD definition.

The groups H_C and H_CD describe intrinsic induced-substructure motions.
They are not automatically the motions available from the GLOBAL
pointwise-owner kernel. Its actual coordinate and pair images will be
called B_C and P_CD below. In particular an internally possible motion
may fail because of constraints involving other classes. The fact that
the original structure is homogeneous, if it happens to be so, does not
by itself say that naming ALL moving owners preserves homogeneity.

For N01/N02, countability of X is unnecessary. It is required by the
explicit countable-tree projection proof N03. An empty universe is
allowed if the underlying convention permits it: Ccal is then empty,
Gamma and N are trivial, and every empty product below has its one
empty tuple.

## N02: Global binary patching and actual binding marginals

Define the concrete restriction homomorphism

    rho:N -> product_(C in Ccal) H_C,
    rho(n)_C = n restricted to C.

This is injective because the F-classes partition the ENTIRE universe.
The precise meaning of the source's tuple equality FC1 is the assertion
that rho is a group isomorphism onto the global intrinsic solution group

    Sol_all = {h in product_C H_C:
                         (h_C,h_D) in H_CD for all C!=D}.

One inclusion is restriction of an actual n. For the converse, take one
global family h in Sol_all and define its union permutation sigma on X:
sigma(x)=h_C(x) for the unique C containing x. The definition is unique
because classes are disjoint, and sigma is bijective because each h_C
bijects C to itself. Its inverse is the union of h_C inverse.

Check atomic relations by their complete argument tuple. A unary tuple
lies in one class and is preserved by H_C. A binary tuple either lies
in one class, including a repeated point, or lies in two distinct classes;
it is preserved respectively by H_C or H_CD. The latter check includes
both orientations in a nonsymmetric language. Nullary truth values do
not depend on the map. Arity at most two exhausts all relation instances,
so sigma and its inverse preserve the structure. Thus sigma belongs to
Gamma and fixes every class setwise, hence sigma is in N. The union map
is inverse to rho, and it respects coordinatewise group composition.
No topology or compactness is used for this global patching step.

The entire-universe premise matters: there are no unassigned points or
additional sorts outside the partition whose binary interactions could
obstruct this union. This is different from prescribing motions merely
on some selected finite sorts and asking a larger automorphism group
for an extension.

From now on use rho to identify N with its concrete tuple image when
writing projections. Define

    B_C=pr_C(rho(N)),
    P_CD=pr_(C,D)(rho(N)) <= B_C times B_D.

They are finite subgroup images. We have B_C<=H_C and P_CD<=H_CD. For
each b_C in B_C there is an actual n realizing it; its D-coordinate
provides a partner in P_CD. The same holds for each b_D. Therefore P_CD
is subdirect over the ACTUAL B_C,B_D, even when the intrinsic H_CD is
not subdirect over H_C,H_D.

The source's FC3 is also a concrete equality after rho:

    rho(N) = {b in product_C B_C:
                         (b_C,b_D) in P_CD for all C!=D}.

The forward inclusion is immediate. For the reverse, B_C<=H_C and
P_CD<=H_CD put any tuple on the right in Sol_all, and the global patching
isomorphism makes it rho(n) for a unique actual n. This does not require
independently selected witnesses n_CD for different pairs to agree.
Their existence is used only to certify each intrinsic binary constraint;
the global family b itself supplies the coherent pointwise union.

This GLOBAL pair description does NOT assert that a finite projection
pr_S(N) equals the set satisfying only the pairs among S, whether those
pairs use H_CD or actual P_CD. An unselected class can constrain three
or more surviving coordinates after elimination. N03 gives the exact
finite-projection condition: extension must exist over EVERY finite
superset. A separate homogeneity hypothesis will remove this obstruction
in N04. No intrinsic-binding equality B_C=H_C has been proved here.

## N03: Countable compact projection by an explicit finite tree

Now assume the carrier X is countable, retaining finite F-classes. The
class set Ccal is at most countable: fix a coding of points by natural
numbers and assign each nonempty class its least point code. This gives
an injection of the classes into Nat. No countability of the relational
language is needed; each H_C remains a subset of the finite Sym(C).

Fix a finite S subset Ccal and ONE tuple g in product_(C in S) H_C.
The statement to prove is precisely

    g in pr_S(rho(N)) iff
      for every finite T with S subseteq T subseteq Ccal,
      there exists h in Sol(T) with h restricted to S equal to g.

The containment of S in T is NONSTRICT and includes T=S. Thus the right
side already forces g in Sol(S). The boundary tuple g is the same in
every extension request. The witnesses h_T need not initially be
compatible; one must not simply take their union. Nor does checking only
T of some bounded size, or just all pairs inside S, express this condition.

An actual n supplies the required restriction on every T, proving
necessity. If Ccal is finite, take T=Ccal in the hypothesis and apply
the global patching isomorphism to that solution. This handles Ccal empty
as well. If S is empty, its unique tuple extends by the identity on all
classes; both sides of the equivalence hold.

For the remaining infinite case enumerate Ccal minus S without repetitions
as C_0,C_1,... and put T_n=S union {C_0,...,C_(n-1)}. Then T_0=S and
these finite sets exhaust all classes. Let L_n be the finite set of
solutions on T_n extending g. Each L_n is nonempty by the hypothesis
and finite because it is a subset of a finite product of finite H_C.
Every node h in L_(n+1) restricts to a node of L_n, since pair constraints
are hereditary under restriction. The root level L_0 consists exactly
of g.

Here is the full finitely-branching-tree argument, without importing
Konig's lemma. Call a node h in L_n infinitely continuing if for EVERY
m>=n it has an extension in L_m. The root is infinitely continuing
because every level is nonempty and all levels restrict to g. A node
has only finitely many immediate children, since the next coordinate
belongs to the finite group H_(C_n). An infinitely continuing node must
have an infinitely continuing child. Otherwise, for each of its finitely
many children choose a level at which that child has no extension.
Once extension fails at one level it fails at every later level, by
restriction. Taking the maximum of these finitely many levels would
give a level at which no child, and hence not the parent, can extend,
contrary to infinite continuation. The possibility of no children is
already excluded by extension to level n+1.

Recursively choose an infinitely continuing child, starting from g.
This gives h_n in L_n with h_(n+1) restricted to T_n equal to h_n.
For a deterministic choice one can order each finite class by its point
codes, then its finite permutation group and each finite child set, and
choose the first infinitely continuing child. Ordinary recursion on Nat
then gives the branch. There is no external compactness, topological
product theorem or unproved tree lemma in this step.

For each C let h_C be its value at any level containing C. The branch
compatibility makes this independent of the level. Every h_C belongs to
H_C. Given two distinct classes C,D, choose a level containing both;
its solution verifies (h_C,h_D) in H_CD. The union family therefore lies
in Sol_all, and N02 gives its unique actual n in N. All levels extend
the same g, so pr_S(rho(n))=g. This proves sufficiency with the exact
quantifiers of FC2.

Finiteness of individual classes supplies the finite branching. Countable
enumerability supplies the sequence of levels. The global patching theorem
N02 itself has neither restriction, apart from those already needed to
define local maps; the present proof does not claim that its tree argument
works for an uncountable collection. One could obtain other generalizations
with additional compactness principles, but none is imported or asserted
here. In the countable source with finite classes, an infinite carrier
necessarily has infinitely many classes; the finite-class-set case has
already been handled directly.

## N04: Relative homogeneity and entire named finite sorts

First expand X by a separate unary predicate naming EACH actual F-class,
and call the resulting structure X^own. Its full automorphism group is
exactly N: preserving all these predicates means fixing every owner
setwise, in addition to preserving the old structure. This equality does
not say that X^own is homogeneous. Explicitly assume that extra property
for `cor:finite-kernel-relative-homogeneity`.

Let S be finite and h in Sol(S). Its union is a permutation of the finite
induced set U_S=union_(C in S) C. The unary/binary checks in N02 show it
is an induced partial isomorphism in the original language. It preserves
all new owner predicates as well: each selected class maps to itself,
and predicates for unselected classes are false on the whole domain and
range. Homogeneity of X^own extends this partial map to an element of
Aut(X^own)=N. Thus pr_S(rho(N))=Sol(S). The reverse inclusion is always
restriction. S empty uses the empty partial map, which has the identity
extension. Singleton and two-class choices give B_C=H_C and P_CD=H_CD.
Consequently the intrinsic pair groups become subdirect here, as a
CONCLUSION of this extra hypothesis, not as a premise of the general CSP.

Only finite-domain homogeneity is used in this argument, so countability
is not needed for this conditional corollary. Finite classes and finite
S are needed to make U_S finite. Naming moving classes in a homogeneous
original X can destroy homogeneity, so the premise must not be silently
inherited from the reduct. Without it, the smaller actual binding images
and higher-arity eliminated constraints remain possible.

Now select `lem:typed-finite-entire-axis-projection`. This is a distinct
setup: X is a homogeneous relational structure of arity at most two with
pairwise disjoint NAMED entire finite sorts P_i, i in I. Other named sorts
can be infinite, and the P_i need not exhaust X. Put Gamma=Aut(X),
R_i=Aut(X restricted to P_i), and let P_ij be the ACTUAL image of Gamma
on R_i times R_j. This P_ij is not an arbitrary intrinsic pair constraint.
Use the full automorphism group of X, not a possibly proper image of an
earlier finer source group in Aut(X). No symmetry, transitivity, SAP, CCO,
exactness or countability is needed for this finite extension argument.

Every automorphism of the finite induced P_i is a finite partial
isomorphism of X and preserves its named sort predicates. Homogeneity
extends it, so Gamma->R_i is onto. It follows that P_ij is subdirect.
For finite S, any actual Gamma restriction satisfies every P_ij condition.
Conversely, let g_i in R_i, i in S, satisfy (g_i,g_j) in P_ij for all
i!=j. The union g is a bijection of the FINITE induced union P_S. It
preserves within-sort relations by R_i, and for each pair of different
selected sorts an actual gamma_ij realizes its restriction on the WHOLE
P_i union P_j. Thus every cross-sort binary relation instance, in both
orientations, is preserved. Unary predicates and binary loops have already
been checked within sorts; nullary relation values are automatic. There
are no relation instances using three distinct classes because arity is
at most two. Hence g is a finite partial automorphism of X. Homogeneity
extends it to an actual gamma realizing the entire tuple. We have proved

    image(Gamma -> product_(i in S) R_i)
      = {g: (g_i,g_j) in P_ij for all distinct i,j in S}.

For S empty both sides have one empty tuple; for a singleton this is the
coordinate surjectivity just proved. If empty named sorts are allowed by
the ambient convention, their R_i are trivial and cause no exception.
The statement concerns FINITE S only. Homogeneity supplies interactions
with the unselected universe; a pointwise-owner kernel which is merely
a proper subgroup of this full Gamma cannot be substituted for it.

Also select the closely connected `cor:typed-finite-linear-goursat`. Assume
R_i are elementary abelian and choose coordinates V_i=F2^(d_i). Each
P_ij is then a linear subspace of V_i direct-sum V_j, subdirect on both
factors. Define

    N_i={x in V_i:(x,0) in P_ij},
    N_j={y in V_j:(0,y) in P_ij}.

They are vector subspaces. There is a canonical linear isomorphism
theta:V_i/N_i -> V_j/N_j: given x, choose y with (x,y) in P_ij and
send x+N_i to y+N_j. Two choices of y differ by N_j. Changing x by N_i
does not change the target coset. Subspace closure proves linearity.
If the target coset is zero, subtracting the pair (0,y) shows x belongs
to N_i, proving injectivity; subdirectness onto V_j proves surjectivity.

Take W_ij=V_i/N_i, pi_ij the quotient map from V_i, and
rho_ij=theta inverse composed with the quotient map from V_j. These maps
are surjective and linear. A pair in P_ij has pi_ij(x)=rho_ij(y).
Conversely, if this equality holds, choose y' with (x,y') in P_ij.
Then y-y' belongs to N_j, and adding (0,y-y') to that pair gives
(x,y) in P_ij. Therefore

    P_ij={(x,y):pi_ij(x)=rho_ij(y)}.

Choose an orientation for every unordered pair in a finite S and define
the linear map Phi_S from direct-sum_(i in S) V_i to
direct-sum_({i,j} in [S]^2) W_ij by the components
pi_ij(x_i)+rho_ij(x_j). Characteristic two makes vanishing equivalent
to equality of the two quotient coordinates. The entire-axis theorem
therefore identifies the ACTUAL finite Gamma image with ker(Phi_S).
Finite-dimensional rank-nullity yields

    |image(Gamma on S)|=2^(sum_(i in S) d_i-rank(Phi_S)).

The exponent is nonnegative by the rank bound. For empty S the domain
and codomain are zero spaces and the image size is one. For singleton
S the check space is zero and the image is all V_i. Zero-dimensional
individual V_i or W_ij simply give trivial factors or vacuous pair tests.
No linear coordinates or quotient isomorphisms are claimed canonical
beyond the specified constructions.

Finally suppose the actual pair groups on three distinct entire finite
named sorts are graphs of group isomorphisms theta_ij, theta_jk, theta_ik.
This flat-transport argument does not require the groups elementary
abelian. Given x in R_i, coordinate surjectivity supplies ONE actual
gamma in Gamma with gamma_i=x. Its simultaneous restrictions satisfy
gamma_j=theta_ij(x), gamma_k=theta_ik(x), and also
gamma_k=theta_jk(gamma_j). Thus theta_ik=theta_jk composed with theta_ij
for every x. The argument uses actual full-group coordinate lifting,
not independently chosen pair witnesses which might be inconsistent.

These selected entire-axis results do not include the subsequent theorem
applying them to a homogeneous exact quotient source; that source
inheritance remains a separate provider. They say nothing about a finer
source image being the full quotient automorphism group, and give no
automatic strong projection for unnamed moving fibres or for an owner
expansion whose homogeneity has not been proved.

## N05: Finite local subgroup equations and global annihilator

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`. This expands `thm:finite-kernel-linear-width-two` in `sections/finite_packet_kernel_constraints.tex`. The preceding affine-translate lemma is already a selected export of `rigid_groupoid` and is not a provider for this linear proof.

Use the original binary-structure setting: X has a relational language of arity at most two, F partitions its entire universe into finite nonempty invariant classes C, Gamma=Aut(X), and N is the kernel of the induced action on the set of these classes. Owners need not be named or individually fixed by Gamma. For each class C, H_C is the FULL intrinsic group Aut(X restricted to C). Assume each H_C is elementary abelian and identify it with a finite F2-vector space V_C. For C!=D, H_CD is the subgroup of H_C times H_D whose union preserves all induced relations on C union D while fixing the two fibres separately. It need not be subdirect. All these groups refer to actual finite induced structures, not hypothetical motions inferred from quotient names.

The elementary binary patching result established earlier gives

    N = {x in product_C V_C : (x_C,x_D) belongs to H_CD for all C!=D}.

Its proof assembles the fibre permutations to a bijection of the entire universe and checks unary and binary relations within one fibre or across a pair. It requires neither countability nor homogeneity, CCO, SAP, exactness, compactness or extension of partial automorphisms. We use this global identity, not the separate compact finite-projection theorem.

Write V_C^* for the finite linear dual, and D=direct_sum_C V_C^* for finitely supported families of tests. Distinguish D, the test space, from any particular owner named D in N07. For x in the FULL product of the V_C and ell in D, define the pairing <ell,x>=sum_C ell_C(x_C); it is finite because ell has finite support. For W subset D let W^perp be its common zero set in the full product; for Y subset the product let Ann(Y) be the subspace of D vanishing on Y.

Each local H_CD is an F2-linear subspace of the finite space V_C times V_D. It is the common kernel of its annihilator tests. A complete elementary proof is finite separation: for z outside a subspace H, the formula f(h+epsilon*z)=epsilon is well-defined and linear on H+<z>; adjoin vectors outside its current domain until it extends to the finite ambient space. The resulting test vanishes on H and takes value one on z. Conversely every vector of H is killed by every annihilator test. Choosing a finite basis of the local annihilator gives a finite complete defining family if desired; taking all such tests is equally valid.

Embed these local tests into D with support contained in {C,D}, and let R be their algebraic linear span. A one-coordinate row is permitted ONLY when it is a true local defining equation, for instance a restriction implicit in a non-subdirect H_CD. Do not add freely chosen unary restrictions to R: they would change the asserted N. The within-fibre conditions have already been included by taking V_C=H_C as the entire intrinsic group. There is no separate assumption that actual one-owner motions equal V_C. If there is just one fibre and no pair constraints, then R=0 and N=V_C.

Every tuple in N kills all local rows and hence their span. Conversely a tuple killing R satisfies every complete local defining system, so lies in all H_CD and hence in N by binary patching. Therefore N=R^perp. This part is valid without countability and uses no double-annihilator theorem.

For the double-annihilator direction give the following explicit countable proof. The pinned source has countable X, hence at most countably many finite fibres. Each V_C^* is finite, so its direct sum D is countable: enumerate the fibres, then enumerate all tests supported among each initial finite set. Finite D may be enumerated with repetitions, and D always contains zero. The only use of countability in the linear argument is this functional extension step. An uncountable analogue would need a separately justified extension principle; none is silently imported here.

Fix ell not in an arbitrary subspace R of D. On W_0=R+<ell> define f_0(r+epsilon*ell)=epsilon. The decomposition is unique because ell is not in R, so this is linear, zero on R and one on ell. Enumerate D as d_0,d_1,... . Given f_n on W_n, if d_n already lies in W_n, leave both unchanged. Otherwise put W_(n+1)=W_n+<d_n> and define f_(n+1)(w+epsilon*d_n)=f_n(w), choosing value zero on the newly added vector. The decomposition is unique, so this is a consistent linear extension. The union domains exhaust D; the union functions form a linear f:D->F2, with f(R)=0 and f(ell)=1. No Zorn lemma, Hahn--Banach theorem, topological closure or compactness is needed.

Now explicitly identify this functional with an actual PRODUCT tuple. Restrict f to the coordinate injection of V_C^*; this gives f_C in V_C^{**}. Conversely any family of such f_C defines f on D by the finite sum sum_C f_C(ell_C). These two constructions are inverse, proving

    Hom(D,F2) = product_C V_C^{**}.

For a finite vector space V with basis e_1,...,e_d and coordinate dual basis e_1^*,...,e_d^*, every L in V^{**} equals evaluation at the UNIQUE vector v=sum_i L(e_i^*) e_i. Indeed each phi is sum_i phi(e_i)e_i^*, so L(phi)=sum_i phi(e_i)L(e_i^*)=phi(v); uniqueness follows by testing the coordinate forms. The zero-dimensional case has its unique zero vector. This proves finite biduality directly rather than citing it. Thus f corresponds to one actual tuple x in product_C V_C with f(ell)=<ell,x> for every finite-support test.

For the separating f, this tuple x kills R but not the selected ell. Hence every ell outside R lies outside Ann(R^perp). The reverse inclusion is immediate from the definition, so

    Ann(R^perp)=R.

It is essential to use the FULL product of intrinsic V_C here, not its direct sum and not a prematurely substituted product of actual binding groups B_C. With the local defining R, the equation N=R^perp subsequently ensures that the separating tuple is an actual global kernel motion.

All boundary cases are harmless. For no fibres, D is zero, the product and N have one identity tuple, and R=0. Trivial individual H_C give zero-dimensional coordinates. If R=0, R^perp is the whole product and its annihilator is zero. If R=D, R^perp is the identity tuple and its annihilator is D. A separating ell is never needed when no ell outside R exists. None of these statements licenses arbitrary nonvalid unary rows in the one-fibre case.

## N06: Restricted annihilator and width-two equivalence

Let S be a FINITE set of actual fibre classes. Put V_S=product_(C in S) V_C and identify D_S=direct_sum_(C in S) V_C^* with the subspace of D supported in S. Its pairing with V_S is the finite-dimensional dual pairing just proved. Restriction of the pairing gives, for ell in D_S,

    ell vanishes on pr_S(N)
      iff ell vanishes on N
      iff ell belongs to R.

Thus Ann(pr_S N)=R intersect D_S. This is the precise restricted annihilator identity in `eq:finite-kernel-dual`. By finite separation/biduality, pr_S N is the common kernel inside V_S of those restricted rows. No compact finite-projection formula or owner-homogeneity hypothesis has been invoked.

Keep three different kinds of groups distinct. The intrinsic H_C=V_C is given by the finite induced structure. The ACTUAL binding group B_C=pr_C(N) is a subspace of V_C and may be strictly smaller. The ACTUAL pair image P_CD=pr_(C,D)(N) is a subspace of B_C times B_D, subdirect over those actual B's by definition. It can be smaller than the intrinsic local H_CD. Never replace B_C by V_C or P_CD by H_CD without a separately proved extension theorem.

For finite S define

    M_S={x in product_(C in S) B_C :
         (x_C,x_D) in P_CD for every distinct C,D in S}.

Equivalently, M_S is the intersection over all T subset S with |T|<=2 of the inverse images under pr_T of pr_T(N). Singleton tests express actual B_C membership, and two-coordinate tests express actual P_CD membership. The empty test imposes no condition. This reformulation is important for S of size zero or one; one must not simply drop the unary actual-binding conditions.

Let W_S be the span INSIDE D_S of all subspaces R intersect D_T for T subset S, |T|<=2, using the natural zero-extension embeddings. The restricted identity just proved and finite separation imply that pr_T(N) is exactly the common zero set of R intersect D_T in V_T. Consequently

    M_S = W_S^perp inside V_S,
    Ann(M_S)=W_S.

One can check this directly: a tuple satisfies every marginal test precisely when it kills every row in every listed R intersect D_T, precisely when it kills their span. Finite biduality gives the second equality. This avoids any unproved interchange of annihilators with arbitrary infinite intersections.

The actual finite projection pr_S(N) is contained in M_S, so W_S is contained in R intersect D_S. Finite-dimensional separation now proves

    pr_S(N)=M_S
      iff Ann(pr_S N)=Ann(M_S)
      iff R intersect D_S=W_S.

This is exactly `eq:finite-kernel-width-two`. Its rows of support at most two are the true MARGINAL rows R intersect D_T, not merely the original H_CD rows whose coordinate names happen to lie in S. Eliminating outside fibres can create new unary or pair rows as well as rows of higher width. Taking the algebraic span R before intersecting D_S is therefore essential.

For S empty, V_S is the singleton identity tuple, D_S=0, both projection sets coincide and both row spaces are zero. For a singleton, M_S=B_C is its actual projection, and the width-two family already includes D_S's whole restricted row space. For |S|=2, M_S is the actual P_CD and the equality is again automatic. Genuine hidden-projection obstructions can first occur on three surviving fibres. This finite equality is distinct from the GLOBAL representation of N by actual one- and two-coordinate images, which always follows from the original binary patching theorem. A global pair description can hold while an individual finite projection has additional constraints.

## N07: Hidden parity and owner-homogeneity firewall

This expands `rem:finite-kernel-hidden-parity` using an actual finite canonical binary countermodel, not an asserted homogeneous or exact CCO source. Take four NAMED disjoint fibres A=B=C=F2 and Z=F2^2 (Z is the source remark's owner called D). Let the group G=F2^2 act by shifts

    (u,v): a -> a+u,  b -> b+v,
           c -> c+u+v,  z -> z+(u,v).

Use the finite relational structure naming these four fibres and EVERY actual ordered-pair G-orbital. The equivalence whose classes are the four fibres is invariant, and since the fibres are named every automorphism fixes them individually. The action is faithful and each fibre is transitive. These observations do not imply homogeneity of the canonical binary structure.

The intrinsic automorphism group on each of A,B,C is its two-element translation group: its binary palette is equality and inequality. On Z, the pair orbitals are the four exact vector differences. A permutation preserving those differences has z->z+w for one common w, so H_Z is its four-element translation group. Hence the intrinsic groups are V_A=V_B=V_C=F2 and V_Z=F2^2, all elementary abelian.

Between A and B there is just one G-orbital, because (u,v) acts transitively on all four ordered pairs. The same holds between A,C and B,C: (u,u+v) and (v,u+v) range over F2^2. Between A and Z, orbitals are distinguished by a+z_1; between B and Z by b+z_2; between C and Z by c+z_1+z_2. Together with the intrinsic translation description, preservation of these named cross orbitals forces an automorphism's shifts to satisfy

    alpha=delta_1,  beta=delta_2,  gamma=delta_1+delta_2.

Conversely these equalities are precisely the displayed G-action, which preserves all named orbitals. Thus the FULL automorphism group of the canonical binary structure is exactly G, not merely a group contained in a possibly larger automorphism group. Its pointwise-owner kernel is N=G.

The three displayed equations are complete local pair equations, supported respectively on {A,Z},{B,Z},{C,Z}. Their span R has dimension three in the five-dimensional test space. Eliminating Z adds all three rows and produces alpha+beta+gamma=0. Precisely,

    R intersect D_{A,B,C} = span(alpha+beta+gamma),
    R intersect D_T = 0 for every T subset {A,B,C}, |T|<=2.

For verification, cancellation of the Z_1 and Z_2 coefficients requires the three row coefficients to be equal; they are either all zero or all one. Thus the width-two span on A,B,C is zero but its full restricted row space is not. All actual one-fibre B's equal the intrinsic V's in this example, and all actual pair marginals among A,B,C are unrestricted. Nevertheless their three-coordinate projection is the four-element even-parity subgroup, rather than all eight bit triples. This isolates a pure eliminated-coordinate obstruction even without a B_C versus V_C discrepancy.

There is an explicit nonextendible finite binary partial isomorphism. On the induced union of the WHOLE fibres A,B,C, flip each bit. Each intrinsic relation is preserved and every binary relation between these three distinct fibres is unrestricted, so this is a partial isomorphism preserving the named owner predicates. It cannot extend to a global automorphism: alpha=beta=gamma=1 contradicts gamma=alpha+beta. Flipping only A while fixing B and C is another odd-parity nonextendible map on the same whole three fibres. Even the map on three chosen zero points, one from each of A,B,C, to their respective one points is already a nonextendible partial isomorphism. Therefore this finite canonical binary structure, including its owner-named version, is NOT homogeneous. It is a diagnostic of the general projection theorem's limits; it is not claimed to have CCO, SAP or an exact quotient presentation.

A second, separate diagnostic is a GENUINELY HOMOGENEOUS moving-owner source; it is a new sidecar counterexample, not an additional numbered source export. Let X be the six-element set G=S3. For every g in G name the directed binary relation R_g(x,y) iff y=xg, treating R_e as actual equality if desired. A nonempty finite partial isomorphism f preserves x_0^{-1}y for one fixed domain point x_0, so

    f(y)=f(x_0) x_0^{-1} y.

It extends to the left translation by f(x_0)x_0^{-1}; the empty map extends by identity. Thus X is homogeneous and its FULL automorphism group is the left regular S3 action. These are actual directed binary orbitals; no symmetry assumption is needed in this finite-kernel module.

Fix H=<h> for a transposition h and let F(x,y) mean x^{-1}y in H. The three F-classes are the two-point left cosets xH. Their partition is invariant and definable as equality union R_h, but the individual classes move under left translations. The pointwise-owner kernel is core_G(H), the intersection of all three conjugate order-two subgroups, and is trivial. Each induced class nevertheless has intrinsic H_C=C2: its nontrivial permutation swaps its two points and preserves the unique off-diagonal colour h. Thus every actual B_C is trivial and strictly smaller than intrinsic V_C=H_C.

For distinct classes C=xH and C'=yH, a local pair permutation preserving all induced relations extends, by the explicit partial-isomorphism formula, to one left translation. If it preserves both classes, its translating element lies in xHx^{-1} intersect yHy^{-1}. These conjugates are distinct: the normalizer of a transposition subgroup in S3 is that subgroup, so equality would force xH=yH. Distinct order-two subgroups have trivial intersection. Hence H_CC' is trivial. Its legitimate defining equations include the separate unary restrictions on both intrinsic shift coordinates. These are valid local pair equations, illustrating exactly the unary-row scope in N05, rather than freely imposed global cuts. With all three owners present R is the whole three-dimensional test space and N is its zero tuple.

After naming EACH owner class by a unary predicate, the full automorphism group becomes the trivial N. The nontrivial flip of one WHOLE two-point class is still an induced partial isomorphism of this named expansion: it preserves all predicates and all binary relations on its domain. It has no global extension. Consequently naming moving owner classes can destroy homogeneity even when the ORIGINAL reduct was genuinely homogeneous. This countermodel makes no CCO, SAP or exact-source claim. It also does not refute the whole-original-axis extension theorem, whose named homogeneous source hypothesis is absent after the owner naming.

The stronger equality pr_S(N)=Sol(S), using the intrinsic local H_CD, requires relative owner homogeneity as in `cor:finite-kernel-relative-homogeneity`. If the expansion naming EVERY finite fibre by its own unary predicate is homogeneous, a local assignment on a finite union of ENTIRE fibres is a finite induced partial isomorphism and extends to an automorphism fixing all fibres. Then B_C=H_C and P_CD=H_CD, and every finite intrinsic local solution extends. Neither equality follows merely by adding those predicates to an already homogeneous source: reduct homogeneity need not survive an expansion by all owner names. In the four-fibre parity model the owner predicates were already present and failure is direct; in the S3 model adding them destroys the original homogeneity.

For an independently homogeneous binary structure with finitely many finite original named sorts, a union of entire such sorts gives the same extension mechanism; this is the scope of `lem:typed-finite-entire-axis-projection`. A partial subset of a finite fibre is not the entire-sort hypothesis. Likewise a finite collection of moving owner classes inside an infinite original sort is not automatically a collection of original finite named sorts with the required homogeneous owner expansion. Do not transfer the whole-axis projection theorem to that situation without its own proof.

Finally, an actual finer-source owner kernel, an intrinsic induced-fibre automorphism group, the full automorphism group of a quotient binary structure, and the image of an old ambient action are different objects. N05--N06 compare the first two only through their explicitly defined B_C and H_C. Naming owners, having full exact quotient kernels, or invoking phase-seed pairwise consistency from `rigid_groupoid` does not identify these groups. More specific homogeneous SAP+CCO asymmetric-cut examples belong to their own source proofs; this finite parity control is not a proof or disproof of those extra geometric assertions. It supplies no new CCO, SAP, exact descent or arbitrary owner-lifting theorem.
