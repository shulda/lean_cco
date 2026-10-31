# B052 — typed unary terms and canonical returns

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Ten definitions, 39 human claims, four source10 results, QT-NF and six
implementation tasks. This is human proof preparation, with no Lean theorem
or external HN/HKN receiving binding claimed.

## N01: Actual coordinate objects and consistent root signatures

**D01, D06; C01–C05.** All quotient objects are literal interpreted objects:
`B_(a,J)` is the set of actual J-classes of the named original sort a.
Every represented coordinate in this signature has Id<J<Top. Upward maps
send a class to the containing coarser class. A transition for a nonempty
actual relation R satisfying R;R^op subset J sends the class of x to the
class of any R-neighbour y, with the transported target kernel fixed as
J^R=R^op;J;R. The canonical transport provider proves independence of
representatives, surjectivity and injectivity on these quotients.

A nonempty invariant typed relation is serial and coserial: move the source
of one witness pair to any requested source using original transitivity;
move its target instead to obtain a predecessor for any requested target.
Thus all compatible finite RAW products are nonempty. They are invariant,
so in the actual finite full-Aut orbital language each is one of finitely
many finite unions of old pair orbitals. An arbitrary proper-subgroup
invariant refinement would not have this consequence.

Naming is a separate step. FULL NR2 makes every original invariant
equivalence full RAW exact by I05 C25–C27. The full upper-interval
transport isomorphism preserves proper meet-irreducibility: if two
relations meet in H0>=E, they both belong to that upper interval, so the
interval meet-irreducibility is also full-lattice meet-irreducibility.
Non-Top follows from bijectivity of quotient sets. Nonzero needs visible
old SAP: if a nonzero transported coordinate were real equality, its
transport relation would give a total definable real function; two old SAP
copies over its input would separate outputs that functionality forces to
coincide. I02 carries precisely this argument. A pullback H0>=E>Id is
already nonzero. Only after these checks does FULL RAW exactness identify
the new MI kernel with an existing represented coordinate symbol. There
is no hidden SAP premise or conclusion here.

For the root-signature compatibility, suppose R,S contain an actual atom
c and are quotient-functional over the same J. Fix ANY target y, choose
x c y by coseriality, and compute each canonical predecessor label.
The unique R-, S- and c-predecessor J-class is [x]_J. Consequently all
three label maps coincide on the entire target sort, their kernels are
literally equal and their inverse quotient bijections agree. This is a
statement about quotient functions, not equality of binary relations.
For an actual root pair x D y, every direct and branch-forced transition
identity is therefore satisfied by the actual coordinates of x,y.
Branch equations at different admissible J's keep their own types; they
are not artificially identified. Applying any further named functions
preserves the equations. This checks consistency on actual roots and
makes no completion claim for an arbitrary partial root signature.

## N02: Term normalization terminates and bounds functions

**D02–D04; C06–C12.** Read a term from its source toward its value.
Suppose a transition q_(R,E) to F=E^R is followed by u_(F,H).
The upper-interval transport gives the unique H0>=E with H0^R=H.
N01 supplies its proper represented named status. Choose x representing
any E-class and y with x R y. Both composites

- q_(R,E), then u_(F,H);
- u_(E,H0), then q_(R,H0)

send that E-class to [y]_H. Thus the rewrite is pointwise equality
on the same actual quotient carriers. No representative or chart remains
in the equality of functions.

Count every pair consisting of a transition and a later upward map.
If such an inversion exists, there is an adjacent transition/upward pair
in the two-letter word obtained by recording these types of operation.
Swapping that adjacent pair decreases the inversion count by one and
leaves all other pair counts unchanged. Identities can be discarded.
The natural-number count proves termination. Consecutive upward maps
compose because containing-class projection is transitive. With a real
source, their composite with the initial projection is F_K; with source
B_(a,J), it is u_(J,K), allowing K=J and the existing identity.
There are no quotient-to-real functions in this language, so a real term
is either its real identity or begins with one real projection.

For the remaining transition-only word use actual RAW relational
composition, including equality witnesses. If R is followed by S over the
literal middle F=E^R, the quotient-transport provider gives
E^(R;S)=F^S and q_(R;S,E)=q_(S,F) composed q_(R,E).
The product is nonempty by seriality, and its kernel bound follows from
its actual adjacent transport bounds. Induction collapses the whole word
to one actual old relation T in the appropriate finite Rel family.
Typed interior relations retain their order. If same-sort T contains real
Id, I06 gives E^T=E and q_(T,E)=id on the existing coordinate.
This handles pure Id and Id mixed with diversity without placing an
identity-labelled atom in a STRONG word.

We have literal function normal forms:

- real source: real identity, or theta composed F_K;
- coordinate source B_(a,J): theta composed u_(J,K).

Here theta is one actual named quotient bijection or the existing identity.
There are finitely many source and target sorts, represented kernels and
actual Rel families. For a real source a an explicit overcount is
`1 + sum_(K in I_a) sum_b |Rel^(ab)|`; the extra one is its real identity.
For coordinate source B_(a,J), use
`sum_(K in I_a, K>=J) sum_b |Rel^(ab)|`, enlarged by one if needed to
index identities separately. Removing invalid kernel/target combinations
only decreases this count. One may include the coordinate identity as a
separate index uniformly to avoid relying on an Id relation index.
Taking the maximum of these finite overcounts and 1 gives m_typ.
Only the induced FUNCTIONS are counted. Arbitrarily many syntactic
inverse loops can still denote one function.

## N03: Actual and unary-admissible one-generated closures

**D05; C13–C15.** The set of all unary term values of a vertex v contains
v through the identity and is closed under each named unary function by
composition. Conversely every closed set containing v contains all term
values by induction on syntax. It is therefore exactly cl(v).
Evaluation at v is a surjection from the finite set of term functions
with its source sort to this closure; its cardinal is at most m_typ.
A finite actual completed member is unary-closed in the interpreted
ambient structure, so its term evaluations are the ambient evaluations.
The argument applies equally to a real generator and an orphan quotient
generator, even when no real root belongs to the finite substructure.
No amalgamation theorem about orphan bases is being assumed.

For a unary-admissible partial source C, take v in C and the stipulated
isomorphism of the FULL induced cl_C(v) with an actual completed
one-generated member. It is a bijection preserving all unary operations
and binary data and therefore preserves cardinality. The actual bound
applies to its target, proving the same bound for cl_C(v).
This argument is local to each generator. It does not show that C is
complete, that C has a completion or that the whole cardinal |C| is
bounded. In particular, being a finite structure in a finite unary
language, or merely being unary-closed, does not supply the actual
quotient identities or the full one-generated isomorphism required here.

## N04: Malformed long transition cycles are a sharp input guard

**D07; C16–C21.** The actual common-block model can be realized with
infinitely many blocks and infinitely many real A-points and B-points in
every block. Old atomic pair types record whether block labels agree;
within a real sort equality remains separate from same-block diversity.
Its actual finite age has SAP: combine the block partitions extending a
common complete base, assign any unanchored blocks fresh labels as
needed, and choose all new real points distinct in their block and sort.
For old semantic CCO, displayed same-block edges require equality of
block labels; displayed different-block edges require inequality.
If these constraints are inconsistent, some displayed different-block
edge has endpoints joined by a same-block path. A shortest such path is
simple and, together with that edge, is a forbidden specified simple
cycle. If there is no conflict, assign one fresh block to each
same-block component and choose distinct real clones in all prescribed
sorts. This realizes every displayed atomic edge. Thus the model is a
genuine old SAP+CCO example, not merely an arbitrary functional graph.
The proper hidden block quotients QA,QB have inverse same-block maps
f:QA->QB and g:QB->QA, satisfying g f=id and f g=id in genuine members.
There is only one nontrivial proper coordinate per real sort here; other
named unary operations on these two quotients are the corresponding
existing identities or these same inverse functions.

For n>=2 instead put x_i in QA and y_i in QB, set f(x_i)=y_i and
g(y_i)=x_(i+1 mod n), and display no binary orbitals and no real vertices.
All named unary symbols are total on their respective existing carriers.
From any x_i repeated g f visits all x_j, and f reaches all y_j.
From any y_i first apply g and repeat. Hence the unary closure of EVERY
vertex is the entire 2n-point structure. There is no proper nonempty
unary-closed induced substructure. A decomposition as a free amalgam of
two proper substructures would have to cover this whole nonempty source
with such closed pieces; it cannot. The whole source is irreducible in
the unary-functional sense, regardless of its absent displayed edges.

If h preserved all functions into a genuine completed hidden member,
then for every i,
`h(x_(i+1)) = g(f(h(x_i))) = h(x_i)`.
It collapses distinct x-points, contradicting injectivity on the whole
irreducible source. Thus there is no homomorphism-embedding completion.
For a proposed closed-substructure obstruction bound N choose 2n>N.
All closed substructures of size <=N are empty and completable, while
the entire source is noncompletable. This disproves the unrestricted
bound for arbitrary total-unary partial sources.

Every one-generated closure in this example is itself the noncompletable
irreducible whole. Consequently it is NOT isomorphic to an actual
completed one-generated diagram: such an isomorphism would already give
an injective completion. The intended HN one-generated irreducible
membership test excludes it. The example explains why that admissibility
gate is essential; it neither refutes the terminal Ramsey statement nor
installs a new HN theorem or receiving Lean binding.

## N05: Literal real-source kernels, stabilizers and forced terms

**D08; C22–C27.** If tau is the real identity, its kernel is actual real
equality. This is the only case with a real codomain because the language
has no function from a quotient back to a real point. Otherwise N02 gives
literal tau=theta composed F_K with K a represented proper nonzero MI on
the ORIGINAL real source sort. Theta is a bijection, so
`tau(x)=tau(xprime)` iff `F_K(x)=F_K(xprime)` iff `x K xprime`.
This proves QT-NF even if the transition word traversed several original
sorts. Its named theta also recovers the value from the K-coordinate;
the argument is stronger than the existence of some abstract kernel.

For any group preserving the actual named maps, equivariance gives
h tau(x)=theta(h F_K(x)). If h fixes F_K(x), this fixes tau(x).
If h fixes tau(x), comparison with theta(F_K(x)) and injectivity of theta
force h F_K(x)=F_K(x). These two implications prove equality of
stabilizers without transitivity, faithfulness or homogeneity of that
acting group. In the identity case its class is the actual singleton.
The source's phrase any automorphism group is read with these actual
interpreted named maps; an unrelated arbitrary action supplies none of
the required equivariance.

Suppose represented J>Id satisfies J<=K_tau. It cannot be the real
identity case, since then K_tau=Id. Thus use the proper-coordinate normal
form and the named upward u_(J,K_tau). Actual quotient projection gives
F_(K_tau)=u_(J,K_tau) composed F_J pointwise. Define the literal term
sigma_(tau,J)=theta composed u_(J,K_tau). Then
`tau = sigma_(tau,J) composed F_J` on every real point.
If theta comes from an identity-containing RAW composite, it is the
existing identity by N02 and the same formula is valid. No chart,
representative, choice of a root or ordering of original sorts occurs.

## N06: Generic canonical RAW returns and their named upgrade

**D09–D10; C28–C36.** First forget the actual hidden language. Let G act
transitively on the nonempty typed carriers, with nonempty invariant
RAW factors P_i, n>=1, a_n literally a_0 and whole product contained in
E0. Nonempty invariant relations are serial/coserial by the witness-move
argument; this works without a faithful action. Every prefix R_i and
suffix S_i is therefore serial/coserial, allowing R0 and the last suffix
to be actual identity relations. For x R_i y and xprime R_i y choose ONE
suffix witness y S_i z. Whole-word containment gives x E0 z and
xprime E0 z, hence x E0 xprime. Thus lambda_i(y), the E0-class of ANY
R_i-predecessor, is well defined. It is onto and equivariant.
Two target points have the same label precisely when they have
E0-related R_i-predecessors, giving the literal kernel formula
E_i=R_i^op;E0;R_i. In particular R_i;R_i^op subset E0, so this is a
valid original invariant quotient transport, not an assumed equivalence
obtained from a possibly unfunctional relation.

For an edge y P_i z, choose x R_(i-1) y; then x R_i z. Both adjacent
labels are [x]_E0. Any two P_i-predecessors of z therefore have equal
previous labels, proving P_i;P_i^op subset E_(i-1).
Conversely choose P_i-predecessors of two target points; their previous
labels agree exactly when the target labels agree. Hence
P_i^op;E_(i-1);P_i=E_i. The actual induced quotient bijection is
`q_i = bar-lambda_i^-1 composed bar-lambda_(i-1)`.
The SAME kernel E_i and SAME canonical label occur on both incident
macro sides at position i; arbitrary independent charts cannot be
substituted into this formula.

At position zero the label is [x]_E0 because R0=Id. At the end, any
x R_n y has x E0 y, so lambda_n(y)=[y]_E0 on the same literal carrier
as position zero. The composite of the displayed q_i formulas telescopes
to bar-lambda_n^-1 composed bar-lambda_0, which is identity. In particular
E_n=E0. For EVERY coarser invariant J>=E0, compose all labels with the
canonical projection a0/E0->a0/J. The identical proof gives
J_i=R_i^op;J;R_i, exact adjacent kernel transport and identity holonomy
on a0/J simultaneously and compatibly with coarsening. No hidden SAP,
CCO, represented quotient naming or transport section is used.
When the input relations/equivalences have supplied first-order formulas,
finite existential composition supplies formulas for R_i,E_i,J_i.
For arbitrary G, invariance alone proves none of this definability.

Now specialize to actual terminal data and represented Id<J<Top.
The interval isomorphism for prefix R_i preserves full MI and non-Top;
old real SAP prevents collapse to actual equality; FULL NR2 makes the
resulting original invariant MI full RAW exact. Thus EACH J_i is an
existing NAMED represented proper coordinate of its actual old sort.
The E_i may be arbitrary invariant equivalences and are not asserted MI.
Each factor Pi now gives its actual named transition between those exact
J_(i-1),J_i. If an equality-containing same-sort factor occurs, its map
is the existing identity. If a diagonal-free relation is a union, any
chosen atom has the same canonical predecessor labelling by N01, so the
already named atomic transition also realizes the whole-relation map.
The named terms are precisely the generic canonical q_i, hence their
return remains the literal identity. This two-stage proof discharges the
source represented-language statement without pretending that generic
invariant interval transport by itself manufactures named exact sorts.

## N07: Boundaries and validation meaning

**C37–C39.** Generic A05 permits a nonfaithful group or a proper subgroup
of the original full automorphism group. It proves invariant kernel and
return identities. The actual full-Aut finite-orbital context, original
SAP and FULL NR2 are separately invoked only for definability and named
proper-coordinate membership. The stabilizer proof uses any group
preserving the actual named functions; it does not assert that arbitrary
partial hidden isomorphisms extend to this group.

An upward-only term has theta=id. A quotient identity has K=J and the
existing upward identity. The real identity is its separate Id kernel.
For closed words n=1 is allowed and the same suffix proof works; n=0
would be a separate trivial identity assertion. Empty relation factors
are excluded: if a factor were empty, containment of the whole empty
relation in E0 would not give seriality or quotient bijections.
The standing source word convention supplies nonemptiness; repeating it
in the statement is queued only as a receiving-API clarification.

The bounded executable controls check actual finite coordinate functions,
normal forms, real kernels, factorisations and canonical coarsened return
maps. Malformed cycle sizes test closure, irreducibility and the forced
collapse equation. Finite windows are diagnostic witnesses; they certify
no unbounded SAP/CCO, no hidden homogeneity/SAP and no external theorem.
All five existing HN/HKN receiving bindings remain pending.
