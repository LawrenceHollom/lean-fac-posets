# Stage 3 formalisation roadmap

## Scope and endpoint

This roadmap contains only the work still required for Stage 3. Its endpoint is a sorry-free proof
of

```lean
theorem exists_maximalTube [Countable α] (hfac : IsFAC α) (hvac : IsVacillating α) :
    ∃ T : Set α, IsMaximalTube T
```

and hence `main_theorem`, relative only to the explicitly isolated theorem of Zaguia used by the
already completed maximal-tube-to-spine reduction. The completed Stage 1 and Stage 2 modules are
inputs and are not scheduled below.

Stage 3 must also discharge the three preliminary `sorry`s on which it relies: FAC under order
duality, the infinite-chain lemma for FAC posets, and the cover lemma for scattered orders. The
Hausdorff input must either be proved locally or exposed as one precise, documented external
assumption; the current theorem with conclusion `True` is not an acceptable interface.

## Design rules

1. **Normalize before quotienting.** A point of `H(P)` will be either a principal point of `P`, a
   genuinely nonprincipal increasing/decreasing germ, or `⊥`/`⊤`. Principal increasing and
   decreasing chains will be normalized to the principal constructor before taking quotients. This
   avoids the quotient-of-quotients and principal gluing used informally in the paper.
2. **Keep quotient internals private.** Later files may use constructors, induction principles,
   representative predicates, and chosen-representative lemmas, but must not unfold the setoids or
   quotient implementation of `H(P)`.
3. **Bundle recurring objects.** Saturated chains, maximal chains, partition classes, replacement
   witnesses, and candidate chains should be structures with `SetLike` instances. Their invariants
   should travel with the object instead of being reproved at every call site.
4. **Make duality an API.** Prove increasing results first and derive decreasing results through
   `OrderDual` wherever possible. Definitions should use a two-valued direction type rather than
   duplicated Boolean flags or duplicated proofs.
5. **Separate relations from witnesses.** Each replacement has a witness structure, a proposition
   asserting that a witness exists, and a bundled object order. Composition is defined on witnesses;
   reflexivity, transitivity, persistence, and antisymmetry are then proved for the relation.
6. **Construct stable data before maximal extensions.** A sequential upper-bound proof must first
   construct terminal/stable descendants and prove that their union has the required structure.
   For consolidation the stable data are germs forming a chain in `H(P)`. Extend this to a
   maximal chain in `H(P)`, take its principal trace, and extend that trace in `P`. Realize
   the stable germs by new cuts; neither their old representatives nor their atomicity
   need survive. See `CONSOLIDATION_LIMIT_REPAIR.md`.
7. **Use convex hulls for target intervals.** Raw unions of descendant fibres need not be intervals
   in a later maximal chain. Replacement composition and limit witnesses should take the induced
   convex hull in the final target.
8. **Prefer countable cofinal reductions to ordinal bookkeeping.** Before formalizing an
   `ω₁`-stabilization argument, look for a persistent marker of strict progress indexed by the
   countable ambient poset, as in the eta-replacement proof. Keep transfinite arguments only where
   no such marker exists.
9. **State empty cases explicitly.** No proof may take the minimum or maximum of a finite
   incomparability set without a non-emptiness hypothesis. Use `Finset`, `Option`, or an explicit
   empty/non-empty split.
10. **Freeze APIs at phase boundaries.** Downstream work starts only after the phase's public
    declarations compile from an API test file that does not unfold private definitions.
11. **Use whole-chain consolidation with local cofinality.** Witnesses fix formal endpoints,
    preserve genuine directions and existing nonempty suprema/infima, and satisfy
    `D(f(X)) ⊆ D(X)` for increasing germs and the dual upper-profile condition for decreasing
    germs. Do not require genuine global cofinality at ordinary ends: Section 1 of
    `CONSOLIDATION_LIMIT_REPAIR.md` gives a sequence with no such upper bound. The stronger
    endpoint property needed for illfounded gluing is a later consequence. Candidate
    objects are quotiented by mutual whole-chain consolidation, not by germ equivalence.

## Planned module graph

```text
Preliminaries/FAC + Preliminaries/Scattered
  `-- Preliminaries/ReplacementOrder
        `-- Completion/SaturatedChain
              `-- Completion/FiniteDistance
                    `-- Completion/{ChainEquivalence, TraceTransfer, ChainTransitivity, Germs}
                          `-- Completion/Construction
                                `-- Completion/Representatives
                                      `-- Completion/Order
                                            |-- Completion/Embedding
                                            `-- Completion/Completeness
                                                  `-- Illfounded/Limits
                                                        `-- Illfounded/Replacement
                                                              `-- Illfounded/Reduction
                                                                    `-- Alternating/Classes
                                                                          `-- Alternating/Replacement
                                                                                `-- Alternating/Maximal
                                                                                      `-- Consolidation/Atomic
                                                                                            `-- Consolidation/Relation
                                                                                                  `-- Consolidation/Maximal
                                                                                                        `-- Final/TubeFromChain
                                                                                                              `-- Final/Main
```

`Completion/SaturatedChain.lean`, `Completion/Representatives.lean`,
`Completion/Embedding.lean`, and `Preliminaries/ReplacementOrder.lean` are deliberate additions to
the original skeleton. They keep high-churn implementation details out of the large theorem files.

## Risk-first interface spikes

These are short compile-tested prototypes, not throwaway prose designs. They come first because a
bad choice here would force most of Stage 3 to be rewritten.

- [x] **S3.0.1 — `H(P)` representation spike (critical).** In a temporary namespace, implement the
  proposed sum of principal points, increasing germs, decreasing germs, and endpoints. Check that
  its eliminator supports definitions of sign, representatives, and domination without exposing a
  nested quotient.
- [x] **S3.0.2 — quotient transport spike (critical).** Prototype one representative-invariant
  binary relation and one representative-invariant function on increasing germs. Record the exact
  `Quotient.lift`/`Quotient.inductionOn` lemmas that the public API will expose.
- [x] **S3.0.3 — chain-equivalence map spike (critical).** Replace the manuscript's choice of the
  minimum incomparable point by a relation between finite-distance classes: two classes correspond
  when they contain equal or incomparable representatives. Verify on paper and in Lean that this
  gives a total, single-valued order isomorphism. This removes all empty-minimum edge cases.
- **S3.0.1–S3.0.3 decisions:** use a flat five-constructor completion carrier; expose quotient
  constructors and induction while keeping the setoids private; use the representative relation
  `DistanceClassesCorrespond`, whose selected map is now proved to be an endpoint-preserving order
  isomorphism.
- [x] **S3.0.4 — Hausdorff interface spike (high).** State the smallest order-theoretic corollary
  actually needed later: a scattered linear order containing `ω` has a saturated increasing suborder
  containing `ω` but not `ω + 1`, together with its dual. Decide now whether this theorem will be
  proved locally or retained as the sole Stage 3 external assumption.
- **S3.0.4 decision:** retain this corollary as the sole Hausdorff external axiom, with its dual
  theorem derived locally by order duality.
- [x] **S3.0.5 — replacement-limit spike (high).** Extract the reusable running-maximum and
  countable-cofinal lemmas from `Structural/EtaReplacement.lean`. Prototype a stage-tagged state
  and terminal-descendant API parameterized by witness composition, without trying to abstract the
  branch-specific mathematics.
- [x] **S3.0.6 — consolidation witness spike (critical).** Prototype a structure extending an order
  embedding with preservation of the suprema/infima actually used in the paper. Confirm that
  identity and composition are easy and that atomic source points require only the non-recursive
  base consolidation relation.
- **S3.0.5–S3.0.6 decisions:** tag replacement vertices by their stage and parameterize proper
  descent by composed witnesses; use an order embedding carrying precisely nonempty bounded
  `sSup`/`sInf` preservation, with atomic obligations stated only through a supplied base relation.
  Identity and composition compile without extra fields.

Delete the temporary namespaces after their decisions have been incorporated into the modules
below. Record any changed decision in this section before proceeding.

## Ordered implementation packages

The packages below are in dependency order. Within each phase, higher-risk obligations are placed
as early as their prerequisites allow.

### Phase A — Stage 3 prerequisites and reusable order tools

- [x] **S3.A.1 — FAC duality.** Prove `isFAC_orderDual_iff` in `Preliminaries/FAC.lean` and add both
  directional convenience lemmas.
- [x] **S3.A.2 — infinite chain in an infinite FAC poset.** Prove `IsFAC.exists_infinite_chain`,
  isolating the precise Ramsey theorem used from mathlib.
- [x] **S3.A.3 — monotone subsequence API.** Verify that the existing strictly monotone/antitone
  subsequence result no longer depends on a `sorry`, and add range-infinitude and subtype versions
  needed by `Final/TubeFromChain.lean`.
- [x] **S3.A.4 — scattered cover lemma.** Prove `IsScattered.exists_covBy_between`, including
  induced-subposet and order-dual forms.
- [x] **S3.A.5 — finite colouring of `η`.** Prove that one cell of every finite partition of a copy
  of `ℚ` contains a copy of `ℚ`; this is the only combinatorial input needed for scattering of
  `H(P)`.
- [x] **S3.A.6 — exact Hausdorff input (high).** Replace
  `External.hausdorff_classification_interface : True` by the generic saturated-suborder theorem
  chosen in S3.0.4, and prove it locally or declare its precise statement as an external axiom.
- [x] **S3.A.7 — direction abstraction.** Add an `OrderDirection` type with `increasing` and
  `decreasing`, its dual involution, and direction-indexed initial/final segment and
  cofinal/coinitial predicates.
- [x] **S3.A.8 — countable replacement-order tools.** Move/generalize `etaRunningMax` into
  `Preliminaries/ReplacementOrder.lean`; add finite-prefix maxima, enumeration of a nonempty
  countable set, and a theorem turning a countable cofinal family in a chain into a monotone cofinal
  sequence.
- [x] **S3.A.9 — Zorn wrapper.** Add a small theorem that obtains a maximal object from upper bounds
  for nonempty chains above a fixed starting object. This keeps empty-chain bookkeeping out of all
  three later maximality arguments.
- [x] **S3.A.10 — prerequisite gate.** Build the project and confirm that the only remaining
  `sorry`s are the Stage 3 endpoint and explicitly accepted external theorems.

### Phase B — saturated chains and finite-distance classes

- [x] **S3.B.1 — bundled saturated chains.** In `Completion/SaturatedChain.lean`, define nonempty
  saturated chains with `SetLike`, coercions to their induced linear orders, restriction to
  direction-indexed segments, and order-dual transport.
- [x] **S3.B.2 — endpoints.** Define `HasTop`, `HasBottom`, `NoTop`, and `NoBottom` for bundled
  chains and prove that a chain with a top/bottom has a unique such point.
- [x] **S3.B.3 — maximality in a convex hull.** Bundle the assertion that two chains are maximal in
  `Conv(C ∪ D)` and prove the basic “outside point has an incomparable witness” lemma.
- [x] **S3.B.4 — finite-distance relation.** In `Completion/FiniteDistance.lean`, define the
  symmetric finite open-interval relation and prove reflexivity, symmetry, and transitivity.
- [x] **S3.B.5 — convexity of distance classes.** Prove each equivalence class is an interval of the
  source chain and characterize when two classes are strictly ordered.
- [x] **S3.B.6 — quotient linear order.** Construct the linear order on finite-distance classes and
  expose `mk`, `mk_eq_mk`, representative comparison, and quotient induction lemmas.
- [x] **S3.B.7 — endpoint shape.** Prove only the class facts actually needed later: preservation of
  the existence of minima/maxima and the finite/one-sided/two-sided alternatives. Avoid committing
  downstream files to concrete isomorphisms with `ω`, `ω*`, or `ℤ` unless required.

### Phase C — chain equivalence

- [x] **S3.C.1 — mutually finite incomparability.** In
  `Completion/ChainEquivalence.lean`, define it as finite incomparability in both directions plus
  maximality of both chains in their common convex hull.
- [x] **S3.C.2 — local consequences.** Prove incomparability sets are finite intervals, and every
  point of either chain is equal or incomparable to a point of the other unless already contained
  in it.
- [x] **S3.C.3 — correspondence of distance classes (high).** Implement the relation prototyped in
  S3.0.3 and prove existence, uniqueness, order preservation, and symmetry.
- [x] **S3.C.4 — class order isomorphism.** Package the correspondence as the paper's
  `lem:sim-equivalence-bijection`, including preservation of class minima and maxima.
- [x] **S3.C.5 — tail and head equivalence.** Define increasing equivalence through mutually
  finite final segments and decreasing equivalence by duality. Principal chains remain outside
  these setoids.
- [x] **S3.C.6 — setoid laws (high).** Prove finite-trace transfer using a finite trace and
  its possible immediate neighbors. Cut the outer chains above a common middle point, then
  normalize their starting points to be equal or incomparable. Prove common-hull maximality
  from saturation and mutual cofinality. Increasing transitivity is assembled in
  `Completion/ChainTransitivity.lean`; decreasing transitivity follows by duality.
- **S3.C.6 corrected design decision:** retain exactly the direct paper-level relation
  (mutually finite-incomparable final segments). The proposed classwise-maximality composition
  is unnecessary and is not assumed. `MATH_REPAIR.md` gives the replacement proof of Lemma 3.5;
  `Completion/TraceTransfer.lean` proves its finite-trace core. No equivalence closure, additional
  axiom, or boundary-class maximality field is used.
- **Saturation correction:** `IsSaturatedChain` now matches the manuscript: a point between
  two chain points is insertable only if comparable with the entire chain. Ambient convexity
  was too strong. Restriction, duality, common-hull reflexivity, and inheritance of vacillation
  have been updated. In linear orders saturation is still equivalent to convexity, preserving
  the mathematical content of the isolated Hausdorff input. `SaturationExamples.lean` checks
  the diamond example that distinguishes the two notions.
- [x] **S3.C.7 — germ types.** Define increasing and decreasing quotient germs and expose equality,
  representative, direction, and duality APIs.
- [x] **S3.C.8 — API gate.** `Completion/GermAPI.lean` proves representative-independent upper
  bounds, a binary relation, and representative/duality statements using public declarations.
  `Completion/Germs.lean` keeps the setoid, quotient field, and raw constructor private and
  exposes invariant unary/binary lifts. The audited Phase C theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`, with no `sorry` or external mathematical axiom.

### Phase D — construction and order of `H(P)`

- [x] **S3.D.1 — normalized point type.** In `Completion/Construction.lean`, define `H α` with
  constructors for `principal x`, a nonprincipal increasing germ, a nonprincipal decreasing germ,
  `⊥`, and `⊤`.
- [x] **S3.D.2 — nonprincipal views.** Define `N`, `N+`, and `N-` as direction-tagged subtypes,
  placing `⊤` in `N+` and `⊥` in `N-`; provide exhaustive case and disjointness lemmas.
- [x] **S3.D.3 — representative relation.** In `Completion/Representatives.lean`, define when a
  saturated chain represents a nonprincipal point. Provide existence, change-of-representative,
  chosen representative, and endpoint-specific simp lemmas.
- [x] **S3.D.4 — principal embedding.** Define `principal : α → H α`, prove injectivity, and add simp
  lemmas for all constructors. Do not yet declare it an order embedding.
- [x] **S3.D.5 — representative-level domination (high).** Define strict domination for every
  direction pair using nonempty tails/heads. Prove invariance under chain equivalence before
  lifting it to germs.
- [x] **S3.D.6 — mixed domination cases.** Prove principal/germ, germ/principal,
  increasing/decreasing, and endpoint formulas. Use order duality to halve the cases.
- [x] **S3.D.7 — strict-order laws (high).** Prove irreflexivity and transitivity of domination,
  including all mixed constructors.
- [x] **S3.D.8 — partial order.** Define `X ≤ Y` by equality or domination, build the `PartialOrder`
  instance, and prove useful `lt_iff` and constructor comparison simp lemmas.
- [x] **S3.D.9 — principal order embedding.** Upgrade `principal` to `α ↪o H α` and prove it
  preserves/reflection comparability and incomparability.
- [x] **S3.D.10 — cuts induced by germs.** Characterize the principal points below/above a germ;
  prove separation of two distinct comparable germs by a principal point when required.
- [x] **S3.D.11 — scattering of `H(P)`.** Use S3.A.5 and principal separators to prove
  `IsScattered α → IsScattered (H α)`.
- [x] **S3.D.12 — order gate.** Check `#print axioms` for the order and scattering theorems and add
  examples for finite chains, `ℕ`, `ℤ`, and their duals.
- **Phase D implementation:** `Domination.lean` isolates segment separation and its
  representative-invariant quantifier formulas; `Scattering.lean` isolates the scattering
  argument. `OrderAPI.lean` passes the public-API and axiom gates without unfolding the
  representative-level domination relation or germ internals. The audited theorems depend
  only on `propext`, `Classical.choice`, and `Quot.sound`.

### Phase E — sub-completions and completeness

- [x] **S3.E.1 — admissible subposets.** In `Completion/Embedding.lean`, define the condition that
  saturated chains of `Q` remain saturated in `P`, and prove it for convex subposets and saturated
  chains.
- [x] **S3.E.2 — map germs along an inclusion.** Lift representatives, prove preservation and
  reflection of chain equivalence, and define the induced map `H(Q) → H(P)`.
- [x] **S3.E.3 — completion embedding.** Prove the induced map is an order embedding, commutes with
  principal points and endpoints, and preserves direction and representatives.
- [x] **S3.E.4 — completion of a chain is linear.** In `Completion/Completeness.lean`, prove
  `H(C)` is linearly ordered and prove the principal-separator lemma between increasing germs.
- [x] **S3.E.5 — explicit sup candidate (high).** For `D : Set (H C)` without a maximum, define the
  initial segment of principal points lying below some member of `D`; prove it is saturated and has
  no maximum.
- [x] **S3.E.6 — least-upper-bound theorem.** Show the increasing germ of that segment is `sSup D`,
  with separate proofs for empty sets, sets with maxima, and the endpoint cases.
- [x] **S3.E.7 — infimum by duality.** Derive the dual construction and install the
  `CompleteLinearOrder (H C)` instance.
- [x] **S3.E.8 — shape of non-attained bounds.** Prove that a supremum not attained by its
  **nonempty** set lies in `N+`, and dually for infima. Expose sequence-specialized versions
  for later files. The nonempty hypothesis is necessary: `sSup ∅ = ⊥ ∈ N-` and
  `sInf ∅ = ⊤ ∈ N+`.
- **Phase E repair:** `PHASE_E_BLOCKER.md` retains the counterexamples to global endpoint
  cofinality, germ-level antisymmetry, and unchanged realization of stable germs. The new
  mathematical sequential construction is in `CONSOLIDATION_LIMIT_REPAIR.md`; the Phase I/J
  items below now use that construction. `Continuity.lean` separates global cofinality from
  continuity, and `BoundaryProfiles.lean` implements local cofinality and bicomparability.
  `PrincipalInterpolation.lean` and `CutRealization.lean` formalize the principal-cut
  realization and separation core. The full sequential theorem and its atomic/hull
  prerequisites remain unchecked roadmap items; a mathematical proof is not a Lean gate.
- [x] **S3.E.9 — continuity toolkit.** Define the sup/inf-preserving order embeddings prototyped in
  S3.0.6, with identity, composition, restriction, cofinal-image, and coinitial-image lemmas.
  `CompletionAPI.lean` checks composition, convex source restriction, target restriction,
  cofinality, and duality; its axiom audit uses only standard Lean axioms.
- [x] **S3.E.10 — accumulation and bicomparability.** Define accumulation/isolated nonprincipal
  points and bicomparability; prove symmetry, transitivity in the cases used later, and equivalent
  sequential/cofinal formulations.
- [x] **S3.E.10a — local profiles and bicomparability.** `BoundaryProfiles.lean` defines genuine
  lower/upper profiles, local cofinality, and bicomparability. Representative formulas,
  reflexivity, symmetry, transitivity, duality, and uniform principal bounds compile.
  `Sequences.lean` adds cofinal representative sequences and sequential bicomparability;
  `Accumulation.lean` completes accumulation, isolation, duality, cofinality, sup/inf, and
  countable-chain sequential characterizations. Formal endpoints are proved isolated in
  chain completions, including the empty-chain case.
- [x] **S3.E.11 — completion gate.** Freeze the `H(P)` API. No later module may unfold germ
  setoids, quotient constructors, or representative-level domination.
- **Phase E gate passed:** `AharoniKorman.Completion` is the public aggregate import used
  by `Illfounded/Limits.lean`. `COMPLETION_API.md` documents the supported declarations,
  hypotheses, and endpoint conventions. `CompletionAPI.lean` and
  `AccumulationExamples.lean` compile from this interface without unfolding germ internals;
  audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The sequential
  characterizations assume a countable original chain, not a countable completion.

### Phase F — illfounded limits and quasifounded pieces

- [ ] **S3.F.1 — alternating block sequences.** In `Illfounded/Limits.lean`, formalize disjoint
  increasing intervals alternating between infinite wellfounded and co-wellfounded blocks.
- [ ] **S3.F.2 — representative invariance (high).** Define an illfounded limit first for a
  representative and prove invariance under increasing/decreasing chain equivalence and passage to
  a direction-appropriate segment.
- [ ] **S3.F.3 — illfounded points of `H(P)`.** Lift the definition to nonprincipal points and prove
  order-dual, chosen-representative, and bicomparability transport lemmas.
- [ ] **S3.F.4 — quasifounded convex sets.** Define quasifoundedness using closed intervals in
  `H(P)` between principal endpoints. Prove inheritance by convex subsets and order duality.
- [ ] **S3.F.5 — cofinality obstruction (high).** Formalize `lem:increasing-decreasing-cofinal`:
  increasing sequences in `N-` of a countable scattered vacillating quasifounded FAC poset are
  cofinal, and derive the decreasing `N+` case by duality.
- [ ] **S3.F.6 — quasifounded relation on a maximal chain.** Define `x ≈ill y` by quasifoundedness
  of the closed interval and prove it is an interval equivalence relation.
- **S3.F.6 ambient-order convention:** instantiate quasifoundedness in the induced linear
  order `C`, using `H(C)`, for this partition. Ambient gap quasifoundedness in S3.F.4 and
  S3.G.12 uses `H(P)`. These are different predicates: an illfounded branch parallel to
  a three-point maximal chain can lie between its outer endpoints in `H(P)` while being
  incomparable with its middle point, so the ambient predicate would not be transitive.
- [ ] **S3.F.7 — quasifounded partition.** Bundle its equivalence classes, order them, prove they
  are nonempty convex intervals, and provide class membership and comparison APIs.
- [ ] **S3.F.8 — boundary flags.** Represent the possible lower and upper illfounded boundary
  points explicitly and define `illRank : Fin 3` as their count. Prove rank comparison lemmas used
  by replacements; downstream code should not reason by raw cardinality.

### Phase G — illfounded replacement and reduction

- [ ] **S3.G.1 — replacement witness.** In `Illfounded/Replacement.lean`, map every source
  quasifounded class to a nonempty interval of target classes, recording external order preservation
  and singleton rank progress.
- [ ] **S3.G.2 — ordered and disjoint images.** Prove strict ordering of images of distinct source
  classes, disjointness, and persistence of boundary points/rank progress.
- [ ] **S3.G.3 — identity and triviality.** Define the identity witness and prove a trivial witness
  forces equality of maximal-chain carriers.
- [ ] **S3.G.4 — composition (high).** Compose witnesses using the convex hull of iterated images;
  prove the interval and rank clauses separately, then package transitivity.
- [ ] **S3.G.5 — antisymmetry.** Analyze a composite self-replacement, prove it is trivial, and
  install the partial order on bundled maximal chains.
- [ ] **S3.G.6 — tagged descendant forest (high).** For a replacement sequence, use vertices
  `(stage, partitionClass)` rather than identifying equal underlying sets at different stages.
  Define proper descendants existentially over composed witnesses and prove transitivity.
- [ ] **S3.G.7 — terminal leaves from scatteredness (critical).** Formalize the binary-tree
  argument: a class with no terminal descendant yields an order embedding of a dense countable
  order into `P`. Treat singleton rank increases separately; there can be at most two consecutive
  such increases.
- [ ] **S3.G.8 — stable limit classes.** Construct terminal descendants before any maximal-chain
  extension. Prove their underlying union is a nonempty chain and that ordered source classes give
  ordered terminal fibres.
- [ ] **S3.G.9 — sequential upper bound.** Extend the stable union to a maximal chain, take convex
  hulls of terminal fibres in its quasifounded partition, and prove all replacement clauses.
- [ ] **S3.G.10 — arbitrary-chain reduction (critical).** First test whether strict replacements
  admit persistent point or boundary markers and hence a countable cofinal subchain via S3.A.8. If
  not, formalize the manuscript's `ω₁` stabilization as a separate theorem with coherent existential
  witnesses; do not mix it into the sequential construction.
- [ ] **S3.G.11 — illfounded-maximal chain.** Apply the Zorn wrapper to obtain a chain admitting no
  nontrivial illfounded replacement.
- [ ] **S3.G.12 — gap quasifoundedness.** Prove every gap between an initial segment of the chain's
  illfounded boundary points and its complement is quasifounded; package the result as the Stage 3
  version of `prop:quasifounded`.
- [ ] **S3.G.13 — gluing data.** In `Illfounded/Reduction.lean`, define the gap posets and prove each
  is convex, countable, FAC, scattered, and vacillating.
- [ ] **S3.G.14 — maximal-tube gluing.** Formalize `lem:quasifounded-suffices`, with explicit
  lower/upper boundary cases and bicomparable witness chains. Prove the union is a tube first and
  maximal second.

### Phase H — alternating classes and replacements

- [ ] **S3.H.1 — out-wellfoundedness.** In `Alternating/Classes.lean`, define exclusion of
  `ω ⊕ ω*`, with convex-subposet and duality lemmas.
- [ ] **S3.H.2 — alternating equivalence.** Define the relation first on nonprincipal points of
  `H(C)`, then extend it to all of `H(C)`; prove interval monotonicity lemmas.
- [ ] **S3.H.3 — equivalence laws (high).** Prove transitivity by an ordered case split in the
  complete linear order `H(C)`, deriving symmetry/reflexivity directly.
- [ ] **S3.H.4 — alternation classes.** Bundle infinite equivalence classes, prove they are pairwise
  disjoint intervals, and give their inherited linear order, convex hull, and membership APIs.
- [ ] **S3.H.5 — chain profile equivalence.** Define when two maximal chains have the same
  alternation profile and prove it is a setoid suitable for quotienting the later preorder.
- [ ] **S3.H.6 — alternating witness.** In `Alternating/Replacement.lean`, define interval-valued
  witnesses, the external-order clause, coverage, and the global singleton/triviality clause.
- [ ] **S3.H.7 — witness calculus.** Prove ordered/disjoint images, identity, convex-hull
  composition, and preservation of nontriviality under composition.
- [ ] **S3.H.8 — preorder and quotient order.** Prove reflexivity/transitivity and antisymmetry up
  to profile equivalence, then install a partial order on quotient objects rather than using the
  preorder directly with Zorn.
- [ ] **S3.H.9 — illfounded boundary persistence.** Show alternating replacements preserve an
  illfounded limit up to bicomparability, using the sequence-specific completeness API.
- [ ] **S3.H.10 — finite branching (high).** For a tagged replacement sequence, prove every image
  interval is finite using quasifoundedness and the choice of the starting chain.
- [ ] **S3.H.11 — eventual unary branches (critical).** Prove an infinite branch has only unary
  steps eventually. State the result for existential composed witnesses so subsequences do not
  require definitional associativity of composition.
- [ ] **S3.H.12 — sequential upper bound.** Define stabilization points first, prove every source
  class has a nonempty finite terminal fibre, construct their ordered union, extend it to a maximal
  chain, and use convex hulls for the final witness.
- [ ] **S3.H.13 — arbitrary-chain upper bounds (high).** Isolate the countable-cofinal or
  no-uncountable-strict-chain argument from S3.H.12 and then apply the Zorn wrapper.
- [ ] **S3.H.14 — alternating maximal chain.** Produce a maximal chain above the illfounded-maximal
  starting chain and retain all illfounded boundary points up to bicomparability.
- [ ] **S3.H.15 — out-wellfounded convex hull.** Formalize `lem:owf-convex-hull` by turning a
  forbidden `N+`-below-`N-` pair into a nontrivial alternating replacement.

### Phase I — atomic chains and consolidation relation

- [ ] **S3.I.1 — Hausdorff-to-atomic bridge.** Specialize the generic theorem from S3.A.6 to
  saturated representative chains and package the result in the normalized `H(P)` API.
- [ ] **S3.I.2 — atomicity.** In `Consolidation/Atomic.lean`, define increasing atomicity as absence
  of `ω + 1` and decreasing atomicity by duality; prove representative invariance.
- [ ] **S3.I.3 — atomic existence.** Apply the Hausdorff interface to obtain an atomic subchain in
  every scattered chain containing `ω`, with final/initial-segment versions.
- [ ] **S3.I.4 — vacillating shape.** Prove atomic increasing chains in a vacillating poset have a
  final segment of type `ω`, and derive the dual result.
- [ ] **S3.I.5 — completion embedding witness.** In `Consolidation/Relation.lean`, package a strict
  order embedding of whole-chain nonprincipal orders, fixing formal endpoints, preserving
  genuine directions and nonempty suprema/infima, with the local profile clauses of design
  rule 11. Do not require genuine global cofinality.
- [ ] **S3.I.6 — atomic consolidation.** Define the base cofinal-above/coinitial-below relation for
  atomic sources, then define general consolidation using a completion embedding whose atomic
  points satisfy the base relation. This definition is non-recursive.
- [ ] **S3.I.7 — germ-level base relations (high).** Use the representative-independent profile
  API for the atomic base relation, including changes of representative in either argument.
  Whole-chain witnesses remain on whole chains; their existence is not germ invariant.
- [ ] **S3.I.8 — local cofinality lemma.** Derive the profile clauses at every genuine image
  point from the atomic clauses and continuity, proving equivalence of the two interfaces.
  The original global-end reading of `lem:consolidation-is-cofinal` is false.
- [ ] **S3.I.9 — identity and composition.** Use the completion-embedding API to prove reflexivity
  and transitivity, with atomic transitivity as a separate lemma.
- [ ] **S3.I.10 — strongly bicomparable germs.** Define the symmetric consolidation relation and
  prove mutually finite incomparable chains have strongly bicomparable final/initial segments.
- [ ] **S3.I.11 — fixed-domain rigidity (critical).** Iterate a whole-chain self-embedding;
  show a moved genuine point creates a forbidden vacillating chain. Prove atomic
  antisymmetry separately. Do not assert antisymmetry of general germ consolidation.
- [ ] **S3.I.12 — candidate quotient order.** Install the partial order on whole-chain candidates
  modulo mutual reachability. Use I.11 to detect strict final replacements.
- [ ] **S3.I.13 — domination antichain lemma.** Formalize `lem:domination`: infinitely many
  domination-incomparable strict atomic consolidations yield an infinite antichain meeting every
  source chain.
- [ ] **S3.I.14 — quasifounded comparability.** Prove alternation-class suprema/infima have the
  correct direction and that a consolidation maps their nonprincipal points into the corresponding
  out-wellfounded interval.

### Phase J — existence of a consolidated chain

- [ ] **S3.J.1 — candidate object.** In `Consolidation/Maximal.lean`, bundle maximal chains reachable
  from the fixed alternating-maximal chain, retaining the reachability witness.
- [ ] **S3.J.2 — closure under consolidation (high).** Turn a nontrivial alternating replacement
  of a consolidation into one of the original candidate by mapping alternation classes through the
  completion embedding and taking convex hulls. Conclude every candidate is alternating maximal.
- [ ] **S3.J.3 — out-wellfounded target intervals.** Package the result of S3.I.14 and
  `lem:owf-convex-hull` as the exact interval theorem consumed by stabilization.
- [ ] **S3.J.4 — wellfounded `N+`.** Prove `N+` of a countable scattered vacillating
  out-wellfounded poset is well founded; derive the dual statement for `N-`. If realizing
  an ambient chain of germs, use principal cuts, without assuming the old germs survive.
- [ ] **S3.J.5 — tagged atomic transition graph (critical).** For a sequence of candidate
  consolidations, define stage-tagged atomic states protected by the transported lower class
  boundary for increasing states and upper boundary for decreasing states. Keep every path
  in one fixed out-wellfounded hull, and prove eventual stabilization using I.13 and J.4.
- [ ] **S3.J.6 — stable germ constraints.** Prove all protected stabilization sets are nonempty,
  their union is a chain in `H(P)`, and their lower/upper profiles satisfy uniform bounds
  at every later stage. Do not assert unchanged realization or atomicity in the final chain.
- [ ] **S3.J.7 — principal-trace realization (critical).** Extend the stable germ chain to a
  maximal chain `K` in `H(P)`. Prove its principal trace is nonempty (handling empty `P`
  separately), extend the trace to a maximal chain `C` in `P`, and realize the constraints
  by the initial/final cuts they generate in `C`. The interpolation and strict-separation
  lemmas are implemented in `PrincipalInterpolation.lean` and `CutRealization.lean`.
- [x] **S3.J.7a — principal-cut realization core.** Prove principal interpolation in maximal
  chains of a scattered completion, nonemptiness of their principal traces, and existence
  of a maximal trace extension. Construct increasing trace cuts, prove local cofinality
  and strict order preservation, and prove strict separation from any cut with a suitable
  uniform principal bound. The interpolation theorem is checked in both directions; the
  increasing construction also applies in the order dual. This does not yet assemble the
  stable-germ family or the sequential witness.
- [ ] **S3.J.8 — limit embedding on atomic points.** Define the image of an atomic point as the
  supremum/infimum in `H(C)` of the new cut realizations of its stabilization set.
  Use uniform profile bounds, strengthened protection, and principal separation for strictness.
- [ ] **S3.J.9 — extend to all nonprincipal points.** Define images of non-atomic points from
  atomic approximations; prove direction preservation, injectivity, and order preservation.
- [ ] **S3.J.10 — continuity and local cofinality.** Prove the limit map preserves nonempty
  suprema/infima, fixes the formal endpoints, and satisfies the local profile clauses.
- [ ] **S3.J.11 — atomic consolidation clauses.** Prove every atomic source consolidates to its
  limit image, and package the map as a consolidation witness.
- [ ] **S3.J.12 — sequential upper bound.** Repeat S3.J.6–S3.J.11 for an arbitrary starting stage
  and show the resulting chain is still a candidate.
- [ ] **S3.J.13 — arbitrary-chain upper bounds (critical).** Seek persistent markers of strict
  candidate consolidation and apply S3.A.8. If an `ω₁` argument remains necessary, isolate its
  stabilization-point recursion and countability contradiction in a standalone theorem.
- [ ] **S3.J.14 — illfounded endpoint preservation.** Prove consolidation carries cofinal
  alternating `N+`/`N-` sequences to an illfounded bicomparable image. Use quasifoundedness
  to rule out principal points beyond that image, obtaining the actual endpoint property.
- [ ] **S3.J.15 — consolidated chain.** Apply the Zorn wrapper to candidate objects and record the
  final chain together with alternating maximality and every bicomparability invariant needed by
  illfounded gluing.

### Phase K — maximal tube and final assembly

- [ ] **S3.K.1 — finite-incomparability thickening.** In `Final/TubeFromChain.lean`, define
  `finiteIncompHull C = {x | (incomparableSet x ∩ C).Finite}`; prove `C` is contained in it and that
  tubehood implies maximality.
- [ ] **S3.K.2 — convexity of incomparability traces.** Prove the trace on a chain is an interval.
  Develop endpoint lemmas only under an explicit nonempty hypothesis.
- [ ] **S3.K.3 — ordered finite traces.** For an increasing cover sequence in the thickening, prove
  monotonicity of the lower and upper endpoints of nonempty traces, no-gap properties, and separate
  lemmas for empty traces.
- [ ] **S3.K.4 — extract the witness sequence.** From an infinite incomparability set, use FAC,
  atomic existence, and vacillation to obtain an increasing or decreasing saturated cover sequence.
- [ ] **S3.K.5 — contradiction consolidation (high).** Show the union of its finite traces is
  either finite or has an `ω`-tail; in both cases replace it by a saturated chain through the witness
  sequence and construct a nontrivial consolidation.
- [ ] **S3.K.6 — maximal tube around a consolidated chain.** Conclude the thickening is a tube and
  hence a maximal tube, proving `lem:f-finite-incomparability`.
- [ ] **S3.K.7 — quasifounded case.** Combine the alternating-maximal and consolidated-chain
  theorems to obtain a maximal tube with the upper/lower bicomparability data required by
  `Illfounded.Reduction`.
- [ ] **S3.K.8 — scattered case.** Apply illfounded-gap gluing to obtain a maximal tube in every
  countable scattered vacillating FAC poset.
- [ ] **S3.K.9 — general case.** Apply the completed structural reduction to prove
  `exists_maximalTube` for every countable vacillating FAC poset.
### Phase L — verification and trust audit

- [ ] **S3.L.1 — module builds.** Build each phase's terminal module independently, then run
  `lake build` from a clean state.
- [ ] **S3.L.2 — sorry audit.** Confirm there are no `sorry` declarations in Stage 3 or its
  preliminary dependencies. Any retained Hausdorff or Zaguia input must be a named external axiom
  with a precise mathematical statement, not `sorry` or a placeholder conclusion.
- [ ] **S3.L.3 — axiom audit.** Run `#print axioms` on `exists_maximalTube` and `main_theorem`.
  `exists_maximalTube` should use only standard Lean axioms plus an explicitly retained Hausdorff
  input; `main_theorem` may additionally use the documented Zaguia input.
- [ ] **S3.L.4 — API audit.** Check that files after `Completion/Representatives.lean` never unfold
  the germ setoids or nested representation, and that later replacement files use witness
  composition rather than relying on accidental definitional equality.
- [ ] **S3.L.5 — duality audit.** Confirm every decreasing theorem is derived from, or tested
  against, its increasing counterpart under `OrderDual`.
- [ ] **S3.L.6 — documentation.** Update `README.md` with the final trust boundary and add paper
  labels to all public declarations used in the assembly proof.

## Highest-risk checkpoints

Work should stop for a design review if any of these checkpoints fails; downstream coding would
otherwise amplify the problem.

1. **After S3.C.8:** chain equivalence must have a usable quotient API without choosing minima of
   possibly empty incomparability sets.
2. **After S3.D.12:** domination on normalized `H(P)` must be a genuine partial order and the
   principal constructor must be an order embedding.
3. **After S3.E.11:** completeness and sub-completion embeddings must be usable without unfolding
   quotients. This API is frozen before illfounded work begins.
4. **After S3.G.10:** the illfounded replacement order must have an arbitrary-chain upper-bound
   strategy that is demonstrably formalizable. This is the first test of the reusable Stage 2
   limit architecture.
5. **After S3.H.13:** the alternating quotient order must support Zorn without identifying raw
   maximal chains that merely have the same alternation profile.
6. **After S3.I.12:** consolidation must be well-defined on the exact objects later used as
   candidates; the paper's informal switching between chains, germs, and completion points must no
   longer appear in theorem statements.
7. **After S3.J.13:** sequential consolidation limits and the passage to arbitrary chains must be
   separate checked theorems. Prove the stable germs form a chain before extending them in
   `H(P)`, and prove the principal trace nonempty before extending it in `P`.
8. **Before S3.K.5:** all finite incomparability-set arguments must handle the empty case explicitly.

No individual item above should introduce both a new quotient and a long mathematical proof, or
both a new replacement definition and its Zorn argument. If an item grows beyond that boundary,
split it before continuing.
