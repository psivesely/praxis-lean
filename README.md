# praxis-lean

Lean 4 proofs for the witness encryption scheme of the paper *Praxis: Practical Witness Encryption for NP*, by David
Tse, Nikhil Vanjani, and Psi Vesely. The development formalizes the scheme, with the key derived from the name of
$[\kappa]_T$ (see "Gaps"), at the parameters of the paper's instantiation, with 256-bit messages and seeds, and proves
its correctness and extraction theorems there, and it proves the paper's inverse theorem for every choice of
parameters that meets its conditions. Section 6.4 of the paper describes the formalization. This file lists where each
result lives and, for each assumption and gap that Section 6.4 lists, how it enters Lean, if at all.

## Checking

The development builds with Lean `v4.33.1` and Mathlib `v4.33.1`, pinned in `lean-toolchain` and
`lake-manifest.json`:

```bash
lake exe cache get && lake build
```

The build has no `sorry`. For each theorem in the next section, `#print axioms` lists only `propext`,
`Classical.choice`, and `Quot.sound`.

## Results

| Paper | Lean | File |
|---|---|---|
| Correctness theorem | `Praxis.correctness` | `Praxis/Main.lean` |
| Extraction theorem (b) and (c), and the guessing bound of the extractability-error corollary | `Praxis.extraction` | `Praxis/Main.lean` |
| Extraction theorem (a), in Lean's form | `Praxis.Proofs.Assembly.target_failure_bound` | `Praxis/Proofs/Assembly/Extraction.lean` |
| The coupling of Appendix B.4: the same law on $m_0$ and $m_1$ until the target query | `Praxis.Proofs.Coupling.couple_stopped` | `Praxis/Proofs/Coupling/Stopped.lean` |
| The factor one half | `Praxis.Proofs.Coupling.couple_half` | `Praxis/Proofs/Coupling/Half.lean` |
| Inverse theorem | `Praxis.Lift.liftHolds` | `Praxis/Lift/Final.lean`, with the statement in `Praxis/Lift/Record.lean` |

**Correctness.** `Praxis.correctness ch` states `(scheme ch).Correctness` for every admissible choice `ch` of the
QAP evaluation points at the parameters `Params.main`. For every system `S` of the shape (`InShape`), every witness
`x` of `S` (`IsWitness`), and every message `m`, decryption with `x` of an encryption of `m` returns `m` except with
probability at most $2/q$, with both random oracles uniformly random functions. The statement is over `expGroups`
(`Praxis/Setting.lean`), the three groups represented by their exponents.

**Extraction.** `Praxis.extraction ch` states `(scheme ch).Extraction`, for every system `S` of the shape, every
adversary `A` with `InClass A Q QH`, and all messages `m0` and `m1`. `InClass` bounds every run of `A`: at most
$Q < 2^{100}$ calls to the group oracle, rejected calls included, and at most $Q_H \le 2^{100}$ queries to each
random oracle. The predicate has three parts.

- Running time, the paper's (c): on every input in the support of the experiment, the extractor runs within
  $(2Q+2)(1{,}009{,}044{,}091 + 64|S|) + 32{,}696{,}964{,}025$ counted operations (`WithinUnits`), where $|S|$ is
  `size S` (`Praxis/Relation.lean`), and every draw it makes is from a set of at most $2^{256}$ elements
  (`SmallSamples`).
- The guessing bound: in the extraction experiment (`extractExp`), the probability that `A` guesses the bit and the
  extractor outputs no witness is at most $1/2 + (E(2Q+2) + s_0 + s_1)/2$, and
  $E(2Q+2) \le \min\lbrace (Q+1)/2^{100}, E(2^{101}) \rbrace$. This gives the form of the corollary's bound,
  $1/2 + (Q+1)/2^{101} + (s_0+s_1)/2$. Here $E$ is `ledgerE` (`Praxis/Ledger.lean`); the statement writes
  $E(2^{101})$ as $1 - \delta$, with $\delta$ the constant `Constants.ledger_delta`. And $s_b$ is
  `Scheme.succ S m_b A`, the probability that Lean's reduction for $m_b$ solves its MSIS instance.
- Soundness, the paper's (b): every output of the extractor is a witness of `S`.

**The coupling and extraction (a).** `couple_stopped` is Lean's form of the coupling of Appendix B.4: for each output
bit $o$, the probability that `A` outputs $o$ and never queries the key oracle at the target (`TargetQueried`) is the
same on the run with $m_0$ as on the run with $m_1$. From it, `couple_half` bounds the probability in the extraction
experiment by $1/2 + (f_0 + f_1)/4$, where $f_b$ is the probability, on the run with $m_b$, that `A` queries the key
oracle at the target and the extractor outputs no witness (`ExtFails`). `target_failure_bound` is Lean's form of the
paper's (a), $f_b \le E(2Q+2) + s_b$. It takes the interior results of the proof as hypotheses, each proved under
`Praxis/Proofs`, and the proof of `Praxis.extraction` applies it to their proofs. The form of extraction that
Section 1.1 states, with $2\varepsilon$, follows on paper from `couple_stopped` and (a) (Section 5.4); Lean does not
state that form.

**Inverse theorem.** `liftHolds` proves `LiftHolds`: the statement `VectorInverseZ0Statement` holds for every
`P : CertifiedLiftParameters`, whose fields are the conditions (I1) to (I6) of the inverse theorem. Lean draws $r_i$
uniformly from $\lbrace 0, \dots, G_i - 1 \rbrace$ for any widths $G$ that meet `GridBudget`: $G_i \ge g$,
$\sum_i G_i^2 \le g^2 M$, and $G_i^2 < R_{\mathrm{tr}}^2 g^2 M / 3$, where $M$ is a parameter (the field `S`) and
$R_{\mathrm{tr}}$ is that of (I2). The paper's case is $G_i = g$ with $M = N$ (`gridBudget_main`). As $v_0 = 0$, the
paper's shift to $[2, g+1]$ keeps $\mathrm{gp}(v^\top)$.

## Parameters

`Params.main` (`Praxis/Params.lean`) collects the constants of `Praxis/Constants.lean`. The constants below have every
value of Table 4 except two: messages and seeds have 256 bits in Lean and 100 in Table 4. Table 4's $|\mathcal{H}|$
has no Lean constant, since admissibility quantifies over the evaluation points.

| Table 4 | Lean | Table 4 | Lean |
|---|---|---|---|
| $q$ | `q` | $n$ | `n` |
| $\ell_{\mathsf{lab}}$ | `label_bits` | $c_0$ | `c0` |
| $N$ | `N` | $d_R$ | `ring_degree` |
| $n_{\mathsf{c}}$ | `gates_max` | $k$ | `module_rows` |
| $F_{\max}$ | `products_per_gate_max` | $\ell$ | `module_columns` |
| $\mu$, $\ell_{\mathsf{seed}}$ | `message_bits`, `seed_bits` (256, not 100) | $\beta$ | `eta` |
| $\nu$ | `U` | $K_1$, $K_2$ | `K1`, `K2` |
| $D$ | `D` | $g$ | `g` |
| $J$, $\Delta$ | `M_q`, `E1` | $\theta$ | `theta` |
| $J'$, $\Delta'$ | `W_r`, `U * E1p` | | |

Table 4's $\beta$ is `eta`. The constant `beta` is a different value: a primitive $n$-th root of unity derived from
$c_0$.

## Assumptions

The rows of Table 5 of the paper, "What the theorems and the 100-bit level rest on", with the paper's justification
and how each enters Lean.

| Assumption or result | Paper's justification | In Lean |
|---|---|---|
| Bilinear generic group model | Standard for pairing-based schemes. | Part of the games' definitions in `Praxis/Games.lean`. The group oracle (`groupModel`, `groupImpl`) answers linear combinations (`GQuery.lin`), pairings (`GQuery.pair`), and name requests (`GQuery.name`), with labels from a uniformly random encoding (`sampleEncoding`). An adversary (`Adversary`) is an oracle computation against `AdvModel`. A name request returns an opaque reference (`NameRef` in `Praxis/Keys.lean`), not the two labels of the paper's model; this excludes no adversary, since negating the element takes one call, as the request does, and yields the other label, and the key oracle also accepts the pair (`KdfQuery.guess`, also in `Praxis/Keys.lean`). |
| Discrete logarithm in BN254's $\mathbb{G}_T$ | The best known attack outside that model, about $2^{103}$ by the tower number field sieve. | Not in Lean. Extraction is a statement in the generic model, and neither theorem uses BN254 beyond its group order $q$. |
| Random oracles | The standard heuristic; no query is observed, $H_{\mathsf{key}}$ is never programmed, and $H_{\mathsf{seed}}$ only at one fresh seed, to place an MSIS challenge. | Lazily sampled uniform functions in `Praxis/Games.lean`: `hfLazy` is the paper's $H_{\mathsf{seed}}$ and `kdfLazy` its $H_{\mathsf{key}}$. Only the reductions program $H_{\mathsf{seed}}$, at one fresh seed (`blackBoxRun`, `OracleState.programHF`), and $H_{\mathsf{key}}$ is never programmed. Lean's reductions do read the queries to $H_{\mathsf{key}}$ from a log; see "The paper's bound" below. |
| MSIS hardness | Standard; a worst-case to average-case reduction for suitable parameters. | Not assumed in Lean. The extraction bound keeps the reductions' success probabilities `Scheme.succ` as terms; they are `msisSucc` of `reduction` in `Praxis/Reduction.lean`. |
| Parameters by best known attacks | Standard practice; Section 6.2 of the paper states our reductions' loss. | Outside Lean. Lean fixes the parameters `Params.main` and the constants of `Praxis/Constants.lean`, including $q$, $N = 391{,}693$, $n = 4{,}608$, and $T = 2^{100}$. |
| Universal argument of knowledge | Groth16's knowledge soundness on a universal circuit with an honest setup, a generic-group theorem; and a correct encoding of the verifier (Section 6.1). | Outside Lean. The theorems hold for every system of the shape (`Relation`, `InShape`); neither Groth16's knowledge soundness nor the encoding of its verifier as such a system is checked here. We plan to verify the encoding in a future update. |
| Running time of the lifting step | Polynomial by Lenstra's and Kannan and Bachem's algorithms. | Outside Lean. Lean's reductions convert by exhaustive search (`convertLIFT`, which is `Algebra.Short.bruteForce`). It returns a short multiple exactly when one exists (`bruteForce_none_iff`), as the lifting step does, and Lean states no running time for it. |

## Gaps

The rows of Table 6 of the paper, "What the formalization leaves to the paper, and why", and the further difference
in key derivation that Section 6.4 describes.

| Left to the paper | Paper's reason | In Lean |
|---|---|---|
| Both theorems at other parameters | Lean fixes those of Table 4, with 256-bit messages and seeds, but proves the inverse theorem for all that meet its conditions. | Both theorems fix `Params.main` (see "Parameters" above). They hold for every admissible choice of the QAP evaluation points (`AdmissibleChoice Params.main`); Lean constructs no such choice, and the paper shows one exists (Section 4.4). The inverse theorem holds for all parameters that meet its conditions (`LiftHolds`, over every `CertifiedLiftParameters`). |
| The reductions' running time | Lean counts only an adversary's oracle calls. | Lean counts an adversary's calls (`callCost`, `InClass`), not its computation between them, so it states neither the adversary's running time nor the reductions'. These enter only in the extractability error, and the paper proves the reductions' running time. The extractor is a counted program (`UnitComp`, `WithinUnits` in `Praxis/Units.lean`), so its operations are counted. |
| The paper's bound | Lean proves it for its own reductions. | Lean's reductions (`reduction` in `Praxis/Reduction.lean`) differ from the paper's in two ways. They search exhaustively for the short multiple. Their monitor (`monitor`) reads the queries to $H_{\mathsf{key}}$ from a log (`OracleState.kdfLog`), where the paper's reads none and tries two expressions; it also gives up at a disagreement in $\mathbb{G}_1$ or $\mathbb{G}_2$ (`monNew1`, `monNew2`), stops at the key element's name only if its record of it differs from $\kappa$ (`monKdf`), and reads an unrecorded operand of $\mathbb{G}_1$ or $\mathbb{G}_2$ as zero without recording it (`monOp`). Both proofs use the reductions only at a good first mark, where both versions try the mark's expression except with a probability counted in the term $(Q+1)/2^{100}$; at every other first mark that term pays. Lean's success probabilities may thus differ from the paper's $s_0$ and $s_1$. |
| Faithfulness of the definitions | Checked by reading, as for every formalization. | The definitions to read are the scheme (`scheme` in `Praxis/Scheme.lean`, with `Praxis/Enc.lean`, `Praxis/Dec.lean`, and the extractor `extractorC` in `Praxis/ExtractorCounted.lean`), the games (`Praxis/Games.lean`), and the two predicates `Scheme.Correctness` and `Scheme.Extraction` (`Praxis/Main.lean`). Besides Lean's core, Mathlib, and the third-party folders, everything the two statements use is defined in the files directly under `Praxis/` other than `KummerIrr.lean`, in `Praxis/Algebra/Definitions/`, in `Praxis/Algebra/Stmt/Short.lean`, and in `Praxis/Encryption/`. Two modeling choices deserve a reader's check: correctness is stated over `expGroups`, and the extraction experiment encrypts with `encGame`, `encAt`, and `pubView` (`Praxis/Games.lean`), a rendering of encryption with labels that uses the same exponent formulas as `Enc` but that no lemma ties to `Enc`. |
| Key derivation | The formalization predates the paper's derivation of the key from $[\kappa]_T$. | Lean derives the key from the name of $[\kappa]_T$, the unordered pair of the labels of $[\kappa]_T$ and $[-\kappa]_T$ (`ClassName`, `labelName`, and `maskMsg` in `Praxis/Keys.lean`). Correctness is unchanged, as decryption recovers $[\kappa]_T$ exactly before deriving the key. Extraction depends on the derivation only through queries at the key oracle's target. With a label as the target, the monitor's target rule loses a case, and guessing the target costs at most $`Q_H/N_{\mathsf{free}}`$ (`Constants.N_free`), inside the fifth term of $E$, which pays for Lean's guessed names; so the paper proves its bound (a) with the same $E$. |

## Layout

`Praxis/Main.lean` holds the two theorems and their predicates. Among the files directly under `Praxis/` are the
scheme, the games, the keys, the QAP and its domain, the ledger, the relations, and the reductions. The folders under
`Praxis/` hold:

- `Algebra`: shared algebraic definitions, polynomial identities, probability, and the inverse theorem's
  infrastructure;
- `Bounds`: numerical and probability bounds, including the ledger's;
- `Combinatorics`: counting and mass inequalities on finite grids, for the inverse theorem;
- `Encryption`: the sorts of the three groups of the generic model, and the primality of BN254's scalar-field order
  $q$;
- `Lift`: the inverse theorem's statement, its parameters, and its proof;
- `Packing`: packing integer vectors into polynomial coefficient vectors, for the reductions;
- `Proofs`: correctness, extraction, the coupling, simulation, the monitor, the reductions, and the final assembly;
- `Semantics`: that counting an adversary's oracle calls leaves its run unchanged.

The folders `VCVio`, `ToMathlib`, `PolyFun`, and `Cslib` hold unchanged files of third-party libraries, with their
notices:

- `VCVio` and `ToMathlib`: [VCVio](https://github.com/Verified-zkEVM/VCVio) at commit
  `bda0be2da973b1304e016589bb794b22ca299f45`;
- `PolyFun`: [PolyFun](https://github.com/Verified-zkEVM/PolyFun) at commit
  `c0c923693fc827a41d17116579a0c16ed4873b19`, a dependency of VCVio;
- `Cslib`: [Cslib](https://github.com/leanprover/cslib) at commit `98e395a701f2027a413ad24729e1a11a6c772eb4`, a
  dependency of PolyFun.

## License

Apache License 2.0; see `LICENSE`. The third-party files are under the same license and keep their own copyright
notices.
