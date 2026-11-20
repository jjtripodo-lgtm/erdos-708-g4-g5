# Erdős Problem 708 for four and five moduli: g(4) = 5 and g(5) = 6

A Lean 4 formalization of two exact values of the Erdős–Surányi function g(n) ([Erdős Problem 708](https://www.erdosproblems.com/708)). The lower bounds g(4) ≥ 5 and g(5) ≥ 6 are due to Erdős and Surányi (1959). This repository proves the matching upper bounds g(4) ≤ 5 and g(5) ≤ 6, which complete the exact values, and formalizes both directions. The general question, whether g(n) ≤ 2n, is not addressed.

## Paper and registration

- **Paper.** J. Tripodo, *Sharp finite cases of the Erdős–Surányi interval-product problem: g(4) = 5 and g(5) = 6*, Hexagon preprint [hexagon:2611.00694](https://hexagonmath.org/abs/2611.00694v1) (2026), CC BY 4.0. It gives the written proofs, credits the prior work, and maps each written lemma to its Lean declaration in this repository.
- **Formal verification.** Palomar registry entry [PALOMAR-2026-11-19-000019](https://palomar-registry.org/entry?id=PALOMAR-2026-11-19-000019&version=1), registered at commit [`00fbb23c`](https://github.com/jjtripodo-lgtm/erdos-708-g4-g5/tree/00fbb23c3084daa88ea420aa9c74177127d5283f). Later commits, such as this README edit, change no Lean file and are not part of the registered artifact.

To cite the paper:

```bibtex
@misc{hexagon:2611.00694v1,
  title        = {Sharp finite cases of the Erd{\H{o}}s--Sur{\'a}nyi interval-product problem: $g(4)=5$ and $g(5)=6$},
  author       = {Tripodo, John},
  howpublished = {Hexagon preprint hexagon:2611.00694v1},
  year         = {2026},
  url          = {https://hexagonmath.org/abs/2611.00694v1}
}
```

## Result

Let g(n) be minimal such that, for any n distinct integers at least 2 and any set I of consecutive integers whose length is the largest of them, some g(n) elements of I have a product that the product of the n integers divides ([erdosproblems.com/708](https://www.erdosproblems.com/708)).

`Challenge.lean` states four theorems. It imports only Mathlib:

- `Erdos708.erdos_708.variants.four`: `IsLeast {k | ExactCover 4 k} 5`, that is g(4) = 5 in the source's exact reading.
- `Erdos708.erdos_708.variants.five`: `IsLeast {k | ExactCover 5 k} 6`, that is g(5) = 6 in the same reading.
- `Erdos708.erdos_708.variants.g_four`: `∀ g, IsMinCoveringSize g → g 4 = 5`.
- `Erdos708.erdos_708.variants.g_five`: `∀ g, IsMinCoveringSize g → g 5 = 6`.

`ExactCover n k`: for every injective `m : Fin n → ℕ` with every value at least 2, and every integer start `L`, some `B ⊆ {L, …, L + max m − 1}` with `B.card = k` has a product that `∏ m i` divides.

`HasCoveringSize` and `IsMinCoveringSize` are copied verbatim from the open Formal Conjectures pull request [#4388](https://github.com/google-deepmind/formal-conjectures/pull/4388). They use the at-most reading: a set `A` of `n` naturals at least 2, windows `Finset.Ico m (m + max A)` with `m > 0`, and `B.card ≤ k`.

## Statement audit: exact versus at-most cardinality

The source defines g(n) with |B| = g(n) (exact cardinality). Most later work, including Chen's paper and the open Formal Conjectures pull request [#4388](https://github.com/google-deepmind/formal-conjectures/pull/4388), uses |B| ≤ k (at most). The two readings are not the same in general, so this section explains why they agree for n = 4 and n = 5, and how the proof connects them.

**Why the exact reading fails for large n.** Take A = {2, 3, …, n + 1}. The interval has length n + 1, so no B in it has more than n + 1 elements. Under the exact reading, no k > n + 1 can work for every A. But Erdős and Surányi proved g(n) ≥ (2 − o(1))n. So for large n, no k satisfies the exact reading, and "the least such k" does not exist. A public comment on the [erdosproblems.com forum thread for #708](https://www.erdosproblems.com/forum/thread/708) makes the same observation. For this reason, the general question must use the at-most reading.

**Why the readings agree for n = 4 and n = 5.** n distinct integers that are all at least 2 have largest element at least n + 1. So every interval in the problem has at least n + 1 elements. If some set B of at most n + 1 elements works, add more elements of the interval until B has exactly n + 1 elements. Adding factors keeps the divisibility. So for every k ≤ n + 1, "some B with |B| ≤ k works" and "some B with |B| = k works" are equivalent. Here g(4) = 5 = 4 + 1 and g(5) = 6 = 5 + 1, so both readings give the same values.

**How the proof uses this.** The main development proves the at-most statements, for all integer starts: every interval has a cover with at most 5 (resp. 6) elements, and a specific instance has none with at most 4 (resp. 5). `Adapter.lean` proves the padding step above (`exact_of_bound`, which needs k ≤ n + 1) and gets exact covers with 5 (resp. 6) elements. `Solution.lean` then proves the exact `IsLeast` statements. An exact cover with k elements is an at-most cover with k elements, so no k below the at-most minimum can be an exact cover. This bridge is part of the statement audit, not only an implementation detail: it is the reason the Challenge can state the source's exact reading.

**The Formal Conjectures form.** `FC4388/Bridge.lean` proves `g_four` and `g_five` for the PR #4388 definitions. It enumerates the set `A` in increasing order, applies the at-most bound at the positive start `m`, and maps the cover back to natural numbers. Both lower-bound instances start at positive integers, so they apply directly. Both forms are in the Challenge, so the comparator checks each against its own definitions.

**Other conventions.** The interval may start at any integer, as in [ErSu59]. Erdős's 1992 statement [Er92c] uses positive starts x + 1, …, x + aₙ. The two give the same values: an interval that contains 0 is trivially covered, and a negative interval reflects to a positive one, which changes the products only by a sign. The upper bounds here hold for all integer starts. The two lower-bound instances start at positive integers (5935 and 51).

## Why these values matter

- **They are the first exact values since 1959.** Gallai observed g(2) = 2, and Erdős and Surányi proved g(3) = 4 together with g(n) ≥ n + 1 for all n ≥ 3. No further exact value has been recorded.
- **They show the small-n behaviour.** For n = 2, …, 5 the value is n + 1 at n ≥ 3, although g(n) ≥ (2 − o(1))n for large n. So the extremal behaviour that drives the asymptotic lower bound has not appeared by n = 5. Exact small values give concrete test cases for the conjectured bound g(n) ≤ 2n and for proof methods aimed at it.
- **The upper bounds need real case analysis.** The lower bounds come from explicit instances. The upper bounds must hold for every set of moduli and every window. The proofs are the substantive part (outline below).
- **The statements are machine-checked against two independent formulations.** The Challenge states each value in the source's exact reading and in the at-most reading of the open Formal Conjectures pull request #4388. Mutation tests confirm that the checker rejects altered statements.

## Proof outline

- **Upper bound g(4) ≤ 5** (`Erdos708/UniversalUpper.lean`). If 0 is in the window, {0} is a cover. Otherwise, a finite Hall-matching argument assigns the moduli to distinct multiples in the window, or shows where this fails. A matching of size four or three is completed through the one-defect and matching lemmas. A deficient triple goes through the one-anchor and triple-anchor theorems. The remaining two-point case goes through the combined two-anchor theorem. The proof needs only four distinct moduli in [2, M]; one of them does not have to equal M.
- **Upper bound g(5) ≤ 6** (`Erdos708/Five/`). The proof takes a maximal assignment of the five moduli to multiples in the window and splits by the pattern of shared multiples: (2,2,1), (3,1,1), (3,2), the case with one modulus missing, (4,1), and (5). The (5) case has a squarefree four-prime exception. The (4,1) case uses a witness invariant: only one specific modulus can block the propagation step.
- **Lower bounds** (`Erdos708/Sharpness.lean`, `Erdos708/Five/Sharpness.lean`). Factor arguments, not brute-force enumeration, on the instances {77, 91, 139, 143} with window 5935, …, 6077, and {5, 10, 12, 15, 20} with window 51, …, 70.
- **Statement bridges** (`Adapter.lean`, `Solution.lean`, `FC4388/Bridge.lean`). See "Statement audit" above.

## Verify

Requirements: elan. The toolchain is `leanprover/lean4:v4.35.0-rc2`; Mathlib is pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build Challenge Solution
lake comparator --config comparator.json              # needs bubblewrap
lake comparator --config comparator.json --paranoid   # also runs every bundled external kernel
```

`comparator.json` compares all four theorems and permits only `propext`, `Quot.sound` and `Classical.choice`.

Checks run before release (same toolchain, local sandbox):
- `lake comparator --paranoid`: accepted by Lean default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron.
- Mutation tests, each rejected by the comparator: the value 5 changed to 4 in `four`; `2 ≤ m i` changed to `1 ≤ m i` in `ExactCover`; `g 4 = 5` changed to `g 4 = 6`; `0 < m` changed to `1 < m` in `HasCoveringSize`.
- The PR #4388 file on current Formal Conjectures `main`, with `g_four` and `g_five` added, builds with `--wfail`. A consumer proves the types of those exact declarations from this development.

## Relation to the problem and to the literature

**The question.** Gallai observed g(2) = 2. Erdős and Surányi [ErSu59] proved g(3) = 4 and g(n) ≥ (2 − o(1))n. Erdős asked whether g(n) ≤ (2 + o(1))n, or even g(n) ≤ 2n, and offered a prize [Er92c]. This package does not address that question.

**Lower bounds: Erdős and Surányi (1959).** Theorem IV of [ErSu59] states: for every k ≥ 3 there are k distinct integers and an interval as long as the largest of them in which no k elements have a product divisible by the product of the integers. Their Section 8 gives explicit constructions. So g(n) ≥ n + 1 for n ≥ 3, and in particular g(4) ≥ 5 and g(5) ≥ 6, has been known since 1959.

**Prior work.**
- H. Chen, *Explicit upper bounds for the Erdős–Surányi function g(n)*, [doi:10.5281/zenodo.22267395](https://doi.org/10.5281/zenodo.22267395), repository [chy4pro/erdos-708-explicit-upper-bounds](https://github.com/chy4pro/erdos-708-explicit-upper-bounds). Chen proves general upper bounds of the form g(n) ≤ cn, and gives computed instances for g(4) ≥ 5 and g(5) ≥ 6.
- Formal Conjectures pull request [#4388](https://github.com/google-deepmind/formal-conjectures/pull/4388) (open) states the general problem with the at-most reading, and g(2) = 2 and g(3) = 4.

**What is original and what is reused.**
- The upper bounds g(4) ≤ 5 and g(5) ≤ 6, their proofs and this formalization are original to this project, as far as our literature search shows. Novelty and priority have not been independently established.
- The lower bounds are due to Erdős and Surányi (Theorem IV). The explicit lower-bound instances formalized here come from Chen's work: the g(5) ≥ 6 instance (moduli 5, 10, 12, 15, 20; interval 51, …, 70) is Chen's, and the g(4) ≥ 5 instance (moduli 77, 91, 139, 143; interval 5935, …, 6077) adds the modulus 139 to the three-modulus instance (77, 91, 143) at x = 5934 in Chen's repository.

**Gaps and limitations.**
- Only n = 4 and n = 5. The general question g(n) ≤ 2n stays open.
- Permitted axioms: `propext`, `Quot.sound`, `Classical.choice`.
- No independent human mathematical review.
- 70 of the supporting modules were developed in a private repository and ported here to Lean's module system. One theorem in `Erdos708/Five/Case5.lean` sets `maxHeartbeats 400000`; no proof text was changed in the port.

[ErSu59] P. Erdős and J. Surányi, Megjegyzések egy versenyfeladathoz (Bemerkungen zu einer Aufgabe eines mathematischen Wettbewerbs), Mat. Lapok 10 (1959), 39–48. [PDF](https://old.renyi.hu/~p_erdos/1959-07.pdf).
[Er92c] P. Erdős, Some of my forgotten problems in number theory, Hardy–Ramanujan J. 15 (1992), 34–50. [PDF](https://hrj.episciences.org/125/pdf).

## Provenance

- AI use: the proofs and this formalization were developed with AI assistance (ChatGPT/Codex and Claude), directed by John Tripodo. No independent human mathematical review has taken place. John Tripodo is the responsible maintainer for reported issues and corrections.

## Licence

Apache License 2.0. See `LICENSE`. The definitions `HasCoveringSize` and `IsMinCoveringSize` are copied from Formal Conjectures pull request #4388 (Apache License 2.0).
