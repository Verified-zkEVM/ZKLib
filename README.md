# Formally Verified Cryptographic Arguments

This library aims to provide a modular and composable framework for formally verifying (succinct) cryptographic arguments (e.g. SNARKs) based on Interactive (Oracle) Proofs. This is done as part of the Verified zkEVM project.

In the first stage of this library (until middle of 2025), we plan to formalize interactive (oracle) reductions (a modular way of stating IOPs), and prove information-theoretic completeness and soundness for a select list of protocols.

In particular, we aim to formalize the following:
- IOPs building on univariate polynomials: [Plonk](https://eprint.iacr.org/2019/953.pdf) and [FRI](https://eccc.weizmann.ac.il/report/2017/134/)
- IOPs building on multilinear/multivariate polynomials: the [sum-check protocol](https://dl.acm.org/doi/10.1145/146585.146605), [Spartan](https://eprint.iacr.org/2019/550), and [Ligero](https://eprint.iacr.org/2022/1608).
- Merkle trees as vector commitments, allowing us to carry out the [BCS transform](https://eprint.iacr.org/2016/116.pdf) and turn these protocols into interactive arguments.

For each protocol mentioned above, we aim to provide:

- A specification based on `Mathlib` polynomials,
- An implementation of the prover and verifier using computable representations of polynomials,
- Proofs of completeness and round-by-round knowledge soundness for the specification, and proofs that the implementations refine the specifications.

## Library Structure

The core of our library is a mechanized theory of **$$\mathcal{F}$$-Interactive Oracle Reductions** (see [OracleReduction](ArkLib/OracleReduction)):
1. An **$$\mathcal{F}$$-IOR** is an interactive protocol between a prover and a verifier to reduce a relation $$R_1$$ on some public statement & private witness to another relation $$R_2$$.
2. The verifier may _not_ see the messages sent by the prover in the clear, but can make oracle queries to these messages using a specified oracle interface;
  - For example, one can view the message as a vector, and query entries of that vector. Alternatively, one can view the message as a polynomial, and query for its evaluation at some given points.
3. We can **compose** multiple $$\mathcal{F}$$-IORs with _compatible_ relations together (e.g. $$R_1 \implies R_2$$ and $$R_2 \implies R_3$$), allowing us to build existing protocols (e.g. Plonk) from common sub-routines (e.g. zero check, permutation check, quotienting).
4. We can also carry out the **BCS transform**, which takes an $$\mathcal{F}$$-IOR and compose it with **$$\mathcal{F}$$-commitment schemes** to result in an interactive argument.
  - Roughly speaking, an $$\mathcal{F}$$-commitment scheme is a commitment scheme with an associated opening argument for the correctness of the specified oracle interface.
  - The BCS transform then replaces every oracle message from the prover with a commitment to that message, and runs an opening argument for each oracle query the verifier makes to the prover's messages.
5. For reference, $$\mathcal{F}$$-IOR is a natural notion, and related versions have appeared in various places in the literature (see [References](./References.md) for a detailed comparison). Our library takes these existing threads and formalizes them into a cohesive theory.

Using the theory of $$\mathcal{F}$$-IOR, we then formalize various proof systems in [ProofSystem](ArkLib/ProofSystem).

## Roadmap & Contributing

See the list of issues for immediate tasks and the [ROADMAP](./ROADMAP.md) for long-term projects.

We welcome outside contributions to the library! If you're interested in working on any of the items mentioned in the list of issues or the roadmap, please join the Verified zkEVM Telegram group, contact [the authors](mailto:qvd@andrew.cmu.edu), or open a new issue.
