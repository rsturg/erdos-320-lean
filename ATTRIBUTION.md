# Attribution and contribution record

## Project credits

**Riley Sturgill** commissioned and directed this project and authorized its autonomous research, original Lean development, verification, publication, and technical prize submission. The authenticated publishing account is [`rsturg`](https://github.com/rsturg). Those are the human contributions evidenced by this session. No claim is made that Riley personally wrote or manually checked individual Lean proofs.

**jenw1n (Jensen Kohlmeyer)** is credited as project co-author at Riley's explicit request. No separate mathematical argument, Lean edit, verification, identity confirmation, consent to financial terms, or contribution allocation by Jensen is evidenced in the development record. This team credit must not be interpreted as evidence of any of those specific acts or of prize entitlement.

**OpenAI Codex and its research/proof-development subagents** performed the literature and rules research, original Lean implementation, iterative compilation, statement review, dependency audit, and release preparation under Riley's direction. Agent review is a separate automated checking pass within the same AI-assisted project. It is not represented as independent human review or prize-organizer verification. GitHub publication and commits record when this project's complete source became public; they do not establish an earlier contribution date.

No award split between people is proposed or inferred. The prize's 30% formalizer allocation is conditional on organizer decisions and is distinct from any team allocation.

## Mathematical credits

- **Yanping Luo, Ruiyi Yang, and Keheng Zhu**, *Distinct Harmonic Subset Sums*: the accepted matching upper-bound argument and the complete order-of-magnitude resolution. Their manuscript credits GPT-5.6 Sol Pro for mathematical proof development under human direction and records further AI assistance. The problem site uses the RayYoung/Young account wording; this repository preserves the manuscript's spelling Ruiyi Yang.
- **Sandro Bettin, Loïc Grenié, Giuseppe Molteni, and Carlo Sanna**: the lower-bound construction and full iterated-log growth. This project proves a uniform-depth lower estimate in Lean rather than assuming their theorem.
- **M. N. Bleicher and Paul Erdős**: foundational reciprocal-subsum estimates and prime-denominator methods.
- **Paul Erdős and Ronald Graham**: the original problem reference, *Old and New Problems and Results in Combinatorial Number Theory* (1980), p. 43.

The original mathematical theorem is not claimed as a discovery by Riley, Jensen, or this formalization project. The Lean implementation contains original development and adaptations needed to close the full analytic argument; those do not transfer the original solvers' mathematical credit.

## Software and earlier formalizations

Lean, Mathlib, and the authors of the pinned PrimeNumberTheoremAnd project supply essential trusted infrastructure and proved analysis. All resolved dependencies, revisions, and licenses are recorded in [docs/DEPENDENCIES.md](docs/DEPENDENCIES.md).

Existing Star Fleet, plby, Joachim Neu, and other public developments were researched for scope, priority, and dependency provenance. Their project-specific proof source is not included in this repository. The PNT source is resolved directly from its original licensed upstream Git repository. See [docs/PRIOR_WORK.md](docs/PRIOR_WORK.md) for the comparison and limits of the prior-proof audits.
