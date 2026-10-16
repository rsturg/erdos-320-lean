# Earlier formalizations and prize-priority disclosure

Research was performed before original proof development. The following records public evidence checked on 2026-10-16 UTC. It distinguishes source existence and proof checking from prize acceptance.

## Earlier complete-looking sources

- [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos320.lean), selected commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, has a full two-sided target. Its exact revision is publicly corroborated by the earlier [awards PR 1421](https://github.com/TheJustinSunPrize/awards/pull/1421) and repeated in [PR 3934](https://github.com/TheJustinSunPrize/awards/pull/3934). Both registrations are by people disclaiming authorship of that proof. Static inspection is not reported as a clean build of the plby project.
- [Star Fleet](https://www.starfleetmath.com/) supplies a [complete verification bundle](https://www.starfleetmath.com/downloads/verify/erdos-320/erdos-320-solution.zip) with target `ResearchPNT.exists_two_sided_full_product_estimate`. The downloaded archive SHA-256 is `b6fcf44a079068a39343018a31bb47241ea87c7fed591e71ff251c23053e234e`. It asserts a July 11, 2026 date; that date is self-reported and was not independently established from public Git history. Its full stopped-product target was inspected. The exact outcome of the separate reproduction attempt is recorded in [VERIFICATION.md](VERIFICATION.md), without treating the project's own build claims as independent evidence.

Neither project's problem-specific Lean source is included here. This project implements its own finite, analytic, and final proofs. Shared mathematical ideas and licensed upstream dependencies are credited; repository ownership does not establish novelty of the mathematical solution.

## Other submissions

The [Joachim Neu project](https://github.com/joachimneu/distinct-reciprocal-subset-sums) explicitly isolates four additional assumptions. It is relevant prior work but does not, on that basis, meet this project's requirement of no additional unproved mathematical inputs.

The awards repository has related partial or withdrawn submissions: [674](https://github.com/TheJustinSunPrize/awards/pull/674), [724](https://github.com/TheJustinSunPrize/awards/pull/724), [1751](https://github.com/TheJustinSunPrize/awards/pull/1751), [2565](https://github.com/TheJustinSunPrize/awards/pull/2565), [2688](https://github.com/TheJustinSunPrize/awards/pull/2688), and [4450](https://github.com/TheJustinSunPrize/awards/pull/4450). Finite counts or compatible-prime lemmas alone do not prove the full asymptotic statement. The statuses are a research snapshot and can change.

## Eligibility and priority

The catalog at rules snapshot `fd8fa66abb4e21df828fdebc25298e9ad75521bd` listed JSP-000266 as solved, Lean proof No, eligible to claim No, with no recorded candidate or award. The [official process](https://github.com/TheJustinSunPrize/awards/blob/fd8fa66abb4e21df828fdebc25298e9ad75521bd/docs/award-process.md) allows a complete later formalization to be submitted for review, but compares accepted original complete proofs and their corroborated completion history. An unmerged registration does not itself settle eligibility. An earlier author's absence of a claim does not establish forfeiture of source priority.

Earlier complete sources are a serious obstacle to this project's requested formalizer award. This project makes **no claim to be the first complete formalization, no assertion that earlier sources are invalid, and no assertion of entitlement to an award**. The submission asks the committee to review the complete original proof and decide priority and eligibility with the earlier evidence disclosed. The selected completion commit is the first complete verified public release selected by this project, not an artificially earlier partial-development commit.
