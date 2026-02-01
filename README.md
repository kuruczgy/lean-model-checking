# Formalizations of some theorems related to model checking.

## AI usage

This repository contains a significant amount of AI written code. Generally I try to write the theorem statements myself, but some proofs are entirely AI written. I believe this is one of the least risky uses of AI: as long as the theorem statement is correct (we are proving what we think we are proving), any possible mistakes made by the AI are caught by Lean's checker.[^1]

[^1]: Unfortunately this is not completely true, arbitrary code execution is possible during compilation using e.g. custom elaborators, and this can be used to bypass kernel typechecking for some constants using various tricks. See:
[[1]](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
[[2]](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/PSA.20about.20trusting.20Lean.20proofs)
[[3]](https://github.com/leanprover/lean4/issues/9160).
I hope that quick code inspection can catch such attacks, as any such code should look very out of place in a proof. I haven't seen any AI attempt any such attack so far, and I hope that AIs will stay aligned enough that they would rather tell the user that they cannot prove a theorem or that it's false, instead of resorting to such techniques.

## Linear Temporal Logic (LTL) to Büchi automaton translation

We prove that for any LTL formula, there exists an equivalent Büchi automaton that accepts the same words.

See [`LTL_NBW_Statement.lean`](./ModelChecking/LTL_NBW_Statement.lean) for the self contained theorem statement (`for_any_LTL_formula_exists_an_equivalent_NBW_statement`), and [`LTL_NBW_Result.lean`](./ModelChecking/LTL_NBW_Result.lean) for the top-level theorem.
