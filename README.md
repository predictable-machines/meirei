# Meirei

> [!WARNING]
> This project is a **work in progress**. APIs, syntax, and internal representations are subject to breaking changes without notice. Use at your own risk.

A Lean 4 library for formally verifying imperative code through shallow embedding.

## Overview

Meirei implements an imperative language as a set of syntax declarations through Lean 4's metaprogramming API. Programs written in Meirei are elaborated into native Lean 4 programs, enabling formal verification through standard Lean proofs rather than requiring a separate verification framework.

Meirei is intended to be used as an intermediate representation (IR) that other high-level programming languages can translate to, in order to prove properties about functions written in high-level code.

> "**Meirei** (命令 in Japanese) means: instruction; order; command."

## Key Insight

By elaborating imperative code to pure functional Lean, we bridge the gap between:
- Imperative functions (including for loops, mutable variables, early exits, exceptions, and effectful calls)
- Theorem proving (proofs about pure functions)

This enables verification of imperative-style code while maintaining Lean's soundness guarantees.

## Code Example

Here is an example of a function written in Meirei:
```
def processOrders(orderAmounts: [int]) : int {
  discountThreshold <- getDiscountThreshold();
  var totalRevenue : int = 0;
  for amount in orderAmounts {
    if (amount > discountThreshold) {
      multiplier <- getDiscountMultiplier();
      recordSale(amount * multiplier);
      totalRevenue = totalRevenue + amount * multiplier;
    } else {
      recordSale(amount);
      totalRevenue = totalRevenue + amount;
    }
  }
  return totalRevenue;
}
```

To see more code examples, check the [Examples/Functions](Meirei/Examples/Functions/) folder.

## Building

Requires Lean 4 (v4.28.0). Run:

```bash
lake build
```
