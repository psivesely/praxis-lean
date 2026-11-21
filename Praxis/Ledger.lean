import Praxis.Constants
import Mathlib.Algebra.Order.Field.Rat

namespace Praxis

open Praxis.Constants

def choose2 (n : ℕ) : ℚ := (n : ℚ) * ((n : ℚ) - 1) / 2

def ledgerJ (w : ℕ) : ℚ := (w : ℚ) * (L : ℚ) + (w : ℚ) * ((w : ℚ) + 1) / 2

def ledgerE (w : ℕ) : ℚ :=
  (choose2 L1 + choose2 L2 + choose2 LT + (L : ℚ)) * eps_f +
    ledgerJ w * theta + ledgerJ w * eps_f +
    choose2 (L + 3 * w) * eps_f + ((L + 3 * w : ℕ) : ℚ) * eps_f +
    (8 * (w : ℚ) + 8) * eps_f +
    (2 * (L : ℚ) + 4 * (w : ℚ) + 4 * (T : ℚ)) / (N_free : ℚ) +
    4 * (w : ℚ) / 2 ^ 126 + statistical_seed

end Praxis
