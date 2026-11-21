import Praxis.Constants

namespace Praxis

structure Params where

  q : ℕ

  N : ℕ

  gatesMax : ℕ

  productsMax : ℕ

  U : ℕ

  D : ℕ

  Mq : ℕ
  Wr : ℕ

  E1 : ℕ
  E1p : ℕ

  n : ℕ
  m : ℕ
  c0 : ℕ

  beta : ℕ

  d : ℕ
  reserved : ℕ

  rows : ℕ
  cols : ℕ

  K1 : ℕ
  K2 : ℕ

  seedBits : ℕ
  messageBits : ℕ
  labelBits : ℕ
  nameBits : ℕ

  g : ℕ

  theta : ℚ

  eta : ℕ

  tBound : ℕ
  deriving DecidableEq, Repr

namespace Params

variable (P : Params)

structure Valid : Prop where
  pos : 0 < P.N ∧ 0 < P.gatesMax ∧ 0 < P.U ∧ 0 < P.n ∧ 0 < P.d ∧ 0 < P.rows ∧ 0 < P.cols ∧
    0 < P.K1 ∧ 0 < P.K2 ∧ 0 < P.Mq ∧ 0 < P.Wr ∧ 0 < P.g
  products : P.productsMax + 1 = P.U
  n_eq : P.n = 2 * P.m
  n_dvd : P.n ∣ P.q - 1
  reserved_eq : P.reserved = P.d
  rows_eq : P.n = P.d * (P.rows + 1)
  cols_ge : P.N ≤ P.cols * P.d
  cols_lt : P.cols * P.d < P.N + P.d
  legs : P.K1 * P.K2 = P.m
  D_eq : P.D = P.N + 2 + P.U * P.gatesMax
  quot_cover : P.D ≤ P.E1 * P.Mq
  rem_cover : P.E1p * P.Wr = P.gatesMax
  U_dvd : P.U ∣ P.q - 1
  g_odd : P.g % 2 = 1
  tBound_eq : P.tBound = (P.N + 1) * (P.g + 1)
  tBound_lt : 2 * P.tBound + 1 < P.q
  label_fit : P.q ≤ 2 ^ P.labelBits
  name_eq : P.nameBits = 2 * P.labelBits

end Params

def Params.main : Params where
  q := Constants.q
  N := Constants.N
  gatesMax := Constants.gates_max
  productsMax := Constants.products_per_gate_max
  U := Constants.U
  D := Constants.D
  Mq := Constants.M_q
  Wr := Constants.W_r
  E1 := Constants.E1
  E1p := Constants.E1p
  n := Constants.n
  m := Constants.m
  c0 := Constants.c0
  beta := Constants.beta
  d := Constants.ring_degree
  reserved := Constants.reserved_coefficients
  rows := Constants.module_rows
  cols := Constants.module_columns
  K1 := Constants.K1
  K2 := Constants.K2
  seedBits := Constants.seed_bits
  messageBits := Constants.message_bits
  labelBits := Constants.label_bits
  nameBits := Constants.name_bits
  g := Constants.g
  theta := Constants.theta
  eta := Constants.eta
  tBound := Constants.dec_ref_t_bound

end Praxis
