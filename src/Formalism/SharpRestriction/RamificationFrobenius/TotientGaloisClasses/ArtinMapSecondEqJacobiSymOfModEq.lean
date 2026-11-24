module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSym
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.HC.D7

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem jac_congr {x y p : ℕ} (hxy : x ≡ y [MOD p]) : jacobiSym (x : ℤ) p = jacobiSym (y : ℤ) p := by
  rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ)]
  congr 1
  have h : ((x % p : ℕ) : ℤ) = ((y % p : ℕ) : ℤ) := congrArg _ hxy
  simpa [Int.natCast_mod] using h

theorem exists_sign {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (s : ℤˣ) :
    ∃ b : ℕ, Nat.Coprime b p ∧ jacobiSym (b : ℤ) p = (s : ℤ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨1, Nat.coprime_one_left _, by simp [jacobiSym.one_left]⟩
  · have h1 : 1 ≤ p := hp.one_lt.le
    refine ⟨p - 1, ?_, ?_⟩
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.le_of_dvd (by have := hp.two_le; omega) h
      omega
    · have hcast : ((p - 1 : ℕ) : ℤ) = -1 + (p : ℤ) * 1 := by push_cast [h1]; ring
      rw [hcast, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left (-1) p,
        jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hp4]
      simp

theorem ordCompl_eq {l m : ℕ} (hl : l.Prime) (k : ℕ) (hm : ¬ l ∣ m) : ordCompl[l] (l ^ k * m) = m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  have hf : (l ^ k * m).factorization l = k := by
    rw [Nat.factorization_mul (pow_ne_zero _ hl.ne_zero) hm0, Finsupp.add_apply,
      hl.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  rw [hf, Nat.mul_div_cancel_left _ (pow_pos hl.pos _)]

variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH

theorem cop_qd : Nat.Coprime q d := by
  rw [Nat.coprime_primes hH.1 hH.2.1]
  have := hH.2.2.1
  have := hH.2.2.2.1
  omega
theorem q4 : q % 4 = 3 := by
  have := hH.2.2.1
  omega
theorem d4 : d % 4 = 3 := by
  have := hH.2.2.2.1
  omega

end Formalism.HC.D7

end
