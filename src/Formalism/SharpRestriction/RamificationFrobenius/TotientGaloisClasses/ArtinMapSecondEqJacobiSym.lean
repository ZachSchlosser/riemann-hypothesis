module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

namespace D7

def sgnN {p N : ℕ} (hp : p.Prime) (h : p ∣ N) : (ZMod N)ˣ →* ℤˣ :=
  haveI := Fact.mk hp
  (quadraticChar (ZMod p)).toUnitHom.comp (ZMod.unitsMap h)

theorem unitsMap_val {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (((u : ZMod N).val : ℕ) : ZMod M) := by
  rw [ZMod.unitsMap_def, Units.coe_map]
  show ZMod.castHom h (ZMod M) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

theorem unitsMap_neg_one {M N : ℕ} (h : M ∣ N) : ZMod.unitsMap h (-1) = -1 := by
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map]
  show ZMod.castHom h (ZMod M) (-1) = -1
  rw [map_neg, map_one]

theorem sgnN_val {p N : ℕ} [NeZero N] (hp : p.Prime) (h : p ∣ N) (u : (ZMod N)ˣ) :
    ((sgnN hp h u : ℤˣ) : ℤ) = jacobiSym (((u : ZMod N).val : ℕ) : ℤ) p := by
  have := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← unitsMap_val h u]
  exact MulChar.coe_toUnitHom _ _

theorem gs_act {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime] {x : K} (hx : x ^ p = 1) (σ : K →+* K)
    (v : ℕ) (hσ : σ x = x ^ v) (hv : Nat.Coprime v p) :
    σ (Cond.gs p hx) = ((jacobiSym (v : ℤ) p : ℤ) : K) * Cond.gs p hx := by
  set w : (ZMod p)ˣ := ZMod.unitOfCoprime v hv with hw
  have hwv : (w : ZMod p) = (v : ZMod p) := ZMod.coe_unitOfCoprime v hv
  have hψ : ∀ a : ZMod p, σ (AddChar.zmodChar p hx a) = AddChar.zmodChar p hx ((w : ZMod p) * a) := by
    intro a
    rw [AddChar.zmodChar_apply, map_pow, hσ, ← pow_mul]
    have : (w : ZMod p) * a = (((v * a.val : ℕ)) : ZMod p) := by
      push_cast; rw [hwv, ZMod.natCast_zmod_val]
    rw [this, AddChar.zmodChar_apply']
  have hχ : ∀ a : ZMod p, σ (Cond.chi p K a) = Cond.chi p K a := by
    intro a; simp [Cond.chi, MulChar.ringHomComp_apply]
  have h1 : σ (Cond.gs p hx) = gaussSum (Cond.chi p K) (AddChar.mulShift (AddChar.zmodChar p hx) (w : ZMod p)) := by

    simp only [Cond.gs, gaussSum, map_sum, map_mul, hψ, hχ, AddChar.mulShift_apply]
  have h2 := gaussSum_mulShift (Cond.chi p K) (AddChar.zmodChar p hx) w
  have h3 : Cond.chi p K (w : ZMod p) = ((jacobiSym (v : ℤ) p : ℤ) : K) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, hwv]
    rfl
  have h4 : jacobiSym (v : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa using hv)
  have h5 : ((jacobiSym (v : ℤ) p : ℤ) : K) ^ 2 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) h4
  rw [h3, ← h1] at h2
  have h6 : Cond.gs p hx = ((jacobiSym (v : ℤ) p : ℤ) : K) * σ (Cond.gs p hx) := h2.symm
  linear_combination (-σ (Cond.gs p hx)) * h5 - ((jacobiSym (v : ℤ) p : ℤ) : K) * h6

theorem sqrt_act {p N : ℕ} [NeZero N] (hp : p.Prime) (hp4 : p % 4 = 3) (h : p ∣ N) (u : (ZMod N)ˣ)
    (τ : Cond.Cyc N ≃ₐ[ℚ] Cond.Cyc N) (hτ : ∀ w : Cond.Cyc N, w ^ N = 1 → τ w = w ^ (u : ZMod N).val)
    (y : Cond.Cyc N) (hy : y ^ 2 = -(p : Cond.Cyc N)) :
    τ y = (((sgnN hp h u : ℤˣ) : ℤ) : Cond.Cyc N) * y := by
  have := Fact.mk hp
  have hx := Cond.prim_pow (N := N) h
  have hxN : (Cond.z N ^ (N / p)) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, (Cond.z_spec N).pow_eq_one, one_pow]
  have hg := gs_act hx.pow_eq_one (τ : Cond.Cyc N →+* Cond.Cyc N) _ (hτ _ hxN)
    ((ZMod.val_coe_unit_coprime u).coprime_dvd_right h)
  rw [sgnN_val]
  have hsq : y ^ 2 = Cond.gs p hx.pow_eq_one ^ 2 := by rw [hy, Cond.gs_sq hp4 hx]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
  · rw [h1]; exact hg
  · rw [h1, map_neg, mul_neg]; exact congrArg Neg.neg hg

variable (φ : Frame) (hinj : Function.Injective φ.h)

section Art

variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)

theorem sgnN_neg_one {p N : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (h : p ∣ N) : sgnN hp h (-1) = -1 := by
  have := Fact.mk hp
  apply Units.ext
  have h1 : ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) = -1 := by
    rw [unitsMap_neg_one]; rfl
  have h2 : ((sgnN hp h (-1) : ℤˣ) : ℤ) = quadraticChar (ZMod p) ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) :=
    MulChar.coe_toUnitHom _ _
  rw [h2, h1, quadraticChar_neg_one (Cond.ringChar_ne_two hp4), ZMod.card, ZMod.χ₄_nat_three_mod_four hp4]
  rfl

variable {e} {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b)

end Art

variable {q d : ℕ} (hH : HostHyp q d) (he : 2 ≤ φ.e) {L : Type} [Field L] [NumberField L] {ζ a b : L}
  (h : IsLayer (φ.e + 2) q d ζ a b)

end D7

end Formalism.HC

end
