module

public import Formalism.FrobeniusOrbits.Statement
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

section Hcl

variable {e : ℕ}

theorem hcl_eq_hcl_iff (u v : (ZMod (2 ^ (e + 2)))ˣ) :
    hcl e u = hcl e v ↔ u = v ∨ u = -v := by
  apply Formalism.FrobeniusOrbits.Galois.hcl_eq_iff

theorem hcl_neg (u : (ZMod (2 ^ (e + 2)))ˣ) : hcl e (-u) = hcl e u := by
  unfold hcl
  rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  exact ⟨1, by simp⟩

theorem hcl_one : hcl e (1 : (ZMod (2 ^ (e + 2)))ˣ) = 1 := rfl

theorem hcl_neg_one : hcl e (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 1 := by
  rw [hcl_neg, hcl_one]

end Hcl

section Layer

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

alias hostE_isGalois := _root_.Formalism.FrobeniusOrbits.Galois.isGalois_hostE

alias finrank_cmField := _root_.Formalism.FrobeniusOrbits.Galois.finrank_cmField

private lemma hcl_eq_of_pow_add_inv_pow_eq {M : Type} [Field M] {e : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2)))
    (u v : (ZMod (2 ^ (e + 2)))ˣ)
    (huv : ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val =
      ζ ^ (v : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (v : ZMod (2 ^ (e + 2))).val) :
    hcl e u = hcl e v := by
  rw [hcl_eq_hcl_iff]
  have hz : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ two_ne_zero)
  have hx2 : ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have hy2 : ζ ^ (v : ZMod (2 ^ (e + 2))).val * ζ⁻¹ ^ (v : ZMod (2 ^ (e + 2))).val = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  have key : (ζ ^ (u : ZMod (2 ^ (e + 2))).val - ζ ^ (v : ZMod (2 ^ (e + 2))).val) *
      (ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ ^ (v : ZMod (2 ^ (e + 2))).val - 1) = 0 := by
    linear_combination (ζ ^ (u : ZMod (2 ^ (e + 2))).val * ζ ^ (v : ZMod (2 ^ (e + 2))).val) * huv -
      ζ ^ (v : ZMod (2 ^ (e + 2))).val * hx2 + ζ ^ (u : ZMod (2 ^ (e + 2))).val * hy2
  rcases mul_eq_zero.1 key with h1 | h1
  · left
    have h3 := sub_eq_zero.1 h1
    have hij := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3
    exact Units.ext (ZMod.val_injective _ hij)
  · right
    have h3 : ζ ^ ((u : ZMod (2 ^ (e + 2))).val + (v : ZMod (2 ^ (e + 2))).val) = 1 := by
      rw [pow_add]
      exact sub_eq_zero.1 h1
    have h4 := (hζ.pow_eq_one_iff_dvd _).1 h3
    have h5 := (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).2 h4
    push_cast at h5
    simp only [ZMod.natCast_val, ZMod.cast_id', id] at h5
    apply Units.ext
    rw [Units.val_neg]
    exact eq_neg_of_add_eq_zero_left h5

private lemma zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot {M : Type} [Field M] {e : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2)))
    (x : ZMod (2 ^ (e + 2))) : ζ ^ (-x).val = ζ⁻¹ ^ x.val := by
  have hd : 2 ^ (e + 2) ∣ (-x).val + x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2))]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    exact neg_add_cancel x
  have h1 : ζ ^ ((-x).val + x.val) = 1 := (hζ.pow_eq_one_iff_dvd _).2 hd
  rw [pow_add] at h1
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h1

alias galE_of_lift := _root_.Formalism.FrobeniusOrbits.Galois.galE_lift

theorem galE_snd_eq_hcl_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (u : (ZMod (2 ^ (e + 2)))ˣ) :
    (galE e ζ a b σ).2 = hcl e u ↔
      ((σ (thE ζ a b) : hostE ζ a b) : L) =
        ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val := by
  obtain ⟨τ, hτ⟩ := _root_.Formalism.FrobeniusOrbits.Galois.exists_lift hqd h σ
  have hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val +
        ζ⁻¹ ^ ((h.1.autToPow ℚ τ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))).val := by
    rw [hτ]
    show τ (ζ + ζ⁻¹) = _
    rw [map_add (f := _), map_inv₀, ← h.1.autToPow_spec ℚ τ, inv_pow]
  rw [galE_of_lift h hτ]
  unfold galMap
  dsimp only
  rw [hθ]
  constructor
  · intro hk
    rcases (hcl_eq_hcl_iff _ _).1 hk with h1 | h1
    · rw [h1]
    · rw [h1, Units.val_neg, zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot h.1, zpow_neg_val_eq_inv_pow_val_of_isPrimitiveRoot h.1.inv, inv_inv, add_comm]
  · intro hk
    exact hcl_eq_of_pow_add_inv_pow_eq h.1 _ _ hk

end Layer

end Formalism.FrobeniusOrbits
