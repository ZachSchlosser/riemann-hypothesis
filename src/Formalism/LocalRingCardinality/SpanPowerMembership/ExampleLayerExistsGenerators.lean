module

public import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
public import Formalism.DirichletDensity.HostDensityArith
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
public import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSym
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Mathlib.RingTheory.Ideal.NatInt
public import Formalism.CyclotomicNorms.StatementI
public import Mathlib.NumberTheory.LucasPrimality
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.TameInertiaTowers.CentralOrderTwo.Galois

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

-- ===== clump member: Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators =====
-- clump-header: {"m": "Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataHost\npublic import Formalism.LocalRingCardinality.DataSpaces\npublic import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement\npublic import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSym\npublic import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp\npublic import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr\npublic import Formalism.DirichletDensity.HostDensityArith\npublic import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield\npublic import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia\npublic import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff\npublic import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK\npublic import Mathlib.RingTheory.Ideal.NatInt\npublic import Formalism.FrobeniusOrbits.HostCorollaries\npublic import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions\npublic import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq\npublic import Formalism.CyclotomicNorms.StatementI\npublic import Mathlib.NumberTheory.LucasPrimality\npublic import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts\nimport Formalism.TameInertiaTowers.CentralOrderTwo.Galois\nimport Mathlib.Algebra.AffineMonoid.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise

namespace Formalism.BasicNotions.Examples₂

instance instFinitePsi (φ : Formalism.HC.Frame) : Finite ↥(φ.Psi) := inferInstance

instance instFintypePsi (φ : Formalism.HC.Frame) : Fintype ↥(φ.Psi) := Fintype.ofFinite _

alias natCard_Psi := _root_.Formalism.HC.Frame.natCard_Psi

theorem card_Psi (φ : Formalism.HC.Frame) : Fintype.card ↥(φ.Psi) = 2 * φ.ord := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_Psi φ

section Generic

variable {R : Ranks} (H : Host R)

instance instIsCMField : IsCMField H.E := H.isCMField_hostE

instance instIsGalois : IsGalois ℚ H.E := H.hostE_isGalois

instance instTotallyComplex : IsTotallyComplex H.E := inferInstance

theorem cmStar_apply (x : H.E) :
    (letI := H.cmStar; star x) = IsCMField.complexConj H.E x := rfl

theorem emb_star (φ : H.E →+* ℂ) (x : H.E) :
    φ (letI := H.cmStar; star x) = starRingEnd ℂ (φ x) := by
  rw [cmStar_apply]
  exact IsCMField.complexEmbedding_complexConj H.E φ x

theorem emb_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.conjE_apply φ x

theorem star_eq_conj (x : H.E) : (letI := H.cmStar; star x) = H.conj x := by
  apply H.φ₀.injective
  rw [emb_star, emb_conj]

theorem conj_aE : H.conj (H.sqq) = - H.sqq := by
  rw [H.gal_sqq]
  simp [Formalism.HC.HostRaw.conj, Formalism.HC.Frame.cc]
  have hc : ((c0.1 : ℤˣ) : ℤ) = -1 := rfl
  rw [hc]
  simp

theorem conj_bE : H.conj (H.sqd) = - H.sqd := by
  rw [H.gal_sqd]
  simp [Formalism.HC.HostRaw.conj, Formalism.HC.Frame.cc]
  have hc : ((c0.2 : ℤˣ) : ℤ) = -1 := rfl
  rw [hc]
  simp

theorem aE_sq : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq

theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_eq_self_iff (x : H.E) : H.conj x = x ↔ x ∈ H.F := by
  rw [← star_eq_conj, cmStar_apply]
  exact IsCMField.complexConj_eq_self_iff H.E x

def conjF : H.E →ₐ[H.F] H.E :=
  { (H.conj : H.E →+* H.E) with
    commutes' := fun x => by
      show H.conj (x : H.E) = (x : H.E)
      exact (conj_eq_self_iff H x).2 x.2 }

theorem conjF_apply (x : H.E) : conjF H x = H.conj x := rfl

end Generic

section CM

open Polynomial

theorem isIntegral_half {K : Type} [Field K] [CharZero K] (x : K) (k : ℕ)
    (hx : x ^ 2 = -(4 * (k : K) + 3)) : IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨X ^ 2 - X + C ((k : ℤ) + 1), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_natCast, Int.cast_one]
  linear_combination (1 / 4 : K) * hx

variable {R : Ranks} (H : Host R)

theorem q_mod_four : ∃ k : ℕ, H.q = 4 * k + 3 := ⟨H.q / 4, by have := H.hyp.2.2.1; omega⟩
theorem d_mod_four : ∃ k : ℕ, H.d = 4 * k + 3 := ⟨H.d / 4, by have := H.hyp.2.2.2.1; omega⟩

theorem isIntegral_halfB : IsIntegral ℤ ((1 + H.sqd) / 2) := by
  obtain ⟨k, hk⟩ := d_mod_four H
  exact isIntegral_half H.sqd k (by rw [bE_sq H, hk]; push_cast; ring)

theorem conj_half (x : H.E) : H.conj ((1 + x) / 2) = (1 + H.conj x) / 2 := by
  rw [map_div₀, map_add (f := _), map_one, map_ofNat]

theorem unram_at (P : Ideal (𝓞 H.E)) (hP : P.IsMaximal) :
    ∃ θ t : 𝓞 H.E, algebraMap (𝓞 H.E) H.E t = H.conj (algebraMap (𝓞 H.E) H.E θ) ∧ θ - t ∉ P := by
  have h := H.der.unramEF P hP.isPrime (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField H.E))
  push Not at h
  obtain ⟨x, hx⟩ := h
  refine ⟨x, H.conj • x, rfl, fun h1 => hx ?_⟩
  rw [← neg_sub]
  exact P.neg_mem h1

theorem cmData : @CMData H.F H.E _ _ _ _ H.cmStar _ := by
  let _ := H.cmStar
  exact
  { cmUnram := ⟨inferInstance, emb_star H, fun P hP => by
      obtain ⟨θ, t, h1, h2⟩ := unram_at H P hP
      exact ⟨θ, t, by rw [h1, star_eq_conj], h2⟩⟩
    totReal := inferInstance
    deg2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
    fixed := fun a => by
      rw [star_eq_conj, conj_eq_self_iff]
      exact ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩ }

end CM

end Formalism.BasicNotions.Examples₂
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators =====
