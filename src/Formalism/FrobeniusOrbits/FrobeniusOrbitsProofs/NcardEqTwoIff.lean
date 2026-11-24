module

public import Formalism.FrobeniusOrbits.HostThickExists
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Eta

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

theorem cases (g : K ≃ₐ[K⁺] K) : g = 1 ∨ g = IsCMField.complexConj K := by
  classical
  by_contra hne
  push_neg at hne
  have h2 : Nat.card (K ≃ₐ[K⁺] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  haveI : Fintype (K ≃ₐ[K⁺] K) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h2
  have h3 : ({1, IsCMField.complexConj K, g} : Finset (K ≃ₐ[K⁺] K)).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, IsCMField.complexConj K, g,
      (IsCMField.complexConj_ne_one K).symm, hne.1.symm, hne.2.symm, rfl⟩
  have h4 := Finset.card_le_univ ({1, IsCMField.complexConj K, g} : Finset (K ≃ₐ[K⁺] K))
  omega

theorem card_gal : Nat.card (K ≃ₐ[K⁺] K) = 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _

instance isGaloisGroup : IsGaloisGroup (K ≃ₐ[K⁺] K) (𝓞 K⁺) (𝓞 K) :=
  IsGaloisGroup.of_isFractionRing _ _ _ K⁺ K

theorem split_or_inert
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (𝔭 : Ideal (𝓞 K⁺)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    (primesOver 𝔭 (𝓞 K)).ncard = 2 ∨
      ((primesOver 𝔭 (𝓞 K)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 K) = 2) := by
  classical
  have hmax : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭
  obtain ⟨P, hPp, hPl⟩ : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P.LiesOver 𝔭 := by
    first
    | (obtain ⟨Q, hQ⟩ := Ideal.nonempty_primesOver (S := 𝓞 K) 𝔭; exact ⟨Q, hQ.1, hQ.2⟩)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P
  have hin : P.inertia (K ≃ₐ[K⁺] K) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rcases cases K g with h | h
    · exact h
    · exfalso
      subst h
      exact hunr P hPp hP0 (fun x => hg x)
  have h1 := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := K ≃ₐ[K⁺] K) 𝔭 P
  rw [hin, Subgroup.card_bot, mul_one, card_gal K] at h1
  rw [Ideal.inertiaDegIn_eq_inertiaDeg 𝔭 P (K ≃ₐ[K⁺] K)]
  have hfpos : 0 < P.inertiaDeg (𝓞 K⁺) := Ideal.inertiaDeg_pos P (𝓞 K⁺)
  generalize (𝔭.primesOver (𝓞 K)).ncard = n at h1 ⊢
  generalize P.inertiaDeg (𝓞 K⁺) = f at h1 hfpos ⊢
  have hn : n ≤ 2 := by nlinarith
  interval_cases n
  · omega
  · right; exact ⟨rfl, by omega⟩
  · left; rfl

theorem ncard_eq_two_iff
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥) :
    (primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 2 ↔ IsCMField.complexConj K • P ≠ P := by
  classical
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (P.under (𝓞 K⁺)) (𝓞 K) (K ≃ₐ[K⁺] K)
  have h2 := Ideal.card_stabilizer_eq (G := K ≃ₐ[K⁺] K) (P.under (𝓞 K⁺)) P
  rw [← h2, card_gal K] at h1
  have hmem : ∀ g : K ≃ₐ[K⁺] K, g ∈ MulAction.stabilizer (K ≃ₐ[K⁺] K) P ↔ g • P = P :=
    fun g => MulAction.mem_stabilizer_iff
  constructor
  · intro h hcP
    have hne : MulAction.stabilizer (K ≃ₐ[K⁺] K) P ≠ ⊥ := by
      intro hb
      have hc : IsCMField.complexConj K ∈ MulAction.stabilizer (K ≃ₐ[K⁺] K) P := (hmem _).mpr hcP
      rw [hb, Subgroup.mem_bot] at hc
      exact IsCMField.complexConj_ne_one K hc
    have h3 : Nat.card (MulAction.stabilizer (K ≃ₐ[K⁺] K) P) ≠ 1 :=
      fun h' => hne (Subgroup.card_eq_one.mp h')
    rw [h] at h1
    omega
  · intro hcP
    have hb : MulAction.stabilizer (K ≃ₐ[K⁺] K) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      rcases cases K g with hg1 | hg1
      · exact hg1
      · exfalso
        apply hcP
        rw [← hg1]
        exact (hmem g).mp hg
    rw [hb, Subgroup.card_bot, mul_one] at h1
    exact h1

end CM

end Eta

open Eta

end Formalism.FrobeniusOrbits
