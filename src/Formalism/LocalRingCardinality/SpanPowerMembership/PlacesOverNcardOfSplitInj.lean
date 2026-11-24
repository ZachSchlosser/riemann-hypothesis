module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

abbrev AlgC : Type := ↥(algebraicClosure ℚ ℂ)

instance : IsAlgClosed AlgC := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed

theorem mem_algC_of_isIntegral {x : ℂ} (hx : IsIntegral ℚ x) : x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 hx.isAlgebraic

variable {R : Ranks} (H : Host R)

def embOm : H.E →+* AlgC :=
  H.φ₀.codRestrict (algebraicClosure ℚ ℂ).toSubfield (fun x =>
    mem_algC_of_isIntegral ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map
      ((H.φ₀.toRatAlgHom))))

instance algOm : Algebra H.E AlgC := (embOm H).toAlgebra

instance : IsScalarTower ℚ H.E AlgC := IsScalarTower.of_algebraMap_eq (fun x => by
  exact (RingHom.ext_rat (algebraMap ℚ AlgC) ((algebraMap H.E AlgC).comp (algebraMap ℚ H.E)) ▸ rfl))

instance isAlgClosure_om : IsAlgClosure H.E AlgC :=
  IsAlgClosure.mk inferInstance ⟨fun x =>
    (algebraicClosure.isAlgebraic ℚ ℂ |>.isAlgebraic x).tower_top H.E⟩

def toyLocalData (p : ℕ) [Fact p.Prime] : Formalism.GaloisCohomology.LData H.E AlgC p :=
  Classical.choice (Formalism.GaloisCohomology.ldata_nonempty p)

def shaExample (p e : ℕ) : ℚ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    ((Formalism.GaloisCohomology.shaLen (toyLocalData H p) (e : ℤ)).toNat : ℚ)
  else 0

theorem shaExample_nonneg (p e : ℕ) : 0 ≤ shaExample H p e := by
  unfold shaExample; split_ifs <;> positivity

def exampleClassGroupCard : ℕ := ∏ k : Fin 2, (Nat.card (GL (Fin R.r) (ZMod (H.g k)))) ^ R.f

open Polynomial in

open Ideal Polynomial in
theorem placesOver_ncard_of_frob (p : ℕ) [hp : Fact p.Prime] (hpN : ¬ p ∣ H.condN)
    (hF : ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
      IsArithFrobAt ℤ σ P → H.galE σ = 1) :
    (placesOver H.E p).ncard = Module.finrank ℚ H.E := by
  classical
  have := H.hostE_isGalois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, span_singleton_eq_bot]; exact hpZ.ne_zero)
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  obtain ⟨hex, -, -, hin⟩ := H.der.frob p hpN P

  obtain ⟨σF, hσF⟩ := hex
  have hg1 : H.galE σF = 1 := hF P σF hσF
  have hσ1 : σF = 1 := (H.galE_eq_one_iff σF).1 hg1
  subst hσ1
  have hunder : P.under ℤ = span {(p : ℤ)} := (Ideal.LiesOver.over (P := P) (p := span {(p : ℤ)})).symm
  have hcardZ : Nat.card (ℤ ⧸ span {(p : ℤ)}) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hfrob : ∀ x : 𝓞 H.E, x - x ^ p ∈ P := by
    intro x
    have := hσF x
    rw [hunder, hcardZ] at this
    simpa using this

  have hne0 : ∀ I : Ideal (𝓞 H.E), I.LiesOver (span {(p : ℤ)}) → I ≠ ⊥ := by
    rintro I hI rfl
    have h0 : span {(p : ℤ)} = ⊥ := by
      rw [hI.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 H.E))
    exact hpZ.ne_zero (span_singleton_eq_bot.1 h0)
  have hP0 : P ≠ ⊥ := hne0 P hPl
  have hPM : P.IsMaximal := hPp.isMaximal hP0
  let : Field (𝓞 H.E ⧸ P) := Ideal.Quotient.field P
  have : Finite (𝓞 H.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  let : Fintype (𝓞 H.E ⧸ P) := Fintype.ofFinite _
  have hne : (X ^ p - X : (𝓞 H.E ⧸ P)[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hp.out.one_lt
  have hroot : ∀ y : 𝓞 H.E ⧸ P, y ∈ (X ^ p - X : (𝓞 H.E ⧸ P)[X]).roots := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, ← map_pow, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, ← neg_mem_iff, neg_sub]
    exact hfrob x
  have hle : Fintype.card (𝓞 H.E ⧸ P) ≤ p := by
    calc Fintype.card (𝓞 H.E ⧸ P) = (Finset.univ : Finset (𝓞 H.E ⧸ P)).card := rfl
      _ ≤ (X ^ p - X : (𝓞 H.E ⧸ P)[X]).roots.toFinset.card :=
          Finset.card_le_card (fun y _ => Multiset.mem_toFinset.2 (hroot y))
      _ ≤ (X ^ p - X : (𝓞 H.E ⧸ P)[X]).roots.card := Multiset.toFinset_card_le _
      _ ≤ (X ^ p - X : (𝓞 H.E ⧸ P)[X]).natDegree := card_roots' _
      _ = p := Polynomial.natDegree_X_pow_sub_X hp.out.one_lt
  have hnorm : absNorm P = p ^ ((span {(p : ℤ)}).inertiaDeg' P) :=
    absNorm_eq_pow_inertiaDeg' P hp.out
  have hcardk : absNorm P = Fintype.card (𝓞 H.E ⧸ P) := by
    rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← inertiaDeg'_eq_inertiaDeg (span {(p : ℤ)}) P]
    have hpos : 0 < (span {(p : ℤ)}).inertiaDeg' P := by
      rw [inertiaDeg'_eq_inertiaDeg (span {(p : ℤ)}) P]; exact inertiaDeg_pos P ℤ
    have hle' : p ^ (span {(p : ℤ)}).inertiaDeg' P ≤ p ^ 1 := by
      rw [← hnorm, hcardk, pow_one]; exact hle
    have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle'
    omega

  have hinert : Nat.card (P.inertia Gal(H.E/ℚ)) = 1 := by
    have : P.inertia Gal(H.E/ℚ) = ⊥ := by
      ext σ
      rw [AddSubgroup.mem_inertia, Subgroup.mem_bot]
      exact hin σ
    rw [this]; exact Subgroup.card_bot
  have key := ncard_primesOver_mul_card_inertia_mul_finrank (G := Gal(H.E/ℚ)) (span {(p : ℤ)}) P
  rw [hinert, hf, mul_one, mul_one, IsGalois.card_aut_eq_finrank] at key

  rw [← key]
  have himg : (fun v : HeightOneSpectrum (𝓞 H.E) => v.asIdeal) '' placesOver H.E p =
      (span {(p : ℤ)}).primesOver (𝓞 H.E) := by
    ext I
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ⟨?_⟩⟩
      have hle : span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
        rw [span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 H.E) p ∈ v.asIdeal
        have hv' : ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal := hv
        simpa using hv'
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      refine ⟨⟨I, hI, hne0 I hIl⟩, ?_, rfl⟩
      change ((p : ℕ) : 𝓞 H.E) ∈ I
      have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact mem_span_singleton_self _
      simpa using this
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

theorem placesOver_ncard_of_art (p : ℕ) [hp : Fact p.Prime] (hpN : p.Coprime H.condN)
    (hart : H.art (ZMod.unitOfCoprime p hpN) = 1) :
    (placesOver H.E p).ncard = Module.finrank ℚ H.E := by
  refine placesOver_ncard_of_frob H p ((Nat.Prime.coprime_iff_not_dvd hp.out).1 hpN) ?_
  intro P _ _ σ hσ
  rw [(H.frob_iff p hpN P σ).1 hσ, hart]

theorem placesOver_ncard_of_split (p : ℕ) [hp : Fact p.Prime] (hpm : p % H.condN = 1) :
    (placesOver H.E p).ncard = Module.finrank ℚ H.E := by
  have h1 : 1 < H.condN := lt_of_lt_of_le (by norm_num)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero H.condN_ne_zero) H.sixteen_dvd_condN)
  have hmod : p ≡ 1 [MOD H.condN] := by
    unfold Nat.ModEq; rw [hpm, Nat.mod_eq_of_lt h1]
  have hpN : p.Coprime H.condN := Nat.coprime_of_mul_modEq_one 1 (by simpa using hmod)
  refine placesOver_ncard_of_art H p hpN ?_
  have : ZMod.unitOfCoprime p hpN = 1 := by
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_one (R := ZMod H.condN),
      ZMod.natCast_eq_natCast_iff]
    exact hmod
  rw [this, map_one]

end Formalism.BasicNotions.Examples₂
