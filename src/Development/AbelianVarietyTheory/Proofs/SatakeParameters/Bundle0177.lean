import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038
import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalSubgroupContainingHyperspecialEqTopUnramif
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormalHyp

theorem unip_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → ∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N := by
  intro L _ _ ϖ σ q n hU N hN hK u hu
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set U := (((u : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hUdef
  obtain ⟨M, hM⟩ := GlobalTheory.UnitarySwap.exists_pow_mem hϖ' U
  let b : Fin n → ℤ := fun i => (M : ℤ) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))
  have hb : ∀ i : Fin n, b i.rev = -b i := by
    intro i
    have := i.isLt
    simp only [b, Fin.val_rev]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσϖ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hpow : ∀ k : ℤ, 0 ≤ k → Valued.v (ϖ ^ k) ≤ 1 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, map_pow]
    exact pow_le_one₀ zero_le hϖ1
  set k := s * u * s⁻¹ with hkdef
  have hkm : (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹) := by
    rw [hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']
  have hI : Formalism.UG.P.fIwasawaInt (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro i j
    rw [hkm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hle : (M : ℤ) ≤ b i - b j := by
        have : (i.val : ℤ) + 1 ≤ j.val := by exact_mod_cast hij
        simp only [b]
        nlinarith
      have e : ϖ ^ b i * U i j * (ϖ ^ b j)⁻¹ = ϖ ^ (b i - b j - M) * (ϖ ^ M * U i j) := by
        rw [zpow_sub₀ h0, zpow_sub₀ h0, zpow_natCast]
        field_simp
      rw [e, map_mul]
      exact mul_le_one' (hpow _ (by omega)) (hM i j)
    · have e1 : U i i = 1 := hu.2 i
      rw [e1, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ h0), map_one]
    · have e1 : U i j = 0 := hu.1 i j hij
      rw [e1, mul_zero, zero_mul, map_zero]; exact zero_le
  have hkK : k ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ k) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ k) = k := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  have := hN.conj_mem k (hK hkK) s⁻¹
  have e : s⁻¹ * k * s⁻¹⁻¹ = u := by rw [hkdef]; group
  rwa [e] at this

theorem diag_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ t : Formalism.UG.GU σ n, (∀ i j : Fin n, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → t ∈ N := by
  intro L _ _ ϖ σ q n hU N hN hK hu t ht
  have hU' := hU
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU'
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  set T := (((t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTdef
  have hTd : T = Matrix.diagonal (fun i => T i i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h]; exact ht i j h
  have hunit : ∀ i : Fin n, σ (T i i) * T i.rev i.rev = 1 := by
    intro i
    have := congrFun (congrFun (Formalism.UG.P.fIwasawa_mem_un σ t) i) i.rev
    rw [Formalism.UG.P.fIwasawa_gram, Formalism.UG.P.fIwasawa_antiJ, if_pos rfl] at this
    unfold Formalism.UG.P.fIwasawaH at this
    rw [Finset.sum_eq_single i.rev] at this
    · rw [Fin.rev_rev] at this; exact this
    · intro j _ hj
      show σ (T j.rev i) * T j i.rev = 0
      rw [ht j i.rev (fun h => hj h), mul_zero]
    · simp
  have hne : ∀ i, T i i ≠ 0 := by
    intro i h; have := hunit i; rw [h, map_zero, zero_mul] at this; exact zero_ne_one this
  have hv0 : ∀ i, Valued.v (T i i) ≠ 0 := fun i => by simpa using hne i
  let c : Fin n → ℤ := fun i => - WithZero.log (Valued.v (T i i))
  have hvrev : ∀ i, Valued.v (T i.rev i.rev) = (Valued.v (T i i))⁻¹ := by
    intro i
    have := congrArg Valued.v (hunit i)
    rw [map_mul, map_one, hσv] at this
    exact (eq_inv_of_mul_eq_one_right this)
  have hc : ∀ i : Fin n, c i.rev = -c i := by
    intro i
    simp only [c]
    rw [hvrev, WithZero.log_inv]
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ c i) (fun i => by
    rw [map_zpow₀, hσϖ, hc, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hsN : s ∈ N := GlobalTheory.T.uniformizerPowerTorus_mem_normal_unitarySubgroup L ϖ σ q n hU N hN hK hu c hc s hs
  have hvpow : ∀ i, Valued.v (ϖ ^ c i) = Valued.v (T i i) := by
    intro i
    rw [map_zpow₀, hϖ', ← WithZero.exp_zsmul, ← WithZero.exp_log (hv0 i)]
    simp [c]
  have hε : (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => (ϖ ^ c i)⁻¹ * T i i) := by
    rw [Subgroup.coe_mul, Units.val_mul, hs', ← hTdef, hTd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; simp
  have hI : Formalism.UG.P.fIwasawaInt (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro i j
    rw [hε]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, map_mul, map_inv₀, hvpow, inv_mul_cancel₀ (hv0 i)]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]; exact zero_le
  have hkK : s⁻¹ * t ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) = s⁻¹ * t := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  have e : t = s * (s⁻¹ * t) := by group
  rw [e]
  exact N.mul_mem hsN (hK hkK)

theorem borel_eq_diag_mul_unip : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (b : Formalism.UG.GU σ n), Formalism.UG.IsBorelU b → ∃ d u : Formalism.UG.GU σ n, (∀ i j : Fin n, i ≠ j → ((d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧ Formalism.UG.IsUnipU u ∧ b = d * u := by
  intro L _ _ σ n b hb
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i => (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)
    (Formalism.UG.P.fSatake_unit_diag hb)
  have hne : ∀ i, (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    intro i h0; have := Formalism.UG.P.fSatake_unit_diag hb i; rw [h0, map_zero, zero_mul] at this; exact zero_ne_one this
  have hu : (((d⁻¹ * b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
        (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Subgroup.coe_mul, Units.val_mul, hd']
  refine ⟨d, d⁻¹ * b, fun i j hij => by rw [hd, Matrix.diagonal_apply_ne _ hij], ⟨fun i j hji => ?_, fun i => ?_⟩, by group⟩
  · rw [hu, Matrix.diagonal_mul, hb i j hji, mul_zero]
  · rw [hu, Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]

open Formalism.UG in
theorem frame {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L} (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) :
    ∃ P ∈ GLint (Fin n) (intL L), cT σ (P : Matrix (Fin n) (Fin n) L) * (J : Matrix (Fin n) (Fin n) L) * P = antiJ L n := by
  obtain ⟨U, rfl⟩ := hJ
  let c := GlobalTheory.UnramDoubleCoset.intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := U
  have hB : cT c B = B := by
    ext i j
    show σ ((B j i : intL L) : L) = (B i j : L)
    exact hh j i
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (GlobalTheory.UnramDoubleCoset.exists_dvd_norm_sub_X hU) hB U.isUnit
  have hu : IsUnit B := U.isUnit
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (by rw [hp]; exact hu)
  obtain ⟨h, hh', eh⟩ := GlobalTheory.UnramDoubleCoset.exists_antiJ_frame hU n
  set K : GL (Fin n) L := bc ι h2.unit with hKdef
  have hK : (K : Matrix (Fin n) (Fin n) L) = (Polynomial.aeval B p).map ι := rfl
  have hJ : ((bc ι U : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = cT σ (K : Matrix (Fin n) (Fin n) L) * K := by
    rw [hK, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp]; rfl
  refine ⟨K⁻¹ * h, mul_mem (inv_mem ⟨_, rfl⟩) hh', ?_⟩
  rw [hJ, Units.val_mul, cT_mul, ← eh, Matrix.mul_one]
  have e1 : cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have e2 : (K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv K
  calc cT σ (h : Matrix (Fin n) (Fin n) L) * cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ (K : Matrix (Fin n) (Fin n) L) * K) * (((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * h)
      = cT σ (h : Matrix (Fin n) (Fin n) L) * (cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L)) * ((K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * h := by
        simp only [Matrix.mul_assoc]
    _ = cT σ (h : Matrix (Fin n) (Fin n) L) * h := by rw [e1, e2, Matrix.mul_one, Matrix.mul_one]

open Formalism.UG in
theorem antiJ_case {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) (N : Subgroup (GU σ n)) (hN : N.Normal) (hK : KU σ n ≤ N) : N = ⊤ := by
  have h2 := unip_mem L ϖ σ q n hU N hN hK
  have h3 := diag_mem L ϖ σ q n hU N hN hK h2
  rw [eq_top_iff]
  intro g _
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.fIwasawa_iwasawa σ hU.1 hU.2.1 g
  obtain ⟨d, u, hd, hu, rfl⟩ := borel_eq_diag_mul_unip L σ n b hb
  exact N.mul_mem (N.mul_mem (h3 d hd) (h2 u hu)) (hK hk)

theorem normal_closure_hyp : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), Formalism.UG.IsUnramInv ϖ σ q → Odd q → J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ N : Subgroup (Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L)), N.Normal → (∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → g ∈ N) → N = ⊤ := by
  intro L _ _ _ ϖ σ q n J hU hq hJ hh N hN hK
  obtain ⟨P, hP, eP⟩ := frame hU hJ hh
  have memφ : ∀ g : Formalism.UG.GU σ n, P * (g : GL (Fin n) L) * P⁻¹ ∈ Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L) := by
    intro g
    simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eP) g.2
  have memψ : ∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), P⁻¹ * (g : GL (Fin n) L) * P ∈ Formalism.UG.GU σ n :=
    fun g => GlobalTheory.InertDoubleCoset.conj_mem_UJ σ eP g.2
  let φ : Formalism.UG.GU σ n →* Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L) :=
    { toFun := fun g => ⟨P * (g : GL (Fin n) L) * P⁻¹, memφ g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hK' : Formalism.UG.KU σ n ≤ N.comap φ := by
    intro k hk
    show φ k ∈ N
    apply hK
    show P * (k : GL (Fin n) L) * P⁻¹ ∈ _
    exact mul_mem (mul_mem hP (Subgroup.mem_subgroupOf.1 hk).2) (inv_mem hP)
  have htop := antiJ_case hU (N.comap φ) (hN.comap φ) hK'
  rw [eq_top_iff]
  intro g _
  have hm : (⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ : Formalism.UG.GU σ n) ∈ N.comap φ := by rw [htop]; trivial
  have e : φ ⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ = g := Subtype.ext (by
    show P * (P⁻¹ * (g : GL (Fin n) L) * P) * P⁻¹ = g
    group)
  rw [← e]
  exact hm

end GlobalTheory.NormalHyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModel
section
noncomputable section

namespace GlobalTheory.ShortModelTie

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.KerInert.BeCob
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.DworkPowerSeriesWeights (Integral)
open GlobalTheory.CurveDictionary (lgF_eq_logF cc_lgF')

theorem X_mul_lU {K : Type} [Field K] [CharZero K] (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.X * Formalism.L2.Th1.B.lU f = f := by
  ext n
  cases n with
  | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]

theorem integral_ps {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem phTie : Formalism.L2.KerInert.BeCob.PhTie := by
  intro l _ g hLT hOk s2 hph
  have hp : l.Prime := Fact.out
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := cc_lgF' _ _
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  set v := vLT hLT with hvdef
  have hvcc : PowerSeries.constantCoeff v = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  set lW := Formalism.L2.Th1.A.logSer g.W with hlWdef
  have hgl : g.l = lW := Formalism.L2.KerInert.Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff lW = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hlW1 : PowerSeries.coeff 1 lW = 1 := (Formalism.L2.Th1.A.logSpec ℂ_[l] g.W).2.1
  have hvl : PowerSeries.subst v lW = PowerSeries.C e⁻¹ * Lc := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  set P := Formalism.L2.Th1.A.wpReg g.W with hPdef
  have hP : Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)) = P := by
    rw [GlobalTheory.CurveDictionary.wpReg_eq, hPdef, GlobalTheory.CurveDictionary.wpReg_eq g.W, (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.1,
      (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.2.1]
  have hneg : ∀ f : PowerSeries ℂ_[l], PowerSeries.subst v (-f) = -PowerSeries.subst v f := fun f => by
    rw [← PowerSeries.coe_substAlgHom hvS, map_neg]
  have hlU1 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW) = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hlW1]
  set U := PowerSeries.subst v (Formalism.L2.Th1.B.lU lW) with hU
  have hψ : psiLT hLT = -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog U := by
    unfold psiLT
    rw [hph]
    unfold Formalism.L2.Th1.B.phW Formalism.L2.Th1.B.phO
    rw [PowerSeries.subst_sub hvS, PowerSeries.subst_add hvS, hneg, PowerSeries.subst_mul hvS,
      PowerSeries.subst_pow hvS, PowerSeries.subst_C, hvl,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
    have hfl : PowerSeries.subst v (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU lW)) = Formalism.L2.Th1.B.fLog U := by
      rw [hU, PowerSeries.subst_def, PowerSeries.subst_def]
      exact Formalism.L2.Th1.B.subst_fLog (fun _ => hvcc) hlU1
    rw [← hfl]
    rfl
  have hFF : phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU Lc) := by
    unfold phFF
    rw [hP]

  have hvU : v * U = PowerSeries.C e⁻¹ * Lc := by
    have h1 : PowerSeries.subst v (PowerSeries.X * Formalism.L2.Th1.B.lU lW) = v * U := by
      rw [PowerSeries.subst_mul hvS, PowerSeries.subst_X hvS]
    rw [← h1, X_mul_lU lW hlW0, hvl]
  have hprod : Formalism.L2.Th1.B.lU Lc = (PowerSeries.C e * Formalism.L2.Th1.B.lU v) * U := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ_[l]))
    rw [X_mul_lU Lc hL0]
    calc Lc = PowerSeries.C e * (PowerSeries.C e⁻¹ * Lc) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hene, map_one, one_mul]
      _ = PowerSeries.C e * (v * U) := by rw [hvU]
      _ = PowerSeries.X * (PowerSeries.C e * Formalism.L2.Th1.B.lU v * U) := by
          rw [show PowerSeries.C e * (v * U) = PowerSeries.C e * ((PowerSeries.X * Formalism.L2.Th1.B.lU v) * U) by
            rw [X_mul_lU v hvcc]]
          ring

  have hex1 : PowerSeries.coeff 1 g.ex = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hinv
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hex, Formalism.L2.G.Pend.coeff_one_l g hOk.2.1, one_mul,
      PowerSeries.coeff_one_X] at h
    exact h
  have hv1 : PowerSeries.coeff 1 v = e⁻¹ := by
    rw [hvdef]
    unfold vLT
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hv0, hex1, one_mul, PowerSeries.coeff_C_mul,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hp.two_le, mul_one]
  have hA : MvPowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hv1, mul_inv_cancel₀ hene]
  have hLU : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU Lc) = 1 := Formalism.L2.Th1.E.Joints.cc_lU hp.two_le
  have hUc : MvPowerSeries.constantCoeff (U : MvPowerSeries Unit ℂ_[l]) = 1 := by
    have h := congrArg PowerSeries.constantCoeff hprod
    rw [hLU, map_mul] at h
    have hA' : PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1 := hA
    rw [hA', one_mul] at h
    exact h.symm
  have hdiff : (psiLT hLT : MvPowerSeries Unit ℂ_[l]) -
      phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      Formalism.L2.Th1.B.fLog (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) := by
    rw [hψ, hFF, hprod, Formalism.L2.Th1.B.ParO.fLog_mul hA hUc]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdiff]; exact Formalism.L2.Th1.B.constantCoeff_fLog hA
  · rw [hdiff]
    show Integral (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog _))
    rw [Formalism.L2.Th1.B.fExp_fLog hA]
    apply integral_ps
    intro k
    rw [PowerSeries.coeff_C_mul, norm_mul, he1, one_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]
    exact v_integral hOk hLT (k + 1)

end GlobalTheory.ShortModelTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleConjOfTraceEqual
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceConjWeil

theorem frob_mem_weil {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {σ : G E Ω}
    (hσ : IsFrob A (normV w) σ) : σ ∈ Weil h :=
  ⟨1, 0, hσ.1, fun x hx => by simpa using hσ.2 x hx⟩

theorem dense_frob_prime_to (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] :
    Dense {σ : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧ IsFrob B (normV w) σ} := by
  classical
  rw [dense_iff_inter_open]
  rintro W hW ⟨g, hg⟩
  have hV : IsOpen {s : G E Ω | s * g ∈ W} := hW.preimage (continuous_mul_const g)
  have : IsGalois E Ω := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hg)
  have hl : {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    have h0 : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)})
      (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  obtain ⟨v, hv, -, -, B, hB, -, σ, hσ, hU'⟩ :=
    GlobalTheory.Published.cheb_holds E Ω U.toSubgroup U.isOpen U.isNormal' g hl.toFinset
  have := hU hU'
  simp only [Set.mem_ofPred_eq, inv_mul_cancel_right] at this
  refine ⟨σ, this, v, fun h => hv ?_, B, hB, hσ⟩
  simpa using h

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : Weil h), (r (σ : G E Ω)).val.trace = (r' (σ : G E Ω)).val.trace) → ∃ p : GL (Fin a) (Qbar l), ∀ g, r' g = p * r g * p⁻¹ := by
  intro E Ω _ _ _ _ _ l _ a r r' hr hr' hs hs' ht
  refine GlobalTheory.TraceConj.conj_of_trace_eq (G E Ω) (Qbar l) a r r' hs hs' fun g => ?_
  have hc : ∀ ρ : G E Ω →* GL (Fin a) (Qbar l), Continuous ρ →
      Continuous fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace :=
    fun ρ hρ => (Units.continuous_val.comp hρ).matrix_trace
  have hcl : IsClosed {g : G E Ω | ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace} :=
    isClosed_eq (hc r hr) (hc r' hr')
  have hsub : {σ : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧ IsFrob B (normV w) σ} ⊆
      {g : G E Ω | ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace} := by
    rintro σ ⟨w, hw, B, hB, hσ⟩
    exact ht w hw B hB ⟨σ, frob_mem_weil hB hσ⟩
  exact closure_minimal hsub hcl ((dense_frob_prime_to E Ω l).closure_eq ▸ Set.mem_univ g)

end GlobalTheory.TraceConjWeil

end
end

