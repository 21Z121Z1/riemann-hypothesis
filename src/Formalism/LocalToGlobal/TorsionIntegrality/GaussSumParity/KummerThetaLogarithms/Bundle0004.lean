import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementF
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NormLeInvOfLtOne

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
section
noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension cW wpNum wpDen uSer)

theorem lubin_tate_log_is_artin_hasse : LtLogIsLgF := by
  intro K _ l hl
  ext n
  unfold Formalism.L2.Th1.CM.ltLog lgF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have h1 : 1 < l ^ 2 := by nlinarith
  split_ifs with h
  · have hs := Nat.find_spec h
    rw [Finset.sum_eq_single (Nat.find h)]
    · rw [if_pos hs]
    · intro j _ hj
      rw [if_neg]
      intro hj'
      exact hj (Nat.pow_right_injective h1 (hj'.symm.trans hs))
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      have h2 : Nat.find h < (l ^ 2) ^ Nat.find h := Nat.lt_pow_self h1
      exact Nat.lt_succ_of_lt (lt_of_lt_of_eq h2 hs.symm)
  · symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hj
    exact h ⟨j, hj⟩

namespace FAux

section Maps

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem cW_eq (g2 g3 : K) (k : ℕ) :
    cW g2 g3 k =
      if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
      if 4 ≤ k then
        3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
          ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
      else 0 := by
  unfold cW
  rw [Nat.strongRecOn_eq]
  split_ifs <;> rfl

theorem cW_map (g2 g3 : K) (k : ℕ) : φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_eq, cW_eq (φ g2) (φ g3) k]
    split_ifs with h2 h3 h4
    · rw [map_div₀, map_ofNat]
    · rw [map_div₀, map_ofNat]
    · rw [map_mul, map_div₀, map_mul, map_add, map_sub, map_mul, map_natCast, map_one, map_sum]
      simp only [map_ofNat]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.isLt
      rw [map_mul, ih (m.val + 2) (by omega), ih (k - (m.val + 2)) (by omega)]
    · exact map_zero φ

theorem wpNum_map (g2 g3 : K) : PowerSeries.map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold wpNum
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs
  · exact map_one φ
  · exact cW_map φ g2 g3 _
  · exact map_zero φ

theorem wpDen_map (g2 g3 : K) : PowerSeries.map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold wpDen
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  split_ifs
  · exact map_one φ
  · rw [map_mul, map_neg, map_sub, map_natCast, map_one, cW_map]
  · exact map_zero φ

theorem cc_wpDen (g2 g3 : K) : PowerSeries.constantCoeff (wpDen g2 g3) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold wpDen
  rw [PowerSeries.coeff_mk, if_pos rfl]

variable [CharZero K] [CharZero K']

theorem uSer_map (g2 g3 : K) : PowerSeries.map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  unfold uSer
  rw [map_mul, map_mul, PowerSeries.map_X,
    Formalism.L2.Th1.B.Map.map_inv' φ (by rw [cc_wpDen]; exact one_ne_zero), wpNum_map, wpDen_map]

theorem cc_arg {l : ℕ} (hl : 2 ≤ l) (ε : K) :
    PowerSeries.constantCoeff (PowerSeries.C ε * lgF K l) = 0 := by
  rw [map_mul, Pair.cc_lgF hl, mul_zero]

theorem thetaS_map {l : ℕ} (hl : 2 ≤ l) (g2 g3 ε : K) :
    PowerSeries.map φ (thetaS l g2 g3 ε) = thetaS l (φ g2) (φ g3) (φ ε) := by
  unfold thetaS
  rw [Formalism.L2.Th1.B.Map.map_psubst' φ (cc_arg hl ε), uSer_map, map_mul, PowerSeries.map_C,
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF]

theorem cc_phFF {l : ℕ} (hl : 2 ≤ l) (g2 g3 s2 ε : K) :
    PowerSeries.constantCoeff (phFF l g2 g3 s2 ε) = 0 := by
  have h1 : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C ε * lgF K l)
      (Formalism.L2.Th1.B.sigS (Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW g2 g3)))) = 0 :=
    Pair.cc_ps (τ := Unit) (cc_arg hl ε) (Formalism.L2.Th1.B.Map.cc_sigS _)
  have h2 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU (lgF K l) - 1) = 0 := by
    rw [map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hl, sub_self]
  have h3 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU (lgF K l))) = 0 :=
    Pair.cc_ps (τ := Unit) h2 PowerSeries.constantCoeff_log
  unfold phFF
  rw [map_sub, map_add, map_neg, map_mul, map_pow, h1, h3, cc_arg hl ε]
  simp

end Maps

section Field

variable (l : ℕ) [hl : Fact l.Prime]

theorem norm_coe (x : MaximalUnramifiedExtension l) : ‖(MaximalUnramifiedExtension l).subtype x‖ = ‖x‖ := rfl

theorem model (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) (dK : ℕ) (L : PeriodPair)
    (hsq : Squarefree dK) (h4 : dK % 4 = 3) (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (h5 : 5 ≤ l)
    (hd : ¬ l ∣ dK) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (ι : ℂ ≃+* ℂ_[l]) :
    ∃ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
      (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) := by
  obtain ⟨g2, g3, hg⟩ := h2 dK L hsq h4 hcm l h5 hd ι
  obtain ⟨ε, hε, hε1, hc⟩ := h3 dK L hsq h4 hcm l h5 hd hin ι g2 g3 hg
  refine ⟨⟨g2, hg.1⟩, ⟨g3, hg.2.1⟩, ⟨ε, hε⟩, hg, hε1, fun n => ?_⟩
  have hm := thetaS_map (MaximalUnramifiedExtension l).subtype (l := l) (by omega) ⟨g2, hg.1⟩ ⟨g3, hg.2.1⟩ ⟨ε, hε⟩
  have hn := (hc n).2
  rw [lubin_tate_log_is_artin_hasse ℂ_[l] l (by omega)] at hn
  rw [← norm_coe, ← PowerSeries.coeff_map, hm]
  exact hn

theorem ffs (hF1 : CurveExponentCoboundaryCocycle) (g2 g3 ε : MaximalUnramifiedExtension l) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1)
    (hε : ‖ε‖ = 1) (hth : ∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1)
    (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (hF : IsLawOfLog l F) (s2 : MaximalUnramifiedExtension l)
    (hN : ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) :
    F1 F (cob F (phFF l g2 g3 s2 ε)) ∧ F2 l σ (cob F (phFF l g2 g3 s2 ε)) ∧
      Simeq (MvPowerSeries.C (2 : MaximalUnramifiedExtension l) * phFF l g2 g3 s2 ε)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries (MaximalUnramifiedExtension l)))
          (cob F (phFF l g2 g3 s2 ε))) := by
  have h1 := hF1 (MaximalUnramifiedExtension l) l hσ.1 hσ.2.1 hσ.2.2.1 F hF g2 g3 s2 ε hg2 hg3 hε hth
  have h2 := second_level_of_norm_holds (MaximalUnramifiedExtension l) l σ hσ F hF _ (cc_phFF hσ.1.two_le g2 g3 s2 ε) h1 hN
  exact ⟨h1, h2.1, h2.2.2⟩

theorem exists_root2 : ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  refine kurRoots l (l ^ 2 - 1) (by omega) fun hd => ?_
  have h2 : l ∣ l ^ 2 := dvd_pow_self l two_ne_zero
  have h3 : l ∣ 1 := by
    have := (Nat.dvd_sub h2 hd)
    rwa [Nat.sub_sub_self h1.le] at this
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem exists_pi : ∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  exact IsAlgClosed.exists_pow_nat_eq _ (by omega)

end Field

end FAux

theorem complex_multiplication_field_data : FieldDataCM := by
  intro l _ h5
  obtain ⟨σ, hσ, -⟩ := kurFrob l (by omega)
  refine ⟨σ, hσ, (Formalism.InvariantFactorPaths.G7.Top.lawExists (MaximalUnramifiedExtension l) l hσ.1 hσ.2.2.1).1, ?_⟩
  intro d _ hd
  have hl2 := hσ.1.two_le
  have hd0 : d ≠ 0 := NeZero.ne d
  have h1 : 1 < l ^ d := Nat.one_lt_pow hd0 hσ.1.one_lt
  obtain ⟨ζ, hζ⟩ := kurRoots l (l ^ d - 1) (by omega) (fun hdv => by
    have h2 : l ∣ l ^ d := dvd_pow_self l hd0
    have h3 : l ∣ 1 := by
      have := (Nat.dvd_sub h2 hdv)
      rwa [Nat.sub_sub_self h1.le] at this
    exact hσ.1.one_lt.ne' (Nat.dvd_one.1 h3))
  obtain ⟨om, oms, h1, h2⟩ := trDualExists (MaximalUnramifiedExtension l) l d σ hσ hd ζ hζ
  exact ⟨ζ, om, oms, hζ, h1, h2⟩

theorem ThmAEntryCM_of (hF1 : CurveExponentCoboundaryCocycle) : ThmAEntryCM := by
  intro h2 h3 dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  refine ⟨g2, g3, ε, hg, hε, hth, ?_⟩
  intro σ hσ F hF s2 hN
  obtain ⟨a1, a2, -⟩ := FAux.ffs l hF1 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 hN
  exact thmAEntryOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2

theorem ThmAGaussCM_of (hF1 : CurveExponentCoboundaryCocycle) : ThmAGaussCM := by
  intro h2 h3 dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  refine ⟨g2, g3, ε, hg, hε, hth, ?_⟩
  intro σ hσ F hF s2 hN
  obtain ⟨a1, a2, -⟩ := FAux.ffs l hF1 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 hN
  exact thmAGaussOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2

theorem OneLetterGaussCM_of (hF1 : CurveExponentCoboundaryCocycle) : OneLetterGaussCM := by
  intro h2 h3 dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  refine ⟨g2, g3, ε, hg, hε, hth, ?_⟩
  intro σ hσ F hF s2 hN
  obtain ⟨a1, a2, a3⟩ := FAux.ffs l hF1 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 hN
  exact oneLetterGaussOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2
    (FAux.exists_root2 l) _ a3

theorem KernelCM_of (hF1 : CurveExponentCoboundaryCocycle) : KernelCM := by
  intro h2 h3 dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  refine ⟨g2, g3, ε, hg, hε, hth, ?_⟩
  intro σ hσ F hF s2 hN ν r0 r1 _ om oms
  obtain ⟨a1, a2, -⟩ := FAux.ffs l hF1 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 hN
  have : CompleteSpace (MaximalUnramifiedExtension l) := kurComplete l
  exact kernelOfF l (MaximalUnramifiedExtension l) σ hσ (FAux.exists_root2 l) F hF _ a1 a2 ℂ_[l] (MaximalUnramifiedExtension l).subtype ν r0 r1
    (FAux.norm_coe l) (FAux.exists_pi l) om oms

end Formalism.L2.Th1.D
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.GramMatrixExists
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)

namespace OrbitCoverLemmas

theorem odd_gen {K : Type} [Field K] {l : ℕ} (hl : 2 ≤ l) {ι : Type} [Fintype ι]
    (M : ι → ι → K) (e : K) (w : ι → K) (h : ∀ r, e * w r = ∑ r', M r' r * w r') :
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (M x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K))
        (∑ r, MvPowerSeries.C (w r) * at1 (true, r) (lgF K l)) =
      MvPowerSeries.C e * ∑ r, MvPowerSeries.C (w r) * at1 (true, r) (lgF K l) := by
  have hE := expSpec K l hl
  have hsum0 : ∀ r', MvPowerSeries.constantCoeff
      (∑ r, MvPowerSeries.C (M r' r) * at1 ((true, r) : Bool × ι) (lgF K l)) = 0 := by
    intro r'
    rw [map_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [map_mul, Pair.constantCoeff_inVar_eq_zero _ (Pair.cc_lgF hl), mul_zero]
  obtain ⟨φ, hφdef⟩ : ∃ φ : Bool × ι → MvPowerSeries (Bool × ι) K, φ = fun x : Bool × ι =>
      if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (M x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K) := ⟨_, rfl⟩
  rw [← hφdef]
  have hφ0 : ∀ x, MvPowerSeries.constantCoeff (φ x) = 0 := by
    intro x
    rw [hφdef]
    dsimp only
    split_ifs
    · exact Pair.cc_ps (hsum0 _) hE.1
    · simp
  have hφ : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  rw [Pair.subst_sum hφ, Finset.mul_sum]
  have h1 : ∀ r', MvPowerSeries.subst φ
      (MvPowerSeries.C (w r') * at1 (true, r') (lgF K l)) =
      MvPowerSeries.C (w r') *
        ∑ r, MvPowerSeries.C (M r' r) * at1 (true, r) (lgF K l) := by
    intro r'
    rw [TorusDerivation.subst_C_mul hφ, Pair.subst_single_var hφ]
    congr 1
    have e : φ (true, r') = PowerSeries.subst
        (∑ r, MvPowerSeries.C (M r' r) * at1 (true, r) (lgF K l)) (expF K l) := by
      rw [hφdef]
      exact if_pos rfl
    rw [e, Pair.ps_comp (hsum0 r') hE.1, hE.2.1,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (hsum0 r'))]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← mul_assoc, ← map_mul, h r, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [map_mul]
  ring

theorem iter_sum {K : Type} [Field K] (σ : K →+* K) (k : ℕ) {ι : Type} [Fintype ι] (f g : ι → K) :
    σ^[k] (∑ r, f r * g r) = ∑ r, σ^[k] (f r) * σ^[k] (g r) := by
  have hpw : ∀ x, σ^[k] x = (σ ^ k) x := fun x => by rw [RingHom.coe_pow]
  rw [hpw, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hpw, iterate_map_mul]

end OrbitCoverLemmas

theorem eigenOdd_conj (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K) (hl : 2 ≤ l)
    (ι : Type) [Fintype ι] (om oms : ι → K) (b : K) (c : ι → ι → K)
    (hc : ∀ r r', σ (σ (c r' r)) = c r' r)
    (hact : ∀ r, b * oms r = ∑ r', c r' r * oms r') (s : ZMod d) (hs : s.val % 2 = 1) :
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (σ (c x.2 r)) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)) (zXY l σ om oms s) =
      MvPowerSeries.C (σ^[s.val] b) * zXY l σ om oms s := by
  have hs' : ¬ s.val % 2 = 0 := by omega
  unfold zXY
  rw [if_neg hs']
  refine OrbitCoverLemmas.odd_gen hl (fun r' r => σ (c r' r)) _ _ fun r => ?_
  rw [← iterate_map_mul, hact r, OrbitCoverLemmas.iter_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [InverseCommuting.iter_odd (hc r r') hs']

theorem eigenOdd_plain (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K) (hl : 2 ≤ l)
    (ι : Type) [Fintype ι] (om oms : ι → K) (b : K) (c : ι → ι → K)
    (hc : ∀ r r', σ (σ (c r' r)) = c r' r)
    (hact : ∀ r, b * oms r = ∑ r', σ (c r' r) * oms r') (s : ZMod d) (hs : s.val % 2 = 1) :
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (c x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)) (zXY l σ om oms s) =
      MvPowerSeries.C (σ^[s.val] b) * zXY l σ om oms s := by
  have h := eigenOdd_conj K l d σ hl ι om oms b (fun r' r => σ (c r' r))
    (fun r r' => by rw [hc]) hact s hs
  simpa only [hc] using h

theorem odd_eigenspace : EigenOdd := eigenOdd_plain

namespace OrbitCoverLemmas

def blk {K : Type} [Field K] (lam : K) (k x : Bool) : K :=
  if x = false then (if k = false then 1 else lam) else (if k = false then 2⁻¹ else -lam * 2⁻¹)

theorem blk_gram {K : Type} [Field K] (σ : K →+* K) (lam : K) (h2 : (2 : K) ≠ 0)
    (h : lam * σ lam = -1) (x x' : Bool) :
    ∑ k, blk lam k x * σ (blk lam k x') = if x ≠ x' then 1 else 0 := by
  have s2 : σ 2 = 2 := map_ofNat σ 2
  cases x <;> cases x' <;> simp [blk, map_inv₀, s2]
  · linear_combination h
  · field_simp; linear_combination -h
  · field_simp; linear_combination -h
  · field_simp; linear_combination h

theorem lam_spec {K : Type} [Field K] (σ : K →+* K) (m : ℕ) (hm : 0 < m) (ζ : K)
    (hζ : IsPrimitiveRoot ζ ((2 * m + 1) ^ 2 - 1)) (hσ : σ ζ = ζ ^ (2 * m + 1)) :
    (ζ ^ m) * σ (ζ ^ m) = -1 := by
  have e : (2 * m + 1) ^ 2 - 1 = (m * (2 * m + 2)) * 2 := by
    have : (2 * m + 1) ^ 2 = (m * (2 * m + 2)) * 2 + 1 := by ring
    omega
  have hp : IsPrimitiveRoot (ζ ^ (m * (2 * m + 2))) 2 := by
    have := hζ.pow_of_dvd (p := m * (2 * m + 2)) (by positivity) (by rw [e]; exact Dvd.intro _ rfl)
    rwa [e, Nat.mul_div_cancel_left _ (by positivity)] at this
  have := hp.eq_neg_one_of_two_right
  rw [map_pow, hσ, ← this]; ring

theorem norm_two {K : Type} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (h : ‖((2 * m + 1 : ℕ) : K)‖ < 1) : ‖(2 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one K 2
    simpa using this
  refine le_antisymm h2 ?_
  by_contra hlt
  rw [not_le] at hlt
  have hm : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  have e : (1 : K) = ((2 * m + 1 : ℕ) : K) + -(2 * (m : K)) := by push_cast; ring
  have h1 : ‖(1 : K)‖ < 1 := by
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h ?_)
    rw [norm_neg, norm_mul]
    calc ‖(2 : K)‖ * ‖(m : K)‖ ≤ ‖(2 : K)‖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  rw [norm_one] at h1
  exact lt_irrefl _ h1

end OrbitCoverLemmas

theorem gram_matrix_exists : GramExists := by
  intro K _ _ _ l σ hU hζ E _ _
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨hp, hl2, hnl, -, -⟩ := id hU
  obtain ⟨m, rfl⟩ : ∃ m, l = 2 * m + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hm : 0 < m := by omega
  have hσζ : σ ζ = ζ ^ (2 * m + 1) := teichSigma K _ 2 σ hU (by norm_num) ζ hζ.pow_eq_one
  have hN0 : (2 * m + 1) ^ 2 - 1 ≠ 0 := by
    have : 1 < (2 * m + 1) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσζ, map_pow, hσζ, ← pow_mul, ← sq]
    have e : (2 * m + 1) ^ 2 = ((2 * m + 1) ^ 2 - 1) + 1 := by omega
    rw [e, pow_succ, hζ.pow_eq_one, one_mul]
  have hlam := OrbitCoverLemmas.lam_spec σ m hm ζ hζ hσζ
  have n2 : ‖(2 : K)‖ = 1 := by
    refine OrbitCoverLemmas.norm_two m ?_
    rw [hnl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have nlam : ‖ζ ^ m‖ = 1 := by rw [norm_pow, nζ, one_pow]
  have s2 : σ 2 = 2 := map_ofNat σ 2
  have hblk : ∀ k x : Bool, ‖OrbitCoverLemmas.blk (ζ ^ m) k x‖ ≤ 1 ∧
      σ (σ (OrbitCoverLemmas.blk (ζ ^ m) k x)) = OrbitCoverLemmas.blk (ζ ^ m) k x := by
    intro k x
    cases k <;> cases x <;> simp [OrbitCoverLemmas.blk, nlam, hσσ, n2, s2, map_inv₀]
  refine ⟨fun k x => if k.2 = x.2 then OrbitCoverLemmas.blk (ζ ^ m) k.1 x.1 else 0, fun k x => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hblk _ _
    · simp
  · rintro ⟨b, e⟩ ⟨b', e'⟩
    rw [Fintype.sum_prod_type]
    dsimp only
    by_cases h : e = e'
    · subst h
      have h3 : ∀ k : Bool, ∑ y : E, (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b else 0) *
          σ (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b' else 0) =
          OrbitCoverLemmas.blk (ζ ^ m) k b * σ (OrbitCoverLemmas.blk (ζ ^ m) k b') := by
        intro k
        rw [Finset.sum_eq_single e]
        · simp
        · intro y _ hy
          simp [hy]
        · simp
      simp only [h3]
      rw [OrbitCoverLemmas.blk_gram σ _ h2 hlam]
      simp
    · rw [if_neg (fun h' => h h'.2)]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y = e
      · have : ¬ y = e' := fun h' => h (hy ▸ h')
        simp [this]
      · simp [hy]

end Formalism.L2.Th1.D
end
end

