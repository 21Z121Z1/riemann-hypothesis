import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.Bundle0004
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0099
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinates
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem flin_pad {K : Type} [Field K] {σ n m : Type} [Fintype n] [Fintype m] {l linv : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) (c : n ⊕ m → K) (u : m → MvPowerSeries σ K) :
    Formalism.L2.Th1.C.flin l linv c (Sum.elim (fun _ => (0 : MvPowerSeries σ K)) u) =
      Formalism.L2.Th1.C.flin l linv (fun j => c (Sum.inr j)) u := by
  unfold Formalism.L2.Th1.C.flin
  congr 1
  rw [Fintype.sum_sum_type]
  simp [hl]

open Formalism.L2.Th1.C in

theorem unitaryInv_rect {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hFr : Frame R l linv ph) (O : Type) [CommRing O] [StarRing O] (τ : O →+* K)
    (hE : ∀ α, EndInt R l linv (τ α)) (hB : ∀ z : O, star z = z → IsBinomScalar R (τ z))
    (hF1 : Formalism.L2.Th1.C.F1 R l linv ph)
    (hN : ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)))
    (hA : ∀ α : O, AdjAt R l linv ph (τ α) (τ (star α)))
    {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (γ : Matrix n m O)
    (hγ : γ.conjTranspose * γ = 1) {σ : Type} (u : m → MvPowerSeries σ K) (hu : ∀ j, IsPt R (u j)) :
    Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (γ i j)) u) ph) (∑ j, PowerSeries.subst (u j) ph) := by
  set P : Matrix n n O := 1 - γ * γ.conjTranspose with hP
  have hPh : P.conjTranspose = P := by
    rw [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPγ : P * γ = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hγ, Matrix.mul_one, sub_self]
  have hγP : γ.conjTranspose * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hγ, Matrix.one_mul, sub_self]
  have hPP : P * P = P := by
    conv_lhs => rw [show P * P = P * (1 - γ * γ.conjTranspose) from rfl]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPγ, Matrix.zero_mul, sub_zero]
  have hΔ : (Matrix.fromBlocks P γ γ.conjTranspose 0).conjTranspose * Matrix.fromBlocks P γ γ.conjTranspose 0 = 1 := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_conjTranspose, hPh, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, hPP, hPγ, hγP, hγ, ← Matrix.fromBlocks_one]
    congr 1
    · rw [hP]; abel
    · simp
    · simp
    · simp
  have hu' : ∀ c : n ⊕ m, IsPt R (Sum.elim (fun _ : n => (0 : MvPowerSeries σ K)) u c) := by
    rintro (c | c)
    · exact ⟨by simp, fun k => by simp⟩
    · exact hu c
  have key := unitaryInv K R l linv ph hFr O τ hE hB hF1 hN hA (n ⊕ m)
    (Matrix.fromBlocks P γ γ.conjTranspose 0) hΔ σ (Sum.elim (fun _ : n => 0) u) hu'
  have hph : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hl : PowerSeries.constantCoeff l = 0 := hFr.1.1
  have hli : PowerSeries.constantCoeff linv = 0 := hFr.1.2.2.1
  simp only [Fintype.sum_sum_type, flin_pad hl, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, map_zero] at key
  have h0 : PowerSeries.subst (flin l linv (fun _ : m => (0 : K)) u) ph = 0 := by
    unfold flin
    simp [hli, hph]
  simpa [hph, h0] using key

theorem HostLog.subst_unitary : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  intro p _ g2 g3 s2 ε σ F hD n m _ _ _ γ hγ hγo Θ hΘ
  classical
  obtain ⟨h5, hg2, hg3, hε, hθ, hU, hF, hN⟩ := hD
  obtain ⟨hFr, hF1, hall, hbin⟩ := Formalism.L2.Th1.Top.CalcC_proof p h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  have hσ : ∀ a : MaximalUnramifiedExtension p, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (Formalism.L2.Th1.D.frobSq (MaximalUnramifiedExtension p) p σ hU).2
  let _ : StarRing (Formalism.L2.Th1.D.BrC.Osub σ) := Formalism.L2.Th1.D.BrC.starO hσ
  let τ : Formalism.L2.Th1.D.BrC.Osub σ →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (Formalism.L2.Th1.D.BrC.Osub σ).subtype
  let γO : Matrix n m (Formalism.L2.Th1.D.BrC.Osub σ) :=
    Matrix.of fun i j => ⟨γ i j, Formalism.L2.Th1.D.BrC.mem_Osub.2 (hγ i j)⟩
  have hun : γO.conjTranspose * γO = 1 := by
    ext a b
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, Matrix.one_apply]
    have h := hγo a b
    have e : ((if a = b then (1 : Formalism.L2.Th1.D.BrC.Osub σ) else 0 : Formalism.L2.Th1.D.BrC.Osub σ) : MaximalUnramifiedExtension p) =
        if a = b then 1 else 0 := by split_ifs <;> rfl
    rw [e, ← h]
    rfl
  set l := Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hl_def
  set linv := Formalism.L2.Th1.D.expF ℂ_[p] p with hlinv_def
  set ph := PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε) with hph_def
  let t : n → MvPowerSeries m ℂ_[p] := fun i =>
    Formalism.L2.Th1.C.flin l linv (fun j => τ (γO i j)) MvPowerSeries.X
  have hpt : ∀ i, Formalism.L2.Th1.C.IsPt (Formalism.G.unitBall ℂ_[p]) (t i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hFr.1 hFr.2.1 (fun j => (hall _ (hγ i j).1 (hγ i j).2).1)
      (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hcc : ∀ i, MvPowerSeries.constantCoeff (t i) = 0 := fun i => (hpt i).1
  have hcong := unitaryInv_rect (Formalism.G.unitBall ℂ_[p]) l linv ph hFr (Formalism.L2.Th1.D.BrC.Osub σ) τ
    (fun α => (hall α.1 α.2.1 α.2.2).1) (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz)) hF1
    (fun α => (hall α.1 α.2.1 α.2.2).2.1) (fun α => (hall α.1 α.2.1 α.2.2).2.2) γO hun
    (MvPowerSeries.X) (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hph0 : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hPh0 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hb0 : ∀ (k : Type) (i : k), MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries k ℂ_[p]) = 0 :=
    fun k i => Formalism.L2.Th1.C.Pts.constantCoeff_subst_l hFr.1 (MvPowerSeries.constantCoeff_X i)
  set Θt : MvPowerSeries n ℂ_[p] := MvPowerSeries.subst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) Θ with hΘt
  have hΘ' : Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) := hΘ
  have hΘe : Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) = Θt := by
    rw [← mul_assoc]
    have := Formalism.L2.Th1.C.mvExp_neg hPh0
    rw [← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq] at this
    rw [this, one_mul]
  obtain ⟨h3, h4, h5'⟩ := Formalism.L2.Th1.E.substExpInt ℂ_[p] n m t hcc (fun i k => (hpt i).2 k)
    (Formalism.L2.Th1.E.phSum ph) _ hPh0 hΘ'
  rw [hΘe, Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h3
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h5'
  have hid : MvPowerSeries.subst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p]))
      (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) =
      MvPowerSeries.subst t Θt := by
    have hb : MvPowerSeries.HasSubst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 m)
    have hb' : MvPowerSeries.HasSubst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 n)
    have hlin : MvPowerSeries.HasSubst
        (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
    have ht : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero hcc
    rw [MvPowerSeries.subst_comp_subst_apply hlin hb, hΘt, MvPowerSeries.subst_comp_subst_apply hb' ht]
    congr 1
    funext i
    rw [Formalism.InvariantFactorPaths.G7.at1, Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) hcc,
      MvPowerSeries.subst_X ht]
    simp only [t, Formalism.L2.Th1.C.flin]
    rw [Formalism.L2.Th1.C.Pts.subst_l_linv hFr.1 (by
      rw [map_sum]
      exact Finset.sum_eq_zero fun j _ => by
        rw [map_mul, show PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m ℂ_[p]) l = Formalism.InvariantFactorPaths.G7.at1 j l from rfl,
          hb0, mul_zero])]
    rw [← MvPowerSeries.coe_substAlgHom hb, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_X hb]
    rw [MvPowerSeries.subst_C]
    rfl
  unfold HostLog
  rw [hid, h3, ← mul_assoc]
  refine Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' ?_ h4
  obtain ⟨hc0, hcI⟩ := Formalism.L2.Th1.C.Calc.cong_symm hcong
  have hA0 : MvPowerSeries.constantCoeff (∑ i : m, Formalism.InvariantFactorPaths.G7.at1 i ph : MvPowerSeries m ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hB0 : MvPowerSeries.constantCoeff (-(∑ i, PowerSeries.subst (t i) ph) : MvPowerSeries m ℂ_[p]) = 0 := by
    rw [map_neg, h5', neg_zero]
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.C.mvExp_add hA0 hB0,
    ← sub_eq_add_neg]
  exact fun k => hcI k

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProof
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.Proof.NarrowJetMoments

namespace GlobalTheory.DatumJets.HidaSetting

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem conj_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hT : Pr.T u ∈ S) (hg : ∀ i, Pr.g i ∈ S) :
    ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  have hTn : ∀ P ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  intro P hP hP'
  rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
  · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
    change cO X.E (Pr.piT u) ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP, cO_cO]
    exact decoFin_mem_of_mem_divs h
  · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
  · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
  · exact conjP_notMem_rowSG hX hPr hsel hg h h'

theorem notMem_Sall (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hd : l ∣ Pr.cond)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Sall sel mu u) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  rcases (mem_Sall sel mu u P).1 hP with h | h
  · intro hm
    have h0 : Pr.piT u ∈ P.asIdeal := decoFin_mem_of_mem_divs h
    have h1 : (l : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hm
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · refine notMem_rowSG hPr hsel hl hS (fun i e => ?_) h
    subst e
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)

theorem qOf_pos (P : HeightOneSpectrum (𝓞 X.E)) : 0 < Formalism.L2.Col.qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem vG_mem_rowSG {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : P ∈ rowSG Pr sel mu := by
  classical
  exact Finset.mem_union.2 (Or.inl (mem_vGs_iff.2 ⟨i, h⟩))

theorem ne_bot_of_locP {E : Type} [Field E] [NumberField E] [StarRing E] {I : Submodule (𝓞 E) E} {P : HeightOneSpectrum (𝓞 E)}
    (h : localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) : I ≠ ⊥ := by
  rintro rfl
  have h1 : (1 : E) ∈ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
    (mem_locP P _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, Submodule.mem_one.2 ⟨1, by simp⟩⟩
  rw [← h] at h1
  obtain ⟨s, hs, hs'⟩ := (mem_locP P _ _).1 h1
  rw [Submodule.mem_bot, smul_eq_zero] at hs'
  rcases hs' with h | h
  · exact hs (h ▸ zero_mem _)
  · exact one_ne_zero h

theorem setting_of_unit (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (i : Fin 2) (u : Pr.Word) (hT : Pr.T u ∈ S)
    (hg : ∀ i, Pr.g i ∈ S) (cst : LocCst X (rowSG Pr sel mu)) (hcst : cst.Ok) (A : Amb X) (a b : ℕ) (hLa : A.LaHyp a b ∅)
    (hE : A.ESmooth a b) (hU : A.AAUnit (Sall sel mu u)) :
    SplitSet A a b (Sall sel mu u) (X.conjO (Pr.piG i)) (Pr.g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ Pr.g i ∣ cBof sel mu cst u := by
  have hc2 : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P₀, hP₀⟩ : (Pr.vG i).Nonempty := Finset.card_pos.1 (hPr.vG_card i ▸ hX.f_pos)
  have hP₀r : P₀ ∈ rowSG Pr sel mu := vG_mem_rowSG hP₀
  have hne : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast this.symm)
  have hprod : 0 < ∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1 := Finset.prod_pos fun P _ => qOf_pos P.1
  obtain ⟨h1, h2, -, -, h5, h6⟩ := hLa
  refine ⟨⟨hX, ⟨h1, h2, conj_notMem hX hPr hsel u hT hg, hU, h5, h6⟩,
    ne_bot_of_locP (hU P₀ ((mem_Sall sel mu u P₀).2 (Or.inr hP₀r))), hE, hPr.g_prime i, ?_, ?_, fun P hP => ?_⟩,
    pow_pos hprod _, Nat.mul_pos (hPr.T_prime u).pos (pow_pos hprod _), ?_⟩
  · rw [hc2, mul_comm]
    exact hPr.piG_norm i
  · rw [hc2]
    exact (hPr.piG_cop i).symm
  · exact (mem_Sall sel mu u P).2 (Or.inr (vG_mem_rowSG (i := i) ((mem_divs hne P).2 hP)))
  · refine Dvd.dvd.mul_left (dvd_pow ?_ (Nat.one_le_iff_ne_zero.1 hcst.B_pos)) _
    have e : Formalism.L2.Col.qOf P₀ = Pr.g i := hPr.vG_norm i P₀ hP₀
    have hd := Finset.dvd_prod_of_mem (fun P : rowSG Pr sel mu => Formalism.L2.Col.qOf P.1)
      (Finset.mem_univ (⟨P₀, hP₀r⟩ : rowSG Pr sel mu))
    beta_reduce at hd
    rw [e] at hd
    exact hd

theorem typePrimeBadPrimesLevelsHypotheses_proof : GlobalTheory.DatumJets.TypePrimeBadPrimesLevelsHypotheses := by
  intro D EX sel δ B χ cD hH hsel i u mu cst hcst a b hLa hE
  obtain ⟨hcc, -, -, hX1, hPr⟩ := hH
  have hT : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hg : ∀ j, (recPrimes EX).g j ∈ badS D := fun j => Or.inl (by fin_cases j <;> simp)
  refine setting_of_unit hX1.ok hPr hsel i u hT hg cst hcst _ a b hLa hE fun P hP => ?_
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  refine GlobalTheory.AAUnitAway.locP_AA D _ (recSeam D) _ δ B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    refine notMem_Sall hPr hsel u hl (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.small_mem_badS D l hs) ?_ hP hlP
    exact ((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _
  · rintro rfl
    refine notMem_Sall hPr hsel u hl (Or.inl (by simp)) ?_ hP hlP
    exact (dvd_mul_left _ _).mul_right _
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.DatumJets.HidaSetting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsAtPlaceOfFrobeniusOrbit
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordBase_of_jumpIn : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i w hw C hG r ρ π ε κ hR hA h2 hq hd hI
  have hU : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) :=
    GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw h2 hq hd
  have hF : Formalism.MainNotions.LocalSituation.fontCore ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) := hA _ _
  obtain ⟨g, hg, hread⟩ := GlobalTheory.T.wachFunctor_letters_inverseFrobenius_orbit D (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ h2 hq hd
    (D.nbr i w hw).j_dense hU
  refine ⟨g, hg, GlobalTheory.T.localFieldDegree_eq_ramification_mul_inertia D.nbr i w hw, ?_, GlobalTheory.T.wordNum_recWord L C₀ (liftIdx D i) ε g _ hR hg⟩
  exact
    { unram := hU
      split := fun ft => GlobalTheory.splits_of_conjugates_mem _ _ _
        (GlobalTheory.good_conjugates_mem _ _ _ 1 hG) ft
      t1 := GlobalTheory.T.lattice_in_sum_twisted_duals_fits_word L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hI hread
      t2 := GlobalTheory.T.lattice_twisted_dual_fits_word_few_small_jumps L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hU hI hread }

end GlobalTheory.HTW.Rec
end

