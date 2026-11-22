import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0962
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem sig_eq_star (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := by
  have τ0 : D.what₂.Tau := D.eTau.symm 1
  apply (tauE D τ0).injective
  rw [GlobalTheory.FockCompare.tauE_star]
  exact D.sp.cm.cmUnram.2.1 (tauE D τ0) x

theorem cT_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
  refine Matrix.ext fun i j => ?_
  simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  show (D.sp.cm.sig : D.host.E →+* D.host.E) (A j i) = star (A j i)
  exact sig_eq_star _

theorem hRat_eq (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T x y = Matrix.trace (S.gram⁻¹ * yᴴ * T.gram * x) := by
  simp only [GlobalTheory.LatVac.hRat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem hRat_frames (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1)
    (hB' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)
      (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = Matrix.trace (Mᴴ * M) := by
  rw [cT_eq] at hB hB'
  rw [hRat_eq]
  set Bi := (B⁻¹ : GL (Fin S.rank) D.host.E).1 with hBi_def
  have hBi : Bi * B.1 = 1 := by rw [hBi_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSi : S.gram⁻¹ = B.1 * B.1ᴴ := by
    have h1 : B.1 * (B.1ᴴ * S.gram) = 1 := mul_eq_one_comm.1 hB
    have h2 : (B.1 * B.1ᴴ) * S.gram = 1 := by rw [Matrix.mul_assoc]; exact h1
    exact Matrix.inv_eq_left_inv h2
  have hBB : B.1ᴴ * Biᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  calc Matrix.trace (S.gram⁻¹ * (B'.1 * M * Bi)ᴴ * T.gram * (B'.1 * M * Bi))
      = Matrix.trace (B.1 * ((B.1ᴴ * Biᴴ) * (Mᴴ * ((B'.1ᴴ * T.gram * B'.1) * (M * Bi))))) := by
        rw [hSi]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (B.1 * (Mᴴ * (M * Bi))) := by rw [hBB, hB', Matrix.one_mul, Matrix.one_mul]
    _ = Matrix.trace ((Mᴴ * M * Bi) * B.1) := by
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Mᴴ * M) := by rw [Matrix.mul_assoc, hBi, Matrix.mul_one]

theorem embT_sqrt (τ : D.what₂.Tau) :
    embT D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  Formalism.L2.Theta.tauE_sqrtMinusD D τ

theorem embT_ne_conj (τ τ' : D.what₂.Tau) : embT D τ ≠ (starRingEnd ℂ).comp (embT D τ') := by
  intro h
  have h1 := congrArg Complex.im (DFunLike.congr_fun h D.host.sqrtMinusD)
  rw [RingHom.comp_apply, embT_sqrt, embT_sqrt] at h1
  have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  simp at h1
  linarith

theorem trace_split (z : D.host.E) :
    ((Algebra.trace ℚ D.host.E z : ℚ) : ℂ) = ∑ τ : D.what₂.Tau, (embT D τ z + starRingEnd ℂ (embT D τ z)) := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (x := z)
  let e : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →ₐ[ℚ] ℂ) := fun s =>
    RingHom.equivRatAlgHom _ _ (Sum.elim (embT D) (fun τ => (starRingEnd ℂ).comp (embT D τ)) s)
  have he : Function.Bijective e := by
    refine (RingHom.equivRatAlgHom _ _).bijective.comp ⟨?_, fun σ => ?_⟩
    · rintro (a | a) (b | b) hab
      · rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_inj D hab]
      · exact absurd hab (embT_ne_conj a b)
      · exact absurd hab.symm (embT_ne_conj b a)
      · have : embT D a = embT D b := RingHom.ext fun x =>
          (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
        rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_inj D this]
    · obtain ⟨τ, h | h⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D σ
      · exact ⟨Sum.inl τ, h.symm⟩
      · exact ⟨Sum.inr τ, h.symm⟩
  rw [← Fintype.sum_bijective e he (fun s => e s z) (fun σ => σ z) fun _ => rfl, Fintype.sum_sum_type] at h
  rw [show ((Algebra.trace ℚ D.host.E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E z) from rfl, h,
    ← Finset.sum_add_distrib]
  rfl

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem embT_star (τ : D.what₂.Tau) (x : D.host.E) : embT D τ (star x) = starRingEnd ℂ (embT D τ x) :=
  GlobalTheory.FockCompare.tauE_star τ x

theorem absNorm_ne : ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ≠ 0 := by
  have : Ideal.absNorm D.host.ccK ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  exact_mod_cast this

theorem embT_c_add_conj (τ : D.what₂.Tau) :
    embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) +
      starRingEnd ℂ (embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2)) =
      -1 / ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) := by
  have hN := absNorm_ne (D := D)
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D).ne'
  have e : embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) =
      -1 / (((Ideal.absNorm D.host.ccK : ℕ) : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ))) *
        ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) ^ 2 := by
    unfold Formalism.BasicNotions.Host.xi0
    simp only [map_mul, map_div₀, map_neg, map_one, map_natCast, map_pow, map_add, map_ofNat, embT_sqrt]
  rw [e]
  simp only [map_mul, map_div₀, map_neg, map_one, map_pow, map_add, map_natCast, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  field_simp
  ring_nf

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem embT_trace (τ : D.what₂.Tau) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    embT D τ (Matrix.trace (Mᴴ * M)) =
      ((∑ i, ∑ j, Complex.normSq (embT D τ (M i j)) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
    embT_star, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_comm]

theorem k_eq {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (k : ℤ)
    (hk : (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      Matrix.trace (Mᴴ * M))) :
    (k : ℝ) = -(∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
      (Ideal.absNorm D.host.ccK : ℝ) := by
  have h : ((k : ℚ) : ℂ) = ((Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      Matrix.trace (Mᴴ * M)) : ℚ) : ℂ) := by rw [hk]
  rw [trace_split] at h
  have h2 : ∀ τ : D.what₂.Tau,
      embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M)) +
        starRingEnd ℂ (embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M))) =
      -1 / ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) *
        ((∑ i, ∑ j, Complex.normSq (embT D τ (M i j)) : ℝ) : ℂ) := by
    intro τ
    rw [show embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M)) =
        embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) * embT D τ (Matrix.trace (Mᴴ * M)) from
        map_mul _ _ _, embT_trace, map_mul (starRingEnd ℂ), Complex.conj_ofReal, ← add_mul, embT_c_add_conj]
  rw [Finset.sum_congr rfl fun τ _ => h2 τ, ← Finset.mul_sum] at h
  have hN := absNorm_ne (D := D)
  have h3 : ((k : ℝ) : ℂ) = (((-(∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
      (Ideal.absNorm D.host.ccK : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rw [show ((k : ℂ)) = ((k : ℚ) : ℂ) by push_cast; rfl, h]
    field_simp
    simp only [Complex.ofReal_sum]
  exact_mod_cast h3

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem qH_eq {m n : ℕ} (δ : ℂ) (hδ : δ ≠ 0) (M : Matrix (Fin m) (Fin n) D.host.E) :
    Real.sqrt D.host.d / 2 *
      (Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M)).re =
      (∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) / (Ideal.absNorm D.host.ccK : ℝ) := by
  have hA := GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot
  have hH : Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M) =
      (((Complex.normSq δ * ∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
        area (lamOf D D.host.ccK δ) : ℝ) : ℂ) := by
    unfold Hf
    rw [Complex.ofReal_div]
    congr 1
    simp only [embV, tor0, Pi.smul_apply, smul_eq_mul, Complex.mul_conj, Complex.normSq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [hH, Complex.ofReal_re, hA]
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hs := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  have hδ2 : 0 < Complex.normSq δ := Complex.normSq_pos.mpr hδ
  field_simp

theorem al_mul_neg_one_pow : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (k : ℤ), (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) → Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) * (-1 : ℂ) ^ k = 1 := by
  intro D S T B B' hB hB' δ hδ M k hk
  rw [hRat_frames S T B B' hB hB' M] at hk
  have hk' := k_eq M k hk
  have hq := qH_eq δ hδ M
  have hr : Real.sqrt D.host.d / 2 *
      (Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M)).re = ((-k : ℤ) : ℝ) := by
    rw [hq, Int.cast_neg, hk', neg_div, neg_neg]
  unfold al
  rw [hr, round_intCast, _root_.zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num))

end GlobalTheory.SemicharTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTranslateThetaCoordinateOfRealPartLaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem U_thY_of_law : ∀ {D : D7} (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (f : WO S T → ℂ) (c : ℂ), (∀ z : GlobalTheory.FockCompare.RW T S, f (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1))) = c * Complex.exp (-(↑Real.pi * Complex.I) * ↑(-(GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) z))) * f (GlobalTheory.FockCompare.iotaW σ T S z)) → ∀ Y, Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) (GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ) Y = c * GlobalTheory.VacRealForm.thY σ S T (fun τ => B.1.map (tauE D τ)) (fun τ => B'.1.map (tauE D τ)) f δ Y := by
  intro D σ S T B B' hB hB' δ hδ M f c hf Y
  set Bc : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ := fun τ => B.1.map (tauE D τ) with hBc
  set B'c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ := fun τ => B'.1.map (tauE D τ) with hB'c
  set X : RW T S := Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M with hXdef
  set Z : RW T S := δ⁻¹ • Y with hZ
  have hY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  have hinv : ∀ τ, ((B⁻¹ : GL (Fin S.rank) D.host.E).1).map (tauE D τ) = (B.1.map (tauE D τ))⁻¹ := fun τ =>
    (Matrix.inv_eq_left_inv (by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)])).symm
  have hX : infRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = frPt Bc B'c X := by
    funext τ
    show (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1).map (tauE D τ) = B'c τ * Matrix.of (X τ) * (Bc τ)⁻¹
    rw [Matrix.map_mul, Matrix.map_mul, hinv]
    rfl
  have hadd : δ⁻¹ • (Y + δ • X) = Z + X := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  have hfr : frPt Bc B'c (Z + X) = frPt Bc B'c Z + frPt Bc B'c X := (frL Bc B'c).map_add Z X
  have hlaw := hf (frPt Bc B'c Z)
  rw [hX] at hlaw
  have hom : omO S T (frPt Bc B'c X) (frPt Bc B'c Z) =
      ∑ τ, ∑ a, ∑ b, 2 * (((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ (Z τ a b) * X τ a b)).re :=
    omO_frame B B' hB hB' X Z
  have harea : Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) =
      Complex.normSq δ * (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d / 2 :=
    GlobalTheory.MomDict.area_lamOf D _ δ D.host.ccK_ne_bot
  have hxi := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D).1
  have hN : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by
    have h : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast h
  have hd : Real.sqrt D.host.d ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)).ne'
  have hδn : Complex.normSq δ ≠ 0 := (Complex.normSq_pos.2 hδ).ne'
  have hHf : ∀ u v : RW T S, Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • u) (δ • v) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, u τ a b * starRingEnd ℂ (v τ a b) := by
    intro u v
    show (∑ τ, ∑ a, ∑ b, (δ • u) τ a b * starRingEnd ℂ ((δ • v) τ a b)) /
      (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) : ℂ) = _
    have e : ∀ τ a b, (δ • u) τ a b * starRingEnd ℂ ((δ • v) τ a b) =
        (Complex.normSq δ : ℂ) * (u τ a b * starRingEnd ℂ (v τ a b)) := fun τ a b => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Complex.mul_conj]; ring
    simp only [e, ← Finset.mul_sum]
    rw [harea, hxi]
    have h1 : ((Complex.normSq δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδn
    have h2 : ((Ideal.absNorm D.host.ccK : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN
    have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
    generalize (∑ τ, ∑ a, ∑ b, u τ a b * starRingEnd ℂ (v τ a b)) = s
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    field_simp
  have key : -(↑Real.pi * Complex.I) * ↑(-(omO S T (frPt Bc B'c X) (frPt Bc B'c Z))) +
      ((Real.pi * Formalism.L2.Pj.xiR D * sqSum (Z + X) : ℝ) : ℂ) +
      (-(Real.pi : ℂ) * Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Z) (δ • X) -
        (Real.pi : ℂ) * Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) (δ • X) / 2) =
      ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ) := by
    have hOm : omO S T (frPt Bc B'c X) (frPt Bc B'c Z) =
        2 * Formalism.L2.Pj.xiR D * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)).im := by
      rw [hom]
      simp only [Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hSq : sqSum (Z + X) = sqSum Z + 2 * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)).re + sqSum X := by
      unfold sqSum
      simp only [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hQ : (∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) = ((sqSum X : ℝ) : ℂ) := by
      unfold sqSum
      push_cast
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hHf, hHf, hOm, hSq, hQ]
    generalize (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) = p
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;> ring
  show gZ σ S T Bc B'c f (δ⁻¹ • (Y + δ • X)) * _ = c * gZ σ S T Bc B'c f (δ⁻¹ • Y)
  rw [hadd, ← hZ]
  unfold gZ
  rw [hfr, hlaw, hY, ← key, Complex.exp_add, Complex.exp_add]
  ring

end GlobalTheory.VacRealForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodCyclicModuloSpanSomeFactorStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)) (v : ∀ w, V w), (∀ w, genSub (a w) {v w} ⊔ C w = ⊤) → ∀ N : Submodule ℂ (PiTensorProduct ℂ V), (∀ w, Stab (actAt w (a w)) N) → tensAny C ≤ N → PiTensorProduct.tprod ℂ v ∈ N → N = ⊤ := by
  first | exact @GlobalTheory.HoweR.tprod_cyclic_top | exact GlobalTheory.HoweR.tprod_cyclic_top | (intros; apply GlobalTheory.HoweR.tprod_cyclic_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceAdelicCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.CMTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hr : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 w.embedding x
    rw [hc x] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (h.2.1.isComplex w)) hr

def sigE {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Gal(E/F) :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun x => sig_sig h x) (AlgHom.ext fun x => sig_sig h x)

theorem trace_eq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  have hne : (1 : Gal(E/F)) ≠ sigE h := by
    intro h1
    obtain ⟨x, hx⟩ := sig_ne_id h
    exact hx (congrArg (fun g : Gal(E/F) => g x) h1).symm
  have hle : Nat.card Gal(E/F) ≤ 2 := by
    calc Nat.card Gal(E/F) ≤ Nat.card (E →ₐ[F] E) :=
          Nat.card_le_card_of_injective (fun g => (g : E →ₐ[F] E)) (fun a b hab => AlgEquiv.coe_algHom_injective hab)
      _ ≤ Module.finrank F E := card_algHom_le_finrank F E E
      _ = 2 := h.2.2.1
  have hall : ∀ g : Gal(E/F), g = 1 ∨ g = sigE h := by
    classical
    have hc : (({1, sigE h} : Finset Gal(E/F))).card = 2 := Finset.card_pair hne
    have hu : ({1, sigE h} : Finset Gal(E/F)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hc]
      rw [← Nat.card_eq_fintype_card]
      have : 2 ≤ Nat.card Gal(E/F) := by
        rw [Nat.card_eq_fintype_card, ← hc]; exact Finset.card_le_univ _
      omega
    intro g
    have := Finset.mem_univ g
    rw [← hu] at this
    simpa using this
  have hgal : IsGalois F E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [h.2.2.1]
    apply le_antisymm hle
    classical
    rw [Nat.card_eq_fintype_card, ← Finset.card_pair hne]
    exact Finset.card_le_univ _
  rw [trace_eq_sum_automorphisms]
  classical
  rw [Fintype.sum_eq_add 1 (sigE h) hne (fun g hg => absurd (hall g) (by tauto))]
  rfl

end GlobalTheory.CMTrace

namespace GlobalTheory.CMTrace

theorem adele_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : AF F, Algebra.trace (AF F) (AE F E) (algebraMap (AF F) (AE F E) x) = 2 * x) ∧ ∀ c : AE F E, algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) c) = c + cA σ c := by
  intro F E _ _ _ _ _ σ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h.2.2.1, nsmul_eq_mul, Nat.cast_ofNat]
  · have htm : ∀ (a : AF F) (e : E), Algebra.trace (AF F) (AE F E) (a ⊗ₜ[F] e) =
        a * algebraMap F (AF F) (Algebra.trace F E e) := by
      intro a e
      have h1 : a ⊗ₜ[F] e = a • ((1 : AF F) ⊗ₜ[F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]; abel
    | tmul a e =>
      rw [htm, Algebra.TensorProduct.algebraMap_apply, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        ← TensorProduct.tmul_add, ← trace_eq h, mul_comm, ← Algebra.smul_def, Algebra.algebraMap_self,
        RingHom.id_apply, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CMTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexEqZeroOfCutoffZero
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mixTop_position_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) = 0 := by
  unfold mixTop
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun π _ =>
    Finset.sum_eq_zero fun u _ => mul_eq_zero_of_right _ ?_)
  refine Matrix.det_eq_zero_of_row_eq_zero j fun b => ?_
  simp [intersection_update_fsHerm_neg_one]

theorem cutForm_eq_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    (G₀ G₁ : V n → Matrix r r ℂ) {v : V n} (hρ : ρ =ᶠ[𝓝 v] (fun _ => 0)) :
    cutForm ρ G₀ G₁ v = 0 := by
  have h : dbar (fun x => (ρ x : ℂ)) v = dbar (fun _ : V n => (0 : ℂ)) v :=
    dbar_congr (hρ.mono fun x hx => by simp [hx])
  funext a b
  simp [cutForm, h]

theorem corrC_eq_zero_of_eventuallyEq_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    (G₀ G₁ : V n → Matrix r r ℂ) {v : V n} (hρ : ρ =ᶠ[𝓝 v] (fun _ => 0)) : corrC ρ G₀ G₁ v = 0 := by
  unfold corrC
  rw [cutForm_eq_zero G₀ G₁ hρ]
  exact Finset.sum_eq_zero fun j _ => mixTop_position_zero _ _ j

example : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} (G₀ G₁ : V n → Matrix r r ℂ) {v : V n}, ρ =ᶠ[𝓝 v] (fun _ => 0) → corrC ρ G₀ G₁ v = 0 :=
  by
  intro n r _ _ ρ G₀ G₁ v h
  exact corrC_eq_zero_of_eventuallyEq_zero G₀ G₁ h

end GlobalTheory.GoodTop
end

