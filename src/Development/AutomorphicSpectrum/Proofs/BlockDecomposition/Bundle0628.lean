import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0014
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0050
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeQuotientTorsionNonzeroStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_quotient_torsion_nonzero : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ x : (Fin m → K) ⧸ L, Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x ≠ ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalIdeleHermitianBound
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact

section Alg

variable {R : Type} [CommRing R] {s : R →+* R} {n r : ℕ} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R} {M N : Matrix (Fin n) (Fin n) R}

theorem hform_eq_dot (s : R →+* R) (H : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform s H x y = (fun i => s (x i)) ⬝ᵥ (H *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem comp_mulVec (s : R →+* R) (P : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    (fun i => s ((P *ᵥ x) i)) = (fun i => s (x i)) ᵥ* cT s P := by
  funext i
  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, cT, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem hform_mulVec (s : R →+* R) (P H : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    Formalism.UG.hform s H (P *ᵥ x) (P *ᵥ x) = Formalism.UG.hform s (cT s P * H * P) x x := by
  rw [hform_eq_dot, hform_eq_dot, comp_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem hform_smul (s : R →+* R) (c : R) (H : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform s (c • H) x y = c * Formalism.UG.hform s H x y := by
  simp only [Formalism.UG.hform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cT_diagonal (s : R →+* R) (d : Fin r → R) : cT s (diagonal d) = diagonal fun i => s (d i) := by
  ext i j
  by_cases e : i = j
  · subst e; simp [cT]
  · simp [cT, Matrix.diagonal_apply, e, Ne.symm e]

theorem coef_row (hU : cT s M * Jm * M = Jm) (hMN : M * N = 1) {P : Matrix (Fin n) (Fin r) R} {d : Fin r → R}
    (hP : M * P = P * diagonal d) : cT s P * Jm * N = cT s (diagonal d) * (cT s P * Jm) := by
  have e := pgram_unitary hU P N
  rw [hMN, Matrix.mul_one, hP, Formalism.UG.cT_mul] at e
  rw [← e, Matrix.mul_assoc]

theorem col_inv (hNM : N * M = 1) {P : Matrix (Fin n) (Fin r) R} {D A : Matrix (Fin r) (Fin r) R}
    (hP : M * P = P * D) (hDA : D * A = 1) : N * P = P * A := by
  calc N * P = N * (P * (D * A)) := by rw [hDA, Matrix.mul_one]
    _ = N * (M * P) * A := by rw [hP]; simp only [Matrix.mul_assoc]
    _ = P * A := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]

theorem diag_rel (hF : PFr s Jm Xm Ym) (hU : cT s M * Jm * M = Jm) {d d' : Fin r → R}
    (hX : M * Xm = Xm * diagonal d) (hY : M * Ym = Ym * diagonal d') (i : Fin r) : s (d i) * d' i = 1 := by
  have e := pgram_unitary hU Xm Ym
  rw [hX, hY, hF.xy, Formalism.UG.cT_mul] at e
  have e2 : cT s (diagonal d) * diagonal d' = 1 := by
    rw [← e]
    have : cT s (diagonal d) * cT s Xm * Jm * (Ym * diagonal d') =
        cT s (diagonal d) * (cT s Xm * Jm * Ym) * diagonal d' := by simp only [Matrix.mul_assoc]
    rw [this, hF.xy, Matrix.mul_one]
  have := congrFun (congrFun e2 i) i
  rwa [cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this

theorem line_conj (hss : ∀ x, s (s x) = x) (hU : cT s M * Jm * M = Jm) (hMN : M * N = 1)
    {P : Matrix (Fin n) (Fin r) R} {d : Fin r → R} (hP : M * P = P * diagonal d) (i : Fin r) :
    cT s N * vecMulVec (fun k => s ((cT s P * Jm) i k)) ((cT s P * Jm) i) * N =
      (d i * s (d i)) • vecMulVec (fun k => s ((cT s P * Jm) i k)) ((cT s P * Jm) i) := by
  have hrow : (cT s P * Jm) i ᵥ* N = s (d i) • (cT s P * Jm) i := by
    rw [← Matrix.mul_apply_eq_vecMul, coef_row hU hMN hP, cT_diagonal]
    funext k
    simp [Matrix.diagonal_mul]
  have hcol : cT s N *ᵥ (fun k => s ((cT s P * Jm) i k)) = fun k => s (((cT s P * Jm) i ᵥ* N) k) := by
    funext k
    simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, cT, Matrix.transpose_apply, Matrix.map_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hcol, hrow]
  ext a b
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, map_mul, hss]
  ring

theorem aniso_conj (hF : PFr s Jm Xm Ym) (hU : cT s M * Jm * M = Jm) (hUN : cT s N * Jm * N = Jm) (hMN : M * N = 1)
    (hNM : N * M = 1) {d d' : Fin r → R} (hX : M * Xm = Xm * diagonal d) (hY : M * Ym = Ym * diagonal d')
    (P : Matrix (Fin n) (Fin n) R) (hPe : P = 1 - Xm * (cT s Ym * Jm) - Ym * (cT s Xm * Jm)) :
    cT s N * (cT s P * Jm * P) * N = cT s P * Jm * P := by
  have hrel := diag_rel hF hU hX hY
  have h1 : diagonal d * cT s (diagonal d') = 1 := by
    rw [cT_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have := congrArg s (hrel i)
    rwa [map_mul, hF.ss, map_one] at this
  have h2 : diagonal d' * cT s (diagonal d) = 1 := by
    rw [cT_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hrel i
  have hc : N * P = P * N := by
    rw [hPe, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      ← Matrix.mul_assoc N Xm, ← Matrix.mul_assoc N Ym, col_inv hNM hX h1, col_inv hNM hY h2,
      Matrix.mul_assoc Xm, Matrix.mul_assoc Ym, Matrix.mul_assoc Xm, Matrix.mul_assoc Ym,
      coef_row hU hMN hX, coef_row hU hMN hY]
  have e := pgram_unitary hUN P P
  rw [hc] at e
  have e2 : cT s N * (cT s P * Jm * P) * N = cT s (P * N) * Jm * (P * N) := by
    rw [Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  rw [e2, e]

end Alg

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem hform_ratV (H : Matrix (Fin n) (Fin n) E) (ξ : Fin n → E) :
    Formalism.UG.hform (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (JR (F := F) (AF F) H) (ratV F ξ) (ratV F ξ) =
      inclR (F := F) (AF F) (hE σ H ξ ξ) := by
  simp only [Formalism.UG.hform, hE, ratV, JR, Matrix.map_apply, sigRA_inclR, map_sum, map_mul]
  rfl

theorem hR_of_conj (hH : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (c : AF F ⊗[F] E)
    (h : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) P * JR (F := F) (AF F) hH * P = c • JR (F := F) (AF F) hH) (ξ : Fin n → E) :
    hR (AF F) σ hH (P *ᵥ ratV F ξ) (P *ᵥ ratV F ξ) = c * inclR (F := F) (AF F) (hE σ hH ξ ξ) := by
  change Formalism.UG.hform _ _ _ _ = _
  rw [hform_mulVec, h, hform_smul, hform_ratV]

theorem rows_map (J : Matrix (Fin n) (Fin n) E) (C : Matrix (Fin n) (Fin r) E) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F C) * JR (F := F) (AF F) J =
      (cT (σ : E →+* E) C * J).map (inclR (F := F) (AF F)) := by
  unfold JR
  rw [← cT_map_inclR, ← Matrix.map_mul]

theorem JR_normMat (C : Matrix (Fin n) (Fin r) E) (i : Fin r) :
    JR (F := F) (AF F) (normMat σ (rowOf σ J C i)) =
      vecMulVec (fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ
          ((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F C) * JR (F := F) (AF F) J) i k))
        ((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F C) * JR (F := F) (AF F) J) i) := by
  rw [rows_map]
  ext a b
  simp [JR, normMat, rowOf, vecMulVec_apply, sigRA_inclR, -Matrix.map_mul]

theorem sum_lineProj (C D : Matrix (Fin n) (Fin r) E) :
    ∑ i, lineProj σ J C D i = C * (cT (σ : E →+* E) D * J) := by
  ext a b
  rw [Matrix.sum_apply, Matrix.mul_apply]
  rfl

theorem anisoProj_eq : anisoProj σ J X Y = 1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J) := by
  rw [anisoProj, Fintype.sum_sum_type]
  simp only [projFam, Sum.elim_inl, Sum.elim_inr]
  rw [sum_lineProj, sum_lineProj, sub_add_eq_sub_sub]

theorem adMat_anisoProj : adMat F (anisoProj σ J X Y) =
    1 - adMat F X * (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F Y) * JR (F := F) (AF F) J) -
      adMat F Y * (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J) := by
  rw [rows_map, rows_map, anisoProj_eq, ← Matrix.map_mul, ← Matrix.map_mul]
  ext a b
  simp [Matrix.one_apply, apply_ite (inclR (F := F) (AF F)), -Matrix.map_mul]

theorem JR_aniso : JR (F := F) (AF F) (hermFam σ J X Y none) =
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F (anisoProj σ J X Y)) * JR (F := F) (AF F) J * adMat F (anisoProj σ J X Y) := by
  change JR (F := F) (AF F) (cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y) = _
  unfold JR
  rw [Matrix.map_mul, Matrix.map_mul, cT_map_inclR]

theorem idele_norm (h : IsCMExt F E σ) (u : (AF F ⊗[F] E)ˣ) (hu : GlobalTheory.Doubling.absE F E u = 1) :
    ∃ t : GroundTheory.Global.IdeleGroup F, (GroundTheory.Global.IdeleGroup.ideleModule F t : ℝ) = 1 ∧
      algebraMap (AF F) (AF F ⊗[F] E) (t : AF F) = u.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ u.1 := by
  refine ⟨Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) u, ?_, GlobalTheory.Doubling.algebraMap_norm_eq h _⟩
  have h2 : ∀ v : (AF F)ˣ, (((GlobalTheory.WeilM.adeleClass F).modu v : ℝ≥0) : ℝ) =
      (GroundTheory.Global.IdeleGroup.ideleModule F v : ℝ) := fun v => by
    change (distribHaarChar (AdeleRing (𝓞 F) F) v : ℝ) = _
    exact GlobalTheory.ModuAdele.distribHaarChar_adeleRing F v
  rw [← h2, GlobalTheory.ModuAdele.modu_norm_eq_absE, hu]
  simp

theorem idele_norm_inv (h : IsCMExt F E σ) (u : (AF F ⊗[F] E)ˣ) (hu : GlobalTheory.Doubling.absE F E u = 1)
    (e : AF F ⊗[F] E) (he : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ u.1 * e = 1) :
    ∃ t : GroundTheory.Global.IdeleGroup F, (GroundTheory.Global.IdeleGroup.ideleModule F t : ℝ) = 1 ∧
      algebraMap (AF F) (AF F ⊗[F] E) (t : AF F) = e * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ e := by
  obtain ⟨t, ht, e1⟩ := idele_norm h u hu
  refine ⟨t⁻¹, ?_, ?_⟩
  · have e0 : GroundTheory.Global.IdeleGroup.ideleModule F t = 1 := Subtype.ext ht
    rw [map_inv, e0, inv_one]
    rfl
  · have h1 : algebraMap (AF F) (AF F ⊗[F] E) ((t⁻¹ : GroundTheory.Global.IdeleGroup F) : AF F) *
        algebraMap (AF F) (AF F ⊗[F] E) (t : AF F) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h3 := congrArg (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) he
    rw [map_mul, sigRA_sigRA σ h, map_one] at h3
    have h2 : algebraMap (AF F) (AF F ⊗[F] E) (t : AF F) * (e * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ e) = 1 := by
      rw [e1]
      calc _ = (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ u.1 * e) * (u.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ e) := by ring
        _ = 1 := by rw [he, h3, one_mul]
    exact left_inv_eq_right_inv h1 h2

end Adelic

theorem hermFam_levi_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (hermFam σ J X Y j) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (hermFam σ J X Y j) ξ ξ) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW m hm hm1 j
  obtain ⟨d, d', hX, hY⟩ := hm
  obtain ⟨B, hB, hXB, hu⟩ := hm1
  have hF := pfrA h hJ hW
  have hBd : diagonal d = B := (Bm_eq hF hX).symm.trans (Bm_eq hF hXB)
  have hU := unitaryA_matHom m
  have hUN := unitaryA_matHom m⁻¹
  have hMN : (matHom _ σ J m).1 * (matHom _ σ J m⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hNM : (matHom _ σ J m⁻¹).1 * (matHom _ σ J m).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hunit : ∀ i, ∃ u : (AF F ⊗[F] E)ˣ, d i = u ∧ GlobalTheory.Doubling.absE F E u = 1 := fun i => by
    obtain ⟨u, e, e'⟩ := hu i
    exact ⟨u, by rw [← e, ← hBd, Matrix.diagonal_apply_eq], e'⟩
  rcases j with _ | i | i
  · refine ⟨1, ?_, fun ξ => ?_⟩
    · rw [map_one]
      exact le_refl _
    · rw [Units.val_one, map_one]
      refine hR_of_conj _ _ 1 ?_ ξ
      rw [one_smul, JR_aniso]
      exact aniso_conj hF hU hUN hMN hNM hX hY _ adMat_anisoProj
  · obtain ⟨u, e, hu1⟩ := hunit i
    obtain ⟨t, ht, et⟩ := idele_norm_inv h u hu1 (d' i) (by rw [← e]; exact diag_rel hF hU hX hY i)
    refine ⟨t, ht.ge, fun ξ => ?_⟩
    refine hR_of_conj _ _ _ ?_ ξ
    rw [et]
    change cT _ _ * JR (F := F) (AF F) (normMat σ (rowOf σ J Y i)) * _ = _ • JR (F := F) (AF F) (normMat σ (rowOf σ J Y i))
    rw [JR_normMat]
    exact line_conj hF.ss hU hMN hY i
  · obtain ⟨u, e, hu1⟩ := hunit i
    obtain ⟨t, ht, et⟩ := idele_norm h u hu1
    refine ⟨t, ht.ge, fun ξ => ?_⟩
    refine hR_of_conj _ _ _ ?_ ξ
    rw [et, ← e]
    change cT _ _ * JR (F := F) (AF F) (normMat σ (rowOf σ J X i)) * _ = _ • JR (F := F) (AF F) (normMat σ (rowOf σ J X i))
    rw [JR_normMat]
    exact line_conj hF.ss hU hMN hX i

end GlobalTheory.CompanionTheory.ParCocompact

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lf3
section
open Ad3 Ad3.S
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped LSeries.notation

noncomputable section

namespace GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients

theorem unr_mul (v : Pl) {μ₁ μ₂ : (Qv v)ˣ →* ℂˣ} (h1 : IsUnramifiedChar μ₁) (h2 : IsUnramifiedChar μ₂) :
    IsUnramifiedChar (μ₁ * μ₂) := by
  intro u hu
  have a1 := h1 hu
  have a2 := h2 hu
  simp only [MonoidHom.mem_ker, MonoidHom.mul_apply] at a1 a2 ⊢
  rw [a1, a2, mul_one]

theorem unr_inv (v : Pl) {μ : (Qv v)ˣ →* ℂˣ} (h : IsUnramifiedChar μ) : IsUnramifiedChar μ⁻¹ := by
  intro u hu
  have a1 := h hu
  simp only [MonoidHom.mem_ker, MonoidHom.inv_apply] at a1 ⊢
  rw [a1, inv_one]

theorem e2 : faceMap_comp_succAbove_castSucc → E2a → E2b → E2 := by
  intro h1b h2a h2b N M _ _ hM χ D a ha hsat c δ T hadm hT c' hc' s hs
  obtain ⟨⟨e, he⟩, hL⟩ := h1b
  have hk : 1 ≤ D.k := le_trans (by norm_num) D.three
  set ψ : DirichletCharacter ℂ M := DirichletCharacter.changeLevel hM χ⁻¹ with hψ
  set Nf : ℕ → ℂ := fun n => ψ (n : ZMod M) * a (n ^ 2) with hNf
  have hpure : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧
      α * β = χ p * (p : ℂ) ^ (D.k - 1) ∧ ‖α‖ = ‖β‖ := by
    intro p hp hpN
    obtain ⟨q, hq⟩ : ∃ q : Nat.Primes, (q : ℕ) = p := ⟨⟨p, hp⟩, rfl⟩
    set v : Pl := e.symm q with hvdef
    have hv : pOf v = p := by rw [← he v, hvdef, Equiv.apply_symm_apply, hq]
    have hvb : v ∉ D.bad := by rw [hsat.1, hv]; exact hpN
    obtain ⟨α, β, h1, h2, h3⟩ := hsat.2 _ hvb
    refine ⟨α, β, by rw [← hv]; exact h1, by rw [← hv]; exact h2, ?_⟩
    have hu := (D.unit v).2 (unifUnit (Qv v))
    rw [h3, Units.val_div_eq_div_val, norm_div] at hu
    have hβ : ‖(β : ℂ)‖ ≠ 0 := by simp
    field_simp at hu
    exact hu
  have hb : ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (D.k - 1) := by
    intro n hn
    refine (GlobalTheory.T.norm_square_coefficient_le_divisor_bound D.k N χ a ha h2a hpure n hn).trans ?_
    exact mul_le_mul_of_nonneg_right (GlobalTheory.T.card_divisors_sq_le_two_mul' n) (by positivity)
  have hsumm : LSeriesSummable Nf (s + D.k - 1) := GlobalTheory.T.summable_twisted_square_coefficients M N D.k hM χ a hk hb s hs
  have hN1 : Nf 1 = 1 := by simp [Nf, ha.2.1]
  have hNmul : ∀ {m n : ℕ}, m.Coprime n → Nf (m * n) = Nf m * Nf n := by
    intro m n h
    simp only [Nf, Nat.cast_mul, map_mul, mul_pow]
    rw [(h2a D.k N χ a ha).1 _ _ (Nat.Coprime.pow 2 2 h)]
    ring
  have hA := GlobalTheory.CompanionTheory.SquareEuler.hasProd_twist c' hN1 hNmul hsumm
  have h2s : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hB := DirichletCharacter.LSeries_eulerProduct_hasProd (c' ^ 2) h2s
  have hP := hB.mul hA
  have hfac : ∀ v : Pl, (fun p : Nat.Primes => (1 - (c' ^ 2) ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ *
      ∑' j : ℕ, Nf ((p : ℕ) ^ j) * (c' ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(s + D.k - 1))) ^ j) (e v) =
      Set.mulIndicator {v | v ∉ T} (fun v => lf3 (D.ν v) (localChar c v) s) v := by
    intro v
    dsimp only
    have hp : (pOf v).Prime := by rw [← he v]; exact (e v).2
    rw [he v]
    have hp0 : ((pOf v : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    by_cases hvT : v ∈ T
    · have hpM : pOf v ∣ M := (hT v).1 hvT
      have hnu : ¬ IsUnit ((pOf v : ℕ) : ZMod M) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hc
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpM)
      have hc0 : c' ((pOf v : ℕ) : ZMod M) = 0 := MulChar.map_nonunit _ hnu
      have hc20 : (c' ^ 2) ((pOf v : ℕ) : ZMod M) = 0 := MulChar.map_nonunit _ hnu
      rw [Set.mulIndicator_of_notMem (by simpa using hvT), hc20, hc0]
      simp only [zero_mul, sub_zero, inv_one, one_mul]
      rw [tsum_eq_single 0]
      · simp [hN1]
      · intro j hj
        simp [hj]
    · rw [Set.mulIndicator_of_mem (by simpa using hvT)]
      have hvb : v ∉ D.bad := fun h => hvT (hadm.bad h)
      obtain ⟨α, β, hsum, hprod, hν⟩ := hsat.2 v hvb
      have hpM : ¬ pOf v ∣ M := fun h => hvT ((hT v).2 h)
      have hcp := hc' v hpM
      have hunit : IsUnit ((pOf v : ℕ) : ZMod M) :=
        (ZMod.isUnit_iff_coprime _ _).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      have hψp : ψ ((pOf v : ℕ) : ZMod M) = (χ (pOf v))⁻¹ := by
        have h0 := DirichletCharacter.changeLevel_eq_cast_of_dvd χ⁻¹ hM hunit.unit
        rw [IsUnit.unit_spec] at h0
        rw [hψ, h0, ZMod.cast_natCast hM, MulChar.inv_apply_eq_inv']
      have hNfp : ∀ j, Nf (pOf v ^ j) = (χ (pOf v))⁻¹ ^ j * a (pOf v ^ (2 * j)) := by
        intro j
        simp only [Nf, Nat.cast_pow, map_pow, hψp]
        rw [← pow_mul, mul_comm j 2]
      have hu1 := D.unr v hvb
      have hu2 := hadm.unr v hvT
      have hα : (α : ℂ) ≠ 0 := α.ne_zero
      have hβ : (β : ℂ) ≠ 0 := β.ne_zero
      have hν' : ((D.ν v (unifUnit (Qv v)) : ℂˣ) : ℂ) = (α : ℂ) / β := by rw [hν, Units.val_div_eq_div_val]
      have hr : ‖(α : ℂ) / β‖ = 1 := by rw [← hν']; exact (D.unit v).2 _
      have hloc := GlobalTheory.T.hasSum_square_coefficient_local_series h2a h2b D.k N χ a ha hk (pOf v) hp α β (c' ((pOf v : ℕ) : ZMod M)) s hα hβ hsum hprod hr
        (DirichletCharacter.norm_le_one _ _) (by linarith)
      rw [tsum_congr (fun j => by rw [hNfp j]), hloc.tsum_eq]
      rw [lf3, hL v _ (unr_mul v hu1 hu2), hL v _ hu2, hL v _ (unr_mul v (unr_inv v hu1) hu2)]
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hν', ← hcp]
      have hX2 : (c' ^ 2) ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-(2 * s)) =
          (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 := by
        rw [show -(2 * s) = -s + -s by ring, Complex.cpow_add _ _ hp0, MulChar.pow_apply' _ two_ne_zero]
        ring
      have hXn := GlobalTheory.CompanionTheory.SquareEuler.norm_X_lt_one c' (s := s) (by linarith) hp
      have h1X2 : 1 - (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
        intro h
        have h' : ‖c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)‖ ^ 2 = 1 := by
          rw [← norm_pow, show (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 = 1 by
            linear_combination -h, norm_one]
        nlinarith [norm_nonneg (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s))]
      rw [hX2, ← mul_assoc, inv_mul_cancel₀ h1X2, one_mul]
      ring
  have hP2 : HasProd (Set.mulIndicator {v | v ∉ T} (fun v => lf3 (D.ν v) (localChar c v) s))
      (L ↗(c' ^ 2) (2 * s) * L (↗c' * Nf) (s + D.k - 1)) := by
    have := (e.hasProd_iff).2 hP
    convert this using 1
    funext v
    exact (hfac v).symm
  rw [← hasProd_subtype_iff_mulIndicator] at hP2
  have hfun : (fun n : ℕ => (c' * DirichletCharacter.changeLevel hM χ⁻¹) (n : ZMod M) * a (n ^ 2)) =
      ↗c' * Nf := by
    funext n
    simp only [Pi.mul_apply, Nf, hψ, MulChar.coeToFun_mul]
    ring
  rw [DirichletCharacter.LFunction_eq_LSeries _ h2s, hfun]
  exact hP2.tprod_eq

end GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorGlRelationsStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_operator_gl_relations : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ), Formalism.REAL.GlRel (EopV π τ) := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.glRel_EopV | exact GlobalTheory.CompanionTheory.Clozel.glRel_EopV | (intros; apply GlobalTheory.CompanionTheory.Clozel.glRel_EopV <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.TotalTrace

theorem eq_zero_of_exp_mul_eq_one {c : ℂ} (h : ∀ t : ℝ, Complex.exp (c * t) = 1) : c = 0 := by
  have h0 : HasDerivAt (fun v : ℝ => c * (v : ℂ)) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
  have h1 := h0.cexp
  have h2 : (fun t : ℝ => Complex.exp (c * t)) = fun _ => 1 := funext h
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using h3

theorem total_trace_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} {m : (E →+* ℂ) → Multiset ℂ} (hV : IsDiscrete V)
    (hm : ∀ τ, HasInfCharGL V τ (m τ)) : ∑ τ, (m τ).sum = 0 := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hφ0 (Subtype.ext (funext hcon))
  have hlie : lie E N (oneL E N) φ = (∑ τ, (m τ).sum) • φ := by
    rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
    exact Finset.sum_congr rfl fun τ _ => GlobalTheory.CompanionTheory.CentEig.trace_Eop_eq_of_hasInfCharGL (hm τ) φ hφ
  refine eq_zero_of_exp_mul_eq_one fun t => ?_
  have h1 := GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ hlie t g
  rw [(hV.sqInt φ hφ).1 t g] at h1
  have h2 : Complex.exp ((∑ τ, (m τ).sum) * t) * φ.1 g = 1 * φ.1 g := by rw [one_mul]; exact h1.symm
  exact mul_right_cancel₀ hg h2

theorem twBound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  intro E _ _ _ N
  refine ⟨0, fun V m hV hm => ?_⟩
  rw [total_trace_eq_zero hV hm, norm_zero]

end GlobalTheory.CompanionTheory.TotalTrace

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalChartSheetDecompositionStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_chart_sheet_decomposition : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)), IsHermRep Nh B → IsSmoothHerm B →
    ∀ (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
      [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
      (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n)
      (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)) (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ),
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsPiece i Ψ N e Γ →
      ContinuousOn (maDensity (fun _ y' => Real.log (B.h (Γ y')))) e.target ∧
      ∀ ε : ℤˣ, (((Nh.restr i).φ σ₀).chernPart D ε).restrict e.source =
        ((volume.restrict e.target).withDensity fun v =>
          ENNReal.ofReal (((ε : ℤ) : ℝ) * maDensity (fun _ y' => Real.log (B.h (Γ y'))) v)).map e.symm := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens.piece_density <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleRealityStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pole_reality : PoleReal := by
  first | exact @GlobalTheory.CompanionTheory.PoleBound.poleReal | exact GlobalTheory.CompanionTheory.PoleBound.poleReal | (intros; apply GlobalTheory.CompanionTheory.PoleBound.poleReal <;> assumption)
end

