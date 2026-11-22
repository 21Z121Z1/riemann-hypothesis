import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0243
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0256
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftCornerStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.LiftCorner.lift_corner | exact GlobalTheory.SnMass.VolN.LiftCorner.lift_corner | (intros; apply GlobalTheory.SnMass.VolN.LiftCorner.lift_corner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftEntryStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inl p) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inl p) → degB r β ≤ degB r (.inl p) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.LiftEntry.lift_entry | exact GlobalTheory.SnMass.VolN.LiftEntry.lift_entry | (intros; apply GlobalTheory.SnMass.VolN.LiftEntry.lift_entry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRootHaar
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.ThA.OrbSq
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2
open scoped ENNReal

namespace GlobalTheory.Amp.RootQuot

variable {k r : ℕ}

theorem exists_setting (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') : ∃ Bs : B.RealPlaceData k r ℂ ℂ, Bs.z = z ∧ Bs.z' = z' := by
  obtain ⟨μG, hG⟩ := unitary_group_haar_exists k r
  obtain ⟨μN, hN⟩ := unipotent_haar_exists k r
  obtain ⟨μW, hW⟩ := weyl_haar_exists k r z hz hT
  obtain ⟨μW', hW'⟩ := weyl_haar_exists k r z' hz' hT'
  obtain ⟨μsec, hs⟩ := SettingConstruction.sectionExists k r z z' hk hz hz' hT hT'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := character_exists_alt
  exact ⟨⟨z, z', fun _ => 1, fun _ => 1, μG, μW, μN, μW', μsec, χ, hk, hz, hz', hT, hT',
    ⟨rfl, fun _ _ _ _ => rfl⟩, ⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl, fun _ _ _ => rfl,
    continuousOn_const, continuousOn_const, hG, hW, hN, hW', hs, hχ1, hχ2, hχ3⟩, rfl, rfl⟩

theorem perm_invol (p : C.LPt) (n : ℕ) (h : D.ptSize p = n) (a : Fin n) :
    (h ▸ D.ptPerm p : Equiv.Perm (Fin n)) ((h ▸ D.ptPerm p : Equiv.Perm (Fin n)) a) = a := by
  subst h
  exact Dx1.ptPerm_invol p a

theorem zhat_inv_mono {z z' : Fin (2 * r + k + 1) → ℂ} (p : Point ℂ (r + 1)) {g : Mat k r} (hg : g ∈ GG k r)
    (hZ : ZhatO k r z z' g = ptMat p) :
    ∃ d : Fin (r + 1) → ℂ, (∀ a, d a ≠ 0) ∧ Zhat k r z' z g⁻¹ = C2.monoP (permOf p) d := by
  obtain ⟨hw, hd⟩ := VV.ptMatN_monoP' (sw p.1) (r + 1) (isLocPt_sw p).2 (isLocPt_sw p).1
  rw [ptMat_sw, ← hZ] at hw
  generalize (Eq.rec (motive := fun x _ => Fin x → ℂ) (D.ptDiag (sw p.1)) (isLocPt_sw p).2) = d at hw hd
  have hi : ∀ a, permOf p (permOf p a) = a := perm_invol _ _ _
  refine ⟨fun a => star ((-1) ^ (r - (permOf p a).val) * d (permOf p a)), fun a => ?_, ?_⟩
  · exact star_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hd _))
  · rw [NfMid.zhat_inv z z' hg]
    ext i a
    have h1 : (-1 : ℂ) ^ (r - i.val) * Zhat k r z z' g a i = if a = permOf p i then d i else 0 :=
      congrFun (congrFun hw a) i
    have h2 : Zhat k r z z' g a i = (-1 : ℂ) ^ (r - i.val) * if a = permOf p i then d i else 0 := by
      rw [← h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [conjTranspose_apply, h2]
    show _ = if i = permOf p a then _ else 0
    by_cases h : a = permOf p i
    · subst h
      rw [if_pos rfl, if_pos (hi i).symm, hi]
    · rw [if_neg h, if_neg (fun e => h (by rw [e, hi])), mul_zero, star_zero]

theorem gf_inv (z z' : Fin (2 * r + k + 1) → ℂ) {g : Mat k r} (hg : g ∈ GG k r) :
    Gf k r z' z g⁻¹ = Gf k r z z' g := by
  unfold Gf
  simp only [Complex.normSq_eq_norm_sq, NfMid.dmin_inv z z' hg]
  ring

theorem exists_root_haar (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (p : Point ℂ (r + 1)) {g : Mat k r} (hg : g ∈ GG k r)
    (hZ : ZhatO k r z z' g = ptMat p) (hG0 : Gf k r z z' g ≠ 0) :
    ∃ μ : Measure (Mt k r), IsHaarOn (Rset k r g) μ ∧ IsUnimod (Rset k r g) μ ∧
      μ.map (rootCoords k r z' p) = volume := by
  obtain ⟨Bs, rfl, rfl⟩ := exists_setting hk hz' hz hT' hT
  obtain ⟨d, hd, hZw⟩ := zhat_inv_mono p hg hZ
  have hu := isUnit_det_of_mem_GG hg
  have hgi : g⁻¹ ∈ B.GV k r := isClosedSub_GG.2.2.2.2 _ hg
  have hpos : 0 < Gf k r Bs.z Bs.z' g⁻¹ := by
    rw [gf_inv _ _ hg]
    exact lt_of_le_of_ne (gNonneg k r _ _ hz hz' hT hT' g hg) hG0.symm
  have hG : Rad.Good Bs g⁻¹ (permOf p) d :=
    ⟨Rad.exists_rho Bs hgi hpos hd hZw, Rad.u_inj Bs hgi hpos hd hZw, fun ρ hρ => Rad.u_lstg Bs hgi hpos hd hZw hρ⟩
  have hm := Rad.rhoF_meas Bs hgi hd hG
  have hH := Rad.haar_good Bs hgi hd hG
  have hI := haar_measure_inversion k r _ _ (OrbJ.closedR (Matrix.isUnit_nonsing_inv_det g hu)) hH
  have hset : C6.Rset g⁻¹ = Rset k r g := by
    ext x
    simp only [C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  rw [hset] at hH
  have hmu : D.muR Bs g⁻¹ (permOf p) = (volume : Measure (C2.Lstidx (permOf p) → ℂ)).map
      (fun x => (Matrix.of.symm (Rad.rhoF Bs g⁻¹ (permOf p) x) : Mt k r)) := rfl
  have hphi : ∀ x : Mt k r, Rad.phi0 Bs (permOf p) x = cjE (rootEquiv p) (rootCoords k r Bs.z p x) := by
    intro x
    funext q
    rw [cjE_apply]
    have hq : q.1.2.val < r := by have h1 := q.2.1; have h2 := q.1.1.isLt; rw [Fin.lt_def] at h1; omega
    show star (C2.uMap k r Bs.z (Matrix.of x) q.1.2 q.1.1) = star (flagMat k r Bs.z (Matrix.of x) q.1.2 q.1.1)
    unfold C2.uMap flagMat
    rw [dif_pos hq, dif_pos hq]
    exact congrArg star (DF.herm_es _ _)
  have hrc : rootCoords k r Bs.z p = (cjE (rootEquiv p)).symm ∘ Rad.phi0 Bs (permOf p) := by
    funext x; simp [hphi x]
  have hrm : Measurable (rootCoords k r Bs.z p) := by
    rw [hrc]; exact (cjE (rootEquiv p)).symm.measurable.comp (Rad.continuous_radial_phi Bs).measurable
  refine ⟨D.muR Bs g⁻¹ (permOf p), ⟨OrbJ.sigmaF hH, hH.ne_zero, hH.conc, hH.left⟩, ⟨hH.right, hI⟩, ?_⟩
  rw [hmu, Measure.map_map hrm hm]
  have : rootCoords k r Bs.z p ∘ (fun x => (Matrix.of.symm (Rad.rhoF Bs g⁻¹ (permOf p) x) : Mt k r)) =
      (cjE (rootEquiv p)).symm := by
    funext x
    rw [hrc]
    simp only [Function.comp]
    rw [Rad.coordMap_hermRep_leftInverse Bs hgi hd hG]
  rw [this, (cjE_mp _).symm.map_eq]

theorem scale_pos (D : D7) : 0 < 2 * D.host.ka / gg D / (2 * Real.pi) := by
  have h1 : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have h : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
    have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
    positivity
  have h2 : 0 < gg D := by
    unfold gg
    have a := (D.host.g_prime 0).pos
    have b := (D.host.g_prime 1).pos
    positivity
  positivity

theorem exists_rMeas : ∀ (D : D7) (W : LocW D.R.k D.R.rS) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS W.z → inWb D.R.k D.R.rS W.z' → 0 < Tz D.R.k D.R.rS W.z → 0 < Tz D.R.k D.R.rS W.z' → IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG → RelPt D W.z W.z' γ p → ∃ ν, RMeas D W γ 1 ν := by
  rintro D W γ p hz hz' hT hT' hG ⟨hγ, hC, hG0⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨n, hn, n', hn', g, hg, rfl, hZ⟩ := GlobalTheory.CellRep.cell_rep _ _ W.z W.z' γ p hz hz' hT hT' hγ hC
  rw [gInv _ _ W.z W.z' hz hz' n ⟨1, (isClosedSub_UWset W.z).2.2.1, n, hn, (Matrix.one_mul _).symm⟩
    n' ⟨1, (isClosedSub_UWset W.z').2.2.1, n', hn', (Matrix.one_mul _).symm⟩] at hG0
  obtain ⟨μ, h1, h2, h3⟩ := exists_root_haar hk hz hz' hT hT' p hg hZ hG0
  obtain ⟨n1, -, -, -, n5⟩ := isClosedSub_Nset (k := D.R.k) (r := D.R.rS)
  obtain ⟨d1, d2⟩ := StabMeas.haar_smul h1 h2 (pow_pos (scale_pos D) (rootPat p).card)
  obtain ⟨e1, e2⟩ := StabMeas.haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ hn'))) (StabMeas.conj_mem_Rset hn hn' g) d1 d2
  obtain ⟨ν, hν⟩ := GlobalTheory.SgQuot.exists_isQuotMeas _ _ _ W.μG _ (StabMeas.isClosedSub_Rset hγ) hG e1 e2
  refine ⟨ν, p, _, ⟨n, hn, n', hn', g, rfl, hZ, _, d1.2.2.1, ?_, rfl⟩, ?_⟩
  · rw [Measure.map_smul, h3]
  · have e : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 hn'))]
    rw [ENNReal.ofReal_one, one_smul, e]
    exact hν

end GlobalTheory.Amp.RootQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrame
section
namespace GlobalTheory.SignCount

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

private theorem qEps_eq_star_dotProduct_Jm_mulVec {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    ((GlobalTheory.GaussMean.qEps ε x : ℝ) : ℂ) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  simp only [GlobalTheory.GaussMean.qEps, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]
  split_ifs <;> push_cast <;> ring

private theorem qEps_mulVec_of_conjTranspose_mul_Jm_mul {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x := by
  apply Complex.ofReal_injective
  rw [qEps_eq_star_dotProduct_Jm_mulVec, qEps_eq_star_dotProduct_Jm_mulVec, ← h, Matrix.star_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

private theorem qEps_not_eq_neg {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps (fun a => !ε a) x = - GlobalTheory.GaussMean.qEps ε x := by
  simp only [GlobalTheory.GaussMean.qEps, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a = true <;> simp [h]

private theorem card_true_add_card_false_le_of_qEps_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : ∀ x, GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x) :
    Fintype.card {a // η a = true} + Fintype.card {a // ε a = false} ≤ m := by
  classical
  let E₁ : ({a // η a = true} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun u a => if h : η a = true then u ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : η a = true <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : η a = true <;> simp [h] }
  let E₂ : ({a // ε a = false} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun w a => if h : ε a = false then w ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : ε a = false <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : ε a = false <;> simp [h] }
  let Φ := (C.mulVecLin ∘ₗ E₁).coprod E₂
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, w⟩ hp
    have hp' : C *ᵥ E₁ u = -(E₂ w) := by
      have : C *ᵥ E₁ u + E₂ w = 0 := by simpa [Φ] using hp
      exact eq_neg_of_add_eq_zero_left this
    have hnn : ∀ a, 0 ≤ (if η a then (1 : ℝ) else -1) * ‖E₁ u a‖ ^ 2 := by
      intro a
      by_cases h : η a = true
      · simp [h]
      · simp [E₁, h]
    have hnp : GlobalTheory.GaussMean.qEps ε (-(E₂ w)) ≤ 0 := by
      unfold GlobalTheory.GaussMean.qEps
      refine Finset.sum_nonpos fun a _ => ?_
      by_cases h : ε a = false
      · simp [h]
      · simp [E₂, h]
    have hq : GlobalTheory.GaussMean.qEps η (E₁ u) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg fun a _ => hnn a)
      rw [← hC, hp']
      exact hnp
    have hu : u = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 hq
      funext b
      have := hz b.1 (Finset.mem_univ _)
      simpa [E₁, b.2] using this
    have hw : w = 0 := by
      have h0 : E₂ w = 0 := by
        have : C *ᵥ E₁ u = 0 := by simp [hu]
        rw [hp'] at this
        exact neg_eq_zero.1 this
      funext b
      have := congrFun h0 b.1
      simpa [E₂, b.2] using this
    simp [hu, hw]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] using this

theorem card_true_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) :
    Nat.card {a // ε a = true} = Nat.card {a // η a = true} := by
  classical
  have hC := qEps_mulVec_of_conjTranspose_mul_Jm_mul C h
  have h₁ := card_true_add_card_false_le_of_qEps_eq C hC
  have hC' : ∀ x, GlobalTheory.GaussMean.qEps (fun a => !ε a) (C *ᵥ x) =
      GlobalTheory.GaussMean.qEps (fun a => !η a) x := by
    intro x; rw [qEps_not_eq_neg, qEps_not_eq_neg, hC]
  have h₂ := card_true_add_card_false_le_of_qEps_eq C hC'
  simp only [Fintype.card_subtype] at h₁ h₂
  simp only [Bool.not_eq_true', Bool.not_eq_false'] at h₂
  have hε : (Finset.univ.filter fun a => ε a = true).card +
      (Finset.univ.filter fun a => ε a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases ε a <;> simp
    simp [this]
  have hη : (Finset.univ.filter fun a => η a = true).card +
      (Finset.univ.filter fun a => η a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if η a = true then 1 else 0) + (if η a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases η a <;> simp
    simp [this]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  omega

theorem card_true_cons {n : ℕ} (s : Bool) (ε' : Fin n → Bool) :
    Nat.card {a // (Fin.cons s ε' : Fin (n + 1) → Bool) a = true} =
      (if s = true then 1 else 0) + Nat.card {a // ε' a = true} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]

private theorem conjTranspose_mul_Jm_mul_apply {m : ℕ} {ι : Type*} (ε : Fin m → Bool) (M : Matrix (Fin m) ι ℂ)
    (k l : ι) :
    (Mᴴ * Formalism.REAL.Jm ε * M) k l = ∑ i, star (M i k) * ((if ε i then 1 else -1) * M i l) := by
  rw [Matrix.mul_apply]
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, mul_assoc]

theorem gram_cons {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {s : Bool}
    {x₀ : Fin (n + 1) → ℂ} {B : Matrix (Fin (n + 1)) (Fin n) ℂ}
    (h0 : GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s)
    (h1 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (h2 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    (Matrix.of fun i => (Fin.cons (x₀ i) (B i) : Fin (n + 1) → ℂ))ᴴ * Formalism.REAL.Jm ε *
      (Matrix.of fun i => (Fin.cons (x₀ i) (B i) : Fin (n + 1) → ℂ)) =
      Formalism.REAL.Jm (Fin.cons s ε') := by
  have e0 := qEps_eq_star_dotProduct_Jm_mulVec ε x₀
  rw [h0] at e0
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply] at e0
  have e1 : ∀ l, ∑ i, star (x₀ i) * ((if ε i then 1 else -1) * B i l) = 0 := by
    intro l
    have := congrFun h1 l
    simpa [Matrix.vecMul, dotProduct, Formalism.REAL.Jm, Matrix.diagonal_mul] using this
  ext k l
  rw [conjTranspose_mul_Jm_mul_apply]
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
  · rw [← e0]
    cases s <;> simp [Formalism.REAL.Jm, GlobalTheory.GaussMean.sgn]
  · rw [e1]
    simp [Formalism.REAL.Jm, (Fin.succ_ne_zero l).symm]
  · have := congrArg star (e1 k)
    rw [star_sum, star_zero] at this
    rw [show (Formalism.REAL.Jm (Fin.cons s ε') : Matrix _ _ ℂ) k.succ 0 = 0 by
      simp [Formalism.REAL.Jm, Fin.succ_ne_zero k]]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp [mul_comm]
  · rw [← conjTranspose_mul_Jm_mul_apply ε B k l, h2]
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply]

theorem exists_signCompat : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n), Sorts ε f → Sorts ε' f' → ∃ e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q), SignCompat e ∧ sg (e none) = GlobalTheory.GaussMean.sgn ℝ s := by
  intro n ε ε' s x₀ B h0 h1 h2 P Q P' Q' f f' hf hf'
  have hc := card_true_eq _ (gram_cons h0 h1 h2)
  rw [card_true_cons, hf.card_true, hf'.card_true] at hc
  have hPQ := Sorts.add_eq f
  have hPQ' := Sorts.add_eq f'
  cases s
  · simp at hc
    let eL : Fin P' ≃ Fin P := finCongr (by omega)
    let eR : Option (Fin Q') ≃ Fin Q := (finSuccEquiv Q').symm.trans (finCongr (by omega))
    let φ : Option (Fin P' ⊕ Fin Q') ≃ Fin P' ⊕ Option (Fin Q') :=
      { toFun := fun o => o.elim (Sum.inr none) (Sum.elim Sum.inl (fun b => Sum.inr (some b)))
        invFun := Sum.elim (fun a => some (Sum.inl a)) (fun ob => ob.map Sum.inr)
        left_inv := by rintro (_ | _ | _) <;> rfl
        right_inv := by rintro (_ | _ | _) <;> rfl }
    refine ⟨φ.trans (Equiv.sumCongr eL eR), ?_, ?_⟩
    · intro i
      rcases i with i | i <;> simp [φ, GlobalTheory.CompactDualQuot.sg]
    · simp [φ, GlobalTheory.CompactDualQuot.sg, GlobalTheory.GaussMean.sgn]
  · simp at hc
    let eL : Option (Fin P') ≃ Fin P := (finSuccEquiv P').symm.trans (finCongr (by omega))
    let eR : Fin Q' ≃ Fin Q := finCongr (by omega)
    let φ : Option (Fin P' ⊕ Fin Q') ≃ Option (Fin P') ⊕ Fin Q' :=
      { toFun := fun o => o.elim (Sum.inl none) (Sum.elim (fun a => Sum.inl (some a)) Sum.inr)
        invFun := Sum.elim (fun oa => oa.map Sum.inl) (fun b => some (Sum.inr b))
        left_inv := by rintro (_ | _ | _) <;> rfl
        right_inv := by rintro ((_ | _) | _) <;> rfl }
    refine ⟨φ.trans (Equiv.sumCongr eL eR), ?_, ?_⟩
    · intro i
      rcases i with i | i <;> simp [φ, GlobalTheory.CompactDualQuot.sg]
    · simp [φ, GlobalTheory.CompactDualQuot.sg, GlobalTheory.GaussMean.sgn]

end GlobalTheory.SignCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FEqAndRdEq
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace GlobalTheory.DegreeRankEquations

theorem f_eq (D : D7) (X : HidaSetting D) : X.B.I.f = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  unfold AutInst.f
  omega

theorem rd_eq (D : D7) (X : HidaSetting D) : X.B.I.rd = D.host.rdE := by
  have hd : discr X.B.I.E = discr D.host.E := NumberField.discr_eq_discr_of_algEquiv X.B.I.E X.ιE.toRatAlgEquiv
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : (Module.finrank ℚ D.host.E : ℝ) = 2 * (X.B.I.f : ℝ) := by
    unfold AutInst.f
    have : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ X.B.I.F := by rw [← e1, ← e2, e3, mul_comm]
    rw [this]; push_cast; ring
  unfold AutInst.rd Host.rdE
  rw [hd, e4]

end GlobalTheory.DegreeRankEquations
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianPushforwardDensityStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_pushforward_density : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (G : (ι → ℝ) → ℂ), Continuous G → (∀ S : Set (ι → ℝ), IsCompact S → ∫ y in (fun (y : ι → Fin n → ℂ) (v : ι) => qEps (ε v) (y v)) ⁻¹' S, ((∏ v, gauss (y v) : ℝ) : ℂ) = ∫ b in S, G b) → ∀ b : ι → ℝ, (∀ v, b v ≠ 0) → G b = ((∏ v, gaussDens (ε v) (b v) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.GaussMean.ProdDensity.density_eq_prod | exact GlobalTheory.GaussMean.ProdDensity.density_eq_prod | (intros; apply GlobalTheory.GaussMean.ProdDensity.density_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarLie_isHaarOn_unipotentRadical : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ → IsHaarOn (Nset k r) (haarLie (Nset k r) κ) := by
  first | exact @GlobalTheory.haarLie_isHaarOn_Nset | exact GlobalTheory.haarLie_isHaarOn_Nset | (intros; apply GlobalTheory.haarLie_isHaarOn_Nset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEqEll
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.EllName

theorem rankOneInnerOperator_smul_smul_eq_mul_conj_smul {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (α β : ℂ) (a : Wp) (b : Wq) :
    rk1 (α • a) (β • b) = (α * (starRingEnd ℂ) β) • rk1 a b := by
  ext η
  rw [ContinuousLinearMap.smul_apply, rankOneInnerOperator_apply, rankOneInnerOperator_apply, inner_smul_left, smul_smul, smul_smul]
  congr 1
  ring

private theorem Afun_eq_inner_smul_of_isEll {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {μS : Measure (Mt k r)}
    {σ : Mat k r → (H →L[ℂ] H)} {w : H} {l : H → Wp} (hl : IsEll z ψ π μS σ (DD σ w) l)
    {w₀ : H} (hw₀ : w₀ ∈ DD σ w) (ξ : Wp) {x : Mat k r} (hx : x ∈ GG k r) :
    Afun ψ π μS σ w w₀ ξ x = ⟪l w₀, ξ⟫_ℂ • l (σ x w) := by
  unfold Afun
  rw [hl.2.2 _ (mem_DD σ w hx) _ hw₀, rankOneInnerOperator_apply]

theorem iint_eq_ell : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∀ γ ∈ Greg k r z z', Integrable (fun x : Mt k r => rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w))) μG ∧ ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ w₀' w₀ ξ ξ' γ = (⟪l w₀, ξ⟫_ℂ * ⟪ξ', l' w₀'⟫_ℂ * (d : ℂ)) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) γ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' γ hγ
  have hHaar := hStd.2.2.2.2.1
  have hd : (0 : ℝ) < d := hStd.2.2.2.2.2.1.1
  have h0 : μG {x | Matrix.of x ∉ GG k r} = 0 := by
    first
    | exact hHaar.1
    | exact hHaar.2.2.1
  have hGG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := ae_iff.2 h0
  have hU : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ (Hpk k r) hU
  have hγG : γ ∈ GG k r := Greg_subset z z' hγ
  have hγi : γ⁻¹ ∈ GG k r := (hgrp.2.2 γ hγG).2
  have hae : ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq),
      (fun x : Mt k r => rk1 (Afun (psiGen k r z c) π μS σ w w₀ ξ (Matrix.of x))
        (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ' (γ⁻¹ * Matrix.of x))) =ᵐ[μG]
      fun x => (⟪l w₀, ξ⟫_ℂ * (starRingEnd ℂ) ⟪l' w₀', ξ'⟫_ℂ) •
        rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w)) := by
    intro w₀ hw₀ w₀' hw₀' ξ ξ'
    filter_upwards [hGG] with x hx
    rw [Afun_eq_inner_smul_of_isEll hl hw₀ ξ hx, Afun_eq_inner_smul_of_isEll hl' hw₀' ξ' (hgrp.2.1 _ hγi _ hx), rankOneInnerOperator_smul_smul_eq_mul_conj_smul]
  obtain ⟨u, hu, hlu⟩ := hl.2.1
  obtain ⟨u', hu', hlu'⟩ := hl'.2.1
  have hint : Integrable
      (fun x : Mt k r => rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w))) μG := by
    obtain ⟨-, hI, -⟩ := GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' u hu u' hu'
      (l u) (l' u') γ hγ
    have hc : (⟪l u, l u⟫_ℂ * (starRingEnd ℂ) ⟪l' u', l' u'⟫_ℂ) ≠ 0 :=
      mul_ne_zero (inner_self_ne_zero.2 hlu) ((map_ne_zero _).2 (inner_self_ne_zero.2 hlu'))
    refine (hI.smul (⟪l u, l u⟫_ℂ * (starRingEnd ℂ) ⟪l' u', l' u'⟫_ℂ)⁻¹).congr ?_
    filter_upwards [hae u hu u' hu' (l u) (l' u')] with x hx
    rw [Pi.smul_apply, hx, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨hint, ?_⟩
  intro w₀ hw₀ w₀' hw₀' ξ ξ'
  obtain ⟨-, -, hO⟩ := GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' w₀ hw₀ w₀' hw₀'
    ξ ξ' γ hγ
  have hO2 : OO μG (Afun (psiGen k r z c) π μS σ w w₀ ξ) (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') γ =
      (⟪l w₀, ξ⟫_ℂ * (starRingEnd ℂ) ⟪l' w₀', ξ'⟫_ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) γ := by
    unfold OO
    rw [integral_congr_ae (hae w₀ hw₀ w₀' hw₀' ξ ξ'), integral_smul]
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hO2, eq_inv_smul_iff₀ hdne] at hO
  rw [← hO, smul_smul, inner_conj_symm]
  congr 1
  ring

end GlobalTheory.SgInf.EllName
end

