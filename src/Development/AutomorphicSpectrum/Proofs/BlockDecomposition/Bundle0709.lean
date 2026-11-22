import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0355
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExp
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0566
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0053
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0039
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0533
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0700
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeUnramified
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriKeeps
section
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.LeviIwa

theorem block_qr {D : ℕ} (τ : Fin D → ℕ) (hτ : Monotone τ) (h : Matrix (Fin D) (Fin D) ℂ) (hu : IsUnit h)
    (ht : h.BlockTriangular τ) : ∃ k ∈ Matrix.unitaryGroup (Fin D) ℂ, ∃ b : Matrix (Fin D) (Fin D) ℂ,
      h = k * b ∧ b.BlockTriangular id ∧ k.BlockTriangular τ ∧ kᴴ.BlockTriangular τ := by
  obtain ⟨k, hk, b, rfl, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular h hu
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hbu : IsUnit b := by
    have : kᴴ * (k * b) = b := by rw [← Matrix.mul_assoc, hk2, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk2).mul hu
  have hbτ : b.BlockTriangular τ := fun i j hij => hb (by
    by_contra hc
    exact absurd (hτ (not_lt.1 hc)) (not_le.2 hij))
  haveI : Invertible b := hbu.invertible
  have hbi : (b⁻¹).BlockTriangular τ := Matrix.blockTriangular_inv_of_blockTriangular hbτ
  have hkeq : k = (k * b) * b⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu), Matrix.mul_one]
  have hkt : k.BlockTriangular τ := hkeq ▸ ht.mul hbi
  have hkinv : kᴴ = k⁻¹ := (Matrix.inv_eq_left_inv hk2).symm
  haveI : Invertible k := (IsUnit.of_mul_eq_one _ hk1).invertible
  exact ⟨k, hk, b, rfl, hb, hkt, hkinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hkt⟩

theorem blockTri_keeps {D : ℕ} {τ : Fin D → ℕ} {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.BlockTriangular τ) {i : ℕ}
    {v : Fin D → ℂ} (hv : ∀ c, i ≤ τ c → v c = 0) : ∀ c, i ≤ τ c → (M *ᵥ v) c = 0 := by
  intro c hc
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : i ≤ τ d
  · rw [hv d hd, mul_zero]
  · rw [hM (lt_of_lt_of_le (not_le.1 hd) hc), zero_mul]

theorem detOn_unitary {n : ℕ} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, k *ᵥ y ∈ V) (h' : ∀ y ∈ V, kᴴ *ᵥ y ∈ V) :
    GlobalTheory.FlagMeas.detOn k V = 1 := by
  have e := GlobalTheory.RealInd.detOn_mul h' h
  rw [Matrix.mem_unitaryGroup_iff'.1 hk |> fun x => (show kᴴ * k = 1 from x), GlobalTheory.RealInd.detOn_one,
    GlobalTheory.LeviPolar.detOn_conjTranspose n k V h h'] at e
  have h0 := GlobalTheory.LeviPolar.detOn_nonneg k V
  nlinarith

open GlobalTheory.RealInd in

theorem iwaOn_leviOne : ∀ {n a : ℕ} (ε : Fin n → Bool) (j : Fin a → ℕ) (W : GlobalTheory.RealInd.Flag n a),
    GlobalTheory.FlagMeas.IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
      PositivityTheory.Tls2.Iua.IwaOn (GlobalTheory.RealInd.mats (GlobalTheory.RealInd.leviOne ε W)) := by
  intro n a ε j W hW _
  obtain ⟨h0, hm, -, hiso⟩ := hW
  obtain ⟨D, C, τ, hC, hτ, hτa, hfl⟩ := GlobalTheory.T.flag_orthonormal_adapted_basis W h0 hm
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := PI.UpqRep.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := PI.UpqRep.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJdef
  have hlast : ∀ v, C *ᵥ v ∈ W (Fin.last a) := fun v =>
    (hfl _ _).2 ⟨v, rfl, fun c hc => absurd (hτa c) (by simpa using hc)⟩
  have hCJ : Cᴴ * J * C = 0 := by
    ext c d
    have := hiso _ (hlast (Pi.single c 1)) _ (hlast (Pi.single d 1))
    have e : star (Pi.single c (1 : ℂ)) = (Pi.single c 1 : Fin D → ℂ) := by
      ext x
      by_cases hx : x = c
      · subst hx; simp
      · simp [hx]
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e,
      Matrix.mulVec_single_one, single_one_dotProduct] at this
    simpa using this
  obtain ⟨m, R, ε', hR, hJR, hCR, hsum⟩ := GlobalTheory.T.isotropic_hyperbolic_complement ε C hC hCJ
  obtain ⟨U₀, hU₀, hI⟩ := CompanionTheory.D.gk.admitted.iwasawa_decomposition_unitary_group m ε'
  obtain ⟨U, hU, hTri⟩ := GlobalTheory.T.unitary_extension_of_block J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum U₀ hU₀
  refine ⟨U, hU, fun g hg => ?_⟩
  obtain ⟨hgU, hgk, hgd⟩ := GlobalTheory.LeviPolar.mem_mats_leviOne.1 hg
  have hgU' : gᴴ * J * g = J := hgU
  have keep : ∀ x : Matrix (Fin n) (Fin n) ℂ, (∀ y ∈ W (Fin.last a), x *ᵥ y ∈ W (Fin.last a)) →
      x * C = C * (Cᴴ * x * C) := fun x hx => by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨w, hw, -⟩ := (hfl _ _).1 (hx _ (hlast v))
    have e : (Cᴴ * x * C) *ᵥ v = w := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hw, ← Matrix.mulVec_mulVec, e]
  set h := Cᴴ * g * C with hh
  have hgC : g * C = C * h := keep g fun y hy => (hgk _ y hy).1
  have hgC' : gᴴ * C = C * hᴴ := by
    have := keep gᴴ fun y hy => (hgk _ y hy).2
    rw [this, hh]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  have htri : h.BlockTriangular τ := by
    intro c d hdc
    have hda : τ d + 1 < a + 1 := by have := hτa d; omega
    have h1 : C *ᵥ Pi.single d 1 ∈ W ⟨τ d + 1, hda⟩ := (hfl _ _).2 ⟨_, rfl, fun c' hc' => by
      have : c' ≠ d := by rintro rfl; simp at hc'
      simp [this]⟩
    obtain ⟨v, hv, hv0⟩ := (hfl _ _).1 ((hgk _ _ h1).1)
    have h2 : h *ᵥ Pi.single d 1 = v := by
      rw [hh, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec, hC,
        Matrix.one_mulVec]
    have h3 := congrFun h2 c
    rw [Matrix.mulVec_single_one] at h3
    simpa [hv0 c (by simpa using hdc)] using h3
  obtain ⟨hu, hgJC, hgR, hgRU⟩ := GlobalTheory.T.parabolic_stabilizer_block_unit J (Formalism.REAL.Jm ε') C R hJ hJh hC hR hJR hCR hsum g h hgU' hgC hgC'
  obtain ⟨k₀, hk₀, b, hb, hbT, hk₀T, hk₀T'⟩ := block_qr τ hτ h hu htri
  obtain ⟨kR, ⟨hkR, hkRJ⟩, sR, hsR, hgks, hsT⟩ := hI (Rᴴ * g * R) hgRU
  obtain ⟨k, hk, hkJ, hkC, hkC', hkR', hkJC⟩ := GlobalTheory.T.unitary_lift_commuting_involution J (Formalism.REAL.Jm ε') C R hJ hJh hC hCJ hR hJR hCR hsum
    k₀ hk₀ kR hkR hkRJ
  have hk1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hk2 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hk01 : k₀ᴴ * k₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hk₀
  have hkR1 : kRᴴ * kR = 1 := Matrix.mem_unitaryGroup_iff'.1 hkR
  have kk : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → k *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC, ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T hv⟩
  have kk' : ∀ (i : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W i → kᴴ *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨v, rfl, hv⟩ := (hfl _ _).1 hy
    exact (hfl _ _).2 ⟨k₀ᴴ *ᵥ v, by rw [Matrix.mulVec_mulVec, hkC', ← Matrix.mulVec_mulVec], blockTri_keeps hk₀T' hv⟩
  have hkG : k ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change kᴴ * J * k = J; rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hk2, Matrix.one_mul],
      fun i y hy => ⟨kk i y hy, kk' i y hy⟩, fun i => detOn_unitary hk _ (kk i) (kk' i)⟩
  have hkhG : kᴴ ∈ mats (leviOne ε W) := GlobalTheory.LeviPolar.mem_mats_leviOne.2
    ⟨by change (kᴴ)ᴴ * J * kᴴ = J; rw [conjTranspose_conjTranspose, hkJ, Matrix.mul_assoc, hk1, Matrix.mul_one],
      fun i y hy => ⟨kk' i y hy, by simpa using kk i y hy⟩,
      fun i => detOn_unitary (Matrix.mem_unitaryGroup_iff.2 (by simpa [star_eq_conjTranspose] using hk2)) _ (kk' i)
        (by rw [conjTranspose_conjTranspose]; exact kk i)⟩
  refine ⟨k, ⟨hkG, hk⟩, kᴴ * g, GlobalTheory.LeviPolar.mats_mul hkhG hg, by rw [← Matrix.mul_assoc, hk1, Matrix.one_mul], ?_⟩
  have hbu : IsUnit b := by
    have : k₀ᴴ * h = b := by rw [hb, ← Matrix.mul_assoc, hk01, Matrix.one_mul]
    rw [← this]
    exact (IsUnit.of_mul_eq_one _ hk01).mul hu
  haveI : Invertible b := hbu.invertible
  have hci : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbT
  have hbb : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det b).1 hbu)
  have hhinv : (hᴴ)⁻¹ = k₀ * (b⁻¹)ᴴ := Matrix.inv_eq_right_inv (by
    rw [hb, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k₀ᴴ, hk01, Matrix.one_mul,
      ← conjTranspose_mul, hbb, conjTranspose_one])
  refine hTri (kᴴ * g) b (b⁻¹)ᴴ (U₀ᴴ * sR * U₀) ?_ ?_ ?_ hbT hsT ?_
  · rw [Matrix.mul_assoc, hgC, ← Matrix.mul_assoc, hkC', Matrix.mul_assoc, hb, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · have hU1 : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, hgR, ← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc kᴴ, hkR',
      Matrix.mul_assoc R, hgks, ← Matrix.mul_assoc kRᴴ, hkR1, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₀, hU1, Matrix.one_mul]
  · rw [Matrix.mul_assoc, hgJC, ← Matrix.mul_assoc, hkJC, Matrix.mul_assoc, hhinv, ← Matrix.mul_assoc k₀ᴴ, hk01,
      Matrix.one_mul]
  · intro x y hxy
    have := hci (show id x < id y from hxy)
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.LeviIwa
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Brat
section
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisBrat

open scoped TensorProduct NumberField.AdeleRing
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

theorem brat : BRat := by
  intro F E _ _ _ _ _ σ χ c _ _ _ _
  refine ⟨fun y => ?_, fun e x h => ?_⟩
  · change (algebraMap F (AF F) y) ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] (algebraMap F E y)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · obtain ⟨g, hg⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F E))
    have g1 : g 1 = 1 := by
      have := LinearMap.congr_fun hg (1 : F)
      simpa using this
    have h' : (1 : AF F) ⊗ₜ[F] e = x ⊗ₜ[F] (1 : E) := h
    have h2 := congrArg (fun t => TensorProduct.rid F (AF F) (LinearMap.lTensor (AF F) g t)) h'
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at h2
    refine ⟨g e, ?_⟩
    rw [← h2, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CompanionTheory.EisBrat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardResidueEqQV
section
noncomputable section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open PositivityTheory.Rg.BcB.F.Tail.BS
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JacEigAt

theorem qV_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qV E w := by
  unfold qV
  exact Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem card_residue_eq_qV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card 𝓀[w.adicCompletion E] = qV E w := by
  have h := GlobalTheory.LocLanglands.resCard_eq_normV w
  simpa [GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

theorem modExp_points (n : ℕ) (a : Fin n) :
    modExp (fun _ : Fin n => Unit) a = (n : ℤ) - 1 - 2 * (a : ℕ) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  have ha := a.2
  simp only [modExp, Fintype.card_unique, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, h1, h2,
    Fin.card_Ioi, Fin.card_Iio]
  omega

theorem nabs_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (h : ord k ϖ = 1) (m : ℤ) :
    GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) := by
  have h1 : GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = GlobalTheory.SplitWeil.nabs k ϖ ^ m := by
    simp [GlobalTheory.SplitWeil.nabs]
  rw [h1, GlobalTheory.LGrp.nabs_eq_zpow, h, _root_.zpow_neg, zpow_one, _root_.inv_zpow, _root_.zpow_neg]

theorem prod_zpow_sum {ι : Type} (s : Finset ι) (r : ℂ) (hr : r ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, r ^ f a = r ^ ∑ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hr]

theorem absPow_term {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (e m : ℤ) :
    (absPow (w.adicCompletion E) ((e : ℂ) / 2) (ϖ ^ m) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (-(e * m)) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  set r : ℝ := Real.sqrt (qV E w : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hq
  have hrq : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = r ^ (2 : ℤ) := by
    have : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = qV E w := by
      simp [GlobalTheory.SplitWeil.resCard, card_residue_eq_qV]
    rw [this, hr, zpow_ofNat, Real.sq_sqrt hq.le]
  have hs : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hs, val_absPow_ofReal, nabs_zpow ϖ h, hrq, ← _root_.zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hr0.le]
  have : (((2 * -m : ℤ) : ℝ)) * ((e : ℝ) / 2) = ((-(e * m) : ℤ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_intCast]
  push_cast
  rfl

theorem deltaHalf_inv {E : Type} [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (x : Fin n → ℤ) :
    (((deltaHalf (w.adicCompletion E) (fun _ : Fin n => Unit)
        (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i))⁻¹ : ℂˣ) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have hr : (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hd : ∀ i, GeneralLinearGroup.det
      (leviTorus (w.adicCompletion E) (Fin n) (fun i => ϖ ^ x i) i) = ϖ ^ x i :=
    fun i => congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv fun i => ϖ ^ x i) i
  rw [Units.val_inv_eq_inv_val, deltaHalf_apply, Units.coe_prod]
  simp only [hd, absPow_term w ϖ h, modExp_points]
  rw [prod_zpow_sum _ _ hr, ← _root_.zpow_neg, Finset.sum_neg_distrib, neg_neg]

end GlobalTheory.CompanionTheory.JacEigAt

open GlobalTheory.CompanionTheory.JacEigAt in
theorem GlobalTheory.CompanionTheory.JacEigAt.jacEig : JacEig := by
  intro E _ _ _ n w V _ _ π hπ ϖ hϖ ξ c x hx u hu heig
  have hord : ord (w.adicCompletion E) ϖ = 1 := (GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ
  have h := GlobalTheory.T.jacquet_hecke_jacHk (w.adicCompletion E) n V π hπ ϖ hord x hx u hu
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have hqh : qh w ≠ 0 := by
    unfold qh
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hcard : ((Nat.card 𝓀[w.adicCompletion E] : ℕ) : ℂ) = qh w ^ (2 : ℤ) := by
    rw [card_residue_eq_qV, qh, zpow_ofNat, ← Complex.ofReal_pow, Real.sq_sqrt hq.le]
    simp
  set S : ℤ := ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i with hS
  have h' : (Submodule.Quotient.mk (hkS π (iwGL n w) (dcos n w (tdiag ϖ x)) u) :
      Jacquet π (unipB (w.adicCompletion E) (Fin n))) =
      ((Nat.card 𝓀[w.adicCompletion E] : ℂ) ^ S) •
        jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) := h
  rw [heig, Submodule.Quotient.mk_smul, hcard, ← _root_.zpow_mul] at h'
  have hj : jacB π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) =
      (qh w ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) := by
    have := jac_mk (points (Fin n)) π (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i) u
    rw [deltaHalf_inv n w ϖ hord x] at this
    exact this
  have e2 : qh w ^ (2 * S) = qh w ^ S * qh w ^ S := by
    rw [two_mul, zpow_add₀ hqh]
  have hS0 : qh w ^ S ≠ 0 := zpow_ne_zero _ hqh
  rw [e2] at h'
  rw [hj]
  have h3 : (qh w ^ S) • ((qh w ^ S) • jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u)) =
      (qh w ^ S) • ((c * pw ξ x) • (Submodule.Quotient.mk u : Jacquet π (unipB (w.adicCompletion E) (Fin n)))) := by
    rw [smul_smul, ← h', smul_smul]
    congr 1
    ring
  exact smul_right_injective _ hS0 h3

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeToCohomologyIso
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

variable {R : Type} [CommRing R]

def colHMap {K L : DCx.{1} R} (φ : DCx.Hom K L (RingHom.id R)) (q : ℕ) :
    Cx.Hom (colH K q) (colH L q) (RingHom.id R) where
  f p := (φ.col p).mapH q
  comm p x := by
    obtain ⟨a, ha, rfl⟩ := (P.cls_surj (K.col p) q).1 x
    have h1 : (K.col (p + 1)).d q ((colMap K p).f q a) = 0 := by
      rw [(colMap K p).comm, ha, map_zero]
    have h2 : (L.col p).d q ((φ.col p).f q a) = 0 := by
      rw [(φ.col p).comm, ha, map_zero]
    have h3 : (L.col (p + 1)).d q ((colMap L p).f q ((φ.col p).f q a)) = 0 := by
      rw [(colMap L p).comm, h2, map_zero]
    have h4 : (L.col (p + 1)).d q ((φ.col (p + 1)).f q ((colMap K p).f q a)) = 0 := by
      rw [(φ.col (p + 1)).comm, h1, map_zero]
    change (colMap L p).mapH q ((φ.col p).mapH q _) = (φ.col (p + 1)).mapH q ((colMap K p).mapH q _)
    rw [P.mapH_cls _ q a ha h2, P.mapH_cls _ q _ h2 h3, P.mapH_cls _ q a ha h1, P.mapH_cls _ q _ h1 h4]
    have e : (colMap L p).f q ((φ.col p).f q a) = (φ.col (p + 1)).f q ((colMap K p).f q a) := φ.ch p q a
    exact ((P.cls_surj (L.col (p + 1)) q).2.2.1 _ _ h3 h4).2 (by rw [e, sub_self]; exact Submodule.zero_mem _)

variable {C : Type 1} [Category.{0} C]

theorem restr_bij (F : C ⥤ ModuleCat.{0} R) (n : ℕ) :
    Function.Bijective ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n) := by
  let E : C ⥤ Type := (Functor.const C).obj PUnit.{1}
  let G : C ⥤ E.Elements :=
    { obj := fun T => ⟨T, PUnit.unit⟩
      map := fun φ => ⟨φ, rfl⟩ }
  refine P.mapH_bij _ (fun k => ⟨fun x y h => ?_, fun y => ?_⟩) n
  · funext c
    exact congrFun h (c ⋙ G)
  · exact ⟨fun c => y (c ⋙ G), funext fun s => rfl⟩

variable {ι : Type}

def eTot (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (n : ℕ) : CH.H F n ≃ₗ[R] (dbl U hU F).tot.H n :=
  (LinearEquiv.ofBijective _ (restr_bij F n)).trans
    (LinearEquiv.ofBijective _ (P.cech_desc (idxπ U hU) F (fun T x => by
      obtain ⟨α, hα⟩ := hc T
      exact ⟨⟨α, hα⟩, rfl⟩) n))

theorem eTot_apply (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (n : ℕ) (x : CH.H F n) :
    eTot F U hU hc n x = (CH.cechAugRow (idxπ U hU) F).edge.mapH n
      ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n x) := rfl

theorem col_sub (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (p q : ℕ) (hq : q ≠ a) :
    Subsingleton (((dbl U hU F).col p).H q) := by
  have := fun i => hv p i q hq
  exact (colCmp_bij U hU F p q).1.subsingleton

def eRow (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) :
    (dbl U hU F).tot.H (a + j) ≃ₗ[R] (colH (dbl U hU F) a).H j :=
  Classical.choose (GlobalTheory.T.double_complex_degenerate_column_iso (dbl U hU F) a (fun p q hq => col_sub F U hU a hv p q hq) j)

theorem eRow_clsZ (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ)
    (z : Zf (dbl U hU F) (a + j) j) :
    eRow F U hU a hv j (clsZ (dbl U hU F) (a + j) j z) = leadE (dbl U hU F) j a z :=
  Classical.choose_spec (GlobalTheory.T.double_complex_degenerate_column_iso (dbl U hU F) a (fun p q hq => col_sub F U hU a hv p q hq) j) z

def eCol (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a j : ℕ) :
    (colH (dbl U hU F) a).H j ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j :=
  LinearEquiv.ofBijective _ (P.mapH_bij (colCmp U hU F a) (fun p => colCmp_bij U hU F p a) j)

theorem eCol_cls (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a j : ℕ)
    (x : (colH (dbl U hU F) a).X j) (hx : (colH (dbl U hU F) a).d j x = 0)
    (h : (CrystallineSemistableComparison.Pb.cechH F U a).cx.d j ((colCmp U hU F a).f j x) = 0) :
    eCol F U hU a j ((colH (dbl U hU F) a).cls x hx) = (CrystallineSemistableComparison.Pb.cechH F U a).cx.cls _ h :=
  P.mapH_cls _ j x hx h

def eDeg (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) :
    CH.H F (a + j) ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j :=
  (eTot F U hU hc (a + j)).trans ((eRow F U hU a hv j).trans (eCol F U hU a j))

theorem eDeg_apply (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) (x : CH.H F (a + j)) :
    eDeg F U hU hc a hv j x = eCol F U hU a j (eRow F U hU a hv j (eTot F U hU hc (a + j) x)) := rfl

theorem cech_deg : ∀ (R : Type) [CommRing R], ∃ e : ∀ {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ a : ℕ,
    (∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) → ∀ j : ℕ,
      CH.H F (a + j) ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j,
    ∀ {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type}
      (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T)
      (hU' : ∀ α, Cosieve (U' α)) (hc' : ∀ T, ∃ α, U' α T) (a : ℕ)
      (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r))
      (hv' : ∀ n (i : Fin (n + 1) → ι') r, r ≠ a → Subsingleton (HU F' (capT U' i) r)) (m : CH.Mor F F' (RingHom.id R))
      (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (j : ℕ) (c : (CrystallineSemistableComparison.Pb.cechH F U a).X j)
      (h0 : (CrystallineSemistableComparison.Pb.cechH F U a).cx.d j c = 0)
      (h1 : (CrystallineSemistableComparison.Pb.cechH F' U' a).cx.d j (fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      m.pull (a + j) ((e F U hU hc a hv j).symm ((CrystallineSemistableComparison.Pb.cechH F U a).cx.cls c h0)) =
        (e F' U' hU' hc' a hv' j).symm ((CrystallineSemistableComparison.Pb.cechH F' U' a).cx.cls _ h1) := by
  intro R _
  refine ⟨fun F _ U hU hc a hv j => eDeg F U hU hc a hv j, ?_⟩
  intro C C' _ _ F F' ι ι' U U' hU hc hU' hc' a hv hv' m τ hτ j c h0 h1
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.cech_double_complex_map F F' U U' hU hU' m τ hτ
  obtain ⟨c₁, rfl⟩ := (colCmp_bij U hU F j a).2 c
  have hd₁ : (colH (dbl U hU F) a).d j c₁ = 0 := by
    refine (colCmp_bij U hU F (j + 1) a).1 ?_
    rw [← (colCmp U hU F a).comm, h0, map_zero]
  obtain ⟨z, hz⟩ := GlobalTheory.T.double_complex_lead_surjective (dbl U hU F) a j
    (fun p q hq => col_sub F U hU a hv p q hq.ne) ((colH (dbl U hU F) a).cls c₁ hd₁)
  have hy : (eDeg F U hU hc a hv j).symm ((CrystallineSemistableComparison.Pb.cechH F U a).cx.cls _ h0) =
      (eTot F U hU hc (a + j)).symm (clsZ (dbl U hU F) (a + j) j z) := by
    rw [LinearEquiv.symm_apply_eq, eDeg_apply, LinearEquiv.apply_symm_apply, eRow_clsZ, hz, eCol_cls F U hU a j c₁ hd₁ h0]
  obtain ⟨z', hz'1, y', hy', y₀, hy₀, e1, e2, e3⟩ := GlobalTheory.T.double_complex_map_lead_compat (dbl U hU F) (dbl U' hU' F') φ a j z
  show m.pull (a + j) ((eDeg F U hU hc a hv j).symm _) = (eDeg F' U' hU' hc' a hv' j).symm _
  rw [hy, LinearEquiv.eq_symm_apply, eDeg_apply]
  have h2 : eTot F' U' hU' hc' (a + j) (m.pull (a + j) ((eTot F U hU hc (a + j)).symm (clsZ (dbl U hU F) (a + j) j z))) =
      clsZ (dbl U' hU' F') (a + j) j z' := by
    rw [hz'1, ← LinearEquiv.apply_symm_apply (eTot F U hU hc (a + j)) (clsZ (dbl U hU F) (a + j) j z)]
    simp only [LinearEquiv.symm_apply_apply]
    exact (hφ1 _ _).symm
  rw [h2, eRow_clsZ, e2]
  have h3 : (colH (dbl U hU F) a).cls y₀ hy₀ = (colH (dbl U hU F) a).cls c₁ hd₁ := e1.symm.trans hz
  have hd₂ : (colH (dbl U' hU' F') a).d j ((colHMap φ a).f j c₁) = 0 := by
    rw [(colHMap φ a).comm, hd₁, map_zero]
  have h4 : (colH (dbl U' hU' F') a).cls y' hy' = (colH (dbl U' hU' F') a).cls _ hd₂ := by
    have hd₃ : (colH (dbl U' hU' F') a).d j ((colHMap φ a).f j y₀) = 0 := by
      rw [(colHMap φ a).comm, hy₀, map_zero]
    have h5 := congrArg ((colHMap φ a).mapH j) h3
    rw [P.mapH_cls _ j _ hy₀ hd₃, P.mapH_cls _ j _ hd₁ hd₂] at h5
    subst e3
    exact h5
  have h6 : (colCmp U' hU' F' a).f j ((colHMap φ a).f j c₁) =
      fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a ((colCmp U hU F a).f j c₁ (τ ∘ i)) := by
    funext i
    exact hφ2 j a c₁ i
  have h7 : (CrystallineSemistableComparison.Pb.cechH F' U' a).cx.d j ((colCmp U' hU' F' a).f j ((colHMap φ a).f j c₁)) = 0 := by
    rw [(colCmp U' hU' F' a).comm, hd₂, map_zero]
  rw [h4, eCol_cls F' U' hU' a j _ hd₂ h7]
  exact ((P.cls_surj (CrystallineSemistableComparison.Pb.cechH F' U' a).cx j).2.2.1 _ _ h7 h1).2 (by rw [h6, sub_self]; exact Submodule.zero_mem _)

end GlobalTheory.CompanionTheory.CechSerre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHoldsStatement
section
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_unit_holds : CompUnit := by
  first | exact @GlobalTheory.CompanionTheory.CompUnitary.compUnit | exact GlobalTheory.CompanionTheory.CompUnitary.compUnit | (intros; apply GlobalTheory.CompanionTheory.CompUnitary.compUnit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolicStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_multiplier_mirabolic : PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.CMGood → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.MirGen → PositivityTheory.RgEis.CMMir := by
  first | exact @GlobalTheory.CompanionTheory.CMMirror.cmMir | exact GlobalTheory.CompanionTheory.CMMirror.cmMir | (intros; apply GlobalTheory.CompanionTheory.CMMirror.cmMir <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeUnramifiedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_volume_unramified : PositivityTheory.SiegelWeilFormula.Gunr.VolLat := by
  first | exact @GlobalTheory.CompanionTheory.GunrVol.volLat | exact GlobalTheory.CompanionTheory.GunrVol.volLat | (intros; apply GlobalTheory.CompanionTheory.GunrVol.volLat <;> assumption)
end

