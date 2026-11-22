import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0035
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0159
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmThetaBaseVectorTranslatesIntegral
section
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ}
    (h : AnalyticOnNhd ℂ f Set.univ) : ContDiff ℂ ⊤ f :=
  contDiffOn_univ.1 (h.contDiffOn uniqueDiffOn_univ)

theorem contDiff_opU_one (L : PeriodPair) (s : ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.F.opU L s f) := by
  have hd : Differentiable ℂ (Formalism.L2.Th1.F.opU L s f) := by
    have h1 : Differentiable ℂ (fun z : ℂ => f (z + s)) := hf.comp (differentiable_id.add_const s)
    have h2 : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z s
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L s s / 2)) := by
      unfold Formalism.L2.Th1.F.herm
      fun_prop
    exact h1.mul h2
  exact hd.contDiff

theorem norm_sqrt_inv {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (hm : Nat.Coprime m q) :
    ‖ι (((Real.sqrt m : ℝ) : ℂ)⁻¹)‖ = 1 := by
  have h1 : (((Real.sqrt m : ℝ) : ℂ)) ^ 2 = (m : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; simp
  have h2 : ‖ι ((Real.sqrt m : ℝ) : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_natCast]
    exact GlobalTheory.MomOne.Basic.norm_nat_eq_one hm.symm
  have h3 : ‖ι ((Real.sqrt m : ℝ) : ℂ)‖ = 1 := by
    have := norm_nonneg (ι ((Real.sqrt m : ℝ) : ℂ))
    nlinarith [sq_nonneg (‖ι ((Real.sqrt m : ℝ) : ℂ)‖ - 1), sq_nonneg (‖ι ((Real.sqrt m : ℝ) : ℂ)‖ + 1)]
  rw [map_inv₀, norm_inv, h3, inv_one]

theorem norm_root {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) :
    ‖ι z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm).1 (by rw [← norm_pow, ← map_pow, hz, map_one, norm_one])

theorem translates_latInt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (t : D.what₂.Tau → ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) • t ∈ B.lamM → LatInt ι (Ω / ι δ₀) B.lamM (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
  intro D cc δ B hcc hδ q _ hq2 hjac hcop ι δ₀ θ Ω hPer t n hn hnt
  obtain ⟨g, e, hS, hidx, he, hten⟩ := GlobalTheory.T.exists_standard_isometry_fourthPower_split_prime D cc δ B hcc hδ q hq2 hjac hcop ι

  have hmem : B.thMM ∈ Formalism.L2.Th1.H.Th (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))
      (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))) B.lamM :=
    (thM_spec B.L B.ω₀ B.cq B.lamM B.gC B.kappa (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) B.kappa_ne_zero).1
  have hUs : ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) :=
    contDiff_of_analytic (Formalism.L2.Th1.H.opUAnalytic (D.what₂.Tau → ℂ) _ t B.thMM hmem.1)
  have hthd : Differentiable ℂ B.th0 := (Formalism.L2.Th1.F.th0Basic B.L B.ω₀ hS.per hS.half).1

  obtain ⟨S, hSr⟩ := (Formalism.L2.Th1.H.repsExist _ _ _ hS.idx₁).1
  have hshape := Formalism.L2.Th1.H.quadraticSemicharacter_identity_reformulated₂ B.L B.ω₀ D.what₂.Tau (hOne B.L D.what₂.Tau) B.lamM _ _ g hS e B.thMM hten S hSr t
  have hidxC : Nat.Coprime (Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
      (Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) q :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hidx).symm
  set Im := Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM) with hIm
  set St := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hSt
  set idx := Formalism.L2.Th1.H.relIdx St Im with hidxdef
  set v : Fin 4 × D.what₂.Tau → ℂ := g (fun w => t w.2) with hv
  set ω : ℂ_[q] := Ω / ι δ₀ with hω
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : q = 1 := by simpa using hn
    exact (Fact.out : q.Prime).one_lt.ne' h1

  have hnv : (n : ℂ) • v ∈ Im := by
    refine AddSubgroup.mem_map.2 ⟨(n : ℂ) • (fun w : Fin 4 × D.what₂.Tau => t w.2), fun a => hnt, ?_⟩
    show g ((n : ℂ) • fun w : Fin 4 × D.what₂.Tau => t w.2) = (n : ℂ) • v
    rw [map_smul]

  have hord : ∀ x ∈ S, ∀ w, ((n * idx : ℕ) : ℂ) * (v w + x w) ∈ B.L.lattice := by
    intro x hx w
    have h1 : (n : ℂ) • (v + x) ∈ Im := by
      rw [smul_add]
      refine add_mem hnv ?_
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hSr.1 x hx) n
    have h2 := Formalism.L2.Th1.H.relIdx_smul_mem St Im h1
    have h3 := ((AddSubgroup.mem_pi Set.univ).1 h2) w (Set.mem_univ _)
    have e1 : ((n * idx : ℕ) : ℂ) * (v w + x w) = (((idx : ℕ) : ℂ) • (n : ℂ) • (v + x)) w := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      push_cast
      ring
    rw [e1]
    exact h3
  have hNq : Nat.Coprime (n * idx) q := Nat.Coprime.mul_left hn hidxC

  have hfac : ∀ x ∈ S, ∀ w,
      LatInt ι ω St (fun y : Fin 4 × D.what₂.Tau → ℂ => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) := by
    intro x hx w
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ (Fin 4 × D.what₂.Tau → ℂ) ω (lamOf D cc δ) St
      (ContinuousLinearMap.proj w) _ (contDiff_opU_one B.L _ hthd) ?_
      (GlobalTheory.T.cm_theta_translates_prime_to_q_integral D cc δ B hcc hδ q hq2 hjac hcop ι δ₀ θ Ω hPer _ (n * idx) hNq (hord x hx w))
    intro y hy
    refine ⟨1, Nat.coprime_one_left q, ?_⟩
    rw [one_smul, ← B.lat]
    exact ((AddSubgroup.mem_pi Set.univ).1 hy) w (Set.mem_univ _)
  have hcd : ∀ (x : Fin 4 × D.what₂.Tau → ℂ) (w : Fin 4 × D.what₂.Tau),
      ContDiff ℂ ⊤ (fun y : Fin 4 × D.what₂.Tau → ℂ => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) :=
    fun x w => (contDiff_opU_one B.L _ hthd).comp (contDiff_apply ℂ ℂ w)
  have hprod : ∀ x : Fin 4 × D.what₂.Tau → ℂ, ContDiff ℂ ⊤ (fun y : Fin 4 × D.what₂.Tau → ℂ =>
      ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) :=
    fun x => contDiff_prod fun w _ => hcd x w

  have hP : ∀ x ∈ S, LatInt ι ω St (fun y : Fin 4 × D.what₂.Tau → ℂ =>
      ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) := fun x hx =>
    (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (Fin 4 × D.what₂.Tau → ℂ) ω St).1 (Fin 4 × D.what₂.Tau)
      (fun w y => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) (hcd x) (hfac x hx)

  set r : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun x => e * ((Real.sqrt idx : ℝ) : ℂ)⁻¹
      * Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) x
      * Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.H.altE (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)) with hr
  have hrn : ∀ x ∈ S, ‖ι (r x)‖ ≤ 1 := by
    intro x hx
    have hx2 := hSr.1 x hx
    have hb : ‖ι (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) x)‖ = 1 := by
      rcases hS.betaSemi.1 x hx2 with h | h <;> simp [h]
    have hph : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I
        * (Formalism.L2.Th1.H.altE (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)))‖ = 1 :=
      norm_root ι (m := 2 * n) (by omega)
        (Formalism.L2.Th1.H.phase_root_selfDual _ Im hS.selfDual n hnv hx2)
    simp only [hr, map_mul, norm_mul, he, norm_sqrt_inv ι hidxC, hb, hph, one_mul, le_refl]
  set G : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun y =>
    ∑ x ∈ S, r x * ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w) with hG
  have hGd : ContDiff ℂ ⊤ G :=
    ContDiff.sum fun x _ => contDiff_const.mul (hprod x)
  have hGl : LatInt ι ω St G :=
    (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (Fin 4 × D.what₂.Tau → ℂ) ω St).2 _ S r _ (fun x _ => hprod x) hrn hP

  have hpull : LatInt ι ω (Formalism.L2.Th1.H.pow4 B.lamM)
      (fun z => G (LinearMap.toContinuousLinearMap (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) z)) := by
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι _ _ ω St _ _ G hGd ?_ hGl
    intro x hx
    refine ⟨idx, hidxC, ?_⟩
    have h1 : g x ∈ Im := AddSubgroup.mem_map.2 ⟨x, hx, rfl⟩
    have h2 := Formalism.L2.Th1.H.relIdx_smul_mem St Im h1
    rw [Nat.cast_smul_eq_nsmul] at h2
    exact h2
  have hfun : (fun z => G (LinearMap.toContinuousLinearMap (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) z))
      = Formalism.L2.Th1.H.tens4 (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
    funext z
    have hz := hshape (g z)
    rw [LinearEquiv.symm_apply_apply] at hz
    rw [hz]
    rfl
  rw [hfun] at hpull
  exact GlobalTheory.T.latticeJetsAreBoundedMoments_of_tensorFourthPower q ι D.what₂.Tau ω B.lamM _ hUs hpull

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignature
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix ComplexConjugate
attribute [local instance] IsCMField.starRing

namespace GlobalTheory.SelfDualDet
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy GlobalTheory.LocalLattice

theorem congr_of_hasSignature {r p q : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ Bᵀ = Qᵀ * Aᵀ * Q.map conj := by
  obtain ⟨e, P, hP⟩ := hA
  obtain ⟨f, R, hR⟩ := hB
  have hc : ∀ M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ :=
    fun _ => rfl
  rw [hc] at hP hR
  have h1 : Matrix.reindex f f B = (P * R⁻¹).1ᴴ * Matrix.reindex e e A * (P * R⁻¹).1 := by
    have h2 : (R⁻¹).1ᴴ * R.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    calc Matrix.reindex f f B = ((R⁻¹).1ᴴ * R.1ᴴ) * Matrix.reindex f f B * (R.1 * (R⁻¹).1) := by
          rw [h2, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (R⁻¹).1ᴴ * (R.1ᴴ * Matrix.reindex f f B * R.1) * (R⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hR, ← hP, Units.val_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
  generalize P * R⁻¹ = S at h1
  refine ⟨S.1.submatrix e f, ?_, ?_⟩
  · refine (Matrix.isUnit_det_of_right_inverse (B := (S⁻¹).1.submatrix f e) ?_).ne_zero
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  · have h3 := congrArg (fun M => (Matrix.submatrix M f f)ᵀ) h1
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] at h3
    rw [← Matrix.submatrix_mul_equiv _ _ f e f, ← Matrix.submatrix_mul_equiv _ _ f e e,
      Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] at h3
    exact h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_eq_of_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {r r' : ℕ} (h : r = r')
    {G : Matrix (Fin r) (Fin r) E} {G' : Matrix (Fin r') (Fin r') E}
    (hG : ∀ a b, cc (Gᵀ a b) = Gᵀ b a) (hG' : ∀ a b, cc (G'ᵀ a b) = G'ᵀ b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    {L : Submodule (𝓞 E) (Fin r → E)} {L' : Submodule (𝓞 E) (Fin r' → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm G'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) :
    ∃ z : E, G'.det = z * star z * G.det := by
  subst h
  obtain ⟨P, -, hP⟩ := congr_of_modular (E := E) (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun _ hz => mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hz)))
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd)
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd')
    fun τ => by
      obtain ⟨p, q, h1, h2⟩ := hs τ
      exact congr_of_hasSignature h1 h2
  have h1 := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_transpose,
    Published.det_map_cc] at h1
  refine ⟨P.det, h1.trans ?_⟩
  change _ = _ * cc _ * _
  ring

theorem det_eq_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  intro E _ _ _ hc W₁ W₂ h₁ h₂ hr hs
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  exact det_eq_of_matrix hr (fun a b => W₁.herm.eq (W₁.frame b) (W₁.frame a))
    (fun a b => W₂.herm.eq (W₂.frame b) (W₂.frame a))
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₁).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₂).ne_zero
    (isLattice_coordLat W₁ W₁.L0 W₁.standardTuple_isLattice) (isLattice_coordLat W₂ W₂.L0 W₂.standardTuple_isLattice)
    (selfDual_coordLat W₁ W₁.L0 W₁.baseLattice_isUnimodular) (selfDual_coordLat W₂ W₂.L0 W₂.baseLattice_isUnimodular)
    fun τ => ⟨_, _, h₁ τ, hs τ ▸ h₂ τ⟩

end GlobalTheory.SelfDualDet
end

