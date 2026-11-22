import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0640
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0642
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0673
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.GaussThetaFinite

theorem isDatum_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ) (c : ℂ) (h : IsDatum M ψ crd Φ f) :
    IsDatum M ψ crd (c • Φ) (c • f) := by
  refine ⟨Submodule.smul_mem _ c h.1, fun u => ?_⟩
  have h2 := h.2 u
  simp only [Pi.smul_apply, smul_eq_mul, ← h2, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr] at *
  rw [← tsum_mul_left]
  congr 1; ext ξ; ring

theorem eq_zero_of_isDatum_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} [AddCommGroup Z] (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) ≃+ Z)
    (f : Z → ℂ) (h : IsDatum M ψ crd 0 f) : f = 0 := by
  funext w
  have h2 := h.2 (crd.symm w)
  rw [AddEquiv.apply_symm_apply] at h2
  rw [← h2]
  simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem fockVac_of_isGauss : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), M.IsGauss Bs.ψ Bs.emb g →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f : WO S X → ℂ, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ τ : D.what₂.Tau, IsFockVacAt (heisO ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ)) f := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac f hf τ
  unfold IsFockVacAt
  intro z
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hBs.std
  obtain ⟨g₁, h₁⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M Bs.ψ hstd g _ (GlobalTheory.T.archimedean_preimage_realPlace_line D θ hθ ε S X e cS hcS τ z)
  obtain ⟨g₁', h₁'⟩ := GlobalTheory.T.exists_heisenberg_derivative_archimedean_direction M Bs.ψ hstd g _ (GlobalTheory.T.archimedean_preimage_realPlace_line D θ hθ ε S X e cS hcS τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z))
  have d1 := GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hφ hvac f hf τ z g₁ h₁
  have d2 := GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hφ hvac f hf τ _ g₁' h₁'
  have h0 := GlobalTheory.T.gaussianVacuum_heisenbergDerivative_complexStructure_cancel D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac τ z g₁ g₁' h₁ h₁'
  have hsum := GlobalTheory.SquareAgree.isDatum_add M ψ (hψ ▸ hstd) cS _ _ _ _ d1 (isDatum_smul M ψ cS _ _ Complex.I d2)
  have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ + Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁' φ = 0 := by
    funext x
    have := congrArg (fun h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d) => h (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (x i))) h0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.zero_apply, smul_eq_mul] at this
    linear_combination (∏ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), φ v fun i ↦ (GlobalTheory.AdelicU.evFin D.host.F v) (x i)) * this
  rw [hpure] at hsum
  have := eq_zero_of_isDatum_zero M ψ cS _ hsum
  simpa [annih] using this

theorem isFinF_of_isGauss : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), M.IsGauss Bs.ψ Bs.emb g →
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∃ f : WO S X → ℂ, IsFinF ψ θ ε A B f ∧ IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac
  have hsch : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA g φ hφ ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)
  obtain ⟨ξ, JB, co, hξ, hrat, hiff⟩ := GlobalTheory.T.exists_rational_darboux_orientedPair_transport D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS
  have hstd : IsStdChar D ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D ψ (hψ ▸ hBs.std)
  have hD : IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) :=
    (hiff _ _).2 ⟨hsch, rfl⟩
  refine ⟨GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ), ⟨?_, fockVac_of_isGauss D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hemb M hM cS hcS g φ hg hφ hvac _ hD⟩, hD⟩
  exact GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr D ψ hstd (sgn ε S) X _ JB ξ rfl hξ _ co hrat _ hsch

end GlobalTheory.GaussThetaFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusMixedCoordinateSumLeSobolevSeminorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TorusMixedSum

set_option maxHeartbeats 1000000 in
theorem sum_mixS_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ (c : ℝ), 0 < c →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ α : Mx D r r, α.map (finPart D) = 1 →
        (∀ τ, compAt θ τ α = diagonal (fun i => (t i : ℂ))) →
        ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 k Ψ).toReal) := by
  intro D ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' c hc K₀ hK₀ hK₀c μ 𝓕 hμ
  obtain ⟨N, A₄, C₄, hC₄, h4⟩ := GlobalTheory.T.siegelCone_integral_matrix_lattice_count θ hθ X.rank r c hc
  obtain ⟨k₂, C₂, hC₂, h2⟩ := GlobalTheory.T.mixed_theta_series_rapid_decay ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' N
  obtain ⟨k₁, B, C₁, hC₁, h1⟩ := GlobalTheory.T.thetaFunction_heisenbergWord_sup_le_level_pow ψ hψ θ hθ V X K₀ hK₀ hK₀c μ 𝓕 hμ
  obtain ⟨M, hM, h3⟩ := GlobalTheory.T.mixedCoordinate_support_integral_at_level ψ hψ V X S₀ r d μ' 𝓕' hμ' K₀ hK₀ hK₀c
  set Wc : ℝ := ∑ k ∈ Finset.range (k₂ + 1),
    (Fintype.card (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool) : ℝ) ^ k with hWc
  have hWc0 : 0 ≤ Wc := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨k₁ + k₂, B + A₄, C₂ * Wc * C₁ * C₄ * (M : ℝ) ^ A₄, by positivity, ?_⟩
  intro n hn Ψ hΨ hlev t ht α hα hαc
  set sob := GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k₁ + k₂) Ψ with hsob
  have hsob_ne : sob ≠ ⊤ := GlobalTheory.Size.sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΨ _

  have hw : GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k₂ Ψ ≤
      ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob := by
    unfold GlobalTheory.Size.wordSum
    have hk : ∀ k ∈ Finset.range (k₂ + 1), ∀ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ) ≤
          ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob := by
      intro k hk a
      refine (h1 n hn Ψ hΨ hlev (List.ofFn a)).trans ?_
      rw [List.length_ofFn]
      gcongr
      exact GlobalTheory.Size.wordSum_mono (by have := Finset.mem_range.1 hk; omega) Ψ
    calc ∑ k ∈ Finset.range (k₂ + 1), ∑ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
          GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ)
        ≤ ∑ k ∈ Finset.range (k₂ + 1), ∑ _a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
          ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob :=
          Finset.sum_le_sum fun k hk' => Finset.sum_le_sum fun a _ => hk k hk' a
      _ = ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.sum_mul, hWc, ENNReal.ofReal_mul hWc0, ← mul_assoc]
          congr 2
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
          push_cast; rfl
  set K := ENNReal.ofReal C₂ * (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob) with hK
  set L : ℕ := M * n with hL
  have hLpos : 0 < L := Nat.mul_pos hM hn

  have hpt : ∀ ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
      ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ * K := by
    intro ξ
    by_cases h0 : d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0 = 0
    · rw [h0, enorm_zero]; exact bot_le
    have hfin : (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α).map (finPart D) =
        (ξ.map (incA D) : Mx D X.rank r).map (finPart D) := by
      rw [Matrix.map_mul, hα, Matrix.mul_one]
    have hint := h3 n hn Ψ hΨ hlev ξ _ hfin h0
    rw [Set.indicator_of_mem (show ξ ∈ {ξ : Matrix (Fin X.rank) (Fin r) D.host.E |
      ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} from hint)]
    have hc' : ∀ τ, compAt θ τ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) =
        compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ)) := by
      intro τ
      rw [← hαc τ]
      exact Matrix.map_mul (f := ((θ τ).comp (infPart D)))
    have hb := h2 Ψ hΨ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α)
    simp only [hc'] at hb
    set P := ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
      ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N) with hP
    have hP0 : P ≠ 0 := by
      rw [hP, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos (by positivity) _
    have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
    have hb' : ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ * P ≤ K :=
      hb.trans (by rw [hK]; gcongr)
    rw [ENNReal.ofReal_inv_of_pos (pow_pos (by positivity) _), ← hP, ← ENNReal.div_eq_inv_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hP0) (Or.inl hPt)).2 hb'
  have e : sob = ENNReal.ofReal sob.toReal := (ENNReal.ofReal_toReal hsob_ne).symm
  calc ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ
      ≤ ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ * K :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ) * K :=
        ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (C₄ * (L : ℝ) ^ A₄) * K := by gcongr; exact h4 L hLpos t ht
    _ = ENNReal.ofReal (C₄ * (L : ℝ) ^ A₄) * (ENNReal.ofReal C₂ *
          (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * ENNReal.ofReal sob.toReal)) := by rw [hK, ← e]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₂, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hL]
      push_cast
      ring

end GlobalTheory.TorusMixedSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductFunctionEqOfLocalIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem prodRel_map {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (T : ∀ l, (X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, T l (g i l) (y l) = 0 := by
  have hkey : ∀ l, ∃ (s : Finset (X l)) (E : X l → X l → ℂ), (∀ x, E x ∈ (⊤ : Submodule ℂ (X l → ℂ))) ∧
      ∀ u ∈ S.image (fun i => g i l), u = ∑ x ∈ s, u x • E x := fun l =>
    GlobalTheory.finset_functions_recovered_from_values ⊤ _ (fun _ _ => Submodule.mem_top)
  choose s E _ hE using hkey
  have h1 : ∀ i ∈ S, ∏ l, T l (g i l) (y l) =
      ∑ ξ ∈ Fintype.piFinset s, (∏ l, g i l (ξ l)) * ∏ l, T l (E l (ξ l)) (y l) := by
    intro i hi
    have h2 : ∀ l, T l (g i l) (y l) = ∑ x ∈ s l, g i l x * T l (E l x) (y l) := by
      intro l
      conv_lhs => rw [hE l (g i l) (Finset.mem_image_of_mem _ hi)]
      simp [map_sum, Finset.sum_apply]
    simp only [h2]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun i hi => by rw [h1 i hi, Finset.mul_sum], Finset.sum_comm]
  refine Finset.sum_eq_zero fun ξ _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, h ξ, zero_mul]

theorem prodRel_allSome {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, f i l (y l) = 0 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  choose T hT using fun l => (hf i₀ hi₀ l).1
  rw [← prodRel_map S x g T h y]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [fun l => (hf i hi l).2 _ (hT l)]

theorem prodRel_allSome₂ {ι κ I : Type} [Fintype ι] [Fintype κ] {X Y : ι → Type} {X' Y' : κ → Type} (S : Finset I) (x : I → ℂ)
    (g : I → ∀ l, X l → ℂ) (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (g' : I → ∀ l, X' l → ℂ) (f' : I → ∀ l, Y' l → ℂ) (Q' : ∀ l, ((X' l → ℂ) →ₗ[ℂ] (Y' l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (hf' : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q' l) fun T => f' i l = T (g' i l))
    (h : ∀ (z : ∀ l, X l) (z' : ∀ l, X' l), ∑ i ∈ S, x i * ((∏ l, g i l (z l)) * ∏ l, g' i l (z' l)) = 0)
    (y : ∀ l, Y l) (y' : ∀ l, Y' l) :
    ∑ i ∈ S, x i * ((∏ l, f i l (y l)) * ∏ l, f' i l (y' l)) = 0 := by
  simp only [← mul_assoc]
  refine prodRel_allSome S (fun i => x i * ∏ l, f i l (y l)) g' f' Q' hf' (fun z' => ?_) y'
  have := prodRel_allSome S (fun i => x i * ∏ l, g' i l (z' l)) g f Q hf (fun z => by
    rw [← h z z']
    exact Finset.sum_congr rfl fun i _ => by ring) y
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem unfolded_eq_of_local_eq : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → ∀ (α : Type) (SA : Finset α) (xA : α → ℂ) (F : α → ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ) (Gd : α → ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) → ℂ) (fr : α → SchRow ch.G) (fd : α → SchDown ch.G t), (∀ a ∈ SA, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (F a i) (fr a i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (Gd a j) (fd a j)) → (∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ SA, xA a * (∏ i, F a i (x i)) * ∏ j, Gd a j (y j)) → ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R Fc _ ch _ _ hcon t e _ τ φ hτ α SA xA F Gd fr fd hA hloc M hM P h u y
  have key := hcon t M hM P h ((SchRow ch.G × SchDown ch.G t) ⊕ α) (τ.support.disjSum SA)
    (Sum.elim (fun d => τ d) fun a => -xA a) (Sum.elim (fun d => d.1) fr) (Sum.elim (fun d => d.2) fd) ?_ ?_ u y
  · rw [Finset.sum_disjSum] at key
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    exact add_neg_eq_zero.mp key
  · intro i hi j
    have hv := (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta
    rcases i with d | a
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hτ d (by simpa using hi)).2 j).2 hv
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hA a (by simpa using hi)).2 j).2 hv
  · intro y v
    refine prodRel_allSome₂ (τ.support.disjSum SA) (Sum.elim (fun d => τ d) fun a => -xA a)
      (Sum.elim (fun d => (φ d).1) F) (Sum.elim (fun d => d.1) fr)
      (fun i => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) (ch.G.latS (.chi i D.R.m : Pair T) : Set _)
          (ch.G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) 1 (ch.rm.vX i D.R.m))
      (Sum.elim (fun d => (φ d).2) Gd) (Sum.elim (fun d => d.2) fd)
      (fun j => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) (ch.G.latS (.mu t D.R.m j : Pair T) : Set _)
          (ch.G.latT (.mu t D.R.m j : Pair T) : Set _) fun _ => True) 1 (ch.rm.vT D.R.m j)) ?_ ?_ ?_ y v
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).1 l).2
      · exact ((hA a (by simpa using hi)).1 l).2
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).2 l).2
      · exact ((hA a (by simpa using hi)).2 l).2
    · intro z z'
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, ← mul_assoc]
      exact add_neg_eq_zero.mpr (hloc z z')

end GlobalTheory.LocAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumDatumTrivialCombinationLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VacComb

variable {D : D7}

theorem eq_zero_of_isHalf_zero {m n : ℕ} {x : Mx D m n} (hx : IsHalf (0 : AE D) x) : x = 0 := by
  ext i j
  have := hx i j
  simp at this
  simpa using this.symm

theorem isHalf_zero_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := by
  intro i j
  simp

theorem heisenbergSymplecticForm_zero_right_eq_zero (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem heisO_zero_eq_self (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, heisenbergSymplecticForm_zero_right_eq_zero]

theorem heisenbergTranslationCombination_single_one_eq_translate (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T (Finsupp.single w 1) f = heisO ψ S T w f := by
  unfold GlobalTheory.SeeSaw.comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem isFinComb_single_zero {S T : HSp D} : IsFinComb (Finsupp.single (0 : WO S T) (1 : ℂ)) := by
  intro u hu
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
  subst hu
  ext i j
  simp [Matrix.map]

theorem vacuum_isCombOf {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (p : Pair T) : IsCombOf W (FinDatum.vacuum G t p) (Finsupp.single 0 1) := by
  refine ⟨isFinComb_single_zero, ?_, ?_⟩
  · intro u hu
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu
    exact isHalf_zero_zero _
  · have he : (FinDatum.vacuum G t p).e = 0 := rfl
    intro f₀ _ _
    show AllSome _ _
    rw [heisenbergTranslationCombination_single_one_eq_translate, heisO_zero_eq_self]
    refine ⟨⟨(LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS p) (G.pT p) => ℂ) 0).smulRight f₀, ?_, ?_, ?_⟩, ?_⟩
    · intro Φ _ x hx
      obtain rfl := eq_zero_of_isHalf_zero hx
      simp [heisO_zero_eq_self]
    · intro Φ _ y hy
      have hy0 : IsHalf (0 : AE D) y := by rw [he, map_zero] at hy; exact hy
      obtain rfl := eq_zero_of_isHalf_zero hy0
      simp [heisO_zero_eq_self, heisenbergSymplecticForm_zero_right_eq_zero]
    · have h0 : halfInd (0 : AE D) (latO (G.pS p) (G.pT p) ↑(G.latS p) ↑(G.latT p) fun _ => True) 0 = 1 := by
        rw [halfInd, if_pos ⟨zero_mem _, isHalf_zero_zero _⟩]
      rw [he]
      simp [h0]
    · intro Tm hT
      have := hT.vac
      rw [one_smul] at this
      exact this.symm

end GlobalTheory.VacComb

open GlobalTheory.VacComb in

theorem GlobalTheory.VacComb.main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m), IsCombOf ch.W (FinDatum.vacuum ch.G t (.top t j)) (Finsupp.single 0 1) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  exact fun t j => vacuum_isCombOf _ t _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelFourthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_theta_level_fourth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → ∀ τ, IsTypeAt R.θ (G.Xp (j + 1)).V τ ((G.Xp (j + 1)).S τ) (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @GlobalTheory.ColTypeLift.colLift_isTypeAt | exact GlobalTheory.ColTypeLift.colLift_isTypeAt | (intros; apply GlobalTheory.ColTypeLift.colLift_isTypeAt <;> assumption)
end

