import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliser
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0210
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0116
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallSStatement
section
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ), (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  first | exact @GlobalTheory.DeepPoint.deep_point | exact GlobalTheory.DeepPoint.deep_point | (intros; apply GlobalTheory.DeepPoint.deep_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalProductsTendstoFrameStabiliserStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_products_tendsto_frameStabiliser : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)), ∀ g ∈ GfC V, finE V g ∈ St β → ∃ γ : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, Filter.Tendsto γ Filter.atTop (nhds g) ∧ ∀ s, γ s ∈ Subgroup.closure {k : GA D V | k ∈ GfC V ∧ finE V k ∈ St β ∧ ∃ v ε, IsPlaceIdem D v ε ∧ SuppPl ε V k} ∧ ∀ v ∈ s, ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * Formalism.L2.Theta.mt V (γ s) i j = algebraMap (AF D.host.F) (AE D) ε * Formalism.L2.Theta.mt V g i j := by
  first | exact @GlobalTheory.LocalApprox.exists_local_approx | exact GlobalTheory.LocalApprox.exists_local_approx | (intros; apply GlobalTheory.LocalApprox.exists_local_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
section
noncomputable section

namespace GlobalTheory.Grow

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.AdelicU (EmbOver htInf htFin compInf compFin infProj opNorm)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (infHt infNorm)
open GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem infEmb_tmul_one_eq_extensionEmbedding {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {w : InfinitePlace F} {τ : E →+* ℂ} (hτ : τ.comp (algebraMap F E) = w.embedding)
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) (b : Ainf F) :
    θ (b ⊗ₜ[F] (1 : E)) = InfinitePlace.Completion.extensionEmbedding w (b w) := by
  have hc : Continuous fun b : Ainf F => InfinitePlace.Completion.extensionEmbedding w (b w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have key := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hθ.2 hc ?_
  · exact congrFun key b
  funext x
  simp only [Function.comp_apply]
  rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply', hθ.1,
    ← RingHom.comp_apply, hτ]
  simp

theorem htInf_eq_infMat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F} (t : EmbOver E w)
    [StarRing E] {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb t.1 θ) (g : HA (AF F) σ J) :
    htInf F w (bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J g)) =
      max 1 (max (opNorm (infMat σ J θ g)) (opNorm (infMat σ J θ g⁻¹))) := by
  have hre := infEmb_tmul_one_eq_extensionEmbedding t.2 hθ
  have hz : ∀ z : AF F ⊗[F] E, GlobalTheory.AdelicU.infEmb t (compInf F E w z) =
      θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have e : (fstA F a) ⊗ₜ[F] x = ((fstA F a) ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] x) := by simp
      simp only [GlobalTheory.AdelicU.compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, GlobalTheory.AdelicU.infEmb_tmul]
      rw [e, map_mul, hre, hθ.1]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  have hm : ∀ k : HA (AF F) σ J, ((bc (compInf F E w) (GlobalTheory.AdelicU.matHom _ σ J k) : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _).map (GlobalTheory.AdelicU.infEmb t) = infMat σ J θ k := by
    intro k
    ext i j
    exact hz _
  show max 1 (max (GlobalTheory.AdelicU.normInf F w _) (GlobalTheory.AdelicU.normInf F w _)) = _
  rw [GlobalTheory.AdelicU.normInf_eq_opNorm h t, GlobalTheory.AdelicU.normInf_eq_opNorm h t, ← map_inv (bc (compInf F E w)),
    ← map_inv (GlobalTheory.AdelicU.matHom _ σ J), hm, hm]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (V : HSp D)

theorem htInf_eq_infHt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D V) :
    htInf D.host.F (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (bc (compInf D.host.F D.host.E _) (Formalism.L2.Theta.matHom V g)) = infHt θ V τ g := by
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have ht : (tauE D τ).comp (algebraMap D.host.F D.host.E) =
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))).embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp (hcm.1.isReal _))).symm
  exact (htInf_eq_infMat hcm V.gram ⟨_, ht⟩ (hθ τ) g).trans rfl

private theorem htFin_eq_one_of_mem_GinfC {g : GA D V} (hg : g ∈ GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    htFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g)) = 1 := by
  have hk : Formalism.L2.Theta.finHom V g = 1 := hg
  have hz : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E, compFin D.host.F D.host.E v z =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
  have h1 : bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom V g) = 1 := by
    apply Units.ext
    ext i j
    have hij : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) =
        ((1 : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix _ _ _) i j := by
      rw [← hk]; rfl
    show compFin D.host.F D.host.E v (((Formalism.L2.Theta.matHom V g : GL _ _) : Matrix _ _ _) i j) = _
    rw [hz, hij, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1]
  refine (GlobalTheory.AdelicU.htOf_eq_one).2 ⟨?_, ?_⟩ <;> simpa using GlobalTheory.AdelicU.normFin_one_le D.host.F v

theorem height_eq_prod_infHt (hθ : IsInfFam θ) {g : GA D V} (hg : g ∈ GinfC V) :
    height V g = ∏ τ, (infHt θ V τ g : ℝ) := by
  have hinf : ∏ w, htInf D.host.F w (bc (compInf D.host.F D.host.E w) (Formalism.L2.Theta.matHom V g)) =
      ∏ τ, infHt θ V τ g :=
    (Fintype.prod_bijective _ (GlobalTheory.CMTypePlaces.places_bijective D) _ _
      fun τ => (htInf_eq_infHt V hθ τ g).symm).symm
  show ((GlobalTheory.AdelicU.heightGL D.host.F (Formalism.L2.Theta.matHom V g) : NNReal) : ℝ) = _
  rw [GlobalTheory.AdelicU.heightGL, hinf]
  simp only [htFin_eq_one_of_mem_GinfC V hg, finprod_one, mul_one, NNReal.coe_prod]

theorem normInf_le_height (hθ : IsInfFam θ) : ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g := by
  refine ⟨2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ), fun g => ?_⟩
  have hb : ∀ τ, (infHt θ V τ g : ℝ) ≤ height V g := fun τ => by
    have := htInf_le_height V g (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
    rwa [htInf_eq_infHt V hθ τ g] at this
  have he : ∀ τ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖ ≤
      2 * height V g := by
    intro τ i j
    have h1 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j
    have h2 := GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j
    have h3 : infNorm θ V τ g ≤ infHt θ V τ g := le_max_of_le_right (le_max_left _ _)
    have h4 : infNorm θ V τ g⁻¹ ≤ infHt θ V τ g := le_max_of_le_right (le_max_right _ _)
    have h3' : (infNorm θ V τ g : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h3).trans (hb τ)
    have h4' : (infNorm θ V τ g⁻¹ : ℝ) ≤ height V g := (NNReal.coe_le_coe.2 h4).trans (hb τ)
    have e3 : (infNorm θ V τ g : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g)‖ := rfl
    have e4 : (infNorm θ V τ g⁻¹ : ℝ) =
        ‖Matrix.toEuclideanCLM (n := Fin V.rank) (𝕜 := ℂ) (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹)‖ := rfl
    linarith
  calc normInf θ V g = ∑ τ, ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := rfl
    _ ≤ ∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, 2 * height V g := by
        gcongr with τ _ i _ j _
        exact he τ i j
    _ = 2 * (Fintype.card D.what₂.Tau * V.rank * V.rank : ℝ) * height V g := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem height_le_normInf_pow (hθ : IsInfFam θ) : ∃ d : ℕ, ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · refine ⟨0, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, pow_zero]
    simp [GlobalTheory.SmoothForms.HeightCoset.infHt_rank_zero θ V h0]
  · refine ⟨Fintype.card D.what₂.Tau, fun g hg => ?_⟩
    rw [height_eq_prod_infHt V hθ hg, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun τ _ => NNReal.coe_nonneg _)
      (fun τ _ => GlobalTheory.SmoothForms.HeightCoset.infHt_le_normInf θ V hpos τ g)

theorem normInf_height_comparison (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) :
    (∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * height V g) ∧
      ∃ (C : ℝ) (d : ℕ), ∀ g ∈ GinfC V, height V g ≤ C * (1 + normInf θ V g) ^ d := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  refine ⟨⟨C, hC⟩, 1, d, fun g hg => ?_⟩
  have h0 : 0 ≤ normInf θ V g := by
    unfold Formalism.L2.Theta.normInf
    positivity
  calc height V g ≤ normInf θ V g ^ d := hd g hg
    _ ≤ (1 + normInf θ V g) ^ d := pow_le_pow_left₀ h0 (by linarith) d
    _ = 1 * (1 + normInf θ V g) ^ d := (one_mul _).symm

private theorem exists_coset_bound_of_modGrowthExp (V : HSp D) {d : ℕ} (hd : ∀ g ∈ GinfC V, height V g ≤ normInf θ V g ^ d) {A : ℕ}
    {f : GA D V → ℂ} (hf : ModGrowthExp V A f) (x : GA D V) :
    ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ (d * A) := by
  obtain ⟨C, hC⟩ := hf
  have hC0 : 0 ≤ C := nonneg_of_growth hC
  refine ⟨C * height V x ^ A, fun g hg => ?_⟩
  have h1 : height V (x * g) ≤ height V x * normInf θ V g ^ d :=
    (height_mul_le V x g).trans (mul_le_mul_of_nonneg_left (hd g hg) (height_pos V x).le)
  calc ‖f (x * g)‖ ≤ C * height V (x * g) ^ A := hC _
    _ ≤ C * (height V x * normInf θ V g ^ d) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le h1 A) hC0
    _ = C * height V x ^ A * normInf θ V g ^ (d * A) := by rw [mul_pow, ← pow_mul]; ring

variable {V}

theorem exists_modGrowthExp_le_normInf_pow (hθ : IsInfFam θ) (A : ℕ) :
    ∃ N : ℕ, ∀ f : GA D V → ℂ, ModGrowthExp V A f →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖f (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨d, hd⟩ := height_le_normInf_pow V hθ
  exact ⟨d * A, fun f hf x => exists_coset_bound_of_modGrowthExp V hd hf x⟩

theorem UnifModGrowth.growth (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) :
    ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC V,
        ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ V g ^ N := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨N, hN⟩ := exists_modGrowthExp_le_normInf_pow (V := V) hθ A
  exact ⟨N, fun l hl x => hN _ (hA l hl) x⟩

theorem UnifModGrowth.isAutFunSm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : UnifModGrowth V θ φ) (ha : IsAutFun V φ)
    (hs : ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod))
    (hz : ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W) :
    IsAutFunSm θ V φ :=
  { toIsAutFun := ha, smooth := hs, zfin := hz, growth := h.growth hθ }

end GlobalTheory.Grow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftGoodProjectorModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist

theorem exists_thG_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.tw_thF → R.ex_thF → R.ex_thG := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h0 hf hm h e i t
  obtain ⟨th, h1⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks R h0 hf hm fun i t => ((h i t).1 (e i t)).1
  exact ⟨th i t, h1 i t⟩

end GlobalTheory.Twist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniqueIsContr
section
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ContrObj

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

theorem norm_of_isIsoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_riesz [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (φ : FF) (y : H₂) :
    ∃ w : H₁, ∀ x, ⟪x, w⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := by
  let ℓ : H₁ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm.flip y).mkContinuous (‖φ‖ * ‖y‖) fun x => by
    have := norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    rw [norm_of_isIsoBilin hI] at this
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₁).surjective ℓ
  refine ⟨w, fun x => ?_⟩
  have h : ⟪w, x⟫_ℂ = ⟪φ, Tm x y⟫_ℂ := by
    have := congrArg (fun f : H₁ →L[ℂ] ℂ => f x) hw
    simpa [ℓ] using this
  rw [← inner_conj_symm, h, inner_conj_symm]

theorem existsUnique_isContr [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  choose w hw using exists_riesz hI
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) w ?_ ?_ ?_ ?_, fun φ y x => hw φ y x, ?_⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right, inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right, inner_smul_left, mul_comm]
  · intro It hIt
    ext φ y
    exact ext_inner_left ℂ fun x => (hIt φ y x).trans (hw φ y x).symm

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  exact ⟨existsUnique_isContr hI, fun It hC => contrProps_of hI hE hC⟩

section Tensor

open MvPolynomial

variable {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var)

omit [Fintype ι] in
theorem emb_injective (i : ι) : Function.Injective fun s : σ i => e ⟨i, s⟩ :=
  e.injective.comp sigma_mk_injective

def res (α : Var →₀ ℕ) (i : ι) : σ i →₀ ℕ :=
  Finsupp.comapDomain (fun s : σ i => e ⟨i, s⟩) α (emb_injective e i).injOn

theorem res_sum (a : ∀ i, σ i →₀ ℕ) :
    res e (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) = a := by
  classical
  funext j
  ext s
  change (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) (e ⟨j, s⟩) = a j s
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply (emb_injective e j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Sigma.fst (e.injective ht))
  · simp

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials Var ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1)

theorem tens_prod (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ∀ i, MvPolynomial (σ i) ℂ) :
    tens e I (∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  let pr : MultilinearMap ℂ (fun i : ι => MvPolynomial (σ i) ℂ) (MvPolynomial Var ℂ) :=
    (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun i => (rename (fun s : σ i => e ⟨i, s⟩) : MvPolynomial (σ i) ℂ →ₐ[ℂ] _).toLinearMap
  have hpr : ∀ P, pr P = ∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i) := fun P => by simp [pr]
  have key : (tens e I).compMultilinearMap pr
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun i => basisMonomials (σ i) ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, hpr, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply, rename_monomial]
    rw [← monomial_sum_one]
    have := (basisMonomials Var ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1))
      (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [hpr] using this

theorem tprod_ne_zero (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

end Tensor

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ I
  have h : IsTensorIt e I (tens e I) := fun P v => by
    rw [tens_prod, PiTensorProduct.map_tprod]
  refine ⟨tens e I, h, fun hI h0 => ?_⟩
  have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using hex
  have h1 := h P v
  rw [h0] at h1
  exact tprod_ne_zero _ hPv h1.symm

theorem contraction : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction := ⟨contrHilbert, contrTensor⟩

end GlobalTheory.ContrObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
section
open Classical MeasureTheory

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def colMat {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Matrix (Var ι d a) (Var ι d a) ℂ :=
  fun w v => if w.1 = v.1 ∧ w.2.1 = v.2.1 then g v.1 w.2.2 v.2.2 else 0

theorem colSub_eq_lsub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a) = GlobalTheory.JointHarm.FMul.lsub (colMat g) := by
  refine algHom_ext fun v => ?_
  rw [GlobalTheory.JointHarm.FMul.lsub_X, colSub, aeval_X]
  obtain ⟨τ, r, c⟩ := v
  simp only [colMat, Fintype.sum_prod_type, ite_and, apply_ite C, map_zero, ite_mul, zero_mul]
  simp

theorem colMat_conjTranspose {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colMat (d := d) g)ᴴ = colMat fun τ => (g τ)ᴴ := by
  ext w v
  simp only [colMat, conjTranspose_apply]
  by_cases h : v.1 = w.1 ∧ v.2.1 = w.2.1
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, h.1]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩, star_zero]

theorem colSub_comp {d a : ℕ} (h g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub h : Pol ι d a →ₐ[ℂ] Pol ι d a).comp (colSub g) = colSub fun τ => h τ * g τ := by
  refine algHom_ext fun v => ?_
  rw [AlgHom.comp_apply]
  unfold colSub
  rw [aeval_X, aeval_X, map_sum]
  simp only [map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem colSub_one {d a : ℕ} : (colSub (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) =
    AlgHom.id ℂ _ := by
  refine algHom_ext fun v => ?_
  rw [colSub, aeval_X, Finset.sum_eq_single v.2.2]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne hb]
    simp
  · simp

theorem fockS_colSub_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ)
    (P Q : GlobalTheory.MinorFrame.Pol ι d a),
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
      (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  intro ι _ a d u P Q
  rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, colSub_eq_lsub, GlobalTheory.JointHarm.FMul.fockL_lsub_adj,
    ← colSub_eq_lsub, colMat_conjTranspose, ← colSub_eq_lsub, ← AlgHom.comp_apply, colSub_comp]
  have hu : (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)ᴴ * (u τ : Matrix (Fin a) (Fin a) ℂ)) = fun _ => 1 := by
    funext τ
    exact Matrix.mem_unitaryGroup_iff'.1 (u τ).2
  rw [hu, colSub_one, AlgHom.id_apply]

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReductionStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_movedHom_integral_reduction : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  first | exact @GlobalTheory.FrameRed.frMapO_actO_red | exact GlobalTheory.FrameRed.frMapO_actO_red | (intros; apply GlobalTheory.FrameRed.frMapO_actO_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityType
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.HeckeUnitaryInf

theorem isUnitary_of_hasInf : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  intro L _ _ χ I _ φ n h
  have hinf : ∀ k : Lˣ, ‖((χ.1 (infDiag k) : ℂˣ) : ℂ)‖ = 1 := by
    intro k
    have e : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := h k
    rw [e, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h0), one_zpow]
  have hI : ∀ y : (InfiniteAdeleRing L)ˣ, ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖ = 1 := by
    have := (GlobalTheory.HeckeGal.denseRange_units_inf L).equalizer
      (g := fun y => ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖) (h := fun _ => (1 : ℝ))
      ((Units.continuous_val.comp (χ.2.1.comp GlobalTheory.HeckeGal.continuous_inlInf)).norm) continuous_const
      (funext fun k => by
        simp only [Function.comp_apply]
        rw [← GlobalTheory.HeckeGal.infDiag_eq]
        exact hinf k)
    exact fun y => congrFun this y
  have hF : ∀ x : Ideles L, IsFinIdele x → ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1 := by
    intro x hx
    obtain ⟨m, hm, u, k, u1, u2, e⟩ := GlobalTheory.UnUnitCmp.Val.exists_pow_eq x hx
    have e1 := congrArg (fun a => ‖((χ.1 a : ℂˣ) : ℂ)‖) e
    simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hinf k,
      GlobalTheory.HeckeFin.norm_eq_one χ u u1 u2, χ.2.2 k, Units.val_one, norm_one, mul_one] at e1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e1
  intro z
  have hz : z = GlobalTheory.HeckeGal.inlInf L (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) z) *
      finPartI L z := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [hz, map_mul, Units.val_mul, norm_mul, hI, hF _ (fun _ => rfl), one_mul]

end GlobalTheory.HeckeUnitaryInf
end
end

