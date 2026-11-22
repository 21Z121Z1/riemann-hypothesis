import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0082
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIffForallMaximalSpectrumResidueStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ x : B.A, IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  first | exact @GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum | exact GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum | (intros; apply GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralResidueComapInvolutionIffStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_residue_comap_involution_iff : ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A), IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔ IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff | exact GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff | (intros; apply GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportDescendedFunction
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.descFn_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  intro F E _ _ _ _ _ A r M Ax j lam α hαl hαc f hf

  have hstar : Continuous (star : E → E) := by
    have : Isometry (starAddEquiv : E ≃+ E) :=
      (AddMonoidHomClass.isometry_iff_norm (starAddEquiv : E ≃+ E)).2 (fun x => Unram.norm_star F x)
    exact this.continuous
  haveI : ContinuousStar E := ⟨hstar⟩
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjs : Continuous j.symm :=
    LinearMap.continuous_of_finiteDimensional ((j.symm : (Fin r → E) →ₗ[E] A.L).restrictScalars F)

  have hact : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (actU p.2 (Ax, j p.1, lam) : Hn r F E)) := by
    have hg : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (p.2 : Matrix (Fin r) (Fin r) E)) :=
      continuous_subtype_val.comp continuous_snd
    have c1 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) * Ax.1 * star (p.2 : Matrix (Fin r) (Fin r) E)) :=
      (hg.mul continuous_const).mul hg.star
    have c2 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) *ᵥ j p.1) :=
      Continuous.matrix_mulVec hg (hj.comp continuous_fst)
    exact Continuous.prodMk (Continuous.subtype_mk c1 _) (Continuous.prodMk c2 continuous_const)
  set Φ : A.L × Matrix.unitaryGroup (Fin r) E → ℂ := fun p => f (actU p.2 (Ax, j p.1, lam)) * (α p.2 : ℂ) with hΦ
  have hΦl : IsLocallyConstant Φ := by
    refine IsLocallyConstant.mul (hf.1.comp_continuous hact) ?_
    exact (hαl.comp_continuous continuous_snd).comp (fun x : ℝ => (x : ℂ))
  have hdesc : ∀ y, A.descFn M Ax j lam α f y = (letI := M.mU; ∫ g, Φ (y, g) ∂M.μU) := fun y => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y0
    have key : ∀ᶠ y in 𝓝 y0, ∀ g ∈ tsupport α, Φ (y, g) = Φ (y0, g) := by
      refine hαc.isCompact.eventually_forall_of_forall_eventually ?_
      intro g _
      have h1 := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦl (y0, g)
      have h2 : ∀ᶠ z : A.L × Matrix.unitaryGroup (Fin r) E in 𝓝 (y0, g), Φ (y0, z.2) = Φ (y0, g) := by
        have h3 : Tendsto (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) (𝓝 (y0, g)) (𝓝 (y0, g)) := by
          have : Continuous (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) :=
            continuous_const.prodMk continuous_snd
          simpa using this.tendsto (y0, g)
        exact h3.eventually h1
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    rw [hdesc, hdesc]
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hy g hg
    · have : α g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [hΦ, this]
  · let S : Set (Fin r → E) := Prod.fst '' (Prod.snd '' tsupport f)
    let Kset : Set A.L := (fun p : Matrix.unitaryGroup (Fin r) E × (Fin r → E) => j.symm (star (p.1 : Matrix (Fin r) (Fin r) E) *ᵥ p.2)) '' (tsupport α ×ˢ S)
    have hS : IsCompact S :=
      (hf.2.isCompact.image continuous_snd).image continuous_fst
    have hK : IsCompact Kset := by
      refine (hαc.isCompact.prod hS).image ?_
      refine hjs.comp ?_
      exact Continuous.matrix_mulVec ((continuous_subtype_val.comp continuous_fst).star) continuous_snd
    have hKc : IsClosed Kset := by
      have h1 : IsClosed (j '' Kset) := (hK.image hj).isClosed
      have h2 : Kset = j ⁻¹' (j '' Kset) := (Set.preimage_image_eq _ j.injective).symm
      rw [h2]
      exact h1.preimage hj
    refine HasCompactSupport.intro' hK hKc ?_
    intro y hy
    by_contra hne
    rw [hdesc] at hne
    have : ∃ g, Φ (y, g) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      have : (fun g => Φ (y, g)) = fun _ => 0 := funext hall
      rw [this]
      simp
    obtain ⟨g, hg⟩ := this
    have hfg : f (actU g (Ax, j y, lam)) ≠ 0 := left_ne_zero_of_mul hg
    have hαg : (α g : ℂ) ≠ 0 := right_ne_zero_of_mul hg
    have hαg' : α g ≠ 0 := by exact_mod_cast hαg
    apply hy
    refine ⟨(g, g.1 *ᵥ j y), ⟨subset_tsupport _ hαg', ?_⟩, ?_⟩
    · exact ⟨(actU g (Ax, j y, lam)).2, ⟨actU g (Ax, j y, lam), subset_tsupport _ hfg, rfl⟩, rfl⟩
    · simp only [Matrix.mulVec_mulVec]
      have hu : star (g.1 : Matrix (Fin r) (Fin r) E) * g.1 = 1 := Matrix.UnitaryGroup.star_mul_self g
      rw [hu, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportHyperbolicOperati
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem isTest_comp_homeomorph {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {Φ : X → ℂ} (hΦ : IsTest Φ) :
    IsTest (Φ ∘ h) :=
  ⟨hΦ.1.comp_continuous h.continuous, hΦ.2.comp_homeomorph h⟩

theorem isTest_ops : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (Hyp.rg A g Φ)) ∧ (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun p : A.K × A.K => Φ (p.1, -p.2))) ∧ (∀ (s : A.Kˣ) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (fun p : A.K × A.K => Φ ((s : A.K) * p.1, (s : A.K) * p.2))) ∧ (∀ (h Φ : A.K × A.K → ℂ), IsLocallyConstant h → IsTest Φ → IsTest (fun p => h p * Φ p)) ∧ ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → IsTest (c • Φ + Φ') := by
  intro F E _ _ _ _ _ A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g Φ hΦ
    set a := (g : Matrix (Fin 2) (Fin 2) A.K) 0 0
    set b := (g : Matrix (Fin 2) (Fin 2) A.K) 0 1
    set c := (g : Matrix (Fin 2) (Fin 2) A.K) 1 0
    set d := (g : Matrix (Fin 2) (Fin 2) A.K) 1 1
    have hdet : a * d - b * c = 1 := by
      have := g.2
      rw [Matrix.det_fin_two] at this
      simpa [a, b, c, d] using this
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => (p.1 * a + p.2 * c, p.1 * b + p.2 * d)
        invFun := fun p => (p.1 * d - p.2 * c, -(p.1 * b) + p.2 * a)
        left_inv := by
          intro p
          ext
          · simp only; linear_combination p.1 * hdet
          · simp only; linear_combination p.2 * hdet
        right_inv := by
          intro p
          ext
          · simp only; linear_combination p.1 * hdet
          · simp only; linear_combination p.2 * hdet
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro Φ hΦ
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => (p.1, -p.2)
        invFun := fun p => (p.1, -p.2)
        left_inv := by intro p; simp
        right_inv := by intro p; simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro s Φ hΦ
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => ((s : A.K) * p.1, (s : A.K) * p.2)
        invFun := fun p => (((s⁻¹ : A.Kˣ) : A.K) * p.1, ((s⁻¹ : A.Kˣ) : A.K) * p.2)
        left_inv := by intro p; ext <;> simp [← mul_assoc]
        right_inv := by intro p; ext <;> simp [← mul_assoc]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro h Φ hh hΦ
    exact ⟨hh.mul hΦ.1, hΦ.2.mul_left⟩
  · intro c Φ Φ' hΦ hΦ'
    refine ⟨?_, ?_⟩
    · exact (hΦ.1.comp (fun z : ℂ => c • z)).add hΦ'.1
    · exact (hΦ.2.smul_left).add hΦ'.2

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportIdempotentCoordin
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem isTest_coord : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  intro F E _ _ _ _ _ A e h1 h2
  let ι : A.K →ₗ[F] A.L := (Algebra.linearMap A.K A.L).restrictScalars F
  let f : (A.K × A.K) →ₗ[F] A.L :=
    LinearMap.mulRight F e ∘ₗ ι ∘ₗ LinearMap.fst F A.K A.K +
      LinearMap.mulRight F (1 - e) ∘ₗ ι ∘ₗ LinearMap.snd F A.K A.K
  let tr : A.L →ₗ[F] A.K := (Algebra.trace A.K A.L).restrictScalars F
  let g : A.L →ₗ[F] A.K × A.K :=
    LinearMap.prod (tr ∘ₗ LinearMap.mulRight F e) (tr ∘ₗ LinearMap.mulRight F (1 - e))
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  have hf : ∀ p, f p = cc A e p := fun p => rfl
  have hg : ∀ y, g y = ci A e y := fun y => rfl
  have cf : Continuous (cc A e) := by
    have := IsModuleTopology.continuous_of_linearMap f
    simpa [funext hf] using this
  have cg : Continuous (ci A e) := by
    have := IsModuleTopology.continuous_of_linearMap g
    simpa [funext hg] using this
  let H : (A.K × A.K) ≃ₜ A.L :=
    { toFun := cc A e, invFun := ci A e, left_inv := h1, right_inv := h2,
      continuous_toFun := cf, continuous_invFun := cg }
  refine ⟨fun φ hφ => ⟨hφ.1.comp_continuous cf, hφ.2.comp_homeomorph H⟩,
    fun Φ hΦ => ⟨hΦ.1.comp_continuous cg, hΦ.2.comp_homeomorph H.symm⟩⟩

end GlobalTheory.JR.Hyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportPartialFourierGLB
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem exists_nhds_zero_add_invariant_of_isTest {X : Type} [UniformSpace X] [AddCommGroup X] [IsUniformAddGroup X] {f : X → ℂ}
    (hf : IsTest f) : ∃ U ∈ 𝓝 (0 : X), ∀ Y : X, ∀ u ∈ U, f (Y + u) = f Y := by
  obtain ⟨hlc, hcs⟩ := hf

  have hK : IsCompact (tsupport f) := hcs
  haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
  have hfin0 : (Set.range fun x : tsupport f => f x).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  have hT : (Set.range f).Finite := by
    refine (hfin0.insert 0).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ tsupport f
    · exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
    · exact Set.mem_insert_iff.2 (Or.inl (image_eq_zero_of_notMem_tsupport hx))

  set D : Set ℂ := (Set.image2 (fun a b => a - b) (Set.range f) (Set.range f)) \ {0} with hD
  have hDfin : D.Finite := (hT.image2 _ hT).diff
  have hDo : Dᶜ ∈ 𝓝 (0 : ℂ) := hDfin.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hDo
  have huc := hcs.uniformContinuous_of_continuous hlc.continuous (Metric.dist_mem_uniformity hε)
  rw [uniformity_eq_comap_nhds_zero X, Filter.mem_map, Filter.mem_comap] at huc
  obtain ⟨V, hV, hVs⟩ := huc
  refine ⟨V, hV, fun Y u hu => ?_⟩
  have h1 : ((Y, Y + u) : X × X) ∈ (fun p : X × X => p.2 - p.1) ⁻¹' V := by
    simpa [add_sub_cancel_left] using hu
  have h1' := hVs h1
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at h1'
  have h2 : f (Y + u) - f Y ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]; exact h1'
  have h3 := hball h2
  by_contra hne
  exact h3 ⟨⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩, fun h => hne (sub_eq_zero.1 h)⟩

theorem fourG_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → IsTest (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf
  have hU : ∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y := by
    exact exists_nhds_zero_add_invariant_of_isTest (X := Gl r F) (f := f') (by exact hf)
  exact ⟨fourG_isLocallyConstant_of_invariant F E r M ψ hψ f' hf hU,
    fourG_hasCompactSupport F E r M ψ hψ f' hf hU⟩

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantEtaleTraceAddCharHermitianKerne
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem isLocallyConstant_of_isStdChar {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) : IsLocallyConstant (fun t : F => ψ t) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have hs : ‖y - x‖ ≤ 1 := by simpa [dist_eq_norm] using hy
  have : y = x + (y - x) := by abel
  rw [this, AddChar.map_add_eq_mul, hψ.1 _ hs, mul_one]

def kerLinF {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : Et F E) (x : A.K) (y' : A.L) : A.L →ₗ[F] F where
  toFun y := Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y * y'))
  map_add' a b := by simp [star_add, add_mul, mul_add, map_add]
  map_smul' c a := by
    have hc : star (algebraMap F A.L c) = algebraMap F A.L c := by
      rw [IsScalarTower.algebraMap_apply F A.K A.L]; exact A.star_K _
    have h1 : star (c • a) * y' = (algebraMap F A.K c) • (star a * y') := by
      rw [Algebra.smul_def, star_mul, hc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]; ring
    rw [h1, map_smul, smul_eq_mul, ← mul_assoc, mul_comm x, mul_assoc, ← Algebra.smul_def, map_smul]
    rfl

theorem isLocallyConstant_psiK_kerL (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  have hl := isLocallyConstant_of_isStdChar ψ hψ
  refine ⟨?_, fun x y' => ?_⟩
  · have hc : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hl.comp_continuous hc
  · have hc : Continuous (kerLinF A x y') := IsModuleTopology.continuous_of_linearMap _
    exact hl.comp_continuous hc

end GlobalTheory.JR.Hyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlockStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → IsLocallyConstant (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | exact GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | (intros; apply GlobalTheory.JR.fourG_isLocallyConstant_of_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenFiniteEtaleHermitianPairOKStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_finiteEtaleHermitianPair_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsOpen A.OK := by
  first | exact @GlobalTheory.JR.OKOpen.isOpen_OK | exact GlobalTheory.JR.OKOpen.isOpen_OK | (intros; apply GlobalTheory.JR.OKOpen.isOpen_OK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpoly
section
namespace GlobalTheory.UnitLemma

open Polynomial

theorem InvAlg.isReduced_of_separable_P : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  intro K B h
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B h
  have h2 : minpoly K.E (LinearMap.mulLeft K.E B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  have hms : (minpoly K.E B.g).Separable :=
    h.of_dvd (h2 ▸ LinearMap.minpoly_dvd_charpoly (LinearMap.mulLeft K.E B.g))
  have hsurj : ∀ a : B.A, ∃ q : K.E[X], aeval B.g q = a := by
    intro a
    have hle : Submodule.span K.E (Set.range e) ≤
        Subalgebra.toSubmodule (Algebra.adjoin K.E ({B.g} : Set B.A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact Subalgebra.pow_mem (Algebra.adjoin K.E ({B.g} : Set B.A))
        (Algebra.subset_adjoin (Set.mem_singleton B.g)) _
    have ha : a ∈ Algebra.adjoin K.E ({B.g} : Set B.A) := hle (e.span_eq ▸ Submodule.mem_top)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, hq⟩
  refine ⟨fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := hn
  obtain ⟨q, rfl⟩ := hsurj n
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    rw [pow_zero] at hk
    haveI := subsingleton_of_zero_eq_one hk.symm
    exact Subsingleton.elim _ _
  have hdk : minpoly K.E B.g ∣ q ^ k := minpoly.dvd _ _ (by rw [map_pow, hk])
  obtain ⟨r, hr⟩ := (hms.squarefree.dvd_pow_iff_dvd h0.ne').1 hdk
  rw [hr, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacStages

section Rel

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] {β : α → Type} [∀ i, Fintype (β i)] [∀ i, LinearOrder (β i)]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : ∀ i, β i → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def relUnipD (f : ∀ i, (Σ j, c i j) ≃ m i) : Subgroup (Levi k m) :=
  Subgroup.pi Set.univ fun i => unipRad k (f i)

def relEmbD (f : ∀ i, (Σ j, c i j) ≃ m i) : (∀ i, Levi k (c i)) →* Levi k m :=
  MonoidHom.pi fun i => (leviEmb k (f i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

theorem relEmbD_apply (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) (i : α) :
    relEmbD k f g i = leviEmb k (f i) (g i) := rfl

theorem relEmbD_mem_normalizer (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) :
    relEmbD k f g ∈ Subgroup.normalizer (relUnipD k f : Set (Levi k m)) :=
  Subgroup.mem_normalizer_iff.2 fun u => forall₂_congr fun i _ =>
    Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (f i) (g i)) (u i)

def relDeltaHalfD (c : ∀ i, β i → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] :
    (∀ i, Levi k (c i)) →* ℂˣ :=
  ∏ i, (deltaHalf k (c i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

theorem relDeltaHalfD_apply (g : ∀ i, Levi k (c i)) :
    relDeltaHalfD k c g = ∏ i, deltaHalf k (c i) (g i) := by
  simp [relDeltaHalfD, MonoidHom.finsetProd_apply]

variable {k}

def relJacD (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (∀ i, Levi k (c i)) (Jacquet ρ (relUnipD k f)) :=
  twist (jacquet ρ (relUnipD k f) (relEmbD k f) (relEmbD_mem_normalizer k f)) (relDeltaHalfD k c)⁻¹

theorem relJacD_mk (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (g : ∀ i, Levi k (c i)) (v : W) :
    relJacD f ρ g (Submodule.Quotient.mk v) =
      (((relDeltaHalfD k c g)⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (ρ (relEmbD k f g) v) := rfl

end Rel

section Flat

variable {s : ℕ} {t : Fin s → ℕ}

def refinePlace {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) :
    (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun p : Σ a, Fin (t a) => Fin (d' p.1 p.2)) finSigmaFinEquiv.symm).trans
    ((Equiv.sigmaAssoc fun a b => Fin (d' a b)).trans ((Equiv.sigmaCongrRight e').trans e))

theorem refinePlace_apply {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a))
    (i : Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) :
    refinePlace e e' ⟨c, i⟩ =
      e ⟨(finSigmaFinEquiv.symm c).1, e' _ ⟨(finSigmaFinEquiv.symm c).2, i⟩⟩ := rfl

def flatHom (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    (∀ a b, Γ a b) →* ∀ c : Fin (∑ a, t a), Γ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 where
  toFun g c := g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2
  map_one' := rfl
  map_mul' _ _ := rfl

theorem flatHom_apply (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] (g : ∀ a b, Γ a b)
    (c : Fin (∑ a, t a)) :
    flatHom Γ g c = g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 := rfl

theorem flatHom_surjective (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] :
    Function.Surjective (flatHom Γ) := by
  have h : ⇑(flatHom Γ) = (Equiv.piCongrLeft' (fun p : Σ a, Fin (t a) => Γ p.1 p.2) finSigmaFinEquiv) ∘
      (Equiv.piCurry fun a b => Γ a b).symm := rfl
  rw [h]
  exact (Equiv.surjective _).comp (Equiv.surjective _)

end Flat

section Pull

variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSubquotient_of_comp {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (ψ : G' →* G)
    (hψ : Function.Surjective ψ) (h : IsSubquotient (σ.comp ψ) (ρ.comp ψ)) : IsSubquotient σ ρ := by
  obtain ⟨S, f, hf⟩ := h
  refine ⟨⟨S.toSubmodule, fun g v hv => ?_⟩, ⟨f.toLinearMap, fun g => ?_⟩, hf⟩
  · obtain ⟨g', rfl⟩ := hψ g
    exact S.apply_mem_toSubmodule g' hv
  · obtain ⟨g', rfl⟩ := hψ g
    exact f.isIntertwining' g'

theorem isSubquotient_of_equiv {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (φ : σ.Equiv ρ) :
    IsSubquotient σ ρ :=
  .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective

end Pull

end GlobalTheory.JacStages
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTestUnitIndicatorHermitianBlockStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTest_unitIndicatorHermitianBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist F] [LocallyCompactSpace F] [IsUltrametricDist E] [LocallyCompactSpace E] (r : ℕ), (∀ y : E, ‖star y‖ = ‖y‖) → IsTest (unitU r F E) := by
  first | exact @GlobalTheory.JR.isTest_unitU | exact GlobalTheory.JR.isTest_unitU | (intros; apply GlobalTheory.JR.isTest_unitU <;> assumption)
end

