import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1959
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralLeftTranslatePrimitiveFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairMovesPhasedHeisenbergTranslateStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • om (g, h) (heisO ψ S T (finPt hS hT r z) f₀) =
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
  first | exact @GlobalTheory.MovedTr.moved_translate | exact GlobalTheory.MovedTr.moved_translate | (intros; apply GlobalTheory.MovedTr.moved_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquiv
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.RealConjFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem inv_mem_UAt {n : ℕ} {X : Spc F E n} {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) :
    g⁻¹ ∈ UAt σ X (evI F) := by
  intro u hu
  have h1 : u • (mat g - 1) = 0 := hg u hu
  have hm : mat g⁻¹ * mat g = 1 := by simp [mat]
  have : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by
    rw [Matrix.mul_sub, hm, Matrix.mul_one, neg_sub]
  rw [this, smul_neg, ← Matrix.mul_smul, h1, Matrix.mul_zero, neg_zero]

theorem acts_comp {κ : Type} [Fintype κ] {A B : Module.End ℂ ((κ → AF F) → ℂ)}
    (hA : ∀ Φ ∈ schA F κ, A Φ ∈ schA F κ) {f f₁ f₂ : SInf F κ}
    (h₁ : Acts (evI F) A (⇑f) (⇑f₁)) (h₂ : Acts (evI F) B (⇑f₁) (⇑f₂)) :
    Acts (evI F) (B * A) (⇑f) (⇑f₂) := by
  intro r hr
  have e₁ := h₁ r hr
  have hr₁ : Rest (evI F) (⇑f₁) r := ⟨hr.1, by rw [← e₁]; exact hA _ hr.2⟩
  rw [Module.End.mul_apply, e₁]
  exact h₂ r hr₁

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∃ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) ∧
      ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB _ _ _ hw g hg h hh
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hW.pres x Φ hΦ
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw (g, h) hg hh
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw (g⁻¹, h⁻¹) (inv_mem_UAt hg) (inv_mem_UAt hh)
  have hid : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (T₁ f) = f := by
    intro f
    have hc := acts_comp (hpres _) (hT₁ f) (hT₂ (T₁ f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₂ (T₁ f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, T₁ (T₂ f) = f := by
    intro f
    have hc := acts_comp (hpres _) (hT₂ f) (hT₁ (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₁ (T₂ f)) f).2.2.2.1 _ hc (hid f))
  refine ⟨LinearEquiv.ofLinear T₁ T₂ (LinearMap.ext e12) (LinearMap.ext e21), fun f => hT₁ f, fun f => ?_⟩
  exact hT₂ f

end GlobalTheory.RealConjFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylBij

open GlobalTheory.WeylFourier GlobalTheory.RatWeilOp

theorem schA_le_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    Φ ∈ Submodule.span ℂ {Ψ : (κ → AF F) → ℂ | ∃ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ),
      GlobalTheory.RatWeilOp.IsFam φ ∧ Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} := GlobalTheory.T.adelicSchwartzSpace_mem_span_pureTensors

theorem fourier_twice_loc : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (χ : AddChar (Fv F v) ℂ), Continuous χ → (∀ t, ‖χ t‖ = 1) →
    χ ≠ 1 → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure], ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → Fv F v), ∀ a : κ → Fv F v,
      ∫ y, (∫ x, φ x * χ (x ⬝ᵥ y) ∂μ) * χ (y ⬝ᵥ a) ∂μ = d * φ (-a) := GlobalTheory.T.local_fourier_inversion_up_to_constant

theorem fourier_twice_arch : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ d : ℂ, d ≠ 0 ∧ ∀ (f : SInf F κ) (a : κ → mixedEmbedding.mixedSpace F),
      ∫ y, (∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ a) : ℝ)) ∂μ =
      d * f (-a) := GlobalTheory.T.archimedean_fourier_inversion_constant

theorem spAct_weyl {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R] [Algebra F R]
    (w : (κ → R) × (κ → R)) :
    GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) w = (w.2, -w.1) := by
  have h1 : ((-1 : Matrix κ κ F).map (algebraMap F R)) = -1 := by
    rw [Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)]
  simp [GlobalTheory.SympChange.spAct, GlobalTheory.SympChange.weylM, Matrix.fromBlocks_map, h1, Matrix.fromBlocks_mulVec,
    Matrix.neg_mulVec]
  rfl

end GlobalTheory.WeylBij

namespace GlobalTheory.WeylBij

open GlobalTheory.WeylFourier GlobalTheory.RatWeilOp

open scoped Classical in

theorem weyl_hasOpB : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChangeBij.HasOpB ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  intro F _ _ ψ hψ hunr _ κ _ _
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI mV : ∀ v : Pl F, MeasurableSpace (κ → Fv F v) := fun _ => borel _
  haveI bV : ∀ v : Pl F, BorelSpace (κ → Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (κ → AF F), μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μi, hμi⟩ : ∃ μ : Measure (κ → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl F, Measure (κ → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧
      ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by
    let K : ∀ v : Pl F, TopologicalSpace.PositiveCompacts (κ → Fv F v) := fun v =>
      ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
        isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by
          show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))).Nonempty
          rw [(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]
          exact ⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩
    refine ⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (κ → Fv F v)) := by
      ext x; simp [K]
    rw [e]
    exact Measure.addHaarMeasure_self
  haveI := hμv
  obtain ⟨c₀, hc₀, hpure⟩ := GlobalTheory.T.integral_adelic_pureTensor_eq_product_local F κ μ μi μv hμv1
  obtain ⟨ei', hei'bij, hei'⟩ := GlobalTheory.T.exists_archimedeanSchwartz_traceFourier_bijective F κ μi
  have hψc : ∀ v, Continuous (GlobalTheory.LatVac.psiAt ψ v) := fun v => GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v
  have hsub : ∀ v, ∀ φ ∈ SB (κ → Fv F v), φ ∈ intSub (GlobalTheory.LatVac.psiAt ψ v) (μv v) := fun v φ hφ y =>
    (hφ.1.continuous.mul ((hψc v).comp (continuous_id.dotProduct continuous_const))).integrable_of_hasCompactSupport
      hφ.2.mul_right
  let ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v => ftE (GlobalTheory.LatVac.psiAt ψ v) (μv v)
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = ft (GlobalTheory.LatVac.psiAt ψ v) (μv v) φ :=
    fun v φ hφ => ftE_eq _ _ (hsub v φ hφ)
  have hbij : ∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := fun v =>
    (GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace F v (GlobalTheory.LatVac.psiAt ψ v) (hψc v) (fun t => GlobalTheory.StdCharFromIsStd.norm_psi hψ _)
      (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) κ (μv v)).congr fun φ hφ => (hev v φ hφ).symm
  have hind : ∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v := by
    filter_upwards [hunr] with v hv
    rw [hev v (ind κ v) (GlobalTheory.StdVacuum.indicator_mem_SB v)]
    exact GlobalTheory.T.integralPointsIndicator_fourier_self_unramified F v (GlobalTheory.LatVac.psiAt ψ v) (fun x => hv x) κ (μv v) (hμv1 v)
  have hpureE : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ intSub ψ μ ∧
      ft ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := by
    intro f φ hφ
    have hφ' : ∀ y, IsFam (finT ψ φ y) := finT_isFam ψ hψ φ hφ
    have hfun : ∀ y, (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        archT f (fun i => evI F (y i)) (fun i => evI F (x i)) * ∏ᶠ v, finT ψ φ y v (fun i => evFin F v (x i)) :=
      fun y => funext fun x => pure_mul_psi ψ hψ f φ hφ x y
    refine ⟨fun y => ?_, funext fun y => ?_⟩
    · rw [hfun y]
      exact (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).1
    · show ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y) ∂μ = _
      rw [hfun y, (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).2]
      have h2 : ∀ v, ev v (φ v) (fun i => evFin F v (y i)) = ∫ x, finT ψ φ y v x ∂(μv v) := fun v => by
        rw [hev v _ (hφ.1 v)]; rfl
      have h3 : (c₀ • ei' f) (fun i => evI F (y i)) = c₀ * ∫ x, archT f (fun i => evI F (y i)) x ∂μi := by
        have h4 := hei' f (fun i => evI F (y i))
        simp only [archT]
        rw [← h4]
        rfl
      show _ = (c₀ • ei' f) (fun i => evI F (y i)) * ∏ᶠ v, ev v (φ v) (fun i => evFin F v (y i))
      rw [h3, finprod_congr h2]
  let T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ := ftE ψ μ
  have hfam : ∀ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, IsFam φ → IsFam fun v => ev v (φ v) := fun φ hφ =>
    ⟨fun v => (hbij v).mapsTo (hφ.1 v), by filter_upwards [hφ.2, hind] with v h1 h2; rw [h1, h2]⟩
  have hTpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
      T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := fun f φ hφ =>
    (ftE_eq ψ μ (hpureE f φ hφ).1).trans (hpureE f φ hφ).2
  have hgen := schA_le_span_pure F κ
  have hT_schA : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ := by
    intro Φ hΦ
    refine (Submodule.span_le.2 ?_ : _ ≤ (schA F κ).comap T) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    show T _ ∈ schA F κ
    rw [hTpure f φ hφ]
    exact pure_mem_schA _ _ (hfam φ hφ)
  have hint : ∀ Φ ∈ schA F κ, Φ ∈ intSub ψ μ := fun Φ hΦ => by
    refine (Submodule.span_le.2 ?_ : _ ≤ intSub ψ μ) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    exact (hpureE f φ hφ).1

  obtain ⟨dI, hdI, hdIf⟩ := fourier_twice_arch F κ μi
  have hloc := fun v => fourier_twice_loc F v (GlobalTheory.LatVac.psiAt ψ v) (hψc v) (fun t => GlobalTheory.StdCharFromIsStd.norm_psi hψ _)
    (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) κ (μv v)
  choose d hd hdf using hloc
  have hev2 : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v (ev v φ) = fun a => d v * φ (-a) := by
    intro v φ hφ
    funext a
    rw [hev v _ ((hbij v).mapsTo hφ), hev v φ hφ, ← hdf v φ hφ a]
    rfl
  have hev4 : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v (ev v (ev v (ev v φ))) = (d v ^ 2) • φ := by
    intro v φ hφ
    have h2 : ev v (ev v φ) ∈ SB (κ → Fv F v) := (hbij v).mapsTo ((hbij v).mapsTo hφ)
    rw [hev2 v _ h2, hev2 v φ hφ]
    funext a
    simp only [neg_neg, Pi.smul_apply, smul_eq_mul]
    ring
  have hd1 : ∀ᶠ v in cofinite, d v = 1 := by
    filter_upwards [hind] with v hv
    have h0 := congrFun (hev2 v (ind κ v) (GlobalTheory.StdVacuum.indicator_mem_SB v)) 0
    rw [hv, hv] at h0
    have h1 : ind κ v 0 = 1 := by
      simp only [ind]
      exact Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
        from fun i => (v.adicCompletionIntegers F).zero_mem) 1
    rw [neg_zero, h1, mul_one] at h0
    exact h0.symm
  have hei2 : ∀ (f : SInf F κ) (a : κ → mixedEmbedding.mixedSpace F), ei' (ei' f) a = dI * f (-a) := by
    intro f a
    rw [hei', ← hdIf f a]
    congr 1
    funext y
    rw [hei']
  have hei4 : ∀ f : SInf F κ, ei' (ei' (ei' (ei' f))) = (dI ^ 2) • f := by
    intro f
    ext a
    rw [hei2, hei2]
    simp only [neg_neg, SchwartzMap.smul_apply, smul_eq_mul]
    ring

  set C : ℂ := c₀ ^ 4 * dI ^ 2 * ∏ᶠ v, d v ^ 2 with hC
  have hdfin : (Function.mulSupport fun v => d v ^ 2).Finite := by
    refine (Filter.eventually_cofinite.1 hd1).subset fun v hv h => hv ?_
    show d v ^ 2 = 1
    rw [h, one_pow]
  have hCne : C ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc₀) (pow_ne_zero _ hdI)) ?_
    rw [finprod_eq_prod_of_mulSupport_subset _ hdfin.coe_toFinset.symm.subset]
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hd v)
  have hT4pure : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
      T (T (T (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)))) = C • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    intro f φ hφ
    have hφ2 := hfam _ hφ
    have hφ3 := hfam _ hφ2
    rw [hTpure f φ hφ, hTpure _ _ hφ2, hTpure _ _ hφ3, hTpure _ _ (hfam _ hφ3)]
    have e1 : c₀ • ei' (c₀ • ei' (c₀ • ei' (c₀ • ei' f))) = (c₀ ^ 4 * dI ^ 2) • f := by
      simp only [map_smul, smul_smul, hei4]
      ring_nf
    have e2 : (fun v => ev v (ev v (ev v (ev v (φ v))))) = fun v => (d v ^ 2) • φ v :=
      funext fun v => hev4 v (φ v) (hφ.1 v)
    rw [e1, e2]
    funext x
    have hφfin : (Function.mulSupport fun v : Pl F => φ v (fun i => evFin F v (x i))).Finite := by
      have hev : ∀ᶠ v in cofinite, φ v = ind κ v ∧ ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        hφ.2.and (Filter.eventually_all.2 fun i => evFin_mem (x i))
      refine (Filter.eventually_cofinite.1 hev).subset fun v hv hP => hv ?_
      show φ v _ = 1
      rw [hP.1]
      simp only [ind]
      exact Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈
        {z : κ → Fv F v | ∀ i, z i ∈ v.adicCompletionIntegers F} from hP.2) 1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
    rw [finprod_mul_distrib hdfin hφfin, hC]
    ring
  let T4 : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ := T ∘ₗ T ∘ₗ T ∘ₗ T
  have hT4 : ∀ Φ ∈ schA F κ, T (T (T (T Φ))) = C • Φ := by
    intro Φ hΦ
    have := (Submodule.span_le.2 ?_ : _ ≤ LinearMap.eqLocus T4 (C • LinearMap.id)) (hgen Φ hΦ)
    · exact this
    rintro _ ⟨f, φ, hφ, rfl⟩
    exact hT4pure f φ hφ
  let e' : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ := C⁻¹ • (T ∘ₗ T ∘ₗ T)
  have he' : ∀ Φ, e' Φ = C⁻¹ • T (T (T Φ)) := fun Φ => rfl
  refine ⟨T, c₀ • ei', ev, fun g => ?_, hT_schA, fun w Φ hΦ => ?_, fun v => ?_, fun v φ hφ h0 => ?_,
    fun v w φ hφ => ?_, hind, fun f φ h1 h2 => hTpure f φ ⟨h1, h2⟩, ?_⟩
  · obtain ⟨h, hh⟩ := hei'bij.2 (c₀⁻¹ • g)
    exact ⟨h, by rw [ContinuousLinearMap.smul_apply, hh, smul_smul, mul_inv_cancel₀ hc₀, one_smul]⟩
  · rw [spAct_weyl, ftE_eq ψ μ (schr_mem μ ψ w (hint Φ hΦ)), ft_schr, ftE_eq ψ μ (hint Φ hΦ)]
  · refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ h => (hbij v).mapsTo h) fun g hg => ?_
    obtain ⟨φ, h, e⟩ := (hbij v).surjOn hg
    exact ⟨φ, h, e⟩
  · exact (hbij v).injOn hφ (SB (κ → Fv F v)).zero_mem (by rw [h0, map_zero])
  · rw [spAct_weyl, hev v _ (GlobalTheory.SchrSBFin.schr_mem_SB v _ (hψc v) w φ hφ), hev v φ hφ, ft_schr]
  · refine GlobalTheory.SympChangeBij.bijOn_of_inv T e' hT_schA (fun Φ hΦ => ?_) (fun Φ hΦ => ?_) (fun Φ hΦ => ?_)
    · rw [he']
      exact Submodule.smul_mem _ _ (hT_schA _ (hT_schA _ (hT_schA _ hΦ)))
    · rw [he', hT4 Φ hΦ, smul_smul, inv_mul_cancel₀ hCne, one_smul]
    · rw [he', map_smul, hT4 Φ hΦ, smul_smul, inv_mul_cancel₀ hCne, one_smul]

end GlobalTheory.WeylBij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralLeftTranslatePrimitiveFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_leftTranslate_primitiveFrames : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (h : GL C k),
    IsUnif ϖ →
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z)) (X0 k σ * (invT h).val) *
      (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  first | exact @GlobalTheory.LeftTranslateZeta.bigF_phiA_left | exact GlobalTheory.LeftTranslateZeta.bigF_phiA_left | (intros; apply GlobalTheory.LeftTranslateZeta.bigF_phiA_left <;> assumption)
end

