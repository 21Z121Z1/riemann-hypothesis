import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0028
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0061
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0021
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0012
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0017

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.HaarMeasureTripleProductDecomposition
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

theorem UpperTheory.haarMeasure_triple_product_decomposition :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B C : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (C : Set G) → ∀ (j : A × B × C ≃ₜ* G) (μ : Measure G), μ.IsHaarMeasure → ∀ (μA : Measure A) (μB : Measure B) (μC : Measure C), μA.IsHaarMeasure → μB.IsHaarMeasure → μC.IsHaarMeasure → ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => f (j y)) (μA.prod (μB.prod μC)) ∧ ∃ c : ℝ, ∫ y, f (j y) ∂(μA.prod (μB.prod μC)) = c * ∫ g, f g ∂μ := by
  intro G _ _ _ _ _ _ _ _ A B C hA hB hC j μ hμ μA μB μC hμA hμB hμC f hf
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace C := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : (μB.prod μC).IsHaarMeasure := Measure.prod.instIsHaarMeasure μB μC
  haveI : SigmaFinite (μB.prod μC) := inferInstance
  haveI : MeasurableMul (B × C) := inferInstance
  haveI hPH : (μA.prod (μB.prod μC)).IsHaarMeasure :=
    Measure.prod.instIsHaarMeasure μA (μB.prod μC)
  set P : Measure (A × B × C) := μA.prod (μB.prod μC) with hP
  have hme : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  haveI hmap : (Measure.map j P).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P j
  have hk : Measure.map j P = Measure.haarScalarFactor (Measure.map j P) μ • μ :=
    Measure.isMulLeftInvariant_eq_smul _ _
  set k : ℝ≥0 := Measure.haarScalarFactor (Measure.map j P) μ with hkdef
  have hfm : Integrable f (Measure.map j P) := by
    rw [hk]; exact hf.smul_measure (by simp)
  refine ⟨?_, (k : ℝ), ?_⟩
  · exact (hme.integrable_map_iff).1 hfm
  · have h1 : ∫ g, f g ∂(Measure.map j P) = ∫ y, f (j y) ∂P := hme.integral_map f
    rw [← h1, hk, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.MatrixCoefficientBoundedByValueAtOne
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

namespace UpperTheory.MatrixCoefficientBound

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}

private theorem sq_shift (hD : IsFundamentalDomain Γ D μ) {f : G → ℝ} (hi : ∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) (g : G) :
    ∫ y in D, f (y * g) ∂μ = ∫ y in D, f y ∂μ :=
  _root_.UpperTheory.Reformulated.B.Qk59.sq_shift hD hi g

private theorem coef_le (hfin : μ D < ⊤) (hD : IsFundamentalDomain Γ D μ) {φ : G → ℂ} (hc : Continuous φ)
    (hi : ∀ γ ∈ Γ, ∀ y, φ (γ * y) = φ y) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) (g : G) :
    ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
  have hb : ∀ {ψ : G → ℂ}, Continuous ψ → (∀ y, ‖ψ y‖ ≤ C) → IntegrableOn (fun y => ‖ψ y‖ ^ 2) D μ := fun {ψ} h1 h2 =>
    Measure.integrableOn_of_bounded (M := C ^ 2) hfin.ne (h1.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (h2 y) 2)
  have hcg : Continuous fun y => φ (y * g) := hc.comp (continuous_mul_right g)
  have i1 := hb hcg fun y => hC _
  have i2 := hb hc hC
  have e := sq_shift (μ := μ) hD (f := fun y => ‖φ y‖ ^ 2) (fun γ hγ y => by simp only [hi γ hγ y]) g
  calc ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ (y * g) * star (φ y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in D, (‖φ (y * g)‖ ^ 2 + ‖φ y‖ ^ 2) / 2 ∂μ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) ((i1.add i2).div_const 2) (Eventually.of_forall fun y => ?_)
      simp only [norm_mul, norm_star]
      nlinarith [sq_nonneg (‖φ (y * g)‖ - ‖φ y‖)]
    _ = ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
      rw [integral_div, integral_add i1 i2, e]
      ring

end UpperTheory.MatrixCoefficientBound

theorem UpperTheory.matrix_coefficient_bounded_by_value_at_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}, Cpt σ X.J → M.μ.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) M.dom M.μ → ∀ {φ : UA σ X.J → ℂ}, IsFn φ → φ ≠ 0 → ∃ r : ℝ, 0 < r ∧ mc M φ 1 = r ∧ ∀ g, ‖mc M φ g‖ ≤ r := by
  intro F E _ _ _ _ _ σ n d X W M hK hμ hD φ hφ h0
  haveI := hK.cnt
  haveI := hK.right M.μ hμ
  obtain ⟨C, hC⟩ := hK.bdd hφ.1 hφ.2
  have e1 : mc M φ 1 = ((∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [mc, pet, mul_one]
    exact integral_congr_ae (Eventually.of_forall fun y => by simpa using Complex.mul_conj' (φ y))
  have hp : (∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ) ≠ 0 := fun h => h0 <| hK.eq_zero hμ hD hφ.1 hφ.2 (by
    have : pet M.μ M.dom φ φ = mc M φ 1 := by simp [mc]
    rw [this, e1, h]; simp)
  refine ⟨_, lt_of_le_of_ne (integral_nonneg fun y => by positivity) hp.symm, e1, fun g => ?_⟩
  exact UpperTheory.MatrixCoefficientBound.coef_le (hK.fin M.μ M.dom hμ hD) hD hφ.1 hφ.2 hC g
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.PolynomialDataFiniteKType
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

namespace UpperTheory.PolynomialDataFiniteKType₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

private theorem mat_inv_mul {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl

private theorem gInf_le {W : Spc F E d} {k : UA σ W.J} (hk : k ∈ gInf σ W) : k ∈ UAt σ W (evI F) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro u _
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  | mul g h _ _ hg hh =>
    intro u hu
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      have : mat (g * h) = mat g * mat h := rfl
      rw [this, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  | inv g _ hg =>
    intro u hu
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

private noncomputable def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end UpperTheory.PolynomialDataFiniteKType₂

open UpperTheory.PolynomialDataFiniteKType₂ in
theorem UpperTheory.polynomial_data_finite_K_type :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → ∀ Φ ∈ PolData B M, ∃ V : Submodule ℂ (Fn F n d), FiniteDimensional ℂ V ∧ V ≤ schA F (Fin n × Fin d) ∧ ∀ k ∈ gInf σ W, om (1, k) Φ ∈ V := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hK : ∀ k ∈ gInf σ W, k ∈ KInf σ W B.emb := fun k hk =>
    ⟨gInf_le hk, fun w => by
      rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hP.skew.sig w) (hP.skew.cartan w)]
      exact Commute.one_right _⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := h2
    have hD : GlobalTheory.ThK.Dbl.Prs.Dat B M hfin.toFinset f φ :=
      ⟨hf, h1, fun v hv => by simpa using hv⟩
    obtain ⟨g, hg, e⟩ := hD.pureA hP.good
    obtain ⟨U, hU, hU'⟩ := polFin hP f hf
    refine ⟨U.map (pureL φ), inferInstance, ?_, fun k hk => ?_⟩
    · rintro _ ⟨f', -, rfl⟩
      exact Submodule.subset_span ⟨f', g, hg, e f'⟩
    · obtain ⟨A, hA⟩ := GlobalTheory.ThK.Dbl.Prs.inf_op PositivityTheory.ThKF.A.archOp hP (hK k hk)
      have hact := (hA f hf).2
      exact ⟨A f, hU' k (hK k hk) _ hact, (hact _ (hD.rest hP.good)).symm⟩
  | zero => exact ⟨⊥, inferInstance, bot_le, fun k _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    obtain ⟨V', h1', h2', h3'⟩ := hy
    exact ⟨V ⊔ V', inferInstance, sup_le h2 h2', fun k hk => by
      rw [map_add]; exact Submodule.add_mem_sup (h3 k hk) (h3' k hk)⟩
  | smul c x _ hx =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    exact ⟨V, h1, h2, fun k hk => by rw [map_smul]; exact V.smul_mem c (h3 k hk)⟩
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.PolynomialDataStableInfinitePlace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

theorem UpperTheory.polynomial_data_stable_infinite_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ Φ ∈ PolData B M, om (g, h) Φ ∈ PolData B M := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hp g hg h hh Φ hΦ
  obtain ⟨T, hT, hP⟩ := PositivityTheory.ThKF.A.archOp F E σ B n d X W M χX χW om n 0 d 0 hp g hg h hh
  have kg : g ∈ KInf σ X B.emb := ⟨hg, fun w => by
    rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hp.herm.sig w) (hp.herm.cartan w)]; exact Commute.one_right _⟩
  have kh : h ∈ KInf σ W B.emb := ⟨hh, fun w => by
    rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hp.skew.sig w) (hp.skew.cartan w)]; exact Commute.one_right _⟩
  refine Submodule.span_induction (p := fun Φ _ => om (g, h) Φ ∈ PolData B M) ?_ (by simp)
    (fun x y _ _ a b => by rw [map_add]; exact add_mem a b)
    (fun c x _ a => by rw [map_smul]; exact Submodule.smul_mem _ c a) hΦ
  rintro _ ⟨f, f1, φ, f2, f3, rfl⟩
  obtain ⟨ξ, hξ, e⟩ := PositivityTheory.ThKG.pure_eq_pureA hp.good φ f2 f3
  rw [e f, hT.1 f ξ hξ, ← e (T f)]
  exact Submodule.subset_span ⟨T f, hP kg kh f f1, φ, f2, f3, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ThetaLiftContinuous
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

theorem UpperTheory.theta_lift_continuous :
    Tools → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → Continuous (lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ
  have cX : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have cW : Cpt σ W.J := T.cpt F E σ B d W d 0 hp.base (Or.inr hp.skew) (by simp)
  obtain ⟨t1, t2, -⟩ := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp).1 Φ hΦ
  obtain ⟨C, hC⟩ := cX.bdd₂ cW (f := fun x => theta om Φ x.1 x.2) t1 fun γ hγ δ hδ g g' => t2 γ hγ δ hδ g g'
  obtain ⟨C', hC'⟩ := cX.bdd hφ.1 hφ.2
  have hfin : M.μ M.dom < ⊤ := cX.fin _ _ hp.good.haar hp.good.dom
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  haveI := cW.sc
  haveI : FirstCountableTopology (UA σ W.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hs : Continuous fun g => star (φ g) := hφ.1.star
  unfold lift
  refine continuous_of_dominated (bound := fun _ => C * C') (fun h => ?_) (fun h => ?_) (integrable_const _) ?_
  · exact ((t1.comp (continuous_id.prodMk continuous_const)).mul hs).aestronglyMeasurable
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hC (g, h)) (hC' g) (norm_nonneg _) ((norm_nonneg _).trans (hC (g, h)))
  · refine Eventually.of_forall fun g => ?_
    exact (t1.comp (continuous_const.prodMk continuous_id)).mul continuous_const
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ThetaLiftEquivariant
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

theorem UpperTheory.theta_lift_equivariant :
    Tools → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → ∀ (a : UA σ X.J) (b h : UA σ W.J), lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = lift M om Φ φ (h * b) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ a b h
  have c : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have hTB := T.basic F E σ B n d X W M χX χW om n 0 d 0 hp
  let G : UA σ X.J → ℂ := fun x => theta om Φ x (h * b) * star (φ x)
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, G (γ * x) = G x := by
    intro γ hγ x
    have h1 := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (h * b)
    rw [one_mul] at h1
    simp only [G]
    rw [h1, hφ.2 γ hγ x]
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := c.right _ hp.good.haar
  haveI := c.cnt
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = ∫ x in M.dom, G (x * a) ∂M.μ := by
    unfold lift
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [G, theta]
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hmp := measurePreserving_mul_right M.μ a
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight a) G
    ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * a) ⁻¹' ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ a⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * a⁻¹ = γ.1 * (x * a⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd.setIntegral_eq hp.good.dom (f := G) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ThetaLiftLinear
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

namespace UpperTheory.TP.LiftLin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

private theorem integrand_int (T : Tools) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hP : IsPair B M χX χW om n 0 d 0) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) {φ : UA σ X.J → ℂ} (hφ : IsFn φ)
    (h : UA σ W.J) : IntegrableOn (fun g => theta om Φ g h * star (φ g)) M.dom M.μ := by
  have hc : Cpt σ X.J := T.cpt F E σ B n X n 0 hP.base (Or.inl hP.herm) (by simp)
  obtain ⟨h1, h2, -⟩ := (T.basic F E σ B n d X W M χX χW om n 0 d 0 hP).1 Φ hΦ
  have hcont : Continuous fun g => theta om Φ g h * star (φ g) :=
    (h1.comp (continuous_id.prodMk continuous_const)).mul (continuous_star.comp hφ.1)
  obtain ⟨C, hC⟩ := hc.bdd hcont fun γ hγ g => by
    have e := h2 γ hγ 1 (one_mem _) g h
    rw [one_mul] at e
    simp only [e, hφ.2 γ hγ g]
  exact Measure.integrableOn_of_bounded (M := C) (hc.fin M.μ M.dom hP.good.haar hP.good.dom).ne
    hcont.aestronglyMeasurable (Eventually.of_forall hC)

end UpperTheory.TP.LiftLin

open UpperTheory.TP.LiftLin in

theorem UpperTheory.theta_lift_linear :
    Tools → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → (∀ Φ ∈ schA F (Fin n × Fin d), ∀ Φ' ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om (Φ + Φ') φ = lift M om Φ φ + lift M om Φ' φ) ∧ (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om (c • Φ) φ = c • lift M om Φ φ) ∧ (∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ φ' : UA σ X.J → ℂ, IsFn φ → IsFn φ' → lift M om Φ (φ + φ') = lift M om Φ φ + lift M om Φ φ') ∧ (∀ (c : ℂ), ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → lift M om Φ (c • φ) = (starRingEnd ℂ) c • lift M om Φ φ) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres
  refine ⟨fun Φ hΦ Φ' hΦ' φ hφ => ?_, fun c Φ hΦ φ hφ => ?_, fun Φ hΦ φ φ' hφ hφ' => ?_, fun c Φ hΦ φ hφ => ?_⟩
  · funext h
    have e : ∀ g, theta om (Φ + Φ') g h * star (φ g) = theta om Φ g h * star (φ g) + theta om Φ' g h * star (φ g) := fun g => by
      have : theta om (Φ + Φ') g h = theta om Φ g h + theta om Φ' g h := by
        simp only [theta, map_add]
        exact thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΦ')
      rw [this, add_mul]
    simp only [lift, Pi.add_apply, e]
    exact integral_add (integrand_int T hP hΦ hφ h) (integrand_int T hP hΦ' hφ h)
  · funext h
    have e : ∀ g, theta om (c • Φ) g h * star (φ g) = c * (theta om Φ g h * star (φ g)) := fun g => by
      simp only [theta, map_smul, thetaSum_smul, mul_assoc]
    simp only [lift, Pi.smul_apply, smul_eq_mul, e, integral_const_mul]
  · funext h
    have e : ∀ g, theta om Φ g h * star ((φ + φ') g) = theta om Φ g h * star (φ g) + theta om Φ g h * star (φ' g) := fun g => by
      simp only [Pi.add_apply, star_add, mul_add]
    simp only [lift, Pi.add_apply] at e ⊢
    simp only [e]
    exact integral_add (integrand_int T hP hΦ hφ h) (integrand_int T hP hΦ hφ' h)
  · funext h
    have e : ∀ g, theta om Φ g h * star ((c • φ) g) = (starRingEnd ℂ) c * (theta om Φ g h * star (φ g)) := fun g => by
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
      ring
    simp only [lift, Pi.smul_apply, smul_eq_mul] at e ⊢
    simp only [e, integral_const_mul]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.UnitaryAdelicMemOfLocalGroupsNearOne
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

private theorem prj_of_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} {v : Pl F} {g : UA σ X.J} (hg : OffAt v g) : Euler.prj v g = 1 := by
  have h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ hg i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
  refine Subtype.ext (Units.ext ?_)
  show Euler.cut (PositivityTheory.ThKG.Loc.idem F v) (mat g) = 1
  rw [← sub_eq_zero, Euler.cut_sub, h]

theorem UpperTheory.unitaryAdelic_mem_of_localGroups_near_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (S : Finset (Pl F)) (H : Pl F → Subgroup (UA σ X.J)), (∀ v ∈ S, ∃ O : Set (UA σ X.J), IsOpen O ∧ 1 ∈ O ∧ ∀ g ∈ locGrp σ X v, g ∈ O → g ∈ H v) → (∀ b ∈ gAt σ X S, ∃ c : Pl F → UA σ X.J, (∀ v, c v ∈ locGrp σ X v) ∧ (∀ v ∈ S, OffAt v ((c v)⁻¹ * b)) ∧ ∀ H : Subgroup (UA σ X.J), (∀ v ∈ S, c v ∈ H) → b ∈ H) → IsOpen {b : gAt σ X S | b.1 ∈ ⨆ v ∈ S, H v} := by
  intro F E _ _ _ _ _ σ n X S H hO hb
  choose! O hOo h1 hOH using hO
  let K : Subgroup (gAt σ X S) := (⨆ v ∈ S, H v).subgroupOf (gAt σ X S)
  have hK : IsOpen (K : Set (gAt σ X S)) := by
    refine Subgroup.isOpen_of_mem_nhds K (g := 1) ?_
    let U : Set (gAt σ X S) := ⋂ v ∈ S, (fun b : gAt σ X S => Euler.prj v b.1) ⁻¹' O v
    have oU : IsOpen U := isOpen_biInter_finset fun v hv =>
      (hOo v hv).preimage (Euler.cont_prj.comp continuous_subtype_val)
    have mU : (1 : gAt σ X S) ∈ U := by
      refine Set.mem_iInter₂.2 fun v hv => ?_
      show Euler.prj v (1 : UA σ X.J) ∈ O v
      rw [map_one]
      exact h1 v hv
    refine Filter.mem_of_superset (oU.mem_nhds mU) fun b hbU => ?_
    obtain ⟨c, hc, hoff, hlast⟩ := hb b.1 b.2
    refine Subgroup.mem_subgroupOf.2 (hlast _ fun v hv => ?_)
    have e : Euler.prj v b.1 = c v := by
      have := prj_of_off (hoff v hv)
      rw [map_mul, map_inv, Euler.mem_loc.1 (hc v), inv_mul_eq_one] at this
      exact this.symm
    have hm : c v ∈ O v := e ▸ (Set.mem_iInter₂.1 hbU v hv)
    exact (le_iSup₂_of_le v hv le_rfl : H v ≤ ⨆ v ∈ S, H v) (hOH v hv _ (hc v) hm)
  exact hK
end

