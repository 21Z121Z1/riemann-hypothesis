import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ExpAct
open Matrix NumberField IsDedekindDomain
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem form_eq_sum {d : ℕ} (φ : (Fin d → ℂ) →ₗ[ℂ] ℂ) (y : Fin d → ℂ) :
    φ y = ∑ i, y i * φ (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ y]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

def coordCLM {d : ℕ} (x : Fin d → ℂ) (i : Fin d) : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M *ᵥ x) i
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun r M => by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }

theorem coordCLM_apply {d : ℕ} (x : Fin d → ℂ) (i : Fin d) (M : Matrix (Fin d) (Fin d) ℂ) :
    coordCLM x i M = (M *ᵥ x) i := rfl

theorem flow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℝ → (Fin d → ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀ s y, HasDerivAt (fun s => a s y) (a s (A *ᵥ y)) s) (x : Fin d → ℂ) :
    a 1 x = a 0 (NormedSpace.exp A *ᵥ x) := by
  set c : ℝ → Fin d → ℂ := fun s => NormedSpace.exp ((1 - s) • A) *ᵥ x with hc
  set h : ℝ → ℂ := fun s => ∑ i, c s i * a s (Pi.single i 1) with hh
  have hcd : ∀ s i, HasDerivAt (fun s => c s i) (-(A *ᵥ c s) i) s := by
    intro s i
    have e1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A)) (A * NormedSpace.exp ((1 - s) • A)) (1 - s) :=
      hasDerivAt_exp_smul_const' A (1 - s)
    have e2 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((1 - s) • A)) (-(A * NormedSpace.exp ((1 - s) • A))) s := by
      have := e1.scomp s ((hasDerivAt_id s).const_sub 1)
      simp only [neg_smul, one_smul, id] at this
      exact this
    have e3 := (coordCLM x i).hasFDerivAt.comp_hasDerivAt s e2
    have e4 : coordCLM x i (-(A * NormedSpace.exp ((1 - s) • A))) = -(A *ᵥ c s) i := by
      rw [coordCLM_apply, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
      rfl
    exact e3.congr_deriv e4
  have hd : ∀ s, HasDerivAt h 0 s := by
    intro s
    have hs : HasDerivAt h (∑ i, (-(A *ᵥ c s) i * a s (Pi.single i 1) + c s i * a s (A *ᵥ Pi.single i 1))) s :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hcd s i).mul (ha s (Pi.single i 1)))
    convert hs using 1
    · have e4 : ∑ i, c s i * a s (A *ᵥ Pi.single i 1) = a s (A *ᵥ c s) := by
        have e7 := form_eq_sum ((a s).comp (Matrix.toLin' A)) (c s)
        simp only [LinearMap.comp_apply, Matrix.toLin'_apply] at e7
        exact e7.symm
      have e5 : ∑ i, (A *ᵥ c s) i * a s (Pi.single i 1) = a s (A *ᵥ c s) := (form_eq_sum (a s) _).symm
      rw [Finset.sum_add_distrib, e4]
      simp only [neg_mul, Finset.sum_neg_distrib]
      rw [e5]; ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) 1 0
  have h1 : h 1 = a 1 x := by
    simp only [hh, hc, sub_self, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
    exact (form_eq_sum (a 1) x).symm
  have h0 : h 0 = a 0 (NormedSpace.exp A *ᵥ x) := by
    simp only [hh, hc, sub_zero, one_smul]
    exact (form_eq_sum (a 0) _).symm
  rw [← h1, ← h0, hconst]

theorem hasSum_exp_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (φ : (Fin d → ℂ) →ₗ[ℂ] ℂ) (x : Fin d → ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * φ ((A ^ n) *ᵥ x)) (φ (NormedSpace.exp A *ᵥ x)) := by
  let ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => φ (M *ᵥ x)
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (LinearMap.toContinuousLinearMap ψ)
  have e : ∀ n : ℕ, LinearMap.toContinuousLinearMap ψ (((n.factorial : ℂ))⁻¹ • A ^ n) =
      ((n.factorial : ℂ))⁻¹ * φ ((A ^ n) *ᵥ x) := fun n => by
    show ψ _ = _
    simp [ψ, Matrix.smul_mulVec]
  simp only [e] at h
  exact h

theorem eq_of_forms {V : Type} [AddCommGroup V] [Module ℂ V] {a b : V} (h : ∀ l : V →ₗ[ℂ] ℂ, l a = l b) : a = b := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ (a - b)]
  intro l
  simp [h l]

section Sub

variable {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N]
  (hN : ∀ y ∈ N, L y ∈ N)

def crd : N ≃ₗ[ℂ] (Fin (Module.finrank ℂ N) → ℂ) := (Module.finBasis ℂ N).equivFun

def emb : (Fin (Module.finrank ℂ N) → ℂ) →ₗ[ℂ] V := N.subtype ∘ₗ (crd N).symm.toLinearMap

def mat : Matrix (Fin (Module.finrank ℂ N)) (Fin (Module.finrank ℂ N)) ℂ :=
  LinearMap.toMatrix' ((crd N).toLinearMap ∘ₗ L.restrict hN ∘ₗ (crd N).symm.toLinearMap)

theorem emb_mulVec (y) : emb N (mat L N hN *ᵥ y) = L (emb N y) := by
  simp [mat, emb, LinearMap.toMatrix'_mulVec, LinearMap.restrict_apply]

theorem emb_pow_mulVec (n : ℕ) (y) : emb N ((mat L N hN ^ n) *ᵥ y) = (L ^ n) (emb N y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, emb_mulVec, pow_succ, Module.End.mul_apply]

theorem emb_crd (v : V) (hv : v ∈ N) : emb N (crd N ⟨v, hv⟩) = v := by
  simp [emb]

theorem hasSum_emb (v : V) (hv : v ∈ N) (l : V →ₗ[ℂ] ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v))
      (l (emb N (NormedSpace.exp (mat L N hN) *ᵥ crd N ⟨v, hv⟩))) := by
  have h := hasSum_exp_mulVec (mat L N hN) (l ∘ₗ emb N) (crd N ⟨v, hv⟩)
  simp only [LinearMap.comp_apply, emb_pow_mulVec, emb_crd] at h
  exact h

end Sub

theorem exists_isExp {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) (hL : GlobalTheory.RealLift.LocFin L) :
    ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U := by
  have hp : ∀ v : V, ∃ u : V, ∀ l : V →ₗ[ℂ] ℂ,
      HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) (l u) := by
    intro v
    obtain ⟨N, hfin, hv, hN⟩ := hL v
    exact ⟨_, hasSum_emb L N hN v hv⟩
  choose U0 hU0 using hp
  refine ⟨{ toFun := U0, map_add' := fun v w => ?_, map_smul' := fun c v => ?_ }, fun v l => hU0 v l⟩
  · refine eq_of_forms fun l => (hU0 (v + w) l).unique ?_
    have := (hU0 v l).add (hU0 w l)
    simp only [map_add, mul_add]
    exact this
  · refine eq_of_forms fun l => (hU0 (c • v) l).unique ?_
    have := (hU0 v l).mul_left c
    have e : ∀ n : ℕ, c * (((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) = ((n.factorial : ℂ))⁻¹ * l ((L ^ n) (c • v)) :=
      fun n => by simp only [map_smul, smul_eq_mul]; ring
    simp only [e] at this
    simp only [map_smul, smul_eq_mul] at this ⊢
    exact this

def evalAt {X : Type} (p : X) : (X → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj p

open scoped Classical in

theorem evalAt_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (p : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) : evalAt p ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (p i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (p i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [evalAt, GlobalTheory.WeilM.pureA, mul_comm]

open scoped Classical in

def pureL (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) where
  toFun f := GlobalTheory.WeilM.pureA F f g
  map_add' f f' := by funext x; simp [GlobalTheory.WeilM.pureA, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.WeilM.pureA, mul_assoc]

theorem expAct_fock : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V]
    (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V)
    (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L →
    (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) →
    (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) →
    ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := by
  intro F _ _ κ V _ _ _ Φ L om hL hadm hSD
  obtain ⟨U, hU⟩ := exists_isExp L hL
  refine ⟨U, hU, fun T g hg => ?_⟩
  obtain ⟨N, hfin, hT, hN⟩ := hL T
  have hUT : U T = emb N (NormedSpace.exp (mat L N hN) *ᵥ crd N ⟨T, hT⟩) :=
    eq_of_forms fun l => (hU T l).unique (hasSum_emb L N hN T hT l)
  funext p
  let a : ℝ → (Fin (Module.finrank ℂ N) → ℂ) →ₗ[ℂ] ℂ := fun s =>
    evalAt p ∘ₗ om (Multiplicative.ofAdd s) ∘ₗ pureL F g ∘ₗ Φ ∘ₗ emb N
  have ha : ∀ s y, HasDerivAt (fun s => a s y) (a s (mat L N hN *ᵥ y)) s := by
    intro s y
    have h0 := hSD (emb N y) g hg _ (hadm (Multiplicative.ofAdd s) _ (evalAt_mem_adm F κ p))
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h0)
    have e : (fun u => (evalAt p ∘ₗ om (Multiplicative.ofAdd s))
        (om (Multiplicative.ofAdd (u - s)) (GlobalTheory.WeilM.pureA F (Φ (emb N y)) g))) = fun u => a u y := by
      funext u
      show evalAt p (om (Multiplicative.ofAdd s) (om (Multiplicative.ofAdd (u - s)) _)) =
        evalAt p (om (Multiplicative.ofAdd u) _)
      rw [← Module.End.mul_apply, ← map_mul, ← ofAdd_add, add_sub_cancel]
      rfl
    have ev : (evalAt p ∘ₗ om (Multiplicative.ofAdd s)) (GlobalTheory.WeilM.pureA F (Φ (L (emb N y))) g) =
        a s (mat L N hN *ᵥ y) := by
      show _ = evalAt p (om (Multiplicative.ofAdd s) (GlobalTheory.WeilM.pureA F (Φ (emb N (mat L N hN *ᵥ y))) g))
      rw [emb_mulVec]
      rfl
    rw [← e]
    exact h1.congr_deriv ev
  have hf := flow (mat L N hN) a ha (crd N ⟨T, hT⟩)
  have l1 : a 1 (crd N ⟨T, hT⟩) = om (Multiplicative.ofAdd 1) (GlobalTheory.WeilM.pureA F (Φ T) g) p := by
    show evalAt p (om (Multiplicative.ofAdd 1) (GlobalTheory.WeilM.pureA F (Φ (emb N (crd N ⟨T, hT⟩))) g)) = _
    rw [emb_crd]
    rfl
  have l0 : a 0 (NormedSpace.exp (mat L N hN) *ᵥ crd N ⟨T, hT⟩) = GlobalTheory.WeilM.pureA F (Φ (U T)) g p := by
    show evalAt p (om (Multiplicative.ofAdd 0)
      (GlobalTheory.WeilM.pureA F (Φ (emb N (NormedSpace.exp (mat L N hN) *ᵥ crd N ⟨T, hT⟩))) g)) = _
    rw [← hUT, ofAdd_zero, map_one, Module.End.one_apply]
    rfl
  rw [← l1, ← l0]
  exact hf

end GlobalTheory.ExpAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open IsDedekindDomain

namespace GlobalTheory.ArchimedeanL2

theorem lintegral_eq_of_fibres {Z X Y : Type} [AddGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [AddGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] (e : Z ≃ₜ+ X × Y) (μ : Measure Z) [μ.IsAddHaarMeasure]
    (ν : Measure X) [ν.IsAddHaarMeasure] {G G' : X × Y → ENNReal} (hG : Measurable G) (hG' : Measurable G')
    (h : ∀ y, ∫⁻ x, G (x, y) ∂ν = ∫⁻ x, G' (x, y) ∂ν) : ∫⁻ z, G (e z) ∂μ = ∫⁻ z, G' (e z) ∂μ := by
  have he : Measurable e := e.continuous.measurable
  let ρ : Measure Y := Measure.addHaar
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  haveI : (ν.prod ρ).IsAddHaarMeasure := inferInstance
  rw [← lintegral_map hG he, ← lintegral_map hG' he, Measure.isAddLeftInvariant_eq_smul (μ.map e) (ν.prod ρ),
    lintegral_smul_measure, lintegral_smul_measure, lintegral_prod_symm _ hG.aemeasurable,
    lintegral_prod_symm _ hG'.aemeasurable]
  simp only [h]

theorem lintegral_sq_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] (g : SchwartzMap V ℂ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (g x) * g x ∂ν).re := by
  have hi : Integrable (fun x => ‖g x‖ ^ 2) ν := (g.memLp 2 ν).integrable_norm_pow (by norm_num)
  have h1 : ∀ x, star (g x) * g x = ((‖g x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  rw [integral_complex_ofReal, Complex.ofReal_re,
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable {F : Type} [Field F] [NumberField F]

private theorem cont_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem cont_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

variable (F) in

def splitEquiv (κ : Type) : (κ → AF F) ≃ₜ+ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl
  right_inv p := Prod.ext (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _) rfl
  map_add' x y := Prod.ext (funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (y i).1) rfl
  continuous_toFun := (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem lintegral_arch_eq : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : SInf F κ →ₗ[ℂ] SInf F κ) (Ω : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ (f : SInf F κ) (h : (κ → Af F) → ℂ), Ω (pureA F f h) = pureA F (L f) h) →
    (∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
      ∫ x, star (L f₁ x) * L f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖Ω φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ L Ω hΩ hL μ hμ φ hφ
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose f h hh hg using fun i => (g i).2
  let ν : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hB : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hsq : ∀ u : SInf F κ, ∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (u x) * u x ∂ν).re := fun u =>
    @lintegral_sq_eq (κ → mixedEmbedding.mixedSpace F) _ _ _ _ hB ν hν u
  haveI : OpensMeasurableSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    (Prod.borelSpace (α := κ → mixedEmbedding.mixedSpace F) (β := κ → Af F)).opensMeasurable
  have hm : ∀ u : Fin n → SInf F κ, Measurable fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) =>
      ‖∑ i, c i * (u i p.1 * h i p.2)‖ₑ ^ 2 := fun u =>
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      (((u i).continuous.comp continuous_fst).mul ((hh i).1.continuous.comp continuous_snd))).measurable.enorm.pow_const 2
  have hs : ∀ (u : Fin n → SInf F κ) (y : κ → Af F) (x : κ → mixedEmbedding.mixedSpace F),
      ∑ i, c i * (u i x * h i y) = (∑ i, (c i * h i y) • u i) x := fun u y x => by
    rw [sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_apply, smul_eq_mul]; ring
  have key := lintegral_eq_of_fibres (splitEquiv F κ) μ ν (hm fun i => L (f i)) (hm f) fun y => by
    simp only [hs]
    have e : ∑ i, (c i * h i y) • L (f i) = L (∑ i, (c i * h i y) • f i) := by simp only [map_sum, map_smul]
    rw [e, hsq, hsq, hL ν hν]
  have e1 : Ω (∑ i, c i • (g i : (κ → AF F) → ℂ)) = ∑ i, c i • pureA F (L (f i)) (h i) := by
    simp only [map_sum, map_smul, hg, hΩ]
  rw [e1]
  simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact key

end GlobalTheory.ArchimedeanL2
end
end

