import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
import GroundTheory.GlobalFields.TateThesis.Bundle0006
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0002
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsSigmaNe
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma_cm (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2 w.embedding, h.2.2.2 w.embedding, star_star]

theorem exists_sigma_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc : w.IsComplex := h.2.1.isComplex w
  apply InfinitePlace.not_isReal_iff_isComplex.2 hc
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  change star (w.embedding x) = w.embedding x
  rw [← h.2.2.2 w.embedding, hne]

theorem deltaEx' (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -(((ε : ℤ) : E) * δ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨x, hx⟩ := exists_sigma_ne h
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sigma_sigma_cm h]
    simp
  · exact ⟨1, one_ne_zero, by simp⟩

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}

theorem mem_stabiliser_iff_frame_lower_block (hb : IsFrame2 σ Y b) (p : G2 σ Y) :
    p ∈ par2 σ Y ↔ (inFrame b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, t₀, ht₀⟩ := hb
  rw [GlobalTheory.ThK.Dbl.mem_parabolic_GL2_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ((kunf.isPar_frame ht₀ p t).1 ht).1
  · intro h
    set M := inFrame b p with hM
    have hMi : M * inFrame b p⁻¹ = 1 := by
      rw [hM, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    have hdet : IsUnit M.det := Matrix.isUnit_det_of_right_inverse hMi
    have hsplit : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
      rw [← h, Matrix.fromBlocks_toBlocks]
    have hdet2 : M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
      rw [hsplit, Matrix.det_fromBlocks_zero₂₁]
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.fromBlocks]
    have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left (hdet2 ▸ hdet)
    set A := M.toBlocks₁₁
    set T0 := incM F t₀.1
    set T0i := incM F (t₀⁻¹).1
    have e1 : T0 * T0i = 1 := by
      simp only [T0, T0i, incM, ← Matrix.map_mul]
      rw [show t₀.1 * (t₀⁻¹).1 = 1 from t₀.mul_inv]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : T0i * T0 = 1 := by
      simp only [T0, T0i, incM, ← Matrix.map_mul]
      rw [show (t₀⁻¹).1 * t₀.1 = 1 from t₀.inv_mul]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
    let t : GL (Fin n) (AE F E) := ⟨T0 * A * T0i, T0 * A⁻¹ * T0i, by
        calc T0 * A * T0i * (T0 * A⁻¹ * T0i) = T0 * (A * (T0i * T0) * A⁻¹) * T0i := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [e2, Matrix.mul_one, hAA, Matrix.mul_one, e1], by
        calc T0 * A⁻¹ * T0i * (T0 * A * T0i) = T0 * (A⁻¹ * (T0i * T0) * A) * T0i := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [e2, Matrix.mul_one, hAA', Matrix.mul_one, e1]⟩
    exact ⟨t, (kunf.isPar_frame ht₀ p t).2 ⟨h, rfl⟩⟩

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PiMapConst
section
set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adeleHaarB {m : MeasurableSpace (AF F)} (hB : @BorelSpace (AF F) _ m) :
    ∃ μ : @Measure (AF F) m, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ ∀ r : GroundTheory.Global.IdeleGroup F,
      μ.map (fun y => (r : AF F) * y) =
        (((((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal : NNReal) : ENNReal) • μ := by
  have h1 : m = GroundTheory.Global.measurableSpace_adeleRing F :=
    hB.measurable_eq.trans (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm
  subst h1
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GroundTheory.Global.instIsAddHaarMeasureAdeleRingRingOfIntegersAdeleMeasure F
  refine ⟨GroundTheory.Global.adeleMeasure F, inferInstance, inferInstance, fun r => ?_⟩
  exact GroundTheory.Global.map_smul_adeleMeasure r

theorem pi_map_const {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (f : X → X) (hf : Measurable f)
    (c : NNReal) (hμ : μ.map f = (c : ENNReal) • μ) (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Measure.pi fun _ : ι => μ).map (fun y i => f (y i)) = ((c : ENNReal) ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  haveI : SigmaFinite (μ.map f) := by
    rw [hμ]
    exact (inferInstance : SigmaFinite (c • μ))
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp only [hμ]
  haveI : SigmaFinite ((c : ENNReal) • μ) := (inferInstance : SigmaFinite (c • μ))
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem measN (n k : ℕ) (bs : Module.Basis (Fin n) F E) : ∃ κ : Measure ((Fin k → AE F E) × AF F), κ.IsAddHaarMeasure ∧
    ∀ r : GroundTheory.Global.IdeleGroup F, ∃ sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F),
      (∀ c : (Fin k → AE F E) × AF F, sc c = ((fun j : Fin k => (r : AF F) • c.1 j), ((r : AF F) * (r : AF F)) • c.2)) ∧
      κ.map sc = ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ ^ (n * k + 2)) • κ := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI hBA : BorelSpace (AF F) := ⟨rfl⟩
  haveI hBE : BorelSpace (AE F E) := ⟨rfl⟩
  obtain ⟨ν, hνH, hνS, hν⟩ := adeleHaarB (F := F) hBA
  let ψ := (Algebra.TensorProduct.basis (AF F) bs).equivFun
  have hψ : Continuous ψ :=
    IsModuleTopology.continuous_of_linearMap (ψ : AE F E →ₗ[AF F] (Fin n → AF F))
  have hψs : Continuous ψ.symm :=
    IsModuleTopology.continuous_of_linearMap (ψ.symm : (Fin n → AF F) →ₗ[AF F] AE F E)
  let e : ((Fin k → Fin n → AF F) × AF F) ≃+ ((Fin k → AE F E) × AF F) :=
    AddEquiv.prodCongr (AddEquiv.piCongrRight fun _ => ψ.symm.toAddEquiv) (AddEquiv.refl _)
  have he : Continuous e := by
    change Continuous fun p : (Fin k → Fin n → AF F) × AF F => ((fun j => ψ.symm (p.1 j)), p.2)
    exact (continuous_pi fun j => hψs.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
  have hes : Continuous e.symm := by
    change Continuous fun p : (Fin k → AE F E) × AF F => ((fun j => ψ (p.1 j)), p.2)
    exact (continuous_pi fun j => hψ.comp ((continuous_apply j).comp continuous_fst)).prodMk continuous_snd
  let μW : Measure (Fin k → Fin n → AF F) := Measure.pi fun _ => Measure.pi fun _ => ν
  refine ⟨(μW.prod ν).map e, e.isAddHaarMeasure_map _ he hes, fun r => ?_⟩
  set a : AF F := (r : AF F) with ha
  set b : AF F := ((r⁻¹ : GroundTheory.Global.IdeleGroup F) : AF F) with hb
  have hab : b * a = 1 := r.inv_mul
  have hba : a * b = 1 := r.mul_inv
  let S : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F := fun c => (fun j => a • c.1 j, (a * a) • c.2)
  let S' : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F := fun c => (fun j => b • c.1 j, (b * b) • c.2)
  have hS : Continuous S :=
    (continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul a).prodMk
      (continuous_snd.const_smul (a * a))
  have hS' : Continuous S' :=
    (continuous_pi fun j => ((continuous_apply j).comp continuous_fst).const_smul b).prodMk
      (continuous_snd.const_smul (b * b))
  let sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F) :=
    { toFun := S
      invFun := S'
      left_inv := fun c => by
        refine Prod.ext (funext fun j => ?_) ?_
        · show b • a • c.1 j = c.1 j
          rw [smul_smul, hab, one_smul]
        · show (b * b) • (a * a) • c.2 = c.2
          rw [smul_smul, show b * b * (a * a) = (b * a) * (b * a) by ring, hab, one_mul, one_smul]
      right_inv := fun c => by
        refine Prod.ext (funext fun j => ?_) ?_
        · show a • b • c.1 j = c.1 j
          rw [smul_smul, hba, one_smul]
        · show (a * a) • (b * b) • c.2 = c.2
          rw [smul_smul, show a * a * (b * b) = (a * b) * (a * b) by ring, hba, one_mul, one_smul]
      measurable_toFun := hS.measurable
      measurable_invFun := hS'.measurable }
  refine ⟨sc, fun c => rfl, ?_⟩
  let T1 : (Fin k → Fin n → AF F) → (Fin k → Fin n → AF F) := fun w j i => a * w j i
  let T2 : AF F → AF F := fun t => (a * a) * t
  have hT1 : Continuous T1 := continuous_pi fun j => continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).comp (continuous_apply j))
  have hT2 : Continuous T2 := continuous_const.mul continuous_id
  have hcomm : (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) ∘ e = e ∘ Prod.map T1 T2 := by
    funext p
    refine Prod.ext (funext fun j => ?_) rfl
    show a • ψ.symm (p.1 j) = ψ.symm (fun i => a * p.1 j i)
    rw [← map_smul]
    rfl
  set c : NNReal := (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹).toNNReal with hc
  have h1 : ν.map (fun y => a * y) = (c : ENNReal) • ν := hν r
  have hm1 : Measurable fun y : AF F => a * y := (continuous_const.mul continuous_id).measurable
  have hin : (Measure.pi fun _ : Fin n => ν).map (fun y i => a * y i) =
      ((c ^ n : NNReal) : ENNReal) • Measure.pi fun _ : Fin n => ν := by
    rw [pi_map_const ν (fun y => a * y) hm1 c h1 (Fin n), Fintype.card_fin, ENNReal.coe_pow]
  have hW : μW.map T1 = ((c : ENNReal) ^ n) ^ k • μW := by
    have hm2 : Measurable fun y : Fin n → AF F => fun i => a * y i :=
      (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
    have := pi_map_const (Measure.pi fun _ : Fin n => ν) (fun y i => a * y i) hm2 (c ^ n) hin (Fin k)
    rw [Fintype.card_fin, ENNReal.coe_pow] at this
    exact this
  have hA : ν.map T2 = (c : ENNReal) ^ 2 • ν := by
    have : T2 = (fun y => a * y) ∘ (fun y => a * y) := by
      funext t
      simp [T2, mul_assoc]
    rw [this, ← Measure.map_map hm1 hm1, h1, Measure.map_smul, h1, smul_smul, sq]
  rw [show ((μW.prod ν).map e).map sc = ((μW.prod ν).map e).map (sc : (Fin k → AE F E) × AF F → (Fin k → AE F E) × AF F) from rfl,
    Measure.map_map sc.measurable he.measurable, hcomm,
    ← Measure.map_map he.measurable (hT1.measurable.prodMap hT2.measurable),
    ← Measure.map_prod_map μW ν hT1.measurable hT2.measurable, hW, hA,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
  congr 1
  have hx : (0 : ℝ) ≤ ((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt (GroundTheory.Global.IdeleGroup.ideleModule F r).2)
  rw [ENNReal.ofReal_pow hx, ← pow_mul, ← pow_add]
  rfl

theorem measEx' (k : ℕ) (bs : Module.Basis (Fin 2) F E) : ∃ κ : Measure ((Fin k → AE F E) × AF F), κ.IsAddHaarMeasure ∧
    ∀ r : GroundTheory.Global.IdeleGroup F, ∃ sc : ((Fin k → AE F E) × AF F) ≃ᵐ ((Fin k → AE F E) × AF F),
      (∀ c : (Fin k → AE F E) × AF F, sc c = ((fun j : Fin k => (r : AF F) • c.1 j), ((r : AF F) * (r : AF F)) • c.2)) ∧
      κ.map sc = ENNReal.ofReal (((GroundTheory.Global.IdeleGroup.ideleModule F r : ℝ))⁻¹ ^ (2 * k + 2)) • κ :=
  measN 2 k bs

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ptEx' (d : SD σ) {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {X : Type} [TopologicalSpace X] (M M' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Continuous M) (hM' : Continuous M') (h : ∀ c, M c * M' c = 1)
    (hu : ∀ c, (M c)ᵀ * kunf.jw d.n (((ε : ℤ) : AE F E)) * (M c).map (cA σ) = kunf.jw d.n (((ε : ℤ) : AE F E))) :
    ∃ f : X → d.G, Continuous f ∧ ∀ c, inFrame d.b (f c) = M c := by
  have hone : incM F (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hPQ : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.mul_inv, hone]
  have hQP : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.inv_mul, hone]
  have hM'M : ∀ c, M' c * M c = 1 := fun c => by
    first
    | exact mul_eq_one_comm.mp (h c)
    | exact Matrix.mul_eq_one_comm.mp (h c)
    | exact Matrix.mul_eq_one_symm (h c)
  let N : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M c * incM F (d.b⁻¹).1
  let N' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M' c * incM F (d.b⁻¹).1
  have hNN' : ∀ c, N c * N' c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M c) (M' c), h c, Matrix.one_mul, hPQ]
  have hN'N : ∀ c, N' c * N c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M' c) (M c), hM'M c, Matrix.one_mul, hPQ]
  let u : X → GL (Fin d.n ⊕ Fin d.n) (AE F E) := fun c => ⟨N c, N' c, hNN' c, hN'N c⟩
  have mem : ∀ c, u c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    intro c
    obtain ⟨x, hx⟩ := PositivityTheory.SiegelWeilFormula.kunf.exists_of_frame hε (M c) (M' c) (h c) (hu c)
    have hx' : x.1.1 = N c := by
      show x.1.1 = incM F d.b.1 * M c * incM F (d.b⁻¹).1
      rw [← hx]
      show x.1.1 = incM F d.b.1 * (incM F (d.b⁻¹).1 * x.1.1 * incM F d.b.1) * incM F (d.b⁻¹).1
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    have e : u c = x.1 := Units.ext hx'.symm
    rw [e]
    exact x.2
  refine ⟨fun c => ⟨u c, mem c⟩, ?_, ?_⟩
  · apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (continuous_const.matrix_mul hM).matrix_mul continuous_const
    · exact (continuous_const.matrix_mul hM').matrix_mul continuous_const
  · intro c
    show incM F (d.b⁻¹).1 * N c * incM F d.b.1 = M c
    simp only [N, Matrix.mul_assoc]
    rw [hQP, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.RatVecCountable
section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incV_add {k : ℕ} (x y : Fin k → E) :
    GlobalTheory.ThK.incV F (x + y) = GlobalTheory.ThK.incV F x + GlobalTheory.ThK.incV F y := by
  funext i
  simp [GlobalTheory.ThK.incV, map_add]

theorem incV_zero {k : ℕ} : GlobalTheory.ThK.incV F (0 : Fin k → E) = 0 := by
  funext i
  simp [GlobalTheory.ThK.incV]

theorem incV_neg {k : ℕ} (x : Fin k → E) : GlobalTheory.ThK.incV F (-x) = -GlobalTheory.ThK.incV F x := by
  funext i
  simp [GlobalTheory.ThK.incV, map_neg]

theorem mem_ratVec {k : ℕ} {v : Fin k → AE F E} :
    v ∈ AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → _)) ↔ ∃ x, GlobalTheory.ThK.incV F x = v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, incV_zero⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, rfl⟩ := hx
      obtain ⟨Z, rfl⟩ := hy
      exact ⟨X + Z, incV_add X Z⟩
    | neg x _ hx =>
      obtain ⟨X, rfl⟩ := hx
      exact ⟨-X, incV_neg X⟩
  · rintro ⟨X, rfl⟩
    exact AddSubgroup.subset_closure ⟨X, rfl⟩

theorem ratVec_cocompact (k : ℕ) : ∃ K : Set (Fin k → AE F E), IsCompact K ∧
    ∀ v, ∃ γ ∈ AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → _)), γ + v ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi fun _ => C, isCompact_univ_pi fun _ => hC, fun v => ?_⟩
  choose X hX using fun i => hCx (v i)
  exact ⟨GlobalTheory.ThK.incV F X, mem_ratVec.2 ⟨X, rfl⟩, fun i _ => hX i⟩

theorem ratVec_discrete (k : ℕ) :
    DiscreteTopology (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E)))) := by
  obtain ⟨V, hV, hV0⟩ := kfour.exists_nhds_inclR (F := F) (E := E)
  have hW : (⋂ i, (fun v : Fin k → AE F E => v i) ⁻¹' V) ∈ 𝓝 (0 : Fin k → AE F E) := by
    refine Filter.iInter_mem.2 fun i => ?_
    exact (continuous_apply i).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨O, hOW, hO, h0⟩ := mem_nhds_iff.1 hW
  refine discreteTopology_of_isOpen_singleton_zero ?_
  convert hO.preimage continuous_subtype_val using 1
  ext ⟨x, hx⟩
  constructor
  · intro h
    have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
    subst h1
    exact h0
  · intro h
    obtain ⟨X, rfl⟩ := mem_ratVec.1 hx
    have h2 : X = 0 := by
      funext i
      exact hV0 _ (Set.mem_iInter.1 (hOW h) i)
    subst h2
    exact Set.mem_singleton_iff.2 (Subtype.ext incV_zero)

theorem ratVec_countable (k : ℕ) :
    Countable (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E)))) := by
  haveI := kfour.countable_E (E := E)
  have h : (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E))) :
      Set (Fin k → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E))).mono fun v hv => ?_
    obtain ⟨X, rfl⟩ := mem_ratVec.1 hv
    exact ⟨X, rfl⟩
  exact h.to_subtype

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
end

