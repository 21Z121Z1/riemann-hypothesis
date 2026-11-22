import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0013
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutTraceA
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0005

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSubstA
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.SubstA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

theorem exists_mtF_eq {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : GAF σ J} (h : γ ∈ GQF σ J) :
    ∃ m : Matrix (Fin n) (Fin n) E, mtF σ J γ = m.map (incAF F E) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem actOF_inv_actOF (g : GAF σ JS) (h : GAF σ JT) (x : WOF F E nS nT) :
    actOF σ JS JT g⁻¹ h⁻¹ (actOF σ JS JT g h x) = x := by
  rw [← GlobalTheory.WeilPartsF.actOF_mul, inv_mul_cancel, inv_mul_cancel, GlobalTheory.FinLatF.actOF_one]

theorem continuous_actOF (g : GAF σ JS) (h : GAF σ JT) : Continuous (actOF (nS := nS) (nT := nT) σ JS JT g h) := by
  unfold actOF
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem exists_actOF_ratWF {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT)
    (x : Matrix (Fin nT) (Fin nS) E) : ∃ y, actOF σ JS JT γ γ' (ratWF (F := F) x) = ratWF y := by
  obtain ⟨m, hm⟩ := exists_mtF_eq ((GQF σ JS).inv_mem hγ)
  obtain ⟨m', hm'⟩ := exists_mtF_eq hγ'
  refine ⟨m' * x * m, ?_⟩
  unfold actOF ratWF
  rw [hm, hm', Matrix.map_mul, Matrix.map_mul]

theorem actOF_mem_ratLF {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT) {x : WOF F E nS nT}
    (hx : x ∈ ratLF F E nS nT) : actOF σ JS JT γ γ' x ∈ ratLF F E nS nT := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := exists_actOF_ratWF hγ hγ' y
  exact ⟨z, hz.symm⟩

theorem symplOHF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF
  rw [PositivityTheory.ThKW.LatA.symplOF_actOF hS]

theorem isThetaFunOF_comp (hS : IsHermND σ JS) {ψ : AddChar (AF F) ℂ} {f : WOF F E nS nT → ℂ}
    (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' : GAF σ JT} (hγ' : γ' ∈ GQF σ JT) :
    IsThetaFunOF σ JS JT ξ₀ ψ fun w => f (actOF σ JS JT γ γ' w) := by
  let A : WOF F E nS nT →+ WOF F E nS nT := AddMonoidHom.mk' (actOF σ JS JT γ γ') (GlobalTheory.FinLatF.actOF_add γ γ')
  have hA : Continuous (actOF (nS := nS) (nT := nT) σ JS JT γ γ') := continuous_actOF γ γ'
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨y, e⟩ := exists_actOF_ratWF hγ hγ' x
    show f (actOF σ JS JT γ γ' (ratWF x + w)) = _
    rw [GlobalTheory.FinLatF.actOF_add, ← symplOHF_actOF hS γ γ', e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu (GlobalTheory.FinLatF.actOF_mem_finSubF γ γ' h0)) (actOF σ JS JT γ γ' w)
    unfold heisOF at e ⊢
    rw [← e, ← symplOHF_actOF hS γ γ' w u]
    exact congrArg (fun x => _ * f x) (GlobalTheory.FinLatF.actOF_add γ γ' w u)
  · have h3 : ∀ t, (actOF σ JS JT γ γ' (L t)).map (finPartF F E) = 0 := fun t => by
      unfold actOF
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    have := hf.smooth k (A.comp L) (hA.comp h1) h3 (actOF σ JS JT γ γ' w)
    simp only [GlobalTheory.FinLatF.actOF_add]
    exact this

theorem setLIntegral_comp (e : WOF F E nS nT ≃+ WOF F E nS nT) (he : Continuous e) (hes : Continuous e.symm)
    (hΓ : ∀ x, e x ∈ ratLF F E nS nT ↔ x ∈ ratLF F E nS nT) (μ : Measure (WOF F E nS nT)) (hμ : μ.IsAddHaarMeasure)
    {𝓕 : Set (WOF F E nS nT)} (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ) (φ : WOF F E nS nT → ENNReal)
    (hφ : ∀ γ ∈ ratLF F E nS nT, ∀ x, φ (γ + x) = φ x) : ∫⁻ w in 𝓕, φ (e w) ∂μ = ∫⁻ w in 𝓕, φ w ∂μ := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e'⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AF F ⊗[F] E) := e'.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AF F ⊗[F] E) := e'.secondCountableTopology
  have : T2Space (AF F ⊗[F] E) := e'.isEmbedding.t2Space
  have : LocallyCompactSpace (WOF F E nS nT) :=
    inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AF F ⊗[F] E))
  have : SecondCountableTopology (WOF F E nS nT) :=
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AF F ⊗[F] E))
  have : T2Space (WOF F E nS nT) := inferInstanceAs (T2Space (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI tZ : IsTopologicalAddGroup (WOF F E nS nT) := inferInstance
  have hdisc : DiscreteTopology (ratLF F E nS nT) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hcov : ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈
      (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :=
    fun x => ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have hfin := @GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (WOF F E nS nT) _ _ tZ _ _ (ratLF F E nS nT) _ _
    hKc hcov μ hμ 𝓕 h𝓕
  exact @GlobalTheory.RatSubst.setLIntegral_comp_addEquiv (WOF F E nS nT) _ _ tZ _ _ _ _ (ratLF F E nS nT) _ e he hes hΓ μ hμ 𝓕 h𝓕
    hfin.ne φ hφ

end PositivityTheory.ThKW.SubstA

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutTrace
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem gauss_mul_integral (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hbij : Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x))
    (hF : Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume) (κ : ℂ)
    (hκ : ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, Fixes (opFF hc w) (latF F E nS nT Λ) f → IsVacF σ JS JT ξ₀ B.ψ ι s f → ∀ x,
      (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = κ * ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x)
    (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (ht : ∀ k, b * t k * a - t k ∈ Λ)
    (hu : ∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ (∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k)) *
      ∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v = r * κ :=
  Trc.gauss_mul_integral_A C hG hR hO hs ha hb hbij hF κ hκ n t ht hu

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.LagrangianProjectionFormula

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def pr (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (y : WOF F E nS nT) :
    (Fin (nT * nS) → AF F ⊗[F] E) →ₗ[AF F] AF F where
  toFun u := Algebra.trace (AF F) (AF F ⊗[F] E)
    (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace)
  map_add' u u' := by
    rw [map_add, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, mul_add, map_add]
  map_smul' r u := by
    have e : (vecE F E nS nT).symm (r • u) = r • (vecE F E nS nT).symm u := rfl
    rw [e, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, mul_smul_comm, map_smul, RingHom.id_apply]

theorem pr_add (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (y y' : WOF F E nS nT) :
    pr σ JS ξ₀ (y + y') = pr σ JS ξ₀ y + pr σ JS ξ₀ y' := by
  refine LinearMap.ext fun u => ?_
  change Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      (((y + y').map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace) =
    Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      ((y.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace) +
    Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (JS⁻¹.map (incAF F E) *
      ((y'.map (cAF σ))ᵀ * (vecE F E nS nT).symm u)).trace)
  rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, mul_add,
    map_add]

theorem phase_eq (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (hT : JT.det ≠ 0) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (y v : WOF F E nS nT) :
    phase σ JS JT ξ₀ ψ y v = ψ (pr σ JS ξ₀ y (vecE F E nS nT v)) := by
  unfold phase symplOF
  rw [hOF_dual JS JT hT]
  simp only [pr, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]

theorem pr_single (σ : E →ₐ[F] E) (hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (ξ₀ : E) (v : WOF F E nS nT) (k : Fin nT) (b : Fin nS) (z : AF F ⊗[F] E) :
    pr σ JS ξ₀ (Matrix.of fun i j => if i = k ∧ j = b then cAF σ z else 0) (vecE F E nS nT v) =
      Algebra.trace (AF F) (AF F ⊗[F] E) (incAF F E ξ₀ * (v * JS⁻¹.map (incAF F E)) k b * z) := by
  simp only [pr, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    apply_ite (cAF σ), map_zero, hcc, ite_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem pr_sep (σ : E →ₐ[F] E) (hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (hS : JS.det ≠ 0) (ξ₀ : E) (hξ₀ : ξ₀ ≠ 0)
    (u : Fin (nT * nS) → AF F ⊗[F] E) (h : ∀ y : WOF F E nS nT, ψ (pr σ JS ξ₀ y u) = 1) : u = 0 := by
  set v := (vecE F E nS nT).symm u with hv
  have hu : u = vecE F E nS nT v := by rw [hv, AddEquiv.apply_symm_apply]
  have hw : ∀ k b, (v * JS⁻¹.map (incAF F E)) k b = 0 := by
    intro k b
    have h0 : incAF F E ξ₀ * (v * JS⁻¹.map (incAF F E)) k b = 0 := by
      apply GlobalTheory.DblSiegelChar.eq_zero_of_psi_trace hψ
      intro t
      have := h (Matrix.of fun i j => if i = k ∧ j = b then cAF σ t else 0)
      rwa [hu, pr_single σ hcc] at this
    have hunit : IsUnit (incAF F E ξ₀) := (IsUnit.mk0 ξ₀ hξ₀).map (incAF F E)
    exact hunit.mul_right_eq_zero.1 h0
  have e1 : v * JS⁻¹.map (incAF F E) = 0 := by
    ext k b
    exact hw k b
  have e2 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul JS (Ne.isUnit hS), Matrix.map_one _ (map_zero _) (map_one _)]
  have hv0 : v = 0 := by
    calc v = v * JS⁻¹.map (incAF F E) * JS.map (incAF F E) := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
      _ = 0 := by rw [e1, Matrix.zero_mul]
  rw [hu, hv0, map_zero]

end PositivityTheory.ThKW.LagrangianProjectionFormula

end

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity PositivityTheory.ThKW.LagrangianProjectionFormula in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.finj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ N₁ N₂ : WOF F E nS nT → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ ν → Integrable N₂ ν →
      (∀ y, ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₁ v ∂ν = ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₂ v ∂ν) → N₁ = N₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 N₁ N₂ c₁ c₂ i₁ i₂ hN
  have hψ : IsStd B.ψ := hB.std
  have hψn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [cAF, sigR, GlobalTheory.DblSiegelChar.invol hB.cm]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have he : Continuous (vecE F E nS nT) := by
    show Continuous fun (w : WOF F E nS nT) (k : Fin (nT * nS)) => w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    exact continuous_pi fun k => continuous_id.matrix_elem _ _
  have he' : Continuous (vecE F E nS nT).symm := by
    show Continuous fun (u : Fin (nT * nS) → AF F ⊗[F] E) =>
      ((fun i j => u (finProdFinEquiv (i, j))) : WOF F E nS nT)
    first
      | exact continuous_pi fun i => continuous_pi fun j => continuous_apply _
      | fun_prop
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) (AF F ⊗[F] E)
  let E' : WOF F E nS nT ≃ₜ+ (Fin (nT * nS) → AF F ⊗[F] E) :=
    { toAddEquiv := vecE F E nS nT, continuous_toFun := he, continuous_invFun := he' }
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  haveI : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let em : WOF F E nS nT ≃ᵐ (Fin (nT * nS) → AF F ⊗[F] E) := E'.toHomeomorph.toMeasurableEquiv
  haveI := hν
  have hμ : (ν.map em).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν E'
  have hpc : ∀ a : WOF F E nS nT, Continuous (pr σ JS ξ₀ a) := fun a => IsModuleTopology.continuous_of_linearMap _
  have hph : ∀ a, Continuous (phase σ JS JT ξ₀ B.ψ a) := by
    intro a
    have e : phase σ JS JT ξ₀ B.ψ a = fun v => B.ψ (pr σ JS ξ₀ a (vecE F E nS nT v)) :=
      funext fun v => phase_eq σ JS JT hT.2 ξ₀ B.ψ a v
    rw [e]
    exact hψ.1.comp ((hpc a).comp he)
  have hint : ∀ a (N : WOF F E nS nT → ℂ), Integrable N ν →
      Integrable (fun v => phase σ JS JT ξ₀ B.ψ a v * N v) ν := by
    intro a N hNi
    refine hNi.bdd_mul (c := 1) (hph a).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [phase_eq σ JS JT hT.2, hψn]
  set N : (Fin (nT * nS) → AF F ⊗[F] E) → ℂ := fun u => N₁ ((vecE F E nS nT).symm u) - N₂ ((vecE F E nS nT).symm u)
    with hNdef
  have hNc : Continuous N := (c₁.comp he').sub (c₂.comp he')
  have hNi : Integrable N (ν.map em) := by
    rw [integrable_map_equiv em N]
    have : N ∘ em = fun v => N₁ v - N₂ v := by
      funext v
      simp only [hNdef, Function.comp_apply]
      rw [show (vecE F E nS nT).symm (em v) = v from (vecE F E nS nT).symm_apply_apply v]
    rw [this]
    exact i₁.sub i₂
  have key : ∀ a, ∫ u, B.ψ (pr σ JS ξ₀ a u) * N u ∂(ν.map em) = 0 := by
    intro a
    rw [integral_map_equiv em]
    have hx : ∀ v, B.ψ (pr σ JS ξ₀ a (em v)) * N (em v) =
        phase σ JS JT ξ₀ B.ψ a v * N₁ v - phase σ JS JT ξ₀ B.ψ a v * N₂ v := by
      intro v
      have h1 : (vecE F E nS nT).symm (em v) = v := (vecE F E nS nT).symm_apply_apply v
      have h2 : em v = vecE F E nS nT v := rfl
      simp only [hNdef, h2, AddEquiv.symm_apply_apply]
      rw [phase_eq σ JS JT hT.2]
      ring
    simp_rw [hx]
    rw [integral_sub (hint a N₁ i₁) (hint a N₂ i₂), hN a, sub_self]
  have h0 := GlobalTheory.T.eq_zero_of_adelicFourier_separatingChars_vanish F E B.ψ hψ (nT * nS) (WOF F E nS nT) (pr σ JS ξ₀) (pr_add σ JS ξ₀)
    (fun u hu => pr_sep σ hcc hψ JS hS.2 ξ₀ hξ₀ u hu) (ν.map em) hμ N hNc hNi key
  funext v
  have := congrFun h0 (vecE F E nS nT v)
  simp only [hNdef, AddEquiv.symm_apply_apply, Pi.zero_apply] at this
  exact sub_eq_zero.1 this
end

