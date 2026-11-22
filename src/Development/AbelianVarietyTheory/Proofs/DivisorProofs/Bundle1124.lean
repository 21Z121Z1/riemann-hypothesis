import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralZeroOfDerivativeAlongConjCurve
section
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

open GlobalTheory.AutomorphicL2Unitary Set

namespace GlobalTheory.Orb

theorem orbInt_comp_conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (dh : Measure H)
    [dh.IsHaarMeasure] [dh.IsMulRightInvariant] (γ : H) (dt : Measure (cent γ)) [dt.IsHaarMeasure]
    [dt.IsMulRightInvariant] (g : H) (f : H → ℂ) :
    orbInt dh γ dt (f ∘ conjEquiv g) = orbInt dh γ dt f := by
  let r : Quot (cent γ) ≃ᵐ Quot (cent γ) :=
    { toFun := rmul _ g⁻¹
      invFun := rmul _ g
      left_inv := fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]
      right_inv := fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one]
      measurable_toFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable
      measurable_invFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable }
  have hr : MeasurePreserving r (quotMeas _ dt dh) (quotMeas _ dt dh) :=
    measurePreserving_rmul_quotMeas (isClosed_cent γ) g⁻¹
  have h3 : descend (cent γ) (conjFn γ (f ∘ conjEquiv g)) = descend (cent γ) (conjFn γ f) ∘ r := funext fun q => by
    conv_rhs => rw [← Quotient.out_eq q]
    refine Eq.trans ?_ ((leftInv_conjFn le_rfl f).descend_mk (q.out * g⁻¹)).symm
    exact congrArg f (show g * _ * g⁻¹ = _ by group)
  rw [orbInt, quotInt, h3]
  exact hr.integral_comp' _

theorem orbitalIntegral_zero_of_derivative_along_conj_curve {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H) (hs : IsProperOrbit (cent s) s) (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H) (hc : Continuous c) (f f' : H → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f') (hf'c : HasCompactSupport f') (hd : ∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) : HasOrbInt μ s dt f' 0 := by
  have hO := hs.hasOrbInt (dh := μ) (dt := dt) hf' hf'c
  refine ⟨hO.1, ?_⟩
  change orbInt μ s dt f' = 0
  set ν := quotMeas (cent s) dt μ
  have hcf : ∀ (φ : H → ℂ) (g : H), Continuous φ → Continuous (conjFn s (φ ∘ conjEquiv g)) := fun φ g hφ =>
    hφ.comp ((conjEquiv g).continuous.comp (by fun_prop : Continuous fun x : H => x⁻¹ * s * x))
  have hmeas : ∀ (φ : H → ℂ) (g : H), Continuous φ →
      AEStronglyMeasurable (descend (cent s) (conjFn s (φ ∘ conjEquiv g))) ν := fun φ g hφ =>
    (measurable_descend (leftInv_conjFn le_rfl _) (hcf φ g hφ).measurable).aestronglyMeasurable
  let F : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f ∘ conjEquiv (c v)⁻¹))
  let F' : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f' ∘ conjEquiv (c v)⁻¹))
  have hconst : ∀ v, ∫ q, F v q ∂ν = orbInt μ s dt f := fun v =>
    orbInt_comp_conjEquiv μ s dt (c v)⁻¹ f

  obtain ⟨M, hM⟩ := hf'.bounded_above_of_compact_support hf'c
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  set K : Set H := (fun p : ℝ × H => c p.1 * p.2 * (c p.1)⁻¹) '' (Icc (-1) 1 ×ˢ tsupport f')
  have hK : IsCompact K := (isCompact_Icc.prod hf'c).image (by fun_prop)
  obtain ⟨χ, hχ1, -, hχc, hχI⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let χC : H → ℂ := fun x => ((χ x : ℝ) : ℂ)
  have hχC : Continuous χC := by fun_prop
  have hχCc : HasCompactSupport χC := HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hχc Complex.ofReal_zero
  have hχO := hs.hasOrbInt (dh := μ) (dt := dt) hχC hχCc
  let bound : Quot (cent s) → ℝ := fun q => M * ‖descend (cent s) (conjFn s χC) q‖
  have hbound : Integrable bound ν := hχO.1.norm.const_mul M
  have hb : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, ‖F' v q‖ ≤ bound q := by
    intro q v hv
    change ‖f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹)‖ ≤ M * ‖χC (q.out⁻¹ * s * q.out)‖
    rw [inv_inv]
    set y := (c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v
    by_cases hy : y ∈ tsupport f'
    · have hx : q.out⁻¹ * s * q.out ∈ K := ⟨(v, y), ⟨hv, hy⟩, by simp only [y]; group⟩
      have : χC (q.out⁻¹ * s * q.out) = 1 := by simp [χC, hχ1 hx]
      rw [this, norm_one, mul_one]
      exact hM y
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  have hderiv : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun w => F w q) (F' v q) v := by
    intro q v _
    have e1 : (fun w => F w q) = fun w => f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * c w) := funext fun w => by
      change f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * (c w)⁻¹⁻¹) = _
      rw [inv_inv]
    have e2 : F' v q = f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v) := by
      change f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹) = _
      rw [inv_inv]
    rw [e1, e2]
    exact hd _ v
  have hF0 : Integrable (F 0) ν :=
    (hs.hasOrbInt (dh := μ) (dt := dt) (f := f ∘ conjEquiv (c 0)⁻¹) (hf.comp (conjEquiv _).continuous)
      (hfc.comp_homeomorph (conjEquiv (c 0)⁻¹).toHomeomorph)).1
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (s := Icc (-1 : ℝ) 1) (bound := bound) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun v => hmeas f _ hf) hF0 (hmeas f' _ hf')
    (ae_of_all _ hb) hbound (ae_of_all _ hderiv)
  have h0 : HasDerivAt (fun v => ∫ q, F v q ∂ν) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  have := h0.unique hmain.2
  rw [← orbInt_comp_conjEquiv μ s dt (c 0)⁻¹ f']
  exact this.symm

theorem hasOrbInt_zero_of_hasDerivAt_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsProperOrbit (cent s) s → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H), Continuous c → ∀ (f f' : H → ℂ), Continuous f → HasCompactSupport f → Continuous f' → HasCompactSupport f' → (∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) → HasOrbInt μ s dt f' 0 :=
  fun _ _ _ _ _ _ _ _ _ μ _ _ s hs dt _ _ c hc f f' hf hfc hf' hf'c hd =>
    orbitalIntegral_zero_of_derivative_along_conj_curve μ s hs dt c hc f f' hf hfc hf' hf'c hd

end GlobalTheory.Orb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateFirst
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem phiC_congr {D : D7} (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem alg_step {l c a a' x y : ℂ} (h1 : x = l * a) (h2 : a = c * a') (h3 : y = l * a') : x = c * y := by
  rw [h1, h2, h3]; ring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

theorem baseEmbedding_restriction_eq_coefficientInclusion (fw : FWTie T R κw v₀) : res T (sg0 D A) = T.σ₀ :=
  (congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)

theorem ev_base (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (f : Cu T κw i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κw i)) : ℂ) *
        (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = (O i).s0 := (baseEmbedding_restriction_eq_coefficientInclusion T R κw v₀ fw).trans (sOv_eq T.toCore (O i).c' (O i).hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans (O i).hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have h2 := phiC_congr T e hV (O i).hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1))
  have h3 := phi_cE T R O i (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) h
  exact (congrFun (h1.trans h2) h).trans h3.symm

theorem reading_actG (F : Face D A) (hc : R.Char F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hev : fw.Evaluates)
    (hinj : EvInj T R v₀) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hE : (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0)) (g : G) (f : Cu T κw i) :
    ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1)) ∧
      fw.jK i (sg0 D A) f₁ =
        D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f) := by
  have ht := GlobalTheory.T.lift_equivariance_weil_model R F hc i
  have hk := ht.1 g
  obtain ⟨k, hk⟩ := hk
  have hq := hE g k hk (f : T.R ((i : ℕ) + 1)) f.2
  refine ⟨⟨_, hq.1⟩, rfl, hinj i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) (funext fun h => ?_)⟩
  have h1 := ev_base T R κw v₀ fw i hev O ⟨_, hq.1⟩ h
  have h2 := ev_base T R κw v₀ fw i hev O f (h * k)
  have h3 := (ht.2 (sg0 D A)).1 g k hk (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h
  have h4 := (hq.2 h).trans (congrArg (· * _) (hc.grp.chiW i g).symm)
  have h5 := alg_step h1 h4 (h3.trans h2)
  refine h5.trans ?_
  exact (congrFun (congrArg (fun y => y (v₀ i (sg0 D A))) (map_smul (R.HW i (sg0 D A)).e _ _)) h).symm

theorem base_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), fw.Evaluates → EvInj T R v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), (O i).EquivAt (κw i) (T.cE ((i : ℕ) + 1) (O i).s0) → ∀ (g : G) (f : Cu T κw i), ∃ f₁ : Cu T κw i, (f₁ : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1)) ∧ fw.jK i (sg0 D A) f₁ = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i (sg0 D A) g (fw.jK i (sg0 D A) f) :=
  fun T _ R F κw v₀ hc fw i hev hinj O hE g f => reading_actG T R κw v₀ F hc fw i hev hinj O hE g f

end GlobalTheory.GalLift.BaseEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorMvPolynomialSubmoduleEqTopOfOneMulXStatement
section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensorMvPolynomial_submodule_eq_top_of_one_mul_X : ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)), PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N → (∀ (w : ι) (l : σ), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) → N = ⊤ := by
  first | exact @GlobalTheory.RealLift.tensor_submodule_eq_top | exact GlobalTheory.RealLift.tensor_submodule_eq_top | (intros; apply GlobalTheory.RealLift.tensor_submodule_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingleton
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensSup

theorem tensAll_sup_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U C : ∀ w, Submodule ℂ (V w)) :
    tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose u hu c hc huc using fun w => Submodule.mem_sup.1 (hf w)
  have hfe : f = u + c := funext fun w => (huc w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_add_univ]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : s = Finset.univ
  · subst hs
    refine Submodule.mem_sup_left (Submodule.subset_span ⟨u, hu, ?_⟩)
    congr 1
    funext w
    simp
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ s := by
      by_contra h
      push_neg at h
      exact hs (Finset.eq_univ_of_forall h)
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨s.piecewise u c, ⟨w, ?_⟩, rfl⟩)
    rw [Finset.piecewise_eq_of_notMem _ _ _ hw]
    exact hc w

theorem tensAll_fin {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U : ∀ w, Submodule ℂ (V w)) (hU : ∀ w, FiniteDimensional ℂ (U w)) :
    FiniteDimensional ℂ (tensAll U) := by
  have : tensAll U ≤ LinearMap.range (PiTensorProduct.map fun w => (U w).subtype) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun w => (⟨f w, hf w⟩ : U w), by rw [PiTensorProduct.map_tprod]; rfl⟩
  exact Submodule.finiteDimensional_of_le this

theorem tensAll_span_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (v : ∀ w, V w) :
    tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose a ha using fun w => Submodule.mem_span_singleton.1 (hf w)
  have hfe : f = fun w => a w • v w := funext fun w => (ha w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem main : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)],
    ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧
      ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧
      ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  intro T _ _ V _ _ U C
  exact ⟨tensAll_sup_le U C, tensAll_fin U, tensAll_span_le⟩

end GlobalTheory.HoweR.TensSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchIff
section
noncomputable section

namespace GlobalTheory.ThK.PolynomialMatching

open scoped TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def PolMatchOn (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (T : Finset (Pl F)) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem polMatch_iff (B : Base F E) (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a') (Rf : FinMaps F a a')
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) :
    PolMatch B G X R Rf Φ Φ' ↔ ∃ T : Finset (Pl F), X.T ⊆ T ∧ PolMatchOn B G X R Rf T Φ Φ' := Iff.rfl

theorem I'_sum {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {ι : Type} (s : Finset ι) (Ψ : ι → (Fin a' × Fin (a + a') → AF F) → ℂ)
    (hΨ : ∀ j ∈ s, Ψ j ∈ schA F (Fin a' × Fin (a + a'))) (hc : ∀ j ∈ s, G.M'.Conv om' (Ψ j)) (h : UA σ G.W.J) :
    G.M'.I om' (∑ j ∈ s, Ψ j) h = ∑ j ∈ s, G.M'.I om' (Ψ j) h := by
  have e : ∀ g, theta om' (∑ j ∈ s, Ψ j) g h = ∑ j ∈ s, theta om' (Ψ j) g h := by
    intro g
    simp only [theta, map_sum]
    have hm : ∀ j ∈ s, om' (g, h) (Ψ j) ∈ schA F (Fin a' × Fin (a + a')) :=
      fun j hj => hT.weil'.isUSplitting.pres _ _ (hΨ j hj)
    induction s using Finset.induction_on with
    | empty => simp [thetaSum]
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk,
        thetaSum_add F (hm k (Finset.mem_insert_self _ _)) (Submodule.sum_mem _ fun j hj => hm j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hΨ j (Finset.mem_insert_of_mem hj)) (fun j hj => hc j (Finset.mem_insert_of_mem hj))
          (fun j hj => hm j (Finset.mem_insert_of_mem hj))]
  simp only [Model.I, e]
  exact integral_finset_sum s fun j hj => hc j hj h

end GlobalTheory.ThK.PolynomialMatching
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDetHermitianSumZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

namespace GlobalTheory.FibreProj.DetPol

open Classical in

theorem pol_eq_zero_of_indep {ι : Type} [Fintype ι] (φ : (ι → ℤ) → ℝ) (i : ι)
    (h : ∀ n v, φ (Function.update n i v) = φ n) : pol φ = 0 := by
  unfold pol
  refine Finset.sum_involution (fun S _ => if i ∈ S then S.erase i else insert i S) ?_ ?_
    (fun _ _ => Finset.mem_univ _) ?_
  · intro S _
    have hpt : ∀ T : Finset ι, (i ∈ T ↔ i ∉ S) → (∀ j, j ≠ i → (j ∈ T ↔ j ∈ S)) →
        (fun j => if j ∈ T then (-1 : ℤ) else 0) =
          Function.update (fun j => if j ∈ S then (-1 : ℤ) else 0) i (if i ∈ T then -1 else 0) := by
      intro T _ hT
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        by_cases hS : j ∈ S
        · simp [hS, (hT j hj).2 hS]
        · have : j ∉ T := fun h' => hS ((hT j hj).1 h')
          simp [hS, this]
    by_cases hS : i ∈ S
    · simp only [hS, if_true]
      rw [hpt (S.erase i) (by simp [hS]) (fun j hj => by simp [hj]), h]
      have hc := Finset.card_erase_add_one hS
      rw [← hc, pow_succ]
      ring
    · simp only [hS, if_false]
      rw [hpt (insert i S) (by simp [hS]) (fun j hj => by simp [hj]), h]
      rw [Finset.card_insert_of_notMem hS, pow_succ]
      ring
  · intro S _ _ heq
    by_cases hS : i ∈ S
    · simp only [hS, if_true] at heq
      have hn := Finset.notMem_erase i S
      rw [heq] at hn
      exact hn hS
    · simp only [hS, if_false] at heq
      have hm := Finset.mem_insert_self i S
      rw [heq] at hm
      exact hS hm
  · intro S _
    by_cases hS : i ∈ S
    · simp [hS, Finset.insert_erase hS]
    · simp [hS, Finset.erase_insert hS]

variable (α β : Type) [Fintype α] [Fintype β]

def DepOn (T : Finset β) (g : (α ⊕ β → ℤ) → ℂ) : Prop :=
  ∀ n n' : α ⊕ β → ℤ, (∀ a, n (Sum.inl a) = n' (Sum.inl a)) →
    (∀ b ∈ T, n (Sum.inr b) = n' (Sum.inr b)) → g n = g n'

def lowDeg (k : ℕ) : Submodule ℂ ((α ⊕ β → ℤ) → ℂ) :=
  Submodule.span ℂ {g | ∃ T : Finset β, T.card ≤ k ∧ DepOn α β T g}

variable {α β}

theorem mem_lowDeg_of_depOn {k : ℕ} (T : Finset β) (hT : T.card ≤ k) (g : (α ⊕ β → ℤ) → ℂ)
    (hg : DepOn α β T g) : g ∈ lowDeg α β k :=
  Submodule.subset_span ⟨T, hT, hg⟩

theorem lowDeg_mono {k l : ℕ} (h : k ≤ l) : lowDeg α β k ≤ lowDeg α β l :=
  Submodule.span_mono fun _ ⟨T, hT, hg⟩ => ⟨T, hT.trans h, hg⟩

theorem mul_mem_lowDeg {k l : ℕ} {f g : (α ⊕ β → ℤ) → ℂ} (hf : f ∈ lowDeg α β k)
    (hg : g ∈ lowDeg α β l) : f * g ∈ lowDeg α β (k + l) := by
  classical
  have gen : ∀ f, (∃ T : Finset β, T.card ≤ k ∧ DepOn α β T f) → ∀ g, g ∈ lowDeg α β l →
      f * g ∈ lowDeg α β (k + l) := by
    intro f ⟨T, hT, hfT⟩ g hg
    induction hg using Submodule.span_induction with
    | mem g hg' =>
      obtain ⟨T', hT', hgT⟩ := hg'
      refine mem_lowDeg_of_depOn (T ∪ T') ((Finset.card_union_le _ _).trans (by omega)) _ ?_
      intro n n' ha hb
      simp only [Pi.mul_apply]
      rw [hfT n n' ha (fun b hb' => hb b (Finset.mem_union_left _ hb')),
        hgT n n' ha (fun b hb' => hb b (Finset.mem_union_right _ hb'))]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  induction hf using Submodule.span_induction with
  | mem f hf' => exact gen f hf' g hg
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem prod_mem_lowDeg {ι : Type} (s : Finset ι) (f : ι → (α ⊕ β → ℤ) → ℂ) (k : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ lowDeg α β (k i)) : ∏ i ∈ s, f i ∈ lowDeg α β (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact mem_lowDeg_of_depOn ∅ le_rfl _ fun _ _ _ _ => rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_lowDeg (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem pol_eq_zero_of_mem_lowDeg {k : ℕ} (hk : k < Fintype.card β) {g : (α ⊕ β → ℤ) → ℂ}
    (hg : g ∈ lowDeg α β k) : ∀ L : ℂ →ₗ[ℝ] ℝ, pol (fun n => L (g n)) = 0 := by
  classical
  induction hg using Submodule.span_induction with
  | mem g hg' =>
    obtain ⟨T, hT, hgT⟩ := hg'
    intro L
    obtain ⟨b, hb⟩ : ∃ b, b ∉ T := by
      by_contra hc
      push_neg at hc
      have := Finset.card_le_card (fun b _ => hc b : (Finset.univ : Finset β) ⊆ T)
      rw [Finset.card_univ] at this
      omega
    refine pol_eq_zero_of_indep _ (Sum.inr b) fun n v => ?_
    congr 1
    refine hgT _ _ (fun a => by simp) fun b' hb' => ?_
    have : b' ≠ b := fun h => hb (h ▸ hb')
    simp [Function.update_apply, this]
  | zero => intro L; simp [pol]
  | add x y _ _ hx hy =>
    intro L
    have h1 := hx L
    have h2 := hy L
    simp only [pol] at h1 h2 ⊢
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
  | smul c x _ hx =>
    intro L
    have := hx (L ∘ₗ LinearMap.mulLeft ℝ c)
    simpa [smul_eq_mul] using this

end GlobalTheory.FibreProj.DetPol

namespace GlobalTheory.FibreProj.DetPol

theorem det_add_perturb_eq {D d : ℕ} {β : Type} [Fintype β] (A : Matrix (Fin D) (Fin D) ℂ)
    (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ) (K : β → Matrix (Fin d) (Fin d) ℂ)
    (c : β → ℂ) :
    Matrix.det (A + ∑ b, c b • (P * K b * Q)) =
      Matrix.det (Matrix.fromBlocks A (-(P * ∑ b, c b • K b)) Q 1) := by
  rw [Matrix.det_fromBlocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
  congr 2
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem pol_det_perturb_eq_zero : ∀ (D d : ℕ) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β →
    ∀ (H : α → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ)
      (K : β → Matrix (Fin d) (Fin d) ℂ),
    pol (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a +
      ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) = 0 := by
  intro D d α β _ _ hd H P Q K
  classical
  let M : (α ⊕ β → ℤ) → Matrix (Fin D ⊕ Fin d) (Fin D ⊕ Fin d) ℂ := fun n =>
    Matrix.fromBlocks (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a)
      (-(P * ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • K b)) Q 1
  have hfun : (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a +
      ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) =
      fun n => Complex.reLm ((M n).det) := by
    funext n
    rw [det_add_perturb_eq]
    rfl
  rw [hfun]
  refine pol_eq_zero_of_mem_lowDeg hd ?_ Complex.reLm
  have hentry : ∀ r c : Fin D ⊕ Fin d,
      (fun n => M n r c) ∈ lowDeg α β (Sum.elim (fun _ => 0) (fun _ => 1) c) := by
    intro r c
    rcases c with j | j
    · refine mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' ha _ => ?_
      rcases r with r | r
      · simp [M, ha]
      · simp [M]
    · rcases r with r | r
      · have : (fun n => M n (Sum.inl r) (Sum.inr j)) =
            ∑ b, (-(P * K b) r j) • (fun n : α ⊕ β → ℤ => ((n (Sum.inr b) : ℝ) : ℂ)) := by
          funext n
          simp [M, Matrix.mul_sum, Matrix.sum_apply, Matrix.mul_smul, Finset.sum_apply, mul_comm]
        rw [this]
        refine Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
        refine mem_lowDeg_of_depOn {b} (by simp) _ fun n n' _ hb => ?_
        simp [hb b (Finset.mem_singleton_self b)]
      · exact lowDeg_mono (Nat.zero_le 1)
          (mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' _ _ => by simp [M])
  have hdet : (fun n => (M n).det) =
      ∑ σ : Equiv.Perm (Fin D ⊕ Fin d), Equiv.Perm.sign σ • ∏ i, (fun n => M n (σ i) i) := by
    funext n
    simp [Matrix.det_apply, Finset.sum_apply, Finset.prod_apply]
  rw [show (fun n => (M n).det) = _ from hdet]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  have := prod_mem_lowDeg Finset.univ (fun i => fun n => M n (σ i) i)
    (fun i => Sum.elim (fun _ => 0) (fun _ => 1) i) (fun i _ => hentry (σ i) i)
  simpa [Fintype.sum_sum_type] using this

end GlobalTheory.FibreProj.DetPol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationPrincipalLevelEqCoreLevelOpenStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, (∀ g : GA D (Wc D i), g ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ↔ cast (congrArg (GA D) hV.symm) g ∈ T.Kf ((i : ℕ) + 1) (res T σ)) ∧ (∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1) ∧ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) ≤ GfC (Wc D i) ∧ ∃ U : Subgroup (GA D (Wc D i)), IsOpen (U : Set (GA D (Wc D i))) ∧ ∀ k ∈ U, k ∈ GfC (Wc D i) → k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  first | exact @GlobalTheory.HolDict.PrincLev.principal_level | exact GlobalTheory.HolDict.PrincLev.principal_level | (intros; apply GlobalTheory.HolDict.PrincLev.principal_level <;> assumption)
end

