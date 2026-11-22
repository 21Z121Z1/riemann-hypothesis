import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Topology
open scoped ContDiff

namespace GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

def invM (y : Lie E a) : Lie E a := toL (Matrix.of y)⁻¹

omit [IsTotallyComplex E] in

theorem contDiffOn_invM : ContDiffOn ℝ ∞ (invM (E := E) (a := a)) (invSet E a) := by
  have h1 : ContDiffOn ℝ ∞ (fun y : Lie E a => Ring.inverse (Matrix.of y).det) (invSet E a) := fun y hy => by
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hy
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact (this.comp y contDiff_det.contDiffAt).contDiffWithinAt
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  have h2 : ContDiff ℝ ∞ fun y : Lie E a => (Matrix.of y).adjugate i j := by
    simp only [Matrix.adjugate_apply]
    have h3 : ContDiff ℝ ∞ fun y : Lie E a => (Function.update y j (Pi.single i 1) : Lie E a) := by
      refine contDiff_pi.2 fun k => ?_
      by_cases h : k = j
      · subst h; simpa using contDiff_const
      · simpa [Function.update_of_ne h] using contDiff_apply ℝ _ k
    exact contDiff_det.comp h3
  exact h1.mul h2.contDiffOn

theorem continuous_infGL : Continuous (infGL E a) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem continuousOn_chart {φ : GA E a → ℂ} (hφ : Continuous φ) :
    ContinuousOn (fun p : GA E a × Lie E a => chart φ p.1 p.2) (Set.univ ×ˢ invSet E a) := by
  rw [continuousOn_iff_continuous_restrict]
  have hu : Continuous fun p : (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a)) =>
      (IsUnit.unit (p.2.2 : IsUnit (Matrix.of p.1.2)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_snd.comp continuous_subtype_val, ?_⟩
    have := contDiffOn_invM.continuousOn.comp_continuous
      (f := fun p : (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a)) => p.1.2)
      (continuous_snd.comp continuous_subtype_val) fun p => p.2.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  refine (hφ.comp ((continuous_fst.comp continuous_subtype_val).mul (continuous_infGL.comp hu))).congr fun p => ?_
  exact (chart_val φ p.1.1 (IsUnit.unit (p.2.2 : IsUnit (Matrix.of p.1.2)))).symm

omit [IsTotallyComplex E] in

def coef (i : Fin (Module.finrank ℝ (Lie E a))) (y : Lie E a) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord i) ∘L lmul (invM y)

omit [IsTotallyComplex E] in

theorem contDiffOn_coef (i : Fin (Module.finrank ℝ (Lie E a))) : ContDiffOn ℝ ∞ (coef i) (invSet E a) := by
  refine contDiffOn_clm_apply.2 fun Y => ?_
  exact (Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord i) ∘L
    rmul Y).contDiff.comp_contDiffOn contDiffOn_invM

theorem fderiv_chart (φ : Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart φ.1 g) y = ∑ i, chart (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 g y • coef i y := by
  ext Y
  have e : Y = rmul (lmul (invM y) Y) y := by
    change Matrix.of Y = Matrix.of y * ((Matrix.of y)⁻¹ * Matrix.of Y)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hy)]
  have e2 : ∀ X, rmul X y = lmul y X := fun _ => rfl
  conv_lhs => rw [e, e2, ← (Module.finBasis ℝ (Lie E a)).sum_repr (lmul (invM y) Y)]
  rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ← e2, ← chart_lieD φ.2 _ g hy, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm,
    Complex.real_smul]
  rfl

def Good (φ : Sm E a) : Prop := (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}

theorem Good.lie {φ : Sm E a} (h : Good φ) (X : Lie E a) : Good (lie E a X φ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · have e : chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
      funext x; simp only [chart, mul_assoc, h.1]
    simp only [lie_apply, lieD, e]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun k hk => ?_)
    have e := LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : rt E a (finGL E a k) φ = φ := hk
    simp only [Module.End.mul_apply, hk'] at e
    exact e.symm

omit [IsTotallyComplex E] in

theorem exists_bound {r : ℕ} {V : Type} [NormedAddCommGroup V] {Ψ : GA E a → Lie E a → V} {S : Set (Lie E a)}
    (hS : IsCompact S) (hc : ContinuousOn (fun p : GA E a × Lie E a => Ψ p.1 p.2) (Set.univ ×ˢ S))
    (hl : ∀ γ g, Ψ (ratGL E a γ * g) = Ψ g) (g : GA E a) :
    ∃ C, ∀ (x : BlockIx a r → Ad E), ∀ y ∈ S, ‖Ψ (unip x * g) y‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn
    (f := fun p : (BlockIx a r → Ad E) × Lie E a => Ψ (unip p.1 * g) p.2)
    (hc.comp (((CuspidalL2GL.continuous_unip.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun p hp => ⟨trivial, hp.2⟩)
  refine ⟨C, fun x y hy => ?_⟩
  obtain ⟨_, ⟨z, rfl⟩, hk⟩ := hcov x
  have := hC (_, y) ⟨hk, hy⟩
  simp only [unip_add, mul_assoc] at this
  exact (congrArg (fun f => ‖f y‖) ((congrArg (fun u => Ψ (u * _)) (unip_algebraMap z)).trans (hl _ _))).symm.trans_le
    this

theorem Good.chart_left {φ : Sm E a} (h : Good φ) (γ : GL (Fin a) E) (g : GA E a) :
    chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
  funext x; simp only [chart, mul_assoc, h.1]

theorem Good.continuousOn_chart {φ : Sm E a} (h : Good φ) :
    ContinuousOn (fun p : GA E a × Lie E a => chart φ.1 p.1 p.2) (Set.univ ×ˢ invSet E a) :=
  ConstTermSmooth.continuousOn_chart (ContAut.continuous_of_isOpen_stab E a φ h.2)

theorem Good.continuousOn_fderiv {φ : Sm E a} (h : Good φ) :
    ContinuousOn (fun p : GA E a × Lie E a => fderiv ℝ (chart φ.1 p.1) p.2) (Set.univ ×ˢ invSet E a) := by
  refine ContinuousOn.congr ?_ fun p hp => fderiv_chart φ p.1 hp.2
  exact continuousOn_finset_sum _ fun i _ => (h.lie _).continuousOn_chart.smul
    ((contDiffOn_coef i).continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2)

section Integral

variable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
  (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν]

omit [IsTotallyComplex E] in

theorem integrable_unip {V : Type} [NormedAddCommGroup V] {Ψ : GA E a → Lie E a → V}
    (hc : ContinuousOn (fun p : GA E a × Lie E a => Ψ p.1 p.2) (Set.univ ×ˢ invSet E a))
    (hl : ∀ γ g, Ψ (ratGL E a γ * g) = Ψ g) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    Integrable (fun x => Ψ (unip x * g) y) ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  obtain ⟨C, hC⟩ := exists_bound (r := r) (isCompact_singleton (x := y))
    (hc.mono (Set.prod_mono_right (Set.singleton_subset_iff.2 hy))) hl g
  have hf : Continuous fun x : BlockIx a r → Ad E => Ψ (unip x * g) y :=
    hc.comp_continuous ((CuspidalL2GL.continuous_unip.mul continuous_const).prodMk continuous_const) fun _ => ⟨trivial, hy⟩
  exact Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun x => hC x y rfl)

omit [BorelSpace (BlockIx a r → Ad E)] [IsFiniteMeasure ν] in

theorem chart_integral (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun g => ∫ x, φ (unip x * g) ∂ν) g = fun y => ∫ x, chart φ (unip x * g) y ∂ν := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, mul_assoc]
  · simp only [chart, dif_neg h, integral_zero]

theorem Good.hasFDerivAt {φ : Sm E a} (h : Good φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    HasFDerivAt (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) (∫ x, fderiv ℝ (chart φ.1 (unip x * g)) y ∂ν) y := by
  rw [chart_integral]
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hy)
  have hl : ∀ γ g, (fun y => fderiv ℝ (chart φ.1 (ratGL E a γ * g)) y) = fun y => fderiv ℝ (chart φ.1 g) y :=
    fun γ g => by rw [h.chart_left]
  obtain ⟨C, hC⟩ := exists_bound (r := r) (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) hS
    (h.continuousOn_fderiv.mono (Set.prod_mono_right hSU)) hl g
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) fun z hz =>
      (integrable_unip ν h.continuousOn_chart h.chart_left g hz).1)
    (integrable_unip ν h.continuousOn_chart h.chart_left g hy)
    (integrable_unip ν (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) h.continuousOn_fderiv hl g hy).1
    (.of_forall hC) (integrable_const C) (.of_forall fun x z hz => ?_)
  exact ((contDiffAt_chart φ.2 _ (hSU hz)).differentiableAt (by simp)).hasFDerivAt

theorem Good.fderiv_integral {φ : Sm E a} (h : Good φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) y = ∑ i,
      chart (fun g => ∫ x, (CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 (unip x * g) ∂ν) g y • coef i y := by
  rw [(h.hasFDerivAt ν g hy).fderiv]
  simp only [fderiv_chart φ _ hy, chart_integral]
  rw [integral_finset_sum _ fun i _ =>
    (integrable_unip ν (h.lie _).continuousOn_chart (h.lie _).chart_left g hy).smul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _

theorem contDiffOn_integral (g : GA E a) (n : ℕ) : ∀ φ : Sm E a, Good φ →
    ContDiffOn ℝ n (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) (invSet E a) := by
  induction n with
  | zero =>
    intro φ h
    exact contDiffOn_zero.2 fun y hy => (h.hasFDerivAt ν g hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro φ h
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun y hy => (h.hasFDerivAt ν g hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr ?_ fun y hy => h.fderiv_integral ν g hy
    exact ContDiffOn.sum fun i _ => (ih _ (h.lie _)).smul ((contDiffOn_coef i).of_le (by exact_mod_cast le_top))

end Integral

theorem constTerm_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a),
      lieD X (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hl ho
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simp [h1]⟩
  have h : Good φ := ⟨hl, ho⟩
  refine ⟨fun g => contDiffOn_infty.2 fun n => contDiffOn_integral _ g n φ h, fun X g => ?_⟩
  rw [lieD, (h.hasFDerivAt (μ.restrict 𝓕) g (y := oneL E a) isUnit_one).fderiv, ContinuousLinearMap.integral_apply
    (integrable_unip _ (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) h.continuousOn_fderiv
      (fun γ g => by rw [h.chart_left]) g (y := oneL E a) isUnit_one)]
  rfl

end GlobalTheory.ConstTermSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceExtensionByZeroTensorOfPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.ExtZero

open GlobalTheory.CompanionTheory.SaGen

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_tmul (P : PlaceMap F K) (x : K) (e : E) :
    iB (E := E) P (x ⊗ₜ[F] e) = P.inj x ⊗ₜ[F] e := rfl

theorem iB_eq_sum [FiniteDimensional F E] (P : PlaceMap F K) (y : K ⊗[F] E) :
    iB (E := E) P y = ∑ k, P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
      ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := by
  set B := Algebra.TensorProduct.basis K (Module.finBasis F E)
  conv_lhs => rw [← B.sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, iB_tmul]

theorem continuous_iB [FiniteDimensional F E] [IsTopologicalRing K] (P : PlaceMap F K) :
    Continuous (iB (E := E) P) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) (AF F ⊗[F] E)
  have hc : ∀ k, Continuous fun y : K ⊗[F] E =>
      (Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k := fun k =>
    IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis K (Module.finBasis F E)).coord k)
  have h : (iB (E := E) P : K ⊗[F] E → AF F ⊗[F] E) = fun y => ∑ k,
      P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
        ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := funext (iB_eq_sum P)
  rw [h]
  exact continuous_finset_sum _ fun k _ =>
    Continuous.smul (f := fun y => P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k))
      (g := fun _ => (1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) (P.cont_inj.comp (hc k)) continuous_const

end GlobalTheory.CompanionTheory.SaGen.ExtZero

theorem GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) :=
  fun P => GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB P
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatePolynomialsFormMemKernelDifferential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus

theorem cstT_comp_affπ {Rg : Type} [CommRing Rg] {T : Scheme.{0}} {n : ℕ}
    (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (r : Rg) :
    cstT (g ≫ affπ Rg n) r = ringOf g (MvPolynomial.C r) := by
  have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) =
      (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
  simp only [cstT, ringOf, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [n2]

theorem polys_ker : ∀ (Rg : Type) [CommRing Rg] (A₀ T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), ((Q d).D₀.map (GlobalTheory.FormsLocus.cstT (g ≫ affπ Rg (mA * mB)))).mulVec (fun k => GlobalTheory.FormsLocus.ringOf g (GlobalTheory.FormsLocus.polys Q a d F k)) = 0 := by
  intro Rg _ A₀ T f N mA mB Q a g d F
  have hC : ((Q d).D₀.map MvPolynomial.C).mulVec (fun k => polys Q a d F k) = 0 := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, polys, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ν _ => ?_
    have h0 := congrFun (vecOf_ker (Q d) (monSec a d ν)) l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.id_apply, Pi.zero_apply] at h0
    calc ∑ k, MvPolynomial.C ((Q d).D₀ l k) * ((expand mA mB F).coeff ν * MvPolynomial.C (vecOf (Q d) (monSec a d ν) k))
        = (expand mA mB F).coeff ν * MvPolynomial.C (∑ k, (Q d).D₀ l k * vecOf (Q d) (monSec a d ν) k) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]; ring
      _ = 0 := by rw [h0, map_zero, mul_zero]
  have hm : (Q d).D₀.map (cstT (g ≫ affπ Rg (mA * mB))) = ((Q d).D₀.map MvPolynomial.C).map (ringOf g) := by
    rw [Matrix.map_map]; congr 1; funext r; exact cstT_comp_affπ g r
  rw [hm]
  funext l
  have e := RingHom.map_mulVec (ringOf g) ((Q d).D₀.map MvPolynomial.C) (fun k => polys Q a d F k) l
  rw [hC] at e
  simp only [Pi.zero_apply, map_zero] at e
  exact e.symm

end GlobalTheory.FormsLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspFormLin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {d : ℕ}

theorem growth_smul_add (c : ℂ) {f f' : GL (Fin d) (Cinf E) → ℂ}
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N)
    (h' : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f' y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖c * f y + f' y‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, h⟩ := h
  obtain ⟨C', N', h'⟩ := h'
  refine ⟨‖c‖ * |C| + |C'|, N + N', fun y => ?_⟩
  have h1 := one_le_height y
  have e : ‖f y‖ ≤ |C| * height y ^ (N + N') :=
    (h y).trans (mul_le_mul (le_abs_self C) (pow_le_pow_right₀ h1 (Nat.le_add_right N N'))
      (by positivity) (abs_nonneg C))
  have e' : ‖f' y‖ ≤ |C'| * height y ^ (N + N') :=
    (h' y).trans (mul_le_mul (le_abs_self C') (pow_le_pow_right₀ h1 (Nat.le_add_left N' N))
      (by positivity) (abs_nonneg C'))
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, add_mul, mul_assoc]
  exact add_le_add (mul_le_mul_of_nonneg_left e (norm_nonneg c)) e'

theorem isAutForm_smul_add (c : ℂ) {φ ψ : Sm E d} (h : IsAutForm φ) (h' : IsAutForm ψ) :
    IsAutForm (c • φ + ψ) where
  left γ g := by
    change c * φ.1 _ + ψ.1 _ = c * φ.1 _ + ψ.1 _
    rw [h.left, h'.left]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    ((h.level.inter h'.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
      have h1 : finRep E d k φ = φ := hk.1
      have h2 : finRep E d k ψ = ψ := hk.2
      change finRep E d k (c • φ + ψ) = c • φ + ψ
      rw [map_add, map_smul, h1, h2]
  kfin := by
    have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E d k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E d k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change cptRep E d k (c • φ + ψ) ∈ _
    rw [map_add, map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
      (Submodule.subset_span ⟨k, rfl⟩)
  zfin := by
    have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z φ) '' Zalg E d) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (Sm E d) => z ψ) '' Zalg E d)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    change z (c • φ + ψ) ∈ _
    rw [map_add, map_smul]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
      (Submodule.subset_span ⟨z, hz, rfl⟩)
  growth g := growth_smul_add c (h.growth g) (h'.growth g)

theorem isCuspForm_smul_add (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ) (c : ℂ)
    (φ ψ : Sm E d) (h : IsCuspForm φ) (h' : IsCuspForm ψ) : IsCuspForm (c • φ + ψ) := by
  refine ⟨isAutForm_smul_add c h.1 h'.1, fun r h0 h1 _ _ ν 𝓕 hν h𝓕 g => ?_⟩
  have i := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d φ h.1.level) h.1.left ν h𝓕 g
  have i' := CuspidalL2GL.integrableOn_unip (ContAut.continuous_of_isOpen_stab E d ψ h'.1.level) h'.1.left ν h𝓕 g
  change ∫ x in 𝓕, (c * φ.1 (unip x * g) + ψ.1 (unip x * g)) ∂ν = 0
  rw [integral_add (i.const_mul c) i', integral_const_mul, h.2 r h0 h1 ν 𝓕 hν h𝓕 g, h'.2 r h0 h1 ν 𝓕 hν h𝓕 g,
    mul_zero, add_zero]

end GlobalTheory.CuspFormLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsAgreementContainsFormIndependentFields
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem tieIn_of_nonempty_tie :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ⟨fw⟩ => ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalUnipotentVanishing
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_unipotent_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π → ∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → k) → GL (Fin N) k, (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → ∀ w : V, w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  first | exact @GlobalTheory.SmGL.CuspSpan.mem_span_unip | exact GlobalTheory.SmGL.CuspSpan.mem_span_unip | (intros; apply GlobalTheory.SmGL.CuspSpan.mem_span_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetCharIffExp
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetCharArch

theorem map_conj {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

end GlobalTheory.DetCharArch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminedByLowTypes
section
noncomputable section

namespace GlobalTheory.LowTypeRestriction

theorem determinedByLowTypes : DeterminedByLowTypes := GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes

theorem resInj : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj := resInj_of_determined determinedByLowTypes

end GlobalTheory.LowTypeRestriction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorIndicatorMemHecke
section
noncomputable section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem hasDiv_mul_mul {O : Subring L} {d : List ℤ} {g : GL (Fin n) L} (h : HasDiv O d g) {a b : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) O) (hb : b ∈ GLint (Fin n) O) : HasDiv O d (a * g * b) := by
  obtain ⟨ϖ, hϖ, a', ha', b', hb', e⟩ := h
  refine ⟨ϖ, hϖ, a * a', mul_mem ha ha', b' * b, mul_mem hb' hb, ?_⟩
  simp only [Units.val_mul, e, Matrix.mul_assoc]

theorem HasDiv.exists_eq_mul_mul {O : Subring L} (hO : ∀ x : L, Valued.v x ≤ 1 → x ∈ O) {d : List ℤ}
    {g s : GL (Fin n) L} (hg : HasDiv O d g) (hs : HasDiv O d s) :
    ∃ a b : GLint (Fin n) O, g = a * s * b := by
  first
  | exact @_root_.GlobalTheory.DoubleCosetDivisors.main
  | exact _root_.GlobalTheory.DoubleCosetDivisors.main
  | (apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DoubleCosetDivisors.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DoubleCosetDivisors.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DoubleCosetDivisors.main ..)

end Local

end GlobalTheory.SphGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramifiedStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingReducedResidueField_bijective_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), UnramIn E p → Function.Bijective (red io X) := by
  first | exact @GlobalTheory.PrimePart.red_bijective | exact GlobalTheory.PrimePart.red_bijective | (intros; apply GlobalTheory.PrimePart.red_bijective <;> assumption)
end

