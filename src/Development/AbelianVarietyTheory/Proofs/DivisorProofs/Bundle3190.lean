import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3173
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem powAt_coe_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    ((powAt G x k : Ev n) : Alt n) = ∑ i, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) := by
  simp [powAt, Matrix.trace]

theorem transAt_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (x : V n) (k : ℕ) :
    transAt G G' x k = ∑ a, ∑ i ∈ Finset.range k, ∑ p, ∑ q,
      (conn G x (coordVec a) - conn G' x (coordVec a)) p q •
        ((((curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i) q p : Ev n) : Alt n) * dz a) := by
  unfold transAt
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, AddSubmonoidClass.coe_finset_sum,
    Finset.sum_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.smul_def, mul_assoc]

theorem powAt_transAt_smooth : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ k, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((powAt G x k : Alt n)) S) v) ∧ dbarAt (fun x => (powAt G x k : Alt n)) v = 0 ∧ (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (transAt G G' x k) S) v) := by
  intro n r _ _ G G' v hG hGu hG' hG'u k
  obtain ⟨hconst, hsum, hsmul, hmul⟩ := GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v
  obtain ⟨_, hdsum, _, _, _⟩ := GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v
  have hpe : ∀ i, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr
      (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) S) v) ∧
      dbarAt (fun x => (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n)) v = 0 :=
    fun i => GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G G' v hG hGu hG' hG'u k 0 i i
  have hpf : (fun x => ((powAt G x k : Ev n) : Alt n)) =
      fun x => ∑ i ∈ Finset.univ, (((curvEv G x ^ k * curvEv G' x ^ 0) i i : Ev n) : Alt n) :=
    funext fun x => powAt_coe_eq_sum G G' x k
  refine ⟨?_, ?_, ?_⟩
  · simp only [powAt_coe_eq_sum G G']
    exact hsum r Finset.univ _ fun i _ => (hpe i).1
  · rw [hpf, hdsum r Finset.univ _ fun i _ S => ((hpe i).1 S).differentiableAt (by simp)]
    exact Finset.sum_eq_zero fun i _ => (hpe i).2
  · have hη : ∀ a p q, ContDiffAt ℝ ∞
        (fun x => (conn G x (coordVec a) - conn G' x (coordVec a)) p q) v := fun a p q =>
      ((hG.conn hGu (j := ∞) (by simp) (coordVec a)).sub
        (hG'.conn hG'u (j := ∞) (by simp) (coordVec a))) p q
    simp only [transAt_eq_sum]
    refine hsum _ Finset.univ _ fun a _ => hsum _ _ _ fun i _ => hsum _ Finset.univ _ fun p _ =>
      hsum _ Finset.univ _ fun q _ => hsmul _ _ (hη a p q) ?_
    exact hmul _ _ (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1 (hconst (dz a))

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiff
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem trace_mul_mul_eq_sum_entries {R : Type} [CommRing R] {r : Type} [Fintype r] (P M Q : Matrix r r R) :
    (P * M * Q).trace = ∑ p, ∑ q, (Q * P) q p * M p q := by
  rw [Matrix.trace_mul_cycle, Matrix.trace, Finset.sum_comm (f := fun p q => (Q * P) q p * M p q)]
  exact Finset.sum_congr rfl fun q _ => Matrix.mul_apply

theorem dbarAt_transAt (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n)
    (hG : MContDiffAt ∞ G v) (hGu : IsUnit (G v).det) (hG' : MContDiffAt ∞ G' v)
    (hG'u : IsUnit (G' v).det) (k : ℕ) :
    dbarAt (fun x => transAt G G' x k) v = (powAt G v k : Alt n) - powAt G' v k := by
  obtain ⟨_, hsum, hsmul, _, hleib⟩ := GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v
  obtain ⟨sconst, ssum, ssmul, smul⟩ := GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := le_of_eq (by simp)
  have hdiff : ∀ α : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v :=
    fun α h S => (h S).differentiableAt (by simp)
  obtain ⟨W, hW⟩ : ∃ W : ℕ → V n → Matrix r r (Ev n),
      W = fun i x => curvEv G' x ^ (k - 1 - i) * curvEv G x ^ i := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : r → r → V n → Alt n, β = fun p q x =>
      (∑ a, conn G x (coordVec a) p q • dz a) - ∑ a, conn G' x (coordVec a) p q • dz a := ⟨_, rfl⟩

  have hWs : ∀ i p q, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((W i x q p : Ev n) : Alt n) S) v := by
    intro i p q; subst hW; exact (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).1
  have hWc : ∀ i p q, dbarAt (fun x => ((W i x q p : Ev n) : Alt n)) v = 0 := by
    intro i p q; subst hW; exact (GlobalTheory.T.curvatureMatrix_powProduct_entry_smooth_dbarClosed n r G' G v hG' hG'u hG hGu (k - 1 - i) i q p).2

  have hcs : ∀ (H : V n → Matrix r r ℂ), MContDiffAt ∞ H v → IsUnit (H v).det → ∀ p q,
      ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ a, conn H x (coordVec a) p q • dz a) S) v := by
    intro H hH hHu p q
    exact ssum (Fin n) Finset.univ (fun a x => conn H x (coordVec a) p q • dz a) fun a _ =>
      ssmul (fun x => conn H x (coordVec a) p q) (fun _ => dz a)
        (hH.conn hHu hinf (coordVec a) p q) (sconst (dz a))
  have hβs : ∀ p q, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β p q x) S) v := by
    intro p q S; subst hβ
    simpa only [map_sub, Finsupp.sub_apply] using (hcs G hG hGu p q S).sub (hcs G' hG' hG'u p q S)
  have dsub : ∀ α γ : V n → Alt n, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (γ x) S) v) →
      dbarAt (fun x => α x - γ x) v = dbarAt α v - dbarAt γ v := by
    intro α γ hα hγ
    have e : (fun x => α x - γ x) =
        fun x => ∑ j ∈ (Finset.univ : Finset (Fin 2)), (![α, fun y => (-1 : ℂ) • γ y] j) x := by
      funext x; simp [Fin.sum_univ_two, sub_eq_add_neg]
    rw [e, hsum (Fin 2) Finset.univ _ ?_]
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hsmul (-1) γ hγ]
      simp [sub_eq_add_neg]
    · intro j _ S
      fin_cases j
      · exact hα S
      · simpa [map_smul] using (hγ S).const_smul (-1 : ℂ)
  have hdβ : ∀ p q, dbarAt (β p q) v = (curvEv G v p q : Alt n) - curvEv G' v p q := by
    intro p q; subst hβ
    refine (dsub _ _ (hdiff _ (hcs G hG hGu p q)) (hdiff _ (hcs G' hG' hG'u p q))).trans ?_
    rw [GlobalTheory.T.dbar_chernConnection_entry_eq_curvature n r G v hG hGu p q, GlobalTheory.T.dbar_chernConnection_entry_eq_curvature n r G' v hG' hG'u p q]
  have step : ∀ i p q, dbarAt (fun x => ((W i x q p : Ev n) : Alt n) * β p q x) v =
      (W i v q p : Alt n) * ((curvEv G v p q : Alt n) - curvEv G' v p q) := by
    intro i p q
    rw [hleib (fun x => W i x q p) (β p q) (hdiff _ (hWs i p q)) (hdiff _ (hβs p q)), hWc, zero_mul,
      zero_add, hdβ]

  have key : (fun x => transAt G G' x k) =
      fun x => ∑ i ∈ Finset.range k, ∑ p, ∑ q, ((W i x q p : Ev n) : Alt n) * β p q x := by
    funext x
    subst hW hβ
    simp only [transAt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trace_mul_mul_eq_sum_entries, Matrix.map_apply, Matrix.sub_apply, map_sub,
      AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Finset.sum_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub, sub_mul, Subalgebra.coe_sub]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Algebra.smul_def, mul_assoc, mul_sub, sub_mul]

  have alg : ∑ i ∈ Finset.range k, ∑ p, ∑ q, W i v q p * (curvEv G v p q - curvEv G' v p q) =
      powAt G v k - powAt G' v k := by
    refine Eq.trans ?_ (GlobalTheory.T.sum_trace_pow_mul_sub_mul_pow_telescope (Ev n) r (curvEv G v) (curvEv G' v) k)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.trace_mul_cycle, Matrix.trace, Finset.sum_comm, hW]
    exact Finset.sum_congr rfl fun q _ => by rw [Matrix.diag_apply, Matrix.mul_apply]; rfl
  rw [key]
  refine (hsum _ _ _ ?_).trans ?_
  · intro i _
    exact hdiff _ (ssum r Finset.univ _ fun p _ => ssum r Finset.univ _ fun q _ =>
      smul _ _ (hWs i p q) (hβs p q))
  have inner : ∀ i, dbarAt (fun x => ∑ p, ∑ q, ((W i x q p : Ev n) : Alt n) * β p q x) v =
      ∑ p, ∑ q, (W i v q p : Alt n) * ((curvEv G v p q : Alt n) - curvEv G' v p q) := by
    intro i
    refine (hsum _ _ _ ?_).trans (Finset.sum_congr rfl fun p _ => ?_)
    · intro p _
      exact hdiff _ (ssum r Finset.univ _ fun q _ => smul _ _ (hWs i p q) (hβs p q))
    refine (hsum _ _ _ ?_).trans (Finset.sum_congr rfl fun q _ => step i p q)
    intro q _
    exact hdiff _ (smul _ _ (hWs i p q) (hβs p q))
  rw [Finset.sum_congr rfl fun i _ => inner i]
  have := congrArg (fun w : Ev n => (w : Alt n)) alg
  simpa only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_mul, Subalgebra.coe_sub] using this

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCaseCuspFormFibreSlopeGeBound
section
noncomputable section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefFibre

theorem vAdd_pow' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) (n : ℕ) :
    vAdd w (x ^ n) = n * vAdd w x := by
  simp [vAdd, map_pow, WithZero.log_pow]

theorem vAdd_one' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : vAdd w (1 : K) = 0 := by
  simp [vAdd]

theorem subsingleton_idx : ∀ (N : ℕ) (la : Fin N → ℕ), N = 0 → Subsingleton (Idx la) := by
  rintro N la rfl
  constructor
  rintro ⟨m, -⟩ ⟨m', -⟩
  congr 1
  ext ⟨i, _⟩
  exact i.elim0

theorem dim_eq_one_of_zero {N : ℕ} (la : Fin N → ℕ) (hla : Antitone la) (h : N = 0) : dim la = 1 := by
  haveI := subsingleton_idx N la h
  have h1 := dim_pos hla
  have h2 : dim la ≤ 1 := by rw [dim_eq_card]; exact Fintype.card_le_one_iff_subsingleton.2 inferInstance
  omega

theorem fibreAt_defCase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Dom a n → FlatExistsAt U ξ c₁ →
      ∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) (defBound Dw a n c₁) := by
  intro E _ _ _ H Dw l Xo c r U ξ a n c₁ hD hDom hFl Z
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_definiteRationalPointData_component E H Dw l Xo c r U ξ hD Z
  haveI hTC : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hanti : ∀ τ, Antitone (part Dw a τ) := fun τ i j hij => hDom.1 τ (show (i : ℕ) ≤ j from hij)
  obtain ⟨φ, hinj, hrange, hreads⟩ := GlobalTheory.T.exists_injective_dualWeylTensor_cuspForms_rationalPoint E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hconj, hint⟩ := GlobalTheory.T.integral_coordinates_forms_and_fibre_norm_bound E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hlie, -⟩ := GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree E H Dw l Xo c r U ξ hD Z P
  have hth := GlobalTheory.T.thetaLine_degree_ge_half_detLie_definitePoint E H Dw l Xo c r U ξ hD Z P
  have hIntOne : ∀ (w : HeightOneSpectrum (𝓞 c.F)) (m : ℕ), IntAt w (1 : Matrix (Fin m) (Fin m) c.F) :=
    fun w m i j => by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hBad : ∀ τ, IsAdelic fun w => P.B w τ := fun τ => by
    refine ⟨fun w => (P.loc w).2.1 τ, P.fin.subset fun w hw h => hw ?_⟩
    show IntAt w (P.B w τ) ∧ IntAt w (P.B w τ)⁻¹
    have hB : P.B w τ = 1 := by rw [h.2]; rfl
    rw [hB, inv_one]
    exact ⟨hIntOne w _, hIntOne w _⟩
  have ha0 : ∀ w, P.a w ^ n ≠ 0 := fun w => pow_ne_zero _ (P.loc w).1
  have hsupp1 : (Function.support fun w => vAdd w (P.a w)).Finite :=
    P.fin.subset fun w hw h => hw (by simp only; rw [h.1, vAdd_one'])
  have hsupp : (Function.support fun w => vAdd w (P.a w ^ n)).Finite :=
    hsupp1.subset fun w hw h => hw (by simp only at h ⊢; rw [vAdd_pow', h, mul_zero])
  have hspos : ∀ σ, 0 < (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ =>
    pow_pos (inv_pos.2 (Real.sqrt_pos.2 (P.arch σ).1)) n
  have hsconj : ∀ σ, (Real.sqrt (P.N ((starRingEnd ℂ).comp σ)))⁻¹ ^ n = (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ => by
    rw [(hconj σ).1]
  obtain ⟨hdet, hslope⟩ := GlobalTheory.T.slope_dualWeylFibreLattice_ge c.F (E →+* ℂ) Dw.mult (part Dw a) hanti (fun w => P.a w ^ n) P.B
    (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) P.X ha0 hsupp hBad hspos (fun σ τ => (P.arch σ).2.1 τ) hsconj
    (fun σ τ => (hconj σ).2 τ)
  have hlat : IsAdelic fun w => fibA (part Dw a) (P.a w ^ n) (P.B w) :=
    GlobalTheory.T.fibre_action_preserves_adelic_matrices c.F (E →+* ℂ) Dw.mult (part Dw a) (fun w => P.a w ^ n) P.B ha0 hsupp hBad
  have hsec : ∀ x, φ x ∈ sec Xo c a n := fun x => by
    have h1 : φ x ∈ cuspOn U Z (wtZ a n) := hrange ▸ ⟨x, rfl⟩
    have h2 := cuspOn_le U Z (wtZ a n) h1
    rw [cuspW_wtZ] at h2
    exact cusp_le_sec Xo c U a n h2
  have hne : ∀ τ, Nonempty (Idx (part Dw a τ)) := fun τ =>
    Fintype.card_pos_iff.1 ((dim_eq_card _) ▸ dim_pos (hanti τ))

  have hline : lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) (fun w => (vAdd w (P.a w ^ n) : ℝ)) = n * P.degTh := by
    simp only [PtData.degTh, lineDeg, vAdd_pow', Int.cast_mul, Int.cast_natCast, Real.log_pow]
    have hf := fin_mul (ρ := fun w => (vAdd w (P.a w) : ℝ)) (hsupp1.subset fun w hw => by simpa [Function.mem_support] using hw) (lw c.F)
    simp only [mul_assoc]
    rw [← mul_finsum, ← Finset.mul_sum]
    ring

  have hterm : ∀ τ : E →+* ℂ, ¬ τ (H.rt : E) = H.rt0 →
      (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2 = 0 := fun τ hτ => by
    have hm : Dw.mult τ = 0 := by simp [Datum.mult, hτ, hD.q]
    have hm' : (Dw.mult τ : ℝ) = 0 := by rw [hm]; simp
    rw [dim_eq_one_of_zero _ (hanti τ) hm, hm', div_zero, zero_mul]
    simp
  have hpsi : ∀ τ : Psi H,
      (size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) * detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) -
        Real.log (dim (part Dw a τ.1)) / 2 =
      (size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2 := fun τ => by
    have hm : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]
    have hl : P.degLie τ.1 = c₁ := by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]
    have hm' : (Dw.mult τ.1 : ℝ) = Dw.p := by rw [hm]
    rw [hm', show detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) = P.degLie τ.1 from rfl, hl]
  have hsum := (Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
    (fun τ => (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2)).symm
  have h0 : ∑ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) = 0 :=
    Finset.sum_eq_zero fun τ _ => hterm τ.1 τ.2
  rw [h0, add_zero] at hsum
  have hsum' : ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) :=
    Finset.sum_congr rfl fun τ _ => hpsi τ
  have hlieSum : ∑ τ : Psi H, P.degLie τ.1 = (Fintype.card (Psi H) : ℝ) * c₁ := by
    rw [Finset.sum_congr rfl fun τ _ => (show P.degLie τ.1 = c₁ by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbound : defBound Dw a n c₁ = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
      Real.log (dim (part Dw a τ.1)) / 2) + (Fintype.card (Psi H) : ℝ) * ((n : ℝ) / 2 * c₁) +
      (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) := by
    have hS : ∑ τ : Psi H, ((((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) + (n : ℝ) / 2) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2)) = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2) + ∑ _τ : Psi H, ((n : ℝ) / 2 * c₁) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [defBound, hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left hth hn
  rw [hlieSum] at hmul
  refine ⟨TIdx (part Dw a), inferInstance, inferInstance, ⟨fun τ => (hne τ).some⟩, locLat (P.matA a n), P.matY a n, φ,
    GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily c.F _ (P.matA a n) hlat, hdet, ?_, hinj, hrange, fun x hx w v hv =>
      (hint x (φ x) (hsec x) (hreads x)).1 hx w v hv, fun σ x z hz => (hint x (φ x) (hsec x) (hreads x)).2 σ z hz⟩
  refine le_trans ?_ hslope
  have htot : ∑ t : E →+* ℂ, ((size (part Dw a t) : ℝ) / (Dw.mult t : ℝ) *
      detDeg (fun w => P.B w t) (fun σ => P.X σ t) - Real.log (dim (part Dw a t)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) := by
    rw [hsum]
    convert hsum' using 3
  rw [hline, htot, hbound]
  nlinarith [hmul]

end GlobalTheory.DefFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyAddOrdGtNegOneLogResolutionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrepancy_add_ord_gt_neg_one_log_resolution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (g f : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y), η ≠ 0 → 0 < m → IsLogRes p n η m (CartierDiv.principal g) s K B → (∀ y', s y' ∈ (CartierDiv.principal f).supp → y' ∈ B) → RegAt y (f : X.functionField) → Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → (∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m) → ∀ E : DivOver p, E.Through y → -1 < discrep E η m g + E.ord f := by
  first | exact @GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes | exact GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes | (intros; apply GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantProjArithSurjectiveComplexPointsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_projArith_surjective_complexPoints : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (E : ℕ), IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map π hπ (spMap σ) : CxPts q σ → CxPts p σ) := by
  first | exact @GlobalTheory.DomSurj.surjective_cxPts_map | exact GlobalTheory.DomSurj.surjective_cxPts_map | (intros; apply GlobalTheory.DomSurj.surjective_cxPts_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8MumfordBundlePowerSectionNonvanishingClosedFib
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem thetaNZ_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → GlobalTheory.LN.ThetaNZ (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W) := by
  intro hL hL2 hE V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  have hB : GlobalTheory.Mum.Base V₁ := by
    obtain ⟨h1, h2, h3, h4⟩ := hCN
    exact ⟨⟨h1, inferInstance, h2, h3⟩, h4⟩
  obtain ⟨Pc, hPc, hEv⟩ := GlobalTheory.T.exists_cubical_e8LB_evenOn hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  obtain ⟨A, gen, hgen, hA⟩ := GlobalTheory.T.exists_polAV_generic_fibre_e8LB hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D, U, hU, -⟩ := GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal V₁ hB _ Pc hS8 hEv A gen hgen (hPc ▸ hA)
  have h := GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section V₁ hB D A _ U (hU ▸ hEv)
  rw [hU, hPc] at h
  exact h

end GlobalTheory.PowE8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfPairingVanishes
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_pairing_vanishes : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D), (∀ v, (D.EF.baseChange ℚ).baseChange (AfP p) v z = 0) → z = 0 := by
  first | (exact @GlobalTheory.LKGeo.nondeg_afP) | (exact GlobalTheory.LKGeo.nondeg_afP) | (intros; apply GlobalTheory.LKGeo.nondeg_afP  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleBigCellCoordinatesFlagSpaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_bigCellCoordinates_flagSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)).Etale := by
  first | exact @GlobalTheory.CellEtale.etale_cellCoord | exact GlobalTheory.CellEtale.etale_cellCoord | (intros; apply GlobalTheory.CellEtale.etale_cellCoord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualRowsOfClassSumsStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventual_rows_of_class_sums : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel Ind.Part 𝒜), AtAll Ind.PPA 𝒜 τ → AtAll Ind.PDiv 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : Ind.Part D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.Ties) 𝒜 τ → Ind.EvW Ind.PRows 𝒜 τ := by
  first | exact @GlobalTheory.Fc.Ind.evW_pRows_of_rows | exact GlobalTheory.Fc.Ind.evW_pRows_of_rows | (intros; apply GlobalTheory.Fc.Ind.evW_pRows_of_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPowMulMemHermPairSectionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_pow_mul_mem_hermPairSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e a b : ℤ) (x f : X.functionField), x ∈ P.H e 0 → x ≠ 0 → (∀ z ∈ NV P e 0 x, ∀ i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j → RegAt z (P.loc a b f i j)) → ∀ᶠ c : ℕ in atTop, x ^ c * f ∈ P.H (e * c + a) b := by
  first | exact @GlobalTheory.HSAmp.eventually_pow_mul_mem_H | exact GlobalTheory.HSAmp.eventually_pow_mul_mem_H | (intros; apply GlobalTheory.HSAmp.eventually_pow_mul_mem_H <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySurjectiveToPushforwardAmpleLineBundleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i], ∀ᶠ N in atTop, Function.Surjective ((GlobalTheory.LB.toPushforward (lbPow L N) i).app ⊤) := by
  first | exact @GlobalTheory.surjective_toPushforward_app_top_lbPow | exact GlobalTheory.surjective_toPushforward_app_top_lbPow | (intros; apply GlobalTheory.surjective_toPushforward_app_top_lbPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_sectionValueUnitFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ ℓ : P.H a b →+ ℂ, ∀ f : P.H a b, ℓ f = val P a b σ y f := by
  first | exact @GlobalTheory.HSAmp.val_additive | exact GlobalTheory.HSAmp.val_additive | (intros; apply GlobalTheory.HSAmp.val_additive <;> assumption)
end

