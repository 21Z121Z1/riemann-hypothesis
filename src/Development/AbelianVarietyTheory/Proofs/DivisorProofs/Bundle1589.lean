import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartMapIntoAffineConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Polynomial in

theorem poly_eq_C_of_eq_aeval_invSelf {K : Type} [CommRing K] (p q : K[X])
    (h : algebraMap K[X] (Localization.Away (X : K[X])) p =
      aeval (IsLocalization.Away.invSelf (X : K[X]) : Localization.Away (X : K[X])) q) :
    p = C (p.eval 0) := by
  set L := Localization.Away (X : K[X])
  set n := q.natDegree
  letI : Invertible (algebraMap K[X] L X) :=
    ⟨IsLocalization.Away.invSelf (X : K[X]),
      by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf _, IsLocalization.Away.mul_invSelf _⟩
  have hr : (q.reflect n).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
  have key := eval₂_reflect_mul_pow (algebraMap K L) (algebraMap K[X] L X) n (q.reflect n) hr
  rw [reflect_reflect] at key
  have hev : ∀ r : K[X], eval₂ (algebraMap K L) (algebraMap K[X] L X) r = algebraMap K[X] L r :=
    fun r => eval₂_algebraMap_X r (IsScalarTower.toAlgHom K K[X] L)
  have h2 : algebraMap K[X] L (p * X ^ n) = algebraMap K[X] L (q.reflect n) := by
    rw [map_mul, map_pow, h, aeval_def, ← hev (q.reflect n)]
    exact key
  have hinj : Function.Injective (algebraMap K[X] L) :=
    IsLocalization.injective L (Submonoid.powers_le.2 X_mem_nonzeroDivisors)
  have h3 := hinj h2
  have hdeg : (p * X ^ n).natDegree ≤ n := h3 ▸ hr
  have hp0 : p.natDegree = 0 := by
    by_cases hp : p = 0
    · simp [hp]
    have hc : (p * X ^ n).coeff (p.natDegree + n) ≠ 0 := by
      rw [coeff_mul_X_pow]; exact mt leadingCoeff_eq_zero.mp hp
    have := le_natDegree_of_ne_zero hc
    omega
  rw [← coeff_zero_eq_eval_zero]
  exact eq_C_of_natDegree_eq_zero hp0

end GlobalTheory

namespace GlobalTheory

theorem chart_map_into_affine_const (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens)
    (hW : IsAffineOpen W) (g₀ g₁ : Sp (Polynomial K) ⟶ Y) (h₀ : ∀ x, g₀ x ∈ W) (h₁ : ∀ x, g₁ x ∈ W)
    (h : spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) :
        Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁) :
    g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  haveI := hW.isOpenImmersion_fromSpec
  have r₀ : Set.range g₀.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₀ x
  have r₁ : Set.range g₁.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₁ x
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₀ r₀)
  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₁ r₁)
  have e₀ : Spec.map φ₀ ≫ hW.fromSpec = g₀ := by rw [hφ₀]; exact IsOpenImmersion.lift_fac _ _ _
  have e₁ : Spec.map φ₁ ≫ hW.fromSpec = g₁ := by rw [hφ₁]; exact IsOpenImmersion.lift_fac _ _ _
  rw [← e₀, ← e₁] at h
  simp only [spMap, ← Category.assoc, ← Spec.map_comp, cancel_mono] at h
  rw [Spec.map_inj] at h
  have key : ∀ a, φ₀ a = Polynomial.C ((φ₀ a).eval 0) := fun a =>
    poly_eq_C_of_eq_aeval_invSelf (φ₀ a) (φ₁ a) (congrArg (fun f => f.hom a) h)
  rw [← e₀]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact key a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

theorem cHess_apply_eq_ddbar {n : ℕ} {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hg : ContDiffAt ℝ 2 g x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.cHess n g x j k =
      ddbar g x (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
  have e : ReciprocityTheory.L2DbarEstimates.wdb n k g = fun y => dbar g y (EuclideanSpace.single k 1) := by
    funext y
    simp only [ReciprocityTheory.L2DbarEstimates.wdb, dbar_apply, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
    ring
  rw [ddbar_eq_del_dbar hg, del_apply, ReciprocityTheory.L2DbarEstimates.cHess, Matrix.of_apply, e]
  simp only [ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
  ring

end GlobalTheory.CurveDens

namespace GlobalTheory.CurveDens

theorem chernDens_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ),
    (∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → IsDens fun (c : AlgChart p σ 1) y => c.chernDens φ y) ∧
    ∀ (L : X.Modules) (g : Met p σ L 1), g.IsCInf → ∀ (U : X.Opens) (t : Γ(L, U)),
      IsFrame (fun _ : Fin 1 => t) → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ ptsIn p σ U →
        c.chernDens g.detWeight y = -(leviForm (fun v => Real.log (g.form t t (c.e.symm v)).re) (c.e y)
          (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)).re / Real.pi := by
  intro k _ X p σ
  refine ⟨fun B φ hφ => ⟨fun c c' y hy hy' => c.chernDens_trans c' hφ hy hy', fun c v hv => ?_⟩, ?_⟩
  · have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (pick φ.isLB (c.e.symm v))))
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v))) :=
      ⟨hv, mem_pick φ.isLB _⟩
    have hs : ContDiffOn ℝ ∞ (fun w => ((φ.φ (pick φ.isLB (c.e.symm v)) (c.e.symm w) : ℝ) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U (pick φ.isLB (c.e.symm v)))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart (hφ _) c)
    have hc := ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb ho hs 0 0
    refine ContinuousAt.continuousWithinAt ?_
    refine ((continuous_const.mul Complex.continuous_re).continuousAt.comp
      (hc.continuousAt (ho.mem_nhds hm)) (f := fun w => ReciprocityTheory.L2DbarEstimates.wd 1 0 (ReciprocityTheory.L2DbarEstimates.wdb 1 0 _) w)
      (g := fun z : ℂ => (Nat.factorial 1 : ℝ) / Real.pi ^ 1 * z.re)).congr ?_
    filter_upwards [ho.mem_nhds hm] with w hw
    rw [Function.comp_apply, c.chernDens_eq hφ (c.e.map_target hw.1) hw.2, AlgChart.hess,
      c.e.right_inv hw.1, Matrix.det_unique]
    rfl
  · intro L g hg U t ht c y hy hU
    let c₀ : VB.Chart L 1 := ⟨U, fun _ => t, ht⟩
    have hi : y ∈ ptsIn p σ ((det L 1).U c₀) := hU
    rw [c.chernDens_eq hg.detWeight hy hi]
    simp only [AlgChart.hess, Matrix.det_unique]
    have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
    have hm := ChartGlue.mem_over c.e hy hU
    have e : (fun v => ((g.detWeight.φ c₀ (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
        fun v => -((Real.log (g.form t t (c.e.symm v)).re : ℝ) : ℂ) := by
      filter_upwards [ho.mem_nhds hm] with v hv
      rw [← Complex.ofReal_neg]
      congr 1
      show -Real.log (g.G c₀ (c.e.symm v)).det.re = -Real.log (g.form t t (c.e.symm v)).re
      rw [Matrix.det_unique, ← g.form_frame c₀ hv.2]
    have hd : ContDiffAt ℝ 2 (fun v => g.detWeight.φ c₀ (c.e.symm v)) (c.e y) :=
      hg.detWeight.contDiffAt c hy hi
    have hu := (contDiffAt_ofReal_comp hd).congr_of_eventuallyEq e.symm
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, cHess_apply_eq_ddbar hu]
    erw [ddbar_neg]
    simp only [leviForm, Nat.factorial_one, Nat.cast_one, pow_one, Fin.default_eq_zero]
    simp only [ContinuousLinearMap.neg_apply, Complex.neg_re]
    ring

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChange
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm

theorem chernAt_changeFrame : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H K A : V n → Matrix r r ℂ) (v : V n), MContDiffAt 2 K v → IsUnit (K v).det → (∀ i j, AnalyticAt ℂ (fun w => A w i j) v) → IsUnit (A v).det → (H =ᶠ[𝓝 v] fun w => chg (A w) (K w)) → ∀ j, chernAt H v j = chernAt K v j := by
  intro n r _ _ H K A v hK hKu hg hAu hH j
  have hconj : ∀ (M P Q : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)), Q * P = 1 →
      (Q * M * P).charpolyRev = M.charpolyRev := by
    intro M P Q hQP
    have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
      rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
    have e : (1 : Matrix r r (Polynomial (MvPolynomial (Fin n × Fin n) ℂ))) -
        (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) • (Q * M * P).map Polynomial.C =
        Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) •
          M.map Polynomial.C) * P.map Polynomial.C := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
        Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
      ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]
  have hsum : ∀ G : V n → Matrix r r ℂ, curvPoly G v =
      ∑ a, ∑ b, (MvPolynomial.X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
        (curv G v (coordVec a) (coordVec b)).map MvPolynomial.C := by
    intro G
    ext i j
    simp [curvPoly, Matrix.sum_apply, mul_comm]
  have hA : MContDiffAt 2 A v := fun a b => (hg a b).contDiffAt.restrict_scalars ℝ
  have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
    have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => A w a b) x :=
      eventually_all.2 fun a => eventually_all.2 fun b => (hg a b).eventually_analyticAt
    filter_upwards [hev] with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b).differentiableAt]
    rfl
  have hGe : H =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u * (A u)ᴴᵀ := hH
  have hcurv : ∀ ξ η, curv H v ξ η = (A v)⁻¹ * curv K v ξ η * A v :=
    fun ξ η => by rw [curv_congr hGe, curv_changeFrame hK hKu hA hAu hA0]
  have key : curvPoly H v = ((A v)⁻¹).map MvPolynomial.C * curvPoly K v * (A v).map MvPolynomial.C := by
    rw [hsum, hsum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
  have key2 : chernPoly H v j = chernPoly K v j := by
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)),
      -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], hconj]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [chernAt, chernAt, key2]

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.FormMul

variable {n : ℕ}

theorem repr_mul (a b : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (a * b) S = ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr a p.1 * (bas n).repr b p.2 * (bas n).repr (bas n p.1 * bas n p.2) S := by
  conv_lhs => rw [← (bas n).sum_repr a, ← (bas n).sum_repr b]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_coefwise (T : (V n → ℂ) → ℂ) (H : V n → Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (coefwise T H) S = T (fun x => (bas n).repr (H x) S) := by
  simp [coefwise, map_sum, Finsupp.single_apply]

theorem coefwise_mul {v : V n} {T : (V n → ℂ) → ℂ}
    (hsum : ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T (fun x => ∑ p, f p x) = ∑ p, T (f p))
    (hmul : ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T (fun x => f x * g x) = f v * T g + T f * g v)
    (hconst : ∀ c : ℂ, T (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    coefwise T (fun x => F x * G x) = coefwise T F * G v + F v * coefwise T G := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (F x * G x) S) = fun x => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
      (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
    funext fun x => repr_mul _ _ _
  rw [repr_coefwise, e, map_add, Finsupp.add_apply, repr_mul (coefwise T F), repr_mul (F v)]
  simp only [repr_coefwise]
  rw [hsum (fun p x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S)
    (fun p => ((hF p.1).mul (hG p.2)).mul (differentiableAt_const _)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hmul (fun x => (bas n).repr (F x) p.1 * (bas n).repr (G x) p.2) (fun _ => (bas n).repr (bas n p.1 * bas n p.2) S)
    ((hF p.1).mul (hG p.2)) (differentiableAt_const _), hconst,
    hmul (fun x => (bas n).repr (F x) p.1) (fun x => (bas n).repr (G x) p.2) (hF p.1) (hG p.2)]
  ring

theorem exists_ι_mul (y : Alt n) : ∃ y' : Alt n, ∀ m, ExteriorAlgebra.ι ℂ m * y = y' * ExteriorAlgebra.ι ℂ m := by
  induction y using ExteriorAlgebra.induction with
  | algebraMap r => exact ⟨algebraMap ℂ _ r, fun m => (Algebra.commutes r _).symm⟩
  | ι x => exact ⟨-ExteriorAlgebra.ι ℂ x, fun m => by
      rw [neg_mul]; exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap m x)⟩
  | mul a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' * b', fun m => by rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]⟩
  | add a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' + b', fun m => by rw [mul_add, ha, hb, add_mul]⟩

theorem sum_mul_leibniz {v : V n} (g : Fin n → (Fin n ⊕ Fin n → ℂ)) (T : Fin n → (V n → ℂ) → ℂ)
    (hsum : ∀ a, ∀ f : Finset (Fin (n + n)) × Finset (Fin (n + n)) → V n → ℂ, (∀ p, DifferentiableAt ℝ (f p) v) →
      T a (fun x => ∑ p, f p x) = ∑ p, T a (f p))
    (hmul : ∀ a, ∀ f g : V n → ℂ, DifferentiableAt ℝ f v → DifferentiableAt ℝ g v →
      T a (fun x => f x * g x) = f v * T a g + T a f * g v)
    (hconst : ∀ a, ∀ c : ℂ, T a (fun _ => c) = 0)
    {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      (∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F) * G v +
        y * ∑ a, ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G := by
  obtain ⟨y, hy⟩ := exists_ι_mul (F v)
  refine ⟨y, ?_⟩
  have h (a : Fin n) : ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) (fun x => F x * G x) =
      ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) F * G v + y * (ExteriorAlgebra.ι ℂ (g a) * coefwise (T a) G) := by
    simp only [coefwise_mul (hsum a) (hmul a) (hconst a) hF hG, mul_add, ← mul_assoc, hy]
  rw [Finset.sum_congr rfl fun a _ => h a, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

theorem delAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, delAt (fun x => F x * G x) v = delAt F v * G v + y * delAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inl a) 1) (fun a f => del f v (coordVec a))
    (fun a f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => del_mul hf hg _) (fun a c => by rw [del_const]; rfl) hF hG

theorem dbarAt_mul {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    ∃ y : Alt n, dbarAt (fun x => F x * G x) v = dbarAt F v * G v + y * dbarAt G v :=
  sum_mul_leibniz (fun a => Pi.single (.inr a) 1) (fun a f => dbar f v (coordVec a))
    (fun a f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
    (fun a f g hf hg => dbar_mul hf hg _) (fun a c => by rw [dbar_const]; rfl) hF hG

variable {M : Type} [TopologicalSpace M]

theorem loc_mul (A : HolAtlas M n) (α β : A.Fld) (i : A.ι) (v : V n) :
    A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  unfold HolAtlas.loc
  split_ifs
  · rfl
  · simp

theorem differentiableAt_coef {A : HolAtlas M n} {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt
    (by simp)

end GlobalTheory.CxForm.FormMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFr
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.CuspCocpt
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem cocompact_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X S) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S
  by_cases hS0 : S = ∅
  · subst hS0
    rw [unip_empty]
    refine ⟨Set.univ, ?_, fun u => ⟨1, Subgroup.one_mem _, Set.mem_univ _⟩⟩
    exact Set.Subsingleton.isCompact fun a _ b _ => Subsingleton.elim a b
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hσ := sigma_sigma h
  have hs : m.val + 1 ≤ r := m.2
  have hS : ∀ i : Fin r, i.val < m.val + 1 ↔ ∃ k ∈ S, i ≤ k := fun i =>
    ⟨fun hi => ⟨m, hm, Fin.le_def.2 (Nat.lt_succ_iff.1 hi)⟩,
      fun ⟨k, hk, hik⟩ => Nat.lt_succ_iff.2 (le_trans (Fin.le_def.1 hik) (Fin.le_def.1 (hm' k hk)))⟩
  have e := (GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (m.val + 1) hs hS
    (fun i => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl).1
  have hC : IsIsoCols σ J (X.submatrix id (Fin.castLE hs)) := isIsoCols_of_isWittFrame hW hσ hJ hs
  exact e ▸ cocompact_unipFlag hJ hσ hC _

end GlobalTheory.CuspCocpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOffOpenFiniteStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_off_open_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ U : X.Opens, genericPoint X ∈ U → ∀ σ : k →+* ℂ, (ptsIn p σ U)ᶜ.Finite := by
  first | exact @GlobalTheory.SurfacePoints.finite_compl_ptsIn | exact GlobalTheory.SurfacePoints.finite_compl_ptsIn | (intros; apply GlobalTheory.SurfacePoints.finite_compl_ptsIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtDelApply
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveDens
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem angleForm_smul (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E) (c : ℂ) :
    angleForm n a a' q (c • ξ) z = c * angleForm n a a' q ξ z := by
  simp only [angleForm, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smulₛₗ, smul_eq_mul,
    map_sub, map_mul, Complex.conj_conj, RingHom.id_apply]
  ring

theorem contDiffAt_del_apply {q : E → ℂ} {z : E} (hq : ContDiffAt ℝ 2 q z) (ξ : E) :
    ContDiffAt ℝ 1 (fun x => del q x ξ) z ∧ ContDiffAt ℝ 1 (fun x => dbar q x ξ) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ q) z := hq.fderiv_right (by norm_num)
  have hv : ∀ w : E, ContDiffAt ℝ 1 (fun x => fderiv ℝ q x w) z := fun w =>
    h1.clm_apply contDiffAt_const
  constructor
  · simp only [del_apply, smul_eq_mul]
    exact contDiffAt_const.mul ((hv ξ).sub (contDiffAt_const.mul (hv _)))
  · simp only [dbar_apply, smul_eq_mul]
    exact contDiffAt_const.mul ((hv ξ).add (contDiffAt_const.mul (hv _)))

theorem contDiffAt_angleForm (n : ℕ) {a a' : E → ℝ} {q : E → ℂ} (ξ : E) {z : E}
    (ha : ContDiffAt ℝ 2 a z) (ha' : ContDiffAt ℝ 2 a' z) (hq : ContDiffAt ℝ 2 q z)
    (h0 : 0 < a z) (h0' : 0 < a' z) : ContDiffAt ℝ 1 (angleForm n a a' q ξ) z := by
  have hla : ContDiffAt ℝ 2 (fun x => (Real.log (a x) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (ha.log h0.ne')
  have hla' : ContDiffAt ℝ 2 (fun x => (Real.log (a' x) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (ha'.log h0'.ne')
  have hq1 : ContDiffAt ℝ 1 q z := hq.of_le (by norm_num)
  have hA : ContDiffAt ℝ 1 (fun x => a x * a' x) z := (ha.mul ha').of_le (by norm_num)
  have hA0 : a z * a' z ≠ 0 := (mul_pos h0 h0').ne'
  have hN : ContDiffAt ℝ 1 (fun x => ‖q x‖ ^ 2) z := hq1.norm_sq ℝ
  have hR : ContDiffAt ℝ 1 (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z ((hN.div hA hA0).pow n)
  have hD : ContDiffAt ℝ 1 (fun x => ((a x * a' x : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hA
  have hconj : ∀ {f : E → ℂ}, ContDiffAt ℝ 1 f z →
      ContDiffAt ℝ 1 (fun x => starRingEnd ℂ (f x)) z :=
    fun hf => Complex.conjCLE.contDiff.contDiffAt.comp z hf
  have e1 := contDiffAt_del_apply hq ξ
  have e2 := contDiffAt_del_apply hla ξ
  have e3 := contDiffAt_del_apply hla' ξ
  have hD0 : ((a z * a' z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA0
  have key : ContDiffAt ℝ 1 (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ) *
      (starRingEnd ℂ (q x) * (del q x ξ - q x * del (fun x => (Real.log (a' x) : ℂ)) x ξ) -
        q x * starRingEnd ℂ (dbar q x ξ - q x * dbar (fun x => (Real.log (a x) : ℂ)) x ξ)) *
      (((a x * a' x : ℝ) : ℂ))⁻¹) z :=
    (hR.mul (((hconj hq1).mul (e1.1.sub (hq1.mul e3.1))).sub
      (hq1.mul (hconj (e1.2.sub (hq1.mul e2.2)))))).mul (hD.inv hD0)
  unfold angleForm
  simpa only [div_eq_mul_inv] using key

theorem angleForm_comp_holo (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E) (φ : E → E)
    (hφ : DifferentiableAt ℂ φ z) (ha : DifferentiableAt ℝ a (φ z))
    (ha' : DifferentiableAt ℝ a' (φ z)) (hq : DifferentiableAt ℝ q (φ z))
    (h0 : 0 < a (φ z)) (h0' : 0 < a' (φ z)) :
    angleForm n (fun x => a (φ x)) (fun x => a' (φ x)) (fun x => q (φ x)) ξ z =
      angleForm n a a' q (fderiv ℂ φ z ξ) (φ z) := by
  have hla : DifferentiableAt ℝ (fun y => (Real.log (a y) : ℂ)) (φ z) :=
    Complex.ofRealCLM.differentiableAt.comp _ (ha.log h0.ne')
  have hla' : DifferentiableAt ℝ (fun y => (Real.log (a' y) : ℂ)) (φ z) :=
    Complex.ofRealCLM.differentiableAt.comp _ (ha'.log h0'.ne')
  unfold angleForm
  rw [del_comp_holo (u := q) hq hφ, dbar_comp_holo (u := q) hq hφ,
    del_comp_holo (u := fun y => (Real.log (a' y) : ℂ)) hla' hφ,
    dbar_comp_holo (u := fun y => (Real.log (a y) : ℂ)) hla hφ]

theorem angleForm_props : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E), (∀ c : ℂ, angleForm n a a' q (c • ξ) z = c * angleForm n a a' q ξ z) ∧ (ContDiffAt ℝ 2 a z → ContDiffAt ℝ 2 a' z → ContDiffAt ℝ 2 q z → 0 < a z → 0 < a' z → ContDiffAt ℝ 1 (angleForm n a a' q ξ) z) ∧ ∀ φ : E → E, DifferentiableAt ℂ φ z → DifferentiableAt ℝ a (φ z) → DifferentiableAt ℝ a' (φ z) → DifferentiableAt ℝ q (φ z) → 0 < a (φ z) → 0 < a' (φ z) → angleForm n (fun x => a (φ x)) (fun x => a' (φ x)) (fun x => q (φ x)) ξ z = angleForm n a a' q (fderiv ℂ φ z ξ) (φ z) :=
  fun _ _ _ _ _ n a a' q ξ z => ⟨angleForm_smul n a a' q ξ z,
    fun ha ha' hq h0 h0' => contDiffAt_angleForm n ξ ha ha' hq h0 h0',
    fun φ hφ ha ha' hq h0 h0' => angleForm_comp_holo n a a' q ξ z φ hφ ha ha' hq h0 h0'⟩

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnDbarCoefficients
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem contDiffOn_dbar_const_dir {n : ℕ} {f : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (w : V n) : ContDiffOn ℝ ∞ (fun v => GlobalTheory.dbar f v w) U := by
  have h : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  simp only [GlobalTheory.dbar_apply]
  exact ContDiffOn.const_smul _ ((h.clm_apply contDiffOn_const).add
    (ContDiffOn.const_smul _ (h.clm_apply contDiffOn_const)))

theorem contDiffOn_repr_dbarAt {n : ℕ} {γ : V n → Alt n} {U : Set (V n)} (hU : IsOpen U)
    (hγ : ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (γ v) S) U) (T : Finset (Fin (n + n))) :
    ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt γ v) T) U := by
  have key : (fun v => (bas n).repr (dbarAt γ v) T) = fun v => ∑ a, ∑ S,
      GlobalTheory.dbar (fun x => (bas n).repr (γ x) S) v (coordVec a) * (bas n).repr (dzb a * bas n S) T := by
    funext v
    simp only [dbarAt, coefwise, map_sum, Finset.mul_sum, mul_smul_comm, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [key]
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ =>
    (contDiffOn_dbar_const_dir hU (hγ S) _).mul contDiffOn_const

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteFreeAlgebraAffineExistsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.hilbertScheme_exists) | (exact GlobalTheory.HilbAff.hilbertScheme_exists) | (intros; apply GlobalTheory.HilbAff.hilbertScheme_exists <;> assumption)
end

