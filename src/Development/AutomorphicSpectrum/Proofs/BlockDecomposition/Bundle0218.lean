import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0182
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0184
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0187
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0199
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.FcCalc.Ibp

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open GlobalTheory.CompanionTheory.WeightIbp (isOpen_invertible val_mem_invertible weight_ibp)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def psi (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem psi_contDiff : ContDiff ℝ ∞ psi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem psi_eq_one {t : ℝ} (h : t ≤ 1) : psi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem psi_eq_zero {t : ℝ} (h : 2 ≤ t) : psi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem exists_deriv_bound : ∃ D : ℝ, ∀ t, ‖deriv psi t‖ ≤ D := by
  have hc : Continuous (deriv psi) := psi_contDiff.continuous_deriv (by simp)
  refine HasCompactSupport.exists_bound_of_continuous
    (HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun t ht => ?_) hc
  rcases lt_or_ge t 1 with h | h
  · have e : psi =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs using psi_eq_one (le_of_lt hs)
    rw [e.deriv_eq]; simp
  · have h2 : 2 < t := by
      by_contra hn
      exact ht ⟨h, not_lt.1 hn⟩
    have e : psi =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h2] with s hs using psi_eq_zero (le_of_lt hs)
    rw [e.deriv_eq]; simp

def chi (R : ℝ) (y : Mat n) : ℝ := psi (R⁻¹ * lg y)

theorem chi_smooth (hL : LgFacts) (R : ℝ) : ContDiffOn ℝ ∞ (chi R : Mat n → ℝ) (GLs n) :=
  psi_contDiff.comp_contDiffOn (contDiffOn_const.mul (hL n).2.2.2.1)

theorem chi_cpt {R : ℝ} (hR : 0 < R) : Cpt (chi R : Mat n → ℝ) := by
  refine ⟨2 * R, fun y _ h => psi_eq_zero ?_⟩
  rw [inv_mul_eq_div, le_div_iff₀ hR]
  exact h.le

theorem chi_eq_one {R : ℝ} (hR : 0 < R) {y : Mat n} (h : lg y ≤ R) : chi R y = 1 := by
  refine psi_eq_one ?_
  rw [inv_mul_eq_div, div_le_iff₀ hR]
  linarith

theorem chi_abs_le (R : ℝ) (y : Mat n) : ‖((chi R y : ℝ) : ℂ)‖ ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg (2 - R⁻¹ * lg y)
  have h1 := Real.smoothTransition.le_one (2 - R⁻¹ * lg y)
  have e : chi R y = Real.smoothTransition (2 - R⁻¹ * lg y) := rfl
  rw [Complex.norm_real, e, Real.norm_of_nonneg h0]
  exact h1

theorem chi_fderiv_le (hL : LgFacts) {D : ℝ} (hD : ∀ t, ‖deriv psi t‖ ≤ D) {R : ℝ} (hR : 0 < R) {x : Mat n}
    (hx : x ∈ GLs n) (v : Mat n) : |fderiv ℝ (chi R) x v| ≤ D * (R⁻¹ * |fderiv ℝ lg x v|) := by
  have hlg : HasFDerivAt (lg : Mat n → ℝ) (fderiv ℝ lg x) x :=
    (((hL n).2.2.2.1.contDiffAt (isOpen_invertible.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hp : HasDerivAt psi (deriv psi (R⁻¹ * lg x)) (R⁻¹ * lg x) :=
    ((psi_contDiff.differentiable (by simp)) _).hasDerivAt
  have h := (hp.comp_hasFDerivAt x (hlg.const_mul R⁻¹)).fderiv
  have e : fderiv ℝ (chi R) x v = deriv psi (R⁻¹ * lg x) * (R⁻¹ * fderiv ℝ lg x v) := by
    have e' : chi R = psi ∘ fun y : Mat n => R⁻¹ * lg y := rfl
    rw [e']
    exact (DFunLike.congr_fun h v).trans rfl
  rw [e, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR)]
  exact mul_le_mul_of_nonneg_right (hD _) (by positivity)

theorem chi_continuous (hL : LgFacts) (R : ℝ) : Continuous fun y : G n => ((chi R y.val : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    ((chi_smooth hL R).continuousOn.comp_continuous Units.continuous_val val_mem_invertible)

section Lim

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))

theorem tendsto_chi (hL : LgFacts) {h : G n → ℂ} (hh : Integrable h μ) :
    Tendsto (fun k : ℕ => ∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * h y ∂μ) atTop (𝓝 (∫ y, h y ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun y => ‖h y‖) (fun k => ?_) hh.norm (fun k => ?_) ?_
  · exact (chi_continuous hL _).aestronglyMeasurable.mul hh.1
  · refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (chi_abs_le _ _)
  · refine Eventually.of_forall fun y => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈lg y.val⌉₊] with k hk
    have h1 : lg y.val ≤ (k : ℝ) + 1 := by
      have := (Nat.le_ceil (lg y.val)).trans (Nat.cast_le.2 hk)
      linarith
    rw [chi_eq_one (by positivity) h1]
    simp

theorem tendsto_chi_deriv (hL : LgFacts) {X : Mat n} {C : ℝ} (hC : ∀ x ∈ GLs n, |fderiv ℝ lg x (x * X)| ≤ C)
    {h : G n → ℂ} (hh : Integrable h μ) :
    Tendsto (fun k : ℕ => ∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y ∂μ) atTop (𝓝 0) := by
  obtain ⟨D, hD⟩ := exists_deriv_bound
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hC0 : ∀ x ∈ GLs n, 0 ≤ C := fun x hx => (abs_nonneg _).trans (hC x hx)
  have hC1 : 0 ≤ C := hC0 _ (val_mem_invertible (1 : G n))
  have hb : ∀ k : ℕ, ‖∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y ∂μ‖ ≤
      (D * C * ∫ y, ‖h y‖ ∂μ) * ((k : ℝ) + 1)⁻¹ := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have := norm_integral_le_of_norm_le (μ := μ)
      (f := fun y : G n => ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * h y)
      (hh.norm.const_mul (D * (((k : ℝ) + 1)⁻¹ * C)))
      (Eventually.of_forall fun y => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (chi_fderiv_le hL hD hk (val_mem_invertible y) _).trans ?_
        gcongr
        exact hC _ (val_mem_invertible y))
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul]
    ring
  refine squeeze_zero_norm hb ?_
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (D * C * ∫ y, ‖h y‖ ∂μ)
  simpa [one_div] using this

end Lim

section Pair

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_coeff (X : Mat n) : ∃ c : Bool × Fin n × Fin n → ℝ, X = ∑ p, c p • bs p := by
  refine ⟨fun p => if p.1 then (X p.2.1 p.2.2).re else (X p.2.1 p.2.2).im, ?_⟩
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_prod_type, Fintype.sum_bool, bs, Matrix.single_apply]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_and]

theorem Rd_expand (f : Mat n → V) {X : Mat n} {c : Bool × Fin n × Fin n → ℝ} (h : X = ∑ p, c p • bs p) (g : Mat n) :
    Rd X f g = ∑ p, c p • Rd (bs p) f g := by
  simp only [Rd]
  rw [h, Matrix.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_smul, map_smul]

theorem lg_bound (hL : LgFacts) (X : Mat n) : ∃ C : ℝ, ∀ x ∈ GLs n, |fderiv ℝ lg x (x * X)| ≤ C := by
  obtain ⟨c, hc⟩ := exists_coeff X
  obtain ⟨C, hC⟩ := (hL n).2.2.2.2.2.2
  refine ⟨∑ p, |c p| * C, fun x hx => ?_⟩
  have e : fderiv ℝ lg x (x * X) = ∑ p, c p * fderiv ℝ lg x (x * bs p) := by
    rw [hc, Matrix.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_smul, map_smul, smul_eq_mul]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x hx p) (abs_nonneg _)

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)}

theorem memLp_Rd {f : Mat n → V} (hf : Sob μ f) (X : Mat n) : MemLp (fun y : G n => Rd X f y.val) 2 μ := by
  obtain ⟨c, hc⟩ := exists_coeff X
  have e : (fun y : G n => Rd X f y.val) = fun y : G n => ∑ p, c p • Rd (bs p) f y.val :=
    funext fun y => Rd_expand f hc y.val
  rw [e]
  exact memLp_finset_sum _ fun p _ => (hf.2 [p]).const_smul (c p)

theorem memLp_self {f : Mat n → V} (hf : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []

theorem integrable_pair {a b : G n → V} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun y => ⟪a y, b y⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)).congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem inner_cls {a b : Mat n → V} (ha : MemLp (fun y : G n => a y.val) 2 μ)
    (hb : MemLp (fun y : G n => b y.val) 2 μ) :
    ⟪cls μ a, cls μ b⟫_ℂ = ∫ y : G n, ⟪a y.val, b y.val⟫_ℂ ∂μ := by
  simp only [cls, dif_pos ha, dif_pos hb]
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

end Pair

theorem ibpSob : IbpSob := by
  intro n _ _ μ _ V _ _ hL _ hR f f' hf hf' X
  obtain ⟨C, hC⟩ := lg_bound hL X
  have m0 := memLp_self hf
  have m0' := memLp_self hf'
  have m1 := memLp_Rd hf X
  have m1' := memLp_Rd hf' X
  rw [inner_cls m1 m0', inner_cls m0 m1']
  have iA := integrable_pair m0 m1'
  have iB := integrable_pair m1 m0'
  have iC := integrable_pair m0 m0'
  have tA := tendsto_chi μ hL iA
  have tB := tendsto_chi μ hL iB
  have tC := tendsto_chi_deriv μ hL hC iC
  have key : ∀ k : ℕ, ∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * ⟪f y.val, Rd X f' y.val⟫_ℂ ∂μ =
      -(∫ y : G n, ((chi ((k : ℝ) + 1) y.val : ℝ) : ℂ) * ⟪Rd X f y.val, f' y.val⟫_ℂ ∂μ) -
        ∫ y : G n, ((fderiv ℝ (chi ((k : ℝ) + 1)) y.val (y.val * X) : ℝ) : ℂ) * ⟪f y.val, f' y.val⟫_ℂ ∂μ :=
    fun k => weight_ibp hR hL μ f' f (chi ((k : ℝ) + 1)) hf'.1 hf.1 (chi_smooth hL _) (chi_cpt (by positivity)) X
  have tA' := (tB.neg.sub tC).congr fun k => (key k).symm
  have e := tendsto_nhds_unique tA tA'
  rw [e, sub_zero, neg_neg]

end GlobalTheory.CompanionTheory.FcCalc.Ibp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToH0BijectiveOfInitial
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

section Initial

universe u v w

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {D : C} (hD : Limits.IsInitial D)

def toH0 : F.obj D →ₗ[R] CH.H F 0 where
  toFun x := (CH.cx F).cls (CH.aug F (fun T => (F.map (hD.to T)).hom) x) ((CrystallineSemistableComparison.P.initial F D hD).1 x)
  map_add' x y := by
    have := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.2.2.1 _ _ ((CrystallineSemistableComparison.P.initial F D hD).1 x) ((CrystallineSemistableComparison.P.initial F D hD).1 y)
      (by rw [map_add, (CrystallineSemistableComparison.P.initial F D hD).1 x, (CrystallineSemistableComparison.P.initial F D hD).1 y, add_zero])
    exact (cls_congr (map_add _ x y) _ _).trans this
  map_smul' r x := by
    have := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.2.2.2 r _ ((CrystallineSemistableComparison.P.initial F D hD).1 x)
      (by rw [map_smul, (CrystallineSemistableComparison.P.initial F D hD).1 x, smul_zero])
    exact (cls_congr (map_smul _ r x) _ _).trans this

theorem toH0_bijective_of_initial : Function.Bijective (toH0 F hD) := by
  obtain ⟨h1, h2, h3, -⟩ := CrystallineSemistableComparison.P.initial F D hD
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h := ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.1 _ (h1 x)).1 hx
    have h' := h2 x ((Submodule.mem_bot R).1 h)
    rwa [one_smul] at h'
  · intro c
    obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).1 c
    obtain ⟨x, hx⟩ := h3 f hf
    rw [one_smul] at hx
    exact ⟨x, cls_congr hx _ _⟩

include hD in
theorem H_succ_sub (j : ℕ) : Subsingleton (CH.H F (j + 1)) := by
  obtain ⟨-, -, -, hex⟩ := CrystallineSemistableComparison.P.initial F D hD
  have key : ∀ x : CH.H F (j + 1), x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) (j + 1)).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) (j + 1)).2.1 a ha).2 ?_
    obtain ⟨y, hy⟩ := hex j a ha
    rw [one_smul] at hy
    exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end Initial

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

section Base

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem base_case {D : C} {D' : C'} (hD : Limits.IsInitial D) (hD' : Limits.IsInitial D') (e : D ⟶ m.G.obj D')
    (ν : ∀ i, N i → R') (a b : ι → IdF Φ.A) (a' b' : IdF Φ'.A) (ha : ∀ i n, m.LeC (ν i n) (a i) a')
    (hb : ∀ i n, m.LeC (ν i n) (b i) b')
    (h : Tens R (N := N) (M := fun i => (sq (a i) (b i)).obj D) (M' := (sq a' b').obj D')
      fun i n x => (m.sqC (ν i n) (ha i n) (hb i n)).τ D' (((sq (a i) (b i)).map e).hom x)) (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (sq (a i) (b i)) j) (M' := CH.H (sq a' b') j)
      fun i n x => (m.sqC (ν i n) (ha i n) (hb i n)).pull j x := by
  cases j with
  | zero =>
    refine tens_transfer (fun i => LinearEquiv.ofBijective (toH0 (sq (a i) (b i)) hD) (toH0_bijective_of_initial _ hD))
      (LinearEquiv.ofBijective (toH0 (sq a' b') hD') (toH0_bijective_of_initial _ hD')).toAddEquiv _ _ (fun i n x => ?_) h
    change (m.sqC (ν i n) (ha i n) (hb i n)).hom.mapH 0 (toH0 (sq (a i) (b i)) hD x) = toH0 (sq a' b') hD' _
    have h1 := (CrystallineSemistableComparison.P.initial (sq (a i) (b i)) D hD).1 x
    refine (CrystallineSemistableComparison.P.mapH_cls _ 0 _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc _ _ h1)).trans (cls_congr (funext fun s => ?_) _ _)
    change (m.sqC (ν i n) (ha i n) (hb i n)).τ _ (((sq (a i) (b i)).map (hD.to (m.G.obj (s.obj (Fin.last 0))))).hom x) =
      ((sq a' b').map (hD'.to (s.obj (Fin.last 0)))).hom ((m.sqC (ν i n) (ha i n) (hb i n)).τ D' (((sq (a i) (b i)).map e).hom x))
    rw [← (m.sqC (ν i n) (ha i n) (hb i n)).nat]
    congr 1
    have h2 := congrArg (fun t => ((sq (a i) (b i)).map t).hom x)
      (hD.hom_ext (hD.to (m.G.obj (s.obj (Fin.last 0)))) (e ≫ m.G.map (hD'.to (s.obj (Fin.last 0)))))
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    exact h2
  | succ j => exact tens_zero (fun i => H_succ_sub _ hD j) (H_succ_sub _ hD' j) _

end Base

section Step

variable [Algebra R R'] [∀ i, Module.Flat R (N i)] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ')
  {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e)
  (hρ : ∀ T, Function.Injective (m.ρ T)) (ν : ∀ i, N i →ₗ[R] R')

theorem step (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r)
    (hQ' : Q'.Ladder a' b' r) (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r'))
    (c1 : ∀ r₀, (r₀ = r ∨ r₀ = r - 1) → ∀ j, Tens R (N := N) (M := fun i => CH.H (sq ((a i r₀).res (Cut.U E)) ((b i r₀).res (Cut.U E))) j)
      (M' := CH.H (sq ((a' r₀).res (Cut.U E')) ((b' r₀).res (Cut.U E'))) j)
      fun i n x => ((m1 m E E' e he hρ).sqC (ν i n) (le_cover_restrict_compat m E E' e he hρ (ha i n r₀)) (le_cover_restrict_compat m E E' e he hρ (hb i n r₀))).pull j x)
    (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  have hle : r - 1 ≤ r := by omega
  choose β hinj hex hsurj hform using fun i => GlobalTheory.T.filtration_critical_comparison_map Q E (a i) (b i) r (hQ i).le ((hQ i).ca r le_rfl)
    ((hQ i).ca _ hle) ((hQ i).cb r le_rfl) ((hQ i).cb _ hle)
  obtain ⟨β', hinj', hex', hsurj', hform'⟩ := GlobalTheory.T.filtration_critical_comparison_map Q' E' a' b' r hQ'.le (hQ'.ca r le_rfl)
    (hQ'.ca _ hle) (hQ'.cb r le_rfl) (hQ'.cb _ hle)
  have sI := fun i => CrystallineSemistableComparison.P.ses_cochains (alpha Q (a i r) (b i r)) (β i) (hinj i) (hex i) (hsurj i)
  have sP := CrystallineSemistableComparison.P.ses_cochains (alpha Q' (a' r) (b' r)) β' hinj' hex' hsurj'
  have hP : ∀ r₀, (r₀ = r ∨ r₀ = r - 1) → ∀ j, Tens R (N := N) (M := fun i => (CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i r₀) (b i r₀))).H j)
      (M' := (CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r₀) (b' r₀))).H j)
      fun i n x => (mP m E E' e he hρ Q Q' (ν i n) (ha i n r₀) (hb i n r₀)).hom.mapH j x := by
    intro r₀ hr₀ j
    exact tens_transfer
      (fun i => LinearEquiv.ofBijective ((CH.Mor.restrict (sq ((a i r₀).res (Cut.U E)) ((b i r₀).res (Cut.U E))) (Cut.P0 Q)).pull j)
        (CrystallineSemistableComparison.P.adj _ (Cut.P0 Q) (Cut.inc E) (Cut.adj Q) j))
      ((LinearEquiv.ofBijective ((CH.Mor.restrict (sq ((a' r₀).res (Cut.U E')) ((b' r₀).res (Cut.U E'))) (Cut.P0 Q')).pull j)
        (CrystallineSemistableComparison.P.adj _ (Cut.P0 Q') (Cut.inc E') (Cut.adj Q') j)).toAddEquiv) _ _
      (fun i n x => pull_restrict_first_piece_compat m E E' e he hρ Q Q' (ν i n) (ha i n r₀) (hb i n r₀) j x) (c1 r₀ hr₀ j)
  have hPt := tens_les
    (K := fun i => CH.cx (Pt.U E ⋙ sq (a i r) (b i r)))
    (L := fun i => CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i r) (b i r)))
    (M := fun i => CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i (r - 1)) (b i (r - 1))))
    (K' := CH.cx (Pt.U E' ⋙ sq (a' r) (b' r)))
    (L' := CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r) (b' r)))
    (M' := CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' (r - 1)) (b' (r - 1))))
    (fun i => (CH.Mor.ofNatTrans (alpha Q (a i r) (b i r))).hom) (fun i => (CH.Mor.ofNatTrans (β i)).hom)
    (fun i => (sI i).1) (fun i => (sI i).2.1) (fun i => (sI i).2.2)
    (CH.Mor.ofNatTrans (alpha Q' (a' r) (b' r))).hom (CH.Mor.ofNatTrans β').hom sP.1 sP.2.1 sP.2.2
    (fun i n => (mPt m E E' e (ν i n) (ha i n r) (hb i n r)).hom)
    (fun i n => (mP m E E' e he hρ Q Q' (ν i n) (ha i n r) (hb i n r)).hom)
    (fun i n => (mP m E E' e he hρ Q Q' (ν i n) (ha i n (r - 1)) (hb i n (r - 1))).hom)
    (fun i n k x => alpha_hom m E E' e he hρ Q Q' (ν i n) (ha i n r) (hb i n r) k x)
    (fun i n k x => funext fun s => beta_τ m E E' e he hρ Q Q' (ν i n) (ha i n) (hb i n) ((hQ i).ca r le_rfl)
      ((hQ i).ca _ hle) (β i) (hform i) β' hform' _ _)
    (hP r (Or.inl rfl)) (hP (r - 1) (Or.inr rfl))
    (fun i j => hadd_Pt m E E' e (ν i) (ha i · r) (hb i · r) j) j
  let u := fun i => LinearEquiv.ofBijective ((CH.Mor.restrict (sq (a i r) (b i r)) (Pt.U E)).pull j)
    (CrystallineSemistableComparison.P.adj _ (Pt.U E) (Pt.S E) (Pt.adj E) j)
  let u' := LinearEquiv.ofBijective ((CH.Mor.restrict (sq (a' r) (b' r)) (Pt.U E')).pull j)
    (CrystallineSemistableComparison.P.adj _ (Pt.U E') (Pt.S E') (Pt.adj E') j)
  refine tens_transfer (fun i => (u i).symm) u'.toAddEquiv.symm _ _ (fun i n x => ?_) hPt
  obtain ⟨z, rfl⟩ := (u i).surjective x
  rw [LinearEquiv.symm_apply_apply]
  symm
  refine (AddEquiv.symm_apply_eq u'.toAddEquiv).2 ?_
  exact pull_U m E E' e (ν i n) (ha i n r) (hb i n r) j z

end Step

section Main

variable [Algebra R R'] [∀ i, Module.Flat R (N i)]

theorem ladder_mono {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Q : Poly Φ} {a b : ℤ → IdF Φ.A} {r r₀ : ℤ}
    (h : Q.Ladder a b r) (hr : r₀ ≤ r) : Q.Ladder a b r₀ :=
  ⟨h.le, fun r' hr' => h.ca r' (hr'.trans hr), fun r' hr' => h.cb r' (hr'.trans hr)⟩

theorem main (ν : ∀ i, N i →ₗ[R] R') : ∀ (d : ℕ) {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ')
    (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e)
    (hρ : ∀ T, Function.Injective (m.ρ T)) (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ)
    (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  intro d
  induction d with
  | zero =>
    intro C C' _ _ Φ Φ' m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j
    exact base_case m (Frame.initial E) (Frame.initial E') e (fun i n => ν i n) (fun i => a i r) (fun i => b i r) (a' r) (b' r)
      (fun i n => ha i n r) (fun i n => hb i n r) (h r (by simp) le_rfl) j
  | succ d ih =>
    intro C C' _ _ Φ Φ' m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j
    refine step m Q Q' E E' e he hρ ν a b a' b' r hQ hQ' ha hb (fun r₀ hr₀ j => ?_) j
    have hle : r₀ ≤ r := by rcases hr₀ with rfl | rfl <;> omega
    have hlo : r - 1 ≤ r₀ := by rcases hr₀ with rfl | rfl <;> omega
    exact ih (m1 m E E' e he hρ) (Cut.Q1 Q) (Cut.Q1 Q') (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) (fr1 m E E' e he hρ)
      (fun T => hρ T.T) (fun i r => (a i r).res (Cut.U E)) (fun i r => (b i r).res (Cut.U E))
      (fun r => (a' r).res (Cut.U E')) (fun r => (b' r).res (Cut.U E')) r₀
      (fun i => Cut.ladder_truncation Q (ladder_mono (hQ i) hle)) (Cut.ladder_truncation Q' (ladder_mono hQ' hle))
      (fun i n r' => le_cover_restrict_compat m E E' e he hρ (ha i n r')) (fun i n r' => le_cover_restrict_compat m E E' e he hρ (hb i n r'))
      (fun r' h1 h2 => h r' (by push_cast; omega) (h2.trans hle)) j

end Main

theorem local_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ') {d : ℕ} (E : Frame Φ d)
    (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, Module.Flat R (N i)] (ν : ∀ i, N i →ₗ[R] R')
    (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  intro R R' _ _ _ C C' _ _ Φ Φ' m Q Q' d E E' e he hρ ι _ _ N _ _ _ ν a b a' b' r hQ hQ' ha hb h j
  exact main ν d m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveCptBoundedTime
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem lg_le_lg_mul_add (hL : LgFacts) {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) :
    lg x ≤ lg (x * y) + lg y := by
  have hdx : x.det ≠ 0 := hx
  have hdy : y.det ≠ 0 := hy
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdx hdy
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hdy
  have h1 := (hL n).1 (x * y) hxy y⁻¹ (inv_mem_GLs hy)
  have h2 := (hL n).2.1 y hy
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hu, h2] at h1
  exact h1

theorem wave_cpt_bounded_time : LgFacts → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V),
    IsWave E u → Cpt (u 0) → ∀ T : ℝ, ∃ R : ℝ, ∀ t, |t| ≤ T → ∀ y ∈ GLs n, R < lg y → u t y = 0 := by
  intro hL hS n E u hu hc T
  obtain ⟨c, hc'⟩ := hS n
  obtain ⟨R₀, hR₀⟩ := hc
  refine ⟨R₀ + |c| * (1 + |T|), fun t ht x hx hlg => hc' E u hu t x hx fun y hy hly => ?_⟩
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  refine hR₀ (x * y) hxy ?_
  have h1 := lg_le_lg_mul_add hL hx hy
  have h2 : |t| ≤ |T| := ht.trans (le_abs_self T)
  have h3 : c * (1 + |t|) ≤ |c| * (1 + |T|) :=
    calc c * (1 + |t|) ≤ |c| * (1 + |t|) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  linarith

end GlobalTheory.CompanionTheory.WaveMult
end
end

