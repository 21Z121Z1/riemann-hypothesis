import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmul
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

namespace GlobalTheory.VacCore

theorem ray_formula {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : V → ℂ) (hk : Differentiable ℝ k) (w : V) (ℓ : V →ₗ[ℝ] ℂ)
    (h : ∀ z, fderiv ℝ k z w = ℓ z * k z) : k w = k 0 * Complex.exp (ℓ w / 2) := by
  set c := ℓ w
  let E : ℝ → ℂ := fun s => Complex.exp (((-(s ^ 2) / 2 : ℝ) : ℂ) * c)
  have hE : ∀ s : ℝ, HasDerivAt E (Complex.exp (((-(s ^ 2) / 2 : ℝ) : ℂ) * c) * (((-(2 * s) / 2 : ℝ) : ℂ) * c)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (-(s ^ 2) / 2 : ℝ)) (-(2 * s) / 2) s := by
      have := ((hasDerivAt_pow 2 s).neg).div_const 2
      simpa using this
    exact ((h1.ofReal_comp).mul_const c).cexp
  have hK : ∀ s : ℝ, HasDerivAt (fun s : ℝ => k (s • w)) (fderiv ℝ k (s • w) w) s := by
    intro s
    have := (hk (s • w)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const w)
    rw [one_smul] at this
    exact this
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => k (s • w) * E s) 0 s := by
    intro s
    have := (hK s).mul (hE s)
    refine this.congr_deriv ?_
    rw [h, map_smul]
    simp only [Complex.real_smul, E]
    push_cast
    ring
  have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => k (s • w) * E s)
    (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) 1 0
  simp only [E, one_smul, zero_smul] at hc
  have : Complex.exp (((-((1:ℝ) ^ 2) / 2 : ℝ) : ℂ) * c) * Complex.exp (c / 2) = 1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; simp
  calc k w = k w * (Complex.exp (((-((1:ℝ) ^ 2) / 2 : ℝ) : ℂ) * c) * Complex.exp (c / 2)) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hc]; simp

theorem conj_mul_eq_zero_of_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f g : SchwartzMap V ℂ) (y₀ : V) (hy : y₀ ≠ 0)
    (h : ∀ z, fderiv ℝ f z y₀ * (starRingEnd ℂ) (g z) + f z * (starRingEnd ℂ) (fderiv ℝ g z y₀) = 0) :
    ∀ z, f z * (starRingEnd ℂ) (g z) = 0 := by
  intro z
  let φ : ℝ → ℂ := fun t => f (z + t • y₀) * (starRingEnd ℂ) (g (z + t • y₀))
  have hL : ∀ t : ℝ, HasDerivAt (fun t : ℝ => z + t • y₀) y₀ t := by
    intro t
    have := ((hasDerivAt_id t).smul_const y₀).const_add z
    simpa using this
  have hφ : ∀ t, HasDerivAt φ 0 t := by
    intro t
    have hf := (f.differentiableAt (x := z + t • y₀)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have hg := (g.differentiableAt (x := z + t • y₀)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have hg' := hg.star
    have := hf.mul hg'
    refine this.congr_deriv ?_
    have := h (z + t • y₀)
    simpa [Complex.star_def] using this
  have hc : ∀ t, φ t = φ 0 := fun t =>
    is_const_of_deriv_eq_zero (fun s => (hφ s).differentiableAt) (fun s => (hφ s).deriv) t 0
  have hlin : Filter.Tendsto (fun t : ℝ => z + t • y₀) (Filter.cocompact ℝ) (Filter.cocompact V) := by
    apply Filter.tendsto_cocompact_cocompact_of_norm
    intro ε
    have hy' : 0 < ‖y₀‖ := norm_pos_iff.mpr hy
    refine ⟨(ε + ‖z‖) / ‖y₀‖, fun t ht => ?_⟩
    have h1 : ‖t • y₀‖ ≤ ‖z + t • y₀‖ + ‖z‖ := by
      calc ‖t • y₀‖ = ‖(z + t • y₀) - z‖ := by simp
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul] at h1
    rw [div_lt_iff₀ hy'] at ht
    linarith
  have hf0 : Filter.Tendsto (fun t : ℝ => f (z + t • y₀)) (Filter.cocompact ℝ) (nhds 0) :=
    (f.tendsto_cocompact).comp hlin
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖g x‖ ≤ C := ⟨_, fun x => (g.toBoundedContinuousFunction).norm_coe_le_norm x⟩
  have hφ0 : Filter.Tendsto φ (Filter.cocompact ℝ) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hf0 ⊢
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have := hf0.mul_const C
    rw [zero_mul] at this
    refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) this
    simp only [φ, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hconst : Filter.Tendsto φ (Filter.cocompact ℝ) (nhds (φ 0)) := by
    have : φ = fun _ => φ 0 := funext hc
    rw [this]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst hφ0
  simpa [φ] using this

noncomputable def lin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b : V) : V →ₗ[ℝ] ℂ where
  toFun z := 2 * Real.pi * Complex.I * (B z a : ℂ) + 2 * Real.pi * (B z b : ℂ)
  map_add' x y := by simp only [map_add, LinearMap.add_apply, Complex.ofReal_add]; ring
  map_smul' c x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

theorem lin_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a b z : V) :
    lin B a b z = 2 * Real.pi * Complex.I * (B z a : ℂ) + 2 * Real.pi * (B z b : ℂ) := rfl

theorem schwartz_vacuum_eq_smul : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ y, (∀ x, B x y = 0) → y = 0) →
    ∀ (J e : (V × V) →ₗ[ℝ] (V × V)) (e' : V →ₗ[ℝ] V), (∀ y, J (J y) = -y) → (∀ y, e (e y) = e y) →
    (∀ y, J (e y) = e (J y)) → (∀ y, (e y).1 = e' y.1) → (∀ y x, B x (e y).2 = B (e' x) y.2) →
    ∀ (f g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ y x, fderiv ℝ g x (J y).1 - 2 * Real.pi * Complex.I * (B x (J y).2 : ℝ) * g x =
      Complex.I * (fderiv ℝ g x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * g x)) →
    (∀ y x, fderiv ℝ f x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I * (B x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f x =
      Complex.I * (fderiv ℝ f x y.1 - 2 * Real.pi * Complex.I * (B x y.2 : ℝ) * f x)) →
    ∃ z : ℂ, f = z • g := by
  intro V _ _ _ B hB J e e' hJ he hJe he1 he2 f g hg0 hg hf

  have hinj : ∀ y, (J y).1 = 0 → y.1 = 0 → y = 0 := by
    intro y hJy hy1
    have key : ∀ x, g x ≠ 0 → B x y.2 = 0 := by
      intro x hx
      have h := hg y x
      simp only [hJy, hy1, map_zero] at h
      have h2 : g x * (2 * Real.pi * (B x y.2 : ℂ) + 2 * Real.pi * Complex.I * (B x (J y).2 : ℂ)) = 0 := by
        linear_combination (-1 : ℂ) * h + (2 * Real.pi * (B x y.2 : ℂ) * g x) * Complex.I_sq
      have h3 := (mul_eq_zero.mp h2).resolve_left hx
      have h4 := congrArg Complex.re h3
      simpa [Real.pi_ne_zero] using h4
    have hy2 : y.2 = 0 := by
      apply hB
      by_contra hne
      push_neg at hne
      obtain ⟨x₀, hx₀⟩ := hne
      apply hg0
      ext x
      simp only [SchwartzMap.zero_apply]
      set t₀ : ℝ := -(B x y.2) / B x₀ y.2
      have hS : IsClosed {t : ℝ | g (x + t • x₀) = 0} :=
        isClosed_eq (g.continuous.comp (continuous_const.add (continuous_id.smul continuous_const)))
          continuous_const
      have hsub : ({t₀}ᶜ : Set ℝ) ⊆ {t : ℝ | g (x + t • x₀) = 0} := by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
        simp only [Set.mem_setOf_eq]
        by_contra hgt
        have := key _ hgt
        rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
        apply ht
        simp only [t₀]
        field_simp
        linarith
      have hcl := hS.closure_subset_iff.mpr hsub
      rw [(dense_compl_singleton t₀).closure_eq] at hcl
      have := hcl (Set.mem_univ 0)
      simpa using this
    exact Prod.ext hy1 hy2
  let T : (V × V) →ₗ[ℝ] (V × V) := (LinearMap.fst ℝ V V ∘ₗ J).prod (LinearMap.fst ℝ V V)
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hinj y (congrArg Prod.fst hy) (congrArg Prod.snd hy)
  have hTs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTi

  choose yx hyx using fun x : V => hTs (x, 0)
  have hyx1 : ∀ x, (J (yx x)).1 = x := fun x => by simpa [T] using congrArg Prod.fst (hyx x)
  have hyx2 : ∀ x, (yx x).1 = 0 := fun x => by simpa [T] using congrArg Prod.snd (hyx x)
  have hray : ∀ k : SchwartzMap V ℂ, (∀ (y : V × V) (z : V), fderiv ℝ k z (J y).1 -
      2 * Real.pi * Complex.I * (B z (J y).2 : ℝ) * k z =
      Complex.I * (fderiv ℝ k z y.1 - 2 * Real.pi * Complex.I * (B z y.2 : ℝ) * k z)) →
      ∀ x, k x = k 0 * Complex.exp (lin B (J (yx x)).2 (yx x).2 x / 2) := by
    intro k hk x
    apply ray_formula k k.differentiable x (lin B (J (yx x)).2 (yx x).2)
    intro z
    have h := hk (yx x) z
    rw [hyx1, hyx2, map_zero] at h
    rw [lin_apply]
    linear_combination h - (2 * Real.pi * (B z (yx x).2 : ℂ) * k z) * Complex.I_sq
  have hg_ray := hray g hg
  have hg00 : g 0 ≠ 0 := by
    intro h0; apply hg0; ext x; rw [hg_ray x, h0]; simp
  have hgne : ∀ x, g x ≠ 0 := fun x => by
    rw [hg_ray x]; exact mul_ne_zero hg00 (Complex.exp_ne_zero _)
  have he'2 : ∀ v, e' (e' v) = e' v := by
    intro v
    have := congrArg Prod.fst (he (v, 0))
    simp only [he1] at this
    simpa using this
  by_cases hz : ∀ v, e' v = 0
  · have he0 : ∀ y, e y = 0 := by
      intro y; apply Prod.ext
      · rw [he1, hz]; rfl
      · apply hB; intro x; rw [he2, hz, map_zero, LinearMap.zero_apply]
    have hf' : ∀ (y : V × V) (z : V), fderiv ℝ f z (J y).1 -
        2 * Real.pi * Complex.I * (B z (J y).2 : ℝ) * f z =
        Complex.I * (fderiv ℝ f z y.1 - 2 * Real.pi * Complex.I * (B z y.2 : ℝ) * f z) := by
      intro y z; have := hf y z; rwa [he0, smul_zero, sub_zero] at this
    have hf_ray := hray f hf'
    refine ⟨f 0 / g 0, ?_⟩
    ext x
    rw [SchwartzMap.smul_apply, smul_eq_mul, hf_ray x, hg_ray x]
    field_simp
  · push_neg at hz
    obtain ⟨v, hv⟩ := hz
    set y₀ := e' v with hy₀def
    have hy₀ : e' y₀ = y₀ := he'2 v
    obtain ⟨u, hu⟩ := hTs (y₀, 0)
    have hu1 : (J u).1 = y₀ := by simpa [T] using congrArg Prod.fst hu
    have hu2 : u.1 = 0 := by simpa [T] using congrArg Prod.snd hu
    have heu : e u = u := by
      have : e u - u = 0 := hinj _
        (by rw [map_sub, Prod.fst_sub, hJe, he1, hu1, hy₀, sub_self])
        (by rw [Prod.fst_sub, he1, hu2, map_zero, sub_self])
      exact sub_eq_zero.mp this
    have hfu : ∀ z, fderiv ℝ f z y₀ = (2 * Real.pi * Complex.I * (B z (J u).2 : ℂ)
        - 2 * Real.pi * (B z u.2 : ℂ)) * f z := by
      intro z
      have h := hf u z
      rw [heu, two_smul, sub_add_cancel_left, map_neg, Prod.fst_neg, Prod.snd_neg, map_neg,
        map_neg, hu1, hu2, map_zero, Complex.ofReal_neg] at h
      linear_combination (-1 : ℂ) * h + (2 * Real.pi * (B z u.2 : ℂ) * f z) * Complex.I_sq
    have hgu : ∀ z, fderiv ℝ g z y₀ = (2 * Real.pi * Complex.I * (B z (J u).2 : ℂ)
        + 2 * Real.pi * (B z u.2 : ℂ)) * g z := by
      intro z
      have h := hg u z
      rw [hu1, hu2, map_zero] at h
      linear_combination h - (2 * Real.pi * (B z u.2 : ℂ) * g z) * Complex.I_sq
    have hk := conj_mul_eq_zero_of_line f g y₀ hv (fun z => by
      rw [hfu z, hgu z]
      simp only [map_add, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring)
    refine ⟨0, ?_⟩
    ext z
    rw [zero_smul, SchwartzMap.zero_apply]
    exact (mul_eq_zero.mp (hk z)).resolve_right ((map_ne_zero _).mpr (hgne z))

end GlobalTheory.VacCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SesquilinearDetOrdSignOnKernelConjGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

theorem ordL_mul_of_ne [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dif_neg hx', dif_neg hy', dif_neg hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

theorem sign_mul_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {d : K} (hd : d ≠ 0) (x : K) :
    (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul_of_ne (mul_ne_zero hσd hd) hx, ordL_mul_of_ne hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

theorem gram_eq_mul (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι]
    (v : ι → Fin n → K) :
    (Matrix.of fun i j => hform σ H (v i) (v j)) =
      cT σ (Matrix.of fun p i => v i p) * H * Matrix.of fun p i => v i p := by
  ext i j
  simp only [hform, cT, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cols_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {ι : Type} (v : ι → Fin n → K) :
    (Matrix.of fun p i => (M *ᵥ v i) p) = M * Matrix.of fun p i => v i p := by
  ext p i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem det_cT (σ : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι K) :
    (cT σ T).det = σ T.det := by
  unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

theorem gram_det_change (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (b b' : Module.Basis ι K W) :
    ∃ d : K, d ≠ 0 ∧
      (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
        σ d * d * (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set T := b.toMatrix b' with hT
  have hcol : (Matrix.of fun p i => (b' i : Fin n → K) p) = (Matrix.of fun p i => (b i : Fin n → K) p) * T := by
    ext p j
    have hs := congrArg (fun x : W => (x : Fin n → K) p) (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    rw [Matrix.of_apply, ← hs, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.of_apply, hT, Module.Basis.toMatrix_apply, mul_comm]
  have hTT : T * b'.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b b'
  have hd : T.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hTT
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨T.det, hd, ?_⟩
  rw [gram_eq_mul σ H (fun i => (b' i : Fin n → K)), gram_eq_mul σ H (fun i => (b i : Fin n → K)), hcol,
    cT_mul]
  set B := Matrix.of fun p i => (b i : Fin n → K) p
  rw [show cT σ T * cT σ B * H * (B * T) = cT σ T * (cT σ B * H * B) * T by simp only [Matrix.mul_assoc]]
  simp only [Matrix.det_mul, det_cT]
  ring

theorem sign_basis [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b : Module.Basis ι K W) (b' : Module.Basis ι' K W) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set e : ι' ≃ ι := b'.indexEquiv b
  have hsub : (Matrix.of fun i j => hform σ H ((b.reindex e.symm) i : Fin n → K) ((b.reindex e.symm) j)) =
      (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).submatrix e e := by
    ext i j
    simp [Module.Basis.reindex_apply]
  obtain ⟨d, hd, hdet⟩ := gram_det_change σ H W (b.reindex e.symm) b'
  rw [hdet, sign_mul_norm σ hσ hd, hsub, Matrix.det_submatrix_equiv_self]

theorem aeval_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    aeval (k⁻¹ * a * k).val Q = (k⁻¹).val * aeval a.val Q * k.val := by
  have hp : ∀ i : ℕ, ((k⁻¹ * a * k : GL (Fin n) K).val) ^ i = (k⁻¹).val * a.val ^ i * k.val := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  simp only [hp, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UnitaryClasses.SgnConj

namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

theorem ker_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) =
      (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).comap (Matrix.toLin' k.val) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.toLin'_apply, aeval_conj]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun y => k.val *ᵥ y) h
    simpa [Matrix.mulVec_mulVec] using this
  · intro h
    rw [h, Matrix.mulVec_zero]

def invEquiv {n : ℕ} (k : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' (k⁻¹).val) (Matrix.toLin' k.val)
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])

theorem map_invEquiv {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).map (invEquiv k : (Fin n → K) →ₗ[K] (Fin n → K)) =
      LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) := by
  rw [ker_conj, Submodule.map_equiv_eq_comap_symm]
  rfl

theorem sgnOn_conj : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K),
    sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := by
  intro K _ _ σ hσ n Q a k
  set V := LinearMap.ker (Matrix.toLin' (aeval a.val Q))
  set V' := LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q))
  let b0 := Module.finBasis K V
  let b'' : Module.Basis (Fin (Module.finrank K V)) K V' :=
    b0.map ((invEquiv k).ofSubmodules V V' (map_invEquiv Q a k))
  have hb'' : ∀ i, (b'' i : Fin n → K) = (k⁻¹).val *ᵥ (b0 i : Fin n → K) := by
    intro i
    simp [b'', Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, invEquiv]
  unfold sgnOn gramOn
  rw [sign_basis σ hσ 1 V' b'' (Module.finBasis K V')]
  congr 3
  rw [gram_eq_mul σ 1 (fun i => (b'' i : Fin n → K)), gram_eq_mul σ _ (fun i => (b0 i : Fin n → K))]
  simp only [hb'']
  rw [cols_mulVec, cT_mul]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

end GlobalTheory.UnitaryClasses.SgnConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilFockAniso
section
noncomputable section

open NumberField MeasureTheory
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
open GlobalTheory.NormSum (Pair Tup)

namespace GlobalTheory.NormAdelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

def openK (X : GlobalTheory.NormDict.Data P) : Subgroup (GA D X.A) := Lev.levA X.A X.KA ⊔ GinfC X.A

def zr (X : GlobalTheory.NormDict.Data P) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)) (T : Tup D P.a P.d P.n) : ℂ :=
  ∫ g in (openK X : Set (GA D X.A)), wcoef X.om ν 𝓕 (X.fock T) (X.fock T) g ∂X.m

def SiegelWeilFockAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank → Formalism.L2.Theta.IsAniso B →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

def GlobalFormAnisoAt (A : HSp D) (L : Lat A) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → Formalism.L2.Theta.IsAniso B →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA,
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    (∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s) m) ∧
    ∃ z, HolValueAt (fun s => ∫ g, integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s g ∂m) (sZero A B) z ∧
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * z

end GlobalTheory.NormAdelic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDetEqUnitMulNormAtInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_det_eq_unit_mul_norm_at_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → Even n →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∃ (y : Fv F v ⊗[F] E) (u : Fv F v), Valued.v u = 1 ∧
      (1 : Fv F v) ⊗ₜ[F] W.J.det = algebraMap (Fv F v) (Fv F v ⊗[F] E) u *
        (y * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ y) := by
  first | exact @GlobalTheory.SkewDetParity.det_eq_unit_mul_norm | exact GlobalTheory.SkewDetParity.det_eq_unit_mul_norm | (intros; apply GlobalTheory.SkewDetParity.det_eq_unit_mul_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOneStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_character_of_trivial_near_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}, 0 < n → ∀ (ν : kˣ →* ℂˣ) (s : ℂ) (P : Set (GL (Fin n) k)), P ∈ 𝓝 1 → (∀ g ∈ P, (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) s = 1) → GlobalTheory.SmGL.IsSmoothChar ν := by
  first | exact @GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds | exact GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds | (intros; apply GlobalTheory.SmoothCharDet.isSmoothChar_of_detChar_apow_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTrivSqZeroExtIsPushoutStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_trivSqZeroExt_isPushout : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∃! z₀ : Sp (TrivSqZeroExt R M) ⟶ X, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ≫ z₀ = x ∧ spMap β ≫ z₀ = z := by
  first | exact @GlobalTheory.Pinch.pinch_main | exact GlobalTheory.Pinch.pinch_main | (intros; apply GlobalTheory.Pinch.pinch_main <;> assumption)
end

