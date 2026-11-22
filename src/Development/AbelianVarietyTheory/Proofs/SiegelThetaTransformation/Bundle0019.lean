import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0016
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticOfUnitaryCmField
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0018
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortIsotropicVectorsExistenceSuccOfVeryShortSte

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalMatrixMoveAdmissibleUniformLevelStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_matrix_move_admissible_uniform_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by
  first | exact @GlobalTheory.SW.twist_move_adm | exact GlobalTheory.SW.twist_move_adm | (intros; apply GlobalTheory.SW.twist_move_adm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticOfUnitaryCmFieldStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_symplectic_of_unitary_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (γ : M2 E N), γ ∈ UU E N → ∃ σ ∈ Matrix.symplecticGroup (QI E N) ℚ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Z ∈ Hn Ψ N, spAct σ (tauOf Ψ Z) = tauOf Ψ (hAct Ψ γ Z) ∧ (spDen σ (tauOf Ψ Z)).det = c * ∏ τ, (hDen Ψ γ Z τ).det ^ 2 ∧ ∀ z z' : CM Ψ n N, (zetaOf Ψ (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = fun k => zetaOf Ψ z z' k ᵥ* (spDen σ (tauOf Ψ Z))⁻¹) ∧ ∀ k, zetaOf Ψ z z' k ⬝ᵥ ((spDen σ (tauOf Ψ Z))⁻¹ * qm σ.toBlocks₂₁) *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k := by
  first | exact @GlobalTheory.SW.exists_symplectic_of_unitary | exact GlobalTheory.SW.exists_symplectic_of_unitary | (intros; apply GlobalTheory.SW.exists_symplectic_of_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianQuadFormRationalCoordsHermitianStatement
section
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_quadForm_rationalCoords_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (k : Fin n), zetaOf Ψ z z' k ⬝ᵥ ((tauOf Ψ Z).map fun t => (t.im : ℂ))⁻¹ *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (imH (Z τ))⁻¹ *ᵥ z τ k := by
  first | exact @GlobalTheory.SW.gauss_form_dictionary | exact GlobalTheory.SW.gauss_form_dictionary | (intros; apply GlobalTheory.SW.gauss_form_dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFnStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTheta_summable_and_determines_testFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → ∀ Z ∈ Hn Ψ N, (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * expo Ψ x Z z z')‖) ∧ ∀ ψ, IsSB ψ → (∀ z z', thH Ψ φ Z z z' = thH Ψ ψ Z z z') → φ = ψ := by
  first | exact @GlobalTheory.SW.thH_summable_and_inj | exact GlobalTheory.SW.thH_summable_and_inj | (intros; apply GlobalTheory.SW.thH_summable_and_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatThH
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.ExpSum

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} {U : Set V}

omit [FiniteDimensional ℂ V] in

theorem convexOn_norm_term (c : ℂ) (L : V →L[ℂ] ℂ) :
    ConvexOn ℝ Set.univ fun p => ‖c * cexp (L p)‖ := by
  have h : ConvexOn ℝ Set.univ fun p => Real.exp ((L p).re) := by
    have := convexOn_exp.comp_linearMap
      (Complex.reLm ∘ₗ (L.toLinearMap.restrictScalars ℝ))
    exact this
  simpa only [norm_mul, Complex.norm_exp, smul_eq_mul] using h.smul (norm_nonneg c)

theorem locally_normal (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) :
    ∀ x ∈ U, ∃ W ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ p ∈ W, ‖c i * cexp (L i p)‖ ≤ u i := by
  intro x hx
  have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  obtain ⟨b, hb, hbU⟩ := exists_mem_interior_convexHull_affineBasis (hU.mem_nhds hx)
  refine ⟨_, mem_interior_iff_mem_nhds.1 hb, fun i => ∑ j, ‖c i * cexp (L i (b j))‖,
    summable_sum fun j _ => hs _ (hbU (subset_convexHull ℝ _ ⟨j, rfl⟩)), fun i p hp => ?_⟩
  obtain ⟨y, ⟨j, rfl⟩, hy⟩ := (convexOn_norm_term (c i) (L i)).exists_ge_of_mem_convexHull
    (Set.subset_univ _) hp
  exact hy.trans (Finset.single_le_sum (f := fun j => ‖c i * cexp (L i (b j))‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j))

theorem differentiableOn (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) :
    DifferentiableOn ℂ (fun p => ∑' i, c i * cexp (L i p)) U :=
  GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU
    (fun i => Differentiable.differentiableOn (by fun_prop)) (locally_normal hU c L hs)

theorem hasSum_deriv (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (hp : p ∈ U) (v : V) :
    HasSum (fun i => c i * L i v * cexp (L i p))
      (deriv (fun s : ℂ => ∑' i, c i * cexp (L i (p + s • v))) 0) := by
  have h1 := GlobalTheory.SCV.hasSum_fderiv_of_locally_normal (F := fun i p => c i * cexp (L i p)) hU
    (fun i => Differentiable.differentiableOn (by fun_prop)) (locally_normal hU c L hs) hp
  have h2 := (ContinuousLinearMap.apply ℂ ℂ v).hasSum h1
  have h3 := ((differentiableOn hU c L hs).differentiableAt (hU.mem_nhds hp)).lineDeriv_eq_fderiv
    (v := v)
  rw [lineDeriv] at h3
  rw [h3]
  have e : (fun i => c i * L i v * cexp (L i p)) = fun i =>
      ContinuousLinearMap.apply ℂ ℂ v (fderiv ℂ (fun p => c i * cexp (L i p)) p) := by
    funext i
    have : HasFDerivAt (fun p => c i * cexp (L i p)) (c i • cexp (L i p) • L i) p :=
      ((L i).hasFDerivAt.cexp).const_mul (c i)
    rw [this.fderiv]
    simp
    ring
  rw [e]
  exact h2

theorem hasSum_deriv_deriv (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (v w : V)
    (hp : ∀ s : ℂ, p + s • v ∈ U) :
    HasSum (fun i => c i * L i w * L i v * cexp (L i p))
      (deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' i, c i * cexp (L i (p + s • v + t • w))) 0) 0) := by
  have h := hasSum_deriv hU (fun i => c i * L i w) L
    (fun q hq => summable_norm_iff.2 (hasSum_deriv hU c L hs hq w).summable)
    (p := p) (by simpa using hp 0) v
  convert h using 3 with s
  exact (hasSum_deriv hU c L hs (hp s) w).tsum_eq.symm

end General

variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem imH_isHermitian (Z : Matrix (Fin N) (Fin N) ℂ) : (imH Z).IsHermitian := by
  unfold imH IsHermitian
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← neg_sub Z, smul_neg,
    ← neg_smul]
  congr 1
  simp

theorem isOpen_dom : IsOpen {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := by
  refine isOpen_iff_mem_nhds.2 fun p hp => ?_
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N => imH (q.1 τ)) (fun i j => ?_)
    (fun q => imH_isHermitian _) p (hp τ)
  change Continuous fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
    (2 * I)⁻¹ * (q.1 τ i j - star (q.1 τ j i))
  fun_prop

theorem expo_eq (x : Matrix (Fin n) (Fin N) E) (Z : CF Ψ N N) (z z' : CF Ψ n N) :
    expo Ψ x Z z z' = ∑ τ : Ψ, ∑ k, (∑ a, ∑ b, τ.1 (x k a) * (Z τ a b * conj (τ.1 (x k b))) +
      ∑ a, τ.1 (x k a) * z τ k a + ∑ a, z' τ k a * conj (τ.1 (x k a))) := by
  simp only [expo, dotProduct, mulVec, Finset.mul_sum]

noncomputable def form (x : Matrix (Fin n) (Fin N) E) :
    (CF Ψ N N × CF Ψ n N × CF Ψ n N) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => 2 * π * I * expo Ψ x p.1 p.2.1 p.2.2
      map_add' := fun p q => by
        simp only [expo_eq, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        simp only [expo_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1
        · congr 1
          · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => by ring
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring }

theorem form_apply (x : Matrix (Fin n) (Fin N) E) (p : CF Ψ N N × CF Ψ n N × CF Ψ n N) :
    form Ψ x p = 2 * π * I * expo Ψ x p.1 p.2.1 p.2.2 := rfl

open Classical in

noncomputable def dir {m : ℕ} (τ : Ψ) (k : Fin m) (a : Fin N) : CF Ψ m N :=
  fun σ i j => if σ = τ then if i = k then if j = a then 1 else 0 else 0 else 0

open Classical in

theorem add_smul_dir {m : ℕ} (x : CM Ψ m N) (τ : Ψ) (k : Fin m) (a : Fin N) (s : ℂ) :
    (fun σ => x σ + if σ = τ then Matrix.single k a s else 0 : CM Ψ m N) =
      (HAdd.hAdd (α := CF Ψ m N) (β := CF Ψ m N) x (s • dir Ψ τ k a) : CF Ψ m N) := by
  funext σ i j
  change x σ i j + (if σ = τ then Matrix.single k a s else 0 : Matrix (Fin m) (Fin N) ℂ) i j =
    x σ i j + s * dir Ψ τ k a σ i j
  by_cases h : σ = τ <;> by_cases h1 : i = k <;> by_cases h2 : j = a <;>
    simp [dir, h, h1, h2, Matrix.single] <;> tauto

theorem form_dir₁ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (a b : Fin N) :
    form Ψ x (dir Ψ τ a b, 0, 0) = 2 * π * I * ∑ k, τ.1 (x k a) * conj (τ.1 (x k b)) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp

theorem form_dir₂ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, dir Ψ τ k a, 0) = 2 * π * I * τ.1 (x k a) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp

theorem form_dir₃ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, 0, dir Ψ τ k a) = 2 * π * I * conj (τ.1 (x k a)) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp

open Classical in

theorem line₁ (Z : CF Ψ N N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) (s : ℂ) :
    (Z, z, z') + s • ((dir Ψ τ a b, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) =
      (Z + s • dir Ψ τ a b, z, z') := by simp

theorem line₂ (Z : CF Ψ N N) (z z' v : CF Ψ n N) (s : ℂ) :
    (Z, z, z') + s • ((0, v, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) = (Z, z + s • v, z') := by simp

theorem line₃ (Z : CF Ψ N N) (z z' v : CF Ψ n N) (s : ℂ) :
    (Z, z, z') + s • ((0, 0, v) : CF Ψ N N × CF Ψ n N × CF Ψ n N) = (Z, z, z' + s • v) := by simp

theorem heat_dir (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖)
    (Z : CF Ψ N N) (hZ : (Z : CM Ψ N N) ∈ Hn Ψ N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) :
    2 * π * I * deriv (fun s : ℂ => ∑' x, φ x * cexp (form Ψ x (Z + s • dir Ψ τ a b, z, z'))) 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' x, φ x *
        cexp (form Ψ x (Z, z + s • dir Ψ τ k a, z' + t • dir Ψ τ k b))) 0) 0 := by
  have h1 := (hasSum_deriv (isOpen_dom Ψ) φ (form Ψ) hs (p := (Z, z, z')) hZ
    (dir Ψ τ a b, 0, 0)).mul_left (2 * π * I)
  have h2 := hasSum_sum (s := Finset.univ) fun k _ =>
    hasSum_deriv_deriv (isOpen_dom Ψ) φ (form Ψ) hs (p := (Z, z, z'))
      (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b) (fun s => by rw [line₂]; exact hZ)
  have e : (fun x => 2 * π * I * (φ x * form Ψ x (dir Ψ τ a b, 0, 0) * cexp (form Ψ x (Z, z, z')))) =
      fun x => ∑ k, φ x * form Ψ x (0, 0, dir Ψ τ k b) * form Ψ x (0, dir Ψ τ k a, 0) *
        cexp (form Ψ x (Z, z, z')) := by
    funext x
    simp only [form_dir₁, form_dir₂, form_dir₃, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e] at h1
  have h3 := h1.unique h2
  simp only [line₁, line₂, line₃] at h3
  exact h3

end GlobalTheory.SW.ExpSum

open GlobalTheory.SW.ExpSum in

theorem GlobalTheory.SW.isHeat_thH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsHeat Ψ (thH Ψ φ) := by
  intro E _ _ _ Ψ hΨ n N φ hφ
  have hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖ := fun p hp =>
    (GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n N φ hφ _ hp).1 _ _
  refine ⟨differentiableOn (isOpen_dom Ψ) φ (form Ψ) hs, fun Z hZ z z' τ a b => ?_⟩
  simp only [add_smul_dir]
  exact heat_dir Ψ φ hs Z hZ z z' τ a b
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.QuadCocycle
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HermComp

variable {N : ℕ}

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {N : ℕ} in

theorem _root_.GlobalTheory.SW.HermComp.row_rel (g : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)
    (h : gᴴ * Matrix.J (Fin N) ℂ * g = Matrix.J (Fin N) ℂ) :
    g.toBlocks₁₁ * g.toBlocks₂₂ᴴ - g.toBlocks₁₂ * g.toBlocks₂₁ᴴ = 1 ∧
      g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = g.toBlocks₂₁ * g.toBlocks₂₂ᴴ := by
  set J := Matrix.J (Fin N) ℂ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hleft : (-(J * gᴴ * J)) * g = 1 := by
    have : J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, this, h, hJJ, neg_neg]
  have hright : g * (-(J * gᴴ * J)) = 1 := mul_eq_one_comm.mp hleft
  have hgJ : g * J * gᴴ = J := by
    have h1 : g * J * gᴴ * J = -1 := by
      have := congrArg Neg.neg hright
      simpa [Matrix.mul_neg, Matrix.mul_assoc] using this
    calc g * J * gᴴ = g * J * gᴴ * J * (-J) := by
            rw [Matrix.mul_assoc (g * J * gᴴ), Matrix.mul_neg, hJJ, neg_neg, Matrix.mul_one]
      _ = J := by rw [h1, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  rw [← Matrix.fromBlocks_toBlocks g] at hgJ
  simp only [J, Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hgJ
  obtain ⟨-, h12, -, h22⟩ := hgJ
  simp only [Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul] at h12 h22
  constructor
  · rw [← neg_inj, neg_sub, ← h12]; abel
  · rw [← sub_eq_zero, ← h22]; abel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_unitary (τ : E →+* ℂ) (γ : M2 E N) (h : γ ∈ UU E N) :
    (γ.map τ)ᴴ * Matrix.J (Fin N) ℂ * γ.map τ = Matrix.J (Fin N) ℂ := by
  have hJ : (Matrix.J (Fin N) E).map τ = Matrix.J (Fin N) ℂ := by
    simpa using Matrix.map_J (Fin N) τ
  have hc : (ccT γ).map τ = (γ.map τ)ᴴ := by
    ext a b
    simp only [ccT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, cc]
    exact IsCMField.complexEmbedding_complexConj E τ _
  have := congrArg (fun M : M2 E N => M.map τ) h
  simpa only [Matrix.map_mul, hJ, hc] using this

end GlobalTheory.SW.HermComp

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem inv_denominator_mul_lower_left_cocycle {N : ℕ}
    {A B C D C' D' Z : Matrix (Fin N) (Fin N) ℂ}
    (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hdet0 : (C * Z + D).det ≠ 0)
    (hdet1 : (C' * ((A * Z + B) * (C * Z + D)⁻¹) + D').det ≠ 0) :
    ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D') * (C * Z + D))⁻¹ * (C' * A + D' * C) =
      (C * Z + D)⁻¹ * ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D')⁻¹ * C') * (Z * Cᴴ + Dᴴ)⁻¹ +
        (C * Z + D)⁻¹ * C := by
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have hadj : (Z * Cᴴ + Dᴴ) * W = Z * Aᴴ + Bᴴ :=
    _root_.GlobalTheory.SW.HAct.den'_act h1 h2 h3 h4 hdet0
  have hinv : (Z * Cᴴ + Dᴴ)⁻¹ = A - W * C := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hadj]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3]
    abel
  have hunit : IsUnit (C' * W + D').det := isUnit_iff_ne_zero.mpr hdet1
  have hC : (C * Z + D)⁻¹ * C = (C * Z + D)⁻¹ * (C' * W + D')⁻¹ * ((C' * W + D') * C) := by
    rw [Matrix.mul_assoc ((C * Z + D)⁻¹), ← Matrix.mul_assoc ((C' * W + D')⁻¹),
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  rw [hinv, Matrix.mul_inv_rev, hC]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem matrix_of_apply_row {m r : Type} {α : Type} (f : m → r → α) (k : m) :
    Matrix.of f k = f k := rfl

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in

theorem _root_.GlobalTheory.SW.transH_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (γ γ' : _root_.GlobalTheory.SW.M2 E N), γ ∈ _root_.GlobalTheory.SW.UU E N → γ' ∈ _root_.GlobalTheory.SW.UU E N → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' = _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) * _root_.GlobalTheory.SW.hFac Ψ γ Z z z') ∧ ∀ φ ψ χ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.TransH Ψ γ φ ψ → _root_.GlobalTheory.SW.TransH Ψ γ' ψ χ → _root_.GlobalTheory.SW.TransH Ψ (γ' * γ) φ χ := by
  intro E _ _ _ Ψ n N γ γ' hγ hγ'
  have key : ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N,
      _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' =
        _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z)
          (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
          (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) *
        _root_.GlobalTheory.SW.hFac Ψ γ Z z z' := by
    intro Z hZ z z'
    obtain ⟨hτ, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
    obtain ⟨-, hden, -⟩ := hcomp γ' hγ'
    have hτ' := ((_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ' hγ').2 _ hmem).1
    unfold _root_.GlobalTheory.SW.hFac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hlow := (_root_.GlobalTheory.SW.HAct.mul_blocks (E := E) (τ : E →+* ℂ) γ γ').2.2.1
    obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.SW.HAct.blocks (by
      rw [← _root_.GlobalTheory.SW.HAct.map_blocks (E := E) (τ : E →+* ℂ) γ]
      exact _root_.GlobalTheory.SW.HAct.map_mem (τ : E →+* ℂ) hγ)
    have hM := inv_denominator_mul_lower_left_cocycle (C' := (toBlocks₂₁ γ').map (τ : E →+* ℂ))
      (D' := (toBlocks₂₂ γ').map (τ : E →+* ℂ)) (Z := Z τ) h1 h2 h3 h4 (hτ τ).1 (hτ' τ).1
    rw [hden τ, Matrix.det_mul, mul_pow, hlow]
    simp only [_root_.GlobalTheory.SW.hDen, _root_.GlobalTheory.SW.hDen',
      _root_.GlobalTheory.SW.hAct] at hM ⊢
    rw [hM]
    simp only [matrix_of_apply_row, Matrix.add_mulVec, dotProduct_add, Finset.sum_add_distrib,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_add,
      Complex.exp_add]
    ring
  refine ⟨key, fun φ ψ χ hφ hψ Z hZ z z' => ?_⟩
  obtain ⟨-, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hact, hden, hadj⟩ := hcomp γ' hγ'
  have hvar : (fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ (γ' * γ) Z τ)⁻¹ *ᵥ z τ k) =
      fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ *ᵥ
          (Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) k := by
    funext τ
    congr 1
    funext k
    rw [hadj τ, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    rfl
  have hvar' : (fun τ => Matrix.of fun k =>
        z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ (γ' * γ) Z τ)⁻¹) =
      fun τ => Matrix.of fun k =>
        (Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) k ᵥ*
          (_root_.GlobalTheory.SW.hDen Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ := by
    funext τ
    congr 1
    funext k
    rw [hden τ, Matrix.mul_inv_rev, ← Matrix.vecMul_vecMul]
    rfl
  rw [hact, hvar, hvar', hψ _ hmem, hφ Z hZ z z', key Z hZ z z', mul_assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootOfUnityPhaseVacuumSiegelThetaTransformStatement
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootOfUnityPhaseVacuum_siegelThetaTransform : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  first | exact @GlobalTheory.Phase.WeilPV.pv_of_transS | exact GlobalTheory.Phase.WeilPV.pv_of_transS | (intros; apply GlobalTheory.Phase.WeilPV.pv_of_transS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatRationalCoordsIntegralProportionalStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by
  first | exact @GlobalTheory.SW.haar_ofQ_proportional | exact GlobalTheory.SW.haar_ofQ_proportional | (intros; apply GlobalTheory.SW.haar_ofQ_proportional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortIsotropicVectorsExistence_succ_of_very_short_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, (∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C) → (∀ (D : ℕ) (ε : ℝ), 0 < D → 0 < ε → ∃ C : ℝ, ShortIso Ψ (N + 1) D ε C) → ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ (N + 1) D 0 C := by
  first | exact @GlobalTheory.SW.shortIso_step | exact GlobalTheory.SW.shortIso_step | (intros; apply GlobalTheory.SW.shortIso_step <;> assumption)
end

