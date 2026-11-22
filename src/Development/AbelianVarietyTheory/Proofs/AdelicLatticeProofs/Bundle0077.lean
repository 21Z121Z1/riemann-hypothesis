import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalPointsFinitePartSelfDualLatticeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.RatSelfDual

variable {D : D7}

def symplB (S T : HSp D) : WO S T →+ WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => symplO S T x y) ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 x))
    (fun x x' => AddMonoidHom.ext fun y => (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 x x' y)

theorem symplO_nsmul (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T x (N • y) = symplO S T (N • x) y := by
  have h1 : symplO S T x (N • y) = N • symplO S T x y := (symplB S T x).map_nsmul N y
  have h2 : symplO S T (N • x) y = N • symplO S T x y := ((symplB S T).flip y).map_nsmul N x
  rw [h1, h2]

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]

theorem psi_real {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1))
    (S T : HSp D) (x y : WO S T) (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    ψ (symplO S T x y) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  rw [symplO_eq_add, AddChar.map_add_eq_mul, GlobalTheory.OrientedChar.char_symplOH D θ ψ hθ hψ S T x y h, ← Complex.exp_add]
  congr 1
  ring

theorem psi_fin_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) *
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨a, ha⟩ := (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.2.2.2 x y
  have h1 : ψ (symplO S T (ratW T S x) (ratW T S y)) = 1 := by rw [ha]; exact hψ.1.2.2.1 a
  have hx : (iotaW σ T S (infRat S T x) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have hy : (iotaW σ T S (infRat S T y) : WO S T).map (finPart D) = 0 := hσ.real_iota T S _
  have e1 := psi_real hθ hψ S T (iotaW σ T S (infRat S T x)) (ratW T S y) (Or.inl hx)
  have e2 := psi_real hθ hψ S T (finRat S T x) (iotaW σ T S (infRat S T y)) (Or.inr hy)
  rw [hσ.pi_iota, piW_ratW hθ] at e1
  rw [piW_of_inf θ (finRat_inf S T x), LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at e2
  have d1 : symplO S T (ratW T S x) (ratW T S y) =
      symplO S T (iotaW σ T S (infRat S T x)) (ratW T S y) + symplO S T (finRat S T x) (ratW T S y) :=
    (congrArg (fun w => symplO S T w (ratW T S y)) (ratW_eq hσ S T x)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1 _ _ _)
  have d2 : symplO S T (finRat S T x) (ratW T S y) =
      symplO S T (finRat S T x) (iotaW σ T S (infRat S T y)) + symplO S T (finRat S T x) (finRat S T y) :=
    (congrArg (fun w => symplO S T (finRat S T x) w) (ratW_eq hσ S T y)).trans ((GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1 _ _ _)
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, one_mul, mul_comm] at h1
  exact h1

theorem psi_fin_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ψ (symplO S T (finRat S T x) (finRat S T y)) = 1 ↔ ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  have h := psi_fin_mul hψ S T x y
  constructor
  · intro h1
    rw [h1, one_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h2 : ((omO S T (infRat S T x) (infRat S T y) : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_left_cancel₀ (neg_ne_zero.2 Complex.two_pi_I_ne_zero)
      rw [hn]; push_cast; ring
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (infRat S T x) (infRat S T y) : ℂ)) = 1 := by
      rw [hk, Complex.exp_eq_one_iff]
      exact ⟨-k, by push_cast; ring⟩
    rwa [h2, mul_one] at h

theorem eq_zero_of_parts {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {z : WO S T}
    (hf : z.map (finPart D) = 0) (hi : z.map (infPart D) = 0) : z = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine hσ.ext _ (congrFun (congrFun hf i) j) fun τ => ?_
  have : infPart D (z i j) = 0 := congrFun (congrFun hi i) j
  rw [this, RingHom.map_zero]

theorem exists_div {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ γ : WO S T, γ.map (infPart D) = 0 ∧ N • γ = u := by
  refine ⟨Matrix.of fun i j => incA D ((N : D.host.E)⁻¹) * u i j, ?_, ?_⟩
  · funext i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    show infPart D (incA D ((N : D.host.E)⁻¹) * u i j) = 0
    rw [RingHom.map_mul, this, mul_zero]
  · funext i j
    show N • (incA D ((N : D.host.E)⁻¹) * u i j) = u i j
    have h1 : (N : AE D) = incA D (N : D.host.E) := (map_natCast (incA D) N).symm
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, h1, ← map_mul, mul_inv_cancel₀ h2, map_one, one_mul]

theorem finRat_mem_iff : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)), IsStdChar D ψ (-1) → (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)) → (∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0) → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ) → ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T x ∈ Λ ↔ ∀ y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finRat S T y ∈ Λ → ∃ k : ℤ, omO S T (infRat S T x) (infRat S T y) = k := by
  intro D S T ψ Λ hψ hinf hdual happ hden x
  constructor
  · intro hx y hy
    exact (psi_fin_iff hψ S T x y).1 ((hdual _ (finRat_inf S T x)).1 hx _ hy)
  · intro h
    refine (hdual _ (finRat_inf S T x)).2 fun u' hu' => ?_
    obtain ⟨θ, hθ⟩ := hψ.2.1
    obtain ⟨N, hN, hNx⟩ := hden x
    obtain ⟨γ, hγ, hNγ⟩ := exists_div (hinf u' hu') hN
    obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
    have hz0 : γ - finRat S T y₀ - u = 0 := by
      refine eq_zero_of_parts hθ ?_ ?_
      · funext i j
        have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
        have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
        show finPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub] at e0 ⊢
        rw [e1, e0]
      · funext i j
        have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
        have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
        have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
        show infPart D (γ i j - finRat S T y₀ i j - u i j) = 0
        rw [RingHom.map_sub, RingHom.map_sub, e0, e1, e2, sub_zero, sub_zero]
    have hγe : γ = finRat S T y₀ + u := by
      rw [sub_sub] at hz0
      exact sub_eq_zero.1 hz0
    have hu'e : u' = finRat S T (N • y₀) + N • u := by
      rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]
    have hmem : finRat S T (N • y₀) ∈ Λ := by
      have : finRat S T (N • y₀) = u' - N • u := (sub_eq_of_eq_add hu'e).symm
      rw [this]
      exact Λ.sub_mem hu' (Λ.nsmul_mem hu N)
    rw [hu'e, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).2.1, AddChar.map_add_eq_mul, (psi_fin_iff hψ S T x _).2 (h _ hmem), one_mul,
      symplO_nsmul]
    exact (hdual _ (hinf _ hNx)).1 hNx u hu

end GlobalTheory.RatSelfDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticAdelicForm_biadditive_alternating_rational : ∀ (D : D7) (S T : HSp D), (∀ x x' y : WO S T, symplO S T (x + x') y = symplO S T x y + symplO S T x' y) ∧ (∀ x y y' : WO S T, symplO S T x (y + y') = symplO S T x y + symplO S T x y') ∧ (∀ x y : WO S T, symplO S T x y = -symplO S T y x) ∧ (∀ x : WO S T, symplO S T x x = 0) ∧ ∀ γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  first | exact @GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt | exact GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt | (intros; apply GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisOrtho

open GlobalTheory.SplitScalar

theorem setIntegral_add_right {G E : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : G → E)
    (hp : ∀ γ ∈ Γ, ∀ w, h (γ + w) = h w) (u : G) : ∫ w in 𝓕, h (w + u) ∂μ = ∫ w in 𝓕, h w ∂μ := by
  have h1 : IsAddFundamentalDomain Γ (u +ᵥ 𝓕) μ := h𝓕.vadd_of_comm u
  rw [h𝓕.setIntegral_eq h1 (f := h) fun γ w => hp γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) h 𝓕
  simp only [add_comm _ u]
  exact h2.symm

theorem integral_norm_sq_sum {X ι : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (s : Finset ι)
    (g : ι → X → ℂ) (c : ι → ℂ) (C : ℝ) (hm : ∀ i, Measurable (g i)) (hC : ∀ i x, ‖g i x‖ ≤ C)
    (hc : ∀ i ∈ s, ‖c i‖ = 1) (h1 : ∀ i ∈ s, ∫ x, ‖g i x‖ ^ 2 ∂ν = 1)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ x, g i x * (starRingEnd ℂ) (g j x) ∂ν = 0) :
    ∫ x, ‖(∑ i ∈ s, c i • g i) x‖ ^ 2 ∂ν = (s.card : ℝ) := by
  classical
  have hi : ∀ i j, Integrable (fun x => g i x * (starRingEnd ℂ) (g j x)) ν := fun i j => by
    refine Integrable.of_bound (((hm i).mul (Complex.continuous_conj.measurable.comp (hm j))).aestronglyMeasurable)
      (C * C) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC i x) (hC j x) (norm_nonneg _) ((norm_nonneg _).trans (hC i x))
  have e : ∀ x, ((‖(∑ i ∈ s, c i • g i) x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j)) * (g i x * (starRingEnd ℂ) (g j x)) := fun x => by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hi i j).const_mul _,
    Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_congr rfl fun i hi' => ?_
  rw [integral_finset_sum _ fun j _ => (hi i j).const_mul _, Finset.sum_eq_single i]
  · rw [integral_const_mul, Complex.mul_conj', hc i hi']
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, h1 i hi']
    simp
  · intro j hj hji
    rw [integral_const_mul, h0 i hi' j hj hji.symm, mul_zero]
  · exact fun h => absurd hi' h

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_quasi {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) (γ : WO S T) (hγ : γ ∈ ratL T S)
    (w : WO S T) : heisO ψ S T u f (γ + w) = ψ (-(symplOH S T γ w)) * heisO ψ S T u f w := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hf.quasi γ (w + u)
  show ψ (symplOH S T (ratW T S γ + w) u) * f (ratW T S γ + w + u) =
    ψ (-(symplOH S T (ratW T S γ) w)) * (ψ (symplOH S T w u) * f (w + u))
  rw [add_assoc, h, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    symplOH_add_left, symplOH_add_right]
  congr 2
  abel

theorem continuous_heisO (hψ : IsCharAF D.host.F ψ) {f : WO S T → ℂ} (hf : Continuous f) (u : WO S T) :
    Continuous (heisO ψ S T u f) :=
  (hψ.1.comp (continuous_const.mul (continuous_symplO S T continuous_id continuous_const))).mul
    (hf.comp (continuous_id.add continuous_const))

theorem norm_heisO (hψ : IsCharAF D.host.F ψ) (f : WO S T → ℂ) (u w : WO S T) :
    ‖heisO ψ S T u f w‖ = ‖f (w + u)‖ := by
  rw [heisO, norm_mul, hψ.2.1, one_mul]

theorem mul_conj_of_norm_one {z : ℂ} (h : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj', h]; simp

theorem thetaNormSq_sum_heisenbergTranslates_distinctChars (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsCharAF D.host.F ψ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : IsCovolOne (ratL T S) μ 𝓕) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (hn : nrm2 μ 𝓕 f = 1) (ι : Type) (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ)
    (hc : ∀ i ∈ s, ‖c i‖ = 1)
    (hl : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ (l : WO S T) (ε : ℂ), ‖ε‖ = 1 ∧ heisO ψ S T l f = ε • f ∧
      ψ (symplO S T (a i - a j) l) ≠ 1) :
    nrm2 μ 𝓕 (∑ i ∈ s, c i • heisO ψ S T (a i) f) = (s.card : ℝ) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨hμ, h𝓕, h1⟩ := hμ
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    rintro _ ⟨γ, rfl⟩ w
    exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  have hC' : ∀ w, ‖f w‖ ≤ C := fun w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  refine integral_norm_sq_sum (μ.restrict 𝓕) s (fun i => heisO ψ S T (a i) f) c C
    (fun i => (continuous_heisO hψ hf.cont _).measurable) (fun i x => by rw [norm_heisO hψ]; exact hC' _) hc
    (fun i _ => ?_) fun i hi j hj hij => ?_
  · simp_rw [norm_heisO hψ]
    exact (setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕 (fun w => ‖f w‖ ^ 2)
      (fun γ hγ w => by simp only [hp γ hγ w]) (a i)).trans hn
  · obtain ⟨l, ε, hε, he, hne⟩ := hl i hi j hj hij
    have ev : ∀ b w, ψ (symplOH S T w l) * heisO ψ S T b f (w + l) =
        ψ (symplO S T l b) * (ε * heisO ψ S T b f w) := fun b w => by
      have := congrFun (heisO_comm ψ S T l b f) w
      rw [he, heisO_smul] at this
      exact this
    have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
      (fun w => heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w)) (fun γ hγ w => by
        have := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T γ w)))
        simp only [heisO_quasi hf _ γ hγ, map_mul]
        linear_combination (heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w)) * this) l
    have hκ : ψ (symplO S T (a i - a j) l) * (ψ (symplO S T l (a i)) * (starRingEnd ℂ) (ψ (symplO S T l (a j)))) = 1 := by
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, symplO_sub_left, symplO_skew S T l (a i), symplO_skew S T l (a j),
        show -symplO S T l (a i) - -symplO S T l (a j) + symplO S T l (a i) = symplO S T l (a j) by abel]
      exact mul_conj_of_norm_one (hψ.2.1 _)
    have e : ∀ w, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) =
        ψ (symplO S T (a i - a j) l) *
          (heisO ψ S T (a i) f (w + l) * (starRingEnd ℂ) (heisO ψ S T (a j) f (w + l))) := fun w => by
      have e1 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T w l))
      have e2 := mul_conj_of_norm_one hε
      have e3 := ev (a i) w
      have e4 := congrArg (starRingEnd ℂ) (ev (a j) w)
      rw [map_mul, map_mul, map_mul] at e4
      have e5 := congrArg₂ (· * ·) e3 e4
      rw [mul_mul_mul_comm, e1, one_mul] at e5
      rw [e5, mul_mul_mul_comm (ψ _), ← mul_assoc, hκ, one_mul, mul_mul_mul_comm, e2, one_mul]
    have k2 : ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ =
        ψ (symplO S T (a i - a j) l) *
          ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ := by
      conv_rhs => rw [← key, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall e)
    have k3 : (ψ (symplO S T (a i - a j) l) - 1) *
        ∫ w in 𝓕, heisO ψ S T (a i) f w * (starRingEnd ℂ) (heisO ψ S T (a j) f w) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← k2, sub_self]
    exact (mul_eq_zero.1 k3).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.HeisOrtho

end
end

