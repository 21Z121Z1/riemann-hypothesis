import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import ReciprocityTheory.DualLattices.UpBrChar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousRepSmoothOnUH
section
noncomputable section

open MeasureTheory Matrix Topology
open scoped ContDiff

namespace GlobalTheory.UHContSmooth

variable {n : ℕ}

def grp (H : Matrix (Fin n) (Fin n) ℂ) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | (g : Matrix (Fin n) (Fin n) ℂ) ∈ PI.UpqRep.UH H}
  mul_mem' := by
    intro g h hg hh
    have hg' : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * g = H := hg
    have hh' : (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * h = H := hh
    show (g.1 * h.1)ᴴ * H * (g.1 * h.1) = H
    rw [conjTranspose_mul]
    calc (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H *
          ((g : Matrix (Fin n) (Fin n) ℂ) * h)
        = (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = H := by rw [hg', hh']
  one_mem' := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * 1 = H
    simp
  inv_mem' := by
    intro g hg
    have hg' : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * g = H := hg
    show ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * H *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = H
    have h1 : ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (g : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv g
    calc ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * H *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * H * g) *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg']
      _ = H := by
          rw [show ∀ A B C D E : Matrix (Fin n) (Fin n) ℂ, A * (B * C * D) * E = (A * B) * C * (D * E)
            from fun A B C D E => by simp only [Matrix.mul_assoc], h1, h2, Matrix.one_mul, Matrix.mul_one]

def mat {H : Matrix (Fin n) (Fin n) ℂ} (g : grp H) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem left_inv {H : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ PI.UpqRep.UH H) : (H * gᴴ * H) * g = 1 := by
  have hg' : gᴴ * H * g = H := hg
  calc (H * gᴴ * H) * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hH]

theorem range_mat {H : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) :
    Set.range (mat (H := H)) = PI.UpqRep.UH H := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact u.2
  · intro hg
    have h2 := left_inv hH hg
    exact ⟨⟨⟨g, H * gᴴ * H, mul_eq_one_comm.mp h2, h2⟩, hg⟩, rfl⟩

theorem isClosedEmbedding_mat {H : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) :
    IsClosedEmbedding (mat (H := H)) := by
  have hc : Continuous (mat (H := H)) := Units.continuous_val.comp continuous_subtype_val
  let f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun g => (g, MulOpposite.op (H * gᴴ * H))
  have hf : Continuous f :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ mat (H := H)
      = Units.embedProduct _ ∘ (Subtype.val : grp H → (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
    funext g
    simp only [Function.comp_apply, f, Units.embedProduct_apply]
    rw [Units.inv_eq_of_mul_eq_one_left (left_inv hH (g := mat g) g.2)]
    rfl
  have hi : IsInducing (mat (H := H)) := by
    refine IsInducing.of_comp hc hf ?_
    rw [hcomp]
    exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal
  refine ⟨⟨hi, fun a b h => Subtype.ext (Units.ext h)⟩, ?_⟩
  rw [range_mat hH]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_contDiff {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix (Fin n) (Fin n) ℂ}
    {ρ : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ} (hH : H * H = 1) (h1 : ρ 1 = 1)
    (hmul : ∀ g ∈ PI.UpqRep.UH H, ∀ h ∈ PI.UpqRep.UH H, ρ (g * h) = ρ g * ρ h)
    (hcont : ContinuousOn ρ (PI.UpqRep.UH H)) (x₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ F : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ, ContDiff ℝ ∞ F ∧
      ∀ x ∈ Metric.ball x₀ 1, x ∈ PI.UpqRep.UH H → ρ x = F x := by
  have hemb := isClosedEmbedding_mat hH
  have hrange := range_mat hH
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have : LocallyCompactSpace (grp H) := hemb.locallyCompactSpace
  have : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  have : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℂ _
  borelize ↥(grp H)
  set μ : Measure (grp H) := Measure.haar
  have hmem : ∀ g : grp H, mat g ∈ PI.UpqRep.UH H := fun g => g.2
  have hu : Continuous (mat (H := H)) := hemb.continuous
  have hb : Continuous fun g : grp H => ρ (mat g) := hcont.comp_continuous hu hmem
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ PI.UpqRep.UH H := hmem 1
  have hnb : {g | ‖ρ g - 1‖ < 1 / 2} ∈ 𝓝[PI.UpqRep.UH H] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hcont 1 hone) (Metric.ball_mem_nhds _ (half_pos one_pos))
    simpa [h1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφU, hφc, hφ, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hψ : Continuous fun g : grp H => φ (mat g) := hφ.continuous.comp hu
  have hψc : HasCompactSupport fun g : grp H => φ (mat g) := hφc.comp_isClosedEmbedding hemb
  have hcs : HasCompactSupport fun g : grp H => φ (mat g) • ρ (mat g) := hψc.smul_right
  have hcn : Continuous fun g : grp H => φ (mat g) • ρ (mat g) := hψ.smul hb
  have hint := Continuous.integrable_of_hasCompactSupport (E := Matrix ι ι ℂ) (μ := μ) hcn hcs
  have hψi : Integrable (fun g : grp H => φ (mat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : grp H, φ (mat g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  set c := ∫ g : grp H, φ (mat g) ∂μ with hc
  set M := ∫ g : grp H, φ (mat g) • ρ (mat g) ∂μ with hM
  have hMu : IsUnit M := by
    have e1 : ∫ g : grp H, (φ (mat g) • ρ (mat g) - φ (mat g) • (1 : Matrix ι ι ℂ)) ∂μ
        = M - c • (1 : Matrix ι ι ℂ) := by
      rw [integral_sub hint (hψi.smul_const _), integral_smul_const]
    have e2 : ‖∫ g : grp H, (φ (mat g) • ρ (mat g) - φ (mat g) • (1 : Matrix ι ι ℂ)) ∂μ‖
        ≤ ∫ g : grp H, φ (mat g) * (1 / 2) ∂μ := by
      refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : φ (mat g) = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs ⟨hφU (subset_tsupport _ hg), hmem g⟩)) (hφ0 _)
    rw [e1, integral_mul_const, ← hc] at e2
    have e3 : ‖-(c⁻¹ • (M - c • (1 : Matrix ι ι ℂ)))‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_of_nonneg (inv_pos.2 hpos).le, inv_mul_lt_iff₀ hpos]
      linarith
    have e4 := isUnit_one_sub_of_norm_lt_one e3
    have e5 : M = (c • (1 : Matrix ι ι ℂ)) * (1 - -(c⁻¹ • (M - c • (1 : Matrix ι ι ℂ)))) := by
      rw [Matrix.smul_mul, Matrix.one_mul, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hpos.ne',
        one_smul]
      abel
    rw [e5]
    refine IsUnit.mul (IsUnit.of_mul_eq_one (c⁻¹ • (1 : Matrix ι ι ℂ)) ?_) e4
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  obtain ⟨N, hN⟩ := hMu.exists_right_inv
  let y : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun x => H * xᴴ * H
  have hy : ContDiff ℝ ∞ y := (contDiff_const.mul GlobalTheory.GardingVec.contDiff_conjTranspose).mul contDiff_const
  have hform : ∀ x ∈ PI.UpqRep.UH H, ρ x * M = ∫ g : grp H, φ (y x * mat g) • ρ (mat g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (mat (H := H)) := by rw [hrange]; exact hx
    have e0 := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ) (ρ x)) hint
    simp only [ContinuousLinearMap.mul_apply'] at e0
    rw [hM, ← e0,
      ← integral_mul_left_eq_self (fun g : grp H => φ (y x * mat g) • ρ (mat g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : mat (z * g) = x * mat g := by rw [← hz]; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, show y x * x = 1 from left_inv hH hx, Matrix.one_mul, hmul _ hx _ (hmem g),
      Matrix.mul_smul]
  have hC : IsCompact (Set.image2 (· * ·) (Metric.closedBall x₀ 1) (tsupport φ)) :=
    (isCompact_closedBall x₀ 1).mul hφc
  have hK := hemb.isCompact_preimage hC
  have hs : ContDiff ℝ ∞ fun x => ∫ g in (mat (H := H)) ⁻¹'
      (Set.image2 (· * ·) (Metric.closedBall x₀ 1) (tsupport φ)), φ (y x * mat g) • ρ (mat g) ∂μ :=
    contDiff_infty.2 fun m => GlobalTheory.GardingVec.contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
      (fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × Matrix ι ι ℂ) =>
        φ (y z.1 * z.2.1) • z.2.2)
      ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
        (contDiff_snd.comp contDiff_snd))
  refine ⟨_, hs.mul (contDiff_const (c := N)), fun x hx hxG => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_, ← hform x hxG, Matrix.mul_assoc, hN,
    Matrix.mul_one]
  by_contra hne
  refine hg ⟨x, Metric.ball_subset_closedBall hx, y x * mat g,
    subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
  show x * (y x * mat g) = mat g
  rw [← Matrix.mul_assoc, show x * y x = 1 from mul_eq_one_comm.1 (left_inv hH hxG), Matrix.one_mul]

theorem exists_contDiff_entry {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix (Fin n) (Fin n) ℂ}
    {ρ : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ} (hH : H * H = 1) (h1 : ρ 1 = 1)
    (hmul : ∀ g ∈ PI.UpqRep.UH H, ∀ h ∈ PI.UpqRep.UH H, ρ (g * h) = ρ g * ρ h)
    (hcont : ∀ i j, ContinuousOn (fun g => ρ g i j) (PI.UpqRep.UH H)) (i j : ι)
    (x₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : (Fin n → Fin n → ℂ) → ℂ), IsOpen U ∧ x₀ ∈ U ∧
      ContDiff ℝ ∞ F ∧ ∀ x ∈ U, x ∈ PI.UpqRep.UH H → ρ x i j = F (Matrix.of.symm x) := by
  obtain ⟨F, hF, hFe⟩ := exists_contDiff hH h1 hmul
    (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont i j) x₀
  let A : (Fin n → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => Matrix.of p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let B : Matrix ι ι ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun m => m i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨Metric.ball x₀ 1, fun p => B (F (A p)), Metric.isOpen_ball, Metric.mem_ball_self one_pos,
    (LinearMap.toContinuousLinearMap B).contDiff.comp
      (hF.comp (LinearMap.toContinuousLinearMap A).contDiff), fun x hx hxG => ?_⟩
  rw [hFe x hx hxG]
  rfl

end

theorem smoothOnH_of_continuousOn : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Matrix (Fin n) (Fin n) ℂ) (ρ : Matrix (Fin n) (Fin n) ℂ → Matrix ι ι ℂ), H * H = 1 → ρ 1 = 1 →
    (∀ g ∈ PI.UpqRep.UH H, ∀ h ∈ PI.UpqRep.UH H, ρ (g * h) = ρ g * ρ h) →
    (∀ i j, ContinuousOn (fun g => ρ g i j) (PI.UpqRep.UH H)) →
    ∀ i j, PI.UpqRep.SmoothOnH H (fun g => ρ g i j) := by
  intro n ι _ _ H ρ hH h1 hmul hcont i j x₀ _
  obtain ⟨U, F, hU, hx, hF, hFe⟩ := exists_contDiff_entry hH h1 hmul hcont i j x₀
  exact ⟨U, F, hU, hx, hF.contDiffOn, hFe⟩

end GlobalTheory.UHContSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_ringHom_ringOfIntegers_lift {E : Type} [Field E] [NumberField E] {V K : Type} [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] [Field K] [Algebra V K] [IsFractionRing V K] (φ : 𝓞 E →+* K) :
    ∃ ψ : 𝓞 E →+* V, ∀ a, algebraMap V K (ψ a) = φ a := by
  have hint : ∀ a, ∃ x : V, algebraMap V K x = φ a := by
    intro a
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral ℤ (φ a) := map_isIntegral_int φ h1
    exact IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top
  choose f hf using hint
  have hinj := IsFractionRing.injective V K
  refine ⟨{ toFun := f
            map_one' := hinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := hinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [map_add, hf, hf, hf, map_add]) }, hf⟩

theorem exists_types_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ (τT : (E →+* ℂ) → (𝓞 E →+* T.V)), (∀ τ a, algebraMap T.V T.Fr (τT τ a) = io (embK c τ a)) ∧ IsTypes X io (fun τ => X.ι.comp (τT τ)) ∧ Function.Injective (fun τ => X.ι.comp (τT τ)) ∧ (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ X.ι (τT τ H.rt) = X.ι (τT τ' H.rt)) ∧ ∀ τ a, τT (ComplexEmbedding.conjugate τ) a = τT τ (H.bar a) := by
  intro E _ _ _ H l c T io p _ X
  have hinj := IsFractionRing.injective T.V T.Fr
  choose σV hσV using fun τ : E →+* ℂ =>
    exists_ringHom_ringOfIntegers_lift (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hT : ∀ τ a, algebraMap X.O X.C (X.ι (σV τ a)) = X.ιF (io (embK c τ a)) := by
    intro τ a
    rw [← X.comp, hσV']
  have key : ∀ τ τ' (a : 𝓞 E), τ (a : E) = τ' (a : E) ↔ X.ι (σV τ a) = X.ι (σV τ' a) := by
    intro τ τ' a
    constructor
    · intro h
      have h1 : embK c τ a = embK c τ' a := by
        apply Subtype.ext
        rw [embK_coe, embK_coe]
        exact h
      have h2 : σV τ a = σV τ' a := hinj (by rw [hσV', hσV', h1])
      rw [h2]
    · intro h
      have h1 : embK c τ a = embK c τ' a :=
        io.injective (X.ιF.injective (by rw [← hT, ← hT, h]))
      exact congrArg (fun z : c.F => (z : ℂ)) h1
  refine ⟨σV, hσV', hT, ?_, fun τ τ' => key τ τ' H.rt, fun τ a => ?_⟩
  · intro τ τ' h
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    exact (key τ τ' a).2 (RingHom.congr_fun h a)
  · have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    exact hinj (by rw [hσV', hσV', h])

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColength
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
open ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CharDepth

theorem det_dvd_det_of_trunc_mem_span {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R)
    (h : ∀ j, (fun a : Fin n => A a.castSucc j) ∈ Submodule.span R (Set.range fun i => fun a => B a i)) :
    B.det ∣ A.det := by
  choose X hX using fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (h j)
  rw [Matrix.det_succ_row A (Fin.last n)]
  refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
  have e : A.submatrix (Fin.last n).succAbove j.succAbove = B * Matrix.of (fun i k => X (j.succAbove k) i) := by
    ext a k
    have := congrFun (hX (j.succAbove k)) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.submatrix_apply, Fin.succAbove_last, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, Matrix.det_mul]
  exact Dvd.intro _ rfl

theorem minor_dvd_minor {R : Type} [CommRing R] {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (ι : Fin g → Fin N)
    (hι : ∀ s (hs : s ≤ g), Submodule.span R (Set.range fun b : Fin s => fun a : Fin s =>
      M (Fin.castLE hs a) (ι (Fin.castLE hs b))) = omTr M s hs)
    (n m : ℕ) (hnm : n ≤ m) (hm : m ≤ g) :
    (Matrix.of fun a b : Fin n => M (Fin.castLE (hnm.trans hm) a) (ι (Fin.castLE (hnm.trans hm) b))).det ∣
      (Matrix.of fun a b : Fin m => M (Fin.castLE hm a) (ι (Fin.castLE hm b))).det := by
  induction m, hnm using Nat.le_induction with
  | base => exact dvd_rfl
  | succ m hnm ih =>
    refine (ih (Nat.le_of_succ_le hm)).trans (det_dvd_det_of_trunc_mem_span _ _ fun j => ?_)
    have h := hι m (Nat.le_of_succ_le hm)
    have h2 : (fun a : Fin m => M (Fin.castLE (Nat.le_of_succ_le hm) a) (ι (Fin.castLE hm j))) ∈
        omTr M m (Nat.le_of_succ_le hm) := Submodule.subset_span ⟨_, rfl⟩
    rw [← h] at h2
    exact h2

theorem exists_smul_eq_zero_of_hasLen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) (hx : x ≠ 0) : x ≤ 1 ∧ ∃ c : R, c ≠ 0 ∧ ∀ m : M, c • m = 0 := by
  obtain ⟨m, c, ⟨e⟩, hc⟩ := h
  have hc' : v (algebraMap R C (∏ i, c i)) = x := by rw [map_prod, map_prod, hc]
  refine ⟨hc' ▸ hv.map_le_one _, ∏ i, c i, ?_, fun z => ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hc'
    exact hx hc'.symm
  · apply e.injective
    rw [map_smul, map_zero]
    funext i
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e z i)
    rw [Pi.smul_apply, ← hy, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem c (Finset.mem_univ i)).mul_right y)

theorem exists_flag_characters (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    (hv : v.Integers O) (d s : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O) (x : NNReal)
    (h : HasAF v F w x) (hx : x ≠ 0) :
    x ≤ 1 ∧ ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, x ≤ v (algebraMap O C
      (Matrix.of fun a b : Fin (i.val + 1) =>
        ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  obtain ⟨N, u, hu, hlen⟩ := h
  obtain ⟨hx1, c, hc, hkill⟩ := exists_smul_eq_zero_of_hasLen hv hlen hx
  refine ⟨hx1, ?_⟩
  let M : Matrix (Fin s) (Fin N) O := fun a k => res w (dl (u k)) a
  have hom : omTr M s le_rfl = Submodule.span O (Set.range fun k => res w (dl (u k))) := rfl
  have hspan : ∀ n (hn : n ≤ s), ∀ y : Fin n → O, c • y ∈ omTr M n hn := by
    intro n hn y
    let y' : Fin s → O := Function.extend (Fin.castLE hn) y 0
    have h1 : c • y' ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hkill _
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
    refine (Submodule.mem_span_range_iff_exists_fun O).2 ⟨r, ?_⟩
    funext a
    have h2 := congrFun hr (Fin.castLE hn a)
    have h3 : y' (Fin.castLE hn a) = y a := (Fin.castLE_injective hn).extend_apply y 0 a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3] at h2 ⊢
    exact h2
  obtain ⟨ι, -, hι⟩ := charThm C v O hv s N M c hc hspan
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  have hfull := char_len hv M ι s le_rfl (hι s le_rfl)
  rw [hom] at hfull
  have hxe := hasLen_unique hv hlen hfull
  refine ⟨fun b => u (ι b), fun b => hu _, fun i => ?_⟩
  have hd := hv.le_of_dvd (minor_dvd_minor M ι hι (i.val + 1) s i.isLt le_rfl)
  rw [← hxe] at hd
  exact hd

end GlobalTheory.CharDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalBiextensionIntegralChartValuedExtens
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharDepth

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ in

theorem isCanonGauge_mapFB_tower {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) {h : PS k 2 d} {R' : Type} [CommRing R'] [Algebra R' k]
    (φ : R →+* R') (hφ : ∀ x, algebraMap R' k (φ x) = algebraMap R k x) (hh : B.IsCanonGauge k h) :
    (FBMap.mapFB φ B).IsCanonGauge k h := by
  have hK : ∀ {n : ℕ} (f : PS R n d), FB.toK k (MvPowerSeries.map φ f) = FB.toK k f := by
    intro n f
    ext mo
    simp only [MvPowerSeries.coeff_map, hφ]
  have hF : (FBMap.mapFB φ B).FK k = B.FK k := funext fun _ => hK _
  have hA : (FBMap.mapFB φ B).actK k = B.actK k := funext fun _ => funext fun _ => hK _
  refine ⟨hh.ax0, hh.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF]; exact (hK _).trans hh.ph1
  · rw [hF]; exact (hK _).trans hh.ph2
  · exact (hK _).trans hh.sy
  · rw [hA]; exact (hK _).trans (hh.ad a)

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_formalBiext_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ B : FB X.O (chD Ch.ch) (𝓞 E), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) ∧
      (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) ∧
      B.IsCanonGauge X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X
  letI := io.toAlgebra
  obtain ⟨BT, e1, e2, -, -, -, -, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨-, -, h3, h4⟩ := e7 X.C
  refine ⟨FBMap.mapFB X.ι BT, ?_, fun a => ?_,
    isCanonGauge_mapFB_tower BT X.ι (fun x => (X.comp x).symm) ((h3 _).2 h4)⟩
  · rw [← e1]; rfl
  · rw [← e2]; rfl

end GlobalTheory.CharDepth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
section
set_option autoImplicit false

namespace GlobalTheory.CharDepth

open IsLocalRing Formalism.L2.Pj

theorem exists_local_extension_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O) (φ : A →+* B) (hφ : Function.Injective φ)
    (hint : φ.IsIntegral) (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_21; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 v hv φ hφ hint ι h_21 hι; exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension)
  | exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | (apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension ..)

theorem ValExt.exists_local_extension :
    ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∀ (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ ι' : T'.V →+* X.O, IsLocalHom ι' ∧ ι'.comp φ = X.ι := by
  intro T T' φ hφ hfin p _ X
  haveI := X.ι_local
  refine exists_local_extension_of_integral X.v X.ints φ hφ hfin.to_isIntegral X.ι ?_
  have h : (algebraMap X.O X.C).comp X.ι = X.ιF.comp (algebraMap T.V T.Fr) := by
    ext x; exact (X.comp x).symm
  rw [h, RingHom.coe_comp]
  exact X.ιF.injective.comp (IsFractionRing.injective T.V T.Fr)

end GlobalTheory.CharDepth
end

