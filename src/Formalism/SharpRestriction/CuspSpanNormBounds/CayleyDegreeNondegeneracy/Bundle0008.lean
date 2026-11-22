import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InnerMemOneOfMemDualOrthLattice

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DegIsFdegCayley
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory
open scoped InnerProductSpace ENNReal Matrix

section Gen

variable {n : ℕ} {ε : Fin n → Bool}

theorem deg_fdegOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (w : H)
    (h : IsFdeg μ σ d) (hw : w ≠ 0) : fdegOf μ σ w = d := by
  obtain ⟨hd, hall⟩ := h
  have hint := (hall w w w w).2
  have e1 : ∀ g : Formalism.REAL.UJ ε, coefOn σ w w g * star (coefOn σ w w g) =
      (((‖coefOn σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    intro g
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast
    rfl
  simp only [e1] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have key : (∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ : ℝ) = ‖w‖ ^ 4 / d := by
    have h3 : ((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / (d : ℂ)) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      push_cast
      ring
    have h2 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := hint.trans h3
    exact_mod_cast h2
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  unfold fdegOf
  rw [key]
  field_simp

theorem deg_fdegOf_equiv {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (m : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)) (v : H) : fdegOf m σ v = fdegOf m σ' (U v) := by
  have hi : ∀ g : Formalism.REAL.UJ ε, coefOn σ' (U v) (U v) g = coefOn σ v v g := by
    intro g
    unfold coefOn
    rw [← hU (umat g) (by exact g.2) v, U.inner_map_map]
  unfold fdegOf
  simp only [hi, U.norm_map]

theorem deg_fdegOf_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (c : NNReal) (hc : 0 < c)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) :
    fdegOf (Formalism.REAL.muG ε) σ v = (c : ℝ) * fdegOf (((c : NNReal) : ℝ≥0∞) • Formalism.REAL.muG ε) σ v := by
  unfold fdegOf
  rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← mul_div_assoc, mul_div_mul_left _ _ hc']

theorem deg_inner_isom {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  let T' : H →ₗᵢ[ℂ] H := { toLinearMap := T.toLinearMap, norm_map' := hT }
  T'.inner_map_map x y

theorem deg_UJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  simp only [UJset, Set.mem_setOf_eq] at *
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc] at *
  rw [← Matrix.mul_assoc _ a b, ← Matrix.mul_assoc aᴴ _ b, ha]
  exact hb

end Gen

theorem deg_isFdeg_cayley {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (m : Measure (Formalism.REAL.UJ ε))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (P P' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayley k r ε P) (hP' : IsCayley k r ε P')
    (hrep : IsURepOn (UJset ε) (fun g => σ (P'⁻¹ * g * P'))) (d : ℝ)
    (hd : IsFdeg m (fun g => σ (P⁻¹ * g * P)) d) : IsFdeg m (fun g => σ (P'⁻¹ * g * P')) d := by
  obtain ⟨hPu, hPJ⟩ := hP
  obtain ⟨hPu', hPJ'⟩ := hP'
  obtain ⟨⟨hσ1, hσmul⟩, hiso, -⟩ := hrep
  have h1 : σ (P'⁻¹ * 1 * P') = 1 := hσ1
  have hm : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      σ (P'⁻¹ * (a * b) * P') = (σ (P'⁻¹ * a * P')).comp (σ (P'⁻¹ * b * P')) := hσmul
  have hiso' : ∀ g ∈ UJset ε, ∀ x : H, ‖σ (P'⁻¹ * g * P') x‖ = ‖x‖ := hiso
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hdet' : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det P').1 hPu'
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPPi' : P' * P'⁻¹ = 1 := Matrix.mul_nonsing_inv P' hdet'
  have hPiP' : P'⁻¹ * P' = 1 := Matrix.nonsing_inv_mul P' hdet'
  have hmem : ∀ A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Aᴴ * Formalism.REAL.Jm ε * A = Formalism.QuantumDeterminants.Hpk k r → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.QuantumDeterminants.Hpk k r →
      B * B⁻¹ = 1 → A * B⁻¹ ∈ UJset ε := by
    intro A B hA hB hBB
    show (A * B⁻¹)ᴴ * Formalism.REAL.Jm ε * (A * B⁻¹) = Formalism.REAL.Jm ε
    have hB1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBB, Matrix.conjTranspose_one]
    calc (A * B⁻¹)ᴴ * Formalism.REAL.Jm ε * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * Formalism.REAL.Jm ε * A) * B⁻¹ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm ε * B) * B⁻¹ := by rw [hA, hB]
      _ = ((B⁻¹)ᴴ * Bᴴ) * Formalism.REAL.Jm ε * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hB1, hBB, Matrix.one_mul, Matrix.mul_one]
  have hQ : P * P'⁻¹ ∈ UJset ε := hmem P P' hPJ hPJ' hPPi'
  have hQi : P' * P⁻¹ ∈ UJset ε := hmem P' P hPJ' hPJ hPPi
  have hQQi : P * P'⁻¹ * (P' * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P'⁻¹, hPiP', Matrix.one_mul, hPPi]
  have hBC : ∀ x : H, σ (P'⁻¹ * (P * P'⁻¹) * P') (σ (P'⁻¹ * (P' * P⁻¹) * P') x) = x := by
    intro x
    have e := congrArg (fun T : H →L[ℂ] H => T x) (hm _ hQ _ hQi)
    simp only [ContinuousLinearMap.comp_apply, hQQi, h1, one_apply_eq_self] at e
    exact e.symm
  have hcoef : ∀ a b : H, coefOn (ε := ε) (fun g => σ (P'⁻¹ * g * P')) a b =
      coefOn (ε := ε) (fun g => σ (P⁻¹ * g * P)) (σ (P'⁻¹ * (P' * P⁻¹) * P') a)
        (σ (P'⁻¹ * (P' * P⁻¹) * P') b) := by
    intro a b
    funext g
    unfold coefOn
    beta_reduce
    have hg : umat g ∈ UJset ε := by exact g.2
    have hconj : P⁻¹ * umat g * P = P'⁻¹ * (P' * P⁻¹ * umat g * (P * P'⁻¹)) * P' := by
      simp only [← Matrix.mul_assoc, hPiP', Matrix.one_mul]
      rw [Matrix.mul_assoc _ P'⁻¹ P', hPiP', Matrix.mul_one]
    rw [hconj, hm _ (deg_UJ_mul hQi hg) _ hQ, hm _ hQi _ hg]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hBC a, deg_inner_isom _ (hiso' _ hQi)]
  refine ⟨hd.1, fun v w v' w' => ?_⟩
  have hv := hd.2 (σ (P'⁻¹ * (P' * P⁻¹) * P') v) (σ (P'⁻¹ * (P' * P⁻¹) * P') w)
    (σ (P'⁻¹ * (P' * P⁻¹) * P') v') (σ (P'⁻¹ * (P' * P⁻¹) * P') w')
  rw [hcoef v w, hcoef v' w']
  refine ⟨hv.1, ?_⟩
  rw [hv.2, deg_inner_isom _ (hiso' _ hQi), deg_inner_isom _ (hiso' _ hQi)]

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExtendByIdentitySymmFixOrth
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LinAlg

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem finrank_orth_add_finrank (U : Submodule E S.V) : finrank E (orth S U) + finrank E U = finrank E S.V := by
  classical
  let b := Module.finBasis E U
  let ℓ : Fin (finrank E U) → Module.Dual E S.V := fun a => S.hT (b a : S.V)
  have hind : LinearIndependent E (fun a => (b a : S.V)) :=
    b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hspan : Submodule.span E (Set.range fun a => (b a : S.V)) = U := by
    have : (Set.range fun a => (b a : S.V)) = U.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hℓ : LinearIndependent E ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have h1 : S.hT (∑ a, star (c a) • (b a : S.V)) = 0 := by
      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smulₛₗ, starRingEnd_apply, star_star]
    have h2 : ∑ a, star (c a) • (b a : S.V) = 0 := S.nondeg.1 _ (fun y => by rw [h1]; rfl)
    have h3 := Fintype.linearIndependent_iff.1 hind _ h2 a
    simpa using h3
  have hΦ : finrank E (Submodule.span E (Set.range ℓ)) = finrank E U := by
    rw [finrank_span_eq_card hℓ]; simp
  have hco : (Submodule.span E (Set.range ℓ)).dualCoannihilator = orth S U := by
    ext v
    rw [Submodule.mem_dualCoannihilator, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h
      have hle : U ≤ LinearMap.ker (S.hT.flip v) := by
        rw [← hspan]
        refine Submodule.span_le.2 ?_
        rintro _ ⟨a, rfl⟩
        have := h (ℓ a) (Submodule.subset_span ⟨_, rfl⟩)
        simpa [ℓ] using this
      intro x hx
      simpa using hle hx
    · intro h φ hφ
      refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hφ
      · rintro _ ⟨a, rfl⟩
        exact h _ (b a).2
      · simp
      · intro x y _ _ hx hy
        simp [hx, hy]
      · intro c x _ hx
        simp [hx]
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range ℓ))
  rw [hΦ, hco] at this
  omega

theorem isCompl_orth_of_nondegenerate (U : Submodule E S.V) (hU : U ⊓ orth S U = ⊥) : IsCompl U (orth S U) := by
  have hd : Disjoint U (orth S U) := disjoint_iff.2 hU
  refine ⟨hd, codisjoint_iff.2 (Submodule.eq_top_of_disjoint U (orth S U) ?_ hd)⟩
  have := finrank_orth_add_finrank S U
  omega

end LinAlg

section Ext

variable (D : D7)

theorem embedding_isometry_W (x y : (D.sp.X 0).V) : (VS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
  D.sp.iXY_isom 0 (lt_of_lt_of_le (by norm_num) D.R.two_le_m) x y

theorem embedding_W_injective : Function.Injective (D.sp.iXY 0) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
  rw [← embedding_isometry_W D y x, hx, map_zero]

theorem isCompl_range_orth_range : IsCompl (LinearMap.range (D.sp.iXY 0)) (orth (hS D) (LinearMap.range (D.sp.iXY 0))) := by
  refine isCompl_orth_of_nondegenerate _ _ ?_
  rw [eq_bot_iff]
  rintro _ ⟨⟨x, rfl⟩, hx⟩
  have hx' := (Formalism.MainNotions.mem_orth_iff _ _).1 hx
  have h0 : x = 0 := (D.sp.X 0).nondeg.2 x (fun y => by rw [← embedding_isometry_W D y x]; exact hx' _ ⟨y, rfl⟩)
  rw [h0, map_zero]
  exact Submodule.zero_mem _

def conjEquivOnEmbeddingRange (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) :
    LinearMap.range (D.sp.iXY 0) ≃ₗ[D.host.E] LinearMap.range (D.sp.iXY 0) :=
  (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)).symm ≪≫ₗ γ ≪≫ₗ LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)

def extendByIdentity (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).symm ≪≫ₗ
    ((conjEquivOnEmbeddingRange D γ).prodCongr (LinearEquiv.refl _ _)) ≪≫ₗ Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)

theorem extendByIdentity_apply (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (w : (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    extendByIdentity D γ (D.sp.iXY 0 w + b) = D.sp.iXY 0 (γ w) + b := by
  have e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)
      (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [e]
  unfold extendByIdentity
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Submodule.coe_prodEquivOfIsCompl']
  unfold conjEquivOnEmbeddingRange
  simp only [LinearEquiv.prodCongr_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.refl_apply]
  rfl

theorem exists_decomp_range_orth (x : (VS D).V) : ∃ (w : (D.sp.X 0).V) (b : (VS D).V),
    b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) ∧ x = D.sp.iXY 0 w + b := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).surjective x
  obtain ⟨w, hw⟩ := a.2
  exact ⟨w, b.1, b.2, by rw [Submodule.coe_prodEquivOfIsCompl', hw]⟩

theorem inner_decomp_orth_range (w w' : (D.sp.X 0).V) (b b' : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) (hb' : b' ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    (VS D).hT (D.sp.iXY 0 w + b) (D.sp.iXY 0 w' + b') = (D.sp.X 0).hT w w' + (VS D).hT b b' := by
  have h1 : (VS D).hT (D.sp.iXY 0 w) b' = 0 := (Formalism.MainNotions.mem_orth_iff _ _).1 hb' _ ⟨w, rfl⟩
  have h2 : (VS D).hT b (D.sp.iXY 0 w') = 0 := Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 hb _ ⟨w', rfl⟩)
  simp only [map_add, LinearMap.add_apply]
  rw [embedding_isometry_W, h1, h2]
  ring

theorem extendByIdentity_mem_isom (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) :
    extendByIdentity D γ ∈ isom (VS D).hT := by
  intro x y
  obtain ⟨w, b, hb, rfl⟩ := exists_decomp_range_orth D x
  obtain ⟨w', b', hb', rfl⟩ := exists_decomp_range_orth D y
  rw [extendByIdentity_apply D γ w b hb, extendByIdentity_apply D γ w' b' hb', inner_decomp_orth_range D _ _ _ _ hb hb',
    inner_decomp_orth_range D _ _ _ _ hb hb', hγ w w']

theorem extendByIdentity_symm_apply (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (w : (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    (extendByIdentity D γ).symm (D.sp.iXY 0 w + b) = D.sp.iXY 0 (γ.symm w) + b := by
  rw [LinearEquiv.symm_apply_eq, extendByIdentity_apply D γ _ b hb, LinearEquiv.apply_symm_apply]

theorem extendByIdentity_symm_fix_orth (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (b : (VS D).V)
    (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) : (extendByIdentity D γ).symm b = b := by
  have := extendByIdentity_symm_apply D γ 0 b hb
  simpa using this

end Ext

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cyc

variable {D : D7} {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
  [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
  (M : Submodule (𝓞 D.host.E) V) (T : ℕ) (w₁ : V) (hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual h M)
  (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
  (hann : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a)

include hw₁ hgen in

theorem discriminant_one_generator : DiscGen h M 1 := by
  refine ⟨{Submodule.Quotient.mk ⟨w₁, hw₁⟩}, by simp, ?_⟩
  rw [eq_top_iff, Finset.coe_singleton]
  intro q _
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨a, ha⟩ := hgen w hw
  refine Submodule.mem_span_singleton.2 ⟨-a, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
  show (-a) • w₁ - w ∈ M
  have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
  rw [e]
  exact M.neg_mem ha

include hw₁ hgen hann in

theorem corank_one_mod_prime_over (p : Ideal (𝓞 D.host.F)) (hp : p.IsMaximal) (hTp : ((T : ℕ) : 𝓞 D.host.F) ∈ p) :
    eP h M p = 1 := by
  set P : Ideal (𝓞 D.host.E) := pE D.host.F D.host.E p with hP
  set Md := Formalism.HermitianLatticesTheory.dual h M with hMd
  set K : Submodule (𝓞 D.host.E) Md := (M ⊔ P • Md).comap Md.subtype with hK
  have hTP : ((T : ℕ) : 𝓞 D.host.E) ∈ P := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hTp
    rw [map_natCast] at this
    exact this
  have hstep : ∀ n ∈ P • Md, ∃ b ∈ P, n - b • w₁ ∈ M := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro r hr w hw
      obtain ⟨c, hc⟩ := hgen w hw
      refine ⟨-(r * c), P.neg_mem (P.mul_mem_right _ hr), ?_⟩
      have e : r • w - (-(r * c)) • w₁ = r • (w + c • w₁) := by
        rw [neg_smul, sub_neg_eq_add, smul_add, mul_smul]
      rw [e]
      exact M.smul_mem _ hc
    · rintro x y ⟨b, hb, hx⟩ ⟨b', hb', hy⟩
      refine ⟨b + b', P.add_mem hb hb', ?_⟩
      have e : x + y - (b + b') • w₁ = (x - b • w₁) + (y - b' • w₁) := by rw [add_smul]; abel
      rw [e]
      exact M.add_mem hx hy
  set φ : 𝓞 D.host.E →ₗ[𝓞 D.host.E] (Md ⧸ K) :=
    LinearMap.toSpanSingleton (𝓞 D.host.E) (Md ⧸ K) (Submodule.Quotient.mk ⟨w₁, hw₁⟩) with hφ
  have hφa : ∀ a, φ a = Submodule.Quotient.mk (a • (⟨w₁, hw₁⟩ : Md)) := fun a => by
    rw [hφ, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_smul]
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha⟩ := hgen w hw
    refine ⟨-a, ?_⟩
    rw [hφa, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, Submodule.mem_comap]
    show (-a) • w₁ - w ∈ M ⊔ P • Md
    have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [e]
    exact Submodule.mem_sup_left (M.neg_mem ha)
  have hker : LinearMap.ker φ = P := by
    ext a
    rw [LinearMap.mem_ker, hφa, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap]
    show a • w₁ ∈ M ⊔ P • Md ↔ a ∈ P
    constructor
    · intro ha
      obtain ⟨m, hm, n, hn, e⟩ := Submodule.mem_sup.1 ha
      obtain ⟨b, hb, hnb⟩ := hstep n hn
      have h1 : (a - b) • w₁ ∈ M := by
        have : (a - b) • w₁ = m + (n - b • w₁) := by rw [sub_smul, ← e]; abel
        rw [this]
        exact M.add_mem hm hnb
      obtain ⟨o, ho⟩ := (hann _).1 h1
      have : a = ((T : ℕ) : 𝓞 D.host.E) * o + b := by rw [← ho]; ring
      rw [this]
      exact P.add_mem (P.mul_mem_right _ hTP) hb
    · intro ha
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul ha hw₁)
  have hcard : Nat.card (Md ⧸ K) = Ideal.absNorm p ^ 2 := by
    rw [← Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv,
      Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv, ← Formalism.MainNotions.BridgeLemma.absNorm_pE]
    rfl
  have hq := Formalism.MainNotions.BridgeLemma.absNorm_ge_two p hp
  show Nat.log (Ideal.absNorm p ^ 2) (Nat.card (Md ⧸ K)) = 1
  rw [hcard]
  have := Nat.log_pow (b := Ideal.absNorm p ^ 2) (by nlinarith) 1
  rwa [pow_one] at this

end Cyc

theorem orthLattice_structure_of_det (D : D7) (u : D.what₂.Word)
    (hdet : ForPrimeFlagLattice D u fun F0 Λ =>
      latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ)) : BaseLatticeStructure D u := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  exact ⟨orthLattice_isLattice F0 he hz Λ hΛ hu, orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu, hdet hTp h3 hsp F0 he hz Λ hrow,
    discriminant_one_generator _ _ w₁ hw₁ hgen, fun p hp hTpp => corank_one_mod_prime_over _ _ (Tu D u) w₁ hw₁ hgen hann p hp hTpp⟩

end Formalism.MainNotions.BridgeLemma₂

end
end

