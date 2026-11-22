import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0150
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0145
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0151
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0152
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0149
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0054
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0126
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDefStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_domain_iff_pos_def : ∀ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q ↔ (1 - (bigZe e q t)ᴴ * bigZe e q t).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.mem_ballDom_iff_posDef_bigZe <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZero
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex

theorem re_star_dotProduct_self {κ : Type} [Fintype κ] (w : κ → ℂ) :
    (star w ⬝ᵥ w).re = ‖WithLp.toLp 2 w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (star (w i) * w i).re = Complex.normSq (w i) := by
    simp [Complex.normSq_apply]
  rw [this, Complex.normSq_eq_norm_sq]

theorem re_form_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) (v : κ' → ℂ) :
    (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re = ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
  have h : star v ⬝ᵥ ((Zᴴ * Z) *ᵥ v) = star (Z *ᵥ v) ⬝ᵥ (Z *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, h, Complex.sub_re,
    re_star_dotProduct_self, re_star_dotProduct_self]

theorem posDef_iff {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) :
    (1 - Zᴴ * Z).PosDef ↔ ∀ v : κ' → ℂ, v ≠ 0 → ‖WithLp.toLp 2 (Z *ᵥ v)‖ < ‖WithLp.toLp 2 v‖ := by
  have hH : (1 - Zᴴ * Z).IsHermitian :=
    (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)
  constructor
  · intro h v hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp h).2 hv)).1
    have h0 : (0 : ℝ) < ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
      rw [← re_form_eq]
      simpa using hpos
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (sub_pos.mp h0)
  · intro h
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hH, fun v hv => ?_⟩
    have hre : 0 < (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re := by
      rw [re_form_eq, sub_pos]
      exact pow_lt_pow_left₀ (h v hv) (norm_nonneg _) two_ne_zero
    have hstar : star (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)) = star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v) := by
      conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
    have him : (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem ballMat_combo {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (s t : Fin n → ℂ) (a b : ℝ) (τ : Ψ) :
    ballMat q (a • s + b • t) τ = a • ballMat q s τ + b • ballMat q t τ := by
  ext x y
  simp [ballMat]

theorem convex_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) [Fintype Ψ] :
    Convex ℝ (ballDom q) := by
  intro s hs t ht a b ha hb hab τ
  refine (posDef_iff _).mpr fun v hv => ?_
  have h1 := (posDef_iff _).mp (hs τ) v hv
  have h2 := (posDef_iff _).mp (ht τ) v hv
  have hc := convex_ball (0 : EuclideanSpace ℂ (Fin j)) ‖WithLp.toLp 2 v‖
    (x := WithLp.toLp 2 (ballMat q s τ *ᵥ v)) (y := WithLp.toLp 2 (ballMat q t τ *ᵥ v))
    (by simpa using h1) (by simpa using h2) ha hb hab
  have he : WithLp.toLp 2 (ballMat q (a • s + b • t) τ *ᵥ v) =
      a • WithLp.toLp 2 (ballMat q s τ *ᵥ v) + b • WithLp.toLp 2 (ballMat q t τ *ᵥ v) := by
    rw [ballMat_combo, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    rfl
  rw [he]
  simpa using hc

theorem zero_mem_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have h : ballMat q (0 : Fin n → ℂ) τ = 0 := by
    ext x y
    simp [ballMat]
  rw [h]
  simpa using (Matrix.PosDef.one : (1 : Matrix (Fin j') (Fin j') ℂ).PosDef)

theorem ballDom_open_convex_zero : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n),
    IsOpen (ballDom q) ∧ Convex ℝ (ballDom q) ∧ (0 : Fin n → ℂ) ∈ ballDom q :=
  fun _ _ _ _ _ q => ⟨BallInverse.isOpen_ballDom q, convex_ballDom q, zero_mem_ballDom q⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMulStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_mul : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → ∀ t ∈ ballDom q, moebBall q (fun τ => u τ * v τ) t = moebBall q u (moebBall q v t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusTransitiveStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_transitive : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q → ∃ u : Ψ → Matrix (Sg j j') (Sg j j') ℂ, (∀ τ, IsSgU (u τ)) ∧ moebBall q u 0 = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.moebBall_transitive | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.moebBall_transitive | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.moebBall_transitive <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroContinuousStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_zero_continuous : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (X : Type) [TopologicalSpace X] (f : X → Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, Continuous fun x => f x τ) → (∀ x τ, IsSgU (f x τ)) → Continuous fun x => moebBall q (f x) 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.continuous_moebBall_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitaryStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_zero_eq_iff_unitary : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → (moebBall q u 0 = moebBall q (fun τ => u τ * v τ) 0 ↔ ∀ τ, (v τ)ᴴ * v τ = 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.moebBall_zero_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.moebBall_zero_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Stab.moebBall_zero_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallPotentialFormula
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem ballPot_ballPt_eq : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ), ballPot q (ballPt q W) = -∑ τ, Real.log (1 - W τ * (W τ)ᴴ).det.re := by
  intro Ψ _ j j' n q W
  unfold ballPot
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hm : ballMat q (ballPt q W) τ = (W τ)ᵀ := by
    ext a b
    simp [ballMat, ballPt]
  have key : 1 - ((W τ)ᵀ)ᴴ * (W τ)ᵀ = (starRingEnd ℂ).mapMatrix (1 - W τ * (W τ)ᴴ) := by
    ext a b
    simp only [Matrix.sub_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, map_sub, map_sum, map_mul]
    congr 1
    · by_cases h : a = b <;> simp [Matrix.one_apply, h]
    · refine Finset.sum_congr rfl fun c _ => ?_
      simp
  rw [hm, key, ← RingHom.map_det, Complex.conj_re]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CMFieldDegreeEqTwiceCardStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CM_field_degree_eq_twice_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card | exact GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.CMRank.finrank_eq_two_mul_card <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateEmbeddingsCriterionStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_embeddings_criterion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → ∀ i k : Ix Ψ j j', (∀ a : 𝓞 E, emb σ i a = star (emb σ k a)) ↔ (i.2 = k.2 ∧ i.1.isLeft ≠ k.1.isLeft) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.EmbConj.emb_eq_star_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenProjectionInEigenspace
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)

omit [IsCMField E] in

theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

def mulPt (a : 𝓞 E) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) where
  toFun y := fun τ => F.σ τ a • y τ
  map_add' y y' := by
    ext τ i
    simp [mul_add]
  map_smul' r y := by
    ext τ i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, RingHom.id_apply]
    ring

theorem vec_smul (a : 𝓞 E) (x : Λ) : C.vec (a • x) = mulPt (F := F) a (C.vec x) := by
  ext τ i
  simp [LatEmb.vec, mulPt, C.e_smul, embOf_coe]

def vecHom : Λ →+ (Ψ → Fin (j + j') → ℂ) where
  toFun := C.vec
  map_zero' := by
    ext τ i
    simp [LatEmb.vec]
  map_add' x y := by
    ext τ i
    simp [LatEmb.vec]

theorem vec_lam (k : Fin (2 * g)) : C.vec (C.lam k) = C.bas k := by
  ext τ i
  exact (C.bas_eq k τ i).symm

theorem perExt_bas (k : Fin (2 * g)) : C.perExt R (C.bas k) = R.P (C.lam k) := by
  simp [LatEmb.perExt]

theorem perExt_vec (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  have h : ((C.perExt R).toAddMonoidHom.comp (vecHom C)).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    change C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [vec_lam, perExt_bas]
  exact congrArg (fun f : Λ →ₗ[ℤ] (Fin g → ℂ) => f x) h

theorem perExt_mulPt (a : 𝓞 E) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R (mulPt (F := F) a y) = R.B a (C.perExt R y) := by
  have h : (C.perExt R).comp (mulPt (F := F) a) = ((R.B a).restrictScalars ℝ).comp (C.perExt R) := by
    refine C.bas.ext fun k => ?_
    change C.perExt R (mulPt (F := F) a (C.bas k)) = R.B a (C.perExt R (C.bas k))
    rw [← vec_lam, ← vec_smul, perExt_vec, perExt_vec, R.act]
  exact congrArg (fun f : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) => f y) h

open Classical in
theorem perExt_single_smul (a : 𝓞 E) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    C.perExt R (Pi.single τ (F.σ τ a • y)) = R.B a (C.perExt R (Pi.single τ y)) := by
  rw [← perExt_mulPt]
  congr 1
  ext τ' i
  by_cases h : τ' = τ
  · subst h
    simp [mulPt]
  · simp [mulPt, Pi.single_eq_of_ne h]

theorem B_pPart (a : 𝓞 E) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    R.B a (C.pPart R τ y) = F.σ τ a • C.pPart R τ y := by
  classical
  have h : C.pPart R τ (F.σ τ a • y) = F.σ τ a • C.pPart R τ y := (pPartL C R τ).map_smul _ _
  rw [← h]
  simp only [LatEmb.pPart, map_smul, map_sub, perExt_single_smul]
  rw [smul_comm Complex.I (F.σ τ a) y, perExt_single_smul]

theorem pPart_mem_eigSp (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pPart R τ y ∈ eigSp R.B (F.σ τ) := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a
  simp [B_pPart]

end

theorem pPart_mem_eigSp_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ), C.pPart R τ y ∈ eigSp R.B (F.σ τ) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R τ y
  exact pPart_mem_eigSp C R τ y

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingInverseRootImaginaryStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_inverse_root_imaginary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (s : 𝓞 E →+* ℂ) (m : ℕ), m ≠ 0 → ∃ ε : ℝ, ε ^ 2 = 1 ∧ embOf s (((m : E) * (H.rt : E))⁻¹) = Complex.I * (((1 / ((m : ℝ) * Real.sqrt H.d)) * ε : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatXi.conj_inv_mul_rt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem embeddingPieces_of_resK (hA : ArithIntersectionSystemStatement)
    (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) :
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement :=
  have hInt : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hR
  have hRes : ResExistsStatement := GlobalTheory.T.resolution_exists_of_resolution_statement hR
  GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt)
    (GlobalTheory.T.piece_degree_of_intersection_and_resolution hA hRes hInt)

end GlobalTheory.CompanionTheory.Ar.Giv
end

