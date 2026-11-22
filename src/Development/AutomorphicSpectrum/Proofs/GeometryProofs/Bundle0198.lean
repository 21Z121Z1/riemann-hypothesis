import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0190
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperGroupGermFiniteSubscheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSum
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEigenLineGenerator

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsModuleStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction

open GroundTheory.Heights₂.Heights.Regular

theorem exists_eventually_int_eq_zero {X V J : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fintype J] (v : X → J → V) (x₀ : X)
    (hv : ∀ i, ContinuousAt (fun x => v x i) x₀)
    (hind : ∀ r : J → ℝ, ∑ i, r i • v x₀ i = 0 → r = 0) :
    ∃ ε > (0 : ℝ), ∀ᶠ x in 𝓝 x₀, ∀ m : J → ℤ, ‖∑ i, (m i : ℝ) • v x i‖ < ε → m = 0 := by
  classical
  let T : (J → ℝ) →ₗ[ℝ] V := ∑ i, (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).smulRight (v x₀ i)
  have hT : ∀ r, T r = ∑ i, r i • v x₀ i := fun r => by simp [T, LinearMap.sum_apply]
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro r hr
    exact hind r (by rw [← hT]; exact hr)
  obtain ⟨K, hK0, hK⟩ := T.exists_antilipschitzWith hker
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hb : ∀ r, ‖r‖ ≤ K * ‖T r‖ := fun r => by
    simpa [dist_zero_right] using hK.le_mul_dist r 0
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card J + 1 := ⟨_, rfl⟩
  have hN : 0 < N := by rw [hNdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (2 * K * N) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ i, ‖v x i - v x₀ i‖ < δ := by
    refine eventually_all.2 fun i => ?_
    have := (Metric.tendsto_nhds.1 (hv i).tendsto) δ hδ
    simpa [dist_eq_norm] using this
  filter_upwards [hev] with x hx m hm
  obtain ⟨r, hr⟩ : ∃ r : J → ℝ, r = fun i => (m i : ℝ) := ⟨_, rfl⟩
  have hm' : ‖∑ i, r i • v x i‖ < 1 / (2 * K) := by rw [hr]; exact hm
  have hsplit : T r = ∑ i, r i • v x i - ∑ i, r i • (v x i - v x₀ i) := by
    rw [hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub]; abel
  have herr : ‖∑ i, r i • (v x i - v x₀ i)‖ ≤ N * (‖r‖ * δ) := by
    calc ‖∑ i, r i • (v x i - v x₀ i)‖ ≤ ∑ i, ‖r i • (v x i - v x₀ i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : J, ‖r‖ * δ := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm r i) (hx i).le (norm_nonneg _) (norm_nonneg _)
      _ = (Fintype.card J : ℝ) * (‖r‖ * δ) := by simp
      _ ≤ N * (‖r‖ * δ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hNdef]; linarith
  have h1 : ‖r‖ ≤ K * (‖∑ i, r i • v x i‖ + N * (‖r‖ * δ)) := by
    refine (hb r).trans (mul_le_mul_of_nonneg_left ?_ hKpos.le)
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith)
  have h2 : K * (N * (‖r‖ * δ)) = ‖r‖ / 2 := by
    rw [hδdef]; field_simp
  have h3 : K * ‖∑ i, r i • v x i‖ < 1 / 2 := by
    have := mul_lt_mul_of_pos_left hm' hKpos
    have h4 : K * (1 / (2 * K)) = 1 / 2 := by field_simp
    linarith
  have h5 : ‖r‖ < 1 := by
    rw [mul_add, h2] at h1
    linarith
  funext i
  have h6 : |(m i : ℝ)| < 1 := by
    have := (norm_le_pi_norm r i).trans_lt h5
    rw [hr] at this
    simpa [Real.norm_eq_abs] using this
  have h7 : |m i| < 1 := by exact_mod_cast h6
  simpa using Int.abs_lt_one_iff.1 h7

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)

theorem P_injective {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) : Function.Injective (L.P w) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply L.unimod.1
  rw [map_zero]
  refine LinearMap.ext fun y => ?_
  have h := L.im w hw x y
  rw [hx] at h
  simp at h
  exact_mod_cast h.symm

theorem real_indep {J : Type*} [Fintype J] (b : Module.Basis J ℤ Λ) {w : Fin n → ℂ}
    (hw : w ∈ logCover L.a_le) (r : J → ℝ) (h : ∑ i, r i • L.P w (b i) = 0) : r = 0 := by
  classical
  funext j
  obtain ⟨u, hu⟩ := L.unimod.2 (b.coord j)
  let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => (L.P w u ⬝ᵥ L.H (expCover a w) *ᵥ star v).im
      map_add' := fun v v' => by simp [star_add, mulVec_add, dotProduct_add]
      map_smul' := fun t v => by simp [star_smul, mulVec_smul, dotProduct_smul] }
  have h1 : ∀ i, ψ (L.P w (b i)) = if i = j then 1 else 0 := fun i => by
    have h2 := L.im w hw u (b i)
    change (L.P w u ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w (b i))).im = _
    rw [h2, hu]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have h2 := congrArg ψ h
  simp only [map_sum, map_smul, h1, map_zero, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  simpa using h2

theorem continuousAt_P (x : Λ) {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le) :
    ContinuousAt (fun w => L.P w x) w₀ :=
  (L.hol x).continuousOn.continuousAt ((isOpen_logCover L.a_le).mem_nhds hw)

theorem continuousAt_apply (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1)) (x : Λ)
    {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le) :
    ContinuousAt (fun w => A (expCover a w) (L.P w x)) w₀ := by
  classical
  have hP := continuousAt_P L x hw
  have hexp : ContinuousAt (expCover (n := n) a) w₀ := (continuous_expCover a).continuousAt
  have hAe : ∀ v, ContinuousAt (fun w => A (expCover a w) v) w₀ := fun v =>
    ContinuousAt.comp (f := expCover a) (g := fun z => A z v)
      ((hA v).continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (expCover_mem_ball L.a_le hw))) hexp
  have h1 : (fun w => A (expCover a w) (L.P w x)) = fun w =>
      ∑ i, (L.P w x i) • A (expCover a w) (fun j => if i = j then 1 else 0) := by
    funext w
    exact LinearMap.pi_apply_eq_sum_univ _ _
  rw [h1]
  exact tendsto_finset_sum _ fun i _ =>
    (((continuous_apply i).continuousAt.comp hP).smul (hAe _))

theorem eventually_eq (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1))
    (hex : ∀ w ∈ logCover L.a_le, ∀ x, ∃ y, L.P w y = A (expCover a w) (L.P w x))
    (x y : Λ) {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le)
    (h : L.P w₀ y = A (expCover a w₀) (L.P w₀ x)) :
    ∀ᶠ w in 𝓝 w₀, L.P w y = A (expCover a w) (L.P w x) := by
  haveI := L.free
  haveI := L.fin
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℤ Λ) :=
    ⟨Module.Free.chooseBasis ℤ Λ⟩
  obtain ⟨ε, hε, hev⟩ := exists_eventually_int_eq_zero (fun w i => L.P w (b i)) w₀
    (fun i => continuousAt_P L (b i) hw) (real_indep L b hw)
  have hD : ContinuousAt (fun w => A (expCover a w) (L.P w x) - L.P w y) w₀ :=
    (continuousAt_apply L A hA x hw).sub (continuousAt_P L y hw)
  have hsmall : ∀ᶠ w in 𝓝 w₀, ‖A (expCover a w) (L.P w x) - L.P w y‖ < ε := by
    have h0 := (Metric.tendsto_nhds.1 hD.tendsto) ε hε
    simpa [h, dist_eq_norm] using h0
  filter_upwards [hev, hsmall, (isOpen_logCover L.a_le).mem_nhds hw] with w h1 h2 hwC
  obtain ⟨y', hy'⟩ := hex w hwC x
  have hk : L.P w (y' - y) = ∑ i, ((b.repr (y' - y) i : ℤ) : ℝ) • L.P w (b i) := by
    conv_lhs => rw [← b.sum_repr (y' - y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
  have hm := h1 (fun i => b.repr (y' - y) i) (by rw [← hk, map_sub, hy']; exact h2)
  have h0 : y' - y = 0 := b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun hm i)
  rw [← sub_eq_zero.1 h0, hy']

theorem eq_of_mem (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1))
    (hex : ∀ w ∈ logCover L.a_le, ∀ x, ∃ y, L.P w y = A (expCover a w) (L.P w x))
    (x y : Λ) {w₀ w₁ : Fin n → ℂ} (h0 : w₀ ∈ logCover L.a_le) (h1 : w₁ ∈ logCover L.a_le)
    (h : L.P w₀ y = A (expCover a w₀) (L.P w₀ x)) :
    L.P w₁ y = A (expCover a w₁) (L.P w₁ x) := by
  classical
  choose φ hφ using fun w : logCover L.a_le => hex w.1 w.2 x
  have hlc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    have h2 := (continuous_subtype_val.continuousAt (x := w)).eventually
      (eventually_eq L A hA hex x (φ w) w.2 (hφ w))
    filter_upwards [h2] with w' hw'
    exact P_injective L w'.2 ((hφ w').trans hw'.symm)
  haveI : PreconnectedSpace (logCover L.a_le) :=
    Subtype.preconnectedSpace (convex_logCover L.a_le).isPreconnected
  have h2 := hlc.apply_eq_of_preconnectedSpace ⟨w₀, h0⟩ ⟨w₁, h1⟩
  have hy : φ ⟨w₀, h0⟩ = y := P_injective L h0 ((hφ ⟨w₀, h0⟩).trans h.symm)
  rw [← hy, h2]
  exact hφ ⟨w₁, h1⟩

theorem exists_module_of_period_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ))), (∀ c x, DifferentiableOn ℂ (fun z => B z c x) (Metric.ball 0 1)) → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ c x, ∃ y, L.P w y = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x)) → ∃ _ : Module (𝓞 E) Λ, ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ (c : 𝓞 E) x, L.P w (c • x) = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x) := by
  intro E _ _ _ n a g Λ _ L B hB hex
  obtain ⟨w₀, hw₀⟩ := logCover_nonempty L.a_le
  choose f hf using fun c x => hex w₀ hw₀ c x
  have key : ∀ w ∈ logCover L.a_le, ∀ c x, L.P w (f c x) = B (expCover a w) c (L.P w x) :=
    fun w hw c x => eq_of_mem L (fun z => B z c) (fun x => hB c x)
      (fun w hw x => hex w hw c x) x (f c x) hw₀ hw (hf c x)
  have inj := P_injective L hw₀
  have e1 : ∀ x, f 1 x = x := fun x => inj (by rw [hf]; simp)
  have e2 : ∀ c d x, f (c * d) x = f c (f d x) := fun c d x => inj (by
    rw [hf, hf, hf, map_mul, Module.End.mul_apply])
  have e3 : ∀ c, f c 0 = 0 := fun c => inj (by rw [hf]; simp)
  have e4 : ∀ c x y, f c (x + y) = f c x + f c y := fun c x y => inj (by
    rw [map_add, hf, hf, hf, map_add, map_add])
  have e5 : ∀ c d x, f (c + d) x = f c x + f d x := fun c d x => inj (by
    rw [map_add, hf, hf, hf, map_add, LinearMap.add_apply])
  have e6 : ∀ x, f 0 x = 0 := fun x => inj (by rw [hf]; simp)
  exact ⟨{ smul := f, one_smul := e1, mul_smul := e2, smul_zero := e3, smul_add := e4,
           add_smul := e5, zero_smul := e6 }, key⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointFrameSpecializationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_frame_specialization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → y ≫ pullback.snd _ _ = spMap σ → (Z.eig τ).IsFrameAt b₁ ⟨_, h⟩ → (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt b₂ ⟨_, h⟩ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values | exact GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperGroupGermFiniteSubschemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_group_germ_finite_subscheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left →
    ∃ (A' : Type) (_ : CommRing A') (_ : HopfAlgebra k A') (_ : Coalgebra.IsCocomm k A') (_ : Module.Finite k A'),
      Module.finrank k A' = Module.finrank k A ∧
      ∃ (D : LinearMap.ker (Matrix.toLin' (rho g.B a)) →ₗ[k] (A' →ₗ[k] k))
        (T : LinearMap.ker (Matrix.toLin' (rho g.B (star a))) →ₗ[k] A'),
        Function.Injective D ∧ Function.Injective T ∧
        (∀ u f f', D u (f * f') = D u f * Coalgebra.counit (R := k) f' + Coalgebra.counit (R := k) f * D u f') ∧
        (∀ z, Coalgebra.comul (R := k) (T z) = T z ⊗ₜ[k] (1 : A') + (1 : A') ⊗ₜ[k] T z) ∧
        ∀ (u : LinearMap.ker (Matrix.toLin' (rho g.B a))) (z : LinearMap.ker (Matrix.toLin' (rho g.B (star a)))),
          (z : Fin d → k) ⬝ᵥ (bil (g.B.ad a) 1 1).transpose.mulVec (u : Fin d → k) = 0 → D u (T z) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom | exact GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperOfProperCover
section
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isProper_of_finite_cover (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0})
    (π : ∀ i, Y i ⟶ X) (hsep : IsSeparated p) (hft : LocallyOfFiniteType p)
    (hprop : ∀ i, IsProper (π i ≫ p)) (hcov : ∀ x : X, ∃ i, x ∈ Set.range (π i)) :
    IsProper p := by
  have huc : UniversallyClosed p := by
    constructor
    intro X' Y' i₁ i₂ f' hpb Z hZ
    have hW : ∀ i, IsPullback (pullback.fst i₁ (π i) ≫ f') (pullback.snd i₁ (π i)) i₂
        (π i ≫ p) := fun i => (IsPullback.of_hasPullback i₁ (π i)).paste_horiz hpb
    have hc : ∀ i, IsClosedMap ⇑(pullback.fst i₁ (π i) ≫ f') := fun i =>
      @UniversallyClosed.universally_isClosedMap _ _ _ (hprop i).toUniversallyClosed
        _ _ _ _ _ (hW i)
    have key : ⇑f' '' Z =
        ⋃ i, ⇑(pullback.fst i₁ (π i) ≫ f') '' (⇑(pullback.fst i₁ (π i)) ⁻¹' Z) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, y', hy'⟩ := hcov (i₁ x)
        obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y' hy'.symm
        refine ⟨i, w, ?_, ?_⟩
        · rw [hw]
          exact hx
        · show f' (pullback.fst i₁ (π i) w) = f' x
          rw [hw]
      · rintro ⟨i, w, hw, rfl⟩
        exact ⟨pullback.fst i₁ (π i) w, hw, rfl⟩
    convert isClosed_iUnion_of_finite fun i =>
      hc i _ (hZ.preimage (pullback.fst i₁ (π i)).continuous) using 1
  exact @IsProper.mk _ _ _ hsep huc hft

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumLatticeWedgeComap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.BlockFrame

theorem frame_of_sum_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P Wv : Type) [AddCommGroup P] [Module Ω P] [AddCommGroup Wv] [Module Ω Wv] (i : Wv →ₗ[Ω] P) (A B : Lat ξ P) (Va Vb : Submodule Ω P) (N j : ℕ) (hj : j ≤ N) (b : Fin N → Wv) (s : Fin (N - j) → P) (p : Cpt ξ), Function.Injective i → LinearMap.range i = Va ⊔ Vb → Disjoint Va Vb → (∀ x ∈ A p, x ∈ Va) → (∀ x ∈ B p, x ∈ Vb) → (Lat.comap (fun q => A q ⊔ B q) i).IsFrameAt b p → Submodule.span Ω (Set.range (b ∘ headIdx hj)) = Va.comap i → (∀ k, s k ∈ Vb ∧ i (b (tailIdx hj k)) - s k ∈ Va) → B.IsFrameAt s p ∧ (∀ k, i (b (tailIdx hj k)) - s k ∈ A p) ∧ ∀ k, i (b (headIdx hj k)) ∈ A p := by
  intro X Ω _ ξ P Wv _ _ _ _ i A B Va Vb N j hj b s p hinj hrange hdisj hAV hBV hfr hhead hs
  have hzero : ∀ {x : P}, x ∈ Va → x ∈ Vb → x = 0 := fun h1 h2 => Submodule.disjoint_def.1 hdisj _ h1 h2
  have hmemfr : ∀ k, i (b k) ∈ A p ⊔ B p := fun k => by
    have h : b k ∈ (Lat.comap (fun q => A q ⊔ B q) i) p := by
      rw [hfr.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  have hbhead : ∀ k, i (b (headIdx hj k)) ∈ Va := fun k => by
    have h : b (headIdx hj k) ∈ Va.comap i := by
      rw [← hhead]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  have hH : ∀ k, i (b (headIdx hj k)) ∈ A p := fun k => by
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 (hmemfr (headIdx hj k))
    have he0 : e = 0 := hzero (by
      have h : e = i (b (headIdx hj k)) - a := by rw [← hae]; abel
      rw [h]
      exact Va.sub_mem (hbhead k) (hAV a ha)) (hBV e he)
    rw [← hae, he0, add_zero]
    exact ha
  have hT : ∀ k, i (b (tailIdx hj k)) - s k ∈ A p ∧ s k ∈ B p := fun k => by
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 (hmemfr (tailIdx hj k))
    have hes : e - s k = 0 := hzero (by
      have h : e - s k = (i (b (tailIdx hj k)) - s k) - a := by rw [← hae]; abel
      rw [h]
      exact Va.sub_mem (hs k).2 (hAV a ha)) (Vb.sub_mem (hBV e he) (hs k).1)
    have hes' : e = s k := sub_eq_zero.1 hes
    refine ⟨?_, hes' ▸ he⟩
    have h : i (b (tailIdx hj k)) - s k = a := by rw [← hae, hes']; abel
    rw [h]
    exact ha
  have hcase : ∀ k : Fin N, (∃ a, k = headIdx hj a) ∨ ∃ a, k = tailIdx hj a := fun k => by
    by_cases h : (k : ℕ) < j
    · exact Or.inl ⟨⟨k, h⟩, by ext; rfl⟩
    · exact Or.inr ⟨⟨k - j, by have := k.2; omega⟩, by ext; simp [tailIdx]; omega⟩
  have hspan : ∀ x ∈ Submodule.span (regAt ξ p) (Set.range b),
      ∃ t ∈ Submodule.span (regAt ξ p) (Set.range s), i x - t ∈ Va := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rcases hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨0, zero_mem _, by simpa using hbhead a⟩
      · exact ⟨s a, Submodule.subset_span ⟨a, rfl⟩, (hs a).2⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨t, ht, hxt⟩ := hx
      obtain ⟨t', ht', hyt⟩ := hy
      refine ⟨t + t', add_mem ht ht', ?_⟩
      have h : i (x + y) - (t + t') = (i x - t) + (i y - t') := by rw [map_add]; abel
      rw [h]
      exact Va.add_mem hxt hyt
    | smul r x _ hx =>
      obtain ⟨t, ht, hxt⟩ := hx
      refine ⟨r • t, Submodule.smul_mem _ r ht, ?_⟩
      have h : i (r • x) - r • t = (r : Ω) • (i x - t) := by
        rw [smul_sub]
        show i ((r : Ω) • x) - (r : Ω) • t = _
        rw [map_smul]
      rw [h]
      exact Va.smul_mem _ hxt
  have hle : Submodule.span (regAt ξ p) (Set.range s) ≤ B p := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact (hT k).2)
  have hgen : B p = Submodule.span (regAt ξ p) (Set.range s) := by
    refine le_antisymm (fun e he => ?_) hle
    have hr : e ∈ LinearMap.range i := by
      rw [hrange]
      exact Submodule.mem_sup_right (hBV e he)
    obtain ⟨x, rfl⟩ := hr
    have hxc : x ∈ (Lat.comap (fun q => A q ⊔ B q) i) p := by
      show i x ∈ A p ⊔ B p
      exact Submodule.mem_sup_right he
    rw [hfr.2] at hxc
    obtain ⟨t, ht, hxt⟩ := hspan x hxc
    have h0 : i x - t = 0 := hzero hxt (Vb.sub_mem (hBV _ he) (hBV _ (hle ht)))
    rw [sub_eq_zero.1 h0]
    exact ht
  have htinj : Function.Injective (tailIdx hj) := fun a c h => by
    have h' := congrArg Fin.val h
    simp only [tailIdx] at h'
    ext
    omega
  have hli : LinearIndependent Ω s := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have hx1 : (∑ k, g k • b (tailIdx hj k)) ∈ Va.comap i := by
      have h : i (∑ k, g k • b (tailIdx hj k)) = ∑ k, g k • (i (b (tailIdx hj k)) - s k) := by
        simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, hg, sub_zero]
      show i _ ∈ Va
      rw [h]
      exact Va.sum_mem fun k _ => Va.smul_mem _ (hs k).2
    have hdis : Disjoint (Set.range (headIdx hj)) (Set.range (tailIdx hj)) := by
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨a, rfl⟩ ⟨c, h⟩
      have h' := congrArg Fin.val h
      simp only [headIdx, tailIdx, Fin.val_castLE] at h'
      have := a.2
      omega
    have hd := hfr.1.disjoint_span_image hdis
    have hx2 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (tailIdx hj)) :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨_, ⟨k, rfl⟩, rfl⟩)
    have hx3 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (headIdx hj)) := by
      rw [← Set.range_comp, hhead]
      exact hx1
    have hx0 := Submodule.disjoint_def.1 hd _ hx3 hx2
    exact Fintype.linearIndependent_iff.1 (hfr.1.comp _ htinj) g hx0
  exact ⟨⟨hli, hgen⟩, fun k => (hT k).1, hH⟩

end GlobalTheory.CompanionTheory.Ar.BlockFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorWedgeDetChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.TopWedge

theorem exists_form_tprod_wedge (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (V : Ψ → Type)
    [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (n : ℕ) (e : ∀ τ, Fin n → V τ)
    (hli : ∀ τ, LinearIndependent Ω (e τ)) (hspan : ∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤) :
    ∃ Φ : (PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) →ₗ[Ω] Ω,
      Φ (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ)) = 1 := by
  classical
  let b : ∀ τ, Module.Basis (Fin n) Ω (V τ) := fun τ => Module.Basis.mk (hli τ) (hspan τ).ge
  let φ : ∀ τ, ⋀[Ω]^n (V τ) →ₗ[Ω] Ω := fun τ => exteriorPower.alternatingMapLinearEquiv (b τ).det
  have hφ : ∀ τ, φ τ (exteriorPower.ιMulti Ω n (e τ)) = 1 := fun τ => by
    have hb : (⇑(b τ) : Fin n → V τ) = e τ := Module.Basis.coe_mk _ _
    simp only [φ, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [← hb]
    exact (b τ).det_self
  refine ⟨PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra Ω Ψ Ω).compLinearMap φ), ?_⟩
  rw [PiTensorProduct.lift.tprod]
  simp [hφ]

theorem eq_mul_prod_det : ∀ (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (V : Ψ → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (n : ℕ) (e e' : ∀ τ, Fin n → V τ) (T : ∀ τ, Matrix (Fin n) (Fin n) Ω) (a a' : Ω), (∀ τ, LinearIndependent Ω (e τ)) → (∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤) → (∀ τ q, e' τ q = ∑ p, T τ p q • e τ p) → a • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) = a' • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e' τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) → a = a' * ∏ τ, (T τ).det := by
  intro Ψ _ Ω _ V _ _ n e e' T a a' hli hspan hT h
  classical
  obtain ⟨Φ, hΦ⟩ := exists_form_tprod_wedge Ψ Ω V n e hli hspan
  have hq : ∀ τ, exteriorPower.ιMulti Ω n (e' τ) = (T τ).det • exteriorPower.ιMulti Ω n (e τ) := fun τ => by
    rw [← GlobalTheory.CompanionTheory.Ar.BigBlock.iotaMulti_comb]
    congr 1
    funext q
    exact hT τ q
  have htp : (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e' τ)) =
      (∏ τ, (T τ).det) • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ)) := by
    simp_rw [hq]
    exact MultilinearMap.map_smul_univ _ _ _
  have h2 := congrArg Φ h
  rw [htp, map_smul, map_smul, map_smul, hΦ] at h2
  simpa using h2

end GlobalTheory.CompanionTheory.Ar.TopWedge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEigenLineGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_eigen_line_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → ∃ φ : FrameFn Xo c, IsLineFn U τ φ ∧ Represents Y U τ Z.M a b φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_frameFn_of_gen | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_frameFn_of_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_frameFn_of_gen <;> assumption)
end

