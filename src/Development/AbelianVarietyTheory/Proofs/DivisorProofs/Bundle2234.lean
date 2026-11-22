import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTangentLiftOfModelTangent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TanLiftPull

theorem toUnit_left_eq {S : Scheme.{0}} (A : Over S) (f : A ⟶ 𝟙_ (Over S)) : f.left = A.hom := by
  simpa using Over.w f

theorem one_left_eq {S : Scheme.{0}} (A : Over S) (G : Over S) [GrpObj G] :
    (1 : A ⟶ G).left = A.hom ≫ η[G].left := by
  rw [← toUnit_left_eq A (toUnit A)]
  rfl

theorem exists_isTan_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), ∃ w : epsOver V V ⟶ G.G, IsTan w ∧ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y V _ x G ψ v
  have hpb : IsPullback ψ.φ G.G.hom Y.t.G.hom x := ψ.cart.1
  have hsq : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ Y.t.G.hom = (epsOver V V).hom ≫ x := by
    rw [Over.w]; rfl
  have hfa : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (algebraMap V (DualNumber V)) = 𝟙 _ := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of V)
    ext a
    simp
  refine ⟨Over.homMk (hpb.lift _ _ hsq) (hpb.lift_snd _ _ _), ?_, (hpb.lift_fst _ _ _).symm⟩
  show spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ hpb.lift _ _ hsq = (1 : ptOver V V ⟶ G.G).left
  apply hpb.hom_ext
  · rw [Category.assoc, hpb.lift_fst]
    have h1 := congrArg (fun f => f.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
    simp only [smT_left] at h1
    have key : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (epsMul (0 : V)) =
        spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext <;> simp [epsMul]
    have hunit : η[G.G].left ≫ ψ.φ = x ≫ η[Y.t.G].left := by
      have h := ψ.cm.e_comm
      rw [ψ.base] at h
      exact h
    rw [← key, Category.assoc, h1, one_left_eq, one_left_eq, Category.assoc, hunit]
    simp only [Over.mk_hom, ← Category.assoc, hfa]
    simp [spMap]
  · rw [Category.assoc, hpb.lift_snd, Over.w]
    simp only [Over.mk_hom]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

end GlobalTheory.TanLiftPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPuncturedDiscInjectiveEvalAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowEval

noncomputable def absConv (u : ℂ) : Subring (PowerSeries ℂ) where
  carrier := {Φ | Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖}
  zero_mem' := by simp
  one_mem' := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [PowerSeries.coeff_one, Finset.notMem_singleton.1 hn]
  add_mem' := by
    intro f g hf hg
    refine (Summable.add hf hg).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add, add_mul]
    exact norm_add_le _ _
  neg_mem' := by
    intro f hf
    simpa [map_neg, neg_mul, norm_neg] using hf
  mul_mem' := by
    intro f g hf hg
    have e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
      rw [PowerSeries.coeff_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun kl h => ?_
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
      ring
    show Summable fun n => ‖PowerSeries.coeff n (f * g) * u ^ n‖
    simp only [e]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => PowerSeries.coeff n f * u ^ n) (g := fun n => PowerSeries.coeff n g * u ^ n) hf hg

noncomputable def evalAt (u : ℂ) : absConv u →+* ℂ where
  toFun Φ := ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n
  map_one' := by
    rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
    simp
  map_zero' := by simp
  map_add' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    simp only [Subring.coe_add, map_add, add_mul]
    exact hf.of_norm.tsum_add hg.of_norm
  map_mul' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    refine tsum_congr fun n => ?_
    simp only [Subring.coe_mul]
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl h => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
    ring

theorem countable_closure {A : Type} [CommRing A] (S : Set A) (hS : S.Countable) :
    Countable (Subring.closure S) := by
  haveI : Countable S := hS.to_subtype
  haveI : Countable (MvPolynomial S ℤ) :=
    (MvPolynomial.basisMonomials S ℤ).repr.injective.countable
  let φ : MvPolynomial S ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) Subtype.val
  have hle : Subring.closure S ≤ φ.range := Subring.closure_le.2 fun s hs =>
    ⟨MvPolynomial.X ⟨s, hs⟩, by simp [φ]⟩
  have hc : (φ.range : Set A).Countable := by
    rw [RingHom.coe_range]; exact Set.countable_range _
  exact (hc.mono hle).to_subtype

theorem radius_ge (ε : ℝ) (Φ : PowerSeries ℂ)
    (h : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) :
    ENNReal.ofReal ε ≤ (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrε : (r : ℝ) < ε := by
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 hr
  refine FormalMultilinearSeries.le_radius_of_summable _ ?_
  have hs := h (r : ℂ) (by exact_mod_cast hr0) (by simpa using hrε)
  refine hs.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]
  simp

end GlobalTheory.PowEval

open GlobalTheory.PowEval in

theorem GlobalTheory.exists_injective_evalAt_closure : ∀ (ε : ℝ) (S : Set (PowerSeries ℂ)), 0 < ε → S.Countable → (∀ Φ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) → ∃ (u : ℂ) (i : Subring.closure S →+* ℂ), u ≠ 0 ∧ ‖u‖ < ε ∧ Function.Injective i ∧ ∀ Φ : Subring.closure S, i Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n := by
  intro ε S hε hS h
  haveI : Countable (Subring.closure S) := countable_closure S hS
  let p : PowerSeries ℂ → FormalMultilinearSeries ℂ ℂ ℂ := fun Φ =>
    FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ
  have hsum : ∀ (Φ : PowerSeries ℂ) (u : ℂ), (p Φ).sum u = ∑' n, PowerSeries.coeff n Φ * u ^ n := by
    intro Φ u
    show FormalMultilinearSeries.ofScalarsSum _ u = _
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp [smul_eq_mul]
  have hcl : ∀ Φ ∈ Subring.closure S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖ := by
    intro Φ hΦ u hu0 hu
    have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hu
    exact hle hΦ
  have hrad : ∀ Φ ∈ Subring.closure S, ENNReal.ofReal ε ≤ (p Φ).radius := fun Φ hΦ =>
    radius_ge ε Φ (hcl Φ hΦ)
  have hpos : ∀ Φ ∈ Subring.closure S, 0 < (p Φ).radius := fun Φ hΦ =>
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) (hrad Φ hΦ)
  have hball : ∀ Φ ∈ Subring.closure S, Metric.ball (0 : ℂ) ε ⊆ EMetric.ball 0 (p Φ).radius := by
    intro Φ hΦ
    rw [← Metric.emetric_ball]
    exact EMetric.ball_subset_ball (hrad Φ hΦ)
  let J := Option {Φ : Subring.closure S // Φ ≠ 0}
  let f : J → ℂ → ℂ := fun i => match i with
    | none => id
    | some Φ => (p (Φ.1 : PowerSeries ℂ)).sum
  have han : ∀ i, AnalyticOnNhd ℂ (f i) (Metric.ball 0 ε) := by
    intro i
    cases i with
    | none => exact analyticOnNhd_id
    | some Φ =>
      exact ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).analyticOnNhd.mono (hball _ Φ.1.2)
  have hnz : ∀ i, ∃ x ∈ Metric.ball (0 : ℂ) ε, f i x ≠ 0 := by
    intro i
    cases i with
    | none =>
      refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      · show ((ε / 2 : ℝ) : ℂ) ≠ 0
        exact_mod_cast (by linarith : ε / 2 ≠ 0)
    | some Φ =>
      by_contra hcon
      push_neg at hcon
      have hev : (p (Φ.1 : PowerSeries ℂ)).sum =ᶠ[nhds 0] 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with y hy
        exact hcon y hy
      have h0 := ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).hasFPowerSeriesAt.eq_zero_of_eventually hev
      apply Φ.2
      apply Subtype.ext
      ext n
      have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n) h0
      simpa using (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := fun n => PowerSeries.coeff n (Φ.1 : PowerSeries ℂ)) n).1 this
  obtain ⟨u, hu, hx⟩ := GlobalTheory.exists_forall_ne_zero_of_countable_analytic ℂ (Metric.ball 0 ε)
    Metric.isOpen_ball (convex_ball 0 ε).isPreconnected (Metric.nonempty_ball.2 hε) J f han hnz
  have hu0 : u ≠ 0 := hx none
  have hun : ‖u‖ < ε := mem_ball_zero_iff.1 hu
  have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hun
  let i : Subring.closure S →+* ℂ := (evalAt u).comp (Subring.inclusion hle)
  refine ⟨u, i, hu0, hun, ?_, fun Φ => rfl⟩
  refine (injective_iff_map_eq_zero i).2 fun Φ hΦ => ?_
  by_contra hne
  apply hx (some ⟨Φ, hne⟩)
  show (p (Φ : PowerSeries ℂ)).sum u = 0
  rw [hsum]
  exact hΦ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuad
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.PsiFrame

theorem char_ext {X G : Type} [AddCommGroup X] [CommGroup G] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f g : X → G)
    (hf : ∀ a b, f (a + b) = f a * f b) (hg : ∀ a b, g (a + b) = g a * g b) (h : ∀ l, f (bX l) = g (bX l)) (χ : X) :
    f χ = g χ := by
  let F : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun a b => by simp [hf])
  let G' : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (g x)) (fun a b => by simp [hg])
  have : F.toIntLinearMap = G'.toIntLinearMap := bX.ext fun l => by simp [F, G', h]
  have := LinearMap.congr_fun this χ
  simpa [F, G'] using this

def eu (z : ℂ) : ℂˣ := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

theorem eu_add (z w : ℂ) : eu (z + w) = eu z * eu w := by
  ext; simp [eu, Complex.exp_add]

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a b : X) :
    co bX (a + b) = co bX a + co bX b := by
  ext l; simp [co]

theorem co_neg {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a : X) :
    co bX (-a) = - co bX a := by
  ext l; simp [co]

theorem co_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (l : Fin r) :
    co bX (bX l) = Pi.single l 1 := by
  ext l'
  by_cases h : l' = l
  · subst h; simp [co]
  · simp [co, h, Finsupp.single_apply, Ne.symm h]

theorem exists_quad {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (Ψ : X → ℂˣ)
    (hev : ∀ a, Ψ (-a) = Ψ a)
    (hb : ∀ a a' b, Ψ (a + a' + b) / Ψ (a + a') / Ψ b = (Ψ (a + b) / Ψ a / Ψ b) * (Ψ (a' + b) / Ψ a' / Ψ b)) :
    ∃ (t : Matrix (Fin r) (Fin r) ℂ) (b2 : Fin r → ℂ), t.IsSymm ∧ Half b2 ∧ ∀ χ, (Ψ χ : ℂ) =
      Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
  classical
  set T : X → X → ℂˣ := fun a b => Ψ (a + b) / Ψ a / Ψ b with hT
  have Ts : ∀ a b, T a b = T b a := fun a b => by simp only [hT, add_comm a b, div_right_comm]
  have Tl : ∀ a a' b, T (a + a') b = T a b * T a' b := hb
  have Tr : ∀ a b b', T a (b + b') = T a b * T a b' := fun a b b' => by rw [Ts, Tl, Ts b, Ts b']
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let t : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun l l' => Complex.log (T (bX l) (bX l')) / (2 * Real.pi * Complex.I)
  have ts : t.IsSymm := by
    ext l l'; simp [t, Ts (bX l)]
  have hs : ∀ u v : Fin r → ℂ, u ⬝ᵥ t *ᵥ v = v ⬝ᵥ t *ᵥ u := fun u v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ts.eq, dotProduct_comm]
  have TQ : ∀ a b, T a b = eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)) := by
    intro a b
    refine char_ext bX (fun a => T a b) (fun a => eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tl _ _ _) (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) a
    refine char_ext bX (fun b => T (bX l) b) (fun b => eu (2 * Real.pi * Complex.I * (co bX (bX l) ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tr _ _ _) (fun _ _ => by rw [co_add, Matrix.mulVec_add, dotProduct_add, mul_add, eu_add])
      (fun l' => ?_) b
    ext
    have : Pi.single l 1 ⬝ᵥ t *ᵥ Pi.single l' 1 = t l l' := by simp
    simp only [co_basis, this, eu, Units.val_mk0, t, Matrix.of_apply]
    rw [mul_div_cancel₀ _ hc, Complex.exp_log (Units.ne_zero _)]
  let φ : X → ℂˣ := fun χ => Ψ χ / eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ))
  have φadd : ∀ a b, φ (a + b) = φ a * φ b := by
    intro a b
    have h1 : Ψ (a + b) = T a b * Ψ a * Ψ b := by
      simp only [hT]; rw [mul_right_comm, div_mul_cancel, div_mul_cancel]
    have h2 : (Real.pi * Complex.I * (co bX (a + b) ⬝ᵥ t *ᵥ co bX (a + b)) : ℂ) =
        2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b) + Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX a) +
          Real.pi * Complex.I * (co bX b ⬝ᵥ t *ᵥ co bX b) := by
      rw [co_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hs (co bX b) (co bX a)]
      ring
    simp only [φ]
    rw [h1, h2, eu_add, eu_add, ← TQ, _root_.mul_assoc, _root_.mul_assoc, mul_div_mul_left_eq_div, div_mul_div_comm]
  have φev : ∀ a, φ (-a) = φ a := fun a => by
    simp only [φ, hev, co_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  have φ0 : φ 0 = 1 := by
    have := φadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have φsq : ∀ a, (φ a : ℂ) = 1 ∨ (φ a : ℂ) = -1 := fun a => by
    have := φadd a (-a)
    rw [add_neg_cancel, φ0, φev] at this
    have h2 : (φ a : ℂ) * φ a = 1 := by rw [← Units.val_mul, ← this, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  let b2 : Fin r → ℂ := fun l => if (φ (bX l) : ℂ) = 1 then 0 else 1 / 2
  refine ⟨t, b2, ts, fun l => ?_, fun χ => ?_⟩
  · simp only [b2]; split_ifs <;> simp
  · have : φ χ = eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      refine char_ext bX φ (fun χ => eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2))) φadd
        (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) χ
      ext
      simp only [co_basis, single_dotProduct, _root_.one_mul, eu, Units.val_mk0, b2]
      split_ifs with h
      · simp [h]
      · rw [(φsq _).resolve_left h, show (2 * Real.pi * Complex.I * (1 / 2) : ℂ) = Real.pi * Complex.I by ring,
          Complex.exp_pi_mul_I]
    have h2 : Ψ χ = eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      rw [eu_add, ← this]; simp only [φ]; rw [mul_div_cancel]
    rw [h2]; rfl

theorem exists_cd (N : NumD ℂ) (g' r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (e : AB N.toNumB g') (hc : e.Cub) (hs : e.Sym) :
    ∃ d : CD N g' r bX, d.toAB = e := by
  classical
  choose z hz using fun l => e.onto (N.c (bX l))
  let t12 : Matrix (Fin g') (Fin r) ℂ := Matrix.of fun i l => z l i
  let w : N.X → Fin g' → ℂ := fun χ => t12 *ᵥ co bX χ
  have wadd : ∀ a b, w (a + b) = w a + w b := fun a b => by simp only [w, co_add, Matrix.mulVec_add]
  have wneg : ∀ a, w (-a) = - w a := fun a => by simp only [w, co_neg, Matrix.mulVec_neg]
  have ceq : ∀ χ, N.c χ = e.ex (w χ) := by
    refine char_ext bX N.c (fun χ => e.ex (w χ)) N.c_add (fun a b => by rw [wadd, e.ex_add]) (fun l => ?_)
    rw [← hz]; congr 1
    ext i; simp [w, co_basis, t12]
  obtain ⟨t, b2, ht, hb2, h⟩ := exists_quad bX (fun χ => N.ψ χ * e.fr (w χ))
    (fun a => by
      have h1 := N.even a
      have h2 := hs (w a)
      rw [wneg, ← h2, ← h1, ceq, _root_.mul_assoc])
    (fun a a' b => by
      have h1 := congrArg Additive.ofMul (N.bimult a a' b)
      have h2 := congrArg Additive.ofMul (hc (w a) (w a') (w b))
      apply Additive.ofMul.injective
      simp only [ceq, wadd, ofMul_mul, ofMul_div] at h1 h2 ⊢
      linear_combination (norm := abel) h1 - h2)
  exact ⟨{ toAB := e, cub := hc, sym := hs, t12 := t12, t22 := t, b2 := b2, toricPeriodBlock_isSymm := ht, hb2 := hb2, c_eq := ceq,
           ψ_eq := fun χ => by simpa using h χ }, rfl⟩

end GlobalTheory.MBLow.Cl.PsiFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecDivNonzeroLocusEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.Cartier.RatSecDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_mul_unit_iff {x : X} {a u : X.functionField} (hu : UnitAt x u) :
    UnitAt x (a * u) ↔ UnitAt x a := by
  refine ⟨fun h => ?_, fun h => h.mul hu⟩
  have e : a = a * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one]
  rw [e]; exact h.mul hu.inv

theorem local_of {D D' : CartierDiv X} {V : X.Opens} {h : X.functionField}
    (H : ∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V))
    {x : X} {gi rk : X.functionFieldˣ} (hi : D.IsEqn x gi) (hk : D'.IsEqn x rk) :
    RegAt x (h * (gi : X.functionField) / (rk : X.functionField)) ∧
      (UnitAt x (h * (gi : X.functionField) / (rk : X.functionField)) ↔ x ∈ V) := by
  obtain ⟨g, g', hg, hg', hr, hu⟩ := H x
  have u : UnitAt x (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) :=
    (hg.iff_unitAt.1 hi).mul (hk.iff_unitAt.1 hg')
  have e : h * (gi : X.functionField) / (rk : X.functionField) =
      h * (g : X.functionField) / (g' : X.functionField) *
        (((gi : X.functionField) / g) * ((g' : X.functionField) / rk)) := by
    have := g.ne_zero; have := g'.ne_zero; have := rk.ne_zero
    field_simp
  rw [e, unitAt_mul_unit_iff u]
  exact ⟨hr.mul u.regAt, hu⟩

end GlobalTheory.Cartier.RatSecDiv

open GlobalTheory.Cartier.RatSecDiv in

theorem GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq :
    ∀ {X : Scheme.{0}} [IsIntegral X] (D D' : CartierDiv X) (L : LB X) (r : L.ι → X.functionFieldˣ),
    Presents D' L r → ∀ (V : X.Opens) (h : X.functionField),
    (∀ x : X, ∃ g g' : X.functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧
      RegAt x (h * (g : X.functionField) / (g' : X.functionField)) ∧
      (UnitAt x (h * (g : X.functionField) / (g' : X.functionField)) ↔ x ∈ V)) →
    ∃ θ : (LB.div (toLB D) L).Sec, nonzeroLocus θ = V := by
  intro X _ D D' L r hP V h H
  have key (p : (LB.div (toLB D) L).ι) : ∃ a : Γ(X, (LB.div (toLB D) L).U p), ∀ hp,
      fnOf _ hp a = h * (p.1.1.2 : X.functionField) / (r p.2 : X.functionField) := by
    by_cases hp : genericPoint X ∈ (LB.div (toLB D) L).U p
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hp fun x hx =>
        (local_of H (p.1.2.2 x hx.1) (hP.isEqn p.2 x hx.2)).1
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (hp h').elim⟩
  choose a ha using key
  refine ⟨⟨a, fun p q => fn_ext fun hpq => ?_⟩, ?_⟩
  · have hp : genericPoint X ∈ (LB.div (toLB D) L).U p := hpq.1
    have hq : genericPoint X ∈ (LB.div (toLB D) L).U q := hpq.2
    refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg _ (fnOf_resG _ hpq _))).symm)
    rw [ha p hp, ha q hq]
    have eL := hP.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2)
    have e1 : fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val =
        (p.1.1.2 : X.functionField) / (q.1.1.2 : X.functionField) := fnOf_toLB_g _ _ _
    have eg : fnOf _ hpq ((LB.div (toLB D) L).g p q).val =
        fnOf _ (memInf hpq.1.1 hpq.2.1) ((toLB D).g p.1 q.1).val *
          (fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val)⁻¹ := by
      change fnOf _ hpq ((res _ ((toLB D).g p.1 q.1) * (res _ (L.g p.2 q.2))⁻¹ : Γ(X, _)ˣ).val) = _
      erw [Units.val_mul, map_mul, map_units_inv]
      exact congrArg₂ (· * ·) (fnOf_resG _ _ _) (congrArg _ (fnOf_resG _ _ _))
    have eL' : fnOf _ (memInf hpq.1.2 hpq.2.2) (L.g p.2 q.2).val =
        (r p.2 : X.functionField) / (r q.2 : X.functionField) :=
      (eq_div_of_mul_eq (r q.2).ne_zero eL.symm)
    rw [eg, e1, eL']
    have := (p.1.1.2).ne_zero; have := (q.1.1.2).ne_zero
    have := (r p.2).ne_zero; have := (r q.2).ne_zero
    field_simp
  · have hmem (p : (LB.div (toLB D) L).ι) (y : X) (hy : y ∈ (LB.div (toLB D) L).U p) :
        y ∈ X.basicOpen (a p) ↔ y ∈ V := by
      rw [← unitAt_fnOf_iff hy (gen_mem hy), ha p (gen_mem hy)]
      exact (local_of H (p.1.2.2 y hy.1) (hP.isEqn p.2 y hy.2)).2
    refine le_antisymm (iSup_le fun p y hy => (hmem p y (X.basicOpen_le _ hy)).1 hy) fun y hy => ?_
    obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) y
    obtain ⟨k, hk⟩ := exists_chart hP.isLB y
    exact Opens.mem_iSup.2 ⟨(i, k), (hmem (i, k) y ⟨hi, hk⟩).2 hy⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisationStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), ∃ ι : VK fw i →ₛₗ[algebraMap T.Q.c.F D.what₂.LL] (Fin (R.nW i) → D.what₂.LL), (∀ (f : VK fw i), ∃ h : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ι f = ((fw.e i ⟨f, h⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) ∧ (∀ (n : ℕ) (b : Fin n → VK fw i), LinearIndependent T.Q.c.F b → LinearIndependent D.what₂.LL (fun k => ι (b k))) ∧ ι '' (latW (T.U ((i : ℕ) + 1)) (wtZ (wtA (κ i)) (κ i).n) : Set (VK fw i)) = ((R.FW i).MK : Set (Fin (R.nW i) → D.what₂.LL)) := by
  first | exact @GlobalTheory.CovTop.SupImage.exists_emb_image_latW | exact GlobalTheory.CovTop.SupImage.exists_emb_image_latW | (intros; apply GlobalTheory.CovTop.SupImage.exists_emb_image_latW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlopeStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), HasPhi y φ → ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∃ r : ℕ, r ≤ Module.finrank ℚ E * Dw.q ∧ ShortBasis Q r ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * (r : ℝ) ^ 3 * φ) (2 * Real.sqrt r) := by
  first | exact @GlobalTheory.ShortPhi.exists_shortBasis | exact GlobalTheory.ShortPhi.exists_shortBasis | (intros; apply GlobalTheory.ShortPhi.exists_shortBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, IsTangent (ub σ k)) ∧ (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧ ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w := by
  first | exact @GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring | exact GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring | (intros; apply GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring <;> assumption)
end

