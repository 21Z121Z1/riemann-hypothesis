import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0029
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PeriodTorusConstantEqBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0023
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSymmetryTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFrame_symmetry_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  first | exact @GlobalTheory.AnVal.Sym.sy_trivial | exact GlobalTheory.AnVal.Sym.sy_trivial | (intros; apply GlobalTheory.AnVal.Sym.sy_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CubicalReadingOneAnalyticFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_reading_one_analyticFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ a b d : Fin g → ℂ, Φ.toAnFr.GenRd (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (Φ.e a) (lift (Φ.e b) (Φ.e d))).left (fun I => psumL 3 g I ![a, b, d]) 1 := by
  first | exact @GlobalTheory.cubical_reading_one | exact GlobalTheory.cubical_reading_one | (intros; apply GlobalTheory.cubical_reading_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameJetPairIsAnEStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticFrame_jetPair_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  first | exact @GlobalTheory.AnVal.exists_isAnE | exact GlobalTheory.AnVal.exists_isAnE | (intros; apply GlobalTheory.AnVal.exists_isAnE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HermFormDiagonalEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem hermForm_diagonal_eq (d z w : Fin g → ℂ) :
    hermForm (Matrix.diagonal d) z w = ∑ j, d j * z j * conj (w j) := by
  simp only [hermForm, dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  ring

theorem selfD_of_isSympl (hs : IsSympl X bas) : SelfD X X.Λ := by
  refine ⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, ha⟩ : ∃ a, (bas a : Fin r → E) = x := ⟨bas.symm ⟨x, hx⟩, by simp⟩
    obtain ⟨b, hb⟩ : ∃ b, (bas b : Fin r → E) = y := ⟨bas.symm ⟨y, hy⟩, by simp⟩
    refine ⟨-omegaStd a b, ?_⟩
    rw [← ha, ← hb, hs a b]
    push_cast
    rfl
  · have hint : ∀ c, ∃ n : ℤ, GlobalTheory.SW.crd X bas x c = n := by
      intro c
      cases c with
      | inl j =>
        obtain ⟨k, hk⟩ := h _ (bas (Pi.single (Sum.inr j) 1)).2
        have e := GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x)
          (fun c => (((Pi.single (Sum.inr j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))
        rw [GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk] at e
        simp [Pi.single_apply] at e
        exact ⟨-k, by push_cast; linarith⟩
      | inr j =>
        obtain ⟨k, hk⟩ := h _ (bas (Pi.single (Sum.inl j) 1)).2
        have e := GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x)
          (fun c => (((Pi.single (Sum.inl j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))
        rw [GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk] at e
        simp [Pi.single_apply] at e
        exact ⟨k, by linarith⟩
    choose n hn using hint
    have hx : x = (bas n : Fin r → E) := by
      rw [← GlobalTheory.SW.vecQ_crd X bas x, ← GlobalTheory.SW.vecQ_intCast]
      congr 1
      funext c
      exact hn c
    rw [hx]
    exact (bas n).2

theorem hx_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, X.IsOrtho x → (∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j)) ∧ (∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re = ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u)) ∧ (∀ u ∈ X.Λ, u ≠ 0 → X.firstMinimumSq x ≤ (hx X bas idx x (pv X idx x u) (pv X idx x u)).re) ∧ IsUnitFr X x ∧ SelfD X X.Λ := by
  intro E _ _ _ r X g bas idx hs x hxd ho
  have hHm := GlobalTheory.ThFr.Hm_of_isOrtho idx hs ho
  have h1 : ∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j) := by
    intro z z'
    rw [hx_eq_hermForm idx x z z', hHm, hermForm_diagonal_eq]
  have h2 : ∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re =
      ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u) := by
    intro u
    rw [hx_eq_hermForm idx x, hHm]
    exact (congrArg Complex.re (GlobalTheory.ThFr.hermForm_diagonal_c_self idx hxd ho u)).trans
      (Complex.ofReal_re _)
  have h0 : ∀ z, 0 ≤ (hx X bas idx x z z).re := by
    intro z
    rw [h1, Complex.re_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    have e : ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z j) =
        ((X.c (idx j).1 * Complex.normSq (z j) : ℝ) : ℂ) := by
      rw [_root_.mul_assoc, Complex.mul_conj]
      push_cast
      ring
    rw [e, Complex.ofReal_re]
    exact mul_nonneg (GlobalTheory.ThFr.c_pos X _).le (Complex.normSq_nonneg _)
  refine ⟨h1, h2, ?_, ?_, selfD_of_isSympl hs⟩
  · intro u hu hne
    rw [h2]
    unfold Data.firstMinimumSq
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro t ⟨v, -, -, rfl⟩
      rw [← h2]
      exact h0 _
    · exact ⟨u, hu, hne, rfl⟩
  · unfold IsUnitFr
    intro τ i
    unfold dmin lminor
    rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp_apply, Complex.norm_real]
    unfold sgn
    split_ifs <;> simp

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NetSizeCubic
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.NetSize

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_two_lt_d9; linarith

lemma eps_pos {M f w k : ℝ} (hM : 1 ≤ M) (hf : 1 ≤ f) (hw : 0 < w) (hk : 0 < k) :
    0 < epStar M f w k := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := Real.pi_pos
  unfold epStar
  exact lt_min one_pos (by positivity)

lemma neg_log_eps_le {M f w k L : ℝ} (hM : 1 ≤ M) (hf : 1 ≤ f) (hw : 0 < w) (hk : 0 < k)
    (hL : 1 ≤ L) (h1 : Real.log f ≤ 2 * L) (h2 : Real.log M ≤ 30 * L)
    (h3 : Real.log w ≤ 3 * L) (h4 : Real.log k ≤ 4 * L) :
    -Real.log (epStar M f w k) ≤ 41 * L := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := Real.pi_gt_three
  have hl1 := log_two_le_one
  unfold epStar
  rcases le_total 1 (Real.pi / (M * (f * w + 2) * k * Real.log 2)) with h | h
  · rw [min_eq_left h, Real.log_one]; linarith
  · rw [min_eq_right h]
    have hf0 : 0 < f := by linarith
    have hM0 : 0 < M := by linarith
    have hfw : f * w ≤ Real.exp (5 * L) := by
      rw [← Real.log_le_iff_le_exp (by positivity), Real.log_mul hf0.ne' hw.ne']
      linarith
    have he : 1 ≤ Real.exp (5 * L) := Real.one_le_exp (by linarith)
    have hA : Real.log (f * w + 2) ≤ 7 * L := by
      have h5 : f * w + 2 ≤ 2 ^ 2 * Real.exp (5 * L) := by linarith
      have h6 := Real.log_le_log (by positivity) h5
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp] at h6
      push_cast at h6
      linarith
    have hB : Real.log (Real.log 2) ≤ Real.log Real.pi :=
      Real.log_le_log hl2 (by linarith)
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hl2.ne',
      Real.log_mul (by positivity) hk.ne', Real.log_mul hM0.ne' (by positivity)]
    linarith

theorem net_size_cubic : ∀ (f r L M w k0 dE s NA NC g : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ L → 1 ≤ M → 0 < w → 0 < k0 → 1 ≤ dE → 0 ≤ s → 1 ≤ NA → 1 ≤ NC → 1 ≤ g → Real.log f ≤ 2 * L → Real.log r ≤ L → Real.log M ≤ 30 * L → Real.log w ≤ 3 * L → Real.log k0 ≤ 4 * L → Real.log dE ≤ 4 * f * L → Real.log (1 + s) ≤ 3 * L → Real.log NA ≤ 30 * f * L → Real.log NC ≤ 30 * f * L → Real.log g ≤ 30 * f * L → 2 * f * r ^ 2 * Real.log (3 * NA * NC * g * r * (max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * epStar M f w k0))) ^ 2) + (2 * f * r ^ 2 * Real.log (6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s)))) + 2 * f * r ^ 3 * Real.log (r * max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * epStar M f w k0)))) + Real.log 16 ≤ 1000 * (f * r * L) ^ 3 := by
  intro f r L M w k0 dE s NA NC g hf hr hL hM hw hk hd hs hNA hNC hg lf lr lM lw lk ld ls lA lC lg
  have he := eps_pos hM hf hw hk
  have hle := neg_log_eps_le hM hf hw hk hL lf lM lw lk
  have hl1 := log_two_le_one
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set ε := epStar M f w k0
  have hf0 : 0 < f := by linarith
  have hr0 : 0 < r := by linarith
  have hL0 : 0 < L := by linarith
  have hd0 : 0 < dE := by linarith
  have hNA0 : 0 < NA := by linarith
  have hNC0 : 0 < NC := by linarith
  have hg0 : 0 < g := by linarith
  have hfL : L ≤ f * L := le_mul_of_one_le_left hL0.le hf
  set B := max 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * ε)) with hBdef
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := by linarith
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : Real.log B ≤ 65 * (f * L) := by
    rcases le_total 1 ((2 * f * r) ^ 4 * dE ^ 2 / (4 * ε)) with h | h
    · rw [hBdef, max_eq_right h, Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      push_cast
      linarith
    · rw [hBdef, max_eq_left h, Real.log_one]; positivity
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  have T1 : Real.log (3 * NA * NC * g * r * B ^ 2) ≤ 223 * (f * L) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  have h6 : Real.log 6000 ≤ 13 := by
    have h := Real.log_le_log (show (0:ℝ) < 6000 by norm_num) (show (6000:ℝ) ≤ 2 ^ 13 by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have T2 : Real.log (6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s)))) ≤ 20 * (f * L) := by
    have e : 6 * r ^ 2 / (1 / (1000 * r ^ 2 * (1 + s))) = 6000 * r ^ 4 * (1 + s) := by
      field_simp; ring
    rw [e, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  have T3 : Real.log (r * B) ≤ 66 * (f * L) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    linarith
  have T4 : Real.log 16 ≤ 4 := by
    have : (16:ℝ) = 2 ^ 4 := by norm_num
    rw [this, Real.log_pow]; push_cast; linarith
  have hr23 : r ^ 2 ≤ r ^ 3 := pow_le_pow_right₀ hr (by norm_num)
  have hP : f * r ^ 3 * (f * L) ≤ (f * r * L) ^ 3 := by
    have h1 : 1 ≤ f * L ^ 2 := one_le_mul_of_one_le_of_one_le hf (one_le_pow₀ hL)
    calc f * r ^ 3 * (f * L) ≤ f * r ^ 3 * (f * L) * (f * L ^ 2) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = (f * r * L) ^ 3 := by ring
  have hQ : f * r ^ 2 * (f * L) ≤ f * r ^ 3 * (f * L) := by gcongr
  have hone : 1 ≤ (f * r * L) ^ 3 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) hL)
  have U1 := mul_le_mul_of_nonneg_left T1 (show 0 ≤ 2 * f * r ^ 2 by positivity)
  have U2 := mul_le_mul_of_nonneg_left T2 (show 0 ≤ 2 * f * r ^ 2 by positivity)
  have U3 := mul_le_mul_of_nonneg_left T3 (show 0 ≤ 2 * f * r ^ 3 by positivity)
  linarith

end GlobalTheory.NetSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedPullbackMulNReadsTheta
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section MulN

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
  (Φ : AnFr A L x0 g)

theorem mulN_e_zero : Φ.e 0 = 1 := by
  have h := Φ.e_add 0 0
  rw [add_zero] at h
  simpa using h

theorem mulN_e_nsmul (N : ℕ) (z : Fin g → ℂ) : Φ.e ((N : ℂ) • z) = Φ.e z ^ N := by
  induction N with
  | zero => simp [mulN_e_zero Φ]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, Φ.e_add, ih, pow_succ]

omit [IsCommMonObj A] in
theorem mulN_comp {Z : Over S} (y : Z ⟶ A) (N : ℕ) : y ≫ mulA A N = y ^ N := by
  unfold mulA
  induction N with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

omit [IsCommMonObj A] in
theorem mulN_eSec (N : ℕ) : eSec A ≫ (mulA A N).left = eSec A := by
  have h1 : (η : 𝟙_ (Over S) ⟶ A) = 1 := by
    have h0 : (1 : 𝟙_ (Over S) ⟶ A) = toUnit _ ≫ η := rfl
    simpa using h0.symm
  have h := mulN_comp (η : 𝟙_ (Over S) ⟶ A) N
  rw [h1, one_pow] at h
  unfold eSec
  rw [← Over.comp_left, h1, h]

theorem mulN_genRd (N : ℕ)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (hg : α₀.IsGen) (hn : IsNormMul A L.L L.rig N α₀) (z : Fin g → ℂ) :
    Φ.GenRd ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1] α₀ (Φ.e z).left ![z, (N : ℂ) • z] 1 := by
  have hφ : ∀ (z : Fin g → ℂ) (k : Fin 2), (Φ.e z).left ≫ (![𝟙 A.left, (mulA A N).left] : Fin 2 → (A.left ⟶ A.left)) k
      = (Φ.e ((![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)).left := by
    intro z k
    fin_cases k
    · simp
    · simp [← Over.comp_left, mulN_comp, mulN_e_nsmul]
  have hper : ∀ gm ∈ Φ.lat, (∀ z, (Φ.e (z + gm)).left = (Φ.e z).left) ∧
      ∀ k, (![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k gm ∈ Φ.lat := by
    intro gm hgm
    refine ⟨fun z => by rw [Φ.genMove_e_per z gm hgm], fun k => ?_⟩
    fin_cases k
    · simpa using hgm
    · simpa [Nat.cast_smul_eq_nsmul] using Φ.lat.nsmul_mem hgm N
  have hherm : ∀ z w, ∑ k, (((![(N : ℤ) ^ 2, -1] : Fin 2 → ℤ) k : ℤ) : ℂ) *
      hermForm Φ.Hm ((![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)
        ((![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k w) = 0 := by
    intro z w
    simp [Fin.sum_univ_two, hermForm]
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    ring
  obtain ⟨⟨v, -, hv⟩, -⟩ := GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel S A L x0 g Φ A.left (Fin 2) ![𝟙 A.left, (mulA A N).left]
    ![(N : ℤ) ^ 2, -1] α₀ hg g (fun z => (Φ.e z).left) ![LinearMap.id, (N : ℂ) • LinearMap.id] Φ.lat Φ.hol hφ
    Φ.span hper hherm
  have hrig : Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => 1) L.rig x0 (fun _ => 0) 1 := by
    refine ⟨fun _ => (Φ.genMove_e_zero_left).symm, fun j hj => ?_⟩
    have hj' := (GlobalTheory.AnValGenCorr.chart_iff _ _ _ _).mp hj PUnit.unit
    rw [← Φ.genMove_e_zero_left] at hj'
    simp
    exact (Φ.fr_0 (j PUnit.unit) hj').symm
  have h0 := hv 0
  rw [Φ.genMove_e_zero_left] at h0
  have h0' := (Φ.genRd_pullGen_iff _ _ α₀ (eSec A) x0 _ v).mpr h0
  have hinv := (GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ S PUnit PUnit _ _ _ _ L.rig L.rig x0 _ _ 1 1
    hrig hrig).2.2.2
  have hpow := Φ.genRd_rigPow ((N : ℤ) ^ 2)
  have hmul := (GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ _ PUnit PUnit _ _ _ _ _ _ x0 _ _ 1 _
    hpow hinv).2.2.1
  have hv1 := (GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ _ (Fin 2) (PUnit ⊕ PUnit) _ _ _ _ _ _ x0 _ _ v _
    h0' hmul).2.1 hn ?ss ⟨fun _ => 0, ?pa, ?pb⟩
  · simp at hv1
    subst hv1
    have hz := hv z
    have hp : (fun k => (![LinearMap.id, (N : ℂ) • LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k z)
        = ![z, (N : ℂ) • z] := by
      funext k
      fin_cases k <;> simp
    rw [hp] at hz
    exact hz
  · unfold LB.SameSum
    intro ψ
    have e0 : eSec A ≫ 𝟙 A.left = eSec A := Category.comp_id _
    have e1 : eSec A ≫ (mulA A N).left = eSec A := mulN_eSec N
    simp [Fin.sum_univ_two, Fintype.sum_sum_type]
    split_ifs <;> simp_all
  · intro k
    fin_cases k <;> simp
  · rintro (_ | _) <;> rfl

end MulN

theorem rd_mulN : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (N : ℕ) (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])) (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] ![(N : ℤ) ^ 2, -1])) (s : LB.Sec (LPow A L.L 1 (Over.mk x0))) (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), α₀.IsGen → IsNormMul A L.L L.rig N α₀ → LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd (Over.mk x0) A).left) → IsTwistPull A L.L (mulT A (Over.mk x0) N) (snd (Over.mk x0) A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ → Φ.Rd 1 s θ → Φ.Rd ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by
  intro S A _ _ L x0 g Φ N α₀ α s s₁ θ h1 h2 h3 h4 h5
  have hψ : mulT A (Over.mk x0) N ≫ fst (Over.mk x0) A = fst (Over.mk x0) A := by
    unfold mulT
    simp
  have hsnd : ∀ z, (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A).left = (Φ.e z).left := by
    intro z
    unfold ptSecT
    rw [← Over.comp_left]
    simp
  have hsN : (snd (Over.mk x0) A).left ≫ (mulA A N).left = (snd (Over.mk x0) A ^ N).left := by
    rw [← Over.comp_left, mulN_comp]
  have hpt : ∀ z, (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A ^ N).left = (Φ.e ((N : ℂ) • z)).left ∧
      ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ
          LB.wchart L.L ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] j ∧
        valAt' (ptSecT A (Φ.e z)).left
            (LB.wchart L.L ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] j) (α.s j).val =
          (fun _ => (1 : ℂ)) z * (Φ.fr (j 0) z ^ ((N : ℤ) ^ 2) * Φ.fr (j 1) ((N : ℂ) • z) ^ (-(1 : ℤ))) := by
    intro z
    have hqm : (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A ^ N).left = (Φ.e ((N : ℂ) • z)).left := by
      rw [← hsN, ← Category.assoc, hsnd, ← Over.comp_left, mulN_comp, mulN_e_nsmul]
    refine ⟨hqm, ?_⟩
    have hg := mulN_genRd Φ N α₀ h1 h2 z
    rw [← hsnd z] at hg
    have hpull := (Φ.genRd_pullGen_iff _ _ α₀ (snd (Over.mk x0) A).left (ptSecT A (Φ.e z)).left _ 1).mpr hg
    obtain ⟨J, hJ⟩ : ∃ J : ((Over.mk x0 ⊗ A).left ⟶ A.left) → L.L.ι,
        ∀ ψ, ⊤ ≤ ((ptSecT A (Φ.e z)).left ≫ ψ) ⁻¹ᵁ L.L.U (J ψ) :=
      ⟨fun ψ => (GlobalTheory.AnValGenCorr.exists_chart L.L L.3 ((ptSecT A (Φ.e z)).left ≫ ψ)).choose,
        fun ψ => (GlobalTheory.AnValGenCorr.exists_chart L.L L.3 ((ptSecT A (Φ.e z)).left ≫ ψ)).choose_spec⟩
    have hcv := GlobalTheory.AnValGenCorr.corr_val L.L _ _ _ _ α _ h3 J (ptSecT A (Φ.e z)).left hJ
    refine ⟨fun k => J (![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ^ N).left] k),
      (GlobalTheory.AnValGenCorr.chart_iff _ _ _ _).mpr (fun k => hJ _), ?_⟩
    rw [hcv, hpull.2 _ ((GlobalTheory.AnValGenCorr.chart_iff _ _ _ _).mpr (fun k => hJ _))]
    have hs0 : (snd (Over.mk x0) A).left ≫ (![𝟙 A.left, (mulA A N).left] : Fin 2 → (A.left ⟶ A.left)) 0 =
        (snd (Over.mk x0) A).left := Category.comp_id _
    have hs1 : (snd (Over.mk x0) A).left ≫ (![𝟙 A.left, (mulA A N).left] : Fin 2 → (A.left ⟶ A.left)) 1 =
        (snd (Over.mk x0) A ^ N).left := hsN
    simp only [Fin.prod_univ_two, hs0, hs1]
    simp
  have res := AnFr.rd_twistPull S A L x0 g Φ (mulT A (Over.mk x0) N) (snd (Over.mk x0) A ^ N) (lift_snd _ _)
    ((N : ℤ) ^ 2) 1 α s s₁ θ (fun z => (N : ℂ) • z) (fun _ => 1) hψ h4 h5 hpt
  simpa using res

end GlobalTheory.AnVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ProjAEqSumReps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VacMean

open GlobalTheory.SW.TensVac GlobalTheory.SW.TensLat

theorem projA_eq_sum_reps {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E}
    {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)} (hA : Good X w A) (hA' : Good X w A')
    {v : TF n g} (hv : IsVac X bas w A' v) {R : Finset (Matrix (Fin n) (Fin r) E)}
    (hR : ∀ y ∈ R, y ∈ A) (hR' : ∀ y ∈ A, ∃! y' ∈ R, y - y' ∈ A') :
    projA X bas w A v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v := by
  have hfix : ∀ y, epsW X w y • heisG X bas y v = v ↔ y ∈ A' := by
    refine fun y => ⟨fun h => ?_, hv.2.2 y⟩
    by_contra hy
    have := hA'.ip_eq_zero idx hs hn hv hy
    rw [h, hv.2.1] at this
    exact one_ne_zero this
  have hiff : ∀ a ∈ A, ∀ b ∈ A, epsW X w a • heisG X bas a v = epsW X w b • heisG X bas b v ↔
      b - a ∈ A' := by
    intro a ha b hb
    rw [← neg_add_eq_sub, ← hfix, ← hA.rho_rho idx hs hn (A.neg_mem ha) hb hv.1]
    constructor
    · intro h
      rw [← h, hA.rho_rho idx hs hn (A.neg_mem ha) ha hv.1, neg_add_cancel,
        rho_zero idx hs hn hv.1]
    · intro h
      conv_lhs => rw [← h]
      rw [hA.rho_rho idx hs hn ha (A.neg_mem ha) (rho_sb idx hs hn b hv.1), add_neg_cancel,
        rho_zero idx hs hn (rho_sb idx hs hn b hv.1)]
  have hinj : Set.InjOn (fun y => epsW X w y • heisG X bas y v) R := fun a ha b hb h =>
    (hR' b (hR b hb)).unique ⟨ha, (hiff a (hR a ha) b (hR b hb)).1 h⟩
      ⟨hb, by rw [sub_self]; exact A'.zero_mem⟩
  have himg : (fun y => epsW X w y • heisG X bas y v) '' A =
      (fun y => epsW X w y • heisG X bas y v) '' R := by
    refine Set.Subset.antisymm ?_ (Set.image_mono fun y hy => hR y hy)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', ⟨h1, h2⟩, -⟩ := hR' y hy
    exact ⟨y', h1, (hiff y' (hR y' h1) y hy).2 h2⟩
  rw [projA, himg, finsum_mem_image hinj, finsum_mem_coe_finset, hinj.ncard_image,
    Set.ncard_coe_finset]

theorem vac_proj_mean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∃ R : Finset (Matrix (Fin n) (Fin r) E), (∀ y ∈ R, y ∈ tens Λ L) ∧ (∀ y ∈ tens Λ L, ∃! y', y' ∈ R ∧ ∀ b, y b - y' b ∈ L) ∧ R.card = ((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup) ^ r ∧ 0 < R.card ∧ projA X bas (w : E) (tens Λ L) v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X (w : E) y • heisG X bas y v := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn w hw L hL Λ hΛ v hv
  have good (Λ) (hΛ : Λ ∈ Vset E n 1) : Good X (w : E) (tens Λ L) :=
    ⟨tens_fg hΛ hL.1, tens_selfDual hΛ hL, fun y hy => epsW_semichar hΛ hL w.isIntegral_coe hw hy⟩
  have hS := GlobalTheory.SW.Base.stdL_mem_Vset (E := E) n 1
  have hidx := (tens_selfDual_semichar_index E r X g bas idx n hs hn w w.isIntegral_coe hw L hL 1
    Λ hΛ).2.2.2.2.2 _ hS
  obtain ⟨v', hv', -⟩ := (good Λ hΛ).vac hs
  have hne : (tens (stdL E n) L).relIndex (tens Λ L) ≠ 0 := by
    intro h
    have := (good Λ hΛ).overlap idx hs hn (good _ hS) hv' hv
    rw [h] at this
    simp at this
  obtain ⟨R, hR, hR'⟩ := TensorLat.exists_reps_of_relIndex_ne_zero hne
  have hc := TensorLat.card_eq_relIndex_of_reps hR hR'
  refine ⟨R, hR, fun y hy => ?_, hc.trans hidx, hc ▸ Nat.pos_of_ne_zero hne,
    projA_eq_sum_reps idx hs hn (good Λ hΛ) (good _ hS) hv hR hR'⟩
  have := hR' y hy
  simp only [mem_tens_stdL] at this
  exact this

end GlobalTheory.Dict.VacMean
end

