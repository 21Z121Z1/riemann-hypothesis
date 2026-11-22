import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0028
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralCongrWeakApproximation
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0047
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
import ReciprocityTheory.SemistableReduction.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.RApprox
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0046
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenSectT

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspRestrictComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

private theorem evC_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h : GenFrEx Xo c) (Z : Comp Xo c)
    (f g : Rul Xo c) : evC h Z (f * g) = evC h Z f * evC h Z g := by
  show evR Xo c (f * g) (genFr h Z) = evR Xo c f (genFr h Z) * evR Xo c g (genFr h Z)
  unfold evR evalAt
  split
  · exact map_mul _ _ _
  · simp

theorem exists_cusp_restrict_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (Z : Comp Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∃ g' ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g' = evC h Z g ∧ ∀ Z', Z' ≠ Z → evC h Z' g' = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA r U hU Z a n g hg
  obtain ⟨χ, hχ, hidem, h1, h0⟩ := GlobalTheory.T.exists_idempotent_weightZero_section_of_component E H Dw l Xo c hL h hA Z
  refine ⟨χ * g, GlobalTheory.Reg.IdemCusp.idem_mul_mem_cusp E H Dw l Xo c r U hU χ hχ hidem a n g hg, ?_, ?_⟩
  · rw [evC_mul' h Z, h1, _root_.one_mul]
  · intro Z' hZ'
    rw [evC_mul' h Z', h0 Z' hZ']
    simp

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralCongrWeakApproximationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_congr_weak_approximation : ∀ (Ω : Type) [Field Ω] (ι : Type) [Finite ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))), (∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) → (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) → ∀ (i₀ : ι) (a : Ω), v i₀ a ≤ 1 → ∃ a' : Ω, (∀ i, v i a' ≤ 1) ∧ v i₀ (a - a') < 1 := by
  first | exact @GlobalTheory.WeakApprox.exists_integral_congr | exact GlobalTheory.WeakApprox.exists_integral_congr | (intros; apply GlobalTheory.WeakApprox.exists_integral_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsEveryFinitePlace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem isDiscreteValuationRing_valuationSubring_place {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (la.valuation K).valuationSubring :=
  (la.valuation K).valuationSubring_isDiscreteValuationRing

theorem exists_sCharts : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ := by
  intro hST E _ _ _ H Dw l Xo c hEv hDiag la hM
  obtain ⟨Y, hY⟩ := hM
  have := isDiscreteValuationRing_valuationSubring_place la

  obtain ⟨J, hJ, P, hP⟩ := GlobalTheory.T.exists_finite_integral_chart_cover_flagSpace hST E H Dw l Xo c hEv.bc (la.valuation c.F).valuationSubring Y hY
  have := hJ
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_normal_charts_of_covering_charts E H Dw l Xo c hEv hDiag la J P hP
  refine ⟨⟨S, hS⟩, fun a n m ws hws hnz => ?_⟩

  obtain ⟨J', hJ', P', hP', hF⟩ := GlobalTheory.T.exists_refined_covering_chart_family E H Dw l Xo c hEv _ _ J P hP a n m ws hws hnz
  have := hJ'
  obtain ⟨S', hS', hW⟩ := GlobalTheory.T.exists_normal_charts_of_covering_charts E H Dw l Xo c hEv hDiag la J' P' hP'
  exact ⟨S', hW m ws hF, hS'⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRatioFormsAtPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.ConstRatio

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev Deg (wL : WeightFamilies.Wt D j) (m : ℕ) : Submodule B.KO X.Forms :=
  LinearMap.range (X.inc (addL (wt0 D j) wL m))

theorem deg_mul {m n : ℕ} {x y : X.Forms} (hx : x ∈ Deg X wL m) (hy : y ∈ Deg X wL n) :
    x * y ∈ Deg X wL (m + n) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  have h : X.inc _ F * X.inc _ G ∈
      LinearMap.range (X.inc (wadd (addL (wt0 D j) wL m) (addL (wt0 D j) wL n))) := by
    obtain ⟨H, hH⟩ := X.inc_mul _ _ F G
    exact ⟨H, hH.symm⟩
  rwa [wadd_addL_addL, zero_weight_add] at h

theorem deg_one (F : B.Cusp j wL) : X.inc wL F ∈ Deg X wL 1 := by
  have h : X.inc wL F ∈ LinearMap.range (X.inc wL) := ⟨F, rfl⟩
  unfold Deg
  rwa [add_zero_weight_one_eq]

theorem deg_wsmul (k : ℕ) (g : B.Cusp j (wsmul k wL)) : X.inc (wsmul k wL) g ∈ Deg X wL k := by
  have h : X.inc _ g ∈ LinearMap.range (X.inc (wsmul k wL)) := ⟨g, rfl⟩
  unfold Deg
  rwa [addL, zero_weight_add]

theorem deg_mul_pow {m : ℕ} {y x : X.Forms} (hy : y ∈ Deg X wL m) (hx : x ∈ Deg X wL 1) (e : ℕ) :
    y * x ^ e ∈ Deg X wL (m + e) := by
  induction e with
  | zero => simpa using hy
  | succ e ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact deg_mul X ih hx

theorem deg_mul_prod (d : Fin N →₀ ℕ) {m : ℕ} {y : X.Forms} (hy : y ∈ Deg X wL m) (s : Finset (Fin N)) :
    y * ∏ i ∈ s, X.inc wL (w i) ^ d i ∈ Deg X wL (m + ∑ i ∈ s, d i) := by
  classical
  refine Finset.induction_on s (by simpa using hy) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have e1 : y * (X.inc wL (w a) ^ d a * ∏ i ∈ s, X.inc wL (w i) ^ d i) =
      (y * ∏ i ∈ s, X.inc wL (w i) ^ d i) * X.inc wL (w a) ^ d a := by ring
  have e2 : m + (d a + ∑ i ∈ s, d i) = m + ∑ i ∈ s, d i + d a := by ring
  rw [e1, e2]
  exact deg_mul_pow X ih (deg_one X (w a)) (d a)

theorem deg_mul_aeval {k : ℕ} (Pw : MvPolynomial (Fin N) B.KO) (hPw : Pw.IsHomogeneous k) {m : ℕ} {y : X.Forms}
    (hy : y ∈ Deg X wL m) :
    y * MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw ∈ Deg X wL (m + k) := by
  classical
  rw [Pw.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, mul_left_comm, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = k := by
    have := hPw (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h := deg_mul_prod X w d hy d.support
  rw [hdeg] at h
  exact h

theorem ratio_large {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (hB : CurveLoc.BirAt X N w gF) (k0 : Fin N) (hk0 : gF (X.inc wL (w k0)) ≠ 0) (a : Ω) :
    ∃ k : ℕ, ∀ m, k < m → ∃ n d : B.Cusp j (addL (wt0 D j) wL m),
      gF (X.inc _ d) ≠ 0 ∧ gF (X.inc _ n) = a * gF (X.inc _ d) := by
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB a
  refine ⟨k, fun m hm => ?_⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hm
  have h1 : X.inc wL (w k0) * X.inc wL (w k0) ^ e ∈ Deg X wL (1 + e) :=
    deg_mul_pow X (deg_one X (w k0)) (deg_one X (w k0)) e
  have hd := deg_mul_aeval X w Pw hPw h1
  have hn := deg_mul X h1 (deg_wsmul X k g)
  have e1 : 1 + e + k = k + e + 1 := by ring
  rw [e1] at hd hn
  obtain ⟨d, hd⟩ := hd
  obtain ⟨n, hn⟩ := hn
  have hPv : gF (MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw) =
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw :=
    MvPolynomial.comp_aeval_apply (fun i => X.inc wL (w i)) gF Pw
  refine ⟨n, d, ?_, ?_⟩
  · rw [hd, map_mul, map_mul, map_pow, hPv]
    exact mul_ne_zero (mul_ne_zero hk0 (pow_ne_zero _ hk0)) hne
  · rw [hd, hn, map_mul, map_mul gF _ (MvPolynomial.aeval _ Pw), hPv, ← he]
    ring

end GlobalTheory.ConstRatio

namespace GlobalTheory

open ConstRatio in

theorem exists_ratio_forms_at_points : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (Pt : Type) [Finite Pt] (U : Pt → Type) [∀ ζ, Field (U ζ)] (ev : ∀ ζ, Rp X la N →+* U ζ) (ι : Type) (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) (Zc : Pt → ι) (jz : ∀ ζ, Ω (Zc ζ) →+* U ζ), (∀ ζ, ∃ k, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc wL (w k))) ≠ 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), gF (Zc ζ) (X.inc u F) = 0 → ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F)) = 0) → (∀ ζ (u : WeightFamilies.Wt D j) (F F' : B.Cusp j u), jz ζ (gF (Zc ζ) (X.inc u F)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F')) = jz ζ (gF (Zc ζ) (X.inc u F')) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc u F))) → (∀ Z, CurveLoc.BirAt X N w (gF Z)) → (∀ Z (u : WeightFamilies.Wt D j) (F : B.Cusp j u), ∃ F' : B.Cusp j u, gF Z (X.inc u F') = gF Z (X.inc u F) ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc u F') = 0) → ∀ a : ∀ Z, Ω Z, ∃ (k : ℕ) (F F' : B.Cusp j (addL (wt0 D j) wL k)), ∀ ζ, ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) ≠ 0 ∧ ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F)) = jz ζ (a (Zc ζ)) * ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ F')) := by
  intro D B P j X la N wL w Pt _ U _ ev ι Ω _ _ gF Zc jz h1 h2 h3 hB hs a
  classical
  haveI := Fintype.ofFinite Pt
  choose k0 hk0 using h1
  have hg0 : ∀ ζ, gF (Zc ζ) (X.inc wL (w (k0 ζ))) ≠ 0 := fun ζ h => hk0 ζ (h2 ζ wL _ h)
  choose K hK using fun ζ => ratio_large X w (gF (Zc ζ)) (hB _) (k0 ζ) (hg0 ζ) (a _)
  set M : ℕ := Finset.univ.sup K with hM
  have hlt : ∀ ζ, K ζ < 1 + M := fun ζ => by
    have : K ζ ≤ M := Finset.le_sup (f := K) (Finset.mem_univ ζ)
    omega
  have key : ∀ Z, ∃ n d : B.Cusp j (addL (wt0 D j) wL (1 + M)),
      (∀ Z', Z' ≠ Z → gF Z' (X.inc _ n) = 0 ∧ gF Z' (X.inc _ d) = 0) ∧
      (Z ∈ Set.range Zc → gF Z (X.inc _ d) ≠ 0 ∧ gF Z (X.inc _ n) = a Z * gF Z (X.inc _ d)) := by
    intro Z
    by_cases hZ : Z ∈ Set.range Zc
    · obtain ⟨ζ, rfl⟩ := hZ
      obtain ⟨n, d, hd, hn⟩ := hK ζ _ (hlt ζ)
      obtain ⟨n', hn1, hn2⟩ := hs (Zc ζ) _ n
      obtain ⟨d', hd1, hd2⟩ := hs (Zc ζ) _ d
      refine ⟨n', d', fun Z' h => ⟨hn2 Z' h, hd2 Z' h⟩, fun _ => ?_⟩
      rw [hn1, hd1]
      exact ⟨hd, hn⟩
    · exact ⟨0, 0, fun Z' _ => by simp, fun h => absurd h hZ⟩
  choose n d hoff hon using key
  have hsum : ∀ (f : ι → B.Cusp j (addL (wt0 D j) wL (1 + M))),
      (∀ Z Z', Z' ≠ Z → gF Z' (X.inc _ (f Z)) = 0) → ∀ ζ,
      gF (Zc ζ) (X.inc _ (∑ Z ∈ Finset.univ.image Zc, f Z)) = gF (Zc ζ) (X.inc _ (f (Zc ζ))) := by
    intro f hf ζ
    rw [map_sum, map_sum]
    exact Finset.sum_eq_single_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ ζ))
      fun Z _ h => hf Z _ h.symm
  refine ⟨1 + M, ∑ Z ∈ Finset.univ.image Zc, n Z, ∑ Z ∈ Finset.univ.image Zc, d Z, fun ζ => ?_⟩
  have hn := hsum n (fun Z Z' h => (hoff Z Z' h).1) ζ
  have hd := hsum d (fun Z Z' h => (hoff Z Z' h).2) ζ
  obtain ⟨o1, o2⟩ := hon (Zc ζ) ⟨ζ, rfl⟩
  rw [← hd] at o1
  rw [← hd, ← hn] at o2
  generalize (∑ Z ∈ Finset.univ.image Zc, n Z) = F at o2 ⊢
  generalize (∑ Z ∈ Finset.univ.image Zc, d Z) = F' at o1 o2 ⊢
  have hj : jz ζ (gF (Zc ζ) (X.inc _ F')) ≠ 0 := (map_ne_zero _).2 o1
  constructor
  · obtain ⟨G, hG⟩ := deg_mul_pow X (deg_one X (w (k0 ζ))) (deg_one X (w (k0 ζ))) M
    have hev : ev ζ (Formalism.MainNotions.Gaps.EtaleWeightGaps.emb X la N (X.inc _ G)) ≠ 0 := by
      rw [hG, map_mul, map_mul, map_pow, map_pow]
      exact mul_ne_zero (hk0 ζ) (pow_ne_zero _ (hk0 ζ))
    intro h0
    have h := h3 ζ _ F' G
    rw [h0, mul_zero] at h
    exact mul_ne_zero hj hev h
  · have h := h3 ζ _ F F'
    rw [o2, map_mul] at h
    apply mul_left_cancel₀ hj
    rw [← h]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSubfieldValuationClosureStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subfield_valuation_closure' : ∀ (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (S : Subfield U), ∃ S' : Subfield U, ∀ u, u ∈ S' ↔ ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ s ∈ S, v (u - s) < γ := by
  first | exact @GlobalTheory.exists_subfield_valuation_closure | exact GlobalTheory.exists_subfield_valuation_closure | (intros; apply GlobalTheory.exists_subfield_valuation_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FiniteReducedSection
section
noncomputable section

namespace GlobalTheory.CurveRecord

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

theorem finite_reduced_of_eq {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
    [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K'] [CharZero K] {Dd m : ℕ}
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = Dd)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = Dd)
    (t : Fin (Dd + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    FiniteDimensional K' (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) ∧
      IsReduced (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) := by
  have e : a = GenSect.tsec K Kl t v := funext fun i => ha i
  subst e
  have := GenSect.s1T (Kl := Kl) hfg htr v k₀ hv₀ hbig t ht
  unfold GenSect.tJ at this
  exact this

set_option maxHeartbeats 1000000 in

theorem tv_indep {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) [Algebra B.KO (Kp X la N)]
    [IsScalarTower B.KO (X.Kl la) (Kp X la N)] :
    AlgebraicIndependent B.KO (fun p : Idx D j N => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have h0 := (MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)).map' hinj
  have h1 := h0.map' (f := IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N))
    (IsFractionRing.injective (Op X la N) (Kp X la N))
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic _ (nonZeroDivisors (X.Ol la))
  have h2 := (Algebra.IsAlgebraic.algebraicIndependent_iff (X.Ol la) (X.Kl la)).mp h1
  have h3 := h2.restrictScalars (R := B.KO) (algebraMap B.KO (X.Kl la)).injective
  have hfun : (fun p : Idx D j N => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) =
      ⇑(IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)) ∘
        (⇑(IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) ∘ MvPolynomial.X) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, Tv]
  rw [hfun]
  exact h3

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem rzMap_sec_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem map_Jid_eq : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

theorem finite_reduced_record
    (hfg : (⊤ : IntermediateField B.KO Ω).FG) (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j)
    (v : Fin N → Ω) (hv : ∀ k, gF (X.inc wL (w k)) = v k) (k₀ : Fin N) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun k => v k / v k₀)) =
      WeightFamilies.dimY D j) :
    FiniteDimensional (Kp X la N) (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) ∧
      IsReduced (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) := by
  let iK : Algebra B.KO (Kp X la N) :=
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la N) := IsScalarTower.of_algebraMap_eq' rfl
  rw [map_Jid_eq]
  exact finite_reduced_of_eq hfg htr v k₀ hv₀ hbig _ (tv_indep X la N)
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i)) (fun i => by rw [rzMap_sec_eq]; simp only [hv])

end Rec

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 1000000 in

theorem finite_reduced_section (hfg : FnFG (T.Q.Xo j) T.Q.c) (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨-, ⟨-, hB2⟩, -, -⟩ := hH
  obtain ⟨k₀, hk₀, htrZ⟩ := hB2 Z
  exact finite_reduced_record (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w (hfg Z) (htr Z)
    (fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun k => formsEvR_single j hG hT Z _ _) k₀ hk₀ htrZ

end GlobalTheory.CurveRecord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SubalgebraEqIntegralClosureOfValuesResidues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.LocStructNak

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]

theorem dvd_of_vL_le [∀ ζ : Pts O A, IsDVRAt ζ] (c b : ↥(As O A))
    (h : ∀ ζ : Pts O A, vL ζ c ≤ vL ζ b) : c ∣ b := by
  have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) b ∈
      Ideal.map (algebraMap ↥(As O A) (Loc ζ)) (Ideal.span {c}) := by
    intro ζ
    have h1 := h ζ
    rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact h1
  exact Ideal.mem_span_singleton.1 (Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩))

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem exists_residue (C : Subalgebra O ↥(As O A)) (ζ : Pts O A) (b c d : ↥(As O A))
    (hc : c ∈ C) (hd : d ∈ C) (hd0 : d ∉ ζ.asIdeal) (h : d * b - c ∈ ζ.asIdeal) :
    ∃ c' ∈ C, b - c' ∈ ζ.asIdeal := by
  haveI : Algebra.IsIntegral ↥C ↥(As O A) := Algebra.IsIntegral.tower_top O
  haveI := ζ.isMaximal
  have hmax : (ζ.asIdeal.comap (algebraMap ↥C ↥(As O A))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal
  obtain ⟨y, z, hz, hyz⟩ := hmax.exists_inv (x := ⟨d, hd⟩) (by simpa [Ideal.mem_comap] using hd0)
  have hz' : (z : ↥(As O A)) ∈ ζ.asIdeal := hz
  have hyz' : (y : ↥(As O A)) * d + z = 1 := congrArg Subtype.val hyz
  refine ⟨y * c, C.mul_mem y.2 hc, ?_⟩
  have e : b - y * c = y * (d * b - c) + b * z := by
    linear_combination (-b) * hyz'
  rw [e]
  exact ζ.asIdeal.add_mem (ζ.asIdeal.mul_mem_left _ h) (ζ.asIdeal.mul_mem_left _ hz')

theorem exists_approx [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)] (C : Subalgebra O ↥(As O A))
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, vL ζ c = (n ζ : ℕ∞))
    (hres : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C, b - c ∈ ζ.asIdeal)
    (n : Pts O A → ℕ) (b : ↥(As O A)) : ∃ c ∈ C, ∀ ζ, (n ζ : ℕ∞) ≤ vL ζ (b - c) := by
  classical
  letI := Fintype.ofFinite (Pts O A)
  obtain ⟨N, hN⟩ : ∃ N, ∑ ζ, n ζ = N := ⟨_, rfl⟩
  induction N generalizing n with
  | zero =>
    refine ⟨0, C.zero_mem, fun ζ => ?_⟩
    rw [(Finset.sum_eq_zero_iff.1 hN) ζ (Finset.mem_univ _)]
    simp
  | succ N ih =>
    obtain ⟨ζ₀, -, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := n)
      (by rw [hN]; omega)
    have hsum : ∑ ζ, Function.update n ζ₀ (n ζ₀ - 1) ζ = N := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ζ₀), ← Finset.sdiff_singleton_eq_erase] at hN
      omega
    obtain ⟨c₁, hc₁, h₁⟩ := ih _ hsum
    obtain ⟨c, hc, hv⟩ := hval (Function.update n ζ₀ (n ζ₀ - 1))
    obtain ⟨b', hb'⟩ := dvd_of_vL_le c (b - c₁) (fun ζ => by rw [hv]; exact h₁ ζ)
    obtain ⟨c', hc', hm⟩ := hres ζ₀ b'
    refine ⟨c₁ + c * c', C.add_mem hc₁ (C.mul_mem hc hc'), fun ζ => ?_⟩
    have e : b - (c₁ + c * c') = c * (b' - c') := by linear_combination hb'
    rw [e, vL_mul, hv]
    by_cases hζ : ζ = ζ₀
    · subst hζ
      have h1 : 1 ≤ vL ζ (b' - c') := by
        rw [Order.one_le_iff_ne_zero, Ne, vL_eq_zero_iff]
        exact not_not.2 hm
      rw [Function.update_self]
      calc (n ζ : ℕ∞) = ((n ζ - 1 : ℕ) : ℕ∞) + 1 := by
            have : n ζ = (n ζ - 1) + 1 := by omega
            conv_lhs => rw [this]
            push_cast
            rfl
        _ ≤ _ := add_le_add le_rfl h1
    · rw [Function.update_of_ne hζ]
      exact le_self_add

theorem as_le_of_val_of_residue (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [Algebra O A] (ϖ : O) (hU : IsUnif A ϖ) [∀ ζ : Pts O A, IsDVRAt ζ] [Finite (Pts O A)]
    [Module.Finite O ↥(As O A)] (C : Subalgebra O A) (hC : C ≤ As O A)
    (hval : ∀ n : Pts O A → ℕ, ∃ c ∈ C, ∀ ζ, ord ϖ ζ c = (((n ζ : ℕ) : ℤ) : WithTop ℤ))
    (hres : ∀ (ζ : Pts O A), ∀ b ∈ As O A, ∃ c ∈ C, ∃ d ∈ C,
      ord ϖ ζ d = 0 ∧ 0 < ord ϖ ζ (d * b - c)) : As O A ≤ C := by
  set C' : Subalgebra O ↥(As O A) := C.comap (As O A).val with hC'
  have hinj : Function.Injective (ENat.map (Nat.cast : ℕ → ℤ)) :=
    (ENat.strictMono_map_iff.2 Nat.strictMono_cast).injective
  have hzero : ∀ (ζ : Pts O A) (a : ↥(As O A)), ord ϖ ζ (a : A) = 0 ↔ a ∉ ζ.asIdeal := by
    intro ζ a
    rw [ord_of_mem ζ hU a.2, ← vL_eq_zero_iff]
    constructor
    · intro h
      exact hinj h
    · intro h
      change (vL ζ a).map (Nat.cast : ℕ → ℤ) = 0
      rw [h]
      rfl
  have hval' : ∀ n : Pts O A → ℕ, ∃ c ∈ C', ∀ ζ, vL ζ c = (n ζ : ℕ∞) := by
    intro n
    obtain ⟨c, hc, h⟩ := hval n
    refine ⟨⟨c, hC hc⟩, hc, fun ζ => hinj ?_⟩
    rw [← ord_of_mem ζ hU (hC hc), h ζ, ENat.map_natCast]
  have hres' : ∀ (ζ : Pts O A) (b : ↥(As O A)), ∃ c ∈ C', b - c ∈ ζ.asIdeal := by
    intro ζ b
    obtain ⟨c, hc, d, hd, hd0, h⟩ := hres ζ b b.2
    refine exists_residue C' ζ b ⟨c, hC hc⟩ ⟨d, hC hd⟩ hc hd ((hzero ζ ⟨d, hC hd⟩).1 hd0) ?_
    by_contra hn
    exact h.ne' ((hzero ζ _).2 hn)
  have key : (⊤ : Submodule O ↥(As O A)) ≤ Subalgebra.toSubmodule C' := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro b _
    obtain ⟨c, hc, h⟩ := exists_approx C' hval' hres' (ep ϖ) b
    obtain ⟨b', hb'⟩ := dvd_of_vL_le (algebraMap O ↥(As O A) ϖ) (b - c)
      (fun ζ => by rw [← coe_ep ζ hU]; exact h ζ)
    have e : b = c + ϖ • b' := by rw [Algebra.smul_def, ← hb']; ring
    rw [e]
    exact Submodule.add_mem_sup hc (Submodule.smul_mem_smul
      ((IsLocalRing.mem_maximalIdeal ϖ).2 hU.irreducible.not_isUnit) Submodule.mem_top)
  intro x hx
  exact key (Submodule.mem_top (x := (⟨x, hx⟩ : ↥(As O A))))

end GlobalTheory.LocStructNak
end

