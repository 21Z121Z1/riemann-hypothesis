import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FamilyUnifIndexEqOfMarkedLatticeIsometry
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnifMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

lemma isPeriod_comp_symm {D' D'' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (gam : D'.La ≃ₗ[𝓞 E] D''.La) (hg : ∀ a b, D''.EF (gam a) (gam b) = D'.EF a b)
    {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P) :
    IsPeriod D'' ty (P.comp gam.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hE⟩ := hP
  have hP' : ∀ x, (P.comp gam.symm.toLinearMap.toAddMonoidHom) x = P (gam.symm x) := fun _ => rfl
  have hr : (P.comp gam.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨gam.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨gam x, by rw [hP', LinearEquiv.symm_apply_apply]⟩
  refine ⟨?_, ?_, ?_, ?_, Hm, hH, hpos, ?_⟩
  · intro a x k
    rw [hP', hP', map_smul, h1]
  · intro x y hxy
    exact gam.symm.injective (h2 hxy)
  · rw [hr]; exact h3
  · have : Set.range (P.comp gam.symm.toLinearMap.toAddMonoidHom) = Set.range P := by
      have := congrArg (fun s : AddSubgroup (Fin g → ℂ) => (s : Set (Fin g → ℂ))) hr
      simpa only [AddMonoidHom.coe_range] using this
    rw [this, h4]
  · intro x y
    rw [hP', hP', hE, ← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

lemma isHolTo_ex {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) {P : (U.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (U.Di i) ty P) : IsHolTo Set.univ (fun z => (U.ex i P z).left) := by
  have h := (U.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  intro V f
  obtain ⟨ho, hd⟩ := h V f
  have hc : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · have h3 := ho.preimage hc.continuous
    have h4 : {b ∈ Set.univ | ⊤ ≤ (U.ex i P b).left ⁻¹ᵁ V} =
        (fun z : Fin g → ℂ => ((0, z) : (Fin 0 → ℂ) × (Fin g → ℂ))) ⁻¹'
          {b ∈ Set.univ ×ˢ Set.univ | ⊤ ≤ (U.ex i P b.2).left ⁻¹ᵁ V} := by
      ext z
      exact ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩
    exact h4 ▸ h3
  · refine hd.comp (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) hc.differentiableOn ?_
    intro z hz
    exact ⟨⟨trivial, trivial⟩, hz.2⟩

theorem index_eq_of_isometry : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (i j : Fin U.n) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ a b, (U.Di j).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a, ∃ e, gam (U.t i a) = U.t j a + l.M' • e) → i = j := by
  intro hT hL E _ _ _ H D l Xo σ g ty hr hσ hty U i j gam hg ht
  obtain ⟨-, P, hP⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (U.Di i) g ty
    (by rw [(U.sig i).1, (U.sig i).2]; exact hty)
  have hP' := isPeriod_comp_symm gam hg hP
  refine U.disj i j P _ hP hP' ?_
  refine (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hT hL E H D l Xo σ g ty hr hσ hty (U.Di i) (U.Di j)
    (U.t i) (U.t j) P _ _ _ (U.ex i P) (U.ex j _)
    ⟨U.over_σ i P hP, hP, ⟨U.ex_add i P hP, U.ex_onto i P hP, isHolTo_ex U i hP, U.ex_diff i P hP⟩,
      U.ex_ker i P hP, U.ex_lin i P hP, U.ex_weil i P hP, U.ex_eta i P hP, U.ex_etaA i P hP⟩
    ⟨U.over_σ j _ hP', hP', ⟨U.ex_add j _ hP', U.ex_onto j _ hP', isHolTo_ex U j hP', U.ex_diff j _ hP'⟩,
      U.ex_ker j _ hP', U.ex_lin j _ hP', U.ex_weil j _ hP', U.ex_eta j _ hP', U.ex_etaA j _ hP'⟩).2
    ⟨gam, LinearEquiv.refl ℂ _, hg, fun a _ => ?_, fun a => ?_, fun a => ?_⟩
  · obtain ⟨e, he⟩ := ht a
    obtain ⟨c, hc⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    exact ⟨c • e, by rw [he, hc, mul_smul]⟩
  · obtain ⟨e, he⟩ := ht a
    obtain ⟨c, hc⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
    exact ⟨c • e, by rw [he, hc, mul_smul]⟩
  · change P (gam.symm (gam a)) = P a
    rw [LinearEquiv.symm_apply_apply]

end GlobalTheory.UnifMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.ExtraWeight

theorem finrank_host (D : D7) : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  push_cast
  ring

theorem discr_rpow (D : D7) :
    |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f) = D.host.rdE ^ 2 := by
  have hf : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  unfold Host.rdE
  rw [finrank_host, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  push_cast
  field_simp

theorem two_le_dimY (D : D7) {j : ℕ} (hj : j < D.R.m) (h1 : 1 ≤ j) : 2 ≤ WeightFamilies.dimY D j := by
  have hf : 8 ≤ D.R.f := D.eight_le_f
  have hk := D.R.m_add_three_le_k
  have hp : 1 ≤ (D.R.sigW j).1 := by unfold Ranks.sigW; simp only; omega
  have hq : 1 ≤ (D.R.sigW j).2 := by unfold Ranks.sigW; simp only; omega
  have hpq : 1 ≤ (D.R.sigW j).1 * (D.R.sigW j).2 := Nat.mul_pos hp hq
  unfold WeightFamilies.dimY
  calc 2 ≤ 8 * 1 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hf (by omega)

theorem core (r f m ρ rd PP c T g DF q : ℝ) (hg : g = 1250 * r) (hr : 0 ≤ r) (hrT : r ≤ T) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ m) (hrd : 2 * f * m ≤ rd) (hPP : 0 < PP) (hq : 0 < q)
    (hc : c = rd ^ 7 * PP * DF ^ 2 / q) (hql : (rd ^ 7) ^ 4 * PP ^ 3 * DF ^ 2 ≤ q) (hgP : g * f * m ^ 3 ≤ PP ^ 2) :
    r * (1 + rd ^ 7 * T * c * (2 * f * ρ) ^ 2 * ρ / 2 / (1 / (2 * 5 ^ 4 * rd ^ 2))) ≤ 2 * T := by
  have h2f : 2 * f ≤ rd := by nlinarith
  have hrd1 : 1 ≤ rd := by linarith
  have hT : 0 ≤ T := hr.trans hrT
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcP : c * (PP ^ 2 * rd ^ 21) ≤ 1 := by
    rw [hc, div_mul_eq_mul_div, div_le_one hq]
    calc _ = (rd ^ 7) ^ 4 * PP ^ 3 * DF ^ 2 := by ring
      _ ≤ q := hql
  have e : r * (1 + rd ^ 7 * T * c * (2 * f * ρ) ^ 2 * ρ / 2 / (1 / (2 * 5 ^ 4 * rd ^ 2))) =
      r + T * (c * ((g * f * ρ ^ 3) * (2 * f * rd ^ 9))) := by
    rw [hg]; field_simp; ring
  have a1 : g * f * ρ ^ 3 ≤ PP ^ 2 := by
    refine le_trans ?_ hgP
    have : 0 ≤ g * f := by rw [hg]; positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρ 3) this
  have a2 : 2 * f * rd ^ 9 ≤ rd ^ 21 := by
    calc 2 * f * rd ^ 9 ≤ rd * rd ^ 9 := mul_le_mul_of_nonneg_right h2f (by positivity)
      _ = rd ^ 10 := by ring
      _ ≤ rd ^ 21 := pow_le_pow_right₀ hrd1 (by norm_num)
  have a3 : (g * f * ρ ^ 3) * (2 * f * rd ^ 9) ≤ PP ^ 2 * rd ^ 21 :=
    mul_le_mul a1 a2 (by positivity) (by positivity)
  have a4 : c * ((g * f * ρ ^ 3) * (2 * f * rd ^ 9)) ≤ 1 := (mul_le_mul_of_nonneg_left a3 hc0).trans hcP
  rw [e]
  have := mul_le_mul_of_nonneg_left a4 hT
  linarith

theorem numbers : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → j < D.R.m → 1 ≤ j → 1 ≤ WeightAlgebra.DF wL → 0 < WeightAlgebra.cc D large₂ C2 A2 CR wL ∧ (Tn : ℝ) * WeightAlgebra.cc D large₂ C2 A2 CR wL * g0 D ≤ 1 ∧ 1 ≤ WeightFamilies.RRv D K.CRm ∧ (D.R.r : ℝ) * (1 + WeightFamilies.c1 D K.CRm Tn (WeightAlgebra.cc D large₂ C2 A2 CR wL) j / (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f)))) ≤ 2 * Tn ∧ addL wF wL Tn = ka ∧ 2 ≤ WeightFamilies.dimY D j ∧ 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn := by
  intro D B P j X K Ch Ah Cq Aq large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hH ht hPg hj h1 hDF
  obtain ⟨hA, hS, h3, -, -⟩ := hH
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hL, hF, -, -, -, -, hrT, -, -, h11, -, hd⟩ := hS
  have hgP := g0fm3_le_of_dom hPg ht hd
  obtain ⟨e1, e2, e3⟩ := tie_eqs ht
  have hCR : CR = 7 := ht.2.2.2.2.2.1
  have hK : K.CRm = 7 := ht.2.2.2.2.2.2.1
  have hrd16 := sixteen_le_rdE_of_parA hA
  have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
  have hRR : WeightFamilies.RRv D 7 = D.host.rdE ^ 7 := by
    unfold WeightFamilies.RRv; exact_mod_cast Real.rpow_natCast D.host.rdE 7
  have hC : 1000 ≤ C2 := ht.1 ▸ hd.1
  have hPP : 0 < WeightFamilies.PPv D large₂ C2 A2 := by
    unfold WeightFamilies.PPv
    have := WeightFamilies.one_le_zBase large₂
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨hql, -, -, hTc, -, -⟩ := h3
  rw [Real.rpow_zero, one_mul, hCR, hRR] at hql
  rw [e1, e2, e3] at hTc
  have hDF' : (1 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hDF
  have hrd0 : 0 < D.host.rdE := by linarith
  have hq : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by positivity) hql
  have hc : WeightAlgebra.cc D large₂ C2 A2 CR wL = D.host.rdE ^ 7 * WeightFamilies.PPv D large₂ C2 A2 * (WeightAlgebra.DF wL : ℝ) ^ 2 / (qq D : ℝ) := by
    unfold WeightAlgebra.cc; rw [hCR, hRR]
  refine ⟨by rw [hc]; positivity, hTc, ?_, ?_, ?_, two_le_dimY D hj h1, h11⟩
  · rw [hK, hRR]; exact one_le_pow₀ (by linarith)
  · rw [discr_rpow]
    unfold WeightFamilies.c1 WeightFamilies.dP
    rw [hK, hRR]
    push_cast
    have hf : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
    refine core _ _ (D.R.m : ℝ) _ _ _ _ _ (g0 D : ℝ) _ _ ?_ (Nat.cast_nonneg _) ?_ (by linarith) (by linarith)
      (Nat.cast_nonneg _) ?_ hrd hPP hq hc hql hgP
    · unfold g0; push_cast; norm_num
    · exact_mod_cast (by omega : D.R.r ≤ Tn)
    · have : WeightFamilies.rho D j ≤ D.R.m := by unfold WeightFamilies.rho Ranks.sigW; simp only; omega
      exact_mod_cast this
  · obtain ⟨f1, f2, f3⟩ := hF
    have l1 := hL.1
    obtain ⟨aP, aM, p1, p2, n, p3⟩ := ka
    unfold addL wadd wsmul
    simp only [WeightFamilies.Wt.mk.injEq]
    simp only at hn f2 f3
    refine ⟨?_, ?_, ?_⟩
    · funext τ i
      have := f2 τ i
      zify; linarith
    · funext τ i
      have := f3 τ i
      zify; linarith
    · rw [f1, l1, hn, hnV]

end GlobalTheory.ExtraWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares.PolyDict

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem ofWt_C {ι : Type} (u : WeightFamilies.Wt D j) (F : B.Cusp j u) :
    OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial ι X.Forms) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact LinearMap.mem_range.mpr ⟨F, rfl⟩
  · exact Submodule.zero_mem _

theorem ofWt_sum {ι κ : Type} (u : WeightFamilies.Wt D j) (s : Finset κ) (p : κ → MvPolynomial ι X.Forms)
    (h : ∀ k ∈ s, OfWt X u (p k)) : OfWt X u (∑ k ∈ s, p k) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact Submodule.sum_mem _ fun k hk => h k hk m

theorem ofWt_X_mul {ι : Type} (u : WeightFamilies.Wt D j) (i : ι) (p : MvPolynomial ι X.Forms) (h : OfWt X u p) :
    OfWt X u (MvPolynomial.X i * p) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X_mul']
  split_ifs
  · exact h _
  · exact Submodule.zero_mem _

theorem ofWt_mul {ι : Type} (u u' : WeightFamilies.Wt D j) (p q : MvPolynomial ι X.Forms) (hp : OfWt X u p)
    (hq : OfWt X u' q) : OfWt X (wadd u u') (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  refine Submodule.sum_mem _ fun x _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp x.1)
  obtain ⟨G, hG⟩ := LinearMap.mem_range.mp (hq x.2)
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  rw [← hF, ← hG, hH]
  exact LinearMap.mem_range_self _ _

theorem toRp_C (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (F : X.Forms) :
    toRp X la N (MvPolynomial.C F) = emb X la N F := MvPolynomial.eval₂Hom_C _ _ _

theorem toRp_X (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (p : Idx D j N) :
    toRp X la N (MvPolynomial.X p) = algebraMap (Op X la N) (Rp X la N) (Tv X la N p) := MvPolynomial.eval₂Hom_X' _ _ _

theorem toFn_C (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (F : X.Forms) :
    R.toFn t (MvPolynomial.C F) = R.ev F := MvPolynomial.eval₂Hom_C _ _ _

theorem toFn_X (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (p : Idx D j N) :
    R.toFn t (MvPolynomial.X p) = fun _ => t p := MvPolynomial.eval₂Hom_X' _ _ _

private lemma algebraMap_mul_mem_Vw (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (u : WeightFamilies.Wt D j)
    (x : Op X la N) {v : Rp X la N} (hv : v ∈ Vw X la N u) :
    algebraMap (Op X la N) (Rp X la N) x * v ∈ Vw X la N u := by
  rw [IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N), ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hv

theorem toRp_mem (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (u : WeightFamilies.Wt D j)
    (p : MvPolynomial (Idx D j N) X.Forms) (hp : OfWt X u p) : toRp X la N p ∈ Vw X la N u := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp m)
  have key : toRp X la N (MvPolynomial.monomial m (p.coeff m)) = emb X la N (p.coeff m) *
      m.prod fun n e => (algebraMap (Op X la N) (Rp X la N) (Tv X la N n)) ^ e := by
    rw [toRp, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [key, ← hF, mul_comm]
  have hbase : emb X la N (X.inc u F) ∈ Vw X la N u := Submodule.subset_span ⟨F, rfl⟩
  suffices H : ∀ v ∈ Vw X la N u,
      (m.prod fun n e => (algebraMap (Op X la N) (Rp X la N) (Tv X la N n)) ^ e) * v ∈ Vw X la N u from
    H _ hbase
  unfold Finsupp.prod
  refine Finset.prod_induction _ (fun x => ∀ v ∈ Vw X la N u, x * v ∈ Vw X la N u) ?_ ?_ ?_
  · intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  · intro v hv
    rwa [one_mul]
  · intro n _ v hv
    show algebraMap (Op X la N) (Rp X la N) (Tv X la N n) ^ (m n) * v ∈ _
    rw [← map_pow]
    exact algebraMap_mul_mem_Vw la N u _ hv

theorem toFn_mem (R : Rdg X) {N : ℕ} (t : Idx D j N → ℂ) (u : WeightFamilies.Wt D j)
    (p : MvPolynomial (Idx D j N) X.Forms) (hp : OfWt X u p) : R.toFn t p ∈ R.sp u Set.univ := by
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  obtain ⟨F, hF⟩ := LinearMap.mem_range.mp (hp m)
  have key : R.toFn t (MvPolynomial.monomial m (p.coeff m)) = R.ev (p.coeff m) *
      m.prod fun n e => (fun _ : R.Y => t n) ^ e := by
    rw [Rdg.toFn, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  rw [key, ← hF, mul_comm]
  have hbase : R.ev (X.inc u F) ∈ R.sp u Set.univ := Submodule.subset_span ⟨F, Set.mem_univ _, rfl⟩
  suffices H : ∀ v ∈ R.sp u Set.univ,
      (m.prod fun n e => (fun _ : R.Y => t n) ^ e) * v ∈ R.sp u Set.univ from H _ hbase
  unfold Finsupp.prod
  refine Finset.prod_induction _ (fun x => ∀ v ∈ R.sp u Set.univ, x * v ∈ R.sp u Set.univ) ?_ ?_ ?_
  · intro a b ha hb v hv
    rw [mul_assoc]
    exact ha _ (hb v hv)
  · intro v hv
    rwa [one_mul]
  · intro n _ v hv
    show (fun _ : R.Y => t n) ^ (m n) * v ∈ _
    have hc : (fun _ : R.Y => t n) ^ (m n) * v = (t n ^ m n) • v := by
      funext y
      simp [Pi.pow_apply, Pi.mul_apply, Pi.smul_apply]
    rw [hc]
    exact Submodule.smul_mem _ _ hv

theorem sp_mul (R : Rdg X) (u u' : WeightFamilies.Wt D j) (f : R.Y → ℂ) (hf : f ∈ R.sp u Set.univ) (g : R.Y → ℂ)
    (hg : g ∈ R.sp u' Set.univ) : f * g ∈ R.sp (wadd u u') Set.univ := by
  have hfg := Submodule.mul_mem_mul hf hg
  simp only [Rdg.sp, Submodule.span_mul_span] at hfg ⊢
  refine Submodule.span_le.mpr ?_ hfg
  rintro _ ⟨_, ⟨F, -, rfl⟩, _, ⟨G, -, rfl⟩, rfl⟩
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  show R.ev (X.inc u F) * R.ev (X.inc u' G) ∈ _
  rw [← map_mul R.ev, hH]
  exact Submodule.subset_span ⟨H, Set.mem_univ _, rfl⟩

theorem sp_span (R : Rdg X) (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) :
    R.sp u (Submodule.span B.KO s) = R.sp u s := by
  unfold Rdg.sp
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' : F ∈ Submodule.span B.KO s := hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      simp only [map_smul, R.ev_smul]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem sp_finrank (R : Rdg X) (u : WeightFamilies.Wt D j) (M : Submodule B.KO (B.Cusp j u)) :
    FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M := by
  let b := Module.finBasis B.KO M
  have hli : LinearIndependent B.KO (fun i => (b i : B.Cusp j u)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli' := R.indep u _ _ hli
  have hspan : Submodule.span B.KO (Set.range fun i => (b i : B.Cusp j u)) = M := by
    rw [show (Set.range fun i => (b i : B.Cusp j u)) = M.subtype '' Set.range b from Set.range_comp _ _,
      Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hs := sp_span R u (Set.range fun i => (b i : B.Cusp j u))
  rw [hspan] at hs
  have e : R.sp u (M : Set (B.Cusp j u)) =
      Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i : B.Cusp j u))) := by
    rw [hs]
    unfold Rdg.sp
    rw [← Set.range_comp]
    rfl
  rw [e]
  exact ⟨FiniteDimensional.span_of_finite ℂ (Set.finite_range _),
    (finrank_span_eq_card hli').trans (Fintype.card_fin _)⟩

end GlobalTheory.Shares.PolyDict

namespace GlobalTheory.Shares

open PolyDict in

theorem polyDictionary : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (R : Rdg X) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (wL : WeightFamilies.Wt D j) (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ), (∀ i, toRp X la N (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = sec X la w i ∧ R.toFn t (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k))) = R.s w t i ∧ OfWt X wL (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (X.inc wL (w k)) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ F, toRp X la N (MvPolynomial.C F) = emb X la N F ∧ R.toFn t (MvPolynomial.C F) = R.ev F) ∧ (∀ u (F : B.Cusp j u), OfWt X u (MvPolynomial.C (X.inc u F) : MvPolynomial (Idx D j N) X.Forms)) ∧ (∀ u u' (p q : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → OfWt X u' q → OfWt X (wadd u u') (p * q)) ∧ (∀ u (p : MvPolynomial (Idx D j N) X.Forms), OfWt X u p → toRp X la N p ∈ Vw X la N u ∧ R.toFn t p ∈ R.sp u Set.univ) ∧ (∀ u u', ∀ f ∈ R.sp u Set.univ, ∀ g ∈ R.sp u' Set.univ, f * g ∈ R.sp (wadd u u') Set.univ) ∧ (∀ u (s : Set (B.Cusp j u)), R.sp u (Submodule.span B.KO s) = R.sp u s) ∧ (∀ u (M : Submodule B.KO (B.Cusp j u)), FiniteDimensional ℂ (R.sp u M) ∧ Module.finrank ℂ (R.sp u M) = Module.finrank B.KO M) := by
  intro D B P j X R la N wL w t
  refine ⟨fun i => ⟨?_, ?_, ?_⟩, fun F => ⟨PolyDict.toRp_C la N F, PolyDict.toFn_C R t F⟩,
    fun u F => PolyDict.ofWt_C u F, fun u u' p q hp hq => PolyDict.ofWt_mul u u' p q hp hq,
    fun u p hp => ⟨PolyDict.toRp_mem la N u p hp, PolyDict.toFn_mem R t u p hp⟩,
    fun u u' f hf g hg => PolyDict.sp_mul R u u' f hf g hg,
    fun u s => PolyDict.sp_span R u s, fun u M => PolyDict.sp_finrank R u M⟩
  · rw [map_sum]
    unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, PolyDict.toRp_X, PolyDict.toRp_C, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]
  · rw [map_sum]
    unfold Rdg.s
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, PolyDict.toFn_X, PolyDict.toFn_C]
    funext y
    simp [Pi.mul_apply, Pi.smul_apply]
  · exact PolyDict.ofWt_sum wL _ _ fun k _ => PolyDict.ofWt_X_mul wL _ _ (PolyDict.ofWt_C wL (w k))

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfLevelGeneratorNorm
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem half_level_generator_norm :
    ∀ (D : D7) (T : Top D) (_h : LawsP T) (_EX : ErrX D), ∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α} := by
  intro D T h _EX
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM

  have hbb : ∀ x : 𝓞 D.host.E, T.Q.H.bar (T.Q.H.bar x) = x := by
    intro x
    rw [bar_core T.toCore, bar_core T.toCore, barE_barE]

  have hn : ∀ i, piOf T.toCore _EX i * T.Q.H.bar (piOf T.toCore _EX i) = (D.host.g i : 𝓞 D.host.E) := by
    intro i
    rw [bar_core T.toCore]
    exact piOf_mul_barE T.toCore _EX i
  set π₀ := piOf T.toCore _EX 0
  set π₁ := piOf T.toCore _EX 1
  refine ⟨T.Q.H.bar (π₀ * π₁), ?_, ?_⟩
  · rw [hbb, map_mul, level_M T.toCore hM]
    have h0 := hn 0
    have h1 := hn 1
    push_cast
    rw [← h0, ← h1]
    ring
  · rw [hbb, Mb_eq T.toCore hM, ← span_piOf T.toCore hM _EX 0, ← span_piOf T.toCore hM _EX 1,
      Ideal.span_singleton_mul_span_singleton]

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRowsOfLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem pageRows_of_le : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka w : WeightFamilies.Wt D j), 0 ≤ large₂.sc.L → WeightAlgebra.DF w ≤ WeightAlgebra.DF ka → w.n ≤ ka.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w := by
  intro D large₂ j ka w hL hd hn h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · refine le_trans (Real.log_le_log (by positivity) ?_) h8
    have : ((WeightAlgebra.DF w : ℕ) : ℝ) ≤ ((WeightAlgebra.DF ka : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  · rcases Nat.eq_zero_or_pos w.n with h0 | h0
    · rw [h0]; simpa using hL
    · exact le_trans (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)) h9

end GlobalTheory
end

