import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0071
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0069
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0072
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0077
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0091
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0089
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0046
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0049
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRunDataGeneratingScaledThetaLatticeWeight
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem exists_tiedW_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ThInt (recPJ h j hj) hinj EX wL → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → ∃ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw := by
  intro hC D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hP hR hI hG4 hPrw
  obtain ⟨hL, hf, hr, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR
  obtain ⟨hDF, hn, hrn, hLP⟩ :=
    (GlobalTheory.RunWeights.weights_below D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj.1 hP).1 wL (by simp)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hRL := GlobalTheory.pageRows_of_le D large₂ j ka wL hL0 hDF hn hR
  have hn0 : 0 < wL.n := by omega
  have hO : OPO large₂ (recB h.toLawsCore) := by
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -⟩, -⟩ := hP
    exact hO
  obtain ⟨N, w0, hspan, hN, hsup⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hC D T h hG large₂ j hj wL hRL hL hrn hLP
  have hcount := log_count_le_mul_size D _ large₂ j wL N Prw hL hn0 hRL hO hPrw hN
  have hs : (0 : ℝ) ≤ wL.size := by
    have h1 := frn_le_size_sub_one wL
    have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * wL.n := by positivity
    push_cast at h1
    linarith
  have hp : 0 ≤ Real.log (D.host.pde : ℝ) := Real.log_natCast_nonneg _
  have hZ : 0 ≤ Zb D large₂ := by unfold Zb; positivity
  have hnum := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j wL D.host.pde hL hn0).2.2
  have hGc := mul_le_mul_of_nonneg_right (hG4 D.host.pde (by simp)) hs
  have hd : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
    rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  have hK : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
  refine (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) N w0
    ((lamStar D + 2 * Real.log D.host.pde) * wL.size) _ Gc Prw (by positivity) (by positivity) (fun σ => ?_)
    hspan hsup (hnum.trans hGc)).2 hI hcount
  rw [sW_eq_sOf]
  refine ((GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D _ hinj EX j wL).2 σ).2.2.2.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hs

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortThetaFamilyWithBlockPolynomialRules
section
noncomputable section

namespace GlobalTheory.BlockTh

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem span_sum_elim {R M ι κ : Type} [CommRing R] [AddCommGroup M] [Module R M] (S : Submodule R M) (u : ι → M)
    (v : κ → M) (hu : Submodule.span R (Set.range u) = S) (hv : ∀ k, v k ∈ S) :
    Submodule.span R (Set.range (Sum.elim u v)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | k, rfl⟩
    · rw [← hu]
      exact Submodule.subset_span ⟨i, rfl⟩
    · exact hv k
  · rw [← hu]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩

private theorem span_range_sum_elim_eq_thAll {D : D7} {Pr : ModuliIntegralCharts.Prov D} {j : ℕ} (B : WeightFamilies.Prov D) (X : PJ D B Pr j)
    (w : WeightFamilies.Wt D j) {N M' : ℕ} {ι : Type} (w0 : Fin N → B.Cusp j w) (v : ι → B.Cusp j w) (e : Fin M' ≃ Fin N ⊕ ι)
    (h0 : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll w) (hv : ∀ q, v q ∈ X.thAll w) :
    Submodule.span (𝓞 B.KO) (Set.range (fun k => Sum.elim w0 v (e k))) = X.thAll w := by
  rw [show Set.range (fun k => Sum.elim w0 v (e k)) = Set.range (Sum.elim w0 v) from
    EquivLike.range_comp (Sum.elim w0 v) e]
  exact span_sum_elim _ w0 v h0 hv

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem theta_family_block : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * w.n → ∃ (N : ℕ) (w0 : Fin N → (recB h.toLawsCore).Cusp j w) (P₁ : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA w) w.n ∧ IsBlockProd P₁ ∧ ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) 1 P₁ (fun k => ((w0 k).1 : T.R j)) ∧ (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) (w1 : Fin N → B.Cusp j w) => Submodule.span (𝓞 B.KO) (Set.range w1) = X.thAll w) (recB h.toLawsCore) (recPJ h j hj) w0 ∧ N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ (recB h.toLawsCore).KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) ∧ ∀ k σ, Real.log ((recB h.toLawsCore).supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) + Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
  intro hC D T h hG large₂ j hj w hP hL hr hlast hn
  obtain ⟨N0, w0, hspan, hN0, hsup0⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hC D T h hG large₂ j hj w hP hL hr hlast
  obtain ⟨-, ⟨hM, -⟩, -, hdat⟩ := h.toLawsCore.pins
  obtain ⟨hp, hq, -⟩ := hdat j hj
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    exact Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  have hfE : I2.PT.f D.host.E = D.R.f := by
    dsimp only [I2.PT.f]
    rw [Formalism.MainNotions.StandardLattice.finrank_host D]
    omega
  have he : ∀ {m : ℕ} (g : Fin m → ℕ), Antitone g → ∀ i k : ℕ, i ≤ k → ext0 g k ≤ ext0 g i := by
    intro m g hg i k hik
    dsimp only [ext0]
    by_cases h1 : k < m <;> by_cases h2 : i < m
    · rw [dif_pos h1, dif_pos h2]
      exact hg (Fin.mk_le_mk.2 hik)
    · exact absurd (lt_of_le_of_lt hik h1) h2
    · rw [dif_neg h1]
      exact Nat.zero_le _
    · rw [dif_neg h1, dif_neg h2]
  have hanti : ∀ τ i k, i ≤ k → wtA w (τ, k) ≤ wtA w (τ, i) := by
    intro τ i k hik
    dsimp only [wtA]
    apply Finset.sum_le_sum
    intro t _
    apply add_le_add
    · split_ifs
      · exact he _ (w.aPlus_antitone t) i k hik
      · exact le_rfl
    · split_ifs
      · exact he _ (w.aM_anti t) i k hik
      · exact le_rfl
  obtain ⟨P, hPh, hPb, hPdeg, hPl1⟩ := GlobalTheory.T.exists_blockProduct_mem_integralHarmonic D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c (wtA w) w.n hanti
    (by rw [hfE, hpq]; exact hn)
  have hdom : Dom (wtA w) w.n := dom_wtA w
  have hlp : LastPos (T.Q.Dw j) (wtA w) := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlast
  obtain ⟨_, hnab⟩ := h.nabPin j hj
  have hex : ∀ q : Fin w.n → LevQ (T.Q.Dw j) T.Q.l, ∃ f : T.R j,
      IsThRule (T.Q.Xo j) T.Q.c (T.nab j) (fun b => levRep (q b)) P f :=
    fun q => by
      obtain ⟨⟨f, hf, -⟩, -⟩ := GlobalTheory.thetaRule_exists_and_eval hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
        (T.nab j) hnab (wtA w) w.n (fun b => levRep (q b)) P hPh
      exact ⟨f, hf⟩
  choose f hf using hex
  have hfC : ∀ q, f q ∈ cutR T.C j w := by
    intro q
    have h1 : f q ∈ T.C j w := h.thCusp j hj (wtA w) w.n hdom hlp (f q) ⟨fun b => levRep (q b), P, hPh, hf q⟩
    dsimp only [cutR]
    exact Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun hn' => absurd hj hn'⟩
  let v : (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) → (recB h.toLawsCore).Cusp j w := fun q =>
    (⟨f q, hfC q⟩ : cutR T.C j w)
  have hv1 : ∀ q, ((v q : cutR T.C j w) : T.R j) = f q := fun q => rfl
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.card_lattice_quotient_half_level D.host.E T.Q.H (T.Q.Dw j) T.Q.l
  let _ : Fintype (LevQ (T.Q.Dw j) T.Q.l) := Fintype.ofFinite _
  let e : Fin (N0 + Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l)) ≃ Fin N0 ⊕ (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _).symm)
  let W : Fin (N0 + Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l)) → (recB h.toLawsCore).Cusp j w :=
    fun k => Sum.elim w0 v (e k)
  have hWq : ∀ q, W (e.symm (Sum.inr q)) = v q := by
    intro q
    simp only [W, Equiv.apply_symm_apply, Sum.elim_inr]
  refine ⟨_, W, P, hPh, hPb, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun q => e.symm (Sum.inr q), fun a b hab => Sum.inr_injective (e.symm.injective hab), fun q => ⟨f q, hf q, fun p y => ?_⟩⟩
    show (W (e.symm (Sum.inr q))).1 p y = _
    rw [hWq q, map_one, one_mul]
  · refine span_range_sum_elim_eq_thAll (recB h.toLawsCore) (recPJ h j hj) w w0 v e hspan fun q => ?_
    dsimp only [recPJ, mkX, spanIn]
    simp only [Submodule.mem_comap]
    exact Submodule.subset_span (show f q ∈ T.th j w from ⟨fun b => levRep (q b), P, hPh, hf q⟩)
  · have hfd : FD.fdeg D.host.E = D.R.f := by
      dsimp only [FD.fdeg]
      rw [Formalism.MainNotions.StandardLattice.finrank_host D]
      omega
    have hc : Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) =
        (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) := by
      rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard, hM, hpq, hfd, ← pow_mul]
    have hB1 : 0 < Module.finrank ℚ (recB h.toLawsCore).KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n) :=
      Nat.mul_pos Module.finrank_pos (pow_pos (by omega) _)
    have hGX := Nat.le_mul_of_pos_right ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n)) hB1
    rw [hc]
    linarith
  · intro k σ
    obtain ⟨x, rfl⟩ : ∃ x, e.symm x = k := ⟨e k, e.symm_apply_apply k⟩
    rcases x with i | q
    · have h0 : W (e.symm (Sum.inl i)) = w0 i := by
        simp only [W, Equiv.apply_symm_apply, Sum.elim_inl]
      rw [h0]
      exact hsup0 i σ
    · rw [hWq q]
      have hs : (recB h.toLawsCore).supN j w σ (v q) = T.Ns j w σ (f q) := by
        change cutN T.C T.Ns j w σ (v q) = _
        dsimp only [cutN]
        rw [if_pos hj]
      rw [hs]
      have h2 : ((Formalism.MainNotions.WeightAlgebra.DF w : ℕ) : ℝ) = Formalism.MainNotions.WeightAlgebra.absA w := by
        dsimp only [Formalism.MainNotions.WeightAlgebra.DF, Formalism.MainNotions.WeightAlgebra.degP, Formalism.MainNotions.WeightAlgebra.absA]
        push_cast
        rfl
      have hDF : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ Formalism.MainNotions.WeightAlgebra.absA w := by
        rw [← h2]
        exact_mod_cast ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
      have hA0 : 0 ≤ Formalism.MainNotions.WeightAlgebra.absA w := by
        rw [← h2]
        positivity
      rw [hpq] at hPl1
      have hℓ0 : 0 ≤ Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))) :=
        Real.log_nonneg (le_max_left _ _)
      have hℓexp : l1At σ P ≤ Real.exp (Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)))) := by
        rw [Real.exp_log (lt_of_lt_of_le one_pos (le_max_left _ _))]
        dsimp only [l1At]
        exact le_trans (hPl1 σ) (le_max_right _ _)
      have hℓle : Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))) ≤
          (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r := by
        rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
        · rw [h0, Nat.cast_zero, mul_zero, max_eq_left (pow_le_one₀ le_rfl zero_le_one), Real.log_one]
        · have h1 : (1 : ℝ) ≤ (D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) := one_le_pow₀ (by exact_mod_cast h0)
          rw [max_eq_right h1, Real.log_pow]
          exact mul_le_mul_of_nonneg_left (Real.log_le_self (by positivity)) (by positivity)
      have hNs := GlobalTheory.T.log_supNorm_thetaGenerator_le hC D T h hG large₂ j hj w hP hL hr hlp (fun b => levRep (q b)) P hPh (f q) (hf q) σ _ hℓ0 hℓexp
      have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
      have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
      have t1 : 0 ≤ 3 * (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L := mul_nonneg (by positivity) hL0
      have t2 : 0 ≤ 5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) :=
        mul_nonneg (by norm_num) (Real.log_nonneg (Nat.one_le_cast.2 Module.finrank_pos))
      have t3 : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| /
          (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := by
        apply div_nonneg _ (Nat.cast_nonneg _)
        apply Real.log_nonneg
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero _)
      rcases Nat.eq_zero_or_pos w.n with hn0 | hwn
      · have hr0' : D.R.r = 0 := by omega
        have hs1 : (D.R.sigW j).1 = 0 := by omega
        have hs2 : (D.R.sigW j).2 = 0 := by omega
        have hA : Formalism.MainNotions.WeightAlgebra.absA w = 0 := by
          have : IsEmpty (Fin (D.R.sigW j).1) := by rw [hs1]; infer_instance
          have : IsEmpty (Fin (D.R.sigW j).2) := by rw [hs2]; infer_instance
          simp [Formalism.MainNotions.WeightAlgebra.absA]
        have hZ0 : Zb D large₂ = 0 := by simp [Zb, hr0']
        have hrc : (D.R.r : ℝ) = 0 := by exact_mod_cast hr0'
        rw [hA, hrc] at hNs
        rw [hrc] at hℓle
        rw [hZ0]
        nlinarith
      · have h9430 := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w 0 hL hwn).1
        have hk1 : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r ≤ 140 * D.R.r * large₂.sc.L * Formalism.MainNotions.WeightAlgebra.absA w := by
          have : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r ≤ Formalism.MainNotions.WeightAlgebra.absA w * D.R.r :=
            mul_le_mul_of_nonneg_right hDF hr0
          nlinarith [mul_nonneg hA0 hr0]
        linarith

end GlobalTheory.BlockTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRules
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegreeInterpolationBounds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem totalDegree_eq_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = Formalism.L2.Pj.DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = Formalism.L2.Pj.DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Formalism.L2.Pj.DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  apply le_antisymm
  · exact Finset.sup_le fun m' hm' => (key m' hm').le
  · exact (key m hm) ▸ MvPolynomial.le_totalDegree hm

theorem pow_le_sq_of_log {M x : ℝ} {d : ℕ} (hM : 1 < M) (hd : 1 ≤ d) (hx : 0 ≤ x)
    (h : (d : ℝ) / 2 * Real.log M ≤ Real.log x) : M ^ d ≤ x ^ 2 := by
  have hl : 0 < Real.log M := Real.log_pos hM
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero] at h
      nlinarith
    · exact h0
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  linarith

theorem i2iAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  intro hCI D T h EX j hj K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hTie hPage hSupp P₁ hP hB N w hC
    tableLineDegreeFive hP14
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  obtain ⟨α, hα1, hα2⟩ := GlobalTheory.RunIn.half_level_generator_norm D T h EX
  obtain ⟨hrun, hcc, -, -⟩ := GlobalTheory.T.thetaRunParameters_at_typePrimes_product D _ _ j (recPJ h j hj) K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hHP hTie hPage hSupp
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hP0 : P₁ ≠ 0 := fun e => GlobalTheory.BlockThInhab.not_isBlockProd_zero (T.Q.Dw j) wL.n T.Q.c.F (e ▸ hB)
  have hdeg : P₁.totalDegree = WeightAlgebra.DF wL :=
    (totalDegree_eq_DF T.Q.c hP hP0).trans (GlobalTheory.WeightExponents.weight_exponents D T.Q h.pins j hj wL).1
  have hq : (T.Q.Dw j).q ≤ D.R.m := by
    rw [(h.pins.2.2.2 j hj).2.1]
    exact Nat.sub_le _ _
  have hs : ∀ σ : T.Q.c.F →+* ℂ,
      (T.Q.l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F)‖ ^ 2 := by
    intro σ
    have h3 : (3 : ℝ) ≤ T.Q.l.M := by exact_mod_cast T.Q.l.three_le
    refine pow_le_sq_of_log (by linarith) (by rw [hdeg]; have := hSupp.2.2.2.2; omega) (norm_nonneg _) ?_
    rw [hdeg, hM, Nat.cast_mul]
    exact hSupp.2.1 σ
  have key := GlobalTheory.T.integralityBound_of_family_containing_scaled_thetaRules hCI D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D) (T.nab j) hnab
    (fun σ hσ => ⟨h.unf j hj σ hσ, h.unTest j hj σ hσ, h.xiAbs j hj σ hσ⟩) α hα1 hα2 (wtA wL) wL.n P₁ (dom_wtA wL) hP hB
    _ hs N (fun k => ((w k).1 : T.R j)) (fun k => cusp_le_sec _ _ _ _ _ (cutR_le T.C j wL (w k).2)) hC
    (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m (by rw [hdeg, hM]; exact hrun) (Or.inr hq) tableLineDegreeFive
    (cc D large₂ C2 A2 CR wL) hP14 (by rw [hM]; exact hcc)
  rw [hdeg, hM] at key
  exact key

end GlobalTheory.DegreeInterpolationBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoBaseComponentShortPolynomialGeneratorStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_base_component_short_polynomial_generator : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ReciprocityTheory.ChartRestriction.G.PullbackSections.NoBaseSt := by
  first | exact @GlobalTheory.NoBase.noBase | exact GlobalTheory.NoBase.noBase | (intros; apply GlobalTheory.NoBase.noBase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorMemSpanSmallSupNormShortGeneratorsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGenerator_mem_span_small_supNorm_shortGenerators : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  first | exact @GlobalTheory.RunIn.sh_mem_span_small | exact GlobalTheory.RunIn.sh_mem_span_small | (intros; apply GlobalTheory.RunIn.sh_mem_span_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNet_dimension_and_pointCount_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ (Nt : NetNorms.NetData (recB h.toLawsCore) j ka) (σ₀ : (recB h.toLawsCore).KO →+* ℂ), NetNorms.NetMax Nt ∧ NetNorms.NetLeSup Nt ∧ NetNorms.NetPageG Nt large₂ 1041 3 ∧ NetNorms.NetInj Nt σ₀ ∧ Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ pdR large₂ ka ∧ DeepSubMul (recPJ h j hj) ∧ Real.log (Module.finrank (recB h.toLawsCore).KO ((recB h.toLawsCore).Cusp j ka) : ℝ) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ del : ℕ, LatAt (recB h.toLawsCore) j ka → ShareRd (D := D) (j := j) Tn del ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka)) → Real.log del ≤ 1041 * Zb D large₂ ^ 3 := by
  first | exact @GlobalTheory.RunJoin.net_at_run | exact GlobalTheory.RunJoin.net_at_run | (intros; apply GlobalTheory.RunJoin.net_at_run <;> assumption)
end

