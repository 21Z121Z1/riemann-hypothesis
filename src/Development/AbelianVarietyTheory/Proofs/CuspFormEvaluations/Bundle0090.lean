import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0082
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0089
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0051
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0055
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortFiniteGeneratorsThetaLattice
section
noncomputable section

namespace GlobalTheory.ThetaFamily

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem span_eq_spanIn {D : D7} {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]
    (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j)) (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) {ι : Type}
    (g : ι → cutR C j w) (hg : ∀ i, (g i : R j) ∈ s)
    (hs : ∀ f ∈ s, f ∈ AddSubgroup.closure (Set.range fun i => (g i : R j))) :
    Submodule.span (𝓞 K) (Set.range g) = spanIn C j w s := by
  unfold spanIn
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hg i)
  · intro x hx
    have hx' : (x : R j) ∈ Submodule.span (𝓞 K) s := hx
    let F : cutR C j w →ₗ[𝓞 K] R j := (cutR C j w).subtype.restrictScalars (𝓞 K)
    have hsub : Submodule.span (𝓞 K) s ≤ (Submodule.span (𝓞 K) (Set.range g)).map F := by
      rw [Submodule.span_le]
      intro f hf
      have hcl : AddSubgroup.closure (Set.range fun i => (g i : R j)) ≤
          ((Submodule.span (𝓞 K) (Set.range g)).map F).toAddSubgroup := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨g i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
      exact hcl (hs f hf)
    obtain ⟨y, hy, hyx⟩ := hsub hx'
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']

theorem exists_family (hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hn : IsNab Xo c nab) (ht : ThValTot Xo c nab) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {R : ℕ}
    (b : Fin R → MvPolynomial (LtN Dw n) c.F) (hb : ∀ i, b i ∈ harmA (Dw := Dw) c a n)
    (hgen : ∀ P ∈ harmA (Dw := Dw) c a n, ∃ z : Fin R → ℤ, P = ∑ i, (z i : c.F) • b i) :
    ∃ g : (Fin n → LevQ Dw l) × Fin R → Rul Xo c,
      (∀ p, IsThRule Xo c nab (fun k => levRep (p.1 k)) (b p.2) (g p)) ∧
      ∀ f ∈ thGen Xo c nab a n, f ∈ AddSubgroup.closure (Set.range g) := by
  have hex : ∀ p : (Fin n → LevQ Dw l) × Fin R,
      ∃ f : Rul Xo c, IsThRule Xo c nab (fun k => levRep (p.1 k)) (b p.2) f := fun p =>
    (existsUnique_thRule Xo c nab ht (fun k => levRep (p.1 k)) (hb p.2)).exists
  choose g hg using hex
  refine ⟨g, hg, ?_⟩
  rintro f ⟨x, P, hP, hf⟩
  obtain ⟨hlin, hmod⟩ := GlobalTheory.T.theta_rules_linear_and_level_congruence hci E H Dw l Xo c nab hn a n
  set q : Fin n → LevQ Dw l := fun k => Submodule.Quotient.mk (x k) with hq
  have hrep : ∀ k, x k - levRep (q k) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro k
    have h1 : Submodule.Quotient.mk (levRep (q k)) = q k := by
      unfold levRep
      exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q k))
    rw [← Submodule.Quotient.eq, h1]
  have hf' : IsThRule Xo c nab (fun k => levRep (q k)) P f := hmod x _ P f hrep hf
  obtain ⟨z, hz⟩ := hgen P hP
  have hsum : f = ∑ i, ((z i : ℤ) : c.F) • g (q, i) := by
    refine hlin (fun k => levRep (q k)) R (fun i => ((z i : ℤ) : c.F)) b f (fun i => g (q, i)) hb ?_ ?_ ?_
    · rw [← hz]; exact hP
    · rw [← hz]; exact hf'
    · intro i; exact hg (q, i)
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (q, i))) _

theorem log_rdE (D : D7) : Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) = lrd D := by
  have hf : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by
    first
    | exact_mod_cast Formalism.MainNotions.Gaps.LevGap.finrank_hostE_eq D.host
    | exact_mod_cast Formalism.MainNotions.StandardLattice.finrank_host D
  have hd : (NumberField.discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  unfold lrd ReciprocityTheory.ChartRestriction.G.FD.rdE ReciprocityTheory.ChartRestriction.G.FD.dE
  rw [Real.log_rpow (abs_pos.mpr hd), hf]
  ring

theorem absA_eq {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : absA w = (WeightAlgebra.DF w : ℝ) := by
  unfold absA WeightAlgebra.DF WeightAlgebra.degP
  push_cast
  rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem theta_family : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) => ∃ (N : ℕ) (w0 : Fin N → B.Cusp j w), Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll w ∧ N ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n)) ∧ ∀ k σ, Real.log (B.supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) (recB h.toLawsCore) (recPJ h j hj) := by
  intro hci D T h hG large₂ j hj w hpg hL hr hlast
  beta_reduce

  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    first
    | exact Formalism.MainNotions.Gaps.LevGap.finrank_hostE_eq D.host
    | exact Formalism.MainNotions.StandardLattice.finrank_host D
  have hfd : ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg
    omega
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.toLawsCore.toLawsM.pins.2.1.1
  have hk := D.R.m_add_three_le_k
  obtain ⟨hj1, hj2⟩ := id hj
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    have h4 := h.toLawsCore.toLawsM.pins.2.2.2 j hj
    unfold IsDatW at h4
    rw [h4.1, h4.2.1]
    simp only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]
    omega
  have hr1 : 1 ≤ D.R.r := by
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  have hnpos : 0 < w.n := by omega
  have hDF : Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w := ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
  have hLP : Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlast
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hnabex, -, htot, hcusp, -, -⟩ := id h
  obtain ⟨inst, hn⟩ := hnabex j hj
  obtain ⟨-, hlrd, -, -, hlf, -, -, hlDF, hln⟩ := id hpg

  have hrd : Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) ≤ 2 * large₂.sc.L := by
    rw [log_rdE]; exact hlrd
  have hfd' : Real.log (ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E) ≤ 2 * large₂.sc.L := by
    rw [hfd]; exact hlf
  have hDFr : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ WeightAlgebra.DF w := by exact_mod_cast hDF
  have hDF' : Real.log (1 + Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)) ≤ 2 * large₂.sc.L := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hlDF
    linarith
  obtain ⟨R, b, hb, hgen, hR, hl1⟩ := GlobalTheory.T.exists_reduced_integral_basis_harmonicPolynomials D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n
    (by rw [hpq]; exact hr) (wtA w) large₂.sc.L hL hrd hfd' hDF' hln

  obtain ⟨g, hgr, hgcl⟩ := exists_family hci (T.Q.Xo j) T.Q.c (T.nab j) hn (htot j hj) (wtA w) w.n b hb hgen
  have hmem : ∀ f, f ∈ T.th j w ↔ ∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
      P ∈ harmA T.Q.c (wtA w) w.n ∧ IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f := fun f => Iff.rfl
  have hth : ∀ p, g p ∈ T.th j w := fun p => (hmem _).2 ⟨fun k => levRep (p.1 k), b p.2, hb p.2, hgr p⟩
  have hcut : ∀ p, g p ∈ cutR T.C j w := by
    intro p
    unfold cutR
    rw [Submodule.mem_inf, Submodule.mem_iInf]
    exact ⟨hcusp j hj (wtA w) w.n (dom_wtA w) hLP (g p) (hth p), fun hn' => absurd hj hn'⟩
  have : Finite (LevQ (T.Q.Dw j) T.Q.l) := (GlobalTheory.T.card_lattice_quotient_half_level D.host.E T.Q.H (T.Q.Dw j) T.Q.l).1
  let e := Finite.equivFin ((Fin w.n → LevQ (T.Q.Dw j) T.Q.l) × Fin R)
  let w0 : Fin (Nat.card ((Fin w.n → LevQ (T.Q.Dw j) T.Q.l) × Fin R)) → ↥(cutR T.C j w) :=
    fun k => ⟨g (e.symm k), hcut (e.symm k)⟩
  refine ⟨_, (w0 : Fin _ → (recB h.toLawsCore).Cusp j w), ?_, ?_, ?_⟩
  ·
    have h2 : Set.range (fun k => ((w0 k : cutR T.C j w) : T.R j)) = Set.range g :=
      e.symm.surjective.range_comp g
    have hsp := span_eq_spanIn T.C j w (T.th j w) w0 (fun k => hth (e.symm k))
      (fun f hf => by rw [h2]; exact hgcl f ((hmem f).1 hf))
    exact hsp
  ·
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_fin,
      (GlobalTheory.T.card_lattice_quotient_half_level D.host.E T.Q.H (T.Q.Dw j) T.Q.l).2, hM, hfd, hpq, ← pow_mul]
    rw [hfd, hpq] at hR
    refine Nat.mul_le_mul le_rfl (le_trans hR (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by omega) _)))
  ·
    intro k σ
    have hs : (recB h.toLawsCore).supN j w σ (w0 k) = T.Ns j w σ (g (e.symm k)) := by
      dsimp only [recB, mkB]
      unfold cutN
      rw [if_pos hj]
    rw [hs]
    have hexp := hl1 (e.symm k).2 σ
    simp only [hfd, hpq] at hexp
    have hlg : 0 ≤ Real.log (Module.finrank ℚ T.Q.c.F) := Real.log_natCast_nonneg _
    have hld : 0 ≤ Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F := by
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply Real.log_nonneg
      have : (1 : ℤ) ≤ |NumberField.discr T.Q.c.F| := Int.one_le_abs (NumberField.discr_ne_zero _)
      exact_mod_cast this
    have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
    have hA : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ absA w := by rw [absA_eq]; exact hDFr
    have hrL : (0 : ℝ) ≤ 140 * (D.R.r : ℝ) * large₂.sc.L := by positivity
    have hAm := mul_le_mul_of_nonneg_left hA hrL
    have hfrnL : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L := by positivity
    have hDF0 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) := Nat.cast_nonneg _
    have hℓ : (0 : ℝ) ≤ 140 * ((D.R.r : ℕ) : ℝ) * large₂.sc.L * (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) +
        2 * (D.R.f : ℝ) * ((D.R.r : ℕ) : ℝ) * (w.n : ℝ) * large₂.sc.L + 4 * Real.log (Module.finrank ℚ T.Q.c.F) +
        Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F := by
      have : (0 : ℝ) ≤ 140 * ((D.R.r : ℕ) : ℝ) * large₂.sc.L * (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) := by positivity
      linarith
    have key := GlobalTheory.T.log_supNorm_thetaGenerator_le hci D T h hG large₂ j hj w hpg hL hr hLP (fun i => levRep ((e.symm k).1 i)) (b (e.symm k).2)
      (hb _) (g (e.symm k)) (hgr _) σ _ hℓ hexp
    have h30 := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w 0 hL hnpos).1
    show Real.log (T.Ns j w σ (g (e.symm k))) ≤ 400 * Zb D large₂ * w.size + 3 * (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L +
      5 * Real.log (Module.finrank ℚ T.Q.c.F) + Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F + 2
    nlinarith [key, h30, hAm, hfrnL, hlg, hld]

end GlobalTheory.ThetaFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAllFramesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_all_frames : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → 3 * WeightAlgebra.DF w + 2 ≤ T.Q.l.M → ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0 := by
  first | exact @GlobalTheory.RunIn.exists_theta_ne_zero_record | exact GlobalTheory.RunIn.exists_theta_ne_zero_record | (intros; apply GlobalTheory.RunIn.exists_theta_ne_zero_record <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegralityBoundOfFamilyContainingScaledThetaRul
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem totalDegree_eq_sum_rows {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmA c a n) (h0 : P ≠ 0) (hh : P.IsHomogeneous P.totalDegree) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  classical
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 h0
  have hr := hP.1.2.2 m hm
  have h1 := hh (MvPolynomial.mem_support_iff.1 hm)
  have h2 : m.degree = P.totalDegree := by rw [Finsupp.degree_eq_weight_one]; exact h1
  rw [← h2, Finsupp.degree_eq_sum]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hr τ i

theorem lieFac_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (x : ℝ) (hx : 0 < x)
    (a : (E →+* ℂ) × ℕ → ℕ) (d : ℕ) (hd : d = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) :
    lieFac Dw x a ^ 2 = ((2 * Real.pi * x)⁻¹) ^ d := by
  have hp : 0 < 2 * Real.pi * x := by positivity
  have hd' : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = d := by rw [hd]; push_cast; rfl
  unfold lieFac
  rw [hd', ← Real.exp_nat_mul, ← Real.exp_log (inv_pos.2 hp), ← Real.exp_nat_mul, Real.log_inv]
  congr 1
  push_cast
  ring

theorem i2iAt_of_containsTh : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → (∀ σ, GoodEmb c σ → IsUnf (U σ) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x)) ∧ ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), Dom a n → P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ s : c.F, (∀ σ : c.F →+* ℂ, (l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ s‖ ^ 2) → ∀ (N : ℕ) (wR : Fin (N + 1) → Rul Xo c), (∀ i, wR i ∈ sec Xo c a n) → ContainsTh Xo c nab s P₁ wR → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∀ tableLineDegreeFive cc : ℝ, p14 E r n m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (m : ℝ) ^ 4 * (I2.dstar (E := E) m : ℝ) ^ 4 * I2.RR (E := E) / l.M ≤ cc → I2AtFramePoints U xR wR (a, n) (I2.th (E := E) l.M R0) tableLineDegreeFive P₁.totalDegree cc := by
  intro hCI E _ _ _ H Dw l Xo c _ r U xR nab hnab hU α hα hMb a n P₁ hdom hP hbp s hs N wR hw hct R0 m hrun hm
    tableLineDegreeFive cc hP14 hcc σ hσ k x hx
  classical
  obtain ⟨hUn, hFT, hxi⟩ := hU σ hσ
  obtain ⟨b, -, hbd, hbo, -, hphi, hpn⟩ := exists_ortho_frame E r ((U σ).X k) x hx
  obtain ⟨T, Pr, hTr, hq, hPm, hph, hbound⟩ := GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound hCI E H Dw l Xo c σ r (U σ) k ⟨_, hbd⟩ xR nab hnab hσ hUn
    (hFT k _) hbo (hxi k) α hα hMb a n P₁ hP hbp R0 m hrun hm
  obtain ⟨h0, hh, -⟩ := GlobalTheory.T.determinantBlockProduct_rename_torusPolynomial E H Dw n c.F σ P₁ hbp Dw.mult id (fun _ => le_rfl) Function.injective_id
  have hdeg := totalDegree_eq_sum_rows c a n P₁ hP h0 hh
  have hxR : 0 < xR := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hxi k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 ((U σ).X k).ξ0_ne)
  have hM : (0 : ℝ) < l.M := by
    have := Pr.hq
    rw [hq] at this
    exact_mod_cast this
  obtain ⟨jb, hjb, hf⟩ := hct
  choose f hf1 hf2 using hf
  haveI : Finite (LevQ Dw l) := (GlobalTheory.card_levQ E H Dw l).1
  haveI : Fintype (Fin n → LevQ Dw l) := Fintype.ofFinite _
  have hb := hbound f hf1
  rw [finsum_eq_sum_of_fintype] at hb
  have hrec : ∀ j, recNrm (U σ) xR a n (wR j) k x =
      lieFac Dw xR a * ‖rdU (U σ) (wR j) k (FD.rmul x b)‖ := fun j => by
    unfold recNrm
    rw [hpn _ _ (hUn.2.2.2.2.1 a n hdom (wR j) (hw j) k)]
  have hval : ∀ q, rdU (U σ) (wR (jb q)) k (FD.rmul x b) =
      σ s * toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩)) := fun q => by
    have e : wR (jb q) = s • f q := by
      funext p y
      rw [hf2 q p y]
      exact (Algebra.smul_def s (f q p y)).symm
    rw [e, map_smulₛₗ]
    show σ s * rdU (U σ) (f q) k (FD.rmul x b) = _
    congr 1
    exact dif_pos hbd
  have hkey : (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ j, recNrm (U σ) xR a n (wR j) k x ^ 2 := by
    have hl := lieFac_sq Dw xR hxR a _ hdeg
    have hL : (0 : ℝ) ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree := by positivity
    calc (Real.pi⁻¹) ^ P₁.totalDegree * Pr.Jbound n
        = ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ((2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n)) := by
          rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow]
          congr 2
          field_simp
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * ((l.M : ℝ) ^ P₁.totalDegree *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hL
      _ ≤ ((2 * Real.pi * xR)⁻¹) ^ P₁.totalDegree * (‖σ s‖ ^ 2 *
            ∑ q, ‖toC (evR Xo c (f q) ((U σ).un k ⟨_, hbd⟩))‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hs σ)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hL
      _ = ∑ q, recNrm (U σ) xR a n (wR (jb q)) k x ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hrec, hval, mul_pow, hl, norm_mul, mul_pow]
      _ = ∑ j ∈ Finset.univ.image jb, recNrm (U σ) xR a n (wR j) k x ^ 2 :=
          (Finset.sum_image (f := fun j => recNrm (U σ) xR a n (wR j) k x ^ 2) fun _ _ _ _ h => hjb h).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have hfin := neg_log_sqrt_le_of_jbound E T P₁.totalDegree n Pr _ tableLineDegreeFive cc hkey (by rw [hTr, hPm]; exact hP14)
    (by rw [hPm, hq]; exact hcc)
  rw [hph] at hfin
  rw [← hphi]
  exact hfin

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_supNorm_shortThetaGenerator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.log_sup_short_generator_le | exact GlobalTheory.RunIn.log_sup_short_generator_le | (intros; apply GlobalTheory.RunIn.log_sup_short_generator_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NetDataExists
section
open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn.NetAtRecord

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem good_conj_iff (c : Coeff l) (σ : c.F →+* ℂ) :
    GoodEmb c (ComplexEmbedding.conjugate σ) ↔ ¬ GoodEmb c σ := by
  constructor
  · intro h1 h2
    have e : (starRingEnd ℂ) H.rt0 = H.rt0 := by
      have h3 : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h1
      rwa [show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h2] at h3
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp e
    have hre := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  · intro h
    have := goodEmb_goodOf c σ
    unfold goodOf at this
    rwa [if_neg h] at this

theorem goodOf_conj (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c (ComplexEmbedding.conjugate σ) = goodOf c σ := by
  unfold goodOf
  by_cases h : GoodEmb c σ
  · rw [if_neg (fun h' => (good_conj_iff c σ).1 h' h), if_pos h]
    ext x; simp [ComplexEmbedding.conjugate]
  · rw [if_pos ((good_conj_iff c σ).2 h), if_neg h]; rfl

end

theorem supN_conj {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ)
    (F : (recB h.toLawsCore).Cusp j w) :
    (recB h.toLawsCore).supN j w (ComplexEmbedding.conjugate σ) F = (recB h.toLawsCore).supN j w σ F := by
  have e : T.Ns j w (ComplexEmbedding.conjugate σ) = T.Ns j w σ := by
    funext f
    unfold Core.Ns
    rw [goodOf_conj]
  change cutN T.C T.Ns j w (ComplexEmbedding.conjugate σ) F = cutN T.C T.Ns j w σ F
  unfold cutN
  rw [e]

theorem netData_exists : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∃ Nt : NetData (recB h.toLawsCore) j w, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt (1041 * Zb D large₂ ^ 3) ∧ ∀ σ, NetInj Nt σ := by
  intro D T h hG large₂ j hj w hP hL hr hf
  classical
  have key := GlobalTheory.T.exists_scalar_evaluations_cusp_forms_finite_net D T h hG large₂ j hj w hP hL hr hf
  have key2 : ∀ σ : T.Q.c.F →+* ℂ, ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)),
      GoodEmb T.Q.c σ → (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧
        (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧
        ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F →
          LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
    intro σ
    by_cases hσ : GoodEmb T.Q.c σ
    · obtain ⟨n, ev, H⟩ := key σ hσ
      exact ⟨n, ev, fun _ => H⟩
    · exact ⟨0, Fin.elim0, fun h' => absurd h' hσ⟩
  choose n ev H using key2
  exact GlobalTheory.T.exists_netData_from_half_conjugate_embeddings D (recB h.toLawsCore) j w (GoodEmb T.Q.c)
    (fun σ => by rw [good_conj_iff]; exact not_not.symm) (supN_conj h j w) n ev _ H

end GlobalTheory.RunIn.NetAtRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorsNoCommonZeroOfChartIndependenceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerators_noCommonZero_of_chartIndependence : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → NoCommonZeroSt := by
  first | exact @GlobalTheory.noCommonZero_of_chartIndep | exact GlobalTheory.noCommonZero_of_chartIndep | (intros; apply GlobalTheory.noCommonZero_of_chartIndep <;> assumption)
end

