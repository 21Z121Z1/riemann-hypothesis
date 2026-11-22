import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0183
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenImmersionChart
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0182
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0184
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import GroundTheory.GlobalFields.TateThesis.TateMain

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisZeroImageDividedPower
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogEpsP

variable {l : ℕ} [Fact l.Prime]

theorem cris_eq_zero (A : PAlg l) (n : ℕ) {y : Acris l}
    (hy : y ∈ Ideal.span {(l : Acris l)} ^ n) : A.cris n y = 0 := by
  rw [Ideal.span_singleton_pow] at hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul, map_pow, map_natCast, PAlg.pow_l_acr, mul_zero]

theorem cris_log (A : PAlg l) (n : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    A.cris n (ACris.log hx) = ∑ k ∈ Finset.range (l * n), A.cris n (ACris.logTerm hx k) := by
  obtain ⟨N, hN⟩ := ACris.isAdicSum_log hx n
  have h2 := cris_eq_zero A n (hN (max N (l * n)) (le_max_left _ _))
  rw [map_sub, sub_eq_zero, map_sum,
    ← Finset.sum_range_add_sum_Ico _ (le_max_right N (l * n)),
    Finset.sum_eq_zero (s := Finset.Ico (l * n) (max N (l * n))) (fun k hk =>
      cris_eq_zero A n (ACris.logTerm_mem hx (Finset.mem_Ico.1 hk).1)), add_zero] at h2
  exact h2

theorem cris_logTerm (A : PAlg l) (n k : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    A.cris n (ACris.logTerm hx k) =
      (-1) ^ k * (k.factorial : A.Acr n) * A.mkAcr n (A.cris0 (ACris.dpowZero hx (k + 1))) := by
  rw [ACris.logTerm, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    PAlg.cris_of, ACris.logTermZero]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

theorem acrisZero_image_divided_power (A : PAlg l) (k : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    (A.cris0 (ACris.dpowZero hx k)).1 = dpw k (WittVector.map A.s x) :=
  awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) x

theorem map_mu (A : PAlg l) (e : Ob l) :
    WittVector.map A.s (AInf.mu (K := ℂ_[l]) (p := l) e) = WittVector.teichmuller l (A.s e) - 1 := by
  rw [AInf.mu, map_sub, map_one, WittVector.map_teichmuller]

end GlobalTheory.CompanionTheory.LogEpsP

theorem GlobalTheory.CompanionTheory.LogEpsP.logEps : CrystallineSemistableComparison.E.LogEps := by
  intro l _ A n
  refine ⟨fun k => A.cris0 (ACris.dpowZero (ACris.mu_mem_ker (untilt_epsilon (p := l))) k), fun k => ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LogEpsP.acrisZero_image_divided_power, GlobalTheory.CompanionTheory.LogEpsP.map_mu]
  · rw [ACris.periodT, GlobalTheory.CompanionTheory.LogEpsP.cris_log]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.CompanionTheory.LogEpsP.cris_logTerm A n k _
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobalStatement
section
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_local_to_global : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) → ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | exact GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local | (intros; apply GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechFormsAddSmulStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_forms_add_smul : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j), cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x := by
  first | exact @GlobalTheory.CompanionTheory.OmCech.cechOmAdd_smul | exact GlobalTheory.CompanionTheory.OmCech.cechOmAdd_smul | (intros; apply GlobalTheory.CompanionTheory.OmCech.cechOmAdd_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechH0PullCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h0_pull_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : cechH G.obj V 0),
    (cechHZeroEquivH G' U hU : cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((cechHZeroEquivH G V hV : cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  first | exact @GlobalTheory.CompanionTheory.CechZero.cechHZeroEquivH_pull | exact GlobalTheory.CompanionTheory.CechZero.cechHZeroEquivH_pull | (intros; apply GlobalTheory.CompanionTheory.CechZero.cechHZeroEquivH_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_short_exact_pull_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {F I Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {g₁ : F ⟶ I} {g₂ : I ⟶ Q} {g₁' : F' ⟶ I'} {g₂' : I' ⟶ Q'}
    (hC : IsCechShortExact V g₁ g₂) (hC' : IsCechShortExact U g₁' g₂') (φ₁ : F ⟶ (Opens.map f).op ⋙ F')
    (φ₂ : I ⟶ (Opens.map f).op ⋙ I') (φ₃ : Q ⟶ (Opens.map f).op ⋙ Q')
    (h₁₂ : ∀ W x, φ₂.app W (g₁.app W x) = g₁'.app _ (φ₁.app W x))
    (h₂₃ : ∀ W x, φ₃.app W (g₂.app W x) = g₂'.app _ (φ₂.app W x)) (n : ℕ) (σ : cocycles Q V n),
    cechPullH f φ₁ V U τ hτ (n + 1) (hC.delta n σ) =
      hC'.delta n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩ := by
  first | exact @GlobalTheory.CompanionTheory.OmCechDelta.cechPullH_delta | exact GlobalTheory.CompanionTheory.OmCechDelta.cechPullH_delta | (intros; apply GlobalTheory.CompanionTheory.OmCechDelta.cechPullH_delta <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNorm
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.ChartDenom

theorem exists_nat_mul_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingQ y c) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * x ∈ chartRingZ y c := by
  unfold chartRingQ at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Nat.cast_one, one_mul]
    exact Algebra.subset_adjoin hx
  | algebraMap r =>
    refine ⟨r.den, r.den_ne_zero, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_ne_zero
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [h]
    exact intCast_mem _ _
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u + v) = (n : Ω) * ((m : Ω) * u) + (m : Ω) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hmu) (mul_mem (natCast_mem _ _) hnv)
  | mul u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u * v) = ((m : Ω) * u) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact mul_mem hmu hnv

theorem chartLatQ_le_span_chartLatNm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ),
      chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  intro K _ ι _ Ω _ _ y a τ s hs
  classical
  have hex : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_chartRingZ y c (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hc⟩
  choose n hn0 hn using hex
  have hN : (∏ c, n c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hn0 c
  have hNΩ : (((∏ c, n c : ℕ)) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : (((∏ c, n c : ℕ)) : Ω) * s ∈ chartLatNm y a τ := by
    intro c hc
    have e : ((((∏ c, n c : ℕ)) : Ω) * s) * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
          ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      push_cast; ring
    rw [e]
    have h : (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
        ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) ∈ chartRingZ y c :=
      mul_mem (natCast_mem _ _) (hn c hc)
    exact Subalgebra.algebraMap_mem (integralClosure (chartRingZ y c) Ω) (⟨_, h⟩ : chartRingZ y c)
  have h1 : (((∏ c, n c : ℕ)) : Ω) * s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω) :=
    Submodule.subset_span hmem
  have h2 := Submodule.smul_mem _ (((∏ c, n c : ℕ) : ℚ)⁻¹) h1
  have e : (((∏ c, n c : ℕ) : ℚ)⁻¹) • ((((∏ c, n c : ℕ)) : Ω) * s) = s := by
    rw [Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hNΩ, one_mul]
  rwa [e] at h2

end GlobalTheory.CompanionTheory.Ar.ChartDenom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShift
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Conductor

theorem mem_chartRingQ_of_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω}
    (hx : x ∈ chartRingZ y c) : x ∈ chartRingQ y c := by
  unfold chartRingZ at hx
  unfold chartRingQ
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin hz
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add u v _ _ hu hv => exact add_mem hu hv
  | mul u v _ _ hu hv => exact mul_mem hu hv

theorem exists_conductor_section :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
      ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ),
        ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω),
          c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  classical
  intro K _ ι _ Ω _ _ y D _ hbir
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  refine ⟨∑ c : C, δ c, ∏ c : C, aeval y (F c), Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c,
    fun a τ s hs => ?_⟩
  have key : ∀ s ∈ chartLatNm y a τ, (∏ c : C, aeval y (F c)) * s ∈
      chartLatQ y ((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) 1 := by
    intro s hs c' hc'
    let c : C := ⟨c', hc'⟩
    have hx := hs c' hc'
    have hm : ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) *
          (((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) k))) =
        (∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) * Conductor.invMon y c' (∑ c : C, δ c) := by
      rw [← Conductor.prod_zpow_eq_invMon, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc' k)]
      congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
      ring
    apply mem_chartRingQ_of_mem_chartRingZ
    rw [hm, ← Conductor.invMon_sum y c' Finset.univ δ]
    have hsplit : (∏ b : C, aeval y (F b)) * s * ((∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) *
          ∏ b : C, Conductor.invMon y c' (δ b)) =
        (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
          (aeval y (F c) * Conductor.invMon y c' (δ c) *
            (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
        ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
        Finset.prod_mul_distrib]
      ring
    rw [hsplit]
    exact mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b)) (hcond c _ hx)
  induction hs using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero => simpa using Submodule.zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
  | smul r u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu

end GlobalTheory.CompanionTheory.Conductor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeWchMem

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D :=
  fun D N i h j => GlobalTheory.CompanionTheory.ConeChart.preimage_chart_mem D N i h j

end GlobalTheory.CompanionTheory.ConeWchMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassUniqueOfLiftAndLog
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtChern

theorem restrict_id_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (x : H (𝟭 C ⋙ F) 2) (x' : H F 2)
    (h : x = (Mor.restrict F (𝟭 C)).pull 2 x') : x = x' := by
  subst h
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  rfl

theorem chern_class_unique_of_lift_and_log : CrystallineSemistableComparison.E.LiftEx → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.FirstChernUniqueEtale := by
  intro hL hG l _ H O _ X q κ D hE y y' hy hy'
  obtain ⟨Λ⟩ := (hL l H O X q κ (El (PX q κ)) (𝟭 _) D).2 hE
  funext n
  obtain ⟨z, hz, hc, e⟩ := hy (El (PX q κ)) (𝟭 _) Λ n
  obtain ⟨z', hz', hc', e'⟩ := hy' (El (PX q κ)) (𝟭 _) Λ n
  have hzz : z = z' := by
    funext s
    exact (hG l _ n).2.1 _ _ _ (hc s) (hc' s)
  subst hzz
  have e1 := restrict_id_pull _ _ _ e
  have e2 := restrict_id_pull _ _ _ e'
  exact e1.symm.trans e2

end GlobalTheory.CompanionTheory.EtChern
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsCongr
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

universe w w'

section LES

theorem cls_congr {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {x y : K.X n} (h : x = y) (hx : K.d n x = 0)
    (hy : K.d n y = 0) : K.cls x hx = K.cls y hy := by
  subst h; rfl

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}

theorem sq_mapH {K L : Cx.{w} R} {K' L' : Cx.{w'} R'} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L L' σ)
    (φ' : Cx.Hom K' L' (RingHom.id R')) (ψ' : Cx.Hom K K' σ)
    (h : ∀ n x, ψ.f n (φ.f n x) = φ'.f n (ψ'.f n x)) (n : ℕ) (z : K.H n) :
    ψ.mapH n (φ.mapH n z) = φ'.mapH n (ψ'.mapH n z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 z
  have c1 : L.d n (φ.f n x) = 0 := by rw [φ.comm, hx, map_zero]
  have c2 : L'.d n (ψ.f n (φ.f n x)) = 0 := by rw [ψ.comm, c1, map_zero]
  have c3 : K'.d n (ψ'.f n x) = 0 := by rw [ψ'.comm, hx, map_zero]
  have c4 : L'.d n (φ'.f n (ψ'.f n x)) = 0 := by rw [φ'.comm, c3, map_zero]
  rw [CrystallineSemistableComparison.P.mapH_cls φ n x hx c1, CrystallineSemistableComparison.P.mapH_cls ψ n _ c1 c2, CrystallineSemistableComparison.P.mapH_cls ψ' n x hx c3,
    CrystallineSemistableComparison.P.mapH_cls φ' n _ c3 c4]
  exact cls_congr (h n x) _ _

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

theorem tens_les [∀ i, Module.Flat R (N i)]
    {K L M : ι → Cx.{w} R} {K' L' M' : Cx.{w'} R'}
    (f : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) (g : ∀ i, Cx.Hom (L i) (M i) (RingHom.id R))
    (hf : ∀ i n, Function.Injective ((f i).f n)) (hfg : ∀ i n, Function.Exact ((f i).f n) ((g i).f n))
    (hg : ∀ i n, Function.Surjective ((g i).f n))
    (f' : Cx.Hom K' L' (RingHom.id R')) (g' : Cx.Hom L' M' (RingHom.id R'))
    (hf' : ∀ n, Function.Injective (f'.f n)) (hfg' : ∀ n, Function.Exact (f'.f n) (g'.f n))
    (hg' : ∀ n, Function.Surjective (g'.f n))
    (a : ∀ i, N i → Cx.Hom (K i) K' σ) (b : ∀ i, N i → Cx.Hom (L i) L' σ) (c : ∀ i, N i → Cx.Hom (M i) M' σ)
    (hab : ∀ i n k x, (b i n).f k ((f i).f k x) = f'.f k ((a i n).f k x))
    (hbc : ∀ i n k x, (c i n).f k ((g i).f k x) = g'.f k ((b i n).f k x))
    (hL : ∀ j, Tens R (N := N) (M := fun i => (L i).H j) (M' := L'.H j) fun i n x => (b i n).mapH j x)
    (hM : ∀ j, Tens R (N := N) (M := fun i => (M i).H j) (M' := M'.H j) fun i n x => (c i n).mapH j x)
    (hadd : ∀ i j, ∃ F : N i ⊗[R] (K i).H j →+ K'.H j, ∀ n x, F (n ⊗ₜ x) = (a i n).mapH j x) :
    ∀ j, Tens R (N := N) (M := fun i => (K i).H j) (M' := K'.H j) fun i n x => (a i n).mapH j x := by
  intro j
  choose δ hδ h0 e1 e2 e3 using fun i => CrystallineSemistableComparison.P.les (f i) (g i) (hf i) (hfg i) (hg i)
  obtain ⟨δ', hδ', h0', e1', e2', e3'⟩ := CrystallineSemistableComparison.P.les f' g' hf' hfg' hg'
  have dcomm : ∀ i n k z, (a i n).mapH (k + 1) (δ i k z) = δ' k ((c i n).mapH k z) := by
    intro i n k z
    obtain ⟨m, hm, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (M i) k).1 z
    obtain ⟨y, rfl⟩ := hg i k m
    obtain ⟨x, hx⟩ := CrystallineSemistableComparison.CechClassBoundaries.conn_ex (f i) (g i) (hfg i) y hm
    have hxc := CrystallineSemistableComparison.CechClassBoundaries.conn_cyc (f i) (hf i) y x hx
    have c3 : K'.d (k + 1) ((a i n).f (k + 1) x) = 0 := by rw [(a i n).comm, hxc, map_zero]
    have c4 : M'.d k ((c i n).f k ((g i).f k y)) = 0 := by rw [(c i n).comm, hm, map_zero]
    have c5 : M'.d k (g'.f k ((b i n).f k y)) = 0 := by rw [← hbc]; exact c4
    rw [hδ i k y x hm hxc hx, CrystallineSemistableComparison.P.mapH_cls (a i n) _ x hxc c3, CrystallineSemistableComparison.P.mapH_cls (c i n) k _ hm c4,
      cls_congr (hbc i n k y) c4 c5, hδ' k _ _ c5 c3 (by rw [← hab, hx, (b i n).comm])]
  cases j with
  | zero =>
    refine tens_five (M₁ := fun _ => PUnit.{w + 1}) (M₂ := fun _ => PUnit.{w + 1}) (L₁ := PUnit.{w' + 1}) (L₂ := PUnit.{w' + 1})
      (fun _ => 0) (fun _ => 0) (fun i => (f i).mapH 0) (fun i => (g i).mapH 0)
      0 0 (f'.mapH 0).toAddMonoidHom (g'.mapH 0).toAddMonoidHom
      (fun _ _ _ => 0) (fun _ _ _ => 0) _ (fun i n x => (b i n).mapH 0 x) (fun i n x => (c i n).mapH 0 x)
      (fun _ _ _ => rfl) (fun i n x => ?_) (fun i n x => ?_) (fun i n x => ?_)
      (fun i y => by simp) (fun i y => ?_) (fun i => e1 i 0)
      (fun y => by simp) (fun y => ?_) (e1' 0)
      (tens_zero (fun _ => inferInstance) inferInstance _) (tens_zero (fun _ => inferInstance) inferInstance _)
      (hL 0) (hM 0) (fun i => hadd i 0)
    · have : (0 : PUnit.{w + 1} →ₗ[R] (K i).H 0) x = 0 := rfl
      simp
    · exact sq_mapH (f i) (b i n) f' (a i n) (hab i n) 0 x
    · exact sq_mapH (g i) (c i n) g' (b i n) (hbc i n) 0 x
    · constructor
      · intro h
        have : y = 0 := h0 i (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
    · constructor
      · intro h
        have : y = 0 := h0' (h.trans (map_zero _).symm)
        exact ⟨0, by simp [this]⟩
      · rintro ⟨t, rfl⟩
        simp
  | succ k =>
    exact tens_five (fun i => (g i).mapH k) (fun i => δ i k) (fun i => (f i).mapH (k + 1)) (fun i => (g i).mapH (k + 1))
      (g'.mapH k).toAddMonoidHom (δ' k).toAddMonoidHom (f'.mapH (k + 1)).toAddMonoidHom (g'.mapH (k + 1)).toAddMonoidHom
      (fun i n x => (b i n).mapH k x) (fun i n x => (c i n).mapH k x) _
      (fun i n x => (b i n).mapH (k + 1) x) (fun i n x => (c i n).mapH (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) k x) (fun i n x => dcomm i n k x)
      (fun i n x => sq_mapH (f i) (b i n) f' (a i n) (hab i n) (k + 1) x)
      (fun i n x => sq_mapH (g i) (c i n) g' (b i n) (hbc i n) (k + 1) x)
      (fun i => e2 i k) (fun i => e3 i k) (fun i => e1 i (k + 1)) (e2' k) (e3' k) (e1' (k + 1))
      (hL k) (hM k) (hL (k + 1)) (hM (k + 1)) (fun i => hadd i (k + 1))

end LES

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleRootsLiftToTiltStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_roots_lift_to_tilt : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U), (∀ i, u (i + 1) ^ l = u i) → ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp | exact GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAdeleWeight
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EpConvB

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors
open GroundTheory.Global GroundTheory.Automorphic

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) : ℝ :=
  if y.2 ∈ idealFiniteAdeles L then ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ else 0

theorem adeleWeight_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    0 ≤ adeleWeight L A y := by
  unfold adeleWeight
  split_ifs <;> positivity

theorem adeleWeight_le_one (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ 1 := by
  unfold adeleWeight
  split_ifs
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (homeomorphMixedSpace K y.1)]))
  · exact zero_le_one

theorem adeleWeight_mono {L L' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (L : FractionalIdeal (𝓞 K)⁰ K) ≤ L') (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ adeleWeight L' A y := by
  unfold adeleWeight
  by_cases h1 : y.2 ∈ idealFiniteAdeles L
  · have h2 : y.2 ∈ idealFiniteAdeles L' := idealFiniteAdeles_subset h h1
    simp only [if_pos h1, if_pos h2, le_refl]
  · rw [if_neg h1]
    split_ifs
    · positivity
    · exact le_rfl

@[simp] theorem adeleWeight_zero (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    adeleWeight L A (0 : 𝔸[K]) = 1 := by
  have h0 : (0 : 𝔸[K]).2 ∈ idealFiniteAdeles L := zero_mem _
  have h1 : homeomorphMixedSpace K (0 : 𝔸[K]).1 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  unfold adeleWeight
  rw [if_pos h0, h1]
  simp

theorem continuous_adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    Continuous (adeleWeight (K := K) L A) := by
  have hc : IsClopen ((idealFiniteAdeles L : AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K]) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles L), isOpen_idealFiniteAdeles L⟩
  have hc' : IsClopen {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L} := hc.preimage continuous_snd
  have hf : Continuous fun y : 𝔸[K] ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun y ↦ ?_
    have := norm_nonneg (homeomorphMixedSpace K y.1)
    positivity
  have : adeleWeight (K := K) L A = Set.indicator {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L}
      (fun y ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹) := by
    funext y
    simp only [adeleWeight, Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]
  exact hf.indicator (by rw [hc'.frontier_eq]; simp)
end

end GlobalTheory.CompanionTheory.EpConvB
end

