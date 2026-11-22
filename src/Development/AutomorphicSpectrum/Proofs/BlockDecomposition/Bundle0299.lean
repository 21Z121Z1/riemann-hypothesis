import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0290
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0288
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.Bundle0002
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFundamentalDomainDiff
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Unfolding

theorem setLIntegral_le_mul_fundamentalDomain_diff {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (F S T : Set G) (hF : IsFundamentalDomain Γ F μ) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : G → ℝ≥0∞) (hh : Measurable h)
    (hinv : ∀ γ ∈ Γ, ∀ x, h (γ * x) = h x) (N : ℕ)
    (hN : ∀ x, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (hST : ∀ γ ∈ Γ, ∀ x, γ * x ∈ S → x ∉ T) :
    ∫⁻ x in S, h x ∂μ ≤ N * ∫⁻ x in F \ T, h x ∂μ := by
  have hmeas : ∀ γ : Γ, Measurable (fun x : G => S.indicator h (γ • x)) := fun γ =>
    (hh.indicator hS).comp (measurable_const_smul γ)
  have h1 : ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := by
    rw [← lintegral_indicator hS]
    exact hF.lintegral_eq_tsum'' _
  have hpt : ∀ x, ∑' γ : Γ, S.indicator h (γ • x) ≤ N * Tᶜ.indicator h x := by
    intro x
    by_cases hx : x ∈ T
    · have hz : ∀ γ : Γ, S.indicator h (γ • x) = 0 := fun γ => by
        apply Set.indicator_of_notMem
        intro hmem
        exact hST γ γ.2 x (by simpa [Subgroup.smul_def] using hmem) hx
      simp [hz]
    · have hrew : ∀ γ : Γ, S.indicator h (γ • x) =
          ({γ : Γ | (γ : G) * x ∈ S}).indicator (fun _ => h x) γ := fun γ => by
        by_cases hg : (γ : G) * x ∈ S
        · rw [Set.indicator_of_mem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_mem hg, hinv γ γ.2 x]
        · rw [Set.indicator_of_notMem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_notMem hg]
      simp_rw [hrew]
      rw [← tsum_subtype, ENNReal.tsum_set_const,
        Set.indicator_of_mem (show x ∈ Tᶜ from hx)]
      gcongr
      have hc := ENat.toENNReal_le.mpr (hN x)
      simpa using hc
  calc ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := h1
    _ = ∫⁻ x in F, ∑' γ : Γ, S.indicator h (γ • x) ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ ≤ ∫⁻ x in F, (N : ℝ≥0∞) * Tᶜ.indicator h x ∂μ := lintegral_mono hpt
    _ = N * ∫⁻ x in F, Tᶜ.indicator h x ∂μ :=
        lintegral_const_mul _ (hh.indicator hT.compl)
    _ = N * ∫⁻ x in F \ T, h x ∂μ := by
        rw [setLIntegral_indicator hT.compl, Set.inter_comm, Set.diff_eq]

end GlobalTheory.CompanionTheory.Unfolding
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleVecMulUnipMatrix
section
noncomputable section

open NumberField Filter Topology Matrix
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
  GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.SiegelEscape

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_eq_of_mem_lat {γ : AdelicGLn.AdelicGL K n} (hγ : γ ∈ lat K n) :
    ∃ (γ₀ : GL (Fin n) K) (u : IdeleGroup K),
      γ = AdelicGLn.diagonal K n γ₀ * scalarUnits K n u := by
  set s : IdeleGroup K := posIdele (Real.exp 1) (Real.exp_pos _) with hs
  have hz : (tor K fun _ : Fin n => (1 : ℝ)) = scalarUnits K n s := rfl
  have hN : (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [hz, ← map_zpow, ← scalarUnits_mul_comm, mul_inv_cancel_right, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have h := Subgroup.mul_normal (AdelicGLn.diagonal K n).range
    (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ)))
  have hγ' : γ ∈ (↑((AdelicGLn.diagonal K n).range ⊔
      Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))) : Set (AdelicGLn.AdelicGL K n)) := hγ
  rw [h] at hγ'
  obtain ⟨a, ⟨γ₀, rfl⟩, b, hb, rfl⟩ := Set.mem_mul.1 hγ'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact ⟨γ₀, s ^ k, by rw [hz, map_zpow]⟩

theorem detModule_scalarUnits (u : IdeleGroup K) :
    (detModule K n (scalarUnits K n u) : ℝ) = (ideleModule K u : ℝ) ^ n := by
  rw [detModule, MonoidHom.comp_apply, scalarUnits_apply, det_diagUnits, map_prod,
    coe_finset_prod_pos]
  simp

theorem detModule_unipGL {r : ℕ} (X : UPos n r → 𝔸[K]) : detModule K n (unipGL X) = 1 :=
  mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL X)

theorem detModule_diagonal (γ₀ : GL (Fin n) K) : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)

theorem detModule_aR {r : ℕ} (hr : r ≤ n) (t : ℝ) :
    (detModule K n (aR K n r t) : ℝ) = Real.exp (r * t) ^ Module.finrank ℚ K := by
  have h := ideleModule_det_diagUnits_posIdele (K := K) (n := n)
    (fun i : Fin n => Real.exp (if (i : ℕ) < r then t else 0)) (fun _ => Real.exp_pos _)
  have h2 : ∏ i : Fin n, Real.exp (if (i : ℕ) < r then t else 0) = Real.exp (r * t) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 2
    simp [Fin.card_filter_val_lt, hr]
  rw [h2] at h
  exact h

theorem ratVec_single (l : Fin n) : ratVec (Pi.single l (1 : K)) = Pi.single l (1 : 𝔸[K]) := by
  ext1 i
  by_cases h : i = l
  · subst h; simp [ratVec]
  · simp [ratVec, h]

theorem single_vecMul_unipMatrix {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (X : UPos n r → 𝔸[K]) :
    Pi.single l (1 : 𝔸[K]) ᵥ* unipMatrix X = Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  ext1 j
  rw [Matrix.single_one_vecMul]
  simp [unipMatrix, blockEntry_apply, h, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem single_vecMul_aR {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (t : ℝ) :
    Pi.single l (1 : 𝔸[K]) ᵥ* ((aR K n r t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  have h1 : ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ = 1 → posIdele (K := K) ρ hρ = 1 := by
    rintro _ _ rfl
    exact map_one (posIdeleHom K)
  rw [aR, tor, coe_diagUnits]
  ext1 j
  rw [Matrix.vecMul_diagonal]
  by_cases hj : j = l
  · subst hj
    rw [h1 _ _ (by simp [h])]
    simp
  · simp [Pi.single_apply, hj]

theorem height_eq {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (γ₀ : GL (Fin n) K) (u : IdeleGroup K)
    (X : UPos n r → 𝔸[K]) (t : ℝ) (q : AdelicGLn.AdelicGL K n) :
    Reduction.height (AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q))
        (Pi.single l (1 : K) ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (ideleModule K u : ℝ) *
        adelicNorm (Pi.single l (1 : 𝔸[K]) ᵥ* (q : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  rw [mul_assoc, height_diagonal_mul, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.vecMul_one, Reduction.height, ratVec_single, Units.val_mul, Units.val_mul,
    Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    coe_unipGL, scalarUnits_apply, coe_diagUnits]
  have h0 : Pi.single l (1 : 𝔸[K]) ᵥ* Matrix.diagonal (fun _ : Fin n => ((u : IdeleGroup K) : 𝔸[K])) =
      ((u : IdeleGroup K) : 𝔸[K]) • Pi.single l (1 : 𝔸[K]) := by
    ext1 j
    rw [Matrix.vecMul_diagonal]
    simp [mul_comm]
  rw [h0, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, single_vecMul_unipMatrix hl,
    single_vecMul_aR hl]
  have hne : (Pi.single l (1 : K) : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h l
    simp at this
  have hfc := hasFiniteContent_height q hne
  rw [ratVec_single] at hfc
  exact adelicNorm_smul hfc u

theorem escape : Escape := by
  intro K _ _ n r hr hrn D Q T hD hQ hT
  have hn : 0 < n := by omega
  set l : Fin n := ⟨n - 1, by omega⟩ with hldef
  have hl : r ≤ (l : ℕ) := by simp only [hldef]; omega
  set e : Fin n → K := Pi.single l 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h l
    simp [he] at this
  obtain ⟨ε, hε, hheight⟩ := exists_pos_le_height hT
  obtain ⟨P, hP, hvec⟩ := exists_adelicNorm_vecMul_le_mul hQ
  set A : ℝ := adelicNorm (ratVec e) with hA
  have hA1 : 1 ≤ A := one_le_adelicNorm_ratVec he0
  have hcont : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨_, B, -, -, hB⟩ := exists_pos_bounds hT hcont fun g _ => (detModule K n g).2
  obtain ⟨b, _, hb, -, hb'⟩ := exists_pos_bounds hQ hcont fun g _ => (detModule K n g).2
  set c : ℝ := ε / (P * A) with hc
  have hPA : 0 < P * A := mul_pos hP (by linarith)
  have hcpos : 0 < c := div_pos hε hPA
  set d := Module.finrank ℚ K with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have htend : Tendsto (fun t : ℝ => Real.exp (r * t) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd0).comp
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr0))
  filter_upwards [htend.eventually_gt_atTop (B / (c ^ n * b))] with t ht γ hγ X _ q hq hmem
  obtain ⟨γ₀, u, rfl⟩ := exists_eq_of_mem_lat hγ
  set E : ℝ := (ideleModule K u : ℝ) with hE
  have hEpos : 0 < E := (ideleModule K u).2
  set τ := AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q) with hτ
  have hx0 : (e ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≠ 0 := by
    intro h
    apply he0
    have h2 := congrArg (· ᵥ* ((γ₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using h2
  have h1 : ε ≤ E * (P * A) := by
    have h2 := hheight τ hmem _ hx0
    rw [hτ, height_eq hl] at h2
    have h3 := hvec q hq (ratVec e) (hasFiniteContent_ratVec he0)
    rw [he, ratVec_single] at h3
    rw [hA, he, ratVec_single]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hEpos.le)
  have hcE : c ≤ E := (div_le_iff₀ hPA).2 h1
  have hdet : (detModule K n τ : ℝ) = E ^ n * (Real.exp (r * t) ^ d * (detModule K n q : ℝ)) := by
    rw [hτ, map_mul, map_mul, map_mul, map_mul, detModule_diagonal, detModule_unipGL, one_mul,
      one_mul, Positive.val_mul, Positive.val_mul, detModule_scalarUnits, detModule_aR hrn.le]
  have hle := (hB τ hmem).2
  rw [hdet] at hle
  have hbq := (hb' q hq).1
  have hexp : 0 < Real.exp (r * t) ^ d := pow_pos (Real.exp_pos _) _
  have hcn : 0 < c ^ n := pow_pos hcpos _
  have h4 : c ^ n * (Real.exp (r * t) ^ d * b) ≤ B := by
    refine le_trans ?_ hle
    exact mul_le_mul (pow_le_pow_left₀ hcpos.le hcE n)
      (mul_le_mul_of_nonneg_left hbq hexp.le) (mul_pos hexp hb).le (pow_pos hEpos _).le
  rw [div_lt_iff₀ (mul_pos hcn hb)] at ht
  nlinarith [ht, h4]

end GlobalTheory.CompanionTheory.SiegelEscape

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulFil
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

universe w v u

namespace GlobalTheory.CompanionTheory.BetaFil

open CrystallineSemistableComparison.CH CrystallineSemistableComparison.CechClassBoundaries

theorem img_smul {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F : C ⥤ ModuleCat.{w} R}
    (S S' : SubF F) (a : R) (h : ∀ T, ∀ x ∈ S.S T, a • x ∈ S'.S T) (j : ℕ) :
    ∀ x ∈ S.img j, a • x ∈ S'.img j := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨c, hc, rfl⟩ := clsSurj y
  let α : S.fn ⟶ S'.fn :=
    { app := fun T => ModuleCat.ofHom ((a • (LinearMap.id : F.obj T →ₗ[R] F.obj T)).restrict fun x hx => h T x hx)
      naturality := fun T T' φ => by
        ext x
        exact Subtype.ext (map_smul (F.map φ).hom a x.1).symm }
  have hc' := cyc (Mor.ofNatTrans α).hom c hc
  have hc'' := cyc S'.inc.hom _ hc'
  have hs := cyc S.inc.hom c hc
  refine ⟨(Mor.ofNatTrans α).pull j ((cx S.fn).cls c hc), ?_⟩
  change S'.inc.hom.mapH j ((Mor.ofNatTrans α).hom.mapH j ((cx S.fn).cls c hc)) =
    a • S.inc.hom.mapH j ((cx S.fn).cls c hc)
  rw [mapH_cls' _ c hc hc', mapH_cls' _ _ hc' hc'', mapH_cls' _ c hc hs,
    ← cls_smul a _ hs (by rw [map_smul, hs, smul_zero])]
  rfl

theorem pdS_smul {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (r j : ℕ) (a : Λ)
    (ha : c a ∈ b.I) : ∀ x ∈ (CrystallineSemistableComparison.B.pdS L c r).img j, a • x ∈ (CrystallineSemistableComparison.B.pdS L c (r + 1)).img j :=
  img_smul _ _ a (fun T _ hx => CrystallineSemistableComparison.B.mul_pdPow L T r (T.i_mem ha) hx) j

set_option maxHeartbeats 1000000 in

theorem smul_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n r j : ℕ) (a : Acris l), (base l).cris n a ∈ JJ k (base l) n → ∀ x ∈ HcFil F κ k n r j, a • x ∈ HcFil F κ k n (r + 1) j := by
  intro l _ O _ F κ k n r j a ha x hx
  exact @pdS_smul (bs l k n) (Lc F κ k n) (Acris l) _ ((base l).cris n) r j a ha x hx

end GlobalTheory.CompanionTheory.BetaFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportClosureRegularTraceStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_closure_regular_trace : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 → ∀ w : Pl F, ∀ a ∈ SuppAt d β {w},
  a ∈ closure {a' | a' ∈ SuppAt d β {w} ∧ (qmap (proj w) a').re ^ 2 ≠ 1} := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.RegClosure.reg_closure | exact GlobalTheory.CompanionTheory.PlaneSA.RegClosure.reg_closure | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.RegClosure.reg_closure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoSetLIntegralDiffCompactCovering
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.MeasureTails

theorem tendsto_setLIntegral_diff_compactCovering
    {α : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α]
    [SigmaCompactSpace α] (μ : Measure α) (F : Set α) (h : α → ℝ≥0∞)
    (hfin : ∫⁻ x in F, h x ∂μ < ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ x in F \ compactCovering α k, h x ∂μ) atTop (𝓝 0) := by
  set m : Measure α := (μ.restrict F).withDensity h with hm
  have hmeas : ∀ k : ℕ, MeasurableSet (compactCovering α k)ᶜ := fun k =>
    ((isCompact_compactCovering α k).isClosed.measurableSet).compl
  have hrew : ∀ k : ℕ, ∫⁻ x in F \ compactCovering α k, h x ∂μ = m (compactCovering α k)ᶜ := by
    intro k
    rw [hm, withDensity_apply h (hmeas k), Measure.restrict_restrict (hmeas k), Set.diff_eq,
      Set.inter_comm]
  have huniv : m Set.univ < ⊤ := by
    rw [hm, withDensity_apply h MeasurableSet.univ, Measure.restrict_univ]
    exact hfin
  have hanti : Antitone (fun k : ℕ => (compactCovering α k)ᶜ) := fun i j hij =>
    Set.compl_subset_compl.mpr (compactCovering_subset α hij)
  have hinter : ⋂ k : ℕ, (compactCovering α k)ᶜ = ∅ := by
    rw [← Set.compl_iUnion, iUnion_compactCovering, Set.compl_univ]
  have hne : ∃ k : ℕ, m (compactCovering α k)ᶜ ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top huniv.ne (measure_mono (Set.subset_univ _))⟩
  have key := tendsto_measure_iInter_atTop (μ := m)
    (fun k => (hmeas k).nullMeasurableSet) hanti hne
  rw [hinter, measure_empty] at key
  simp only [hrew]
  exact key

end GlobalTheory.CompanionTheory.MeasureTails
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimage
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mem_ker_smul_top_of_one_tmul_eq_zero {A A' M : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    (hs : Function.Surjective (algebraMap A A')) [AddCommGroup M] [Module A M] (x : M)
    (h : (1 : A') ⊗ₜ[A] x = 0) :
    x ∈ (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M) := by
  have ex : Function.Exact (Submodule.subtype (RingHom.ker (algebraMap A A')))
      (Algebra.linearMap A A') := fun a => by
    constructor
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2
  have hs' : Function.Surjective (Algebra.linearMap A A') := hs
  have ex2 := rTensor_exact M ex hs'
  have h0 : LinearMap.rTensor M (Algebra.linearMap A A') ((1 : A) ⊗ₜ[A] x) = 0 := by
    simpa using h
  obtain ⟨z, hz⟩ := (ex2 _).1 h0
  have key : ∀ z : (RingHom.ker (algebraMap A A')) ⊗[A] M,
      TensorProduct.lid A M (LinearMap.rTensor M
        (Submodule.subtype (RingHom.ker (algebraMap A A'))) z) ∈
        (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using add_mem ha hb
    | tmul a m => simpa using Submodule.smul_mem_smul a.2 Submodule.mem_top
  have := key z
  rw [hz] at this
  simpa using this

theorem cst_comp_spec {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (q : R →+* A) (V : X.Opens) (r : R) :
    cst (f ≫ Spec.map (CommRingCat.ofHom q)) V r = cst f V (q r) := by
  have := appLE_cst (f := f ≫ Spec.map (CommRingCat.ofHom q)) (f' := f) (π := 𝟙 X) (g := q)
    (by simp) (V := V) (V' := V) le_rfl r
  have e : (𝟙 X : X ⟶ X).appLE V V le_rfl = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
    exact X.presheaf.map_id _
  rw [e] at this
  exact this

theorem pull_surjective_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) {X X' : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of A)}
    {f' : X' ⟶ Spec (CommRingCat.of A')} {π : X' ⟶ X}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) {M : LB X} (hM : M.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (SecOn.pullLE M π V _ le_rfl) ∧
      ∀ s : SecOnR f M V, SecOn.pullLE M π V _ le_rfl ((SecOnR.of f M V).symm s) = 0 →
        s ∈ (RingHom.ker g) • (⊤ : Submodule A (SecOnR f M V)) := by
  letI := g.toAlgebra
  have hb := SecOnR.baseChangeHom_bijective (R := A) (R' := A') hM H hV rfl
  constructor
  · intro y
    obtain ⟨z, hz⟩ := hb.2 y
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective A (SecOnR f M V) A' hg z
    refine ⟨x, ?_⟩
    have h := (SecOnR.baseChangeHom_tmul (R := A) (R' := A') H.w le_rfl 1 x).symm.trans hz
    rw [one_smul] at h
    exact h
  · intro s hs
    refine mem_ker_smul_top_of_one_tmul_eq_zero hg s (hb.1 ?_)
    rw [map_zero, SecOnR.baseChangeHom_tmul, one_smul]
    exact hs

theorem mem_smul_top_of_comp {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (q : R →+* A) (M : LB X) (V : X.Opens) (J : Ideal A)
    (K : Ideal R) (hK : ∀ a ∈ J, ∃ r ∈ K, q r = a) (s : SecOnR f M V)
    (hs : s ∈ J • (⊤ : Submodule A (SecOnR f M V))) :
    SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm s) ∈
      K • (⊤ : Submodule R (SecOnR (f ≫ Spec.map (CommRingCat.ofHom q)) M V)) := by
  induction hs using Submodule.smul_induction_on' with
  | smul a ha m _ =>
    obtain ⟨r, hr, rfl⟩ := hK a ha
    have e : SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V
        ((SecOnR.of f M V).symm (q r • m)) =
        r • SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm m) := by
      rw [SecOnR.smul_def r, cst_comp_spec]
      rfl
    rw [e]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  | add x _ y _ hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

theorem redL_surjective_ker : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V'), IsAffineOpen V → Function.Surjective (redL I Y β hβ L w hL e V V' h.ge) ∧ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) = I ^ (e + 1) • ⊤ := by
  intro R _ I Y β hβ L w hL e V V' h hV
  subst h
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (Nat.le_succ (e + 1))
  have hq : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  obtain ⟨h1, h2⟩ := pull_surjective_ker (Ideal.Quotient.factor hle) hq (hβ e) (hL (e + 1)).1 hV
  let E := SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 (β e ⁻¹ᵁ V))
  have hred (s) : redL I Y β hβ L w hL e V _ le_rfl s =
      E.symm (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V _ le_rfl s) := rfl
  refine ⟨fun y => ?_, le_antisymm (fun s hs => ?_) (Submodule.smul_le.2 fun r hr s _ => ?_)⟩
  · obtain ⟨x, hx⟩ := h1 (E y)
    exact ⟨x, (hred x).trans ((E.symm_apply_eq).2 hx)⟩
  · have hs0 := (E.symm.map_eq_zero_iff).1 ((hred s).symm.trans (LinearMap.mem_ker.1 hs))
    refine mem_smul_top_of_comp (Y (e + 1)).hom (Ideal.Quotient.mk (I ^ (e + 1 + 1))) (L (e + 1)) V
      (RingHom.ker (Ideal.Quotient.factor hle)) (I ^ (e + 1)) (fun a ha => ?_) s (h2 s hs0)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨r, ?_, rfl⟩
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact ha
  · rw [LinearMap.mem_ker, map_smul, SecOnR.smul_def]
    have e0 : cst (toR I Y e) (β e ⁻¹ᵁ V) r = 0 := by
      rw [toR, cst_comp_spec, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
    rw [e0, zero_smul]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutes
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem pullLE_oneOn_eq_congr {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y}
    (v : LB.Iso N (N'.pull β)) (hL : (pw N 0).IsLB) (hM : ((pw N' 0).pull β).IsLB)
    (hw : (pullPow v 0).IsGen) (V : Y.Opens) (V' : X.Opens) (e : V' ≤ β ⁻¹ᵁ V) :
    SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V) =
      SecOn.congr hL hM (pullPow v 0) hw V' (oneOn N rfl V') := by
  refine GlobalTheory.LB.sec_ext_of_cover hL.cover fun p q => ?_
  have h := SecOn.coord_congr hL hM (pullPow v 0) hw (oneOn N rfl V') p q
    (O := V' ⊓ ((pw N' 0).pull β).U p ⊓ (pw N 0).U q) inf_le_left
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right)
  have c1 : GlobalTheory.LB.coord (SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V)) p = 1 := by
    rw [SecOn.coord_pullLE]
    exact map_one _
  have c2 : GlobalTheory.LB.coord (oneOn N (rfl : (0 : ℤ) = 0) V') q = 1 := rfl
  have c3 : (show Γ(X, ((pw N' 0).pull β).U p ⊓ (pw N 0).U q)ˣ from (pullPow v 0).s (p, q)) = 1 :=
    zpow_zero _
  rw [c2, c3] at h
  rw [c1]
  refine Eq.trans ?_ h.symm
  simp

theorem red_oneOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (h : a = 0) (e : ℕ) (S : Finset ι), red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ (oneOn (N (e + 1)) h (D (e + 1) S))) = SecOnR.of _ _ _ (oneOn (N e) h (D e S)) := by
  intro R _ I Y β hβ N v hN ι D hDβ a h e S
  subst h
  simp only [red, redL, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq, SecOnR.pull_of, SecOnR.linEquiv_of]
  exact congrArg (SecOnR.of _ _ _) (pullLE_oneOn_eq_congr (v e) _ _ _ _ _ _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotientStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_envelope_filtration_quotient : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → ∀ (b : ℕ →₀ B) (r : ℕ), r ≤ s → ∀ c : B, (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ⊔ Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) := by
  first | exact @GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit | exact GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit | (intros; apply GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit <;> assumption)
end

