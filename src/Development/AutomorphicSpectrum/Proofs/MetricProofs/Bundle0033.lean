import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeIsometryTransport
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariant
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NonvanishingDense

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjection
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

variable {e n : ℕ}

theorem continuous_comp_emb (σ : Fin n ↪ Fin e) :
    Continuous (fun w : Fin e → ℂ => w ∘ σ) :=
  continuous_pi fun j => continuous_apply (σ j)

theorem analyticAt_comp_emb (σ : Fin n ↪ Fin e) (w : Fin e → ℂ) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => v ∘ σ) w := by
  rw [analyticAt_pi_iff]
  intro j
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (σ j)).analyticAt w

theorem extend_comp_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ g w ∘ σ = g :=
  funext fun j => σ.injective.extend_apply g w j

theorem extend_extend_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ (w ∘ σ) (Function.extend σ g w) = w := by
  funext i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    exact σ.injective.extend_apply _ _ j
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]

theorem analyticAt_extend_emb (σ : Fin n ↪ Fin e) {f : (Fin n → ℂ) → Fin n → ℂ} {w : Fin e → ℂ}
    (hf : AnalyticAt ℂ f (w ∘ σ)) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v) w := by
  rw [analyticAt_pi_iff]
  intro i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v (σ j)) =
        (fun y : Fin n → ℂ => f y j) ∘ (fun v : Fin e → ℂ => v ∘ σ) := by
      funext v
      exact σ.injective.extend_apply _ _ j
    rw [hfun]
    exact AnalyticAt.comp (analyticAt_pi_iff.1 hf j) (analyticAt_comp_emb σ w)
  · have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v i) = fun v => v i := by
      funext v
      exact Function.extend_apply' _ _ _ h
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt w

noncomputable def extendHomeo (σ : Fin n ↪ Fin e)
    (τ : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
    (h₁ : AnalyticOnNhd ℂ τ τ.source) (h₂ : AnalyticOnNhd ℂ τ.symm τ.target) :
    OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) where
  toFun w := Function.extend σ (τ (w ∘ σ)) w
  invFun w := Function.extend σ (τ.symm (w ∘ σ)) w
  source := {w | w ∘ σ ∈ τ.source}
  target := {w | w ∘ σ ∈ τ.target}
  map_source' w hw := by
    show Function.extend σ (τ (w ∘ σ)) w ∘ σ ∈ τ.target
    rw [extend_comp_emb]
    exact τ.map_source hw
  map_target' w hw := by
    show Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ ∈ τ.source
    rw [extend_comp_emb]
    exact τ.map_target hw
  left_inv' w hw := by
    show Function.extend σ (τ.symm (Function.extend σ (τ (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.left_inv hw, extend_extend_emb]
  right_inv' w hw := by
    show Function.extend σ (τ (Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ.symm (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.right_inv hw, extend_extend_emb]
  open_source := τ.open_source.preimage (continuous_comp_emb σ)
  open_target := τ.open_target.preimage (continuous_comp_emb σ)
  continuousOn_toFun := fun w hw =>
    (analyticAt_extend_emb σ (h₁ _ hw)).continuousAt.continuousWithinAt
  continuousOn_invFun := fun w hw =>
    (analyticAt_extend_emb σ (h₂ _ hw)).continuousAt.continuousWithinAt

theorem chart_swap :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ ∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i := by
  intro e n X Z _ _ A Ab pr ψ kb σ ψb hψ hb hpr
  have h₁ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb)
      ((Ab.chart kb).symm.trans ψb).source := by
    intro y hy
    exact (hb kb).1 y hy
  have h₂ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb).symm
      ((Ab.chart kb).symm.trans ψb).target := by
    intro y hy
    exact (hb kb).2 y hy
  have hcomp : ∀ y ∈ ψ.source, ψ y ∘ σ = Ab.chart kb (pr y) := fun y hy =>
    funext fun i => ((hpr y hy).2 i).symm
  let T := extendHomeo σ ((Ab.chart kb).symm.trans ψb) h₁ h₂
  have hTan : ∀ w ∈ T.source, AnalyticAt ℂ T w := fun w hw =>
    analyticAt_extend_emb σ (h₁ _ hw)
  have hTsan : ∀ w ∈ T.target, AnalyticAt ℂ T.symm w := fun w hw =>
    analyticAt_extend_emb σ (h₂ _ hw)
  have hsrc : (ψ.trans T).source = ψ.source ∩ pr ⁻¹' ψb.source := by
    ext y
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      have h3 : ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source := hy'
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source] at h3
      have h4 := h3.2
      simp only [Set.mem_preimage] at h4
      rwa [(Ab.chart kb).left_inv (hpr y hy).1] at h4
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      show ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source]
      refine ⟨(Ab.chart kb).map_source (hpr y hy).1, ?_⟩
      simp only [Set.mem_preimage]
      rwa [(Ab.chart kb).left_inv (hpr y hy).1]
  refine ⟨ψ.trans T, ?_, hsrc, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hy2
      have h := (hψ j).1 y ⟨hy1, hy2.1⟩
      exact AnalyticAt.comp (g := T) (f := ψ ∘ (A.chart j).symm) (hTan _ hy2.2) h
    · rintro z ⟨hz1, hz2⟩
      rw [OpenPartialHomeomorph.trans_target] at hz1
      have h := (hψ j).2 (T.symm z) ⟨hz1.2, hz2⟩
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := T.symm) h (hTsan z hz1.1)
  · intro y hy i
    rw [hsrc] at hy
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) (σ i) = ψb (pr y) i
    rw [σ.injective.extend_apply, hcomp y hy.1]
    show ψb ((Ab.chart kb).symm (Ab.chart kb (pr y))) i = ψb (pr y) i
    rw [(Ab.chart kb).left_inv (hpr y hy.1).1]

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderConjugationStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_weight_invariant_under_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation | exact GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderIsometry
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (g' : ℕ) (Λ' : Type) [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)), IsCMFam σ → φ '' Set.range R.P = Set.range R'.P → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) → (∀ a x, φ (R.B a x) = R'.B a (φ x)) → R'.cuspW σ = R.cuspW σ ∧ R'.lam1 = R.lam1 ∧ (∀ m, R'.HasRank σ m ↔ R.HasRank σ m) ∧ ∃ α : Λ ≃ₗ[𝓞 E] Λ', (∀ v, R'.P (α v) = φ (R.P v)) ∧ ∀ I, IsIsoSub R.form I → R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  first | exact @LevelTowerAlt.riemann_lattice_isometry_transport | exact LevelTowerAlt.riemann_lattice_isometry_transport
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHermLineOfLocalSmooth
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace CExt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth Topology Filter Set
open scoped Manifold

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def colMap (p : (k : K) → ι k) (m : (Σ k, ι k × ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => m ⟨q.1, (q.2, p q.1)⟩

theorem colMap_contDiff (p : (k : K) → ι k) {n : WithTop ℕ∞} : ContDiff ℝ n (colMap p) :=
  contDiff_pi.2 fun q => contDiff_apply ℝ ℂ (⟨q.1, (q.2, p q.1)⟩ : Σ k, ι k × ι k)

theorem sameOrbit_colMap {p : (k : K) → ι k} {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι)
    (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) : SameOrbit (colMap p (prMap z)) z := by
  refine ⟨fun k => (starRingEnd ℂ) (z ⟨k, p k⟩) / (blockSq z k : ℂ), fun k =>
    div_ne_zero ((map_ne_zero _).2 (hp k)) (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne'), ?_⟩
  funext q
  simp only [colMap, prMap]
  ring

theorem prMap_diag_ne_zero {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι) {k : K} {i : ι k}
    (hi : z ⟨k, i⟩ ≠ 0) : prMap z ⟨k, (i, i)⟩ ≠ 0 :=
  div_ne_zero (mul_ne_zero hi ((map_ne_zero _).2 hi))
    (Complex.ofReal_ne_zero.2 (blockSq_pos (hz k)).ne')

theorem ne_zero_of_prMap_diag {z : (Σ k, ι k) → ℂ} {k : K} {i : ι k}
    (h : prMap z ⟨k, (i, i)⟩ ≠ 0) : z ⟨k, i⟩ ≠ 0 := by
  intro h0
  apply h
  simp [prMap, h0]

theorem isClosed_prMap_image {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsClosed (prMap '' mcPts P) := by
  have hA : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hC := (isCompact_unitBlocks (K := K) (ι := ι)).inter_right hA
  have hcont : ContinuousOn (prMap (K := K) (ι := ι)) (unitBlocks K ι ∩
      {z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}) := fun z hz =>
    (prMap_continuousAt (unitBlocks_subset hz.1)).continuousWithinAt
  convert (hC.image_of_continuousOn hcont).isClosed using 1
  ext m
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, hc, hu⟩ := exists_normalize (K := K) (ι := ι) hz.1
    exact ⟨_, ⟨hu, (mcPts_smul hP c hc hz).2⟩, prMap_smul c z hc⟩
  · rintro ⟨z, ⟨hu, hz⟩, rfl⟩
    exact ⟨z, ⟨unitBlocks_subset hu, hz⟩, rfl⟩

theorem exists_smooth_on_matrices {P : Ideal (MRing ι)} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hP : IsMultiHomogIdeal P) (hinv : ∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') :
    ∃ g : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ z ∈ mcPts P, g (prMap z) = u z := by
  have ht : ∀ m : (Σ k, ι k × ι k) → ℂ,
      Convex ℝ {r : ℝ | ∀ z ∈ mcPts P, prMap z = m → r = u z} := by
    intro m x hx y hy a b _ _ hab z hz hzm
    rw [smul_eq_mul, smul_eq_mul, hx z hz hzm, hy z hz hzm, ← add_mul, hab, one_mul]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := (⊤ : ℕ∞))
    (M := (Σ k, ι k × ι k) → ℂ) (F := ℝ) 𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) ht (fun x => by
    by_cases hx : x ∈ prMap '' mcPts P
    · obtain ⟨z₀, hz₀, rfl⟩ := hx
      choose p hp using hz₀.1
      obtain ⟨V, w, hV, hmem, hw, hwu⟩ := hloc (colMap p (prMap z₀))
        (mem_mcPts_of_sameOrbit hP (sameOrbit_colMap hz₀.1 hp) hz₀)
      have hO : IsOpen (colMap p ⁻¹' V ∩ {m | ∀ k, m ⟨k, (p k, p k)⟩ ≠ 0}) := by
        refine (hV.preimage (colMap_contDiff p (n := 0)).continuous).inter ?_
        simp only [setOf_forall]
        exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
      refine ⟨_, hO.mem_nhds ⟨hmem, fun k => prMap_diag_ne_zero hz₀.1 (hp k)⟩, w ∘ colMap p, ?_, ?_⟩
      · exact contMDiffOn_iff_contDiffOn.2
          (hw.comp (colMap_contDiff p).contDiffOn fun y hy => hy.1)
      · rintro y ⟨hy1, hy2⟩ z hz rfl
        have ho := sameOrbit_colMap hz.1 fun k => ne_zero_of_prMap_diag (hy2 k)
        show w (colMap p (prMap z)) = u z
        rw [hwu _ ⟨hy1, mem_mcPts_of_sameOrbit hP ho hz⟩]
        exact hinv z hz _ ho
    · refine ⟨_, (isClosed_prMap_image hP).isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy z hz hzy
      exact absurd ⟨z, hz, hzy⟩ hy)
  exact ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z hz => hg _ z hz rfl⟩

variable (ι) in

def expLine (g : ((Σ k, ι k × ι k) → ℂ) → ℝ) : HermLine ι where
  a := 0
  h z := by
    classical
    exact if z ∈ nzBlocks K ι then Real.exp (g (prMap z)) else 1
  pos z hz := by
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  smul c z hc := by
    classical
    have hiff : (fun p : Σ k, ι k => c p.1 * z p) ∈ nzBlocks K ι ↔ z ∈ nzBlocks K ι := by
      refine forall_congr' fun k => exists_congr fun i => ?_
      simp [hc k]
    simp only [hiff, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, prMap_smul c z hc]

end CExt

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem exists_hermLine_of_local_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (u : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, ∀ z', SameOrbit z' z → u z' = u z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, ι k) → ℂ)) (w : ((Σ k, ι k) → ℂ) → ℝ), IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w V ∧ ∀ z' ∈ V ∩ mcPts P, w z' = u z') → ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ z ∈ mcPts P, Real.log (B.h z) = u z := by
  intro K _ ι _ P u hP hinv hloc
  obtain ⟨g, hg, hgu⟩ := CExt.exists_smooth_on_matrices hP hinv hloc
  refine ⟨CExt.expLine ι g, rfl, ?_, fun z hz => ?_⟩
  · have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)))
        (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.nzBlocks K ι) :=
      Real.contDiff_exp.comp_contDiffOn
        (hg.comp_contDiffOn GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap_contDiffOn)
    refine h1.congr fun z hz => ?_
    exact if_pos hz
  · have h2 : (CExt.expLine ι g).h z = Real.exp (g (GlobalTheory.CompanionTheory.Ar.Flat.PlaceWeightSmooth.prMap z)) :=
      if_pos hz.1
    rw [h2, Real.log_exp, hgu z hz]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSncAdaptedChartAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalForm

theorem holoOn_coord {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (i : Fin e) :
    A.HoloOn ψ.source (fun y => ψ y i) := by
  intro j z hz
  exact (analyticAt_pi_iff.1 ((hψ j).1 z hz)) i

theorem exists_local_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSNC A L s m W → ∀ x, ∃ (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ ∧ x ∈ φ.source ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧ φ x = 0 ∧ φ.source ⊆ L.U x ∧ (∀ i ∈ S, 1 ≤ μ i) ∧ A.HoloOn φ.source v ∧ (∀ y ∈ φ.source, v y ≠ 0) ∧ ∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i := by
  intro e X _ A L s nb m W hsnc x
  obtain ⟨ψ, hψ, hxψ, hψU, σ, hinj, -, u, hu, hu0, hs⟩ := hsnc x
  obtain ⟨c, hc⟩ : ∃ c, c = ψ x := ⟨_, rfl⟩
  have hev : ∀ᶠ z in 𝓝 c, z ∈ ψ.target ∧ ∀ i, c i ≠ 0 → z i ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 c, z ∈ ψ.target := ψ.open_target.mem_nhds (hc ▸ ψ.map_source hxψ)
    refine h1.and ?_
    rw [eventually_all]
    intro i
    by_cases h : c i = 0
    · simp [h]
    · filter_upwards [((continuous_apply i).continuousAt (x := c)).eventually_ne h] with z hz _
      exact hz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hV : IsOpen (ψ.source ∩ ψ ⁻¹' Metric.ball c r) :=
    ψ.continuousOn.isOpen_inter_preimage ψ.open_source Metric.isOpen_ball
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : (3 / r : ℂ) ≠ 0 := by simpa using hrC
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (ψ.restrOpen _ hV).transHomeomorph (pa_aff (3 / r : ℂ) ha c) := ⟨_, rfl⟩
  have hφc : IsCompatChart A φ := hφ ▸ pa_compat_aff A _ (pa_compat_restr A _ hψ _ hV) _ ha _
  have hsrc : ∀ y ∈ φ.source, y ∈ ψ.source ∧ ψ y ∈ Metric.ball c r := by
    intro y hy
    subst hφ
    exact ⟨hy.1, hy.2.2⟩
  have hφapp : ∀ y, φ y = (3 / r : ℂ) • (ψ y - c) := by
    intro y
    subst hφ
    rfl
  have hxφ : x ∈ φ.source := by
    subst hφ
    refine ⟨hxψ, hxψ, ?_⟩
    show ψ x ∈ Metric.ball c r
    rw [← hc]
    exact Metric.mem_ball_self hr
  have htarget : Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target := by
    intro z hz
    subst hφ
    set w : Fin e → ℂ := (3 / r : ℂ)⁻¹ • z + c with hw
    have hwb : w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, hw, add_sub_cancel_right, norm_smul]
      have hz' : ‖z‖ ≤ 2 := by simpa using hz
      have : ‖(3 / r : ℂ)⁻¹‖ = r / 3 := by
        rw [norm_inv, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
        norm_num
      rw [this]
      nlinarith
    have hwT : w ∈ ψ.target := (hball _ hwb).1
    have hmem : w ∈ (ψ.restrOpen _ hV).target :=
      ⟨hwT, ψ.map_target hwT, by simpa [ψ.right_inv hwT] using hwb⟩
    exact hmem

  let g : Fin nb → X → ℂ := fun k y => (σ k).elim 1 (fun i => ψ y i ^ m k)
  have hg : ∀ k y, (match σ k with
      | some i => ψ y i ^ m k
      | none => 1) = g k y := by
    intro k y
    simp only [g]
    cases σ k <;> rfl
  have hgholo : ∀ k, A.HoloOn ψ.source (g k) := by
    intro k j z hz
    simp only [g]
    cases σ k with
    | none => exact analyticAt_const
    | some i => exact (holoOn_coord A ψ hψ i j z hz).pow (m k)
  let K : Finset (Fin nb) := Finset.univ.filter (fun k => ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let S : Finset (Fin e) := Finset.univ.filter (fun i => c i = 0 ∧ ∃ k, σ k = some i ∧ 1 ≤ m k)
  let μ : Fin e → ℕ := fun i => ∑ k, if σ k = some i then m k else 0
  have hμ : ∀ k i, σ k = some i → μ i = m k := by
    intro k i hk
    refine (Finset.sum_eq_single k (fun b _ hb => if_neg fun h => hb (hinj _ _ i h hk))
      (by simp)).trans (if_pos hk)
  have hKS : ∀ y, ∏ k ∈ K, g k y = ∏ i ∈ S, ψ y i ^ μ i := by
    intro y
    refine Finset.prod_bij (fun k hk => Classical.choose (Finset.mem_filter.1 hk).2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2, k, h1, h3⟩
    · intro k hk k' hk' hkk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      obtain ⟨h1', -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk').2
      exact hinj k k' _ h1 (hkk ▸ h1')
    · intro i hi
      obtain ⟨-, h0, k, hk, hm⟩ := Finset.mem_filter.1 hi
      have hkK : k ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hk, h0, hm⟩
      refine ⟨k, hkK, ?_⟩
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hkK).2
      exact Option.some.inj (h1.symm.trans hk)
    · intro k hk
      obtain ⟨h1, -, -⟩ := Classical.choose_spec (Finset.mem_filter.1 hk).2
      have key : ∀ i, σ k = some i → g k y = ψ y i ^ μ i := by
        intro i hi
        simp only [g]
        rw [hi, hμ k i hi]
        rfl
      exact key _ h1
  let T : Finset (Fin nb) := Finset.univ.filter
    (fun k => ¬ ∃ i, σ k = some i ∧ c i = 0 ∧ 1 ≤ m k)
  let C : ℂ := ((r : ℂ) / 3) ^ (∑ i ∈ S, μ i)
  have hC : C ≠ 0 := pow_ne_zero _ (div_ne_zero hrC (by norm_num))
  refine ⟨φ, S, μ, fun y => u y * C * ∏ k ∈ T, g k y, hφc, hxφ, htarget, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφapp, ← hc, sub_self, smul_zero]
  · exact fun y hy => hψU (hsrc y hy).1
  · intro i hi
    obtain ⟨-, -, k, hk, hm⟩ := Finset.mem_filter.1 hi
    rw [hμ k i hk]
    exact hm
  · intro j z hz
    have hz' : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source := ⟨hz.1, (hsrc _ hz.2).1⟩
    exact ((hu j z hz').mul analyticAt_const).mul
      (Finset.analyticAt_fun_prod _ fun k _ => hgholo k j z hz')
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hsrc y hy
    refine mul_ne_zero (mul_ne_zero (hu0 y hy1) hC) (Finset.prod_ne_zero_iff.2 ?_)
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    simp only [g]
    cases hσ : σ k with
    | none => exact one_ne_zero
    | some i =>
      by_cases hm : m k = 0
      · simp [hm]
      · have hci : c i ≠ 0 := fun h0 => hk' ⟨i, hσ, h0, Nat.one_le_iff_ne_zero.2 hm⟩
        exact pow_ne_zero _ ((hball _ hy2).2 i hci)
  · intro y hy
    obtain ⟨hy1, -⟩ := hsrc y hy
    have hcoord : ∀ i ∈ S, ψ y i = ((r : ℂ) / 3) * φ y i := by
      intro i hi
      obtain ⟨-, h0, -⟩ := Finset.mem_filter.1 hi
      rw [hφapp]
      simp only [Pi.smul_apply, Pi.sub_apply, h0, sub_zero, smul_eq_mul]
      field_simp
    have hsplit : ∏ k, g k y = (∏ k ∈ K, g k y) * ∏ k ∈ T, g k y :=
      (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have hmono : ∏ i ∈ S, ψ y i ^ μ i = C * ∏ i ∈ S, φ y i ^ μ i := by
      rw [Finset.prod_congr rfl (fun i hi => by rw [hcoord i hi, mul_pow]),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have h2 : s x y = u y * ∏ k, g k y := by
      rw [hs y hy1]
      congr 1
      exact Finset.prod_congr rfl (fun k _ => hg k y)
    show s x y = u y * C * (∏ k ∈ T, g k y) * ∏ i ∈ S, φ y i ^ μ i
    rw [h2, hsplit, hKS, hmono]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.LocalForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateFormStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_eigencomponent_conjugate_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsIsoSub R.form I → ∀ s : 𝓞 E →+* ℂ, (∀ v ∈ I, ∀ w ∈ I, R.ip (eigComp R.B ((starRingEnd ℂ).comp s) (R.P v)) (eigComp R.B ((starRingEnd ℂ).comp s) (R.P w)) = starRingEnd ℂ (R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P w)))) ∧ ∀ (r : ℕ) (v : Fin r → Λ), (∀ a, v a ∈ I) → LinearIndependent (𝓞 E) v → LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isotropic_eigencomponent_conjugate_form | exact GlobalTheory.CompanionTheory.Relay.isotropic_eigencomponent_conjugate_form | (intros; apply GlobalTheory.CompanionTheory.Relay.isotropic_eigencomponent_conjugate_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositive
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isotropic_sublattice_covolume_positive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → (∃ r v, IsNzFamily I r v) ∧ ∀ r v, IsNzFamily I r v → R.nz σ I = R.nzOf σ I v ∧ 0 < R.nz σ I ∧ r = Module.finrank (𝓞 E) I := by
  first | exact @LevelTowerAlt.isotropic_submodule_nonzero_family | exact LevelTowerAlt.isotropic_submodule_nonzero_family
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCoversComplexPoints
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem resolution_onto_complex_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsArithVar P (e + 1) → ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z :=
  @PositivityTheory.UnitarySelfGeneration.r_onto

end GlobalTheory.CompanionTheory.Ar.Cmp
end

