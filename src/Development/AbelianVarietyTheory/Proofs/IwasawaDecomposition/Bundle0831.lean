import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0823
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0819
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0821
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0820
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0822
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0827
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0829
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0824
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0828
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0739
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedThetaRationalOnGoodCovers

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodFrameOfHolomorphicLatticeFamily
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PeriodFrame.exists_frame_of_latFam : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (d ρ₁ : ℝ) (P τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (Δ : (Fin n → ℂ) → Matrix {j : Fin g // rk ≤ j.val} {j : Fin g // rk ≤ j.val} ℂ), 0 < ρ₁ ∧ ρ₁ ≤ 1 ∧ 0 < d ∧ rk ≤ g ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, IsUnit (P z).det) ∧ (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) ∧ (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (((τ s).map Complex.im).map Complex.ofReal)⁻¹) ∧ ContinuousOn Δ (Metric.ball 0 ρ₁) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, ((Δ z).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).submatrix Subtype.val Subtype.val = Δ (logExp a s)) ∧ (∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 ρ₁) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).mulVec (fun j => (v j : ℂ)) = F (logExp a s)) := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlamc hlam hH htor
  obtain ⟨hDo, hDc, hDan, hDmaps⟩ := GlobalTheory.logDom_chart_props n a
  have hlogc : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) :=
    continuous_iff_continuousAt.2 fun s => (hDan s).continuousAt
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀def
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    by_cases h : (k : ℕ) < a <;> simp [s₀, h]
  obtain ⟨hr, hlamR, hlamD⟩ := GlobalTheory.T.punctPolydiscCover_latticeBasis_real_holomorphic n a g r K lam hK hlamc hlam
  have hlB : ∀ b ∈ logDom n a, IsLatBasis (K (logExp a b)) (lam b) := fun b hb => ⟨hlamR b hb, (hlam b hb).2.2⟩
  have hmemL : ∀ b ∈ logDom n a, ∀ i, lam b i ∈ K (logExp a b) := fun b hb i =>
    ((hlam b hb).2.2 _).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hpre : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hζc : ContinuousOn (fun s => ζ (logExp a s)) (logDom n a) := hζ.continuousOn.comp hlogc.continuousOn hDmaps
  have hcex' : ∀ i : Fin r₀, ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, m j • lam b j := fun i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => ζ (logExp a b) i) s₀ hpre hlamc ((continuous_apply i).comp_continuousOn hζc) hlB
      (fun b hb => hζK _ (hDmaps hb) i) hs₀
  have hcex : ∃ c : Matrix (Fin r₀) (Fin r) ℤ, ∀ i, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, c i j • lam b j := by
    choose c hc using hcex'
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hcex
  have hsh := fun (k : Fin a) (s : Fin n → ℂ) (hs : s ∈ logDom n a) => GlobalTheory.PeriodFrame.shift_mem ha k hs
  have hTex' : ∀ (k : Fin a) (i : Fin r), ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, m j • lam b j := fun k i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i) s₀ hpre hlamc
      ((continuous_apply i).comp_continuousOn
        (hlamc.comp (continuous_add_right _).continuousOn fun b hb => (hsh k b hb).1))
      hlB (fun b hb => by rw [← (hsh k b hb).2]; exact hmemL _ (hsh k b hb).1 i) hs₀
  have hTex : ∃ T : Fin a → Matrix (Fin r) (Fin r) ℤ, ∀ k i, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, T k i j • lam b j := by
    choose T hT using hTex'
    exact ⟨T, hT⟩
  obtain ⟨T, hT⟩ := hTex
  obtain ⟨Hm₀, hH₀h, hH₀p, hH₀l⟩ := hH s₀ hs₀
  have hM₀ := hH₀l s₀ hs₀ rfl
  have hMa : Mᵀ = -M := GlobalTheory.T.hermForm_im_intMatrix_transpose_neg g r Hm₀ (lam s₀) M hH₀h hM₀
  have hMd : M.det ≠ 0 :=
    GlobalTheory.det_ne_zero_of_im_hermForm_eq_int g r Hm₀ (lam s₀) M hH₀p (hlamR s₀ hs₀) (hlam s₀ hs₀).2.1 hM₀
  have hTM : ∀ k, T k * M * (T k)ᵀ = M := by
    intro k
    have h1 := GlobalTheory.T.hermForm_im_intCombination_eq_conj_mul g r r Hm₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (T k) M (fun i => hT k i s₀ hs₀) hM₀
    have h2 := hH₀l _ (hsh k s₀ hs₀).1 (hsh k s₀ hs₀).2
    ext i j
    have h3 := (h1 i j).symm.trans (h2 i j)
    exact_mod_cast h3
  have hcT : ∀ k, c * T k = c := fun k =>
    GlobalTheory.T.coeffMatrix_mul_eq_of_same_intCombinations g r r₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (ζ (logExp a s₀)) c (T k) (hlam s₀ hs₀).1 (fun i => hT k i s₀ hs₀) (fun i => hc i s₀ hs₀)
      (fun i => by rw [← (hsh k s₀ hs₀).2]; exact hc i _ (hsh k s₀ hs₀).1)
  have hcLI : LinearIndependent ℚ (fun i j => (c i j : ℚ)) :=
    GlobalTheory.rowsInd_rat_of_real g r r₀ (lam s₀) (ζ (logExp a s₀)) c (hζi _ (hDmaps hs₀)) (fun i => hc i s₀ hs₀)
  have hco := GlobalTheory.CoisoCount.coisotropic_of_torsion_count r r₀ M c hMd hcLI (by
    intro N hN
    obtain ⟨S, hcard, hS⟩ := htor N hN
    refine ⟨S, by rw [hr]; exact hcard, fun u u' hu => ?_⟩
    obtain ⟨m, hm⟩ := hS u u' hu s₀ hs₀ Hm₀ hM₀
    rw [GlobalTheory.T.hermForm_im_intCombination_dotProduct g r r₀ Hm₀ (lam s₀) (ζ (logExp a s₀)) c M (fun i => hc i s₀ hs₀) hM₀ u u'] at hm
    exact ⟨m, by exact_mod_cast hm⟩)
  obtain ⟨rk, α, φ, β, gm, dl, hrk, hN1, hN2, hN3, hN4, hN5, hN6, hN7⟩ := GlobalTheory.T.exists_rational_symplecticBasis_adapted_coisotropic g r r₀ M c hr hMa hMd hcLI hco
  choose b hb using fun k => GlobalTheory.T.intIsometry_fixing_rowSpace_symplectic_shift g r r₀ rk M (T k) c α φ β hr hMa (hTM k) (hcT k) hN1 hN2 hN3 hN5
  obtain ⟨D, Bz, hD, hBz⟩ := GlobalTheory.T.exists_common_denominator_rat_matrices a g b
  have hBzs : ∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → Bz k j l = 0 := by
    intro k j l h
    have h1 := hBz k j l
    rw [(hb k).1 j l h, mul_zero] at h1
    exact_mod_cast h1
  have hPeq : ∀ s ∈ logDom n a, GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α =
      GlobalTheory.PeriodFrame.combMat (lam s) (α * c.map (Int.cast : ℤ → ℚ)) :=
    fun s hs => GlobalTheory.PeriodFrame.combMat_comb _ _ c α (fun i => hc i s hs)
  have hRie : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧
      IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det ∧ (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef ∧
      (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀᴴ =
        ((D : ℝ) : ℂ) • (((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).map Complex.ofReal)⁻¹ := by
    intro s hs
    obtain ⟨Hm, h1, h2, h3⟩ := hH s hs
    refine ⟨Hm, h3 s hs rfl, ?_⟩
    unfold GlobalTheory.PeriodFrame.perTau
    rw [hPeq s hs]
    exact GlobalTheory.T.riemannRelations_rationalCombinationFrame g r Hm M (lam s) _ φ D hD h1 h2 (hlamR s hs) (h3 s hs rfl) hN1 hN2 hN3
  have hdet : ∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det := fun s hs => by
    obtain ⟨_, _, h, _⟩ := hRie s hs
    exact h
  obtain ⟨hPd, hτd⟩ := GlobalTheory.T.differentiableOn_rationalFrame_periodMatrix_logCover n a g r₀ r ζ lam α φ D hζ hlamD hdet
  have hτsm : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef := fun s hs _ => by
    obtain ⟨_, _, _, h1, h2, _⟩ := hRie s hs
    exact ⟨h1, h2⟩
  have hmono : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∀ k : Fin a,
      GlobalTheory.PeriodFrame.perTau a ζ lam α φ D (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) =
        GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s + (Bz k).map (Int.cast : ℤ → ℂ) := by
    intro s hs _ k
    unfold GlobalTheory.PeriodFrame.perTau
    rw [(hsh k s hs).2, hPeq s hs,
      GlobalTheory.PeriodFrame.combMat_comb (lam (s + _)) (lam s) (T k) φ (fun i => hT k i s hs), (hb k).2]
    exact GlobalTheory.PeriodFrame.combMat_shift (lam s) _ φ (b k) D (Bz k) (hPeq s hs ▸ hdet s hs) (hBz k)
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ :=
    GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha 1 (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D) Bz one_pos le_rfl hτd hτsm hmono
  have hPu : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det :=
    GlobalTheory.T.isUnit_det_rational_combination_frame_closed_ball n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ Bz hD hζ hstd (fun s hs i => hc i s hs) hN7 hN6 hdet hτ₀d
      hBzs hτ₀e
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 1) := fun j l => (hτ₀d j l).continuousOn
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
        (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) =
        (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
          (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) := by
    intro s hs hz
    rw [hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hBzs _ j l (Or.inl hj)]
  refine ⟨rk, (D : ℝ), 1, fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α, GlobalTheory.PeriodFrame.perTau a ζ lam α φ D, Bz,
    fun z => (τ₀ z).submatrix Subtype.val Subtype.val, one_pos, le_rfl, by exact_mod_cast hD, hrk, hPd, hPu, hτd,
    hτsm, hmono, hBzs, ?_, ?_, ?_, hagree, ?_⟩
  · intro s hs hz Hm hHm
    obtain ⟨Hm', h1, _, _, _, h5⟩ := hRie s hs
    have hHH : Hm = Hm' :=
      GlobalTheory.T.complexMatrix_eq_of_hermForm_im_eq_real_span g r Hm Hm' (lam s) (hlam s hs).2.1 (fun i j => (hHm i j).trans (h1 i j).symm)
    subst hHH
    exact h5
  · exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1
  · refine GlobalTheory.T.posDef_imPart_on_polydisc_of_punctured_cover n a {j : Fin g // rk ≤ j.val} (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g))
      (fun j l => hτ₀d j.1 l.1) ?_
    intro s hs
    rw [← hagree s hs (hDmaps hs)]
    exact (hτsm s hs (hDmaps hs)).2.submatrix Subtype.val_injective
  · exact GlobalTheory.T.not_periodMatrix_intVec_continuous_boundary n a g r₀ r K ζ lam M c α φ rk D hK hζ hζK hζ0 (fun s hs => ⟨hlamR s hs, (hlam s hs).2.2⟩)
      (fun s hs i => hc i s hs) hMa hN3 hN4 hD hdet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBoundOfPrimitiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_bound_of_primitive : (PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, SeriesExistList hL cDep) := by
  first | exact @GlobalTheory.HeightCounting.Up.SeriesStep.sb1l | exact GlobalTheory.HeightCounting.Up.SeriesStep.sb1l | (intros; apply GlobalTheory.HeightCounting.Up.SeriesStep.sb1l <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceLevelsClassesComparisonMaps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.KerOne

theorem levels_cls_cmp_at_served : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg))
        (clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1))
        (up : Formalism.L2.G.Cmp.CmpUp t.cmp (w.tw Z) u v hg Lv),
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ (a a' : Lv.compS j) (L L' : ((Fl u v hg).Pj (j + 1)).Tup),
          ((Fl u v hg).Pj (j + 1)).IsLatTup L → ((Fl u v hg).Pj (j + 1)).IsLatTup L' →
          (clsS j a L = clsS j a' L' ↔ a = a' ∧ ∃ γ : (Lv.levS j a).Γ, L' = (Lv.levS j a).smul γ L)) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ x, ∃ a L, ((Fl u v hg).Pj (j + 1)).IsLatTup L ∧ clsS j a L = x) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → Submodule.span ((w.D Z).gat u v hg).O
          (up.cmpS j '' ((((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).L :
            Set (((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).V)) = Lv.Int (j + 1)) := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨Lv, I, H, hC, hX, hE0⟩ : ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
    by_cases hμ : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0
    · exact GlobalTheory.T.exists_comparisonData_steps_upTo_rank w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
    · exact GlobalTheory.T.comparison_data_steps_non_reference_tuple w hO hF hP Z t Wt nch n Y hmu hQ O hO' hU E hE Fl hfl hw u v hg hμ
  classical
  let S := Formalism.MainNotions.G.CmpJ.stepsMu H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds t.Gt
  let clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1) :=
    fun j a L => if hj : j + 1 ≤ (w.D Z).R.m then
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L)
    else (hE0 j (by omega)).elim a
  have hcls : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) a L, clsS j a L =
      Formalism.MainNotions.G.KAat.castCls (hC j hj) (j + 1) (Formalism.MainNotions.G.KAat.clsOf (S := (I.at' j hj).st) (H.core j hj) a L) :=
    fun j hj a L => dif_pos hj
  refine ⟨Lv, clsS, Formalism.L2.G.Cmp.CmpUp.ofRat S.cmpS S.injS S.ratS, ?_, ?_, ?_⟩
  · intro j hj a a' L L' hL hL'
    rw [hcls j hj, hcls j hj, (Formalism.MainNotions.G.KAat.castCls_inj _ _).eq_iff]
    exact Formalism.MainNotions.G.KAat.clsOf_iff (S := (I.at' j hj).st) (H.core j hj) (hX j hj) a a' L L' hL hL'
  · intro j hj x
    obtain ⟨x0, rfl⟩ := Formalism.MainNotions.G.KAat.castCls_surj (hC j hj) (j + 1) x
    obtain ⟨a, L, hL, e⟩ := Formalism.MainNotions.G.KAat.clsOf_surj (S := (I.at' j hj).st) (H.core j hj) x0
    exact ⟨a, L, hL, (hcls j hj a L).trans (congrArg _ e)⟩
  · intro j hj
    exact S.intS (Formalism.MainNotions.G.CmpJ.descUp H t.Gt) j hj

end GlobalTheory.Mem.Top.KerOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesIntegralUniformPrimePowerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_integral_uniform_prime_power : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  first | exact @GlobalTheory.serInt_outright | exact GlobalTheory.serInt_outright | (intros; apply GlobalTheory.serInt_outright <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedThetaRationalOnGoodCoversStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untwisted_theta_rational_on_good_covers : GlobalTheory.SerStd.UntwRatS := by
  first | exact @GlobalTheory.SerStd.untwRatS | exact GlobalTheory.SerStd.untwRatS | (intros; apply GlobalTheory.SerStd.untwRatS <;> assumption)
end

