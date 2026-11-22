import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0119
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0035
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0112
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0110
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0114
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfFlatTower
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.FlatL
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

theorem colGeR_single (K : Type) [Field K] (d j : ℕ) (hj : 1 ≤ j) :
    colGeR K d j (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) = colGeE K d j := by
  funext i l
  by_cases hl : (l : ℕ) = j
  · by_cases hi : (l : ℕ) = i + 1
    · have hlt : (i : ℕ) < j := by omega
      have hij : (⟨(i : ℕ), hlt⟩ : Fin j) = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
      simp only [colGeR, colGeE]
      rw [dif_pos ⟨hl, hlt⟩, hij]
      simp [hl, hi]
      omega
    · simp only [colGeR, colGeE]
      by_cases hlt : (i : ℕ) < j
      · rw [dif_pos ⟨hl, hlt⟩]
        have hne : (⟨(i : ℕ), hlt⟩ : Fin j) ≠ ⟨j - 1, by omega⟩ := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        simp [hi, Pi.single_eq_of_ne hne]
      · rw [dif_neg (by tauto)]
        simp [hi]
  · simp only [colGeR, colGeE]
    rw [dif_neg (by tauto)]
    have : (j + 1 ≤ (l : ℕ)) ↔ j ≤ (l : ℕ) := by omega
    simp [this]

theorem wh_row_ne_zero (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ) (hj : 1 ≤ j) (hd : j < d) (hχ : ∀ x y, χ (x * y * x⁻¹) = χ y)
    (r : Fin j → K) (hr : r ≠ 0) :
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeE K d j) ψ₀ χ := by
  have hs : (Pi.single (⟨j - 1, by omega⟩ : Fin j) (1 : K) : Fin j → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨j - 1, by omega⟩
    simp at this
  obtain ⟨g, hg⟩ := GlobalTheory.T.GL_transitive_nonzero_vectors K j r _ hr hs
  obtain ⟨h, h1, h2⟩ := GlobalTheory.T.block_embedding_GL_inverse K d j hd.le g
  rw [GlobalTheory.T.whittaker_block_embedding_conj K d j ψ₀ χ g h r hd hχ h1 h2, hg, colGeR_single K d j hj]

theorem wh_step (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (hj : 1 ≤ j) (hd : j < d) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ τ.character =
      ((Fintype.card K : ℂ) ^ j - 1) * wh (colGe d j) (colGeE K d j) ψ₀ τ.character := by
  rw [GlobalTheory.T.whittaker_column_recursion K d j ψ₀ τ.character hd (GlobalTheory.T.pattern_set_card_column_step K d j hd) (GlobalTheory.T.additive_character_sum_orthogonality K j ψ₀ hψ)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin j → K)),
    GlobalTheory.T.whittaker_vanishes_of_radical_sums K d j ψ₀ τ.character (GlobalTheory.T.cuspidal_unipotent_radical_sum_zero K d j τ hj hd hτ), zero_add,
    Finset.sum_congr rfl (fun r hr => wh_row_ne_zero K d j ψ₀ τ.character hj hd
      (fun x y => FDRep.char_conj τ y x) r (Finset.ne_of_mem_erase hr))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  have h1 : 1 ≤ Fintype.card K ^ j := Nat.one_le_pow _ _ Fintype.card_pos
  rw [Nat.cast_sub h1]
  simp

theorem wh_top (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) :
    wh (colGe d d) (colGeE K d d) ψ₀ τ.character = (Module.finrank ℂ τ : ℂ) := by
  classical
  have hset : patSet K (colGe d d) = {1} := by
    ext u
    simp only [patSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      ext i l
      by_cases hil : i = l
      · subst hil; simpa using (h i i).1 rfl
      · have := (h i l).2 hil (fun hc => by have := hc.2; have := l.2; omega)
        simp [this, Matrix.one_apply_ne hil]
    · rintro rfl i l
      exact ⟨fun h => by simp [h], fun h _ => by simp [Matrix.one_apply_ne h]⟩
  have hE : patChar (colGeE K d d) ψ₀ (1 : GL (Fin d) K) = 1 := by
    have : ∀ i l : Fin d, colGeE K d d i l = 0 := by
      intro i l
      simp only [colGeE]
      rw [if_neg]
      rintro ⟨-, h⟩
      have := l.2
      omega
    simp [patChar, this]
  simp only [wh, hset, Set.ncard_singleton, Set.mem_singleton_iff]
  simp [hE, FDRep.char_one]

theorem wh_one_eq (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) :
    wh (colGe d 1) (colGeE K d 1) ψ₀ χ = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ χ := by
  have h1 : colGe d 1 = fun i j : Fin d => i < j := by
    funext i l
    simp only [colGe, eq_iff_iff, and_iff_left_iff_imp]
    intro h
    have : (i : ℕ) < l := h
    omega
  have h2 : colGeE K d 1 = cutE K d 0 := by
    funext i l
    simp only [colGeE, cutE]
    congr 1
    apply propext
    omega
  rw [h1, h2]

theorem wh_prod (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    wh (colGe d k) (colGeE K d k) ψ₀ τ.character =
      wh (colGe d 1) (colGeE K d 1) ψ₀ τ.character * ∏ i ∈ Finset.Ico 1 k, ((Fintype.card K : ℂ) ^ i - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [wh_step K d k ψ₀ τ hψ hτ hk (by omega), ih (by omega), Finset.prod_Ico_succ_top hk]
    ring

theorem cuspWh : ReciprocityTheory.Ty.Fin.St.CuspWh := by
  intro K _ _ _ d ψ₀ τ hψ hτ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [← wh_top K 0 ψ₀ τ]
    have h1 : colGe 0 0 = fun i j : Fin 0 => i < j := by
      funext i; exact i.elim0
    have h2 : colGeE K 0 0 = cutE K 0 0 := by
      funext i; exact i.elim0
    rw [h1, h2]
    simp
  · rw [← wh_top K d ψ₀ τ, wh_prod K d ψ₀ τ hψ hτ d hd le_rfl, wh_one_eq]

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.DensInt

theorem exists_cutoff (V : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] :
    ∃ χ : ℕ → V → ℝ, (∀ k, Continuous (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧ ∀ x, ∀ᶠ k in Filter.atTop, χ k x = 1 := by
  have h : ∀ k : ℕ, ∃ f : C(V, ℝ), Set.EqOn f 1 (compactCovering V k) ∧ Set.EqOn f 0 (∅ : Set V) ∧
      HasCompactSupport f ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := fun k =>
    exists_continuous_one_zero_of_isCompact (isCompact_compactCovering V k) isClosed_empty
      (Set.disjoint_empty _)
  choose f h1 _ h3 h4 using h
  refine ⟨fun k => f k, fun k => (f k).continuous, h3, fun k x => h4 k x, fun x => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_mem_compactCovering x
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  exact h1 k (compactCovering_subset V hk hk₀)

theorem density_limit {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (f : V → Y) (ι : X → Y)
    (B : Set X) (m : X → Measure V)
    (H : ∀ ψ : V → ℂ, Continuous ψ → HasCompactSupport ψ →
      HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B ψ (fun S => ∫ x, ψ x ∂(m S)) ∧ ∀ S, Integrable ψ (m S))
    (φ : V → ℂ) (hφc : Continuous φ) (hφ : Integrable φ μ) (hφS : ∀ S ∈ B, Integrable φ (m S))
    (hD : ContinuousOn (fun S => ∫ x, ‖φ x‖ ∂(m S)) B) (K : Set X) (hK : IsCompact K) (hKB : K ⊆ B) :
    ∫ v in f ⁻¹' (ι '' K), φ v ∂μ = ∫ b in K, (∫ x, φ x ∂(m b)) ∂ν := by
  obtain ⟨χ, hχc, hχs, hχb, hχ1⟩ := exists_cutoff V
  set ψ : ℕ → V → ℂ := fun k x => φ x * (χ k x : ℂ) with hψ
  have hψc : ∀ k, Continuous (ψ k) := fun k =>
    hφc.mul (Complex.continuous_ofReal.comp (hχc k))
  have hψs : ∀ k, HasCompactSupport (ψ k) := fun k => by
    have : HasCompactSupport (fun x => (χ k x : ℂ)) := (hχs k).comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    exact this.mul_left
  have hψn : ∀ k x, ‖ψ k x‖ ≤ ‖φ x‖ := fun k x => by
    simp only [hψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb k x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hχb k x).2
  have hψl : ∀ x, Filter.Tendsto (fun k => ψ k x) Filter.atTop (𝓝 (φ x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 x] with k hk
    simp [hψ, hk]
  have hmeas : ∀ k (ρ : Measure V), AEStronglyMeasurable (ψ k) ρ := fun k ρ =>
    (hψc k).aestronglyMeasurable

  have hL : Filter.Tendsto (fun k => ∫ v in f ⁻¹' (ι '' K), ψ k v ∂μ) Filter.atTop
      (𝓝 (∫ v in f ⁻¹' (ι '' K), φ v ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _) hφ.norm.integrableOn
      (fun k => Filter.Eventually.of_forall (hψn k)) (Filter.Eventually.of_forall hψl)

  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ S ∈ K, ‖∫ x, ‖φ x‖ ∂(m S)‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hD.mono hKB)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hR : Filter.Tendsto (fun k => ∫ b in K, (∫ x, ψ k x ∂(m b)) ∂ν) Filter.atTop
      (𝓝 (∫ b in K, (∫ x, φ x ∂(m b)) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((H _ (hψc k) (hψs k)).1.1.mono hKB).aestronglyMeasurable hKm
    · haveI : IsFiniteMeasure (ν.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := ν)⟩
      exact integrable_const _
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      calc ‖∫ x, ψ k x ∂(m S)‖ ≤ ∫ x, ‖ψ k x‖ ∂(m S) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖φ x‖ ∂(m S) := integral_mono ((H _ (hψc k) (hψs k)).2 S).norm (hφS S (hKB hS)).norm (hψn k)
        _ ≤ ‖∫ x, ‖φ x‖ ∂(m S)‖ := Real.le_norm_self _
        _ ≤ C := hC S hS
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      exact tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _)
        (hφS S (hKB hS)).norm (fun k => Filter.Eventually.of_forall (hψn k))
        (Filter.Eventually.of_forall hψl)
  refine tendsto_nhds_unique hL (hR.congr fun k => ?_)
  exact ((H _ (hψc k) (hψs k)).1.2 K hK hKB).symm

set_option maxHeartbeats 1000000 in

theorem density_identity_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)) (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous φ → Integrable φ μ → (∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)) → ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S)) {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∀ K : Set (HermR (Ainf F) σ n), IsCompact K → K ⊆ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∫ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' K), φ X ∂μ = ∫ S in K, (∫ X, φ X ∂(m S)) ∂ν := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hfib φ hφc hφ hφS hD K hK hKB
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact density_limit μ ν (gramR (Ainf F) σ J) Subtype.val _ m
    (fun ψ h1 h2 => GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram F E σ hσ M J hJ (Ainf F) hR n μ ν m hμ hν hfib ψ h1 h2)
    φ hφc hφ hφS hD K hK hKB

end GlobalTheory.CompanionTheory.SW.DensInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvMemOf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

universe w

variable {R : Type} [CommRing R]

structure DFil (K : DCx.{w} R) where
  L : ℤ → ∀ p q, Submodule R (K.X p q)
  mem_h : ∀ r p q x, x ∈ L r p q → K.dh p q x ∈ L r (p + 1) q
  mem_v : ∀ r p q x, x ∈ L r p q → K.dv p q x ∈ L r p (q + 1)
  anti : ∀ {r r' : ℤ}, r ≤ r' → ∀ p q, L r' p q ≤ L r p q

def DFil.Ex {K : DCx.{w} R} (F : DFil K) (r : ℤ) (p : ℕ) : ℕ → Prop
  | 0 => ∀ x ∈ F.L r p 0, K.dv p 0 x ∈ F.L (r + 1) p 1 → x ∈ F.L (r + 1) p 0
  | q + 1 => ∀ x ∈ F.L r p (q + 1), K.dv p (q + 1) x ∈ F.L (r + 1) p (q + 2) →
      ∃ v ∈ F.L r p q, x - K.dv p q v ∈ F.L (r + 1) p (q + 1)

variable {K : DCx.{w} R} (F : DFil K)

theorem sgl_mem {r : ℤ} {p q : ℕ} {x : K.X p q} (hx : x ∈ F.L r p q) (a b : ℕ) : K.sgl p q x a b ∈ F.L r a b := by
  by_cases h : a = p ∧ b = q
  · obtain ⟨rfl, rfl⟩ := h
    rwa [K.sgl_self]
  · rw [K.sgl_ne x (by omega)]
    exact zero_mem _

theorem dv_mem_of {r : ℤ} {e q : ℕ} (y : ∀ p q, K.X p q) (h1 : K.D y e (q + 1) ∈ F.L r e (q + 1))
    (h2 : ∀ e', e = e' + 1 → y e' (q + 1) ∈ F.L r e' (q + 1)) : K.dv e q (y e q) ∈ F.L r e (q + 1) := by
  have h3 : K.Dh y e (q + 1) ∈ F.L r e (q + 1) := by
    cases e with
    | zero => exact zero_mem _
    | succ e => exact F.mem_h _ _ _ _ (h2 e rfl)
  rw [K.D_apply] at h1
  have h4 : (-1 : ℤ) ^ e • K.dv e q (y e q) ∈ F.L r e (q + 1) := (Submodule.add_mem_iff_right _ h3).1 h1
  rcases neg_one_pow_eq_or ℤ e with h | h <;> rw [h] at h4 <;> simpa using h4

theorem kill (r : ℤ) (m : ℕ) (y : ∀ p q, K.X p q) (hy : y ∈ K.T (m + 1)) (hyL : ∀ p q, y p q ∈ F.L r p q) :
    ∀ e : ℕ, (∀ p q, p < e → K.D y p q ∈ F.L (r + 1) p q) → (∀ p q, p < e → p + q = m + 1 → F.Ex r p q) →
      ∃ w ∈ K.T m, (∀ p q, e ≤ p → w p q = 0) ∧ (∀ p q, (y - K.D w) p q ∈ F.L r p q) ∧
        ∀ p q, p < e → (y - K.D w) p q ∈ F.L (r + 1) p q := by
  intro e
  induction e with
  | zero =>
    intro _ _
    refine ⟨0, zero_mem _, fun _ _ _ => rfl, fun p q => ?_, fun p q h => absurd h (by omega)⟩
    simpa using hyL p q
  | succ e ih =>
    intro hD hE
    obtain ⟨w, hwT, hw0, hwL, hwL'⟩ := ih (fun p q hp => hD p q (by omega)) (fun p q hp => hE p q (by omega))
    have hyT : y - K.D w ∈ K.T (m + 1) := sub_mem hy (K.D_mem m w hwT)
    have hDy : K.D (y - K.D w) = K.D y := by rw [map_sub, K.DD, sub_zero]
    generalize hy' : y - K.D w = y' at hyT hDy hwL hwL'
    by_cases he : e ≤ m + 1
    · obtain ⟨q, hq⟩ : ∃ q, e + q = m + 1 := ⟨m + 1 - e, by omega⟩
      have hx : K.dv e q (y' e q) ∈ F.L (r + 1) e (q + 1) :=
        dv_mem_of F y' (by rw [hDy]; exact hD e (q + 1) (by omega)) (fun e' h => hwL' e' (q + 1) (by omega))
      have hEx := hE e q (by omega) hq
      cases q with
      | zero =>
        have hx0 : y' e 0 ∈ F.L (r + 1) e 0 := hEx _ (hwL e 0) hx
        refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
        rw [hy']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
        · exact hwL' p q hp
        · by_cases hq0 : q = 0
          · subst hq0; exact hx0
          · rw [hyT p q (by omega)]; exact zero_mem _
      | succ q =>
        obtain ⟨v, hv, hxv⟩ := hEx _ (hwL e (q + 1)) hx
        have hDu : K.D ((-1 : ℤ) ^ e • K.sgl e q v) =
            (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) + K.sgl e (q + 1) (K.dv e q v) := by
          rw [map_zsmul, K.D_sgl, smul_add, smul_smul, ← pow_add, ← two_mul, pow_mul]
          simp
        have hval : ∀ p q', (y - K.D (w + (-1 : ℤ) ^ e • K.sgl e q v)) p q' =
            y' p q' - (-1 : ℤ) ^ e • K.sgl (e + 1) q (K.dh e q v) p q' - K.sgl e (q + 1) (K.dv e q v) p q' := by
          intro p q'
          rw [map_add, hDu, ← sub_sub, hy']
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          abel
        refine ⟨w + (-1 : ℤ) ^ e • K.sgl e q v, add_mem hwT (?_), fun p q' h => ?_, fun p q' => ?_, fun p q' hp => ?_⟩
        · refine (K.T m).smul_of_tower_mem _ ?_
          intro a b hab
          exact K.sgl_ne v (by omega)
        · simp only [Pi.add_apply, Pi.smul_apply]
          rw [hw0 p q' (by omega), K.sgl_ne v (Or.inl (by omega))]
          simp
        · rw [hval]
          exact sub_mem (sub_mem (hwL p q') ((F.L r p q').smul_of_tower_mem _ (sgl_mem F (F.mem_h _ _ _ _ hv) p q')))
            (sgl_mem F (F.mem_v _ _ _ _ hv) p q')
        · rw [hval]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
          · rw [K.sgl_ne _ (Or.inl (by omega)), K.sgl_ne _ (Or.inl (by omega))]
            simpa using hwL' p q' hp
          · rw [K.sgl_ne _ (Or.inl (by omega))]
            by_cases hq0 : q' = q + 1
            · subst hq0
              rw [K.sgl_self]
              simpa using hxv
            · rw [K.sgl_ne _ (Or.inr hq0), hyT p q' (by omega)]
              simp
    · refine ⟨w, hwT, fun p q h => hw0 p q (by omega), by rw [hy']; exact hwL, fun p q hp => ?_⟩
      rw [hy']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact hwL' p q hp
      · rw [hyT p q (by omega)]; exact zero_mem _

theorem stair_up (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) (r : ℕ) (hr : r ≤ n) :
    ∃ y ∈ K.T (2 * n + 1), K.D y = K.sgl (n + 1) (n + 1) P ∧ ∀ p q, y p q ∈ F.L (r : ℤ) p q := by
  induction r with
  | zero =>
    refine ⟨y0, hy0, hD, fun p q => ?_⟩
    rw [Nat.cast_zero, hTop]
    trivial
  | succ r ih =>
    obtain ⟨y, hyT, hDy, hyL⟩ := ih (by omega)
    have hPr : P ∈ F.L ((r : ℤ) + 1) (n + 1) (n + 1) := F.anti (by omega) _ _ hP
    obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (r : ℤ) (2 * n) y hyT hyL (n + 2)
      (fun p q _ => by rw [hDy]; exact sgl_mem F hPr p q)
      (fun p q hp hq => hE r p q (by omega))
    refine ⟨y - K.D w, sub_mem hyT (K.D_mem _ w hwT), by rw [map_sub, K.DD, sub_zero, hDy], fun p q => ?_⟩
    rw [Nat.cast_succ]
    by_cases hp : p < n + 2
    · exact hwL' p q hp
    · have := hV p q (by omega)
      rw [Subsingleton.elim ((y - K.D w) p q) 0]
      exact zero_mem _

theorem stair (n : ℕ) (hTop : ∀ p q, F.L 0 p q = ⊤) (hV : ∀ p q, n + 1 < p → Subsingleton (K.X p q))
    (hE : ∀ (r : ℕ) p q, q ≠ r → F.Ex (r : ℤ) p q) (P : K.X (n + 1) (n + 1)) (hP : P ∈ F.L ((n : ℤ) + 1) (n + 1) (n + 1))
    (y0 : ∀ p q, K.X p q) (hy0 : y0 ∈ K.T (2 * n + 1)) (hD : K.D y0 = K.sgl (n + 1) (n + 1) P) :
    ∃ (ω : K.X n (n + 1)) (f : K.X (n + 1) n), ω ∈ F.L ((n : ℤ) + 1) n (n + 1) ∧
      K.dv n (n + 1) ω ∈ F.L ((n : ℤ) + 1 + 1) n (n + 2) ∧ f ∈ F.L (n : ℤ) (n + 1) n ∧
      P = K.dh n (n + 1) ω + (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n f := by
  obtain ⟨y, hyT, hDy, hyL⟩ := stair_up F n hTop hV hE P hP y0 hy0 hD n le_rfl

  obtain ⟨w, hwT, -, hwL, hwL'⟩ := kill F (n : ℤ) (2 * n) y hyT hyL (n + 1)
    (fun p q _ => by rw [hDy]; exact sgl_mem F hP p q) (fun p q hp hq => hE n p q (by omega))
  have hy1T : y - K.D w ∈ K.T (2 * n + 1) := sub_mem hyT (K.D_mem _ w hwT)
  have hDy1 : K.D (y - K.D w) = K.sgl (n + 1) (n + 1) P := by rw [map_sub, K.DD, sub_zero, hDy]
  generalize y - K.D w = y1 at hy1T hDy1 hwL hwL'

  have htT : y1 - K.sgl (n + 1) n (y1 (n + 1) n) ∈ K.T (2 * n + 1) :=
    sub_mem hy1T fun a b hab => K.sgl_ne _ (by omega)
  have hDt : K.D (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    have := hV (n + 2) n (by omega)
    rw [map_sub, K.D_sgl, hDy1, Subsingleton.elim (K.dh (n + 1) n (y1 (n + 1) n)) 0, map_zero, zero_add, map_sub, map_zsmul]
  have htL : ∀ p q, (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) p q ∈ F.L ((n : ℤ) + 1) p q := by
    intro p q
    rw [Pi.sub_apply, Pi.sub_apply]
    by_cases hp : p < n + 1
    · rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
      exact hwL' p q hp
    · by_cases hp' : p = n + 1
      · subst hp'
        by_cases hq : q = n
        · subst hq
          rw [K.sgl_self, sub_self]
          exact zero_mem _
        · rw [K.sgl_ne _ (Or.inr hq), hy1T _ _ (by omega), sub_zero]
          exact zero_mem _
      · have := hV p q (by omega)
        rw [Subsingleton.elim (y1 p q - K.sgl (n + 1) n (y1 (n + 1) n) p q) 0]
        exact zero_mem _
  have ecast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; rfl
  obtain ⟨w2, hw2T, hw20, hw2L, hw2L'⟩ := kill F ((n : ℤ) + 1) (2 * n) _ htT htL n
    (fun p q hp => by
      rw [hDt, K.sgl_ne _ (Or.inl (by omega))]
      exact zero_mem _)
    (fun p q hp hq => by
      have := hE (n + 1) p q (by omega)
      rwa [ecast] at this)
  have hDt' : K.D ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) =
      K.sgl (n + 1) (n + 1) (P - (-1 : ℤ) ^ (n + 1) • K.dv (n + 1) n (y1 (n + 1) n)) := by
    rw [map_sub, K.DD, sub_zero, hDt]
  have ht0 : ((y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2) (n + 1) n = 0 := by
    have h1 : K.D w2 (n + 1) n = 0 := by
      rw [K.D_apply]
      have h2 : K.Dv w2 (n + 1) n = 0 := by
        cases n with
        | zero => rfl
        | succ n =>
          show K.dv (n + 1 + 1) n (w2 (n + 1 + 1) n) = 0
          rw [hw20 _ _ (by omega), map_zero]
      have h3 : K.Dh w2 (n + 1) n = 0 := by
        show K.dh n n (w2 n n) = 0
        rw [hw20 _ _ le_rfl, map_zero]
      rw [h2, h3]; simp
    show (y1 (n + 1) n - K.sgl (n + 1) n (y1 (n + 1) n) (n + 1) n) - K.D w2 (n + 1) n = 0
    rw [h1, K.sgl_self]
    simp
  generalize (y1 - K.sgl (n + 1) n (y1 (n + 1) n)) - K.D w2 = t at hDt' ht0 hw2L hw2L'
  refine ⟨t n (n + 1), y1 (n + 1) n, hw2L _ _, ?_, hwL _ _, ?_⟩
  · refine dv_mem_of F t ?_ (fun e' h => hw2L' e' _ (by omega))
    rw [hDt', K.sgl_ne _ (Or.inl (by omega))]
    exact zero_mem _
  · have h := congrFun (congrFun hDt' (n + 1)) (n + 1)
    rw [K.sgl_self, K.D_apply] at h
    have h2 : K.Dv t (n + 1) (n + 1) = 0 := by
      show K.dv (n + 1) n (t (n + 1) n) = 0
      rw [ht0, map_zero]
    rw [h2, smul_zero, add_zero] at h
    have h3 : K.Dh t (n + 1) (n + 1) = K.dh n (n + 1) (t n (n + 1)) := rfl
    rw [← h3, h]
    abel

end GlobalTheory.CompanionTheory.ConeCech
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerProductCuspidalIsoStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_product_cuspidal_iso : ReciprocityTheory.Ty.Fin.St.IpCuspIso := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.IpIso.main | exact GlobalTheory.CompanionTheory.TyFin.IpIso.main | (intros; apply GlobalTheory.CompanionTheory.TyFin.IpIso.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCosetScaledRiemannSumStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coset_scaled_riemann_sum : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), IsStdInf li → ∀ (ι : Type) [Fintype ι] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun x : latCoset I x0 => φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) ∧ Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : latCoset I x0, φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ * ∫ y, φ y ∂(Measure.pi fun _ => li))) := by
  first | exact @GlobalTheory.CompanionTheory.Equi.lat_sum | exact GlobalTheory.CompanionTheory.Equi.lat_sum | (intros; apply GlobalTheory.CompanionTheory.Equi.lat_sum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfFlatTowerStatement
section
open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lseq_of_flat_tower : ∀ (W : Type) [CommRing W] (l : ℕ) (Kt : ℕ → Cx.{1} W) (ψ : ∀ n, Cx.Hom (Kt n) (quo l (Kt (n + 1)) n) (RingHom.id W)) (hψ : ∀ n j, Function.Bijective ((ψ n).mapH j)), (∀ c, FlatL l c (Kt c)) → (∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j)) → ∀ j, Nonempty (LSeq l (tsys l Kt ψ hψ j) (tsys l Kt ψ hψ (j + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys | exact GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys | (intros; apply GlobalTheory.CompanionTheory.TowFlat.nonempty_lSeq_tsys <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseqStatement
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_limit_of_lseq : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W] (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  first | exact @GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | exact GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | (intros; apply GlobalTheory.CompanionTheory.TowerLim.module_finite_lim <;> assumption)
end

