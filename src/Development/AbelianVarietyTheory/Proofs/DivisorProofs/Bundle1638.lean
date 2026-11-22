import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFunctionTwistBounded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.DotAddRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Pointwise
namespace GlobalTheory.ThetaParsevalInner

theorem setIntegral_eq_zero_of_twist {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant] (G : AddSubgroup V) [Countable G]
    {s : Set V} (hs : IsAddFundamentalDomain G s μ) {h : V → ℂ} (hper : ∀ g ∈ G, ∀ y, h (g + y) = h y)
    {c : V} {a : ℂ} (hc : ∀ y, h (c + y) = a * h y) (ha : a ≠ 1) : ∫ y in s, h y ∂μ = 0 := by
  have ht : IsAddFundamentalDomain G (c +ᵥ s) μ := hs.vadd_of_comm c
  have e1 : ∫ y in s, h y ∂μ = ∫ y in c +ᵥ s, h y ∂μ := hs.setIntegral_eq ht (fun g y => hper g g.2 y)
  have e2 : ∫ y in c +ᵥ s, h y ∂μ = ∫ y in s, h (c + y) ∂μ := by
    have := (measurePreserving_add_left μ c).setIntegral_preimage_emb (measurableEmbedding_addLeft c) h (c +ᵥ s)
    rw [← this]
    congr 2
    ext y
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e3 : ∫ y in s, h (c + y) ∂μ = a * ∫ y in s, h y ∂μ := by
    simp_rw [hc]
    exact integral_const_mul a _
  have : (1 - a) * ∫ y in s, h y ∂μ = 0 := by rw [sub_mul, one_mul, ← e3, ← e2, ← e1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem lintegral_thetaSum_schr_sq : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
      μ 𝓕₁ ≠ ⊤ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ x : (κ → AF F),
      ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
        μ 𝓕₁ * ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 := by
  intro F _ _ ψ hψ κ _ μ hμ 𝓕₁ hF hfin Φ hΦ x
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : Countable F := countable_numberField F
  haveI : IsFiniteMeasure (μ.restrict 𝓕₁) := isFiniteMeasure_restrict.mpr hfin
  haveI := hμ
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hψ
  obtain ⟨emb, hemb⟩ : ∃ emb : (κ → F) → (κ → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (κ → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (κ → F) → (κ → AF F) → ℂ, e = fun ξ y => ψ (emb ξ ⬝ᵥ y) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (κ → AF F) → ℂ, g = fun y => ∑' ξ, a ξ * e ξ y := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have he_norm : ∀ ξ y, ‖e ξ y‖ = 1 := fun ξ y => by rw [he]; exact hnorm _
  have he_cont : ∀ ξ, Continuous (e ξ) := fun ξ => by
    rw [he]; exact hcont.comp (continuous_const.dotProduct continuous_id)
  have hconj : ∀ t, (starRingEnd ℂ) (ψ t) = ψ (-t) := fun t => by
    have h1 : ψ t * (starRingEnd ℂ) (ψ t) = 1 := by rw [Complex.mul_conj', hnorm]; simp
    have h2 : ψ t * ψ (-t) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have h0 : ψ t ≠ 0 := fun h => by simpa [h] using hnorm t
    exact mul_left_cancel₀ h0 (h1.trans h2.symm)
  have hemb_sub : ∀ ξ η, emb (ξ - η) = emb ξ - emb η := by
    intro ξ η; rw [hemb]; funext i; simp [map_sub]
  have he_sub : ∀ ξ η y, e (ξ - η) y = e ξ y * (starRingEnd ℂ) (e η y) := by
    intro ξ η y
    simp only [he]
    rw [hconj, hemb_sub, sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hsum_e : ∀ y, Summable fun ξ => ‖a ξ * e ξ y‖ := fun y => by simpa [norm_mul, he_norm] using hsum
  have hg_bd : ∀ y, ‖g y‖ ≤ ∑' ξ, ‖a ξ‖ := fun y => by
    rw [hg]
    refine (norm_tsum_le_tsum_norm (hsum_e y)).trans (le_of_eq ?_)
    congr 1; funext ξ; rw [norm_mul, he_norm, mul_one]
  have hg_cont : Continuous g := by
    rw [hg]
    exact continuous_tsum (fun ξ => continuous_const.mul (he_cont ξ)) hsum
      (fun ξ y => by rw [norm_mul, he_norm, mul_one])
  have h1 : ∀ y, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ = ‖g y‖ₑ := by
    intro y
    have : GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ) = ψ (⅟2 * (x ⬝ᵥ y)) * g y := by
      rw [hg, ← tsum_mul_left]
      unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
      congr 1; funext ξ
      subst ha he hemb
      simp only [AddChar.map_add_eq_mul]; ring
    rw [this, enorm_mul, ← ofReal_norm_eq_enorm (ψ _), hnorm, ENNReal.ofReal_one, one_mul]
  have hgsq_int : Integrable (fun y => ‖g y‖ ^ 2) (μ.restrict 𝓕₁) :=
    Integrable.of_bound (hg_cont.norm.pow 2).aestronglyMeasurable ((∑' ξ, ‖a ξ‖) ^ 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hg_bd y) 2)
  have lhs : ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
      ENNReal.ofReal (∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgsq_int (ae_of_all _ fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [h1, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hcomp : ∀ y, ((‖g y‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : (κ → F) × (κ → F), a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y := by
    intro y
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    simp only [hg]
    rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm (hsum_e y) (by simpa [norm_mul, he_norm] using hsum)]
    congr 1; funext p
    rw [he_sub, map_mul]; ring
  have hFint : ∀ p : (κ → F) × (κ → F),
      Integrable (fun y => a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y) (μ.restrict 𝓕₁) := fun p =>
    (Integrable.of_bound (he_cont _).aestronglyMeasurable 1 (ae_of_all _ fun y => (he_norm _ _).le)).const_mul _
  have hnormint : ∀ p : (κ → F) × (κ → F),
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ = ‖a p.1‖ * ‖a p.2‖ * μ.real 𝓕₁ := by
    intro p
    simp only [norm_mul, he_norm, RCLike.norm_conj, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun p : (κ → F) × (κ → F) =>
      ∫ y in 𝓕₁, ‖a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y‖ ∂μ := by
    simp_rw [hnormint]
    exact (hsum.mul_of_nonneg hsum (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_right _
  have horth : ∀ ζ : κ → F, ∫ y in 𝓕₁, e ζ y ∂μ = if ζ = 0 then (μ.real 𝓕₁ : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ y, e 0 y = 1 := fun y => by simp [he, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push_neg at h; exact hζ (funext h)
      haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
        refine Function.Surjective.countable (f := fun ρ : κ → F => (⟨emb ρ, ?_⟩ : GlobalTheory.ThetaParseval.ratVec F κ)) ?_
        · exact (GlobalTheory.ThetaParseval.mem_ratVec_iff _).2 ⟨ρ, by rw [hemb]⟩
        · rintro ⟨r, hr⟩
          obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
          exact ⟨ρ, by subst hemb; rfl⟩
      refine setIntegral_eq_zero_of_twist μ (GlobalTheory.ThetaParseval.ratVec F κ) hF (h := e ζ) ?_
        (c := Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0)) (a := ψ s0) ?_ hs0
      · intro r hr y
        obtain ⟨ρ, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff r).1 hr
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        rw [show emb ζ ⬝ᵥ (fun i => algebraMap F (AF F) (ρ i)) = algebraMap F (AF F) (ζ ⬝ᵥ ρ) by
          subst hemb; simp [dotProduct, map_sum, map_mul], htriv, one_mul]
      · intro y
        simp only [he, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  have hFval : ∀ p : (κ → F) × (κ → F), ∫ y in 𝓕₁, a p.1 * (starRingEnd ℂ) (a p.2) * e (p.1 - p.2) y ∂μ =
      if p.1 = p.2 then ((‖a p.1‖ ^ 2 * μ.real 𝓕₁ : ℝ) : ℂ) else 0 := by
    intro p
    rw [integral_const_mul, horth]
    by_cases h : p.1 = p.2
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h, h, Complex.mul_conj']; push_cast; ring
    · rw [if_neg (sub_ne_zero.mpr h), if_neg h, mul_zero]
  have hI : ∫ y in 𝓕₁, ‖g y‖ ^ 2 ∂μ = (∑' ξ, ‖a ξ‖ ^ 2) * μ.real 𝓕₁ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [hcomp]
    rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
    simp_rw [hFval]
    have hinj : Function.Injective (fun ξ : κ → F => (ξ, ξ)) := fun _ _ h => (Prod.ext_iff.1 h).1
    rw [← hinj.tsum_eq]
    · simp only [if_true]
      rw [← tsum_mul_right, Complex.ofReal_tsum]
    · intro p hp
      by_cases h : p.1 = p.2
      · exact ⟨p.1, Prod.ext rfl h⟩
      · exact absurd (if_neg h) hp
  have hsq : Summable fun ξ => ‖a ξ‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ξ => by
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hsum.le_tsum ξ (fun _ _ => norm_nonneg _)) (norm_nonneg _))
      (hsum.mul_left (∑' ξ, ‖a ξ‖))
  rw [lhs, hI, ENNReal.ofReal_mul (tsum_nonneg fun _ => sq_nonneg _), ofReal_measureReal hfin, mul_comm,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsq]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ha, hemb]

end GlobalTheory.ThetaParsevalInner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFiniteIdem
section
noncomputable section

open Matrix GlobalTheory.TorFin Formalism.REAL

namespace GlobalTheory.CentreFin

section Alg
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_mem {k : ℕ} {E : Fin k → Fin k → A} {S : Subalgebra ℂ A} (h : ∀ a b, E a b ∈ S) (u : ℂ) : qdet E u ∈ S := by
  unfold qdet qminor
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem commute_qdet {k : ℕ} {E : Fin k → Fin k → A} {x : A} (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) :=
  ((Subalgebra.mem_centralizer_iff ℂ).1 (qdet_mem (S := Subalgebra.centralizer ℂ {x})
    (fun a b => (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact h a b) u) x rfl)

theorem exists_coef {k : ℕ} (E : Fin k → Fin k → A) (s : ℂ) {B : Subalgebra ℂ A} (hB : ∀ u, qdet E u ∈ B) :
    ∃ c : ℕ → A, c k = 1 ∧ (∀ j ≤ k, c j ∈ B) ∧ (∀ u, qdet E (u - s) = ∑ j ∈ Finset.range (k + 1), u ^ j • c j) ∧
      (∑ i, E i i = 0 ∨ ∃ j ≤ k, ∃ t : ℂ, ∑ i, E i i = c j + t • (1 : A)) := by
  cases k with
  | zero => exact ⟨fun _ => 1, rfl, fun _ _ => one_mem _, fun u => by simp [qdet, qminor], Or.inl (by simp)⟩
  | succ m =>
    obtain ⟨c, t, h1, h2, h3⟩ := GlobalTheory.T.shifted_capelli_determinant_subleading_coeff_trace A m E s
    refine ⟨c, h1, fun j hj => ?_, h3, Or.inr ⟨m, m.le_succ, -t, by rw [h2, neg_smul, add_neg_cancel_right]⟩⟩
    exact GlobalTheory.coeff_mem_of_poly_values_mem A (Subalgebra.toSubmodule B) _ c (fun u => h3 u ▸ hB _) j (Nat.lt_succ_of_le hj)

end Alg

section Loc
variable {n : ℕ} {J p q : Matrix (Fin n) (Fin n) ℂ}

def nilPQ (p q : Matrix (Fin n) (Fin n) ℂ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | ∃ A B, Y = p * A * (1 - p) + (1 - q) * B * q}
  add_mem' := fun ⟨A, B, e⟩ ⟨A', B', e'⟩ => ⟨A + A', B + B', by rw [e, e']; noncomm_ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := fun c _ ⟨A, B, e⟩ => ⟨c • A, c • B, by rw [e]; simp⟩

end Loc

end GlobalTheory.CentreFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalQuotientTransitionCocycle
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cocycle_local_quotient_transition : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) →
    (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) →
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    ∀ (j k l : 𝒰.I₀) (T : Scheme.{0}) (x : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k))
      (y : T ⟶ pullback ((B k).hom ≫ 𝒰.f k) (𝒰.f l)) (z : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f l)),
      x ≫ b j k = y ≫ pullback.fst _ _ → x ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ → y ≫ b k l = z ≫ b j l := by
  intro S 𝒰 A H _ _ i B q b hfl hsu hqc hb hchar j k l T x y z hxy hxz
  let κ : pullback (x ≫ pullback.fst _ _) (q j).left ⟶ T := pullback.fst _ _
  let α : pullback (x ≫ pullback.fst _ _) (q j).left ⟶ pullback A.hom (𝒰.f j) := pullback.snd _ _
  have hκα : κ ≫ x ≫ pullback.fst _ _ = α ≫ (q j).left := by
    simpa [κ, α, Category.assoc] using pullback.condition (f := x ≫ pullback.fst _ _) (g := (q j).left)
  haveI : Flat κ := by dsimp [κ]; infer_instance
  haveI : Surjective κ := by dsimp [κ]; infer_instance
  haveI : QuasiCompact κ := by dsimp [κ]; infer_instance
  haveI : Epi κ := Flat.epi_of_flat_of_surjective _
  have hqj : (q j).left ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := by
    simpa using Over.w (q j)
  have ha : (α ≫ pullback.fst _ _) ≫ A.hom = κ ≫ x ≫ pullback.fst _ _ ≫ (B j).hom ≫ 𝒰.f j := by
    simp only [Category.assoc]
    rw [pullback.condition, ← reassoc_of% hqj, ← reassoc_of% hκα]
  have hak : (α ≫ pullback.fst _ _) ≫ A.hom = (κ ≫ x ≫ pullback.snd _ _) ≫ 𝒰.f k := by
    rw [ha]; simp only [Category.assoc, pullback.condition]
  have hyz : y ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ := by
    rw [← cancel_mono (𝒰.f l)]
    simp only [Category.assoc]
    rw [← pullback.condition, ← pullback.condition, ← reassoc_of% hxy, reassoc_of% (hb j k),
      ← pullback.condition, ← reassoc_of% hxz]
  have hal : (α ≫ pullback.fst _ _) ≫ A.hom = (κ ≫ z ≫ pullback.snd _ _) ≫ 𝒰.f l := by
    rw [ha]; simp only [Category.assoc, ← pullback.condition]
    rw [← reassoc_of% hxz]
  have hk1 := pullback.lift_fst _ _ hak
  have hk2 := pullback.lift_snd _ _ hak
  have hl1 := pullback.lift_fst _ _ hal
  have hl2 := pullback.lift_snd _ _ hal
  have h1 := hchar j k _ α (pullback.lift _ _ hak) (κ ≫ x) hk1.symm
    (by rw [Category.assoc]; exact hκα) (by rw [hk2, Category.assoc])
  have h2 := hchar j l _ α (pullback.lift _ _ hal) (κ ≫ z) hl1.symm
    (by rw [Category.assoc, ← hxz]; exact hκα) (by rw [hl2, Category.assoc])
  have h3 := hchar k l _ (pullback.lift _ _ hak) (pullback.lift _ _ hal) (κ ≫ y) (hk1.trans hl1.symm)
    (by rw [Category.assoc, ← hxy, ← Category.assoc]; exact h1)
    (by rw [hl2, Category.assoc, hyz])
  rw [← cancel_epi κ, ← Category.assoc, h3, ← h2, Category.assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayDescentRangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_away_lift_descent : ∀ (k : Type) [Field k] (P : Polynomial k) (T : Finset (Localization.Away P)), ∃ F : Finset k, ∀ (R : Subring k), (F : Set k) ⊆ R → ∀ (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → ∀ t ∈ T, t ∈ (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h).range := by
  first | exact @GlobalTheory.localization_away_descent_range | exact GlobalTheory.localization_away_descent_range | (intros; apply GlobalTheory.localization_away_descent_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayPolynomialSubringLiftInjectiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizationAway_polynomial_subring_lift_injective : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∀ (R : Subring k) (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → Function.Injective (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h) := by
  first | exact @GlobalTheory.descentLocInj | exact GlobalTheory.descentLocInj | (intros; apply GlobalTheory.descentLocInj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormConjVacuumEqRankProductMulStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_conj_vacuum_eq_rank_product_mul : ∀ (D : D7) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] (σ₀ : K →+* ℂ) (R : Ranks) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D D.host.ccK → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK dl → TaylorLogMetric.IsChi D χ → B.VecP χ → ThetaFieldData B cD σ₀ R M → ∀ ρ : M →ₐ[ℚ] ℂ, ∃ lt : ℝ, ∀ i < R.m, logThAt B M ρ (R.N i) (R.N (i + 1)) = (R.N i : ℝ) * (R.N (i + 1) : ℝ) * lt := by
  first | exact @GlobalTheory.ConjVacuumPower.logThAt_eq_mul | exact GlobalTheory.ConjVacuumPower.logThAt_eq_mul | (intros; apply GlobalTheory.ConjVacuumPower.logThAt_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankBoxFunctionStableStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_rank_box_function_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan | exact GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan | (intros; apply GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweringPartKillsFockProductMinorsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowering_part_kills_fock_product_minors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus (R.MW i σ) τ, ∀ h, RderC R.θ (Wc D i) τ Z (fun g => thetaKO om h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f (deltaAtEmb D i σ))) = 0 := by
  first | exact @GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero | exact GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero | (intros; apply GlobalTheory.LowKillDelta.rderC_ptAt_delta_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantChartPointCentreFactorTwo
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartGraph

theorem maj_cpt_le_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (cpt X x z) τ v ≤ 2 * X.maj x τ v ∧ X.maj x τ v ≤ 2 * X.maj (cpt X x z) τ v := by
  intro E _ _ _ r X x z hxo hz τ v
  have hx : x ∈ X.dom := ModeHalfA.dom_of_orth X hxo
  have ho : X.IsOrtho x := hxo
  have hZ := GlobalTheory.T.chartGraphCoordinates_opNorm_le_of_small E r X z hz
  have hy : X.xZ x (graphCoord X z) ∈ X.dom := OrthonormalChartBounds.xZ_mem_dom X hx ho (by linarith)
  obtain ⟨hdet, hcol⟩ := GlobalTheory.T.chart_firstColumns_eq_graph_times_topBlock E r X x z τ
  have heq := GlobalTheory.T.majorant_eq_of_firstColumns_change E r X (cpt X x z) (X.xZ x (graphCoord X z)) τ (chartMatrixTopBlock X z τ)
    (by rw [hdet]; exact one_ne_zero) (Data.gramPos_det_ne X hy τ) hcol v
  obtain ⟨h1, h2⟩ := UnipMove.MajH.maj_xZ' X hx ho (ρ := 1 / 50) (by norm_num) (by norm_num) hZ τ v
  have h0 : 0 ≤ X.maj x τ v := by
    rw [ModeHalfA.maj_orth X hxo]; exact Finset.sum_nonneg fun _ _ => by positivity
  rw [heq]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.ChartGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactBlockLeviSecond
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ContDiff

namespace GlobalTheory.CuspSmooth

theorem conj_list_prod {G : Type} [Group G] (g : G) (l : List G) :
    g⁻¹ * l.prod * g = (l.map fun a => g⁻¹ * a * g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.prod_cons, List.map_cons]; rw [← ih]; group

theorem mem_Sm_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        (fun x => ψ (ι x * g₀)) ∈ GlobalTheory.CuspRep.Sm E d := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW K hK S l d h ι hι hd _ _ _ ψ hψ g₀ _ g
  classical
  refine GlobalTheory.T.contDiffOn_invSet_of_smooth_along_prod_exp E d _ {X | ∃ v, ∀ i j, ∀ u, u ≠ v → X i j u = 0} ?_ ?_
  · rw [eq_top_iff]
    intro X _
    have e : X = ∑ v : InfinitePlace E, (Matrix.of fun i j => Pi.single v (X i j v)) := by
      ext i j u
      rw [Matrix.sum_apply, Finset.sum_apply]
      simp [Pi.single_apply]
    rw [e]
    exact Submodule.sum_mem _ fun v _ => Submodule.subset_span ⟨v, fun i j u hu => by simp [Pi.single_apply, hu]⟩
  · intro k X hX y hy
    choose v hv using hX
    have hγ : ∀ i, IsRealLine σ J (fun t : ℝ => g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • X i))) * g₀) :=
      fun i => GlobalTheory.EisCont.CentreFinite.isRealLine_conj hcm
        (GlobalTheory.T.isRealLine_blockEmbedding_exp_infinitePlace F E σ hcm n J hJ r Xf Yf hW l d h ι hι (v i) (X i) (hv i)) g₀
    have hs := hψ.1.smooth k _ hγ (ι (g * GlobalTheory.CuspRep.infGL E d hy.unit) * g₀)
    convert hs using 2 with t
    set P : GL (Fin d) (GlobalTheory.CuspRep.Cinf E) := (List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).prod
    have hP : (P : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) =
        (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod := by
      simp only [P]
      rw [← Units.coeHom_apply, map_list_prod, List.map_ofFn]
      rfl
    have hU : GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) =
        GlobalTheory.CuspRep.toL (hy.unit * P).val := by
      rw [Units.val_mul, hP]
      congr 2
    rw [hU, GlobalTheory.CuspRep.chart_val]
    have e3 : (List.ofFn fun i => g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t i • X i))) * g₀) =
        ((List.ofFn fun i => GlobalTheory.CuspRep.expGLi d (t i • X i)).map (ι.comp (GlobalTheory.CuspRep.infGL E d))).map
          (fun a => g₀⁻¹ * a * g₀) := by
      simp [List.map_ofFn, Function.comp_def]
    rw [e3, ← conj_list_prod, ← map_list_prod]
    simp only [P, map_mul, MonoidHom.comp_apply, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CuspSmooth
end

