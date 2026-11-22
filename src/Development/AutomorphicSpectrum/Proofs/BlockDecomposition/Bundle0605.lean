import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingVolumeByUnit
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.UnitScale

theorem map_pi_scale {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, α i → α i) (hg : ∀ i, Measurable (g i))
    (c : ι → ℝ≥0∞) (hc0 : ∀ i, c i ≠ 0) (hct : ∀ i, c i ≠ ⊤)
    (h : ∀ i, (μ i).map (g i) = c i • μ i) :
    (Measure.pi μ).map (fun x i => g i (x i)) = (∏ i, c i) • Measure.pi μ :=
  _root_.UpperTheory.Reformulated.B.MapPiScale.map_pi_scale μ g hg c hc0 hct h

end GlobalTheory.CompanionTheory.AvgFree.UnitScale

open GlobalTheory.CompanionTheory.AvgFree.UnitScale in

theorem GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n M : ℕ) (l : Fin n) (D : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), MeasurableSet D → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) {X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) ∈ D} = ((θ : ℝ≥0∞) ^ M)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) D := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv s θ hθ n M l D hD
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := hlv.1
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hK
  set μ := GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv with hμ
  haveI : SigmaFinite μ := inferInstance
  let g : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun x => (s : Fv F v ⊗[F] E) * x
  have hgm : Measurable g := (continuous_const.mul continuous_id).measurable
  have hgs : Function.Surjective g := fun y =>
    ⟨((s⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * y, by simp [g]⟩
  have hθ0 : (θ : ℝ≥0∞) ≠ 0 := by
    intro h0
    have h1 := hθ Set.univ
    rw [h0, zero_mul] at h1
    have h2 : (fun x => (s : Fv F v ⊗[F] E) * x) '' Set.univ = Set.univ := Set.image_univ_of_surjective hgs
    rw [h2] at h1
    exact (IsOpen.measure_pos μ isOpen_univ ⟨0, trivial⟩).ne' h1
  have hθt : (θ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hmap : μ.map g = (θ : ℝ≥0∞)⁻¹ • μ := by
    ext Y hY
    rw [Measure.map_apply hgm hY, Measure.smul_apply, smul_eq_mul]
    have h1 := hθ (g ⁻¹' Y)
    have h2 : (fun x => (s : Fv F v ⊗[F] E) * x) '' (g ⁻¹' Y) = Y := Set.image_preimage_eq Y hgs
    rw [h2] at h1
    rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hθ0 hθt, one_mul]

  have hvec : (Measure.pi fun _ : Fin M => μ).map (fun x i => g (x i)) =
      ((θ : ℝ≥0∞)⁻¹ ^ M) • Measure.pi fun _ : Fin M => μ := by
    have := map_pi_scale (fun _ : Fin M => μ) (fun _ => g) (fun _ => hgm) (fun _ => (θ : ℝ≥0∞)⁻¹)
      (fun _ => ENNReal.inv_ne_zero.2 hθt) (fun _ => ENNReal.inv_ne_top.2 hθ0) (fun _ => hmap)
    simpa using this
  have hvm : Measurable (fun (x : Fin M → Fv F v ⊗[F] E) i => g (x i)) :=
    measurable_pi_lambda _ fun i => hgm.comp (measurable_pi_apply i)
  let gV : Fin n → (Fin M → Fv F v ⊗[F] E) → (Fin M → Fv F v ⊗[F] E) := fun a =>
    if a = l then (fun x i => g (x i)) else id
  let c : Fin n → ℝ≥0∞ := fun a => if a = l then (θ : ℝ≥0∞)⁻¹ ^ M else 1
  have hgV : ∀ a, Measurable (gV a) := fun a => by
    by_cases h : a = l
    · simpa [gV, h] using hvm
    · simpa [gV, h] using measurable_id
  have hc0 : ∀ a, c a ≠ 0 := fun a => by
    by_cases h : a = l
    · simpa [c, h, hθt] using fun _ => hθt
    · simp [c, h]
  have hct : ∀ a, c a ≠ ⊤ := fun a => by
    by_cases h : a = l
    · simpa [c, h] using ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hθ0)
    · simp [c, h]
  have hmapV : ∀ a, (Measure.pi fun _ : Fin M => μ).map (gV a) = c a • Measure.pi fun _ : Fin M => μ :=
    fun a => by
    by_cases h : a = l
    · simpa [gV, c, h] using hvec
    · simp [gV, c, h]
  have htup := map_pi_scale (fun _ : Fin n => Measure.pi fun _ : Fin M => μ) gV hgV c hc0 hct hmapV
  have hT : Measurable (fun (x : Fin n → Fin M → Fv F v ⊗[F] E) a => gV a (x a)) :=
    measurable_pi_lambda _ fun a => (hgV a).comp (measurable_pi_apply a)
  have hset : {X : Fin n → Fin M → Fv F v ⊗[F] E |
      GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : Fv F v ⊗[F] E)) ∈ D} =
      (fun (x : Fin n → Fin M → Fv F v ⊗[F] E) a => gV a (x a)) ⁻¹' D := by
    ext X
    have : GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : Fv F v ⊗[F] E)) = fun a => gV a (X a) := by
      funext a i
      by_cases h : a = l
      · subst h
        simp [GlobalTheory.CompanionTheory.SW.rmul, dMat, Matrix.diagonal_apply, gV, g, mul_comm]
      · simp [GlobalTheory.CompanionTheory.SW.rmul, dMat, Matrix.diagonal_apply, gV, h]
    simp [this]
  have hprod : (∏ a, c a) = ((θ : ℝ≥0∞) ^ M)⁻¹ := by
    simp [c, ENNReal.inv_pow]
  show (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => μ) _ = _ *
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => μ) D
  rw [hset, ← Measure.map_apply hT hD, htup, hprod, Measure.smul_apply, smul_eq_mul]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistOrbit

theorem finite_of_subset_mul' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' T K' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twConj' (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

theorem continuous_nrmL' (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

theorem proper' (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := GlobalTheory.T.orbit_compact_mod_centralizer_separable_local E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL' hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := GlobalTheory.NormOneProper.main E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj' hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

theorem continuous_thPair (hU : Unr E) (a b : ℕ) (w : Pl E) :
    Continuous ((thL a w).prodMap (thL b w)) := by
  have h1 := (GlobalTheory.BCT.thL_continuous_involutive E hU a w).1
  have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU b w).1
  exact (h1.comp continuous_fst).prodMk (h2.comp continuous_snd)

theorem isOpen_isCompact_pair_integral_points (a b : ℕ) (w : Pl E) :
    IsOpen (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
  obtain ⟨o₁, c₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨o₂, c₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [K2, Subgroup.coe_prod]
  exact ⟨o₁.prod o₂, c₁.prod c₂⟩

theorem proper_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    ∃ D : Set (GLw a w × GLw b w), IsCompact D ∧ ∀ x : GLw a w × GLw b w,
      x⁻¹ * y * ((thL a w).prodMap (thL b w)) x ∈ C →
        ∃ t ∈ twCent ((thL a w).prodMap (thL b w)) y, ∃ d ∈ D, x = t * d := by
  obtain ⟨D₁, hD₁, p₁⟩ := proper' hU a w y.1 h₁ _ (hC.image continuous_fst)
  obtain ⟨D₂, hD₂, p₂⟩ := proper' hU b w y.2 h₂ _ (hC.image continuous_snd)
  refine ⟨D₁ ×ˢ D₂, hD₁.prod hD₂, fun x hx => ?_⟩
  obtain ⟨t₁, ht₁, d₁, hd₁, e₁⟩ := p₁ x.1 ⟨_, hx, rfl⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, e₂⟩ := p₂ x.2 ⟨_, hx, rfl⟩
  refine ⟨(t₁, t₂), ?_, (d₁, d₂), ⟨hd₁, hd₂⟩, Prod.ext e₁ e₂⟩
  exact Prod.ext ht₁ ht₂

theorem finite_doubleCosets (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set (GLw a w × GLw b w))
        (K2 a b w : Set (GLw a w × GLw b w)) |
      ∃ k ∈ K2 a b w, (Quotient.out q * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (Quotient.out q * k) ∈ C}.Finite := by
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  obtain ⟨D, hD, hp⟩ := proper_pair hU a b w y h₁ h₂ C hC
  have hD' : IsCompact ((fun p : (GLw a w × GLw b w) × (GLw a w × GLw b w) => p.1 * p.2⁻¹) ''
      (D ×ˢ (K2 a b w : Set (GLw a w × GLw b w)))) :=
    (hD.prod hKc).image (continuous_fst.mul continuous_snd.inv)
  refine finite_of_subset_mul' _ (K2 a b w) hKo _ hD'
    (fun x => ∃ k ∈ K2 a b w, (x * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * k) ∈ C) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, d, hd, e⟩ := hp _ hx
  refine ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e, mul_inv_cancel_right]

theorem rStab_index_ne_zero (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (K' : Subgroup (GLw a w × GLw b w)) (f : GLw a w × GLw b w → ℂ) (ho : IsOpen (K' : Set (GLw a w × GLw b w)))
    (hf : IsHecke K' f) (x : K2 a b w) :
    (rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      ((thL a w).prodMap (thL b w)) ((x : GLw a w × GLw b w) * k))).index ≠ 0 := by
  obtain ⟨-, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  have hθ := continuous_thPair hU a b w
  set θ := (thL a w).prodMap (thL b w) with hθdef
  set W : Subgroup (GLw a w × GLw b w) := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set (GLw a w × GLw b w)) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace (K2 a b w) := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf (K2 a b w) : Subgroup (K2 a b w)) : Set (K2 a b w)) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf (K2 a b w)).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf (K2 a b w) ≤ rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      θ ((x : GLw a w × GLw b w) * k)) := by
    intro k' hk' k
    have hk'W : (k' : GLw a w × GLw b w) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : GLw a w × GLw b w)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : GLw a w × GLw b w) ∈ K' := hk'W.2
    have e : (((x * (k * k') : K2 a b w) : GLw a w × GLw b w)⁻¹ * y * θ ((x : GLw a w × GLw b w) * (k * k' : K2 a b w))) =
        (k' : GLw a w × GLw b w)⁻¹ * ((((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
          θ ((x : GLw a w × GLw b w) * k)) * θ (k' : GLw a w × GLw b w)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf.2 _ hl _).1, (hf.2 _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

theorem locSupp : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact ⟨fun C hC => finite_doubleCosets hU a b w y h₁ h₂ C hC,
    fun K' f ho _ hf x => rStab_index_ne_zero hU a b w y K' f ho hf x⟩

end GlobalTheory.CompanionTheory.TwistOrbit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDensityFromBoxVolumeGrowth
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem exists_mem_boxK_two_pow {K W : Type} [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) {n M : ℕ}
    {R : ℝ} (hR : 0 < R) (X : Fin n → Fin M → K) :
    ∃ j : ℕ, X ∈ boxK κ (fun _ _ => (2 : ℝ) ^ j * R) := by
  set B : ℝ := ∑ a, ∑ i, ∑ w, ‖κ (X a i) w‖ with hB
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / R) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨j, fun a i w => ?_⟩
  have h1 : ‖κ (X a i) w‖ ≤ ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun w => ‖κ (X a i) w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have h2 : ∑ w, ‖κ (X a i) w‖ ≤ ∑ i, ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun i => ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have h3 : ∑ i, ∑ w, ‖κ (X a i) w‖ ≤ B :=
    Finset.single_le_sum (f := fun a => ∑ i, ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h4 : B < (2 : ℝ) ^ j * R := (div_lt_iff₀ hR).1 hj
  linarith

theorem exists_large_ofReal_div_mul_le {A : ℝ} (hA : 0 ≤ A) {D ε : ℝ≥0∞} (hD : D ≠ ⊤) (hε : ε ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ENNReal.ofReal (A / R) * D ≤ ε := by
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hε)
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hDr : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ A * D.toReal / δ := by positivity
  refine ⟨1 + A * D.toReal / δ, by linarith, ?_⟩
  have hRpos : 0 < 1 + A * D.toReal / δ := by linarith
  have hkey : A / (1 + A * D.toReal / δ) * D.toReal ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
    have : (δ : ℝ) * (1 + A * D.toReal / δ) = δ + A * D.toReal := by
      field_simp
    rw [this]
    have : (0 : ℝ) ≤ δ := hδ0'.le
    linarith
  calc ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * D
      = ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * ENNReal.ofReal D.toReal := by
        rw [ENNReal.ofReal_toReal hD]
    _ = ENNReal.ofReal (A / (1 + A * D.toReal / δ) * D.toReal) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_le_ofReal hkey
    _ = δ := ENNReal.ofReal_coe_nnreal
    _ ≤ ε := hδ.le

theorem tsum_geometric_half_mul (c d : ℝ≥0∞) :
    ∑' j : ℕ, c * (2⁻¹ : ℝ≥0∞) ^ j * d = c * 2 * d := by
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    ENNReal.one_sub_inv_two, inv_inv]

theorem shell_real_identity {c R : ℝ} (hR : 0 < R) (e j : ℕ) :
    c / ((2 : ℝ) ^ j * R) ^ (e + 1) * ((2 : ℝ) ^ (j + 1) * R) ^ e
      = c * 2 ^ e / R * (1 / 2) ^ j := by
  have h2 : (2 : ℝ) ^ (j + 1) * R = 2 * ((2 : ℝ) ^ j * R) := by ring
  have key : ∀ P : ℝ, P ≠ 0 → c / P ^ (e + 1) * (2 * P) ^ e = c * 2 ^ e / P := by
    intro P hP
    rw [mul_pow, pow_succ]
    field_simp
  rw [h2, key _ (by positivity), one_div, inv_pow]
  field_simp

theorem tail_small_of_density :
    ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  intro K W _ _ κ n M H _ _ μ ν q C₀ hC₀ hden hq hbox φ hφ ε hε
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = 2 * (M - n) * Fintype.card W * n := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := hφ (e + 1)
  have hA : 0 ≤ |C| * (2 : ℝ) ^ e := by positivity
  obtain ⟨R, hR1, hRε⟩ := exists_large_ofReal_div_mul_le hA
    (ENNReal.mul_ne_top (by simp) hC₀ : (2 : ℝ≥0∞) * C₀ ≠ ⊤) hε
  refine ⟨R, hR1, fun Y hY => ?_⟩
  have hR0 : 0 < R := by linarith
  let S : ℕ → Set (Fin n → Fin M → K) := fun j =>
    (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) \ boxK κ (fun _ _ => (2 : ℝ) ^ j * R)) ∩ q ⁻¹' Y
  have hcover : (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y ⊆ ⋃ j, S j := by
    rintro X ⟨hX, hXY⟩
    classical
    have hex := exists_mem_boxK_two_pow κ hR0 X
    have hne : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      simp only [pow_zero, one_mul] at this
      exact hX this
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
    refine Set.mem_iUnion.2 ⟨j, ⟨?_, ?_⟩, hXY⟩
    · have := Nat.find_spec hex
      rw [hj] at this
      exact this
    · exact Nat.find_min hex (by omega)
  have hshell : ∀ j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
      ≤ ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
    intro j
    have hRj : 1 ≤ (2 : ℝ) ^ j * R := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
      nlinarith
    have hRj0 : 0 < (2 : ℝ) ^ j * R := by linarith
    have hSm : MeasurableSet (S j) := ((hbox _).diff (hbox _)).inter (hq hY)
    have hpt : ∀ X ∈ S j, ‖φ X‖ₑ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) := by
      rintro X ⟨⟨-, hX⟩, -⟩
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((hC _ hRj X hX).trans ?_)
      exact div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
    have hmu : μ (S j) ≤ C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y := by
      have h1 := hden (fun _ _ => (2 : ℝ) ^ (j + 1) * R) (fun _ _ => by positivity) Y hY
      have h2 : μ (S j) ≤ μ (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) ∩ q ⁻¹' Y) :=
        measure_mono fun X hX => ⟨hX.1.1, hX.2⟩
      have h3 : (∏ a : Fin n, ∏ w : W, ENNReal.ofReal ((2 : ℝ) ^ (j + 1) * R) ^ (2 * (M - n)))
          = ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) := by
        rw [ENNReal.ofReal_pow (by positivity), he]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      rw [h3] at h1
      exact h2.trans h1
    calc ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
        ≤ ∫⁻ _ in S j, ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) ∂μ :=
          setLIntegral_mono' hSm hpt
      _ = ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) * μ (S j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            (C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y) := by gcongr
      _ = (ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e)) * (C₀ * ν Y) := by ring
      _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
          rw [← ENNReal.ofReal_mul (by positivity), shell_real_identity hR0,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
          congr 3
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  calc ∫⁻ X in (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
      ≤ ∫⁻ X in ⋃ j, S j, ‖φ X‖ₑ ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) :=
        ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * 2 * (C₀ * ν Y) := tsum_geometric_half_mul _ _
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2 * C₀) * ν Y := by ring
    _ ≤ ε * ν Y := by gcongr

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUniformLimit
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJLim

theorem fj_tendsto : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) {ι : Type} (l : Filter ι) (Fs : ι → G D n → ℂ) (A : G D n → ℂ), Continuous A → LeftInv (GF D n) A → (∀ᶠ i in l, Continuous (Fs i) ∧ LeftInv (GF D n) (Fs i)) → (∀ C : Set (G D n), IsCompact C → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ c ∈ C, ‖Fs i c - A c‖ ≤ ε) → (∀ᶠ i in l, ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (Fs i - A) (M.sh y * g) = pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) → ∀ (g : G D n) (φ : Mx D ρ p → ℂ), Integrable φ m.μ → Tendsto (fun i => FJ M m ψ b₀ (Fs i) g φ) l (𝓝 (FJ M m ψ b₀ A g φ)) := by
  intro hPc D n ρ p hn M m ψ hψ b₀ ι l Fs A hAc hAinv hFs hunif hadd g φ hφ
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨hcont, hbd⟩ := hPc D n ρ p hn M m ψ hψ b₀
  obtain ⟨C, hC, -, hCb⟩ := hbd g
  have hφc : Integrable (fun y => conj (φ y)) m.μ := Complex.conjCLE.toContinuousLinearMap.integrable_comp hφ
  have hint : ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F →
      Integrable (fun y => pc M m ψ b₀ F (M.sh y * g) * conj (φ y)) m.μ := by
    intro F hF hinv
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
    have hc : Continuous fun y => pc M m ψ b₀ F (M.sh y * g) :=
      (hcont F hF hinv).comp (M.sh_cont.mul continuous_const)
    exact hφc.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall fun y => hCb F hF hinv B hB y)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set N : ℝ := ∫ y, ‖φ y‖ ∂m.μ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have hδ : 0 < ε / (N + 1) := by positivity
  filter_upwards [hFs, hadd, hunif C hC _ hδ] with i hi hai hui
  have hsub : Continuous (Fs i - A) := hi.1.sub hAc
  have hsinv : LeftInv (GF D n) (Fs i - A) := fun γ hγ x => by
    simp only [Pi.sub_apply, hi.2 γ hγ x, hAinv γ hγ x]
  have hpt : ∀ y, ‖pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)‖ ≤ ε / (N + 1) := by
    intro y
    rw [← hai y g]
    exact hCb _ hsub hsinv _ (fun c hc => by simpa using hui c hc) y
  have hdiff : FJ M m ψ b₀ (Fs i) g φ - FJ M m ψ b₀ A g φ =
      ∫ y, (pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) * conj (φ y) ∂m.μ := by
    unfold FJ
    rw [← integral_sub (hint _ hi.1 hi.2) (hint _ hAc hAinv)]
    simp only [sub_mul]
  have hle : ‖FJ M m ψ b₀ (Fs i) g φ - FJ M m ψ b₀ A g φ‖ ≤ ε / (N + 1) * N := by
    rw [hdiff, hN, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hφ.norm.const_mul _) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hpt y) (norm_nonneg _)
  rw [dist_eq_norm]
  refine lt_of_le_of_lt hle ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.FJLim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectivePointChartRatioStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_point_chart_ratio : ∀ (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ), w c ≠ 0 →
  (∀ i, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0) ∧
  ∀ i j, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) →
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (GlobalTheory.CompanionTheory.MPSmooth.ptP N c w) = w j / w i := by
  first | exact @GlobalTheory.CompanionTheory.MPSmooth.ptP_chart | exact GlobalTheory.CompanionTheory.MPSmooth.ptP_chart | (intros; apply GlobalTheory.CompanionTheory.MPSmooth.ptP_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatDoubleCosetEqOfRowDetStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_double_coset_eq_of_row_det : ∀ q q' : Ad3.GA.NQ, (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (q'.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 → (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (q'.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 → (q.out : Matrix (Fin 2) (Fin 2) ℚ).det = (q'.out : Matrix (Fin 2) (Fin 2) ℚ).det → q = q' := by
  first | exact @GlobalTheory.CompanionTheory.GAMajInj.maj_inj | exact GlobalTheory.CompanionTheory.GAMajInj.maj_inj | (intros; apply GlobalTheory.CompanionTheory.GAMajInj.maj_inj <;> assumption)
end

