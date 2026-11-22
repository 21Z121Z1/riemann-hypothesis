import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.MeasureInverseInduction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace MeasureInverseInduction

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countGL : Countable (GL (Fin k) E) := by
  haveI : Countable E := GroundTheory.Global.countable_numberField E
  haveI : Countable (Matrix (Fin k) (Fin k) E) := inferInstanceAs (Countable (Fin k → Fin k → E))
  exact Units.val_injective.countable

theorem blk_ratGL {j : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory j γ) : GlobalTheory j (ratGL E k γ) := by
  intro i c hic
  change algebraMap E (Ad E) (γ.val i c) = _
  rw [h i c hic, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  exact tsum_congr fun γ => lintegral_map hF (measurable_const_mul _)

theorem inv_step (ν : Measure (GA E k)) (hinvν : Measure.map (fun h => h⁻¹) ν = ν) (g : GA E k)
    (hc : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F (g * h * g⁻¹) ∂ν = ∫⁻ h, F h ∂ν)
    (f : GA E k → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * h) ∂ν := by
  have hG : Measurable fun x : GA E k => f (g⁻¹ * (g * x * g⁻¹)) :=
    hf.comp ((measurable_const_mul _).comp ((measurable_mul_const _).comp (measurable_const_mul _)))
  calc ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * (g * h⁻¹ * g⁻¹)) ∂ν :=
        lintegral_congr fun h => by congr 1; group
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂Measure.map (fun h => h⁻¹) ν := (lintegral_map hG measurable_inv).symm
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂ν := by rw [hinvν]
    _ = ∫⁻ x, f (g⁻¹ * x) ∂ν := hc (fun y => f (g⁻¹ * y)) (hf.comp (measurable_const_mul _))

def invE (Γ : Set (GL (Fin k) E)) (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) : Γ ≃ Γ where
  toFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  invFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  left_inv γ := Subtype.ext (inv_inv γ.1)
  right_inv γ := Subtype.ext (inv_inv γ.1)

theorem inv_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ)
    (hinvν : Measure.map (fun h => h⁻¹) (nuD E k d) = nuD E k d)
    (hconj : ∀ γ ∈ Γ, ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ h, F (ratGL E k γ * h * (ratGL E k γ)⁻¹) ∂nuD E k d = ∫⁻ h, F h ∂nuD E k d)
    (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) :
    Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc ∫⁻ h, f h ∂Measure.map (fun h => h⁻¹) (nuG Γ d) = ∫⁻ h, f h⁻¹ ∂nuG Γ d :=
        lintegral_map hf measurable_inv
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h)⁻¹ ∂nuD E k d := lint_nuG Γ d _ (hf.comp measurable_inv)
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ.1⁻¹ * h) ∂nuD E k d := tsum_congr fun γ => by
        rw [inv_step _ hinvν _ (hconj γ.1 γ.2) f hf, map_inv (ratGL E k) γ.1]
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d :=
        (invE Γ hΓ).tsum_eq (fun γ : Γ => ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d)
    _ = ∫⁻ h, f h ∂nuG Γ d := (lint_nuG Γ d f hf).symm

theorem sf_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) [SFinite (nuD E k d)] : SFinite (nuG Γ d) := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [nuG]; infer_instance

theorem ae_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (hae : ∀ᵐ u ∂nuD E k d, UU (k - d) u) :
    ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [ae_iff] at hae ⊢
  rw [nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
  intro γ
  rw [(measurableEmbedding_mulLeft (ratGL E k γ)).map_apply]
  exact measure_mono_null (fun u hu hUU => hu ⟨γ.1, u, γ.2, hUU, rfl⟩) hae

theorem nuD_ne_zero (hsf : ∀ d ≤ k, SFinite (nuD E k d)) : ∀ d ≤ k, nuD E k d ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro _ h
    have h1 := congrArg (fun μ : Measure (GA E k) => μ Set.univ) h
    simp [nuD] at h1
  | succ d ih =>
    intro hd h
    haveI := hsf d (by omega)
    have hm : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => blkU p.1 * p.2 :=
      (((continuous_posU (isNil_blk k _ _)).comp continuous_fst).mul continuous_snd).measurable
    have h3 := (Measure.map_eq_zero_iff hm.aemeasurable).mp h
    have h2 := congrArg (fun μ => μ (vecDomain E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) ×ˢ Set.univ)) h3
    simp only [Measure.prod_prod, vecMeasure_vecDomain, one_mul, Measure.coe_zero, Pi.zero_apply] at h2
    exact ih (by omega) (Measure.measure_univ_eq_zero.mp h2)

variable [IsTotallyComplex E]

theorem main_nuG (hD0 : D0) (hN1 : N1) (Γ : Set (GL (Fin k) E)) (d : ℕ) (hd : d ≤ k)
    (hinv : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hblk : ∀ γ ∈ Γ, GlobalTheory (k - d) γ) :
    SFinite (nuG Γ d) ∧ Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d ∧
      ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  obtain ⟨hsf, hae, hinvν, -, hconj⟩ := hN1 E k d hd
  haveI := hsf
  refine ⟨sf_nuG Γ d, inv_nuG Γ d hinvν (fun γ hγ F hF => ?_) hinv, ae_nuG Γ d hae⟩
  rw [hconj _ (blk_ratGL (hblk γ hγ)) F hF, (hD0 E k).2.2.2.1 γ, inv_one, ENNReal.ofReal_one, one_pow, one_mul]

end MeasureInverseInduction

open MeasureInverseInduction in
set_option synthInstance.maxHeartbeats 400000 in
theorem galois_fixed_adelic_matrices_descend : D0 → N0 → N1 → N3 := by
  intro hD0 hN0 hN1 E _ _ _ k
  have hP : ∀ m < k, SFinite (nuP E k m) ∧ Measure.map (fun h => h⁻¹) (nuP E k m) = nuP E k m ∧
      ∀ᵐ h ∂nuP E k m, ∃ γ u, IsMir m γ ∧ UU (m + 1) u ∧ h = ratGL E k γ * u := by
    intro m hm
    have hN := hN0 E k (m + 1) (by omega) (by omega)
    have h6 : ∀ γ : GL (Fin k) E, IsMir m γ → IsMir m γ⁻¹ ∧ GlobalTheory (m + 1) γ := by
      simpa only [Nat.add_sub_cancel] using hN.2.2.2.2.2.1
    have e : k - (k - (m + 1)) = m + 1 := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | IsMir m γ} (k - (m + 1)) (by omega)
      (fun γ hγ => (h6 γ hγ).1) (fun γ hγ => by rw [e]; exact (h6 γ hγ).2)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hB : ∀ j ≤ k, SFinite (nuB E k j) ∧ Measure.map (fun h => h⁻¹) (nuB E k j) = nuB E k j ∧
      ∀ᵐ h ∂nuB E k j, ∃ γ u, GlobalTheory j γ ∧ UU j u ∧ h = ratGL E k γ * u := by
    intro j hj
    have hinv : ∀ γ : GL (Fin k) E, GlobalTheory j γ → GlobalTheory j γ⁻¹ := by
      intro γ hγ
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
        subst this
        rw [inv_one]
        exact hγ
      · exact (hN0 E k j hpos hj).2.2.2.1 γ hγ
    have e : k - (k - j) = j := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | GlobalTheory j γ} (k - j) (by omega)
      (fun γ hγ => hinv γ hγ) (fun γ hγ => by rw [e]; exact hγ)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hall : ∀ γ : GL (Fin k) E, γ ∈ {γ : GL (Fin k) E | GlobalTheory k γ} := fun γ i c h =>
    absurd h (not_or.mpr ⟨not_le.mpr i.isLt, not_le.mpr c.isLt⟩)
  have hK : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F h ∂nuB E k k = ∑' γ : GL (Fin k) E, F (ratGL E k γ) := by
    intro F hF
    rw [nuB, lint_nuG _ _ F hF, Nat.sub_self]
    simp only [nuD, lintegral_dirac, mul_one]
    exact (Equiv.subtypeUnivEquiv hall).tsum_eq (fun γ => F (ratGL E k γ))
  have h4 : 1 ≤ k → (∀ᵐ h ∂nuP E k 0, UU 0 h) ∧ nuP E k 0 ≠ 0 := by
    intro hk
    obtain ⟨-, -, hae⟩ := hP 0 (by omega)
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
      have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
      rw [hh, this, map_one, one_mul]
      exact ⟨hu.1, hu.2.1, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
    · intro h0
      haveI : Countable (GL (Fin k) E) := countGL
      have h1 : nuP E k 0 Set.univ = 0 := by simp [h0]
      rw [nuP, nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero] at h1
      have h2 := h1 ⟨1, show IsMir 0 (1 : GL (Fin k) E) from fun i c _ => rfl⟩
      rw [(measurableEmbedding_mulLeft _).map_apply, Set.preimage_univ, Measure.measure_univ_eq_zero] at h2
      exact nuD_ne_zero (fun d hd => (hN1 E k d hd).1) _ (by omega) h2
  exact ⟨hP, hB, hK, h4⟩

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.NormAverageBound
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace NormAverageBound

theorem norm_avg_le {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G) (Φ : G → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x, ‖Φ x‖ ≤ C) : ‖avg Γ Φ‖ ≤ C := by
  unfold GlobalTheory.CuspGeneric.avg
  split_ifs with hex
  · obtain ⟨-, -, h1⟩ := hex.choose_spec
    have hfin : hex.choose.1 hex.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    calc ‖∫ x in hex.choose.2, Φ x ∂hex.choose.1‖ ≤ C * hex.choose.1.real hex.choose.2 :=
          norm_setIntegral_le_of_norm_le_const hfin (fun x _ => h x)
      _ = C := by simp [Measure.real, h1]
  · simpa using hC

end NormAverageBound

open NormAverageBound in
theorem fourier_column_of : N0 → P0 → P1 → CornerEmbedding → FourierSeriesColumn := by
  intro hN0 hP0 hP1 hK5e E _ _ _ m k hk hkm ψ hψ ι hι F hF g
  obtain ⟨hFc, hFl, hFlaw, hFvan⟩ := hF
  have hPre : PositivityTheory.AdelicQuotientData.Pre ψ k F := ⟨hFc, hFl, hFlaw⟩
  obtain ⟨hcolPre, hcoef, -, -⟩ := hP1 E m ψ hψ k hk hkm F hPre
  obtain ⟨-, hcolL, -⟩ := hcolPre
  obtain ⟨hgamM, huniqM, -⟩ := hN0 E m k hk hkm.le
  obtain ⟨hgamK, -⟩ := hN0 E k k hk le_rfl
  obtain ⟨hex, hprops⟩ := hK5e E m k hkm.le
  obtain ⟨ιE, hιE⟩ := hex E
  obtain ⟨-, -, -, -, -, -, hrat, -⟩ := hprops ι hι
  have hlift : ∀ ρ : RowT E k k, ∃ ρ' : RowT E m k, ∀ i : Fin m,
      Subtype.val ρ' i = if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0 := by
    intro ρ
    refine ⟨Subtype.mk (fun i : Fin m => if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0) ⟨?_, ?_⟩,
      fun i => rfl⟩
    · obtain ⟨c, hc⟩ := Function.ne_iff.1 (Subtype.property ρ).1
      intro h0
      apply hc
      have h1 := congrFun h0 ⟨c, lt_trans c.isLt hkm⟩
      simpa [c.isLt] using h1
    · intro i hi
      simp [show ¬ (i : ℕ) < k by omega]
  choose lift hlift using hlift
  have hA : ∀ ρ : RowT E k k, coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g) =
      colT ψ k F (ι (ratGL E k (gam ρ) * g)) := by
    intro ρ
    rw [hcoef (lift ρ) (ι g), map_mul, hrat ιE hιE]
    have hBlk : PositivityTheory.jumpWindows.GlobalTheory k (ιE (gam ρ)) := by
      intro i c hic
      rw [hιE (gam ρ)]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      rw [dif_neg (by omega)]
    obtain ⟨⟨ξ'', p⟩, ⟨hp, hγ⟩, -⟩ := huniqM _ hBlk
    have hξ : ξ'' = lift ρ := by
      apply Subtype.ext
      funext c
      have hrow := congrArg (fun γ : GL (Fin m) E => (γ : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ c) hγ
      simp only [hιE (gam ρ), Units.val_mul, Matrix.mul_apply] at hrow
      have hpr : ∀ l, (p : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l =
          (1 : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l := fun l => hp _ _ (Or.inl le_rfl)
      simp only [hpr, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at hrow
      rw [(hgamM ξ'').2 ⟨k - 1, by omega⟩ c (by show k - 1 + 1 = k; omega)] at hrow
      rw [← hrow, hlift ρ c]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      by_cases hc : (c : ℕ) < k
      · rw [dif_pos ⟨by show k - 1 < k; omega, hc⟩, dif_pos hc]
        exact (hgamK ρ).2 _ _ (by show k - 1 + 1 = k; omega)
      · rw [dif_neg (fun h => hc h.2), dif_neg hc, Matrix.one_apply, if_neg]
        intro h
        apply hc
        rw [← h]
        show k - 1 < k
        omega
    rw [hγ, map_mul, mul_assoc, hcolL p hp, hξ]
  have hcoef0 : coefF ψ k (0 : UnipotentBlockColumnIndex m k k → E) F (ι g) = 0 := by
    have h0 := hFvan k (by omega) le_rfl (ι g)
    simpa [GlobalTheory.CuspGeneric.coefF, GlobalTheory.CuspGeneric.dot] using h0
  have hinj : Function.Injective
      (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) := by
    intro ρ₁ ρ₂ h
    apply Subtype.ext
    funext j
    have h1 := congrFun h (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m))
      ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k)
    beta_reduce at h1
    rw [hlift, hlift, dif_pos j.isLt, dif_pos j.isLt] at h1
    exact h1
  have hkey : ∀ t : UnipotentBlockColumnIndex m k k, t = (Subtype.mk ((⟨((Subtype.val t).1 : ℕ), ((Subtype.val t).1).isLt⟩ : Fin m),
      (⟨k, hkm⟩ : Fin m)) ⟨(Subtype.property t).1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k) := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show ((Subtype.val t).2 : ℕ) = k
      have h2 := Subtype.property t
      omega
  have hsurj : ∀ c : UnipotentBlockColumnIndex m k k → E, c ≠ 0 → ∃ ρ : RowT E k k,
      (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) = c := by
    intro c hc
    obtain ⟨ρ, hρ⟩ : ∃ ρ : RowT E k k, ∀ j : Fin k, Subtype.val ρ j =
        c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ :
          UnipotentBlockColumnIndex m k k) := by
      refine ⟨Subtype.mk (fun j : Fin k => c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m),
        (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k))
        ⟨?_, fun i hi => absurd hi (not_le.2 i.isLt)⟩, fun j => rfl⟩
      intro h0
      apply hc
      funext t
      rw [hkey t]
      exact congrFun h0 ⟨((Subtype.val t).1 : ℕ), (Subtype.property t).1⟩
    refine ⟨ρ, ?_⟩
    funext t
    show Subtype.val (lift ρ) (Subtype.val t).1 = c t
    rw [hlift, dif_pos (Subtype.property t).1, hρ]
    exact congrArg c (hkey t).symm
  have hoff : ∀ c : UnipotentBlockColumnIndex m k k → E,
      c ∉ Set.range (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) →
        coefF ψ k c F (ι g) = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]; exact hcoef0
    · exact absurd (hsurj c hc0) (fun h => hc h)
  have hper : Per (ratV E (UnipotentBlockColumnIndex m k k)) (fun x => F (blkU x * ι g)) :=
    per_blk hFc (fun c h => hFl _ (isMir_blkU c) h) (ι g)
  obtain ⟨-, hP0b, hP0c⟩ := hP0 E ψ hψ (UnipotentBlockColumnIndex m k k)
  refine ⟨?_, ?_⟩
  · intro B hB
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have hpar : HasSum (fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
        (avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))) :=
      hP0b _ _ hper hper
    have hS := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
      (fun c hc => by simp only [hoff c hc, zero_mul])).2 hpar
    have hSle : ‖avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))‖ ≤ B ^ 2 :=
      norm_avg_le _ _ _ (sq_nonneg B) (fun x => by
        simpa [norm_mul, sq] using mul_le_mul (hB x) (hB x) (norm_nonneg _) hB0)
    have hre := ((Complex.hasSum_iff _ _).1 hS).1
    simp only [Function.comp_def, Complex.mul_conj, Complex.ofReal_re] at hre
    simp only [Complex.mul_conj] at hSle
    have hterm : ∀ ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2 =
        ENNReal.ofReal (Complex.normSq (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := by
      intro ρ
      rw [hA ρ, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.normSq_eq_norm_sq]
    calc ∑' ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2
        = ∑' ρ : RowT E k k, ENNReal.ofReal (Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := tsum_congr hterm
      _ = ENNReal.ofReal (∑' ρ : RowT E k k, Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => Complex.normSq_nonneg _) hre.summable).symm
      _ ≤ ENNReal.ofReal (B ^ 2) := by
          rw [hre.tsum_eq]
          exact ENNReal.ofReal_le_ofReal (le_trans (Complex.re_le_norm _) hSle)
  · intro hfin
    have hfin' : {c : UnipotentBlockColumnIndex m k k → E | coefF ψ k c F (ι g) ≠ 0}.Finite := by
      refine (hfin.image (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1)).subset ?_
      intro c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hc hcoef0
      obtain ⟨ρ, rfl⟩ := hsurj c hc0
      refine ⟨ρ, ?_, rfl⟩
      show colT ψ k F (ι (ratGL E k (gam ρ) * g)) ≠ 0
      rw [← hA ρ]
      exact hc
    have hs : HasSum (fun c => coefF ψ k c F (ι g)) (F (blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) * ι g)) :=
      hP0c _ hper hfin'
    have hb0 : blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) = 1 := by
      unfold GlobalTheory.CuspGeneric.blkU
      exact GlobalTheory.CuspGeneric.posU_zero _
    rw [hb0, one_mul] at hs
    have hs2 := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g)) hoff).2 hs
    show ∑' ρ : RowT E k k, colT ψ k F (ι (ratGL E k (gam ρ) * g)) = F (ι g)
    rw [← hs2.tsum_eq]
    exact tsum_congr fun ρ => (hA ρ).symm

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PsiDeterminantFlag
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PsiDeterminantFlag

theorem exists_psiOK {E : Type} [Field E] [NumberField E] (w : Pl E) :
    ∃ χ : AddChar (w.adicCompletion E) ℂ, PositivityTheory.JacquetShalikaLocal.PsiOK χ := by
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.SplitWeil.exists_hasConductor_one (w.adicCompletion E)
  exact ⟨_, GlobalTheory.CompanionTheory.JSBound.psiOK_of_hasConductor hψ₁⟩

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem dt_fl (hG0 : jumpWindows.G0) (hD0 : D0) (w : Pl E)
    (n : GL (Fin k) (w.adicCompletion E)) (hn : n ∈ Iwasawa.unipotent (w.adicCompletion E) k)
    (κ : GL (Fin k) (w.adicCompletion E)) (hκ : κ ∈ GLnLocal.integralGL (w.adicCompletion E) k)
    (l : Fin k → ℤ) :
    Dt (fl k w (n * Iwasawa.torusPow (w.adicCompletion E) k l * κ)) =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-∑ i, l i) := by
  obtain ⟨_, hmul, _, _, hUU, _, _, _, _, htor, hint⟩ := hD0 E k
  obtain ⟨_, _, hci, hcl, hcl', -⟩ := hG0 E k
  have h1 : Dt (fl k w n) = 1 := by
    obtain ⟨t1, t2, -⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E k w n (fun i j hij => hn.1 hij) hn.2
    exact hUU 0 _ ⟨t1, t2, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
  have h2 : Dt (fl k w κ) = 1 := by
    refine hint _ (hci w κ) fun v => ?_
    by_cases hv : v = w
    · subst hv; rw [hcl]; exact hκ
    · rw [hcl' w v κ hv]; exact one_mem _
  rw [map_mul, map_mul, hmul, hmul, h1, h2, htor, one_mul, mul_one]

end PsiDeterminantFlag

theorem mean_convergence_of : jumpWindows.G0 → D0 → P2 → C0 → C2 → D1 → M0 → LocalHeckeAlgebra → CAUCHY → M1 := by
  intro hG0 hD0 hP2 _ hC2 hD1 hM0 hK8a hC E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hkm hα hα' hD
  have : BorelSpace (GA E k) := ⟨rfl⟩
  obtain ⟨hpos, hmul, hcont, -, hUU, -⟩ := hD0 E k
  obtain ⟨hlaw, hpsN, hUU01, hwhit, -, hgood, -⟩ := hP2 E k ψ hψ
  obtain ⟨β', σ₀', hβ', hM⟩ := hM0 E k μ hk β hβ ψ hψ S m α α' u f φ hD
  have hk1 : k - 1 < k := by omega
  have hWf : Pre ψ 0 (whit ψ (k - 1) f) := hwhit _ hk1 f hD.pre
  have hWφ : Pre ψ 0 (whit ψ (k - 1) φ) := hwhit _ hk1 φ (hgood _ φ hD.good)
  have hPc : Continuous (PW ψ f φ) := hWf.cont.mul (Complex.continuous_conj.comp hWφ.cont)
  have hPu : ∀ n, UU 0 n → ∀ g, PW ψ f φ (n * g) = PW ψ f φ g := by
    intro n hn g
    have h1 := hlaw 0 _ hWf n (hUU01 n hn) g
    have h2 := hlaw 0 _ hWφ n (hUU01 n hn) g
    simp only [PW, h1, h2, map_mul]
    have e : psN ψ n * conj (psN ψ n) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hpsN]; simp
    linear_combination (whit ψ (k - 1) f g * conj (whit ψ (k - 1) φ g)) * e
  have hDtu : ∀ n, UU 0 n → ∀ g, Dt (n * g) = Dt g := fun n hn g => by rw [hmul, hUU 0 n hn, one_mul]
  have hDtm : Measurable fun g : GA E k => (Dt g : ℂ) := Complex.measurable_ofReal.comp hcont.measurable
  have hΦm : ∀ z : ℂ, Measurable fun g => PW ψ f φ g * (Dt g : ℂ) ^ z := fun z =>
    hPc.measurable.mul (hDtm.pow_const z)
  have hΦu : ∀ z : ℂ, ∀ n, UU 0 n → ∀ g,
      PW ψ f φ (n * g) * (Dt (n * g) : ℂ) ^ z = PW ψ f φ g * (Dt g : ℂ) ^ z := by
    intro z n hn g; rw [hPu n hn, hDtu n hn]
  have hχ : ∀ w : Off E S, ∃ χ : AddChar (w.1.adicCompletion E) ℂ, PositivityTheory.JacquetShalikaLocal.PsiOK χ :=
    fun w => PsiDeterminantFlag.exists_psiOK w.1
  let a' : ℂ → Off E S → (Fin k → ℤ) → ℂ := fun z w l =>
    aLoc α α' w l * (((nq w : ℝ) ^ (-∑ i, l i) : ℝ) : ℂ) ^ z
  have ha0 : ∀ z w, a' z w 0 = 1 := by
    intro z w
    obtain ⟨χ, hχ'⟩ := hχ w
    simp [a', (hK8a E S m k α α' w χ hχ' hk hkm).1]
  have hlawz : ∀ z, LawOff S (fun g => PW ψ f φ g * (Dt g : ℂ) ^ z) (a' z) := by
    intro z w g hg n hn κ hκ l
    simp only [a']
    rw [hD.law w g hg n hn κ hκ l, hmul, PsiDeterminantFlag.dt_fl hG0 hD0 w.1 n hn κ hκ l, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hpos g).le (by positivity)]
    simp only [nq]; ring
  have hI : ∀ s : ℂ, 2 < s.re → σ₀' < (s - ((m : ℂ) - k) / 2).re →
      ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β' =
        (∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β') * LS S α α' s := by
    intro s hs hs'
    have hsum := hC2 E k μ hk β' hβ' S _ (a' (s - ((m : ℂ) - k) / 2)) (hΦm _) (hΦu _) (hlawz _) (ha0 _)
      (hM _ hs').1
    obtain ⟨-, hL⟩ := hC E S m k α α' s hkm hα hα' hs
    have e : (fun l : Off E S →₀ (Fin k → ℤ) => ∏ w ∈ l.support, loc (nq w) (α w) (α' w) s (l w)) =
        fun l => ∏ w ∈ l.support, (nq w : ℂ) ^ rhoPair (l w) * a' (s - ((m : ℂ) - k) / 2) w (l w) := by
      funext l
      refine Finset.prod_congr rfl fun w _ => ?_
      obtain ⟨χ, hχ'⟩ := hχ w
      exact (((hK8a E S m k α α' w χ hχ' hk hkm).2 (l w)).1 s).symm
    rw [e] at hL
    have hL2 := hL.mul_right (∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β')
    rw [mul_comm _ (LS S α α' s)]
    exact hsum.unique hL2
  obtain ⟨hdiff, hnz⟩ := hD1 E k μ hk β' hβ' S (PW ψ f φ) u ((σ₀' + 1 : ℝ) : ℂ) hPc hPu hD.one hD.pos
    (hM _ (by simp)).1
  refine ⟨fun s => ∫ g in G0 S, PW ψ f φ g * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) ∂μ.withDensity β',
    max 2 (σ₀' + ((m : ℝ) - k) / 2), hdiff.comp (differentiable_id.sub_const _), ?_, ?_⟩
  · intro σ
    have e : ((σ : ℂ) + u * Complex.I) - ((m : ℂ) - k) / 2 =
        ((σ - ((m : ℝ) - k) / 2 : ℝ) : ℂ) + u * Complex.I := by push_cast; ring
    dsimp only
    rw [e]
    exact hnz _
  · intro s hs
    have hs2 : 2 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hre : (s - ((m : ℂ) - k) / 2).re = s.re - ((m : ℝ) - k) / 2 := by simp
    have hs' : σ₀' < (s - ((m : ℂ) - k) / 2).re := by
      rw [hre]; linarith [le_max_right 2 (σ₀' + ((m : ℝ) - k) / 2)]
    have e1 : ∀ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) * (Dt g : ℂ) ^ s =
        sumF f g * conj (φ g) * (Dt g : ℂ) ^ (s - ((m : ℂ) - k) / 2) := by
      intro g
      rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hpos g).ne'), neg_add_eq_sub]
    simp_rw [e1]
    rw [(hM _ hs').2, hI s hs2 hs']

end PositivityTheory.AdelicQuotientData

end
end

