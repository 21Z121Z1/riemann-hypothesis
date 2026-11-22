import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MeasurePreservingPiCompProd
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0019
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulVec
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramVol

theorem det_gram_contraction_le : ∀ (r : ℕ) (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : V →ₗ[ℂ] W), (∀ x, ‖T x‖ ≤ ‖x‖) → ∀ a : Fin r → V,
    ‖(Matrix.gram ℂ fun b => T (a b)).det‖ ≤ ‖(Matrix.gram ℂ a).det‖ := by
  intro r
  induction r with
  | zero => intro V W _ _ _ _ T _ a; simp
  | succ r ih =>
    intro V W _ _ _ _ T hT a
    have dec : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (v x : U),
        ∃ c : ℂ, x = c • v + (ℂ ∙ v)ᗮ.starProjection x := by
      intro U _ _ v x
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ((ℂ ∙ v).starProjection_apply_mem x)
      exact ⟨c, by rw [hc]; exact ((ℂ ∙ v).starProjection_add_starProjection_orthogonal x).symm⟩
    have orth : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (v x : U),
        inner ℂ v ((ℂ ∙ v)ᗮ.starProjection x) = 0 := by
      intro U _ _ v x
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 ((ℂ ∙ v)ᗮ.starProjection_apply_mem x)
    choose c hc using fun b : Fin r => dec V (a 0) (a b.succ)
    set w : Fin r → V := fun b => (ℂ ∙ a 0)ᗮ.starProjection (a b.succ) with hw
    choose c' hc' using fun b : Fin r => dec W (T (a 0)) (T (w b))
    let T' : V →ₗ[ℂ] W := ((ℂ ∙ T (a 0))ᗮ.starProjection : W →L[ℂ] W).toLinearMap ∘ₗ T
    have hT' : ∀ x, ‖T' x‖ ≤ ‖x‖ := fun x =>
      le_trans ((ℂ ∙ T (a 0))ᗮ.norm_starProjection_apply_le (T x)) (hT x)
    have e1 : a = Fin.cons (a 0) (fun b => c b • a 0 + w b) := by
      funext i
      refine Fin.cases rfl (fun b => ?_) i
      simp only [Fin.cons_succ]
      exact hc b
    have e2 : (fun b => T (a b)) = Fin.cons (T (a 0)) (fun b => (c b + c' b) • T (a 0) + T' (w b)) := by
      funext i
      refine Fin.cases rfl (fun b => ?_) i
      simp only [Fin.cons_succ]
      have h1 : a b.succ = c b • a 0 + w b := hc b
      have h2 : T (w b) = c' b • T (a 0) + T' (w b) := hc' b
      rw [h1, map_add, map_smul, add_smul, add_assoc, ← h2]
    have g1 := Formalism.HermitianLatticeCounting.P.s5b7_gram_cons r (a 0) c w (fun b => orth V _ _)
    have g2 := Formalism.HermitianLatticeCounting.P.s5b7_gram_cons r (T (a 0)) (fun b => c b + c' b) (fun b => T' (w b))
      (fun b => orth W _ _)
    rw [← e1] at g1
    rw [← e2] at g2
    rw [g1, g2, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, norm_norm, norm_norm]
    have := ih V W T' hT' w
    have := hT (a 0)
    gcongr

theorem measurePreserving_mulVec {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (h : ‖g.det‖ = 1) :
    MeasurePreserving (fun x : Fin n → ℂ => g *ᵥ x) volume volume := by
  have hdet : LinearMap.det ((Matrix.toLin' g).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h]; norm_num
  have h1 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ))
    (f := (Matrix.toLin' g).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h1
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h1
  refine ⟨?_, h1⟩
  exact (LinearMap.continuous_of_finiteDimensional ((Matrix.toLin' g).restrictScalars ℝ)).measurable

theorem exists_iso (d c : ℕ) (P : Submodule ℂ (EuclideanSpace ℂ (Fin (d + c)))) (hP : d ≤ Module.finrank ℂ P) :
    ∃ Φ : EuclideanSpace ℂ (Fin (d + c)) ≃ₗᵢ[ℂ] WithLp 2 (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin c)),
      ∀ x, (Φ (P.starProjection x)).ofLp.1 = (Φ x).ofLp.1 := by
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank hP
  have hu' : LinearIndependent ℂ (P.subtype ∘ u) := hu.map' _ (Submodule.ker_subtype P)
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin (d + c))) := Submodule.span ℂ (Set.range (P.subtype ∘ u)) with hK
  have hKP : K ≤ P := by
    rw [hK, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (u i).2
  have hKd : Module.finrank ℂ K = d := by
    rw [hK, finrank_span_eq_card hu']; simp
  have hKc : Module.finrank ℂ Kᗮ = c := by
    have := K.finrank_add_finrank_orthogonal
    rw [hKd, finrank_euclideanSpace, Fintype.card_fin] at this
    omega
  let e1 : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) := ((stdOrthonormalBasis ℂ K).reindex (finCongr hKd)).repr
  let e2 : Kᗮ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin c) := ((stdOrthonormalBasis ℂ Kᗮ).reindex (finCongr hKc)).repr
  refine ⟨K.orthogonalDecomposition.trans (LinearIsometryEquiv.withLpProdCongr 2 e1 e2), fun x => ?_⟩
  have : ∀ y, ((K.orthogonalDecomposition.trans (LinearIsometryEquiv.withLpProdCongr 2 e1 e2)) y).ofLp.1 =
      e1 (K.orthogonalProjectionOnto y) := by
    intro y
    rw [← Submodule.fst_orthogonalDecomposition_apply]
    rfl
  rw [this, this]
  congr 1
  exact Submodule.orthogonalProjectionOnto_starProjection_of_le hKP x

theorem eucl_eq {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq, eucl]
  simp only [Complex.normSq_eq_norm_sq]

theorem vol_le (d c j : ℕ) (hj : j ≤ d) (g : Matrix (Fin (d + c)) (Fin (d + c)) ℂ) (hg : ‖g.det‖ = 1)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin (d + c)))) (hP : d ≤ Module.finrank ℂ P) (R t : ℝ) (hR : 0 < R)
    (ht : 0 ≤ t) :
    volume {B : Fin j → Fin (d + c) → ℂ | (∀ b, eucl (g *ᵥ B b) ≤ R) ∧ gramProj P (fun b => g *ᵥ B b) ≤ t} ≤
      ENNReal.ofReal ((t ^ (2 * (d - j)) * R ^ (2 * j ^ 2) * Real.pi ^ (j * d) / ((d - j).factorial : ℝ) ^ j) *
        (Real.pi * R ^ 2) ^ (c * j)) := by
  obtain ⟨Φ, hΦ⟩ := exists_iso d c P hP
  have h0 : MeasurePreserving
      (Φ : EuclideanSpace ℂ (Fin (d + c)) → WithLp 2 (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin c))) :=
    LinearIsometryEquiv.measurePreserving
      ({ (Φ.toLinearEquiv.restrictScalars ℝ) with norm_map' := Φ.norm_map } :
        EuclideanSpace ℂ (Fin (d + c)) ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin c)))
  have hl : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + c) → ℂ)).symm :=
    GlobalTheory.volume_preserving_ofLp_complex (Fin (d + c))
  have hl' : MeasurePreserving (WithLp.toLp 2 : (Fin (d + c) → ℂ) → EuclideanSpace ℂ (Fin (d + c))) := hl.symm
  have h1 := h0.comp (hl'.comp (measurePreserving_mulVec g hg))
  have h2 : MeasurePreserving (Prod.map (id : EuclideanSpace ℂ (Fin d) → _) (@WithLp.ofLp 2 (Fin c → ℂ)))
      volume volume := (MeasurePreserving.id volume).prod (GlobalTheory.volume_preserving_ofLp_complex (Fin c))
  have h3 := h2.comp (WithLp.volume_preserving_ofLp (EuclideanSpace ℂ (Fin d)) (EuclideanSpace ℂ (Fin c)))
  have h4 := Formalism.HermitianLatticeCounting.P.measurePreserving_pi_comp_prod j _ _ h1 h3
  set S : Set ((Fin j → EuclideanSpace ℂ (Fin d)) × (Fin j → Fin c → ℂ)) :=
    Formalism.HermitianLatticeCounting.P.s5b7_A R d j t ×ˢ
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R) with hS
  have hSm : MeasurableSet S :=
    (Formalism.HermitianLatticeCounting.P.s5b7_A_closed _ _ _ _).measurableSet.prod
      (MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet)
  have hball : volume (Set.pi Set.univ fun _ : Fin j => Set.pi Set.univ fun _ : Fin c => Metric.closedBall (0 : ℂ) R) =
      ENNReal.ofReal ((Real.pi * R ^ 2) ^ (c * j)) := by
    rw [volume_pi_pi]
    simp only [volume_pi_pi, Complex.volume_closedBall, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← pow_mul, ENNReal.ofReal_pow (by positivity), mul_comm Real.pi, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hR.le]
    congr 2
    exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm
  refine le_trans (measure_mono ?_) (le_trans (h4.measure_preimage hSm.nullMeasurableSet).le ?_)
  · rintro B ⟨hB1, hB2⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin j → EuclideanSpace ℂ (Fin (d + c)), v = fun b => WithLp.toLp 2 (g *ᵥ B b) := ⟨_, rfl⟩
    have hn : ∀ b, ‖Φ (v b)‖ ≤ R := fun b => by
      rw [Φ.norm_map, hv, ← eucl_eq]; exact hB1 b
    have hB3 : Real.sqrt ‖(Matrix.gram ℂ fun b => P.starProjection (v b)).det‖ ≤ t := by
      rw [hv]; exact hB2
    have goal : ((fun b => (Φ (v b)).ofLp.1, fun b => (Φ (v b)).ofLp.2.ofLp) :
        (Fin j → EuclideanSpace ℂ (Fin d)) × (Fin j → Fin c → ℂ)) ∈ S := by
      refine ⟨⟨fun b => ?_, ?_⟩, fun b _ i _ => ?_⟩
      · exact le_trans (WithLp.norm_fst_le _ _) (hn b)
      · refine le_trans (Real.sqrt_le_sqrt ?_) hB3
        obtain ⟨T, hT0⟩ : ∃ T : EuclideanSpace ℂ (Fin (d + c)) →ₗ[ℂ] EuclideanSpace ℂ (Fin d),
            ∀ x, T x = (Φ x).ofLp.1 :=
          ⟨(WithLp.fstL 2 ℂ _ _).toLinearMap ∘ₗ Φ.toLinearEquiv.toLinearMap, fun _ => rfl⟩
        have hT : ∀ x, ‖T x‖ ≤ ‖x‖ := fun x => by
          rw [hT0]; exact le_trans (WithLp.norm_fst_le _ (Φ x)) (Φ.norm_map x).le
        have := det_gram_contraction_le j _ _ T hT (fun b => P.starProjection (v b))
        simp only [hT0, hΦ] at this
        exact this
      · rw [mem_closedBall_zero_iff]
        exact le_trans (PiLp.norm_apply_le (Φ (v b)).ofLp.2 i)
          (le_trans (WithLp.norm_snd_le _ _) (hn b))
    rw [hv] at goal
    exact goal
  · rw [hS, Measure.volume_eq_prod, Measure.prod_prod, hball, ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact Formalism.HermitianLatticeCounting.P.s5b7_vol R hR j d hj t ht

theorem norm_det_inv_eq_one {k : ℕ} {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : m ∈ UH (Hb k)) :
    ‖(m⁻¹).det‖ = 1 := by
  have h : mᴴ * Hb k * m = Hb k := hm
  have hH : (Hb k).det ≠ 0 := by
    rw [Hb, det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs <;> simp
  have h2 := congrArg (fun A => ‖Matrix.det A‖) h
  simp only [det_mul, det_conjTranspose, norm_mul, norm_star] at h2
  have hH' : 0 < ‖(Hb k).det‖ := norm_pos_iff.2 hH
  have h3 : ‖m.det‖ ^ 2 = 1 := by
    have : ‖(Hb k).det‖ * ‖m.det‖ ^ 2 = ‖(Hb k).det‖ * 1 := by rw [mul_one]; linarith
    exact mul_left_cancel₀ hH'.ne' this
  have h4 : ‖m.det‖ = 1 := by
    have := norm_nonneg m.det
    nlinarith
  rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, h4, inv_one]

theorem inv_factorial_le (s : ℕ) (hs : 1 ≤ s) : 1 / (s.factorial : ℝ) ≤ (Real.exp 1 / s) ^ s := by
  have h := Real.pow_div_factorial_le_exp (s : ℝ) (Nat.cast_nonneg s) s
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [div_pow, ← Real.exp_nat_mul, mul_one, le_div_iff₀ (by positivity)]
  calc _ = (s : ℝ) ^ s / s.factorial := by ring
    _ ≤ _ := h

theorem vol_gram : ∀ (k j : ℕ), 1 ≤ j → j + 2 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), k - 1 ≤ Module.finrank ℂ P₀ → volume {B : Fin j → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ M y : ℝ, 1 ≤ M → 0 < y → volume {B : Fin j → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ M) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) * (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j))) := by
  intro k j _ hjk m hm P hP
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  have hd : d + 1 - 1 = d := by omega
  rw [hd] at hP ⊢
  have key := vol_le d 2 j (by omega) m⁻¹ (norm_det_inv_eq_one hm) P hP
  obtain ⟨s, hs⟩ : ∃ s, d = j + s := ⟨d - j, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hs2 : d - j = s := by omega
  rw [hs2] at key ⊢
  refine ⟨?_, fun M y hM hy => ?_⟩
  · have hz : ∀ N : ℕ, volume {B : Fin j → Fin (d + 1 + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ (N : ℝ) + 1) ∧
        gramProj P (fun b => m⁻¹ *ᵥ B b) ≤ 0} = 0 := fun N => by
      have := key ((N : ℝ) + 1) 0 (by positivity) le_rfl
      rw [zero_pow (by omega)] at this
      simpa using this
    refine measure_mono_null ?_ (measure_iUnion_null hz)
    intro B hB
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ b, eucl (m⁻¹ *ᵥ B b))
    refine Set.mem_iUnion.2 ⟨N, fun b => ?_, le_of_eq hB⟩
    have : eucl (m⁻¹ *ᵥ B b) ≤ ∑ b, eucl (m⁻¹ *ᵥ B b) :=
      Finset.single_le_sum (f := fun b => eucl (m⁻¹ *ᵥ B b)) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ b)
    linarith
  · refine le_trans (key M (2 * y) (by positivity) (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
    have hpi := Real.pi_pos
    have h1 : (1 / (s.factorial : ℝ)) ^ j ≤ ((Real.exp 1 / s) ^ s) ^ j :=
      pow_le_pow_left₀ (by positivity) (inv_factorial_le s hs1) j
    have hX : 0 ≤ (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
        (Real.pi * Real.exp 1 / (s : ℝ)) ^ (j * s) * (2 * y) ^ (2 * s) := by positivity
    calc _ = (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * (1 / (s.factorial : ℝ)) ^ j) * (2 * y) ^ (2 * s) := by
          rw [hs, mul_add j j s, pow_add, ← sq j, one_div, inv_pow, div_eq_mul_inv]; ring
      _ ≤ (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * ((Real.exp 1 / s) ^ s) ^ j) * (2 * y) ^ (2 * s) := by gcongr
      _ = (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi * Real.exp 1 / (s : ℝ)) ^ (j * s) * (2 * y) ^ (2 * s) := by
          rw [← pow_mul, mul_comm s j, ← mul_pow, mul_div_assoc]
      _ ≤ _ := by linarith

end GlobalTheory.Amp.GramVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MuGPreimageConj
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem muG_preimage_conj {n : ℕ} (ε : Fin n → Bool) (u : Formalism.REAL.UJ ε) (B : Set (Formalism.REAL.UJ ε)) :
    Formalism.REAL.muG ε ((fun g => u⁻¹ * g * u) ⁻¹' B) = Formalism.REAL.muG ε B := by
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  have : (fun g => u⁻¹ * g * u) ⁻¹' B = (fun g => u⁻¹ * g) ⁻¹' ((fun g => g * u) ⁻¹' B) := rfl
  rw [this, measure_preimage_mul, measure_preimage_mul_right]

theorem gauge_map_of_iso : ∀ (n n' : ℕ) (ε : Fin n → Bool) (ε' : Fin n' → Bool), n = n' → ∀ (T : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε') (u : Formalism.REAL.UJ ε), (∀ g, Formalism.REAL.hs (uMat (T (u * g * u⁻¹)) - 1) = Formalism.REAL.hs (uMat g - 1)) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → (ENNReal.ofReal c • Formalism.REAL.muG ε).map T = ENNReal.ofReal c' • Formalism.REAL.muG ε' := by
  intro n n' ε ε' hn T u hT c c' hc hc'
  subst hn
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : (Formalism.REAL.muG ε').IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : ((Formalism.REAL.muG ε).map T).IsHaarMeasure := T.isHaarMeasure_map _
  obtain ⟨a, ha⟩ : ∃ a : NNReal, (Formalism.REAL.muG ε).map T = a • Formalism.REAL.muG ε' :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hball : ∀ r : ℝ, Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
      a * Formalism.REAL.muG ε' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro r
    have h1 := congrArg (fun m : Measure (Formalism.REAL.UJ ε') =>
      m {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}) ha
    have h2 := MeasurableEquiv.map_apply (μ := Formalism.REAL.muG ε) T.toHomeomorph.toMeasurableEquiv
      {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}
    have h3 : (T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
        (fun g => u⁻¹ * g * u) ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
      ext g
      have := hT (u⁻¹ * g * u)
      rw [show u * (u⁻¹ * g * u) * u⁻¹ = g by group] at this
      simp only [Set.mem_preimage, Set.mem_setOf_eq, this]
    change (Formalism.REAL.muG ε).map T _ = Formalism.REAL.muG ε ((T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' _) at h2
    rw [h3, muG_preimage_conj] at h2
    rw [← h2]
    simpa using h1
  have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hca : c' = c * a := by
    have h1 := Filter.Tendsto.const_mul c' hc
    have h2 := Filter.Tendsto.const_mul (c * a) hc'
    have h3 := tendsto_nhds_unique h1 (h2.congr fun r => by
      rw [hball r, ENNReal.toReal_mul, ENNReal.coe_toReal]; ring)
    exact mul_right_cancel₀ hω.ne' h3
  rw [Measure.map_smul, ha, hca, ENNReal.ofReal_mul' a.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_smul]
  rfl

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardRealGeneratedIdealsLe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.RealIdealCount

theorem eq_map_comap {E : Type} [Field E] [NumberField E] [StarRing E]
    (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {𝔫 : Ideal (𝓞 E)}
    (h : 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t}) :
    𝔫 = (𝔫.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
  refine le_antisymm ?_ Ideal.map_comap_le
  conv_lhs => rw [h]
  refine Ideal.span_le.mpr ?_
  rintro t ⟨ht, hst⟩
  have hreal : (t : E) ∈ maximalRealSubfield E := by
    intro φ
    have key := hs φ (t : E)
    rw [hst, starRingEnd_apply] at key
    exact key.symm
  have hint : IsIntegral ℤ (⟨(t : E), hreal⟩ : maximalRealSubfield E) := by
    have ht' : IsIntegral ℤ (t : E) := t.isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
      (algebraMap (maximalRealSubfield E) E).injective).mp ht'
  let s : 𝓞 (maximalRealSubfield E) := ⟨⟨(t : E), hreal⟩, hint⟩
  have hs' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s = t := by
    apply RingOfIntegers.ext
    rfl
  rw [← hs']
  refine Ideal.mem_map_of_mem _ ?_
  rw [Ideal.mem_comap, hs']
  exact ht

private theorem isCMField_of_star_compat {E : Type} [Field E] [NumberField E] [StarRing E]
    [hTC : IsTotallyComplex E]
    (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) : IsCMField E := by
  refine GlobalTheory.LeastExponentCompare.isCMField_of_conj E (fun z => star z)
    (fun φ z => by rw [hs, starRingEnd_apply]) ?_
  by_contra hne
  push_neg at hne
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have hreal : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext z
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := hs w.embedding z
    rw [hne z, starRingEnd_apply] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w)) hreal

private theorem finrank_maximalRealSubfield_eq_fDeg (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Module.finrank ℚ (maximalRealSubfield E) = Formalism.HermitianLatticesTheory.fDeg E := by
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    IsTotallyComplex.finrank (K := E)] at h1
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h2
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem ncard_real_ideals_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ Y : ℝ, 1 ≤ Y → {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.Finite ∧ (({𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.ncard : ℕ) : ℝ) ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ hE Y hY
  obtain ⟨hTC, hs, -⟩ := hE
  haveI := hTC
  haveI : IsCMField E := isCMField_of_star_compat hs
  set F := maximalRealSubfield E
  set S : Set (Ideal (𝓞 E)) := {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧
    (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2} with hSdef
  set T : Set (Ideal (𝓞 F)) := {𝔞 : Ideal (𝓞 F) | 𝔞 ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ Y} with hTdef
  let g : Ideal (𝓞 E) → Ideal (𝓞 F) := fun 𝔫 => 𝔫.comap (algebraMap (𝓞 F) (𝓞 E))
  have hmap : ∀ 𝔫 ∈ S, 𝔫 = (g 𝔫).map (algebraMap (𝓞 F) (𝓞 E)) := fun 𝔫 h𝔫 =>
    eq_map_comap hs h𝔫.2.1
  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hinj : Set.InjOn g S := by
    intro 𝔫₁ h₁ 𝔫₂ h₂ heq
    rw [hmap 𝔫₁ h₁, hmap 𝔫₂ h₂, heq]
  have hmaps : Set.MapsTo g S T := by
    intro 𝔫 h𝔫
    have hn := hmap 𝔫 h𝔫
    refine ⟨?_, ?_⟩
    · intro hbot
      apply h𝔫.1
      rw [hn, hbot, Ideal.map_bot]
    · have hnorm : Ideal.absNorm 𝔫 = Ideal.absNorm (g 𝔫) ^ 2 := by
        conv_lhs => rw [hn]
        rw [Ideal.absNorm_algebraMap, hdeg]
      have hle := h𝔫.2.2
      rw [hnorm] at hle
      push_cast at hle
      exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by linarith) two_ne_zero).mp hle
  have hT : T.Finite := GlobalTheory.IdealBoundedNorm.finite_setOf_absNorm_le F Y
  refine ⟨Set.Finite.of_injOn hmaps hinj hT, ?_⟩
  have hcard : S.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn g hmaps hinj hT
  have hTb := GlobalTheory.IdealBoundedNorm.ncard_absNorm_le F Y hY
  rw [finrank_maximalRealSubfield_eq_fDeg E] at hTb
  calc ((S.ncard : ℕ) : ℝ) ≤ (T.ncard : ℝ) := by exact_mod_cast hcard
    _ ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := hTb

end GlobalTheory.RealIdealCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormDetInnerLeOfDetEqOne
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PlueckerBound

theorem norm_det_inner_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u w : Fin b → E) :
    ‖(Matrix.of fun a a' => ⟪u a, w a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖w a‖ := by
  have h := GlobalTheory.Hadamard.norm_det_apply_le (𝕜 := ℂ) (fun a => innerSL ℂ (u a)) w
  simp only [innerSL_apply_apply, innerSL_apply_norm] at h
  rw [mul_comm]
  exact h

theorem det_inner_sum_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u v : Fin b → E) (t : Matrix (Fin b) (Fin b) ℂ) :
    (Matrix.of fun a a' => ⟪u a, ∑ i, t i a' • v i⟫_ℂ).det
      = (Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det * t.det := by
  rw [← Matrix.det_mul]
  congr 1
  ext a a'
  simp [Matrix.mul_apply, inner_sum, inner_smul_right, mul_comm]

theorem norm_det_inner_le_of_det_eq_one (n b : ℕ) (v u : Fin b → EuclideanSpace ℂ (Fin n))
    (t : Matrix (Fin b) (Fin b) ℂ) (ht : t.det = 1)
    (_h : ∀ a a', a ≠ a' → ⟪∑ i, t i a • v i, ∑ i, t i a' • v i⟫_ℂ = 0) :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖∑ i, t i a • v i‖ := by
  have h := norm_det_inner_le u (fun a => ∑ i, t i a • v i)
  rwa [det_inner_sum_smul, ht, mul_one] at h

end GlobalTheory.PlueckerBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.FockTen

theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    have hf : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    rw [hf, zero_mul, zero_mul]

theorem fockF_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (ten f) (ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [fockF_eq_fockL]
  show Formalism.L2.DIV.fockL (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ)) (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) = _
  rw [Formalism.L2.DIV.fk_fock_prod]
  exact Finset.prod_congr rfl fun τ _ => (fockF_eq_fockL _ _).symm

theorem fockF_extremal_ne {n : ℕ} (l : DomWeight n) : Formalism.REAL.fockF (extremal ℂ n l) (extremal ℂ n l) ≠ 0 := by
  intro h0
  have h1 : normFock l (extremal ℂ n l) (extremal ℂ n l) = 1 := bridge_normFock_extremal_holds n l
  rw [normFock, h0, div_zero] at h1
  exact zero_ne_one h1

theorem nfAll_ten : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (∀ f g : ι → MvPolynomial (Fin n × Fin n) ℂ, nfAll lam (ten f) (ten g) = ∏ τ, normFock (lam τ) (f τ) (g τ)) ∧ (∀ p : MvPolynomial (ι × Fin n × Fin n) ℂ, nfAll lam p p = 0 → p = 0) ∧ ∀ (G M : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (y : Frames G), fnOf G s M (ten f) y = ∏ τ, ((M τ * y.1 τ).det ^ s τ * MvPolynomial.eval (fun v : Fin n × Fin n => (M τ * y.1 τ) v.1 v.2) (f τ)) := by
  intro ι _ n lam
  have hden : ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => fockF_extremal_ne (lam τ)
  refine ⟨fun f g => ?_, fun p hp => ?_, fun G M s f y => ?_⟩
  · rw [nfAll, fockF_ten]
    simp only [normFock]
    rw [Finset.prod_div_distrib]
  · rw [nfAll, div_eq_zero_iff] at hp
    rcases hp with hp | hp
    · by_contra hne
      exact (@LT.lt.ne' ℂ Complex.partialOrder.toPreorder _ _ (Formalism.L2.DIV.ps_fockF_pos p hne)) hp
    · exact absurd hp hden
  · show (∏ τ, (M τ * y.1 τ).det ^ s τ) *
        MvPolynomial.eval _ (∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)) = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval_rename]
    rfl

end GlobalTheory.FockTen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelicStatement
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotentRadical_mem_adelic : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (γ : GL (Fin I.n) I.E), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → I.InUnipRad (starRingEnd I.E) I.J W (γ : Matrix (Fin I.n) (Fin I.n) I.E) → ∃ a ∈ I.GFset ∩ I.NA W, (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧ I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  first | exact @GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic | exact GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic | (intros; apply GlobalTheory.Proof.rational_unipotentRadical_mem_adelic.rational_mem_adelic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureTransportDoubleCosetStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootMeasure_transport_doubleCoset : ∀ (D : D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : Point ℂ (D.R.rS + 1)) (g a a' : MatKR D.R.k D.R.rS) (μ : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → g ∈ UH (Hpk D.R.k D.R.rS) → a ∈ Sset D.R.k D.R.rS z → a' ∈ Sset D.R.k D.R.rS z' → IsRootMeasR D z z' p g μ → IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  first | exact @GlobalTheory.Amp.RootMove.rootMeas_move | exact GlobalTheory.Amp.RootMove.rootMeas_move | (intros; apply GlobalTheory.Amp.RootMove.rootMeas_move <;> assumption)
end

