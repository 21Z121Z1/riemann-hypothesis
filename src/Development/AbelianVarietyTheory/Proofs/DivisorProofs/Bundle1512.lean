import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeSmoothVariationAlongBoundedUnipotent
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapVari

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem nilM_smul {r : ℕ} (τ : ℝ) (x : BlockIx a r → Cinf E) :
    (nilM (τ • x) : Matrix (Fin a) (Fin a) (Cinf E)) = τ • nilM x := by
  ext i j
  simp only [nilM, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp

theorem norm_toL_nilM_le {r : ℕ} (x : BlockIx a r → Cinf E) :
    ‖toL (nilM x : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  change ‖(nilM x : Matrix (Fin a) (Fin a) (Cinf E)) i j‖ ≤ ‖x‖
  simp only [nilM, Matrix.of_apply]
  split_ifs with h
  · exact norm_le_pi_norm x _
  · simp

theorem continuous_unip_inf {r : ℕ} :
    Continuous (fun x : BlockIx a r → Cinf E => (unip x : GL (Fin a) (Cinf E))) := by
  have hN : Continuous (fun x : BlockIx a r → Cinf E => (nilM x : Matrix (Fin a) (Fin a) (Cinf E))) := by
    refine continuous_matrix fun i j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact Units.continuous_iff.2 ⟨continuous_const.add hN, continuous_const.sub hN⟩

theorem exists_bound_compact {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c ∈ Ω, ‖toL (c : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A ∧
      ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A := by
  have h1 : Continuous (fun c : GL (Fin a) (Cinf E) => toL (c : Matrix (Fin a) (Fin a) (Cinf E))) := by
    have h := (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)))
    exact h
  have h2 : Continuous (fun c : GL (Fin a) (Cinf E) =>
      toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) := by
    have h := (Units.continuous_coe_inv (M := Matrix (Fin a) (Fin a) (Cinf E)))
    exact h
  obtain ⟨A1, hA1⟩ := hΩ.exists_bound_of_continuousOn h1.continuousOn
  obtain ⟨A2, hA2⟩ := hΩ.exists_bound_of_continuousOn h2.continuousOn
  exact ⟨max (max A1 A2) 0, le_max_right _ _, fun c hc =>
    ⟨(hA1 c hc).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hA2 c hc).trans ((le_max_right _ _).trans (le_max_left _ _))⟩⟩

theorem norm_conj_le (A : ℝ) (c : GL (Fin a) (Cinf E)) (N : Matrix (Fin a) (Fin a) (Cinf E))
    (h1 : ‖toL (c : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A)
    (h2 : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))‖ ≤ A) :
    ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N * c.val)‖ ≤ a * a * A * A * ‖toL N‖ := by
  have hA : 0 ≤ A := (norm_nonneg _).trans h1
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have p1 := norm_toL_mul_le ((c⁻¹ : GL (Fin a) (Cinf E)).val * N) c.val
  have p2 := norm_toL_mul_le (c⁻¹ : GL (Fin a) (Cinf E)).val N
  have p2' : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N)‖ ≤ a * (A * ‖toL N‖) :=
    p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) ha)
  have p3 : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * N)‖ * ‖toL c.val‖ ≤ (a * (A * ‖toL N‖)) * A :=
    mul_le_mul p2' h1 (norm_nonneg _) (mul_nonneg ha (mul_nonneg hA (norm_nonneg _)))
  exact (p1.trans (mul_le_mul_of_nonneg_left p3 ha)).trans (le_of_eq (by ring))

end GlobalTheory.RapVari

open GlobalTheory.RapVari in

theorem GlobalTheory.rap_vari : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t →
    ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ R : ℝ, 0 ≤ R →
    ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧
    ∀ ψ : Sm E a, ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
    (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
    ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω,
    ∀ z : BlockIx a j → Cinf E, ‖z‖ ≤ R →
    ‖ψ.1 (infGL E a (unip z * (d * c))) - ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a t ht i j hij Ω hΩ R hR
  obtain ⟨C0, hC0, hconj⟩ := GlobalTheory.T.blockUnipotent_conj_coneDiagonal_bound E a t ht i j hij
  obtain ⟨B, Cb, hCb, hbasis⟩ := GlobalTheory.T.lieDerivative_le_of_bound_on_finiteDirections E a
  obtain ⟨A, hA, hAc⟩ := exists_bound_compact hΩ
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have haA : (0 : ℝ) ≤ a * a * A * A := mul_nonneg (mul_nonneg (mul_nonneg ha ha) hA) hA
  refine ⟨(fun p : (BlockIx a j → Cinf E) × GL (Fin a) (Cinf E) => unip p.1 * p.2) ''
      (Metric.closedBall 0 (C0 * C0 * R) ×ˢ Ω), B, Cb * (a * a * A * A) * (C0 * R), ?_, ?_, ?_⟩
  · exact ((isCompact_closedBall 0 (C0 * C0 * R)).prod hΩ).image
      ((continuous_unip_inf.comp continuous_fst).mul continuous_snd)
  · exact mul_nonneg (mul_nonneg hCb haA) (mul_nonneg hC0 hR)
  intro ψ r d hr hrat hd M hM hB c hc z hz
  obtain ⟨hq, hz'⟩ := hconj r d hr hrat hd
  obtain ⟨z', hz'n, hcomm⟩ := hz' z
  have hq0 : 0 ≤ r j / r i := div_nonneg (hr j).le (hr i).le
  have hz'R : ‖z'‖ ≤ C0 * (r j / r i) * R := hz'n.trans (mul_le_mul_of_nonneg_left hz (mul_nonneg hC0 hq0))
  have hz'R' : ‖z'‖ ≤ C0 * C0 * R :=
    hz'R.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hC0) hR)
  have hu : ∀ τ : ℝ, ((c⁻¹ * unip (τ • z') * c : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      1 + τ • ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) := by
    intro τ
    rw [Units.val_mul, Units.val_mul]
    change (c⁻¹ : GL (Fin a) (Cinf E)).val * (1 + nilM (τ • z')) * c.val = _
    rw [nilM_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hNN : ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) *
      ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val) = 0 := by
    calc _ = (c⁻¹ : GL (Fin a) (Cinf E)).val *
          (nilM z' * (c.val * (c⁻¹ : GL (Fin a) (Cinf E)).val) * nilM z') * c.val := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Units.mul_inv, Matrix.mul_one, nilM_mul, Matrix.mul_zero, Matrix.zero_mul]
  have hNnorm : ‖toL ((c⁻¹ : GL (Fin a) (Cinf E)).val * nilM z' * c.val)‖ ≤
      a * a * A * A * (C0 * (r j / r i) * R) :=
    (norm_conj_le A c _ (hAc c hc).1 (hAc c hc).2).trans
      (mul_le_mul_of_nonneg_left ((norm_toL_nilM_le z').trans hz'R) haA)
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, unip (τ • z') * c ∈
      (fun p : (BlockIx a j → Cinf E) × GL (Fin a) (Cinf E) => unip p.1 * p.2) ''
        (Metric.closedBall 0 (C0 * C0 * R) ×ˢ Ω) := by
    intro τ hτ
    refine ⟨(τ • z', c), ⟨?_, hc⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hτ.2).trans hz'R'
  have key := GlobalTheory.T.norm_sub_le_of_lieDerivative_unipotentSegment E a ψ (infGL E a (d * c)) _ (fun τ => c⁻¹ * unip (τ • z') * c)
    (Cb * (a * a * A * A * (C0 * (r j / r i) * R)) * M) hNN hu (by
      intro τ hτ
      have e : infGL E a (d * c) * infGL E a (c⁻¹ * unip (τ • z') * c) =
          infGL E a (d * (unip (τ • z') * c)) := by
        rw [← map_mul]; congr 1; group
      rw [e]
      refine (hbasis ψ.1 _ _ M (fun Y hY => hB Y hY _ (hmem τ hτ)) hM).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNnorm hCb) hM)
  have e : infGL E a (d * c) * infGL E a (c⁻¹ * unip ((1 : ℝ) • z') * c) = infGL E a (unip z * (d * c)) := by
    rw [← map_mul]; congr 1
    have h1 := hcomm 1
    rw [one_smul, one_smul] at h1
    rw [one_smul, ← mul_assoc (unip z) d c, h1]
    group
  rw [e] at key
  exact key.trans (le_of_eq (by ring))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecomposition
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

open Pointwise Matrix

namespace GlobalTheory.SiegelSetGL

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

theorem continuous_pInfC : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInfC E))

theorem continuous_mapFin : Continuous (GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

theorem exists_compact_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ω : Set (AdelicGLn.AdelicGL E a)), IsCompact ω →
    ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) → ∀ t : ℝ, 0 < t →
    ∃ (Ω : Set (GL (Fin a) (Cinf E))) (Kf : Set (GL (Fin a) (Af E))), IsCompact Ω ∧ IsCompact Kf ∧
      ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, ∀ k ∈ maxCompact (K := E) (n := a),
          ∃ c ∈ Ω, ∃ f ∈ Kf, b * infGL E a d * k = infGL E a (d * c) * finGL E a f := by
  intro E _ _ _ a ω hω hωB t ht
  set pI := GeneralLinearGroup.map (n := Fin a) (pInf E)
  set pF := GeneralLinearGroup.map (n := Fin a) (pFin E)
  have hωI : IsCompact (pI '' ω) := hω.image (continuous_mapInf E a)
  have hup : ∀ b ∈ pI '' ω, b.val.BlockTriangular id := by
    rintro _ ⟨b, hb, rfl⟩ i j hij
    have h0 : (b : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := hωB hb hij
    change pInf E ((b : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0
    rw [h0, map_zero]
  obtain ⟨Ω0, hΩ0, hΩ⟩ := GlobalTheory.T.exists_compact_coneDiagonal_conj_upperTriangular E a (pI '' ω) hωI hup t ht
  have hK := isCompact_maxCompact (K := E) (n := a)
  refine ⟨Ω0 * pI '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    pF '' ω * pF '' (maxCompact (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)),
    hΩ0.mul (hK.image (continuous_mapInf E a)),
    (hω.image (continuous_mapFin E a)).mul (hK.image (continuous_mapFin E a)), ?_⟩
  intro r d hr hrt hd b hb k hk
  refine ⟨(d⁻¹ * pI b * d) * pI k, Set.mul_mem_mul (hΩ r d hr hrt hd _ ⟨b, hb, rfl⟩) ⟨k, hk, rfl⟩,
    pF b * pF k, Set.mul_mem_mul ⟨b, hb, rfl⟩ ⟨k, hk, rfl⟩, ?_⟩
  apply ga_ext
  · change pI (b * infGL E a d * k) = pI (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pI, pInf_infGL, pInf_finGL, mul_one]
    group
  · change pF (b * infGL E a d * k) = pF (infGL E a (d * (d⁻¹ * pI b * d * pI k)) * finGL E a (pF b * pF k))
    simp only [map_mul, pF, pFin_infGL, pFin_finGL, mul_one, one_mul]

end GlobalTheory.SiegelSetGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevPointwiseBoundWords
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.SliceSob

section General
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def dw (l : List V) (g : V → ℂ) : V → ℂ :=
  l.foldr (fun e u y => fderiv ℝ u y e) g

theorem contDiff_dw (l : List V) {g : V → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (dw l g) := by
  induction l with
  | nil => exact hg
  | cons e l ih =>
    exact (ih.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_line {u : V → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x e : V) (t : ℝ) :
    HasDerivAt (fun r : ℝ => u (x + r • e)) (fderiv ℝ u (x + t • e) e) t := by
  have h1 : HasDerivAt (fun r : ℝ => x + r • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  exact ((hu.differentiable (by simp)) (x + t • e)).hasFDerivAt.comp_hasDerivAt t h1

theorem step {u : V → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x e : V) :
    ‖u x‖ ^ 2 ≤ (2 * ∫ r in (0:ℝ)..1, ‖u (x + r • e)‖ ^ 2) +
      2 * ∫ r in (0:ℝ)..1, ‖fderiv ℝ u (x + r • e) e‖ ^ 2 := by
  have hc : Continuous (dw [e] u) := (contDiff_dw [e] hu).continuous
  have := GlobalTheory.sobolev_endpoint_one_variable ℂ (fun r : ℝ => u (x + r • e))
    (fun r : ℝ => fderiv ℝ u (x + r • e) e) 1 one_pos (fun t _ => hasDerivAt_line hu x e t)
    (hc.comp (f := fun r : ℝ => x + r • e) (by fun_prop)).continuousOn
  simpa using this

theorem sobolev_haar [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {D : ℕ} (b : Module.Basis (Fin D) ℝ V) :
    ∃ C : ℝ, ∀ g : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ S : ENNReal,
      (∀ l : List (Fin D), l.length ≤ D → ∫⁻ y, ‖dw (l.map b) g y‖ₑ ^ 2 ∂μ ≤ S) →
      ‖g 0‖ₑ ^ 2 ≤ ENNReal.ofReal C * S := by
  let T : (Fin D → ℝ) ≃L[ℝ] V := b.equivFunL.symm
  have hT : ∀ t, T t = ∑ i, t i • b i := fun t => b.equivFun_symm_apply t
  let ν : Measure V := Measure.map T volume
  haveI : ν.IsAddHaarMeasure := T.isAddHaarMeasure_map _
  let c : ℝ≥0 := Measure.addHaarScalarFactor ν μ
  have hν : ν = c • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  refine ⟨4 ^ D * (c + 1), fun g hg S hS => ?_⟩
  have hpos : (0:ℝ) < 4 ^ D * (c + 1) := by positivity
  rcases eq_or_ne S ⊤ with rfl | hS'
  · rw [ENNReal.mul_top (by simpa using hpos)]; exact le_top
  have key := GlobalTheory.ThetaGrowth.sobolev_iter D 0 (fun i r => r • b i)
    (fun p => {u | ∃ l : List (Fin D), l.length ≤ p ∧ u = dw (l.map b) g}) (c * S.toReal) (0 : V)
    (fun i => by fun_prop)
    (fun p q hpq u ⟨l, hl, hu⟩ => ⟨l, hl.trans hpq, hu⟩)
    (by
      rintro p u ⟨l, hl, rfl⟩
      refine ⟨(contDiff_dw _ hg).continuous, fun i => ⟨dw ((i :: l).map b) g,
        ⟨i :: l, by simpa using hl, rfl⟩, fun x => ?_⟩⟩
      exact step (contDiff_dw _ hg) x (b i))
    (by
      rintro u ⟨l, hl, rfl⟩
      have hcu : Continuous (dw (l.map b) g) := (contDiff_dw _ hg).continuous
      have h1 := hS l (by simpa using hl)
      set u := dw (l.map b) g
      simp only [zero_add, ← hT]
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
        (Continuous.aestronglyMeasurable (by fun_prop))]
      have h2 : ∫⁻ t in Set.univ.pi fun _ => Set.Icc (0:ℝ) 1, ENNReal.ofReal (‖u (T t)‖ ^ 2)
          ≤ c * S := by
        calc _ ≤ ∫⁻ t, ENNReal.ofReal (‖u (T t)‖ ^ 2) := setLIntegral_le_lintegral _ _
          _ = ∫⁻ t, ‖u (T t)‖ₑ ^ 2 := by
            refine lintegral_congr fun t => ?_
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
          _ = ∫⁻ y, ‖u y‖ₑ ^ 2 ∂ν := by
            rw [lintegral_map (hcu.measurable.enorm.pow_const 2) T.continuous.measurable]
          _ = c * ∫⁻ y, ‖u y‖ₑ ^ 2 ∂μ := by
            rw [hν, lintegral_smul_measure]; rfl
          _ ≤ c * S := by gcongr
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hS') h2
      simpa using this)
    g ⟨[], le_rfl, rfl⟩
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_toReal hS', ← ENNReal.ofReal_mul hpos.le]
  refine ENNReal.ofReal_le_ofReal (key.trans ?_)
  rw [mul_assoc]
  gcongr
  linarith

theorem exists_small_basis [FiniteDimensional ℝ V] :
    ∃ (D : ℕ) (b : Module.Basis (Fin D) ℝ V), ∀ i, ‖b i‖ ≤ 1 := by
  let b := Module.finBasis ℝ V
  have h : ∀ i, (‖b i‖⁻¹ : ℝ) ≠ 0 := fun i => inv_ne_zero (norm_ne_zero_iff.2 (b.ne_zero i))
  refine ⟨_, b.unitsSMul fun i => Units.mk0 _ (h i), fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 (b.ne_zero i))]

end General

open GlobalTheory.SobClass

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem contDiff_slice {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (x : κ → AF F) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => Φ (x + archInc F y) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    have e : (fun y => pureA F f g (x + archInc F y)) = fun y =>
        f ((fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1) + y) *
          g (fun i => (x i).2) := by
      funext y
      unfold pureA
      congr 2
      · funext i
        change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 +
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = _
        rw [map_add, RingEquiv.apply_symm_apply]; rfl
      · funext i
        change (x i).2 + (archInc F y i).2 = _
        rw [archInc_snd, add_zero]
    rw [e]
    exact ((f.smooth ⊤).comp (contDiff_const.add contDiff_id)).mul contDiff_const
  | zero => exact contDiff_const
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul a Φ _ h => exact contDiff_const.mul h

theorem realAd_smul_archInc (t : ℝ) (e : κ → mixedEmbedding.mixedSpace F) :
    realAd F t • archInc F e = archInc F (t • e) := by
  funext i
  refine Prod.ext ?_ ?_
  · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (e i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e i)
    rw [← map_mul, Algebra.smul_def]
  · change (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    rw [mul_zero]

theorem word_slice (ψ : AddChar (AF F) ℂ) {Φ : (κ → AF F) → ℂ} (x : κ → AF F)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) fun y => Φ (x + archInc F y))
    (l : List (κ → mixedEmbedding.mixedSpace F)) :
    (fun y => wordH ψ (l.map fun e => (archInc F e, 0)) Φ (x + archInc F y)) =
      dw l fun y => Φ (x + archInc F y) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    funext y
    have h := (hasDerivAt_line (contDiff_dw l hΦ) y e 0).deriv
    rw [zero_smul, add_zero] at h
    refine Eq.trans ?_ h
    change deriv (fun t : ℝ => schr ψ (realAd F t • (archInc F e, 0))
      (wordH ψ (l.map fun e => (archInc F e, 0)) Φ) (x + archInc F y)) 0 = _
    congr 1
    funext t
    rw [← ih]
    simp only [schr, Prod.smul_mk, smul_zero, dotProduct_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul, realAd_smul_archInc, archInc_add, add_assoc]

theorem slice_sobolev : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (L : Finset (List ((κ → AF F) × (κ → AF F)))) (D : ℕ) (C : ℝ), (∀ l ∈ L, l.length ≤ D ∧ ∀ w ∈ l, IsArchUnit w) ∧ ∀ Φ ∈ schA F κ, ∀ x : κ → AF F, ‖Φ x‖ₑ ^ 2 ≤ ENNReal.ofReal C * ∑ l ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l Φ (x + GlobalTheory.SobClass.archInc F y)‖ₑ ^ 2 := by
  intro F _ _ κ _ ψ _
  obtain ⟨D, b, hb⟩ := exists_small_basis (V := κ → mixedEmbedding.mixedSpace F)
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  haveI : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  haveI : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  obtain ⟨C, hC⟩ := sobolev_haar (volume : Measure (κ → mixedEmbedding.mixedSpace F)) b
  let L₀ : Finset (List (Fin D)) := (List.finite_length_le (Fin D) D).toFinset
  refine ⟨L₀.image fun l => (l.map b).map fun e => (archInc F e, 0), D, C, ?_, ?_⟩
  · intro l hl
    obtain ⟨l, hl', rfl⟩ := Finset.mem_image.1 hl
    refine ⟨by simpa [L₀] using hl', fun w hw => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
    exact isArchUnit_der _ fun i => (norm_le_pi_norm _ i).trans (hb j)
  · intro Φ hΦ x
    have h0 : archInc F (0 : κ → mixedEmbedding.mixedSpace F) = 0 := by
      have := archInc_add (F := F) (κ := κ) 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    have := hC _ (contDiff_slice hΦ x) (∑ l ∈ L₀.image fun l => (l.map b).map
        fun e => ((archInc F e, 0) : (κ → AF F) × (κ → AF F)),
        ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l Φ (x + archInc F y)‖ₑ ^ 2)
      (fun l hl => by
        rw [← word_slice ψ x (contDiff_slice hΦ x)]
        exact Finset.single_le_sum (f := fun l => ∫⁻ y : κ → mixedEmbedding.mixedSpace F,
          ‖wordH ψ l Φ (x + archInc F y)‖ₑ ^ 2) (fun _ _ => zero_le)
          (Finset.mem_image_of_mem _ (by simpa [L₀] using hl)))
    simpa only [h0, add_zero] using this

end GlobalTheory.SliceSob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadEndomorphismTorsionSectionEqSpecialisationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spread_endomorphism_torsion_section_eq_specialisation : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ → IsMonHom f₀ → σ ≫ pullback.fst _ _ = 𝟙 _ → σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom → f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ → ∀ (N : ℕ), (N : k₀) ≠ 0 → ∀ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 → ∀ c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)), c ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left → c ≫ pullback.snd _ _ = 𝟙 _ → c ≫ Ψ.left ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left := by
  first | exact @GlobalTheory.TorsCmp.torsion_section_eq | exact GlobalTheory.TorsCmp.torsion_section_eq | (intros; apply GlobalTheory.TorsCmp.torsion_section_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharArchimedeanEqExpNondegenerate
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.StdBeta

theorem at_arch (F : Type) [Field F] [NumberField F] (a : mixedEmbedding.mixedSpace F) :
    At (M := AF F) (evI F) (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · exact mul_zero u.2

theorem evI_arch (F : Type) [Field F] [NumberField F] (a : mixedEmbedding.mixedSpace F) :
    evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) = a :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

theorem stdBeta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧ ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 := by
  intro F _ _ ψ hψ
  refine ⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun a => ?_, fun a ha => ?_⟩
  · rw [hψ.2.2 _ (at_arch F a), evI_arch]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg]
    ring_nf
  · by_contra h
    push_neg at h
    exact ha (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace a fun b => by
      have := h b
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      exact this)

end GlobalTheory.StdBeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharContinuousNontrivialStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_char_continuous_nontrivial : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    Continuous (psiLoc ψ v) ∧ ∃ x : Fv F v, psiLoc ψ v x ≠ 1 := by
  first | exact @GlobalTheory.PsiLocal.psi_loc_main | exact GlobalTheory.PsiLocal.psi_loc_main | (intros; apply GlobalTheory.PsiLocal.psi_loc_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlaneStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_restricted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E)
    (ι : Matrix (Fin d) (Fin d₁) E), ιᵀ * JW * ι.map σ = JW₁ → ∀ z z' : Matrix (Fin n) (Fin d₁) (AE F E),
      symp (cA σ) (-1) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι)ᵀ)
        (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F ι)ᵀ) = symp (cA σ) (-1) (incM F JX) (incM F JW₁) z z' := by
  first | exact @GlobalTheory.MixedLagrGram.symp_restrict_gram | exact GlobalTheory.MixedLagrGram.symp_restrict_gram | (intros; apply GlobalTheory.MixedLagrGram.symp_restrict_gram <;> assumption)
end

