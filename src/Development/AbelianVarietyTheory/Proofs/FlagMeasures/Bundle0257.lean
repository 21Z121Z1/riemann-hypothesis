import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0248
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0243
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0056
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundOfMomentsStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLengthTailBound_of_moments : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r)) (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (q : ℕ) (H₁ : ℝ), inWb k r z → 0 < H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → (∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) → TailBd z νS Φ q H₁ := by
  first | exact @GlobalTheory.Amp.TailTwo.tailBd_of_moments | exact GlobalTheory.Amp.TailTwo.tailBd_of_moments | (intros; apply GlobalTheory.Amp.TailTwo.tailBd_of_moments <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundPrimedOfUnprimedStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  first | exact @GlobalTheory.TypeAsm.tailBd_primed_of_unprimed | exact GlobalTheory.TypeAsm.tailBd_primed_of_unprimed | (intros; apply GlobalTheory.TypeAsm.tailBd_primed_of_unprimed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCoeffMulInnerBesselFunctionalEqIntegral
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem coef_mul_inner_Afun_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ y : Mt k r, Matrix.of y ∈ GG k r → coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have hu₂ : σ (Matrix.of y) u₁ ∈ DD σ w := hstab _ hy u₁ hu₁
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab
    hStd.2.2.2.2.2.2.2.1 _ hu₂ v hv).1
  have hint2 := hint.apply_continuousLinearMap ξ
  have hA : Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y) =
      ∫ s, (coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ ∂μS := by
    unfold Afun be
    exact ContinuousLinearMap.integral_apply hint ξ
  have hinner : ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ s, ⟪(coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ, ξ⟫_ℂ ∂μS := by
    rw [hA, ← inner_conj_symm, ← integral_inner hint2, ← integral_conj]
    congr 1; funext s; rw [inner_conj_symm]
  rw [hinner, ← integral_const_mul]
  have hS0 : μS {x | Matrix.of x ∉ Sset k r z} = 0 := hSide.2.2.2.1.2.2.1
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hS0
  filter_upwards [hae] with s hs
  have hmul : σ (Matrix.of s * Matrix.of y) = (σ (Matrix.of s)).comp (σ (Matrix.of y)) :=
    hStd.2.1.1.2 _ (hSG hs) _ hy
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left]
  have hc : coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) = coef σ u₁ v (Matrix.of s * Matrix.of y) := by
    simp only [coef, hmul, ContinuousLinearMap.comp_apply]
  rw [hc, mul_assoc]
  rfl

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCmStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (j : ℕ) (x : E), (x ∈ dInv E j ∧ imV x = 0) ↔ ∃ y ∈ dInv F j, algebraMap F E y = x := by
  first | exact @GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff | exact GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff | (intros; apply GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLieEUnitaryGroupIffOfInvolutiveStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lieE_unitaryGroup_iff_of_involutive : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)), H * H = 1 → (x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0) := by
  first | exact @GlobalTheory.TubeLie.mem_lieE_UH_of_sq | exact GlobalTheory.TubeLie.mem_lieE_UH_of_sq | (intros; apply GlobalTheory.TubeLie.mem_lieE_UH_of_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodular
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.StabMeas
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RootMeas

theorem normR_facts : ∀ (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → NormR k r γ s μR → IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ NormR k r γ⁻¹ s (μR.map (conjM γ)) := by
  rintro k r γ s μR hs ⟨n₁, h₁, n₂, h₂, g₀, β, hg, rfl, rfl⟩
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  obtain ⟨-, -, b1, b2, a3, c1⟩ := GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular k r g₀ β hg
  have hγ : n₁ * g₀ * n₂ ∈ GG k r :=
    isClosedSub_GG.2.2.2.1 _ (isClosedSub_GG.2.2.2.1 _ (n1 h₁) _ hg.1) _ (n1 h₂)
  have hinv : (n₁ * g₀ * n₂)⁻¹ = n₂⁻¹ * g₀⁻¹ * n₁⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  obtain ⟨d1, d2⟩ := haar_smul b1 b2 hs
  obtain ⟨e1, e2⟩ := haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ h₂))) (conj_mem_Rset h₁ h₂ g₀) d1 d2
  refine ⟨isClosedSub_Rset hγ, e1, e2, n₂⁻¹, n5 _ h₂, n₁⁻¹, n5 _ h₁, g₀⁻¹, β, a3, hinv, ?_⟩
  rw [map_conj_conj, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem_GG (n1 h₂)), ← map_conj_conj,
    Measure.map_smul, c1, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 h₁))]

end GlobalTheory.Amp.RootMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthTransversalFlagsInfIsotropicEqBot
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PerpFlags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem orth_anti {U U' : Submodule E S.V} (h : U ≤ U') : orth S U' ≤ orth S U := fun v hv =>
  (mem_orth _ _).2 fun x hx => (mem_orth _ _).1 hv x (h hx)

theorem xplus_le {T : E} {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T)
    (M : Submodule (𝓞 E) S.V) (h1 : XLam Λ F ≤ M) (h2 : F.fl.z ∈ M) : Xplus F ≤ spanE S M := by
  refine sup_le (fun v hv => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span h2))
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hΛ v
  have h3 : d • v ∈ M := h1 ⟨hd, (toO S (Xsp F)).smul_mem d hv⟩
  have h4 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h3)
  rwa [← algebraMap_smul E d v,
    inv_smul_smul₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h4

theorem gflag_eq_zero {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c : Fin r → E) (hc : c ≠ 0)
    (h : ∀ b, S.hT (∑ a, c a • F.e a) (F'.fvec b) = 0) : Gflag F F' = 0 := by
  have hz : ∀ b, ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b = 0 := fun b => by
    have := h b
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply] at this
    simpa [Zhat, brS, FlagG.fvec] using this
  obtain ⟨a0, ha0⟩ := Function.ne_iff.1 hc
  have d1 : Dl F F' r = 0 := by
    rw [Dl, leadMinorE, dif_pos (Nat.le_succ r), ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨fun a => star (c a), fun e => ha0 (star_eq_zero.1 (congrFun e a0)), funext fun b => ?_⟩
    exact hz (Fin.castLE (Nat.le_succ r) b)
  have d2 : Dl F F' (r + 1) = 0 := by
    rw [Dl, leadMinorE, dif_pos le_rfl, ← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0, fun e => ha0 ?_, funext fun b => ?_⟩
    · simpa using congrFun e a0.castSucc
    · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc] using hz b
  simp [Gflag, d1, d2]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → Hp Λ F F' ≤ orth S (Xplus F) ∧ Hp Λ F F' ≤ orth S (Xplus F') ∧ Hp Λ F F' ⊓ Xsp F = ⊥ := by
  intro E _ _ _ S r T T' Λ F F' hΛ hF hF' hG
  have a1 : Hp Λ F F' ≤ orth S (Xplus F) := orth_anti (xplus_le hΛ F _
    (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
      (hF.2 ▸ Submodule.mem_span_singleton_self _)))))
  have a2 : Hp Λ F F' ≤ orth S (Xplus F') := orth_anti (xplus_le hΛ F' _
    (le_sup_of_le_left le_sup_right)
    (Submodule.mem_sup_right (hF'.2 ▸ Submodule.mem_span_singleton_self _)))
  refine ⟨a1, a2, eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx.2
  by_cases hc : c = 0
  · simp [hc]
  refine absurd (gflag_eq_zero F.fl F'.fl c hc fun b => ?_) hG
  refine GlobalTheory.Mass.RowPerp.swap_zero S.herm ((mem_orth _ _).1 (a2 hx.1) _ ?_)
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · rw [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.LoopC.PerpFlags
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairIsometryUniqueOnOrthModIsotropic
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.BetaUniq

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem keeps_orth {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (P : Submodule E S.V)
    (hP : ∀ x ∈ P, γ x ∈ P) : ∀ x ∈ orth S P, γ x ∈ orth S P := by
  have hle : P.map (γ : S.V →ₗ[E] S.V) ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hP x hx
  have heq : P.map (γ : S.V →ₗ[E] S.V) = P :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq γ P)
  have hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := hγ
  intro x hx
  rw [Formalism.MainNotions.mem_orth_iff] at hx ⊢
  intro y hy
  rw [← heq] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  exact (hiso y x).trans (hx y hy)

theorem exists_of_mem_gsmul {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {a : S.V}
    (h : a ∈ Ideal.span {(g : 𝓞 E)} • Λ) : ∃ l ∈ Λ, a = (g : E) • l := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨b, hb, ?_⟩
  rw [← algebraMap_smul E (g : 𝓞 E) b, map_natCast]

theorem gsmul_mem {Λ : Submodule (𝓞 E) S.V} (g : ℕ) {l : S.V} (hl : l ∈ Λ) :
    (g : E) • l ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
  rw [← map_natCast (algebraMap (𝓞 E) E) g, algebraMap_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl

theorem int_pair {Λ : Submodule (𝓞 E) S.V} (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) :
    ∀ x ∈ Λ, ∀ y ∈ Λ, S.hT x y ∈ (1 : Submodule (𝓞 E) E) := fun x hx y hy => by
  rw [← hu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
  exact hy x hx

theorem exists_sub_smul_mem_orth {r : ℕ} {T' : E} (A : LFlag S r T') (hT : T' ≠ 0) :
    ∀ x ∈ orth S (Xsp A), ∃ a : E, x - a • A.fl.z ∈ orth S (Xplus A) := by
  intro x hx
  rw [Formalism.MainNotions.mem_orth_iff] at hx
  refine ⟨S.hT A.fl.z x / (-T'), ?_⟩
  rw [Formalism.MainNotions.mem_orth_iff]
  refine Formalism.MainNotions.hT_zero_of_mem_Xplus A.fl (fun a => ?_) ?_
  · rw [map_sub, map_smul, A.fl.z_orth, smul_zero, sub_zero]
    exact hx _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [map_sub, map_smul, A.fl.z_norm, smul_eq_mul, div_mul_cancel₀ _ (neg_ne_zero.2 hT), sub_self]

end GlobalTheory.LoopC.BetaUniq

namespace GlobalTheory.LoopC.BetaUniq

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (A B : LFlag S r T')
    (β₁ β₂ : S.V ≃ₗ[E] S.V), Submodule.IsLattice E Λ → Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → 3 ≤ g → T' ≠ 0 →
    (∀ x ∈ orth S (Xplus A), x ∉ Xsp A → 0 < Algebra.trace ℚ E (S.hT x x)) →
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ A →
    XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B →
    IsAutLam S Λ β₁ → (Xsp A).map (β₁ : S.V →ₗ[E] S.V) = Xsp B → β₁ A.fl.z - B.fl.z ∈ Xsp B →
    IotaCompat Λ F A B β₁ g →
    IsAutLam S Λ β₂ → (Xsp A).map (β₂ : S.V →ₗ[E] S.V) = Xsp B → β₂ A.fl.z - B.fl.z ∈ Xsp B →
    IotaCompat Λ F A B β₂ g → ∀ x ∈ orth S (Xsp A), β₁ x - β₂ x ∈ Xsp B := by
  intro E _ _ _ S r T T' Λ g F A B β₁ β₂ hΛ hu hg hT' hpos hFA hFB h1a h1X h1z h1ι h2a h2X h2z h2ι
  have hg0 : (g : E) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hΛ₁ : ∀ x, β₁ x ∈ Λ ↔ x ∈ Λ := FrEqv.aut_mem_iff h1a
  have hΛ₂ : ∀ x, β₂ x ∈ Λ ↔ x ∈ Λ := FrEqv.aut_mem_iff h2a
  have hΛ₁' : ∀ x, β₁.symm x ∈ Λ ↔ x ∈ Λ := fun x => by
    rw [← hΛ₁ (β₁.symm x), LinearEquiv.apply_symm_apply]
  have hX₁ : ∀ x ∈ Xsp A, β₁ x ∈ Xsp B := fun x hx => h1X ▸ Submodule.mem_map_of_mem hx
  have hX₂ : ∀ x ∈ Xsp A, β₂ x ∈ Xsp B := fun x hx => h2X ▸ Submodule.mem_map_of_mem hx
  have hX₁' : ∀ y ∈ Xsp B, β₁.symm y ∈ Xsp A := fun y hy => by
    rw [← h1X] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  set δ : S.V ≃ₗ[E] S.V := β₁⁻¹ * β₂ with hδ_def
  have hδ_apply : ∀ x, δ x = β₁.symm (β₂ x) := fun x => by
    rw [hδ_def, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  have hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT := mul_mem (inv_mem h1a.1) h2a.1
  have hδX : ∀ x ∈ Xsp A, δ x ∈ Xsp A := fun x hx => by
    rw [hδ_apply]; exact hX₁' _ (hX₂ x hx)
  have hδz : δ A.fl.z - A.fl.z ∈ Xsp A := by
    have e : δ A.fl.z - A.fl.z = β₁.symm (β₂ A.fl.z - β₁ A.fl.z) := by
      rw [hδ_apply, map_sub, LinearEquiv.symm_apply_apply]
    rw [e]
    refine hX₁' _ ?_
    have := (Xsp B).sub_mem h2z h1z
    convert this using 1; abel
  have hδXp : ∀ x ∈ Xplus A, δ x ∈ Xplus A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [map_add, map_smul]
    refine (Xplus A).add_mem (Submodule.mem_sup_left (hδX a ha)) ?_
    have e : c • δ A.fl.z = c • (δ A.fl.z - A.fl.z) + c • A.fl.z := by rw [← smul_add]; congr 1; abel
    rw [e]
    exact (Xplus A).add_mem (Submodule.mem_sup_left ((Xsp A).smul_mem c hδz))
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)))
  set U : Submodule E S.V := orth S (Xplus A) with hU_def
  have hδU : ∀ x ∈ U, δ x ∈ U := keeps_orth hδ _ hδXp
  have hXU : Xsp A ≤ U := Formalism.MainNotions.X_le_orth_Xplus A.fl
  have hrad : ∀ x ∈ Xsp A, ∀ y ∈ U, S.hT x y = 0 := fun x hx y hy =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 hy x (Submodule.mem_sup_left hx)
  have hrad' : ∀ y ∈ U, ∀ x ∈ Xsp A, S.hT y x = 0 := fun y hy x hx =>
    Formalism.MainNotions.hT_swap_zero (hrad x hx y hy)
  set M : Submodule (𝓞 E) S.V := Λ ⊓ toO S U with hM_def
  have hM : ∀ x, x ∈ M ↔ x ∈ Λ ∧ x ∈ U := fun x => Iff.rfl
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have hMfg : M.FG := Submodule.FG.of_le_of_isNoetherian (T := Λ) inf_le_left
  have hint := int_pair hu
  have hUXA : U ≤ orth S (Xsp A) := fun y hy => by
    rw [Formalism.MainNotions.mem_orth_iff] at hy ⊢
    exact fun x hx => hy x (Submodule.mem_sup_left hx)

  have hcong : ∀ x ∈ M, ∃ y ∈ M, δ x - x - (g : E) • y ∈ Xsp A := by
    intro x hx
    obtain ⟨hxΛ, hxU⟩ := (hM x).1 hx

    obtain ⟨l', hl'Λ, hl'⟩ := GlobalTheory.Mass.RowPerp.exists_sub_mem S.herm S.nondeg hΛ hu (orth S (Xsp F))
      ((g : E)⁻¹ • x) (fun y hyΛ hy => by
        have hyX : y ∈ Xsp F := GlobalTheory.Mass.RowPerp.mem_of_perp_perp S.nondeg (Xsp F) y fun w hw =>
          Formalism.MainNotions.hT_swap_zero (hy w ((Formalism.MainNotions.mem_orth_iff _ _).2 hw))
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hFA (Submodule.mem_inf.2 ⟨hyΛ, hyX⟩))
        obtain ⟨l, hlΛ, rfl⟩ := exists_of_mem_gsmul ha
        obtain ⟨t, ht⟩ := Submodule.mem_one.1 (hint x hxΛ l hlΛ)
        refine Submodule.mem_one.2 ⟨t, ?_⟩
        rw [LinearMap.map_smulₛₗ S.hT, LinearMap.smul_apply, map_add, map_smul,
          hrad' x hxU b (Submodule.mem_inf.1 hb).2, add_zero, starRingEnd_apply, star_inv₀, star_natCast,
          smul_eq_mul, smul_eq_mul, ht, inv_mul_cancel_left₀ hg0])
    set l : S.V := x - (g : E) • l' with hl_def
    have hlΛ : l ∈ Λ := by
      rw [hl_def, ← map_natCast (algebraMap (𝓞 E) E) g, algebraMap_smul]
      exact Λ.sub_mem hxΛ (Λ.smul_mem _ hl'Λ)
    have hlF : l ∈ Lrep Λ F := by
      refine Submodule.mem_inf.2 ⟨hlΛ, ?_⟩
      have e : l = (g : E) • ((g : E)⁻¹ • x - l') := by
        rw [hl_def, smul_sub, smul_smul, mul_inv_cancel₀ hg0, one_smul]
      rw [e]
      exact (orth S (Xsp F)).smul_mem _ hl'
    have hlx : l - x ∈ NgX Λ g F A := by
      have e : l - x = (g : E) • (-l') := by rw [hl_def, smul_neg]; abel
      rw [e]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (gsmul_mem g (Λ.neg_mem hl'Λ)))
    have hxA : x ∈ Lrep Λ A := Submodule.mem_inf.2 ⟨hxΛ, hUXA hxU⟩
    have hb1 : l - β₁ x ∈ NgX Λ g F B := (h1ι x hxA l hlF).1 hlx
    have hb2 : l - β₂ x ∈ NgX Λ g F B := (h2ι x hxA l hlF).1 hlx
    have hdiff : β₂ x - β₁ x ∈ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B := by
      have hle : NgX Λ g F B ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ B :=
        sup_le (sup_le le_sup_left hFB) le_sup_right
      have := (NgX Λ g F B).sub_mem hb1 hb2
      refine hle ?_
      convert this using 1; abel
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hdiff
    obtain ⟨lam, hlam, rfl⟩ := exists_of_mem_gsmul ha
    have hbA : β₁.symm b ∈ Xsp A := hX₁' b (Submodule.mem_inf.1 hb).2
    have key : δ x - x - (g : E) • β₁.symm lam = β₁.symm b := by
      have e : b = (β₂ x - β₁ x) - (g : E) • lam := by rw [← hab]; abel
      rw [e, map_sub, map_sub, map_smul, LinearEquiv.symm_apply_apply, hδ_apply]
    refine ⟨β₁.symm lam, (hM _).2 ⟨(hΛ₁' lam).2 hlam, ?_⟩, ?_⟩
    · have e : β₁.symm lam = (g : E)⁻¹ • (δ x - x - β₁.symm b) := by
        rw [← key, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hg0, one_smul]
      rw [e]
      exact U.smul_mem _ (U.sub_mem (U.sub_mem (hδU x hxU) hxU) (hXU hbA))
    · rw [key]; exact hbA
  have hmain : ∀ x ∈ M, δ x - x ∈ Xsp A :=
    GlobalTheory.isom_sub_mem_of_congr E S.V S.hT U (Xsp A) M δ g S.herm hXU hrad hpos hMfg
      (fun x hx => ((hM x).1 hx).2) hδ hδX hg hcong

  have hext : ∀ x ∈ orth S (Xsp A), δ x - x ∈ Xsp A := by
    intro x hx
    obtain ⟨a, hy⟩ := exists_sub_smul_mem_orth A hT' x hx
    set y := x - a • A.fl.z with hy_def
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.Mass.RowPerp.exists_smul_mem hΛ y
    have hdM : d • y ∈ M := (hM _).2 ⟨hd, by
      rw [← algebraMap_smul E d y]; exact U.smul_mem _ hy⟩
    have h1 := hmain _ hdM
    rw [← algebraMap_smul E d y, map_smul, ← smul_sub] at h1
    have hyX : δ y - y ∈ Xsp A :=
      (Submodule.smul_mem_iff _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)).1 h1
    have e : δ x - x = a • (δ A.fl.z - A.fl.z) + (δ y - y) := by
      rw [hy_def, map_sub, map_smul, smul_sub]; abel
    rw [e]
    exact (Xsp A).add_mem ((Xsp A).smul_mem a hδz) hyX
  intro x hx
  have e : β₁ x - β₂ x = -(β₁ (δ x - x)) := by
    rw [hδ_apply, map_sub, LinearEquiv.apply_symm_apply, neg_sub]
  rw [e]
  exact (Xsp B).neg_mem (hX₁ _ (hext x hx))

end GlobalTheory.LoopC.BetaUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdDiffEqProdFactorial
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FormalDegreeDatum

theorem prod_diff_eq_prod_factorial (n : ℕ) :
    (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) =
      ∏ i ∈ Finset.range n, (i.factorial : ℝ) := by
  cases n with
  | zero => simp
  | succ m =>
    have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
    rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial] at h
    push_cast at h
    rw [← h]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr ?_ fun b _ => rfl
    ext b; simp

theorem inUJ_of_cayley {n : ℕ} (ε : Fin n → Bool) (P Q G : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (h1 : Pᴴ * Formalism.REAL.Jm ε * P = G) (h2 : Qᴴ * Formalism.REAL.Jm ε * Q = G) :
    Formalism.REAL.inUJ ε (Q * P⁻¹) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  unfold Formalism.REAL.inUJ
  have : (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h2, ← h1]
  have : (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, hPP]; simp

theorem fdeg_of_conj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsMulLeftInvariant]
    (σ₀ σ₁ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a : Formalism.REAL.UJ ε)
    (hc : ∀ g : Formalism.REAL.UJ ε, σ₀ (umat g) = σ₁ (umat (a * g * a⁻¹)))
    (hu : IsURepOn (UJset ε) σ₁) (d : ℝ) (hd : IsFdeg μ σ₀ d) (w : H) (hw : w ≠ 0) :
    ‖w‖ ^ 4 / ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = d := by
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hmul : ∀ g h : Formalism.REAL.UJ ε, σ₁ (umat (g * h)) w = σ₁ (umat g) (σ₁ (umat h) w) := by
    intro g h
    have := hu.1.2 _ (hmem g) _ (hmem h)
    have e : umat (g * h) = umat g * umat h := rfl
    rw [e, this]; rfl
  have hv : ‖σ₁ (umat a) w‖ = ‖w‖ := hu.2.1 _ (hmem a) w
  set v := σ₁ (umat a) w with hvdef
  have h1 : ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ := by
    rw [← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2) a]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [coefOn, hc, hvdef, ← hmul]
    rw [inv_mul_cancel_right]
  have h2 := (hd.2 v w v w).2
  have h3 : ∀ g : Formalism.REAL.UJ ε, coefOn σ₀ v w g * star (coefOn σ₀ v w g) =
      ((‖coefOn σ₀ v w g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h3] at h2
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hv] at h2
  have h4 : ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ = ‖w‖ ^ 2 * ‖w‖ ^ 2 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hd0 : d ≠ 0 := hd.1.ne'
  rw [h1, h4]
  field_simp

theorem fdeg_mul_prod_factorial : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (cd : Formalism.BasicNotions.CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal) (P : Mat k r) (d : ℝ), GlobalTheory.Mem.Vol.CdScaleIs cd sc → IsHCParam lam → IsDSHpk k r ε lam σ → IsCayley k r ε P → IsFdeg ((sc _ ε : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → d * (∏ i ∈ Finset.range (2 * r + k + 1), (i.factorial : ℝ)) = vand lam := by
  intro hF k r H _ _ _ σ ε lam cd sc P d hsc hlam hDS hP hd
  obtain ⟨Q, ⟨hQ, -⟩, hDS⟩ := hDS
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Mat k r)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ ε := ⟨u, inUJ_of_cayley ε P Q _ hP.1 hP.2 hQ.2⟩
  haveI := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have h1 := hF cd sc hsc _ ε lam hlam H _ w hDS hw
  have h2 := fdeg_of_conj ((sc _ ε : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P))
    (fun g => σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 d hd w hw
  rw [h2, prod_diff_eq_prod_factorial] at h1
  have hne : (∏ i ∈ Finset.range (2 * r + k + 1), (i.factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast i.factorial_ne_zero
  rw [h1, div_mul_cancel₀ _ hne]
  unfold vand
  refine Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun y hy => ?_
  have : x < y := (Finset.mem_filter.1 hy).2
  exact abs_of_pos (sub_pos.2 (hlam.1 this))

end GlobalTheory.FormalDegreeDatum
end

