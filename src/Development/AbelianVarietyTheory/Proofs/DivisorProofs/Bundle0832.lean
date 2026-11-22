import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodFrobeniusTwist
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFieldExistsSqrtNegDiscr
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_sq_eq_neg_of_discr_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  classical
  intro K _ _ d h2 hd
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := inferInstance
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[ℚ] K)).1 hcard
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, σ} := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hy : y = 1
    · exact Or.inl hy
    · exact Or.inr (huniq y hy)
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x := by
    intro x
    rw [_root_.trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hσ)]
    rfl
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (integralBasis K), h2])
  let b : Fin 2 → K := fun i => integralBasis K (e.symm i)
  have hb : ⇑(integralBasis K) ∘ ⇑e.symm = b := rfl
  have key : algebraMap ℚ K (discr K : ℚ) = (b 0 * σ (b 1) - b 1 * σ (b 0)) ^ 2 := by
    rw [coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, hb, Algebra.discr_def,
      Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, htr]
    ring
  refine ⟨b 0 * σ (b 1) - b 1 * σ (b 0), ?_⟩
  rw [← key, hd]
  push_cast
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodFrobeniusTwistStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_period_frobenius_twist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod F.θ t (frob p F.s f) (F.σ y) := by
  first | exact @GlobalTheory.QLog.hasPeriod_frob | exact GlobalTheory.QLog.hasPeriod_frob | (intros; apply GlobalTheory.QLog.hasPeriod_frob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSuccessiveApproximationStepStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_successive_approximation_step : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ (N : ℕ) (f : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → f ∈ quasiInt p k (Fin d) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w)) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ f - h ∈ quasiInt p k (Fin d) ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  first | exact @GlobalTheory.Katz.quasiLog_approx_step | exact GlobalTheory.Katz.quasiLog_approx_step | (intros; apply GlobalTheory.Katz.quasiLog_approx_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionSplitOfIsotropicNormStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_split_of_isotropic_norm : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∃ φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F, ∀ x, (φ x).det = nrm x := by
  first | exact @GlobalTheory.quaternion_split_of_isotropic | exact GlobalTheory.quaternion_split_of_isotropic | (intros; apply GlobalTheory.quaternion_split_of_isotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDetIdealSelfDualNormOneStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relDetIdeal_selfDual_normOne : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  first | exact @GlobalTheory.SelfDualDetNorm.detId_normOne | exact GlobalTheory.SelfDualDetNorm.detId_normOne | (intros; apply GlobalTheory.SelfDualDetNorm.detId_normOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexOfLeNsmul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.HalfReps

section Group

variable {H : Type} [AddCommGroup H] [Module ℚ H] [Module.Finite ℚ H]

theorem relIndex_nsmul (Λ : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c) :
    (Λ.map (nsmulAddMonoidHom c)).relIndex Λ ≠ 0 ∧
      (Λ.map (nsmulAddMonoidHom c)).relIndex Λ ≤ c ^ Module.finrank ℚ H := by
  have : IsAddTorsionFree H := IsAddTorsionFree.of_module_rat H
  have : Module.Finite ℤ Λ.toIntSubmodule := hΛ
  have : Module.Free ℤ Λ.toIntSubmodule := inferInstance
  rw [AddSubgroup.relIndex_map_nsmul]
  refine ⟨pow_ne_zero _ hc.ne', Nat.pow_le_pow_right hc ?_⟩
  have hb := (Module.finBasis ℤ Λ.toIntSubmodule).linearIndependent.map' Λ.toIntSubmodule.subtype
    (Submodule.ker_subtype _)
  have := ((LinearIndependent.iff_fractionRing ℤ ℚ).1 hb).fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  exact this

theorem relIndex_of_nsmul_le (Λ B : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c)
    (hB : ∀ x ∈ B, c • x ∈ Λ) : Λ.relIndex B ≠ 0 ∧ Λ.relIndex B ≤ c ^ Module.finrank ℚ H := by
  have : IsAddTorsionFree H := IsAddTorsionFree.of_module_rat H
  obtain ⟨h0, h1⟩ := relIndex_nsmul Λ hΛ hc
  have hle : B.map (nsmulAddMonoidHom c) ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := nsmulAddMonoidHom c) Λ B (nsmul_right_injective hc.ne')]
  exact ⟨fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_right hle h),
    (AddSubgroup.relIndex_le_of_le_right hle h0).trans h1⟩

theorem relIndex_of_le_nsmul (Λ A B : AddSubgroup H) (hΛ : Module.Finite ℤ Λ) {c : ℕ} (hc : 0 < c)
    (hB : ∀ x ∈ Λ, c • x ∈ B) : B.relIndex (Λ ⊓ A) ≠ 0 := by
  obtain ⟨h0, -⟩ := relIndex_nsmul Λ hΛ hc
  have hle : Λ.map (nsmulAddMonoidHom c) ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hB x hx
  exact fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle
    (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h))

end Group

section Twist

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W]

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) :
    y ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  simp [twist₂, Submodule.mem_iInf]

theorem nsmul_mem_twO (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ}
    (he : ∀ Q, e Q ≤ 1) {x : W} (hx : x ∈ M) : c • x ∈ twist₂ M c e := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine (mem_twO M c e _).2 fun Q => GlobalTheory.ThetaMove.mem_localization_of_mem Q ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 1 - e Q by have := he Q; omega)
  have : ((c : E) ^ e Q)⁻¹ • c • x = (c ^ m) • x := by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← zpow_natCast, ← hm,
      zpow_sub₀ hcE, zpow_one, div_eq_inv_mul]
  rw [this]
  exact nsmul_mem hx _

theorem nsmul_mem_of_twO (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c) {e : HeightOneSpectrum (𝓞 E) → ℤ}
    (he : ∀ Q, -1 ≤ e Q) {x : W} (hx : x ∈ twist₂ M c e) : c • x ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine GlobalTheory.ThetaMove.mem_of_locP fun Q => ?_
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 1 + e Q by have := he Q; omega)
  have : c • x = (c ^ m) • ((c : E) ^ e Q)⁻¹ • x := by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← zpow_natCast, ← hm,
      zpow_add₀ hcE, zpow_one, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hcE), mul_one]
  rw [this]
  exact nsmul_mem ((mem_twO M c e x).1 hx Q) _

end Twist

theorem half_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (dl : ℂ) (AA : Submodule (𝓞 E) E) (S : Finset (HeightOneSpectrum (𝓞 E))) (L : Submodule (𝓞 E) (Sp E a)) (L' : Submodule (𝓞 E) (Sp E b)) (c : ℕ), dl ≠ 0 → AA.FG → Submodule.IsLattice E L → Submodule.IsLattice E L' → 0 < c → Formalism.L2.Th1.H.IsReps (BC emb dl AA S L L' c) (LamC emb dl AA L L' ⊓ AC emb dl AA S L L' c) (repsOf (BC emb dl AA S L L' c) (LamC emb dl AA L L' ⊓ AC emb dl AA S L L' c)) ∧ Formalism.L2.Th1.H.IsReps (LamC emb dl AA L L') (BC emb dl AA S L L' c) (repsOf (LamC emb dl AA L L') (BC emb dl AA S L L' c)) ∧ (repsOf (LamC emb dl AA L L') (BC emb dl AA S L L' c)).card ≤ c ^ (Module.finrank ℚ E * a * b) := by
  intro E _ _ _ ι _ _ a b emb dl AA S L L' c hdl hA hL hL' hc
  have hinj := GlobalTheory.ThetaMove.embH_injective (a := a) (b := b) emb hdl
  have hfg : (perO AA L L').FG :=
    GlobalTheory.ThetaMove.VolumePos.perO_fg hA (GlobalTheory.ThetaMove.VolumePos.homO_fg hL.fg hL'.fg hL.span_eq_top)
  have : Module.Finite (𝓞 E) (perO AA L L') := Module.Finite.iff_fg.2 hfg
  have hfin : Module.Finite ℤ (perO AA L L') := Module.Finite.trans (𝓞 E) _
  have : Module.Finite ℚ (Formalism.L2.Col.HomE E a b) := Module.Finite.trans E _
  have hrk : Module.finrank ℚ (Formalism.L2.Col.HomE E a b) = Module.finrank ℚ E * a * b := by
    rw [← Module.finrank_mul_finrank ℚ E, Module.finrank_linearMap]
    simp [mul_assoc]
  have h1 := relIndex_of_le_nsmul (perO AA L L').toAddSubgroup (halfAO S (perO AA L L') c).toAddSubgroup
    (halfBO S (perO AA L L') c).toAddSubgroup hfin hc
    (fun x hx => nsmul_mem_twO _ hc (fun Q => (GlobalTheory.ThetaMove.expS_bound S Q).2) hx)
  have h2 := relIndex_of_nsmul_le (perO AA L L').toAddSubgroup
    (halfBO S (perO AA L L') c).toAddSubgroup hfin hc
    (fun x hx => nsmul_mem_of_twO _ hc (fun Q => (GlobalTheory.ThetaMove.expS_bound S Q).1) hx)
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.map_inf _ _ _ hinj] at h1
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hrk] at h2
  have r2 := Classical.epsilon_spec (GlobalTheory.RepsMod.exists_reps _ _ h2.1)
  refine ⟨Classical.epsilon_spec (GlobalTheory.RepsMod.exists_reps _ _ h1), r2, ?_⟩
  exact (GlobalTheory.RepsMod.card_reps _ _ _ r2).le.trans h2.2

end GlobalTheory.ColNorms.HalfReps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDetStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_mul_vandermonde_det_eq_det : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → GlobalTheory.JSW.schur n l * Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) = Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  first | exact @GlobalTheory.JSW.schur_mul_det_eq_det | exact GlobalTheory.JSW.schur_mul_det_eq_det | (intros; apply GlobalTheory.JSW.schur_mul_det_eq_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem embedsBy_fA_of_isBCBasis (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ)
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (hB : IsAbelianScheme B) (hM : M.IsLB) (_hk : 1 ≤ k)
    (hVA : VeryAmpleAt B M k) (hb : IsBCBasis B M k bB) : GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB := by
  have hp : IsProper B.hom := hB.proper
  let t : Spec (CommRingCat.of Rg) ⟶ (topS Rg).left := (Sp Rg).topIso.inv
  choose b' hb' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec B M (k : ℤ) (homAt t) (bB i)
  have hspan := (hb Rg t b' hb').2
  have hE := GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) t b' hspan
  have hS := fun i => GlobalTheory.SpanFrame.secScal_of_isPullSec B hM (k : ℤ) (homAt t) (hb' i)
  haveI : IsIso (homAt t) := by
    haveI : IsIso ((Over.forget _).map (homAt t)) := by change IsIso t; infer_instance
    exact isIso_of_reflects_iso (homAt t) (Over.forget _)
  haveI : IsIso (homAt t ▷ B).left := inferInstanceAs (IsIso ((Over.forget _).map (homAt t ▷ B)))
  haveI : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of Rg)))
  have hw : (homAt t ▷ B).left ≫ fA B = (fst (baseAt t) B).left ≫ 𝟙 _ := by
    have e1 := Over.w (homAt t ▷ B)
    have e2 := Over.w (fst (baseAt t) B)
    have e3 : (baseAt t).hom = 𝟙 _ := by simp [baseAt, t, baseOver]
    rw [Category.comp_id, fA, e1, ← e2, e3, Category.comp_id]
  have sq : IsPullback (inv (homAt t ▷ B).left) (fA B) (fst (baseAt t) B).left (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, Category.comp_id, hw, Category.comp_id]
  exact GlobalTheory.AmpleSpan.EmbedsBy.secScal hM sq hE
    fun i => GlobalTheory.AmpleSpan.secScal_symm hM (hS i) (IsIso.inv_hom_id _)

example : ∀ (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → 1 ≤ k → VeryAmpleAt B M k → IsBCBasis B M k bB → GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB :=
  embedsBy_fA_of_isBCBasis

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsCuspDivisibleDegree
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_lift_kills_cusp_divisible_degree : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n) := by
  first | (exact @GlobalTheory.Shin.shLift_cusp_kills_J) | (exact GlobalTheory.Shin.shLift_cusp_kills_J) | (intros; apply GlobalTheory.Shin.shLift_cusp_kills_J  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWhittakerTorusHeckeRecursionStatement
section
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalWhittaker_torus_hecke_recursion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w n, W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w n) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) i))) = (Finset.univ.val.map fun i => (α i : ℂ)).esymm j * ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i))) := by
  first | exact @GlobalTheory.WhittakerRecursion.recursion | exact GlobalTheory.WhittakerRecursion.recursion | (intros; apply GlobalTheory.WhittakerRecursion.recursion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormClassSumMatrixLeCauchySchwarz
section
noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mat_opOf_apply {F F' : GFam K} (M : GFam.Mat F F') (hF : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) (b' : F'.β)
    (d' : F'.D b') :
    ((M.opOf hF s φ b' : (F'.mem b').EqFun) : F'.D b' → F'.V) d' =
      ∑ b, (M b b').appOf (hF b) (s b) (φ b : (F.mem b).D → F.V) d' := by
  simp only [GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem step_le (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t h h' : ℝ)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hh' : 0 ≤ h') (hp : ∀ b, PosAt ((Q.F i).mem b) v) (hp' : ∀ b, PosAt ((Q.F (i + 1)).mem b) v)
    (hc : ∀ b, (Nat.card ((Q.F i).mem b).Cl : ℝ) ≤ h) (hc' : ∀ b, (Nat.card ((Q.F (i + 1)).mem b).Cl : ℝ) ≤ h')
    (hk : ∀ b b' d d', OpLe ((Q.F i).mem b) ((Q.F (i + 1)).mem b') v ((Q.kk i b b').k d d') t) (φ : (Q.F i).Forms) :
    (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (Fintype.card (Q.F (i + 1)).β : ℝ) * h * h' * t *
        (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
  have hN : (famIpAt (Q.F i) (Q.hF i) v φ φ).re =
      ∑ b, (((Q.F i).mem b).ipAt (Q.hF i b) v (φ b : ((Q.F i).mem b).D → (Q.F i).V) (φ b : ((Q.F i).mem b).D → (Q.F i).V)).re := by
    unfold famIpAt
    rw [Complex.re_sum]
  have hN0 : 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
    rw [hN]
    exact Finset.sum_nonneg fun b _ => ipAt_self_nonneg _ v _ (hp b) _
  have hB : ∀ b' d', (((Q.F (i + 1)).mem b').pairAt v ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')
      ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by
    intro b' d'
    have e := mat_opOf_apply (Q.kk i) (Q.hF i) (fun b => ((Q.F i).mem b).outSec) φ b' d'
    change ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d') = _ at e
    rw [e]
    refine (pairAt_sum_le ((Q.F (i + 1)).mem b') v (hp' b') _ _).trans ?_
    rw [Finset.card_univ, hN, Finset.mul_sum _ _ t, Finset.mul_sum _ _ h]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity)
    refine (appOf_le v (Q.kk i b b') (Q.hF i b) (hp b) (hp' b') t ht _ d' fun d => hk b b' d d').trans ?_
    exact mul_le_mul_of_nonneg_right (hc b) (mul_nonneg ht (ipAt_self_nonneg _ v _ (hp b) _))
  have hB0 : 0 ≤ (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by positivity
  calc (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re
      ≤ ∑ _b' : (Q.F (i + 1)).β, h' * ((Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re))) := by
        rw [famIpAt, Complex.re_sum]
        refine Finset.sum_le_sum fun b' _ => ?_
        exact (ipAt_self_le _ v _ (hp' b') _ _ (hB b')).trans (mul_le_mul_of_nonneg_right (hc' b') hB0)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end GlobalTheory.ColNorms.SumBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableKerRepsAddSub
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mulStable_intCast_add {L : PeriodPair} {w : ℂ} (a : ℤ) (h : MulStable L w) :
    MulStable L ((a : ℂ) + w) := by
  intro ω hω
  rw [add_mul]
  refine add_mem ?_ (h ω hω)
  have : ((a : ℂ) * ω) = a • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact zsmul_mem hω a

theorem mulStable_intCast_sub {L : PeriodPair} {w : ℂ} (a : ℤ) (h : MulStable L w) :
    MulStable L ((a : ℂ) - w) := by
  intro ω hω
  rw [sub_mul]
  refine sub_mem ?_ (h ω hω)
  have : ((a : ℂ) * ω) = a • ω := by rw [zsmul_eq_mul]
  rw [this]
  exact zsmul_mem hω a

theorem ringEquiv_sqrtNegNat (σ : ℂ ≃+* ℂ) (p : ℕ) :
    σ (sqrtNegNat p) = sqrtNegNat p ∨ σ (sqrtNegNat p) = -sqrtNegNat p := by
  have h : σ (sqrtNegNat p) ^ 2 = sqrtNegNat p ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

theorem stable_kerReps_add_sub : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (a : ℤ) (S S' : Finset ℂ), L.g₂ ∈ F → L.g₃ ∈ F → MulStable L (sqrtNegNat p) → IsKerReps L (a + sqrtNegNat p) S → IsKerReps L (a - sqrtNegNat p) S' → Stable L F (Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ))) := by
  intro p F L a S S' h2 h3 hm hS hS' σ hσ
  have e2 : L.g₂ = σ L.g₂ := (hσ _ h2).symm
  have e3 : L.g₃ = σ L.g₃ := (hσ _ h3).symm
  have mp := mulStable_intCast_add a hm
  have mm := mulStable_intCast_sub a hm
  have hσa : σ (a : ℂ) = a := map_intCast σ a
  rcases ringEquiv_sqrtNegNat σ p with hs | hs
  · have hp : σ ((a : ℂ) + sqrtNegNat p) = (a : ℂ) + sqrtNegNat p := by rw [map_add, hσa, hs]
    have hm' : σ ((a : ℂ) - sqrtNegNat p) = (a : ℂ) - sqrtNegNat p := by rw [map_sub, hσa, hs]
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S S e2 e3 mp hS (by rw [hp]; exact hS)
    obtain ⟨e', he'⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S' S' e2 e3 mm hS' (by rw [hm']; exact hS')
    refine ⟨Equiv.sumCongr e e', ?_⟩
    rintro (t | t)
    · exact he t
    · exact he' t
  · have hp : σ ((a : ℂ) + sqrtNegNat p) = (a : ℂ) - sqrtNegNat p := by
      rw [map_add, hσa, hs, sub_eq_add_neg]
    have hm' : σ ((a : ℂ) - sqrtNegNat p) = (a : ℂ) + sqrtNegNat p := by
      rw [map_sub, hσa, hs, sub_neg_eq_add]
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S S' e2 e3 mp hS (by rw [hp]; exact hS')
    obtain ⟨e', he'⟩ := GlobalTheory.T.exists_kernel_equiv_conjugate_points L σ _ S' S e2 e3 mm hS' (by rw [hm']; exact hS)
    refine ⟨(Equiv.sumCongr e e').trans (Equiv.sumComm _ _), ?_⟩
    rintro (t | t)
    · exact he t
    · exact he' t

end GlobalTheory.CMModel
end

