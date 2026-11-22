import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.LocalFromCover

theorem trace_conj {p q : ℕ} {Z : Mat p q} (hZ : Z ∈ upq p q) : (starRingEnd ℂ) Z.trace = -Z.trace := by
  have h : Zᴴ * Jm p q + Jm p q * Z = 0 := hZ
  have hJ := GlobalTheory.RealPar.KStabLie.Jm_sq p q
  have h2 := congrArg (fun A => (A * Jm p q).trace) h
  simp only [add_mul, Matrix.trace_add, zero_mul, Matrix.trace_zero] at h2
  rw [mul_assoc, hJ, mul_one, Matrix.trace_mul_comm, ← mul_assoc, hJ, one_mul, Matrix.trace_conjTranspose] at h2
  exact eq_neg_of_add_eq_zero_left h2

theorem trace_reindex' {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) : (Matrix.reindex e e Z).trace = Z.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp fun a => Z a a

theorem exp_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • plainMat e Z) = plainMat e (NormedSpace.exp (t • Z)) := by
  have h : t • plainMat e Z = Matrix.reindex e e (t • Z) := by
    ext a b; simp [plainMat]
  rw [h]
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) (t • Z)).symm

theorem exp_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (Z : Mat p q) (t : ℝ) :
    NormedSpace.exp (t • barMat e Z) = barMat e (NormedSpace.exp (t • Z)) := by
  have h0 : ∀ A : Mat p q, A.map (starRingEnd ℂ) = Aᴴᵀ := fun A => by ext a b; simp
  have h1 := exp_plainMat e (Z.map (starRingEnd ℂ)) t
  have h2 : t • Z.map (starRingEnd ℂ) = (t • Z)ᴴᵀ := by ext a b; simp
  rw [h2, Matrix.exp_transpose, Matrix.exp_conjTranspose, ← h0] at h1
  exact h1

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)

theorem fr_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : M.fr τ * toFrame M τ Y * (M.fr τ)⁻¹ = Y := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc,
    Matrix.mul_nonsing_inv _ hd, mul_one]

theorem trace_toFrame (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) : (toFrame M τ Y).trace = Y.trace := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  rw [toFrame, Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]

theorem rep_exp (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    M.rep τ (NormedSpace.exp (t • toFrame M τ Y)) = M.σ τ (NormedSpace.exp (t • Y)) := by
  rw [DSModel.rep, ← Matrix.exp_conj _ _ (M.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul, fr_toFrame]

variable {M τ}

theorem matches_exp {p q : ℕ} {T : GrpData p q} {R : DSRep T}
    {φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ} {m : ℤ} {U : M.H τ → R.U.H} (h : Matches R M τ φ m U)
    (hφ : ∀ (Z : Mat p q) (t : ℝ), NormedSpace.exp (t • φ Z) = φ (NormedSpace.exp (t • Z)))
    {Z : Mat p q} (hZ : Z ∈ upq p q) (t : ℝ) (x : M.H τ) :
    U (M.rep τ (NormedSpace.exp (t • toFrame M τ (φ Z))) x) =
      ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m • R.U.π (T.expt (t • Z)) (U x) := by
  rw [rep_exp, hφ, h.grp, T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), smul_smul,
    ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]

theorem hasDerivAt_sq_zpow {p q : ℕ} (T : GrpData p q) (m : ℤ) {Z : Mat p q} (hZ : Z ∈ upq p q) :
    HasDerivAt (fun t : ℝ => ((T.sq (T.expt (t • Z)) : ℂˣ) : ℂ) ^ m) (m * (Z.trace / 2)) 0 := by
  have h3 := (hasDerivAt_zpow m _ (.inl (Units.ne_zero _))).comp (0 : ℝ)
    (GlobalTheory.RealPar.Cover.hasDerivAt_sq (T := T) hZ)
  refine h3.congr_deriv ?_
  simp [T.expt_zero]

theorem exists_locIt (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ ≃ₗᵢ[ℂ] R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) (hm : (m : ℚ) = 2 * aT) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hN : Nontrivial R₂.HK.V) (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (hB : IsCoverIt R₁ R₂ B) :
    ∃ A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ, LocIt M M' τ aS aT A := by
  let A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ :=
    LinearMap.mk₂ ℂ (fun P y => U.symm (B (κ P) (U' y)))
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp [LinearIsometryEquiv.map_smulₛₗ, LinearMap.map_smulₛₗ])
  have hA : ∀ P y, A P y = U.symm (B (κ P) (U' y)) := fun _ _ => rfl
  have hmC : (m : ℂ) = 2 * (aT : ℂ) := by exact_mod_cast hm
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  refine ⟨A, fun P y => ?_, ?_, fun P w => ?_, ?_, ?_⟩
  · refine Submodule.subset_span (h₁.smooth _ ?_)
    rw [hA, U.apply_symm_apply]
    exact hB.kfin _ _
  · obtain ⟨v, hv⟩ := exists_ne (0 : R₂.HK.V)
    obtain ⟨P, hP⟩ := hB.ne (R₂.ι v) fun h0 => hv (R₂.ι_inj (by rw [h0, map_zero]))
    refine ⟨κ.symm P, U'.symm (R₂.ι v), Submodule.subset_span (h₂.smooth _ ?_), ?_⟩
    · rw [U'.apply_symm_apply]; exact ⟨v, rfl⟩
    · rw [hA, U'.apply_symm_apply, κ.apply_symm_apply]
      intro h0
      exact hP (U.symm.injective (by rw [h0, map_zero]))
  · haveI : CompleteSpace (M'.H τ) := U'.toIsometryEquiv.completeSpace
    obtain ⟨c, hc⟩ := hB.bdd (κ P)
    let L : M'.H τ →L[ℂ] M.H τ := (A P).mkContinuous c fun y => by
      rw [hA, U.symm.norm_map, ← U'.norm_map y]; exact hc _
    refine ⟨(InnerProductSpace.toDual ℂ (M'.H τ)).symm ((innerSL ℂ w).comp L), fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  · intro X hX P y
    rw [← h₁.lie] at hX
    obtain ⟨Z, hZ, rfl⟩ := hX
    have h1 := (hasDerivAt_sq_zpow T₁ m hZ).fun_smul (hB.src Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h3 : (barMat e Z).map (starRingEnd ℂ) = Matrix.reindex e e Z := by ext a b; simp [barMat]
    have h4 : (barMat e Z).trace = -Z.trace := by
      rw [barMat, trace_reindex', ← trace_conj hZ]
      simp [Matrix.trace]
    convert h2 using 1
    · funext t
      apply U.injective
      rw [matches_exp h₁ (exp_barMat e) hZ, hA]
      simp
    · rw [hA, fr_toFrame, trace_toFrame, h3, h4, map_sub, map_smul, hκ.1, hmC,
        show 2 * (aT : ℂ) * (Z.trace / 2) = aT * Z.trace by ring]
      simp [T₁.expt_zero]
  · intro Y hY P y
    rw [← h₂.lie] at hY
    obtain ⟨Z, hZ, rfl⟩ := hY
    have h1 := (hasDerivAt_sq_zpow T₂ m' hZ).star.fun_smul (hB.tgt Z hZ (κ P) (U' y))
    have h2 := (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h1
    have h4 : (plainMat e' Z).trace = Z.trace := trace_reindex' e' Z
    have h5 : star ((m' : ℂ) * (Z.trace / 2)) = -((aS : ℂ) * Z.trace) := by
      rw [Complex.star_def, map_mul, map_intCast, map_div₀, trace_conj hZ, map_ofNat, hmC']
      ring
    convert h2 using 1
    · funext t
      rw [hA, matches_exp h₂ (exp_plainMat e') hZ, LinearMap.map_smulₛₗ]
      rfl
    · rw [h5, hA, fr_toFrame, trace_toFrame, h4, map_add, map_smul, plainMat, hκ.2]
      simp [T₂.expt_zero]
      abel

end GlobalTheory.Chain.RealIt.LocalFromCover

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierShiftedLatticeAwayFromPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TrOffShift

theorem algebraMap_mem_conjI {D : D7} (I : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.F)
    (h : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ I) :
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ conjI I := by
  apply Ideal.subset_span
  refine ⟨_, h, ?_⟩
  have h2 := GlobalTheory.Ker.MovLev.bar_algebraMap (D := D) s
  have h3 := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) h2
  simp only [Lev.bar] at h3
  have h4 := IsCMField.coe_ringOfIntegersComplexConj D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s)
  exact h3.symm.trans h4

theorem shift_mult : ∀ (D : D7) (r : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (L : Lt D.host.E r) (w : HeightOneSpectrum (𝓞 D.host.F)), (∀ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → ∀ u ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) L, ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • u ∈ L := by
  intro D r Pg Q L w hne u hu
  classical
  have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
    intro PP hPP
    by_contra hcon
    push_neg at hcon
    apply hne PP hPP
    have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := by
      intro s hs
      exact hcon s hs
    exact HeightOneSpectrum.ext
      ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
  choose! tf htf1 htf2 using hex
  refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
  · have : ∏ PP ∈ Pg ∪ Q, tf PP ∈ w.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun c hc => htf2 c hc)
    exact this
  · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP)
        ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
      rw [map_prod]
      exact Ideal.prod_mem_prod (fun PP hPP => algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP))
    have h1 := hu _ (algebraMap_mem_conjI (D := D) _ _ hmem)
    exact Submodule.smul_le_right h1

end GlobalTheory.TrOffShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierStandardLatticeOfMoverTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.MoverStd

theorem exists_mul_std : ∀ (D : D7) (S : HSp D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (σ : Af D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), evalV D.host.F w σ = 0 → (∀ i j, (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * (mt S k₀⁻¹ - 1) i j = 0) → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ v ∈ Λ', ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • v ∈ stdL D.host.E S.rank := by
  intro D S k₀ Λ' σ w hσ hk hm v hv
  obtain ⟨hfg, -, -⟩ := Base.stdL_mem_Vset (E := D.host.E) S.rank 1
  have hs : Submodule.span D.host.E (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) = ⊤ := by
    rw [stdL, Submodule.span_span_of_tower, ← (Pi.basisFun D.host.E (Fin S.rank)).span_eq]
    congr 2
    funext i
    simp
  have ht : ∀ u, MovLev.lf (MovLev.idem w.asIdeal) • (fmtC S k₀⁻¹ *ᵥ u) = MovLev.lf (MovLev.idem w.asIdeal) • u :=
    fun u => MovLev.smul_mulVec_eq _ _ (fun v' => by
      by_cases hv' : w.asIdeal ≤ v'.asIdeal
      · have e : v' = w := (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v'.isPrime.ne_top hv')).symm
        subst e
        refine Or.inr fun ε hε i j => ?_
        obtain ⟨α, rfl, -, hα0⟩ := hε
        have hασ : α * σ = 0 := by
          refine FiniteAdeleRing.ext D.host.F fun u => ?_
          change α u * σ u = 0
          by_cases hu : u = v'
          · subst hu
            rw [show σ u = 0 from hσ, mul_zero]
          · rw [show α u = 0 from hα0 u hu, zero_mul]
        have hmul : pairA D.host.F 0 α * (1 - pairA D.host.F 0 σ) = pairA D.host.F 0 α := by
          refine Prod.ext ?_ ?_
          · change (0 : Ainf D.host.F) * (1 - 0) = 0
            rw [zero_mul]
          · change α * (1 - σ) = α
            rw [mul_sub, mul_one, hασ, sub_zero]
        have h0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * (mt S k₀⁻¹ - 1) i j = 0 := by
          rw [← hmul, map_mul, mul_assoc, map_sub, map_one, hk i j, mul_zero]
        have := congrArg (cA D) h0
        rw [map_mul, map_zero, Matrix.sub_apply, map_sub] at this
        have e1 : cA D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
            algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
          change (pairA D.host.F 0 α) ⊗ₜ D.sp.cm.sig 1 = (pairA D.host.F 0 α) ⊗ₜ 1
          rw [map_one]
        have e' : cA D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
            (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
          rw [Matrix.one_apply]
          split_ifs
          exacts [map_one _, map_zero _]
        rw [e1, e'] at this
        exact this
      · exact Or.inl (if_neg hv')) u
  obtain ⟨t, htw, H⟩ := MovLev.exists_mul (E := D.host.E) w.asIdeal.primeCompl w.asIdeal (fun v' hv' => by
      have h1 : ¬ v'.asIdeal ≤ w.asIdeal := fun h => hv' ((v'.isMaximal.eq_of_le w.isPrime.ne_top h) ▸ le_rfl)
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h1
      exact ⟨a, ha', ha⟩)
    (L := Submodule.span (𝓞 D.host.E) {v}) (Λ := stdL D.host.E S.rank) (Submodule.fg_span_singleton v) hfg hs
    (fun z hz => by
      have hz' : z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin S.rank → D.host.E)) := AddSubgroup.closure_mono (by
        rintro y ⟨a, ha, x, hx, e⟩
        exact ⟨a, ha, x, (Submodule.span_le.2 (Set.singleton_subset_iff.2 hv)) hx, e⟩) hz
      change MovLev.lf (MovLev.idem w.asIdeal) • z ∈ _
      rw [← ht z]
      exact MovLev.hat_int (MovLev.idem_int _) ((hm _).2 ⟨z, hz', rfl⟩))
  exact ⟨t, htw, H v (Submodule.mem_span_singleton_self v)⟩

end GlobalTheory.Ker.MoverStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryTorusTraceFormOfHermitian
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll.HermTrace

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem fld_induction (P : PPol σ n) (p : Fld P → Prop) (h0 : ∀ e, p (algebraMap E (Fld P) e))
    (hadd : ∀ a b, p a → p b → p (a + b)) (hmul : ∀ a, p a → p (a * alpha P)) (l : Fld P) : p l := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := P.1) l
  induction q using Polynomial.induction_on with
  | C a => exact h0 a
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb
  | monomial k a ha => rw [pow_succ, ← mul_assoc, map_mul]; exact hmul _ ha

theorem star_star (hσ : ∀ e, σ (σ e) = e) (P : PPol σ n) (l : Fld P) : star' P (star' P l) = l := by
  induction l using fld_induction with
  | h0 e => rw [star'_algebraMap, star'_algebraMap, hσ]
  | hadd a b ha hb => rw [map_add, map_add, ha, hb]
  | hmul a ha => rw [map_mul, map_mul, ha, star'_alpha, map_inv₀, star'_alpha, inv_inv]

theorem trace_star (hσ : ∀ e, σ (σ e) = e) (P : PPol σ n) (l : Fld P) :
    Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  let e₁ : E ≃+* E := RingEquiv.ofRingHom (σ : E →+* E) (σ : E →+* E) (RingHom.ext hσ) (RingHom.ext hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofRingHom (star' P : Fld P →+* Fld P) (star' P : Fld P →+* Fld P)
    (RingHom.ext (star_star hσ P)) (RingHom.ext (star_star hσ P))
  have h := Algebra.trace_eq_of_equiv_equiv e₁ e₂ (RingHom.ext fun e => (star'_algebraMap P e).symm) l
  have h' : Algebra.trace E (Fld P) l = σ (Algebra.trace E (Fld P) (star' P l)) := h
  rw [h', hσ]

section Form

variable {A : Type} [CommRing A] (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_eq (a b : Fin n → A) : Formalism.UG.hform s J a b = (s ∘ a) ⬝ᵥ (J *ᵥ b) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_unitary (M : Matrix (Fin n) (Fin n) A) (h : Formalism.UG.cT s M * J * M = J) (a b : Fin n → A) :
    Formalism.UG.hform s J (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform s J a b := by
  have e : s ∘ (M *ᵥ a) = (s ∘ a) ᵥ* Formalism.UG.cT s M := by
    funext i
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [hform_eq, hform_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem hform_add_left (a a' b : Fin n → A) :
    Formalism.UG.hform s J (a + a') b = Formalism.UG.hform s J a b + Formalism.UG.hform s J a' b := by
  simp [Formalism.UG.hform, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (a b b' : Fin n → A) :
    Formalism.UG.hform s J a (b + b') = Formalism.UG.hform s J a b + Formalism.UG.hform s J a b' := by
  simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (c : A) (a b : Fin n → A) :
    Formalism.UG.hform s J (c • a) b = s c * Formalism.UG.hform s J a b := by
  simp [Formalism.UG.hform, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (c : A) (a b : Fin n → A) :
    Formalism.UG.hform s J a (c • b) = c * Formalism.UG.hform s J a b := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_symm (hs : ∀ e, s (s e) = e) (hJ : ∀ i j, s (J j i) = J i j) (a b : Fin n → A) :
    Formalism.UG.hform s J b a = s (Formalism.UG.hform s J a b) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hs, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_single (i j : Fin n) : Formalism.UG.hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [Formalism.UG.hform, Pi.single_apply, apply_ite s]

end Form

theorem exists_trace_form : ∀ (F E : Type) [Field F] [Field E] [CharZero E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (A : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) A * J * A = J → ∀ φ : Fld P ≃ₗ[E] (Fin n → E), (∀ y, A *ᵥ φ y = φ (alpha P * y)) → ∃ x : Fld P, x ≠ 0 ∧ star' P x = x ∧ ∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y') := by
  intro F E _ _ _ _ σ hσ n P J hJ A hA φ hφ
  set s : E →+* E := (σ : E →+* E) with hs
  have h1 : ∀ y y', Formalism.UG.hform s J (φ (alpha P * y')) (φ (alpha P * y)) = Formalism.UG.hform s J (φ y') (φ y) :=
    fun y y' => by rw [← hφ, ← hφ, hform_unitary s J A hA]
  have h2 : ∀ l y y', Formalism.UG.hform s J (φ (l * y')) (φ y) = Formalism.UG.hform s J (φ y') (φ (star' P l * y)) := by
    intro l
    induction l using fld_induction with
    | h0 e =>
      intro y y'
      rw [star'_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, hform_smul_left,
        hform_smul_right]
      rfl
    | hadd a b ha hb =>
      intro y y'
      rw [add_mul, map_add, hform_add_left, ha, hb, map_add, add_mul, map_add, hform_add_right]
    | hmul a ha =>
      intro y y'
      rw [mul_assoc, ha, map_mul (star' P), star'_alpha, ← h1 (star' P a * (alpha P)⁻¹ * y) y']
      congr 2
      field_simp [alpha_ne_zero P]
  let f : Module.Dual E (Fld P) :=
    { toFun := fun y => Formalism.UG.hform s J (φ 1) (φ y)
      map_add' := fun a b => by rw [map_add, hform_add_right]
      map_smul' := fun c a => by rw [map_smul, hform_smul_right]; rfl }
  have hnd := traceForm_nondegenerate E (Fld P)
  let x : Fld P := ((Algebra.traceForm E (Fld P)).toDual hnd).symm f
  have hx : ∀ y, Algebra.trace E (Fld P) (x * y) = Formalism.UG.hform s J (φ 1) (φ y) := fun y => by
    have := LinearMap.BilinForm.toDual_def hnd (m := x) (n := y)
    rw [Algebra.traceForm_apply] at this
    rw [← this, LinearEquiv.apply_symm_apply]
    rfl
  have h3 : ∀ y y', Formalism.UG.hform s J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y') := fun y y' => by
    rw [mul_assoc, hx, mul_comm y, ← h2, mul_one]
  refine ⟨x, fun h0 => ?_, ?_, h3⟩
  · have hn : 0 < n := P.2.2.2.1 ▸ P.2.2.1.natDegree_pos
    have hz : J = 0 := by
      ext i j
      rw [← hform_single s J i j, ← φ.apply_symm_apply (Pi.single i 1), ← φ.apply_symm_apply (Pi.single j 1), h3, h0]
      simp
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact hJ.2 (by rw [hz, Matrix.det_zero])
  · rw [← sub_eq_zero]
    refine hnd.1 _ fun z => ?_
    have a := hform_symm s J hσ hJ.1 (φ z) (φ 1)
    rw [h3, h3, map_one, mul_one, mul_one] at a
    have b := trace_star hσ P (x * star' P z)
    rw [map_mul, star_star hσ] at b
    rw [Algebra.traceForm_apply, sub_mul, map_sub, b, a, sub_eq_zero]
    rfl

end GlobalTheory.TrEll.HermTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumClasses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

def vmvBil (E : Type) [Field E] [NumberField E] (n r : ℕ) :
    (Fin n → E) →ₗ[𝓞 E] (Fin r → E) →ₗ[𝓞 E] Matrix (Fin n) (Fin r) E :=
  LinearMap.mk₂ (𝓞 E) (fun v u => vecMulVec v u)
    (fun v v' u => by ext i j; simp [vecMulVec, add_mul])
    (fun a v u => by ext i j; simp [vecMulVec, smul_mul_assoc])
    (fun v u u' => by ext i j; simp [vecMulVec, mul_add])
    (fun a v u => by ext i j; simp [vecMulVec, mul_smul_comm])

theorem tens_quot_finite {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (L : Lt E r)
    (hΛ : Λ.FG) (hL : L.FG) (𝔞 𝔪 : Ideal (𝓞 E)) (hm : 𝔪 ≠ ⊥) :
    Finite (tens Λ (𝔞 • L) ⧸ (tens Λ ((𝔞 * 𝔪) • L)).addSubgroupOf (tens Λ (𝔞 • L))) := by
  set A := tens Λ (𝔞 • L) with hA
  set B := tens Λ ((𝔞 * 𝔪) • L) with hB
  have hM : (Submodule.map₂ (vmvBil E n r) Λ L).FG := hΛ.map₂ _ hL
  have hMZ : ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).FG := hM.restrictScalars
  have hle : A.toIntSubmodule ≤ (Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ := by
    intro x hx
    have hsub : A ≤ ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).toAddSubgroup := by
      rw [hA, tens, AddSubgroup.closure_le]
      rintro y ⟨v, hv, u, hu, rfl⟩
      exact Submodule.apply_mem_map₂ (vmvBil E n r) hv (Submodule.smul_le_right hu)
    exact hsub hx
  have hAfg : A.toIntSubmodule.FG :=
    (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _ hMZ)) _ hle
  haveI : AddGroup.FG A := by
    have : Module.Finite ℤ A.toIntSubmodule := Module.Finite.iff_fg.mpr hAfg
    exact (Module.Finite.iff_addGroup_fg).mp this
  set N := Ideal.absNorm 𝔪 with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.mp h))
  have hNA : ∀ x ∈ A, N • x ∈ B := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u, hu, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨v, hv, N • u, ?_, ?_⟩
      · have h1 : ((N : 𝓞 E)) • u ∈ 𝔪 • (𝔞 • L) := Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hu
        rw [← Submodule.mul_smul, mul_comm] at h1
        rwa [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      · ext i j; simp [vecMulVec]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hNpos, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hNA x x.2

theorem lvCls_finite : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  intro D S T C Lv
  exact tens_quot_finite _ _ (Submodule.fg_span (Set.finite_range _)) C.X.Λ_fg _ _ Lv.ne_bot

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGoodRowsFiniteGroupActionStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_goodRows_finiteGroup_action : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HE → R.models_gE → R.models_ν0 → ∀ g x, ‖R.gE g x‖ = ‖x‖ := by
  first | exact @GlobalTheory.norm_gE_rows | exact GlobalTheory.norm_gE_rows | (intros; apply GlobalTheory.norm_gE_rows <;> assumption)
end

