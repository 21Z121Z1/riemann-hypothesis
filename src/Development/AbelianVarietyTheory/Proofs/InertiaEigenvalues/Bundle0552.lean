import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdREOfIsCrys
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CrysDdR

theorem finrank_DdRE_of_isCrys : ∀ D : D7, ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), (∃ s, Good K s LL) → ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ) = finrank ↥LL.1 T.V := by
  intro D l _ K LL _ T hc τ
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ hc).1
  exact ((GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1 τ).2.2 hdr

end GlobalTheory.CrysDdR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankIotaLetter
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.NL.IotaLetterRank

theorem finrank_iota_letter : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)), finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) = finrank ↥LL.1 T.V := by
  intro D HW F Cm l _ K LL hG T hV c
  unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
  rw [← (Submodule.equivMapOfInjective _ (GlobalTheory.NL.PhiD.iota_injective _) _).finrank_eq]
  exact (GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).2 _ hV

end GlobalTheory.NL.IotaLetterRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem flatPow_dvd_perPow_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (M n : ℕ), ∃ (c : ℕ) (y : Ainf l), (l : Ainf l) ^ n ∣ bk.ev X ^ c - τ ^ M * y := by
  intro l _ K bk τ hτ M n
  have hU : IsUnit (inclW l (τ ^ M)) := by
    rw [map_pow]
    exact (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1.pow M
  obtain ⟨m, t, h⟩ := GlobalTheory.BSP.BddDen.main l K bk (τ ^ M) hU n
  refine ⟨m, t, ?_⟩
  have : bk.ev X ^ m - τ ^ M * t = -(t * τ ^ M - bk.ev X ^ m) := by ring
  rw [this]
  exact (dvd_neg).2 h

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.FontaineAdm

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm8 D := by
  intro D l _ K LL T
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.dcris_finite_le_of_tied (D.locT l) K LL T.V T.ρ
  refine ⟨⟨h1, h2⟩, fun τ => ?_⟩
  obtain ⟨hd, -⟩ := GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ
  exact ⟨(hd τ).1, (hd τ).2.1⟩

end GlobalTheory.Per.FontaineAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsiStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_fullFaithful_exact_psi : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  first | exact @GlobalTheory.fontaine_litFont_assembled | exact GlobalTheory.fontaine_litFont_assembled | (intros; apply GlobalTheory.fontaine_litFont_assembled <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCongrOfFiniteOfLocalDividedPowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)), ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H))) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) → ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.goodSet_of_finite_of_local | exact GlobalTheory.CrysPrism.goodSet_of_finite_of_local | (intros; apply GlobalTheory.CrysPrism.goodSet_of_finite_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsDividedPowerSeriesGeneratorSetStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, frobTot K a l F ∈ SdSet t K e := by
  first | exact @GlobalTheory.CrysPrism.frobTot_mem_SdSet | exact GlobalTheory.CrysPrism.frobTot_mem_SdSet | (intros; apply GlobalTheory.CrysPrism.frobTot_mem_SdSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem WSeed.crystallineDiscPeriods_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ),
    ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ →
      ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ =
        s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  intro l _ K bk τ hτ d ρ _ s Φ hΦ
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hΦS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (bk.iA (bk.ev x)) = bk.iA (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have he : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    change bk.iA (bk.ev (frobS l bk.a bk.E)) ≠ 0
    rw [bk.ev_frob, ← map_zero bk.iA]
    exact fun h => bk.frobenius_ev_E_ne_zero hτ (hinj h)
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  have hQP : s.X.map (bk.iS.comp (frobS l bk.a)) * s.X'.map (bk.iS.comp (frobS l bk.a)) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ he)
  have hPQ := GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hQP
  have hA : (s.X'.map bk.iS).map Φ = s.X'.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; congr 1; funext x; exact hΦS x
  have hF : (s.F.map (C : Wq l bk.a →+* bk.S)).map bk.iS = s.F.map (bk.iS.comp C) := by
    rw [Matrix.map_map]; rfl
  have hX : (s.X.map (frobS l bk.a)).map bk.iS = s.X.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; rfl
  have h2 := congrArg (· * s.X.map (bk.iS.comp (frobS l bk.a))) (s.φ Φ hΦ)
  simp only [Matrix.map_mul, hA] at h2
  rw [Matrix.smul_mul, Matrix.mul_assoc (s.W.map Φ), hPQ, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, hF, hX]
  refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero s.N he) ?_
  dsimp only
  calc bk.iS (frobS l bk.a bk.E) ^ s.N • (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
        s.W.map Φ)
      = ((l : bk.DA bk.ρ₀) ^ s.c₁ * ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N))) •
        s.W.map Φ := by rw [smul_smul]; congr 1; ring
    _ = _ := h2
    _ = _ := by rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowMemFiniteSupportDoublePowerSeriesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_pow_mem_finiteSupportDoublePowerSeries : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0 := by
  first | exact @GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero | exact GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero | (intros; apply GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPreservesLadicDecayDividedPowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c)) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → (∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂) → (∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0) → ∀ w : ℕ × ℕ → Wq l a, LTo0 l w → ∀ v b : ℕ × ℕ → Wq l a, frob2 φ₂ (ofW t K e w) = ofW t K e v → frob2 φ₂ (ofW t K e w) = ofW t K e w ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e b → LTo0 l v ∧ LTo0 l b := by
  first | exact @GlobalTheory.CrysPrism.frob_keeps_decay | exact GlobalTheory.CrysPrism.frob_keeps_decay | (intros; apply GlobalTheory.CrysPrism.frob_keeps_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHypothesesOfAttached
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem noInv_all_places (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i)
    (hT : ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)) (h2 : ValuationStabilityAtRing D.ntw i s)
    (hA : TripleAtt D.naut bkP i s) (hJ : NoJump bkP i s) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  by_cases hl : v ∈ placesOver D.host.E (D.ntw.l i)
  · exact ⟨GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump D bkP i s hJ v hl, GlobalTheory.T.noInv_tateDual_of_hodge_of_noJump D bkP i s hT (GlobalTheory.T.hodge_of_attached D bkP i s hA) hJ v hl⟩
  by_cases hS : v ∈ Spl (X := D.ntw) i
  · rcases hS.1 with hg | hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hg
      exact GlobalTheory.T.noInv_at_type_primes D i s h2 k (fun e => hl (e ▸ hk)) v hk
    · exact GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime D i s (GlobalTheory.T.unramified_of_attached D bkP i s hA) v (Finset.mem_coe.1 hp)
  · obtain ⟨ι, hι⟩ := GlobalTheory.T.pure_of_attached D bkP i s hA
    exact GlobalTheory.T.noInv_away_of_pure D i s ι hι v hl hS

theorem galois_hypotheses_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D), GlobalTheory.TypeLeaf.FrobDense D → (∀ i, D.ntw.NonzeroIndexPlace i → (∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI))) → BlochKatoReduction.adm2 D → (∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, TripleAtt D.naut bkP i s) → BlochKatoReduction.adm1 bkP ∧ BlochKatoReduction.adm8 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → True ∧ ∀ s : D.ntw.Sig i, SelfDual i s ∧ NoJump bkP i s := by
  intro D bkP hF hT h2 hA
  have hJ : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ s, NoJump bkP i s := fun i hi s => by
    obtain ⟨ι, J, h, h'⟩ := GlobalTheory.T.jumps_good_of_attached D bkP i s (hA i hi s)
    exact GlobalTheory.T.noHodgeJump_of_goodJumpMultiset D bkP i s ι J (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s)) h h'
  refine ⟨fun i hi s => ?_, fun i hi s => ?_, fun i hi => ⟨trivial, fun s => ⟨?_, hJ i hi s⟩⟩⟩
  · obtain ⟨ι, J, h, h'⟩ := GlobalTheory.T.jumps_good_of_attached D bkP i s (hA i hi s)
    exact GlobalTheory.T.isotypicValuationAtRing_of_unrRho_hodgeL_noInv_negCount D bkP i s (GlobalTheory.T.unramified_of_attached D bkP i s (hA i hi s)) (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s))
      (noInv_all_places D bkP i s (hT i hi) (h2 i hi s) (hA i hi s) (hJ i hi s))
      (GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps D bkP i s ι J (GlobalTheory.T.hodge_of_attached D bkP i s (hA i hi s)) h h')
  · exact GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob D i s (GlobalTheory.T.unramified_of_attached D bkP i s (hA i hi s)) (GlobalTheory.T.hkFrob_of_attached D bkP i s (hA i hi s))
  · exact GlobalTheory.T.selfDual_lattice_of_conjDualCharpoly D i s (h2 i hi s) (GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense D hF i s (GlobalTheory.T.frobDual_of_attached D bkP i s (hA i hi s)))

end GlobalTheory.TripleGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinfty
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalDecomp

theorem galQ_eq_GK_mul_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k := by
  intro l _ a e _ _ ϖ hea g
  have hl := (Fact.out : l.Prime)
  have hdvd : e ∣ l ^ a - 1 := ⟨1, by omega⟩
  have hG := PiSys.isGalois_field a ϖ hdvd
  have hK : FiniteDimensional ℚ_[l] (ϖ.field a).1 := (ϖ.field a).2
  have hcop : Nat.Coprime l e := by
    refine (Nat.Prime.coprime_iff_not_dvd hl).2 fun h => ?_
    have h2 : l ∣ l ^ a := dvd_pow_self l (NeZero.ne a)
    rw [← hea] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  have hbot : (ϖ.field a).1 ⊓ ϖ.Kinf = ⊥ := by
    set F := (ϖ.field a).1 ⊓ ϖ.Kinf with hF
    haveI : FiniteDimensional ℚ_[l] F := FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : F ≤ (ϖ.field a).1)).toLinearMap (IntermediateField.inclusion (inf_le_left : F ≤ (ϖ.field a).1)).toRingHom.injective
    obtain ⟨n, hn⟩ := GlobalTheory.T.le_adjoin_compatibleRoots_of_finite_kummerTower l e ϖ F inferInstance inf_le_right
    have hN : 0 < l ^ n := pow_pos hl.pos n
    have hx : (ϖ.seq n ^ e) ^ (l ^ n) = -(l : Om l) := by rw [← pow_mul, mul_comm]; exact ϖ.seq_pow_mul n
    have hx0 : ϖ.seq n ^ e ≠ 0 := pow_ne_zero _ (ϖ.seq_ne_zero n)
    have hint : IsIntegral F (ϖ.seq n ^ e) := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (ϖ.seq n ^ e)).tower_top
    have hc0 : (minpoly F (ϖ.seq n ^ e)).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx0
    have hcF : (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) ∈ F := ((minpoly F (ϖ.seq n ^ e)).coeff 0).2
    have hc : (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) ≠ 0 := by
      simpa using hc0
    obtain ⟨j, hj⟩ := GlobalTheory.T.norm_pow_ramifiedUniformizerField_zpow l a e ϖ _ (IntermediateField.mem_inf.1 hcF).1 hc
    have h2 := GlobalTheory.T.norm_minpoly_coeff_zero_pow_of_pow_eq_neg_prime l F (l ^ n) (ϖ.seq n ^ e) hN hx
    have h4 := GlobalTheory.T.finrank_mul_natDegree_minpoly_le_of_pow_eq_neg l F (l ^ n) (ϖ.seq n ^ e) hN hx hn
    have hm : 0 < (minpoly F (ϖ.seq n ^ e)).natDegree := minpoly.natDegree_pos hint
    set m := (minpoly F (ϖ.seq n ^ e)).natDegree with hmdef
    set c : Om l := (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) with hcdef
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.pos
    have hl1 : (l : ℝ) ≠ 1 := by exact_mod_cast hl.one_lt.ne'
    have key : (l : ℝ) ^ (j * ((l ^ n : ℕ) : ℤ)) = (l : ℝ) ^ (-((m * e : ℕ) : ℤ)) := by
      have e1 : ‖c‖ ^ (e * l ^ n) = ((l : ℝ) ^ j) ^ (l ^ n) := by rw [pow_mul, hj]
      have e2 : ‖c‖ ^ (e * l ^ n) = (((l : ℝ)⁻¹) ^ m) ^ e := by rw [mul_comm, pow_mul, h2]
      rw [_root_.zpow_mul, zpow_natCast, ← e1, e2, _root_.zpow_neg, zpow_natCast, ← pow_mul, inv_pow]
    have key2 : j * ((l ^ n : ℕ) : ℤ) = -((m * e : ℕ) : ℤ) := zpow_right_injective₀ hl0 hl1 key
    have hdv : l ^ n ∣ m * e := by
      have : ((l ^ n : ℕ) : ℤ) ∣ ((m * e : ℕ) : ℤ) := ⟨-j, by linarith⟩
      exact Int.natCast_dvd_natCast.1 this
    have hdm : l ^ n ∣ m := (Nat.Coprime.pow_left n hcop).dvd_of_dvd_mul_right hdv
    have hle : l ^ n ≤ m := Nat.le_of_dvd hm hdm
    have hfr : Module.finrank ℚ_[l] F = 1 := by
      have hpos : 0 < Module.finrank ℚ_[l] F := Module.finrank_pos
      by_contra hne
      have : 2 * m ≤ Module.finrank ℚ_[l] F * m := Nat.mul_le_mul_right _ (by omega)
      omega
    exact IntermediateField.finrank_eq_one_iff.1 hfr
  exact GlobalTheory.T.exists_mul_fixingSubgroup_of_inf_eq_bot l (ϖ.field a).1 ϖ.Kinf hK hG hbot g

end GlobalTheory.NgalDecomp
end

