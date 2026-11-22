import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0504
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0491
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0511
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantLeviActionModulusStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinvariant_levi_action_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (h : MirabolicParabolic k (i + 1) t) (η : HPG k (i + 1) (t + 1)) (hη : pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k))) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ η w) = ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 * dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • sigC τ σ h (qC τ σ w) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.QLevi.qC_sigX | exact GlobalTheory.CompanionTheory.BZPhiPG.QLevi.qC_sigX | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.QLevi.qC_sigX <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateCentrePowerBounded
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.CuspGrowth

open GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele in

theorem abs_le_of_conj_mem_compact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ Q : Set (GA E a), IsCompact Q → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (x : GA E a),
      x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x ∈ Q → |n| ≤ n₀ := by
  intro E _ _ _ a ha Q hQ
  have hf : Continuous fun g : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det g)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨B, hB⟩ := (hQ.image hf).isBounded.exists_norm_le
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  set L := Real.log (ideleNorm (E := E) (eIdele E)) with hLdef
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  refine ⟨⌈B / (a * L)⌉₊, fun γ n x hx => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have hv : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x))) = (n : ℝ) * (a * L) := by
    have h1 : GeneralLinearGroup.det (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x) =
        diag E (GeneralLinearGroup.det γ) * (eIdele E ^ a) ^ n := by
      rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, mul_comm, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [h1, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul,
      map_zpow, map_pow, Real.log_zpow, Real.log_pow]
  have hb := hB _ ⟨_, hx, rfl⟩
  beta_reduce at hb
  rw [hv, Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos ha' hL)] at hb
  have h2 : ((|n| : ℤ) : ℝ) ≤ B / (a * L) := by
    rw [le_div_iff₀ (mul_pos ha' hL)]
    simpa using hb
  have h3 : ((|n| : ℤ) : ℝ) ≤ ((⌈B / (a * L)⌉₊ : ℤ) : ℝ) := by
    rw [Int.cast_natCast]
    exact h2.trans (Nat.le_ceil _)
  exact Int.cast_le.1 h3

end GlobalTheory.CompanionTheory.CuspGrowth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBounded
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthEntries

open GlobalTheory.CompanionTheory.BoxBound

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem norm_entry_le_toL (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖A i j w‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (A i j) w).trans
    ((norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i))

theorem norm_toL_le_height (y : GL (Fin a) (Cinf E)) : ‖toL y.val‖ ≤ height y := by
  have := norm_nonneg (toL (y⁻¹).val)
  unfold height
  linarith

theorem norm_toL_inv_le_height (y : GL (Fin a) (Cinf E)) : ‖toL (y⁻¹).val‖ ≤ height y := by
  have := norm_nonneg (toL y.val)
  unfold height
  linarith

theorem norm_toL_mul_le_of_le {u v : GL (Fin a) (Cinf E)} {p r : ℝ} (hu : ‖toL u.val‖ ≤ p)
    (hv : ‖toL v.val‖ ≤ r) : ‖toL (u * v).val‖ ≤ a * (p * r) :=
  (norm_toL_mul_le u.val v.val).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hu hv (norm_nonneg _) ((norm_nonneg _).trans hu)) (Nat.cast_nonneg a))

theorem gFin_mul (g h : GA E a) : gFin (g * h) = gFin g * gFin h := map_mul _ g h

theorem gFin_inv (g : GA E a) : gFin g⁻¹ = (gFin g)⁻¹ := map_inv _ g

theorem gFin_zpow (g : GA E a) (n : ℤ) : gFin (g ^ n) = gFin g ^ n := map_zpow _ g n

theorem gInf_mul (g h : GA E a) : gInf (g * h) = gInf g * gInf h := map_mul _ g h

theorem gInf_inv (g : GA E a) : gInf g⁻¹ = (gInf g)⁻¹ := map_inv _ g

theorem gFin_splitCentre (t : ℝ) : gFin (splitCentre E a t) = 1 := pFin_infGL _

theorem exists_bound_splitCentre (n₀ : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℤ, |m| ≤ n₀ →
    ‖toL (gInf (splitCentre E a 1 ^ m)).val‖ ≤ B := by
  refine ⟨∑ m ∈ Finset.Icc (-(n₀ : ℤ)) n₀, ‖toL (gInf (splitCentre E a 1 ^ m)).val‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun m hm => ?_⟩
  exact Finset.single_le_sum (f := fun m : ℤ => ‖toL (gInf (splitCentre E a 1 ^ m)).val‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_Icc.2 (abs_le.1 hm))

theorem place_eq_norm_pInf (x : E) (w : InfinitePlace E) :
    w x = ‖pInf E (algebraMap E (Ad E) x) w‖ := by
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]

theorem entries_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (g₀ : GA E a)
    (Q : Set (GA E a)), IsCompact Q → ∀ n₀ : ℕ, ∃ (Qf : Set (Af E)) (C : ℝ), IsCompact Qf ∧ 0 ≤ C ∧
      ∀ (y : GL (Fin a) (Cinf E)) (γ : GL (Fin a) E) (n : ℤ), |n| ≤ n₀ →
        (g₀ * infGL E a y)⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * (g₀ * infGL E a y) ∈ Q →
        ∀ i j, algebraMap E (Af E) (γ.val i j) ∈ Qf ∧ ∀ w : InfinitePlace E, w (γ.val i j) ≤ C * height y ^ 2 := by
  intro E _ _ _ a g₀ Q hQ n₀
  have hK : IsCompact ((fun q : GA E a => gFin g₀ * gFin q * (gFin g₀)⁻¹) '' Q) :=
    hQ.image ((continuous_const.mul continuous_gFin).mul continuous_const)
  have hent : ∀ i j : Fin a, Continuous fun g : GL (Fin a) (Af E) => g.val i j := fun i j =>
    (Units.continuous_val : Continuous fun g : GL (Fin a) (Af E) => (g.val : Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨B, hB0, hB⟩ := exists_height_bound (E := E) (a := a) hQ
  obtain ⟨Z, hZ0, hZ⟩ := exists_bound_splitCentre (E := E) (a := a) n₀
  set g1 : ℝ := ‖toL (gInf g₀).val‖ with hg1
  set g2 : ℝ := ‖toL ((gInf g₀)⁻¹).val‖ with hg2
  have hg10 : 0 ≤ g1 := norm_nonneg _
  have hg20 : 0 ≤ g2 := norm_nonneg _
  refine ⟨⋃ i, ⋃ j, (fun g : GL (Fin a) (Af E) => g.val i j) '' ((fun q : GA E a => gFin g₀ * gFin q * (gFin g₀)⁻¹) '' Q),
    (a : ℝ) ^ 5 * (g1 * g2 * B * Z),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hK.image (hent i j),
    mul_nonneg (pow_nonneg (Nat.cast_nonneg a) 5) (mul_nonneg (mul_nonneg (mul_nonneg hg10 hg20) hB0) hZ0), ?_⟩
  intro y γ n hn hq i j
  set X : GA E a := g₀ * infGL E a y with hX
  set q : GA E a := X⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * X with hqdef
  have h1 : ratGL E a γ * splitCentre E a 1 ^ n = X * q * X⁻¹ := by
    rw [hqdef]; group
  have hfin : gFin (ratGL E a γ) = gFin g₀ * gFin q * (gFin g₀)⁻¹ := by
    have e1 : gFin X = gFin g₀ := by
      rw [hX, gFin_mul, show gFin (infGL E a y) = 1 from pFin_infGL y, mul_one]
    have e2 : gFin (splitCentre E a 1 ^ n) = 1 := by
      rw [gFin_zpow, gFin_splitCentre, _root_.one_zpow]
    have h := congrArg gFin h1
    rw [gFin_mul, e2, mul_one, gFin_mul, gFin_mul, gFin_inv, e1] at h
    exact h
  have hinf : gInf (ratGL E a γ) =
      gInf g₀ * y * gInf q * y⁻¹ * (gInf g₀)⁻¹ * gInf (splitCentre E a 1 ^ (-n)) := by
    have h2 : ratGL E a γ = X * q * X⁻¹ * splitCentre E a 1 ^ (-n) := by
      rw [← h1, _root_.zpow_neg, mul_inv_cancel_right]
    have e1 : gInf X = gInf g₀ * y := by
      rw [hX, gInf_mul, show gInf (infGL E a y) = y from pInf_infGL y]
    have h := congrArg gInf h2
    rw [gInf_mul, gInf_mul, gInf_mul, gInf_inv, e1] at h
    rw [h]
    group
  refine ⟨?_, fun w => ?_⟩
  · refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    exact ⟨gFin (ratGL E a γ), ⟨q, hq, hfin.symm⟩, rfl⟩
  · have hy := norm_toL_le_height y
    have hy' := norm_toL_inv_le_height y
    have hR : ‖toL (gInf q).val‖ ≤ B := (norm_toL_le_height _).trans (hB q hq)
    have hZn : ‖toL (gInf (splitCentre E a 1 ^ (-n))).val‖ ≤ Z := hZ (-n) (by rwa [abs_neg])
    have hM := norm_toL_mul_le_of_le (norm_toL_mul_le_of_le (norm_toL_mul_le_of_le
      (norm_toL_mul_le_of_le (norm_toL_mul_le_of_le (le_refl g1) hy) hR) hy') (le_refl g2)) hZn
    rw [← hinf] at hM
    rw [place_eq_norm_pInf]
    have he : ‖pInf E (algebraMap E (Ad E) (γ.val i j)) w‖ ≤ ‖toL (gInf (ratGL E a γ)).val‖ :=
      norm_entry_le_toL (gInf (ratGL E a γ)).val i j w
    refine he.trans (hM.trans_eq ?_)
    ring

end GlobalTheory.CompanionTheory.GrowthEntries

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteAdelicDenominatorStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_finite_adelic_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Set (Af F ⊗[F] E)), IsCompact L → ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ L → IsIntegral ℤ ((d : E) * e) := by
  first | exact @GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact | exact GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AdeleDenom.exists_nat_mul_isIntegral_of_isCompact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSpanFiniteDimStable
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_skew_curve {E : Type} [Field E] [NumberField E] {a : ℕ} (S : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL S) 0 ∧
      (S.conjTranspose = -S → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • S)).unit, Units.ext (by simp), ?_, fun hS t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) S (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hS, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • S)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem liB_skew_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  intro E _ _ _ a φ Z hZ hfd ψ hψ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hW
  have hst : ∀ k : Kinf E a, ∀ w ∈ W, cptRep E a k w ∈ W := by
    intro k w hw
    refine Submodule.span_induction (p := fun w _ => cptRep E a k w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      change cptRep E a (k * k') φ = cptRep E a k (cptRep E a k' φ)
      rw [map_mul, Module.End.mul_apply]
    · rw [map_zero]; exact W.zero_mem
    · intro x y _ _ hx hy; rw [map_add]; exact W.add_mem hx hy
    · intro r x _ hx; rw [map_smul]; exact W.smul_mem r hx
  let S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of (mMap E a (Z : ArchMatrix E a))
  have hS : S.conjTranspose = -S := by
    ext i j w
    have h := congrFun (congrFun hZ i) j
    have h2 := congrFun (congrArg Prod.snd h) ⟨w, IsTotallyComplex.isComplex w⟩
    exact h2
  obtain ⟨c, h0, hc, hu⟩ := exists_skew_curve S
  let W' : Submodule ℂ (GA E a → ℂ) := W.map (Sm E a).subtype
  have hW' : FiniteDimensional ℂ W' := inferInstance
  have hF : ∀ t, (fun g => ψ.1 (g * infGL E a (c t))) ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hS t⟩ ψ, hst _ _ hψ, funext fun g => by
      have e : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E a) = c t := Units.ext rfl
      change ψ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [e]⟩
  have hd : ∀ g : GA E a, HasDerivAt (fun t : ℝ => ψ.1 (g * infGL E a (c t))) ((liB Z ψ).1 g) 0 :=
    fun g => hasDerivAt_curve ψ g c (toL S) h0 hc
  obtain ⟨w, hw, e⟩ := AutomorphicForm.mem_of_hasDerivAt W' hF hd
  rwa [show liB Z ψ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.HCRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnipotentSubgroupFiniteGenerationStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_unipotent_subgroup_finite_generation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (Q : Subgroup (GL (Fin N) k)), Q ≤ unipB k (Fin N) → (∀ s : Finset (GL (Fin N) k), (↑s : Set (GL (Fin N) k)) ⊆ Q → ∃ L : Subgroup (GL (Fin N) k), L ≤ Q ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k))) → ∀ θ : Q →* ℂˣ, (∀ (q : Q) (hq : (q : GL (Fin N) k) ∈ unipB k (Fin N)), θ q = whitChar ψ N ⟨q, hq⟩) → ∀ f ∈ openFns d hd ρ, f ∈ twKer (parInd (stdBlocks d hd) ρ) Q θ → f ∈ Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ, x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g} := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer | exact GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConductorEqTopOfStandardOpen
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem conductor_eq_top_of_standardOpen {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  have h1 : χ.conductor ∣ (⊤ : Ideal (𝓞 F)) :=
    (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans h)
  rw [← Ideal.one_eq_top] at h1
  exact Ideal.isUnit_iff.1 (isUnit_of_dvd_one h1)

theorem toIdele_inv_apply {F : Type} [Field F] [NumberField F]
    (χ : HeckeCharacter F) (x : IdeleGroup F) : (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ :=
  rfl

theorem coeff_inv_mul_coeff : ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
    standardOpenSubgroup F ≤ χ.toIdele.ker → ∀ J : Ideal (𝓞 F), J ≠ ⊥ →
      (χ⁻¹).coeff J * χ.coeff J = 1 := by
  intro F _ _ χ hχ J hJ
  have hc : χ.conductor = ⊤ := conductor_eq_top_of_standardOpen χ hχ
  have hc' : (χ⁻¹).conductor = ⊤ := by
    refine conductor_eq_top_of_standardOpen _ fun x hx ↦ ?_
    have h1 : χ.toIdele x = 1 := hχ hx
    rw [MonoidHom.mem_ker, toIdele_inv_apply, h1, inv_one]
  have h1 : J ≠ ⊥ ∧ IsCoprime J χ.conductor :=
    ⟨hJ, by rw [hc, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  have h2 : J ≠ ⊥ ∧ IsCoprime J (χ⁻¹).conductor :=
    ⟨hJ, by rw [hc', ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  obtain ⟨x, hx, hxJ⟩ := exists_mem_primeToLevel (idealUnit_mem_idealsPrimeTo h1.1 h1.2)
  have hx' : x ∈ primeToLevel (χ⁻¹).conductor := by rw [hc', ← hc]; exact hx
  rw [HeckeCharacter.coeff_of_mem _ h1, HeckeCharacter.coeff_of_mem _ h2,
    HeckeCharacter.idealCharacter_apply _ hx _ hxJ,
    HeckeCharacter.idealCharacter_apply _ hx' _ hxJ, toIdele_inv_apply, ← Circle.coe_mul,
    inv_mul_cancel, Circle.coe_one]

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_frame_weight_ratio_bound : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c, ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio | exact GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def resQ (φ : GA E a → ℂ) : RightCosetSpace (rationalGLOne E a) → ℂ :=
  fun q => φ ((Quotient.out q : normOneGL E a) : GA E a)

theorem resQ_mk {φ : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) (x : normOneGL E a) :
    resQ φ (RightCosetSpace.mk _ x) = φ x := by
  have e : RightCosetSpace.mk (rationalGLOne E a)
      (Quotient.out (RightCosetSpace.mk (rationalGLOne E a) x)) = RightCosetSpace.mk _ x :=
    Quotient.out_eq _
  obtain ⟨γ, hγ⟩ := RightCosetSpace.mk_eq_mk_iff.1 e
  obtain ⟨δ, hδ⟩ : ((γ : normOneGL E a) : GA E a) ∈ AdelicGLn.rationalGL E a := γ.2
  unfold resQ
  rw [← hγ]
  change φ (((γ : normOneGL E a) : GA E a) * (x : GA E a)) = _
  rw [← hδ]
  exact h δ x.1

theorem continuous_resQ {φ : GA E a → ℂ} (hc : Continuous φ) (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) :
    Continuous (resQ φ) := by
  refine (RightCosetSpace.isOpenQuotientMap_mk (rationalGLOne E a)).isQuotientMap.continuous_iff.2 ?_
  have : resQ φ ∘ RightCosetSpace.mk (rationalGLOne E a) = fun x : normOneGL E a => φ x :=
    funext fun x => resQ_mk h x
  rw [this]
  exact hc.comp continuous_subtype_val

end GlobalTheory.CompanionTheory.CuspTransfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7} {r : ℕ}

def rs (σ : (D.what₂.Tau → ℂ) →+ AE D) (s : ℝ) : AE D := σ fun _ => (s : ℂ)

theorem rs_add (σ : (D.what₂.Tau → ℂ) →+ AE D) (s t : ℝ) : rs σ (s + t) = rs σ s + rs σ t := by
  unfold rs
  rw [← map_add]
  congr 1
  funext τ
  simp

theorem rs_zero (σ : (D.what₂.Tau → ℂ) →+ AE D) : rs σ 0 = 0 := by
  unfold rs
  have : (fun _ : D.what₂.Tau => ((0 : ℝ) : ℂ)) = 0 := by funext; simp
  rw [this, map_zero]

theorem finPart_cA (z : AE D) :
    finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

theorem cA_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (s : ℝ) :
    cA D (rs σ s) = rs σ s := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [RingHom.map_sub, finPart_cA, h0, map_zero, sub_zero]
  · have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
    rw [RingHom.map_sub, RingHom.map_sub, GlobalTheory.PhaseReal.infPart_cA,
      GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hσ.inf τ)]
    unfold rs
    rw [hσ.comp]
    simp

theorem continuous_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    Continuous (rs σ) :=
  hσ.cont.comp (continuous_pi fun _ => Complex.continuous_ofReal)

def path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ℝ →+ hermA D r where
  toFun s := ⟨rs σ s • a.1.map (incA D), by
    show adj (rs σ s • a.1.map (incA D)) = rs σ s • a.1.map (incA D)
    rw [adj_smul, cA_rs hσ]
    congr 1
    exact GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA a⟩
  map_zero' := by
    apply Subtype.ext
    show rs σ 0 • a.1.map (incA D) = 0
    rw [rs_zero, zero_smul]
  map_add' s t := by
    apply Subtype.ext
    show rs σ (s + t) • a.1.map (incA D) = rs σ s • a.1.map (incA D) + rs σ t • a.1.map (incA D)
    rw [rs_add, add_smul]

def lam (θ : InfFam D) (α : D.host.F) (t : AE D) : ℝ :=
  -∑ τ, (θ τ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re

def multM (θ : InfFam D) (α : D.host.F) (V : HSp D) (a : HermE D r) (y : Mx D V.rank r) : ℝ :=
  lam θ α (Matrix.trace (HMul.hMul (a.1.map (incA D)) (inner V y y) : Mx D r r))

def pairF (θ : InfFam D) (α : D.host.F) (a β : HermE D r) : ℝ :=
  lam θ α (incA D (Matrix.trace (β.1 * a.1)))

end GlobalTheory.CompanionTheory.WSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowthStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_moderate_growth_alt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), IsAutForm φ → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth | exact GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth | (intros; apply GlobalTheory.CompanionTheory.CTFin.Growth.ct_growth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGenericStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_is_generic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π := by
  first | exact @GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | exact GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal | (intros; apply GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal <;> assumption)
end

