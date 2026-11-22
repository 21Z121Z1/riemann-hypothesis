import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrder
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem extend_step {R : Type} [CommRing R] (K : DCx.{w} R) (n b : ℕ) (x : ∀ p q, K.X p q) (hx : x ∈ K.T n)
    (h0 : ∀ p r, p < b → K.D x p r = 0)
    (hB : ∀ q, b + q = n + 1 → K.D x b q ∈ (K.col b).B q) :
    ∃ x' : ∀ p q, K.X p q, x' ∈ K.T n ∧ (∀ p r, p < b → x' p r = x p r) ∧
      ∀ p r, p < b + 1 → K.D x' p r = 0 := by
  have hD : K.D x ∈ K.T (n + 1) := K.D_mem n x hx
  by_cases hbn : b ≤ n
  · obtain ⟨r, rfl⟩ : ∃ r, n = b + r := ⟨n - b, by omega⟩
    obtain ⟨y, hy⟩ := CrystallineSemistableComparison.Cx.mem_B_succ.mp (hB (r + 1) (by omega))
    have hy' : K.dv b r y = K.D x b (r + 1) := hy
    refine ⟨x - K.sgl b r (((-1 : ℤ) ^ b) • y), sub_mem hx ?_, ?_, ?_⟩
    · intro p q hpq
      exact K.sgl_ne _ (by omega)
    · intro p r' hp
      simp only [Pi.sub_apply]
      rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
    · intro p r' hp
      simp only [map_sub, CrystallineSemistableComparison.DCx.D_sgl, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      rw [K.sgl_ne _ (Or.inl (by omega)), zero_add]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
      · rw [h0 p r' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]
      · by_cases hr : r' = r + 1
        · subst hr
          rw [K.sgl_self, map_zsmul, hy', smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, sub_self]
        · have h1 : K.D x p r' = 0 := hD p r' (by omega)
          rw [h1, K.sgl_ne _ (Or.inr hr), smul_zero, sub_zero]
  · refine ⟨x, hx, fun _ _ _ => rfl, ?_⟩
    intro p r hp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
    · exact h0 p r hp
    · by_cases hr : p + r = n + 1
      · obtain rfl : r = 0 := by omega
        exact CrystallineSemistableComparison.Cx.mem_B_zero.mp (hB 0 hr)
      · exact hD p r hr

theorem leadE_surjective {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hac : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    Function.Surjective (leadE K j a (n := a + j)) := by
  intro t
  obtain ⟨c, hc, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (colH K a) j).1 t
  obtain ⟨y, hy, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K.col j) a).1 c
  have hcls : ∀ (C : CrystallineSemistableComparison.Cx R) (m : ℕ) (u v : C.X m) (hu : C.d m u = 0) (hv : C.d m v = 0),
      u = v → C.cls u hu = C.cls v hv := by
    rintro C m u v hu hv rfl
    rfl
  have hy' : K.dv j a y = 0 := hy
  have hdh : K.dh j a y ∈ (K.col (j + 1)).B a := by
    have hb : (K.col (j + 1)).d a ((colMap K j).f a y) = 0 := by
      show K.dv (j + 1) a (K.dh j a y) = 0
      rw [← K.hv j a y, hy', map_zero]
    have h1 : (colMap K j).mapH a ((K.col j).cls y hy) = 0 := hc
    rw [CrystallineSemistableComparison.P.mapH_cls (colMap K j) a y hy hb] at h1
    exact ((CrystallineSemistableComparison.P.cls_surj (K.col (j + 1)) a).2.1 _ hb).mp h1
  have hmemT : ∀ (m : ℕ) (u : ∀ p q, K.X p q), u ∈ K.T m ↔ ∀ p q, p + q ≠ m → u p q = 0 :=
    fun _ _ => Iff.rfl
  have hx0 : K.sgl j a y ∈ K.T (a + j) := (hmemT _ _).2 fun p q hpq => K.sgl_ne y (by omega)
  have hDx0 : ∀ p r, p < j + 1 → K.D (K.sgl j a y) p r = 0 := by
    intro p r hp
    rw [CrystallineSemistableComparison.DCx.D_sgl, hy', map_zero, smul_zero, add_zero, K.sgl_ne _ (Or.inl (by omega))]
  have hstep : ∀ k : ℕ, ∃ x ∈ K.T (a + j), (∀ p r, p < j + 1 → x p r = K.sgl j a y p r) ∧
      ∀ p r, p < j + 2 + k → K.D x p r = 0 := by
    intro k
    induction k with
    | zero =>
      obtain ⟨x', hx', hag, hD'⟩ := extend_step K (a + j) (j + 1) (K.sgl j a y) hx0 hDx0 (by
        intro q hq
        obtain rfl : q = a := by omega
        rw [CrystallineSemistableComparison.DCx.D_sgl, hy', map_zero, smul_zero, add_zero, K.sgl_self]
        exact hdh)
      exact ⟨x', hx', hag, fun p r hp => hD' p r (by omega)⟩
    | succ k ih =>
      obtain ⟨x, hx, hag, hD⟩ := ih
      obtain ⟨x', hx', hag', hD'⟩ := extend_step K (a + j) (j + 2 + k) x hx hD (by
        intro q hq
        have hqa : q < a := by omega
        have hdv : (K.col (j + 2 + k)).d q (K.D x (j + 2 + k) q) = 0 :=
          dv_lead K (K.D x) (K.DD x) (j + 2 + k) q hD
        have := hac (j + 2 + k) q hqa
        exact ((CrystallineSemistableComparison.P.cls_surj (K.col (j + 2 + k)) q).2.1 _ hdv).mp (Subsingleton.elim _ _))
      exact ⟨x', hx', fun p r hp => (hag' p r (by omega)).trans (hag p r hp),
        fun p r hp => hD' p r (by omega)⟩
  obtain ⟨x, hx, hag, hD⟩ := hstep a
  have hD0 : K.D x = 0 := by
    funext p r
    by_cases hp : p < j + 2 + a
    · exact hD p r hp
    · exact (hmemT _ _).1 (K.D_mem _ x hx) p r (by omega)
  have hZ : (⟨x, hx⟩ : K.T (a + j)) ∈ K.tot.Z (a + j) := LinearMap.mem_ker.2 (Subtype.ext hD0)
  have hxy : x j a = y := (hag j a (by omega)).trans (K.sgl_self j a y)
  have hzf : (⟨⟨x, hx⟩, hZ⟩ : K.tot.Z (a + j)) ∈ Zf K (a + j) j := by
    intro p q hp
    exact (hag p q (by omega)).trans (K.sgl_ne y (Or.inl (by omega)))
  refine ⟨⟨⟨⟨x, hx⟩, hZ⟩, hzf⟩, ?_⟩
  rw [leadE_eq]
  apply hcls
  rw [leadC_eq K j a _ (by show (K.col j).d a (x j a) = 0; rw [hxy]; exact hy)]
  exact hcls _ _ _ _ _ _ hxy

end GlobalTheory.CompanionTheory.CechSerre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre.RowKer

variable {R : Type} [CommRing R] (K : DCx.{w} R)

theorem Dv_mem (W : ∀ p q, K.X p q) (p q : ℕ) : K.Dv W p q ∈ (K.col p).B q := by
  cases q with
  | zero =>
    have h : K.Dv W p 0 = 0 := by cases p <;> rfl
    rw [h]
    exact Submodule.zero_mem _
  | succ q => exact ⟨W p q, rfl⟩

theorem dv_low (W x : ∀ p q, K.X p q) (hD : K.D W = x) (k q : ℕ) (h0 : ∀ p q, p < k → W p q = 0)
    (hx : x k (q + 1) = 0) : K.dv k q (W k q) = 0 := by
  have h1 := congrFun (congrFun hD k) (q + 1)
  rw [DCx.D_apply, hx] at h1
  have h2 : K.Dh W k (q + 1) = 0 := by
    cases k with
    | zero => rfl
    | succ k =>
      show K.dh k (q + 1) (W k (q + 1)) = 0
      rw [h0 k _ (by omega), map_zero]
  rw [h2, zero_add] at h1
  exact Auxfb.zsm_cancel k _ h1

theorem push_step (n k q : ℕ) (hkq : k + q + 1 = n) (W : ∀ p q, K.X p q)
    (hs : ∀ p q, p + q + 1 ≠ n → W p q = 0) (h0 : ∀ p q, p < k → W p q = 0)
    (hv : K.dv k q (W k q) = 0) (hH : Subsingleton ((K.col k).H q)) (hq : 0 < q) :
    ∃ W' : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W' p q = 0) ∧ K.D W' = K.D W ∧
      ∀ p q, p < k + 1 → W' p q = 0 := by
  have hB : W k q ∈ (K.col k).B q :=
    ((P.cls_surj (K.col k) q).2.1 _ hv).1 (Subsingleton.elim _ _)
  obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨y, hy⟩ := hB
  have hy' : K.dv k q y = W k (q + 1) := hy
  have hsq : ((-1 : ℤ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  have hDY : K.D (K.sgl k q ((-1 : ℤ) ^ k • y)) =
      K.sgl (k + 1) q (K.dh k q ((-1 : ℤ) ^ k • y)) + K.sgl k (q + 1) (W k (q + 1)) := by
    rw [K.D_sgl, map_zsmul (K.dv k q), hy', map_zsmul (K.sgl k (q + 1)), smul_smul, hsq, one_smul]
  refine ⟨W - K.D (K.sgl k q ((-1 : ℤ) ^ k • y)), fun p r h => ?_, ?_, fun p r hp => ?_⟩
  · rw [hDY, Pi.sub_apply, Pi.sub_apply, Pi.add_apply, Pi.add_apply, hs p r h,
      K.sgl_ne _ (by omega : p ≠ k + 1 ∨ r ≠ q), K.sgl_ne _ (by omega : p ≠ k ∨ r ≠ q + 1)]
    simp
  · rw [map_sub, K.DD, sub_zero]
  · rw [hDY, Pi.sub_apply, Pi.sub_apply, Pi.add_apply, Pi.add_apply,
      K.sgl_ne _ (by omega : p ≠ k + 1 ∨ r ≠ q), zero_add]
    by_cases h : p = k ∧ r = q + 1
    · obtain ⟨rfl, rfl⟩ := h
      rw [K.sgl_self, sub_self]
    · rw [K.sgl_ne _ (by omega : p ≠ k ∨ r ≠ q + 1), sub_zero]
      by_cases hpk : p < k
      · exact h0 p r hpk
      · exact hs p r (by omega)

theorem push (n a i : ℕ) (hn : n = a + (i + 1)) (W : ∀ p q, K.X p q)
    (hs : ∀ p q, p + q + 1 ≠ n → W p q = 0) (hx : ∀ p q, p < i + 1 → K.D W p q = 0)
    (hac : ∀ p q, a < q → Subsingleton ((K.col p).H q)) (k : ℕ) (hk : k ≤ i) :
    ∃ W' : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W' p q = 0) ∧ K.D W' = K.D W ∧
      ∀ p q, p < k → W' p q = 0 := by
  induction k with
  | zero => exact ⟨W, hs, rfl, fun p q hp => absurd hp (Nat.not_lt_zero p)⟩
  | succ k ih =>
    obtain ⟨W₁, hs₁, hD₁, h₁⟩ := ih (by omega)
    have hv : K.dv k (a + i - k) (W₁ k (a + i - k)) = 0 :=
      dv_low K W₁ _ rfl k _ h₁ (by rw [hD₁]; exact hx k _ (by omega))
    obtain ⟨W₂, hs₂, hD₂, h₂⟩ := push_step K n k (a + i - k) (by omega) W₁ hs₁ h₁ hv
      (hac k _ (by omega)) (by omega)
    exact ⟨W₂, hs₂, hD₂.trans hD₁, h₂⟩

theorem exists_prim {n : ℕ} (z : K.tot.Z n) (hz : K.tot.cls z.1 z.2 = 0) :
    ∃ W : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W p q = 0) ∧ K.D W = z.1.1 := by
  have hB : z.1 ∈ K.tot.B n := ((P.cls_surj K.tot n).2.1 _ _).1 hz
  cases n with
  | zero =>
    have h : z.1 = 0 := (Submodule.mem_bot R).1 hB
    refine ⟨0, fun _ _ _ => rfl, ?_⟩
    rw [h, map_zero]
    rfl
  | succ m =>
    obtain ⟨u, hu⟩ := hB
    exact ⟨u.1, fun p q h => u.2 p q (by omega), congrArg Subtype.val hu⟩

theorem leadE_eq_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ),
    (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, clsZ K (a + j) j z = 0 → leadE K j a z = 0 := by
  intro R _ K a j hac z hz
  obtain ⟨W, hs, hD⟩ := exists_prim K z.1 hz
  have hv : (K.col j).d a (z.1.1.1 j a) = 0 := dv_lead K _ (D_zero K z.1) j a z.2
  suffices h : leadC K j a z ∈ (colH K a).B j by
    rw [leadE_eq]
    exact ((P.cls_surj (colH K a) j).2.1 _ _).2 h
  cases j with
  | zero =>
    have h1 : z.1.1.1 0 a ∈ (K.col 0).B a := by
      rw [← hD, DCx.D_apply]
      have h2 : K.Dh W 0 a = 0 := rfl
      rw [h2, zero_add, pow_zero, one_smul]
      exact Dv_mem K W 0 a
    show _ ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, leadC_eq K 0 a z hv]
    exact ((P.cls_surj _ a).2.1 _ hv).2 h1
  | succ i =>
    obtain ⟨W', -, hD', h0⟩ := push K (a + (i + 1)) a i rfl W hs
      (fun p q hp => by rw [hD]; exact z.2 p q hp) hac i le_rfl
    have hD'' : K.D W' = z.1.1.1 := hD'.trans hD
    have hy : K.dv i a (W' i a) = 0 := dv_low K W' _ hD'' i a h0 (z.2 i _ (by omega))
    have hb : (K.col (i + 1)).d a ((colMap K i).f a (W' i a)) = 0 := by
      rw [(colMap K i).comm]
      exact (congrArg _ hy).trans (map_zero _)
    refine ⟨(K.col i).cls _ hy, ?_⟩
    show (colMap K i).mapH a _ = leadC K (i + 1) a z
    rw [P.mapH_cls _ a _ hy hb, leadC_eq K (i + 1) a z hv]
    refine ((P.cls_surj _ a).2.2.1 _ _ hb hv).2 ?_
    have h2 : z.1.1.1 (i + 1) a = K.dh i a (W' i a) + (-1 : ℤ) ^ (i + 1) • K.Dv W' (i + 1) a := by
      rw [← hD'', DCx.D_apply]
      rfl
    have e : (colMap K i).f a (W' i a) - z.1.1.1 (i + 1) a =
        -((-1 : ℤ) ^ (i + 1) • K.Dv W' (i + 1) a) := by
      rw [h2]
      show K.dh i a (W' i a) - _ = _
      abel
    rw [e]
    exact Submodule.neg_mem _ (zsmul_mem (Dv_mem K W' (i + 1) a) _)

end GlobalTheory.CompanionTheory.CechSerre.RowKer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHalfHoldsStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_half_holds : EisHalf := by
  first | exact @GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf | exact GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf | (intros; apply GlobalTheory.CompanionTheory.SiegelEisHalf.eisHalf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotalStatement
section
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euclidean_total : EucTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal | exact GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.EucT.eucTotal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyOfSectionPlaces
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSec

private theorem exists_heightOneSpectrum_under_maximalRealSubfield {E : Type} [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := by
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (Ideal.comap_bot_le_of_injective _ hinj)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _ hinj
  exact ⟨⟨Q, hQp, hQne⟩, HeightOneSpectrum.ext hQ⟩

theorem eventually_cofinite_of_section :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ P : PlF E → Prop,
  (∀ᶠ w : {w : Pl E // w ∈ S} in cofinite, P (w.1.under (𝓞 (maximalRealSubfield E)))) → ∀ᶠ v in cofinite, P v := by
  intro E _ _ _ S hS P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  refine (hP.image fun w : {w : Pl E // w ∈ S} => w.1.under (𝓞 (maximalRealSubfield E))).subset ?_
  intro v hv
  obtain ⟨w₀, hw₀⟩ := exists_heightOneSpectrum_under_maximalRealSubfield v
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w₀
  exact ⟨⟨u, huS⟩, show ¬P (u.under _) by rw [hu, hw₀]; exact hv, hu.trans hw₀⟩

end GlobalTheory.CompanionTheory.LocHypSec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrderStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_segment_order : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), ∃ σ : Equiv.Perm (Fin h), IsCanon (Γ ∘ σ) := by
  first | exact @GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon | exact GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon | (intros; apply GlobalTheory.CompanionTheory.CanonOrder.exists_isCanon <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFormNonvanishingOnChartStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_nonvanishing_on_chart : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (U : X.Opens), genericPoint X ∈ U → ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧
      j ∉ ptIdeal (i (genericPoint X)) ∧ ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
        GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ U := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianFormStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_hermitian_form : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  first | exact @GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm | exact GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm | (intros; apply GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.IrrSub

def subIncl {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem subIncl_injective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) : Function.Injective (subIncl S) :=
  Subtype.val_injective

theorem hasFiniteLength_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : IsSubquotient σ ρ) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by
  obtain ⟨T, f, hf⟩ := h
  exact GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective f hf
    (GlobalTheory.ProdLength.hasFiniteLength_of_injective (subIncl T) (subIncl_injective T) hρ)

theorem exists_isAtom {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} [Nontrivial V] (h : HasFiniteLength ρ) :
    ∃ S : Subrepresentation ρ, IsAtom S := by
  have hbt : (⊤ : Subrepresentation ρ) ≠ ⊥ := by
    intro e
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [e] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨S, hS, -⟩ := GlobalTheory.CompanionTheory.JacExp.exists_atom_le h hbt
  exact ⟨S, hS⟩

theorem exists_irrRep_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin n) k) V) (A₀ : Representation ℂ (GL (Fin n) k) W),
    IsSmooth A → Nontrivial V → IsSubquotient A A₀ → HasFiniteLength A₀ →
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap A), Function.Injective f := by
  intro k _ _ _ _ n V W _ _ _ _ A A₀ hsm hnt hsub hfl
  obtain ⟨S, hS⟩ := exists_isAtom (hasFiniteLength_of_isSubquotient hsub hfl)
  exact ⟨⟨S.toSubmodule, S.toRepresentation, GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsm S,
    GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS⟩, subIncl S, subIncl_injective S⟩

end GlobalTheory.CompanionTheory.IrrSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegativeSchwartzBumpStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonnegative_schwartz_bump : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : Set (κ → AF F)), IsOpen N → ∀ z₀ ∈ N, ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N → Φ z = 0) ∧ 0 < (Φ z₀).re := by
  first | exact @GlobalTheory.CompanionTheory.AdelicBump.exists_bump | exact GlobalTheory.CompanionTheory.AdelicBump.exists_bump | (intros; apply GlobalTheory.CompanionTheory.AdelicBump.exists_bump <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalizationStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tamagawa_measure_normalization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ n : ℕ, ∃ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf ∧ (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) ∧ IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ b laminf n) minf ∧ ∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ b (lam v) n) (m v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres | exact GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormula
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem map_cols0 {R S : Type*} [Zero R] [Zero S] {a r t n : ℕ} (f : R → S) (hf : f 0 = 0)
    (e : Fin n ≃ Fin r ⊕ Fin t) (x : Matrix (Fin a) (Fin r) R) :
    ((Matrix.fromCols x (0 : Matrix (Fin a) (Fin t) R)).submatrix id e).map f =
      (Matrix.fromCols (x.map f) (0 : Matrix (Fin a) (Fin t) S)).submatrix id e := by
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp
  · simp [hf]

theorem mul_cols0 {R : Type*} [NonUnitalNonAssocSemiring R] {a b r t n : ℕ}
    (e : Fin n ≃ Fin r ⊕ Fin t) (A : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin r) R) :
    A * (Matrix.fromCols x (0 : Matrix (Fin b) (Fin t) R)).submatrix id e =
      (Matrix.fromCols (A * x) (0 : Matrix (Fin a) (Fin t) R)).submatrix id e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp [Matrix.mul_apply]
  · simp

theorem extension_by_zero_orbit_action : Ext0 := by
  intro D n t W hn x₀ h
  have h1 : (rat (L.ext0 hn x₀) : Matrix (Fin W.rank) (Fin n) (AE D)) =
      (Matrix.fromCols (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
        (0 : Matrix (Fin W.rank) (Fin t) (AE D))).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm :=
    map_cols0 (incA D) (map_zero _) _ x₀
  have h2 := mul_cols0 (t := t) (finSumFinEquiv.trans (finCongr hn)).symm (mt W h⁻¹)
    (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
  exact (congrArg (fun M => mt W h⁻¹ * M) h1).trans h2

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

