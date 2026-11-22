import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasicLift
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AntisymProdEqSumQuantumMinorStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antisym_prod_eq_sum_quantumMinor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin m) (Fin (p + m)) ℂ) (Λ : Matrix (Fin (p + m)) (Fin p) ℂ) (N : Matrix (Fin p) (Fin p) ℂ) (w : ℂ), ∑ σ : Equiv.Perm (Fin (p + m)), (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k : Fin p, (Λ * N) (σ (Fin.castAdd m k)) k) • (List.ofFn fun k : Fin m => ∑ d, Q k d • Tm E (w - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod = N.det • ∑ c : Fin m → Fin (p + m), ∑ d : Fin m → Fin (p + m), ((Matrix.of fun a : Fin (p + m) => Fin.append (Λ a) (fun k : Fin m => if a = c k then (1 : ℂ) else 0)).det * ((∏ k, Q k (d k)) * ((m.factorial : ℕ) : ℂ)⁻¹)) • qminor E c d w := by
  first | exact @GlobalTheory.ScalarColsMinor.antisym_prod_eq_sum_qminor | exact GlobalTheory.ScalarColsMinor.antisym_prod_eq_sum_qminor | (intros; apply GlobalTheory.ScalarColsMinor.antisym_prod_eq_sum_qminor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreeIdentity
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPhi

theorem hsInner_smul_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (a b : ℂ) (A A' : Wq →L[ℂ] Wp) :
    B.hsInner (a • A) (b • A') = a * star b * B.hsInner A A' := by
  have h : ∀ (c : ℂ) (Y : Wq →L[ℂ] Wp), B.hsVec (c • Y) = c • B.hsVec Y := fun c Y => rfl
  unfold B.hsInner
  rw [h, h, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  ring

theorem isUnit_det_of_mem {k r : ℕ} {g : Mx k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have h : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h1 : (Formalism.QuantumDeterminants.Hpk k r * (gᴴ * Formalism.QuantumDeterminants.Hpk k r)) * g = 1 := by
    rw [Matrix.mul_assoc, h]; exact PI.HwUniqW.Hpk_mul_self
  exact Matrix.isUnit_det_of_left_inverse h1

theorem haar_left {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem Ph_coeff : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDS ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  intro hH k r ε mu R Wp _ _ _ _ Wq _ _ _ _ D dd hR hdd x y x' y' X X' p hp
  obtain ⟨hmul, hone, hinner, -, -, -, -, ⟨w, hw, -⟩, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hR
  obtain ⟨c, -, hc⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r ε D.μG (haar_left D.haarG)
  obtain ⟨hdeg, hS⟩ := hc mu R hR
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hd : c * Formalism.QuantumDeterminants.fdegHC mu = dd := (hdeg w hw0).symm.trans (hdd w hw0)
  obtain ⟨hI, hE⟩ := hS (R.σ (JF.sR p) y) (R.σ (JF.sL p) x) y' x'
  rw [hd] at hE
  have ha : (Matrix.of p.1.1 : Mx k r) ∈ GG k r := hp.1.1
  have hb : (Matrix.of p.1.2 : Mx k r) ∈ GG k r := hp.2.1.1
  have hc' : (Matrix.of p.2.1 : Mx k r) ∈ GG k r := hp.2.2.1.1
  have hd' : (Matrix.of p.2.2 : Mx k r) ∈ GG k r := hp.2.2.2.1
  have hL : JF.sL p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hb ha
  have hRR : JF.sR p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd' hc'
  have hLi : (JF.sL p)⁻¹ ∈ GG k r := PI.HwUniqW.inv_mem_UH hL
  set Y := (D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹)) with hY
  have key : ∀ g ∈ GG k r, B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) g) (⟪x', R.σ g y'⟫_ℂ • X') =
      ⟪R.σ (JF.sL p) x, R.σ g (R.σ (JF.sR p) y)⟫_ℂ * star ⟪x', R.σ g y'⟫_ℂ * B.hsInner Y X' := by
    intro g hg
    have e1 : B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) g = ⟪x, R.σ (B.sgs p g) y⟫_ℂ • Y := by
      unfold B.rho
      rw [hY, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    have e2 : B.sgs p g = (JF.sL p)⁻¹ * (g * JF.sR p) := by
      unfold B.sgs JF.sL JF.sR
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    have hgR : g * JF.sR p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg hRR
    have e3 : ⟪x, R.σ (B.sgs p g) y⟫_ℂ = ⟪R.σ (JF.sL p) x, R.σ g (R.σ (JF.sR p) y)⟫_ℂ := by
      rw [← hinner _ hL, e2, ← hmul _ hL _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hLi hgR), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_mem hL), Matrix.one_mul, hmul _ hg _ hRR]
    rw [e1, e3, hsInner_smul_smul]
  have hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mx k r) ∈ GG k r := by
    rw [ae_iff]; exact D.haarG.conc
  have hae2 : (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g))
      (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) =ᵐ[D.μG] fun g => ⟪R.σ (JF.sL p) x, R.σ (Matrix.of g) (R.σ (JF.sR p) y)⟫_ℂ *
        star ⟪x', R.σ (Matrix.of g) y'⟫_ℂ * B.hsInner Y X' := hae.mono fun g hg => key _ hg
  refine ⟨(hI.mul_const _).congr hae2.symm, ?_⟩
  unfold B.Ph
  rw [integral_congr_ae hae2, integral_mul_const, hE]

end GlobalTheory.BesselPhi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFrameEntryRelationStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_frame_entry_relation : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsBes R z π l → ∀ i j : Fin k, ∀ v ∈ R.sm, l (R.dC (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) v) = Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) (l v) := by
  first | exact @GlobalTheory.BesselIntertwine.bessel_intertwines_glW | exact GlobalTheory.BesselIntertwine.bessel_intertwines_glW | (intros; apply GlobalTheory.BesselIntertwine.bessel_intertwines_glW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotentStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGrowth_stabilizer_unipotent : Formalism.FourierDecayAlt.ThreeDimData.GrowthS := by
  first | exact @GlobalTheory.besselGrowthS | exact GlobalTheory.besselGrowthS | (intros; apply GlobalTheory.besselGrowthS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselLieTriangularVanishingStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_functional_lie_triangular_eq_character_smul : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), Formalism.QuantumDeterminants.inWb k r z → (∀ x, π 1 x = x) → IsBes R z π l → ∀ Y : Mx k r, (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → Y i j = 0) → ∀ v ∈ R.sm, l (R.dC Y v) = (Formalism.QuantumDeterminants.ell k r z Y - star (Formalism.QuantumDeterminants.ell k r z (-((Formalism.QuantumDeterminants.Hpk k r) * Yᴴ * (Formalism.QuantumDeterminants.Hpk k r))))) • l v := by
  first | exact @GlobalTheory.BesselNilp.bessel_dC | exact GlobalTheory.BesselNilp.bessel_dC | (intros; apply GlobalTheory.BesselNilp.bessel_dC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSumDecompositionStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) := by
  first | exact @GlobalTheory.KapBes.main | exact GlobalTheory.KapBes.main | (intros; apply GlobalTheory.KapBes.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetConjugateTopCoefficient
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.CapelliTop

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem prod_ofFn_sum_smul {t n : ℕ} (q : Fin t → Fin n → ℂ) (x : Fin t → Fin n → A) :
    (List.ofFn fun k : Fin t => ∑ d, q k d • x k d).prod =
      ∑ d : Fin t → Fin n, (∏ k, q k (d k)) • (List.ofFn fun k => x k (d k)).prod := by
  classical
  rw [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply]

theorem qminor_eq_zero {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (d : Fin n → Fin n)
    (hd : ¬ Function.Injective d) (u : ℂ) : qminor E id d u = 0 := by
  simp only [Function.Injective, not_forall] at hd
  obtain ⟨i, j, hij, hne⟩ := hd
  have h := quantumMinorColSkew_holds A n n E hE id d (Equiv.swap i j) u
  have e : d ∘ Equiv.swap i j = d := by
    funext k
    exact Equiv.apply_swap_eq_self hij k
  rw [e, Equiv.Perm.sign_swap hne] at h
  apply eq_zero_of_add_self_eq_zero
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  exact add_eq_zero_iff_eq_neg.mpr h

theorem det_smul_qdet {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (Q : Matrix (Fin n) (Fin n) ℂ)
    (u : ℂ) : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod := by
  classical
  have h1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => ∑ d, Q k d • Tm E (u - (k : ℂ)) (σ k) d).prod =
      ∑ d : Fin n → Fin n, (∏ k, Q k (d k)) • qminor E id d u := by
    simp only [Finset.smul_sum, qminor]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [prod_ofFn_sum_smul (fun k d => Q k d) (fun k d => Tm E (u - (k : ℂ)) (σ k) d),
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  rw [h1, ← Matrix.det_transpose, Matrix.det_apply', Finset.sum_smul]
  refine Fintype.sum_of_injective (fun τ : Equiv.Perm (Fin n) => (τ : Fin n → Fin n))
    DFunLike.coe_injective _ _ ?_ ?_
  · intro d hd
    rw [qminor_eq_zero E hE d, smul_zero]
    intro hinj
    exact hd ⟨Equiv.ofBijective d (Finite.injective_iff_bijective.mp hinj), rfl⟩
  · intro τ
    have h := quantumMinorColSkew_holds A n n E hE id id τ u
    rw [Function.id_comp] at h
    rw [h, mul_comm, mul_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl

theorem mul_pow_shift (x y δ : A) (h : x * δ = δ * (x + y)) (hy : y * δ = δ * y) (s : ℕ) :
    x * δ ^ s = δ ^ s * (x + (s : ℂ) • y) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, mul_assoc, add_mul, h, smul_mul_assoc, hy,
      Nat.cast_succ, add_smul, one_smul, ← mul_smul_comm, ← mul_add]
    congr 2
    abel

theorem prod_ofFn_semiconj {t : ℕ} (x y : Fin t → A) (g : A) (h : ∀ k, x k * g = g * y k) :
    (List.ofFn x).prod * g = g * (List.ofFn y).prod := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [mul_assoc, ih _ _ (fun k => h k.succ), ← mul_assoc, h, mul_assoc]

theorem pt_prod {t : ℕ} (x y : Fin t → A) :
    TL.PT t (fun s : ℂ => (List.ofFn fun k => x k + s • y k).prod) (List.ofFn y).prod := by
  induction t with
  | zero => exact (TL.PT.const 1).congr (fun s => by simp) (by simp)
  | succ t ih =>
    have h := ih (fun k => x k.succ) (fun k => y k.succ)
    refine ((h.mulL (x 0)).up.add (h.mulL (y 0)).mulS).congr (fun s => ?_) ?_
    · simp only [List.ofFn_succ, List.prod_cons, add_mul, smul_mul_assoc]
    · simp only [List.ofFn_succ, List.prod_cons, zero_add]

theorem sum_smul_Tm {n : ℕ} (E : Fin n → Fin n → A) (q : Fin n → ℂ) (u : ℂ) (a : Fin n) :
    ∑ d, q d • Tm E u a d = (q a * u) • (1 : A) + ∑ d, q d • E a d := by
  simp [shiftedGenerator_eq_ite_smul_add, Finset.sum_add_distrib, smul_smul, ite_smul]

theorem top_coefficient : ∀ (A : Type) [Ring A] [Algebra ℂ A] (p m : ℕ) (E : Fin (p + m) → Fin (p + m) → A) (Q : Matrix (Fin (p + m)) (Fin (p + m)) ℂ) (δ : A) (ν : Fin (p + m) → Fin p → A) (u : ℂ), GlRel E → (∀ a k, (∑ d, Q (Fin.castAdd m k) d • E a d) * δ = δ * ((∑ d, Q (Fin.castAdd m k) d • E a d) + ν a k)) → (∀ a k, (∑ d, Q (Fin.natAdd p k) d • E a d) * δ = δ * ∑ d, Q (Fin.natAdd p k) d • E a d) → (∀ a k, ν a k * δ = δ * ν a k) → Q.det • ∑ s : Fin (p + 1), ((F7.lagCo (fun j : Fin (p + 1) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) = δ ^ p * ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ((List.ofFn fun k : Fin p => ν (σ (Fin.castAdd m k)) k).prod * (List.ofFn fun k : Fin m => ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod) := by
  intro A _ _ p m E Q δ ν u hE h1 h2 h3
  set X : Equiv.Perm (Fin (p + m)) → Fin p → A := fun σ k =>
    ∑ d, Q (Fin.castAdd m k) d • Tm E (u - ((k : ℕ) : ℂ)) (σ (Fin.castAdd m k)) d with hX
  set Y : Equiv.Perm (Fin (p + m)) → A := fun σ => (List.ofFn fun k : Fin m =>
    ∑ d, Q (Fin.natAdd p k) d • Tm E (u - (p : ℂ) - ((k : ℕ) : ℂ)) (σ (Fin.natAdd p k)) d).prod with hY
  have e1 : Q.det • qdet E u = ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      ((List.ofFn (X σ)).prod * Y σ) := by
    rw [det_smul_qdet E hE]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [List.ofFn_add, List.prod_append]
    simp only [hX, hY, Fin.val_natAdd, Nat.cast_add, sub_sub]
    rfl
  have eY : ∀ σ (s : ℕ), Y σ * δ ^ s = δ ^ s * Y σ := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => Commute.pow_right (?_ : _ * _ = _ * _) s
    rw [sum_smul_Tm, add_mul, mul_add, h2]
    simp
  have eX : ∀ σ (s : ℕ), (List.ofFn (X σ)).prod * δ ^ s =
      δ ^ s * (List.ofFn fun k => X σ k + (s : ℂ) • ν (σ (Fin.castAdd m k)) k).prod := by
    intro σ s
    refine prod_ofFn_semiconj _ _ _ fun k => mul_pow_shift _ _ _ ?_ (h3 _ _) s
    simp only [hX]
    rw [sum_smul_Tm, add_mul, h1, add_assoc, mul_add δ (_ • _)]
    simp
  have e2 : ∀ s : Fin (p + 1), Q.det • (δ ^ (p - (s : ℕ)) * (qdet E u * δ ^ (s : ℕ))) =
      ∑ σ : Equiv.Perm (Fin (p + m)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (δ ^ p *
        ((List.ofFn fun k => X σ k + ((s : ℕ) : ℂ) • ν (σ (Fin.castAdd m k)) k).prod * Y σ)) := by
    intro s
    rw [← mul_smul_comm, ← smul_mul_assoc, e1, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_assoc, eY, ← mul_assoc _ (δ ^ (s : ℕ)), eX, mul_assoc,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp s.isLt)]
  rw [Finset.smul_sum, Finset.mul_sum]
  simp only [smul_comm Q.det, e2, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := (((pt_prod (X σ) (fun k => ν (σ (Fin.castAdd m k)) k)).mulR (Y σ)).mulL (δ ^ p)).lag
  rw [mul_smul_comm]
  refine Eq.trans ?_ (congrArg _ h.symm)
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

end GlobalTheory.CapelliTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem comp_eq_sum_inner_smul_rankOne {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ Wp) (c : OrthonormalBasis κ ℂ Wq)
    (P : H →L[ℂ] Wp) (A : H →L[ℂ] H) (Q : Wq →L[ℂ] H) :
    P.comp (A.comp Q) = ∑ p : ι × κ, ⟪ContinuousLinearMap.adjoint P (b p.1), A (Q (c p.2))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (b p.1) := by
  ext x
  simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, Fintype.sum_prod_type, smul_smul]
  conv_lhs => rw [← c.sum_repr' x]
  simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [← b.sum_repr' (P (A (Q (c j))))]
  simp only [Finset.smul_sum, smul_smul, mul_comm]

theorem isCoef_of_translate_smul_exists : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → (∀ f : Mx k r → (Wq →L[ℂ] Wp), PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f → ∃ s, IsCoef R l l' f s) ∧ (∀ F s (t : ℂ), IsCoef R l l' F s → IsCoef R l l' (fun g => t • F g) (t * s)) ∧ ((∃ x ∈ R.TK, l x ≠ 0) → (∃ y ∈ R.TK, l' y ≠ 0) → ∀ s : ℂ, ∃ F, IsCoef R l l' F s) := by
  intro hK k r ε mu R Wp _ _ _ _ Wq _ _ _ _ l l' hR
  obtain ⟨hmul, hone, hinner, -, -, hTK, hKF, -, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  refine ⟨?_, ?_, ?_⟩
  · rintro f ⟨a, ha, b, hb, P, Q, hQ, hP, h⟩
    obtain ⟨hai, ha1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
    obtain ⟨hbi, -, hb2⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hb
    let e := stdOrthonormalBasis ℂ Wp
    let c := stdOrthonormalBasis ℂ Wq
    let φ := (finProdFinEquiv (m := Module.finrank ℂ Wp) (n := Module.finrank ℂ Wq)).symm
    refine ⟨_, _, fun i => R.σ a (ContinuousLinearMap.adjoint P (e (φ i).1)),
      fun i => R.σ b⁻¹ (Q (c (φ i).2)), fun i => (innerSL ℂ (c (φ i).2)).smulRight (e (φ i).1),
      fun i => ⟨hTK a ha _ (hKF _ (hP _)), hTK _ hbi _ (hKF _ (hQ _))⟩, fun g hg => ?_, rfl⟩
    have hc : a * (a⁻¹ * g * b⁻¹) * b = g := by
      calc a * (a⁻¹ * g * b⁻¹) * b = (a * a⁻¹) * g * (b⁻¹ * b) := by simp only [Matrix.mul_assoc]
        _ = g := by rw [ha1, hb2, Matrix.one_mul, Matrix.mul_one]
    have h1 : f g = P.comp ((R.σ (a⁻¹ * g * b⁻¹)).comp Q) := by
      have := h (a⁻¹ * g * b⁻¹)
      simpa only [hc] using this
    have hm : a⁻¹ * g * b⁻¹ ∈ GG k r :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg) hbi
    have h2 : ∀ u v, ⟪u, R.σ (a⁻¹ * g * b⁻¹) v⟫_ℂ = ⟪R.σ a u, R.σ g (R.σ b⁻¹ v)⟫_ℂ := by
      intro u v
      rw [← hinner a ha, ← hmul a ha _ hm, ← hmul g hg _ hbi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ha1,
        Matrix.one_mul]
    rw [h1, comp_eq_sum_inner_smul_rankOne e c]
    simp only [h2]
    exact (φ.sum_comp (fun p => ⟪R.σ a (ContinuousLinearMap.adjoint P (e p.1)), R.σ g (R.σ b⁻¹ (Q (c p.2)))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (e p.1))).symm
  · rintro F s t ⟨m, x, y, X, hxy, hF, hs⟩
    refine ⟨m, x, y, fun i => t • X i, hxy, fun g hg => ?_, ?_⟩
    · simp only [hF g hg, Finset.smul_sum, smul_smul, mul_comm]
    · simp only [hs, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_right]
  · rintro ⟨x, hx, hx0⟩ ⟨y, hy, hy0⟩ s
    have h1 : ⟪l x, l x⟫_ℂ ≠ 0 := fun h => hx0 (inner_self_eq_zero.mp h)
    have h2 : ⟪l' y, l' y⟫_ℂ ≠ 0 := fun h => hy0 (inner_self_eq_zero.mp h)
    refine ⟨fun g => ∑ _i : Fin 1, ⟪x, R.σ g y⟫_ℂ •
        ((s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x)),
      1, fun _ => x, fun _ => y,
      fun _ => (s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x),
      fun _ => ⟨hx, hy⟩, fun g _ => rfl, ?_⟩
    rw [Fin.sum_univ_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, inner_smul_right, div_mul_cancel₀ _ (mul_ne_zero h2 h1)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsUnitaryStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayley_endomorphisms_unitary : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  first | exact @GlobalTheory.CapUnitary.isUnitary_of_isE | exact GlobalTheory.CapUnitary.isUnitary_of_isE | (intros; apply GlobalTheory.CapUnitary.isUnitary_of_isE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterEqWeilPairing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem datum_character_eq_zpow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    {F : Type} [Field F] {M : ℕ} (hM : 0 < M) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M)
    (φ : Dw.La →+ Additive Fˣ) (hφ : ∀ a, φ (M • a) = 0) :
    ∃ d : Dw.La, ∀ a, Additive.toMul (φ a) = ζ ^ Dw.EF a d := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : Module.Projective ℤ Dw.La := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 Dw.proj
    haveI : Module.Free ℤ (Dw.La →₀ 𝓞 E) := inferInstance
    exact Module.Projective.of_split (s.restrictScalars ℤ)
      ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hs x)
  let f : ℤ →ₗ[ℤ] Additive Fˣ := LinearMap.toSpanSingleton ℤ (Additive Fˣ) (Additive.ofMul ζ)
  have hmem : ∀ a, φ.toIntLinearMap a ∈ LinearMap.range f := by
    intro a
    have h1 : Additive.toMul (φ a) ∈ rootsOfUnity M F := by
      rw [mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul, hφ]; rfl
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_mem_rootsOfUnity h1
    refine ⟨i, ?_⟩
    change (i : ℤ) • Additive.ofMul ζ = φ a
    rw [natCast_zsmul, ← ofMul_pow, hi]; rfl
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property f.rangeRestrict
    (φ.toIntLinearMap.codRestrict _ hmem) f.surjective_rangeRestrict
  obtain ⟨d, hd⟩ := Dw.unimod.2 ψ
  refine ⟨-d, fun a => ?_⟩
  have skew : Dw.EF a (-d) = ψ a := by
    have := Dw.alt (d + a)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at this
    rw [map_neg, ← hd]
    linarith
  have h2 : f (ψ a) = φ a := congrArg Subtype.val (LinearMap.congr_fun hψ a)
  rw [skew, ← h2]
  rfl

theorem character_eq_weil_pairing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] (A : PolAV (Sp (FractionRing R))), letI := H.starRing; ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a) (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N k : ℕ), 1 ≤ N → 1 ≤ k → Nat.Coprime N k → ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 → ∀ κ : (TFK (R := R) F ⟶ A.A) → Fˣ, (∀ z z', z ≫ oA.act β = 1 → z' ≫ oA.act β = 1 → κ (z * z') = κ z * κ z') → ∃ b : TFK (R := R) F ⟶ A.A, b ≫ oA.act (star β) = 1 ∧ ∀ z, z ≫ oA.act β = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z b (unitOn (κ z)) := by
  intro E _ _ _ H R _ _ F _ _ A
  let _ := H.starRing
  intro oA Dw I N k hN hk hco β u u' hβ huu κ hκ
  have hM : 0 < k * N := Nat.mul_pos hk hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev (k * N) (c • b) = I.ev (k * N) b ≫ oA.act c := fun c b => I.lin _ c b
  obtain ⟨t, k', htk⟩ := (Nat.isCoprime_iff_coprime.2 hco).map (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at htk
  obtain ⟨ε, w, v, hw, hv⟩ : ∃ ε w v : 𝓞 E, β * ε = ((k * N : ℕ) : 𝓞 E) * w ∧ 1 = ε + v * β := by
    refine ⟨k * k' * u' * star β, k' * u', star β * t + k * k' * u, ?_, ?_⟩
    · push_cast
      rw [← hβ]; ring
    · linear_combination (-(k * k' : 𝓞 E)) * huu - htk - t * hβ
  have hzero : ∀ (c : 𝓞 E) (a : Dw.La), I.ev (k * N) ((((k * N : ℕ) : 𝓞 E) * c) • a) = 1 := by
    intro c a
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact (I.ker _ hM _).2 ⟨_, rfl⟩
  have hkill : ∀ a, I.ev (k * N) (ε • a) ≫ oA.act β = 1 := by
    intro a
    rw [← hlin, smul_smul, hw, hzero]
  have hfix : ∀ a, I.ev (k * N) a ≫ oA.act β = 1 → I.ev (k * N) (ε • a) = I.ev (k * N) a := by
    intro a ha
    obtain ⟨f, hf⟩ := (I.ker _ hM (β • a)).1 (by rw [hlin]; exact ha)
    have h1 : a = ε • a + (k * N) • (v • f) := by
      rw [smul_comm (k * N) v f, ← hf, smul_smul, ← add_smul, ← hv, one_smul]
    conv_rhs => rw [h1, I.add, (I.ker _ hM _).2 ⟨_, rfl⟩, _root_.mul_one]
  let φ : Dw.La →+ Additive Fˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (κ (I.ev (k * N) (ε • a))))
    (fun a b => by rw [smul_add, I.add, hκ _ _ (hkill a) (hkill b), ofMul_mul])
  have hφ : ∀ a, φ ((k * N) • a) = 0 := by
    intro a
    rw [← map_zero φ]
    change Additive.ofMul (κ (I.ev (k * N) (ε • (k * N) • a))) = Additive.ofMul (κ (I.ev (k * N) (ε • 0)))
    rw [smul_comm ε (k * N) a, (I.ker _ hM _).2 ⟨_, rfl⟩, smul_zero,
      (I.ker _ hM 0).2 ⟨0, (smul_zero _).symm⟩]
  obtain ⟨d, hd⟩ := datum_character_eq_zpow Dw hM (I.ζ_prim _ hM) φ hφ
  refine ⟨I.ev (k * N) (H.bar ε • d), ?_, fun z hz => ?_⟩
  · rw [← hlin, smul_smul]
    change I.ev (k * N) ((H.bar β * H.bar ε) • d) = 1
    rw [← map_mul, hw, map_mul, map_natCast, hzero]
  · have hzN : z ^ N = 1 := pow_eq_one_of_kill oA.toRingAct (by rw [_root_.mul_comm]; exact hβ) z hz
    obtain ⟨a, rfl⟩ := (I.onto _ hM z).1 (by rw [pow_mul', hzN, one_pow])
    have h1 : κ (I.ev (k * N) a) = I.ζ (k * N) ^ Dw.EF a (H.bar ε • d) := by
      rw [← Dw.adj, ← hd]
      change _ = κ (I.ev (k * N) (ε • ε • a))
      rw [hfix _ (hkill a), hfix a hz]
    rw [h1]
    exact I.isom _ hM _ _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnitsStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedAction_expand_matrixUnits : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  first | exact @GlobalTheory.dC_expand_units | exact GlobalTheory.dC_expand_units | (intros; apply GlobalTheory.dC_expand_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasicStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_unitary_smooth_basic : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  first | exact @GlobalTheory.rep_basic_of_isDS | exact GlobalTheory.rep_basic_of_isDS | (intros; apply GlobalTheory.rep_basic_of_isDS <;> assumption)
end

