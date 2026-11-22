import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixesCrystallineImageDescentDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizXi

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι]

omit [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

theorem desc_succ_eq_zero {P : PhiMod O K l e a ι} (D : Conn P) {v : Vec K a ι} (hv : D.N v = 0) (i : ℕ) :
    D.desc (i + 1) v = 0 := by
  induction i with
  | zero => simp [Conn.desc_succ, Conn.desc_zero, hv]
  | succ i ih => rw [Conn.desc_succ, hv, zero_sub, map_neg, map_nsmul, ih, smul_zero, neg_zero]

theorem muDiv_zero (g : ↥(GK (ϖ.field a))) : ϖ.muDiv a O g 0 = 1 := by
  simp only [PiSys.muDiv, dpow_zero]
  rfl

theorem taylor_fix (g : ↥(GK (ϖ.field a))) {P : PhiMod O K l e a ι} (D : Conn P) (Γ : Matrix ι ι (OA l O))
    (m : P.MM) (hm : D.N m.1 = 0)
    (h : ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ z : ι → OCr l O,
      (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) -
        ∑ i ∈ Finset.range n, ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ =
          (l : OCr l O) ^ r • z) :
    (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) = toCris t ϖ P m := by
  have hsum : ∀ n, ∑ i ∈ Finset.range (n + 1),
      ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ = toCris t ϖ P m := by
    intro n
    rw [Finset.sum_range_succ']
    have h0 : ∀ i ∈ Finset.range n, ϖ.muDiv a O g (i + 1) •
        toCris t ϖ P ⟨D.desc (i + 1) m, D.desc_mem (i + 1) m.2⟩ = 0 := by
      intro i _
      have : (⟨D.desc (i + 1) m, D.desc_mem (i + 1) m.2⟩ : P.MM) = 0 :=
        Subtype.ext (desc_succ_eq_zero D hm i)
      rw [this, map_zero, smul_zero]
    rw [Finset.sum_eq_zero h0, zero_add, muDiv_zero, one_smul]
    exact congrArg _ (Subtype.ext (D.desc_zero m))
  funext i
  rw [← sub_eq_zero]
  refine sep_OCr _ fun r => ?_
  obtain ⟨n₀, hn₀⟩ := h r
  obtain ⟨z, hz⟩ := hn₀ (n₀ + 1) (Nat.le_succ _)
  rw [hsum] at hz
  exact ⟨z i, by rw [← Pi.sub_apply, hz, Pi.smul_apply, smul_eq_mul]⟩

theorem toBcris_eq_toOB {P : PhiMod O K l e a ι} (m : P.MMl) (hm : m.1 ∈ P.MM) (i : ι) :
    toBcris t ϖ P m i = toOB l O (toCris t ϖ P ⟨m.1, hm⟩ i) := by
  rw [toBcris_apply, toCris_apply, ← ϖ.iB_of_mem t K]
  rfl

theorem exists_pow_smul_mem_MM {P : PhiMod O K l e a ι} (m : P.MMl) :
    ∃ N : ℕ, (((l ^ N : ℕ) • m : P.MMl) : Vec K a ι) ∈ P.MM := by
  have hc : ∀ τ i, ∃ n : ℕ, ((l : S O K e) : K⟦X⟧) ^ n * (P.mxInv τ *ᵥ m.1 τ) i ∈ S O K e :=
    fun τ i => mem_away.1 (P.mem_extc_iff.1 (mem_tot.1 m.2 τ) i)
  choose n hn using hc
  refine ⟨∑ τ, ∑ i, n τ i, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_⟩
  have hle : n τ i ≤ ∑ τ, ∑ i, n τ i :=
    (Finset.single_le_sum (f := fun i => n τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, n τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  have h1 : ((((l ^ (∑ τ, ∑ i, n τ i) : ℕ) • m : P.MMl) : Vec K a ι)) τ =
      ((l : S O K e) : K⟦X⟧) ^ (∑ τ, ∑ i, n τ i) • m.1 τ := by
    rw [Submodule.coe_smul_of_tower, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul K⟦X⟧]
    simp
  rw [h1, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact (S O K e).mul_mem ((S O K e).pow_mem (SetLike.coe_mem _) _) (hn τ i)

theorem actB_smul {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : OB l O) (z : TW (OB l O) T) : actB s T g (r • z) = galOB O (s g) r • actB s T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x =>
    simp only [actB, TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable [TameDescentExponentData K l e a]

theorem actB_jB {P : PhiMod O K l e a ι} {T : LocLat (Gl l) ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (hjB : IsCrisCmp I jB) (g : Gl l)
    (Γ : Matrix ι ι (OA l O)) (hΓ : I.IsLMat (sQ l g) g Γ) (y : ι → OB l O) :
    actB (sQ l) T g (jB y) = jB (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (y i)) := by
  obtain ⟨-, hI⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι P T I
  obtain ⟨-, huniq, -, -, hgal⟩ := hI jB hjB
  have hstab := (I.exists_isLMat_iff (sQ l g) g).1 ⟨Γ, hΓ⟩
  have hval : ∀ c : ι → OA l O, IsCrisVal t ϖ P jB (inclL t ϖ P c) (jB fun i => toB l O (c i)) :=
    fun c => ⟨1, c, by simp, by simp, by simp⟩
  have hbas : ∀ j, actB (sQ l) T g (jB (Pi.single j 1)) = jB (Γ.map (toB l O) *ᵥ Pi.single j 1) := by
    intro j
    have e1 : (Pi.single j 1 : ι → OB l O) = fun i => toB l O ((Pi.single j 1 : ι → OA l O) i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    have e2 : (Γ.map (toB l O) *ᵥ Pi.single j 1) = fun i => toB l O
        ((Γ *ᵥ fun k => galOA O (sQ l g) ((Pi.single j 1 : ι → OA l O) k)) i) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite (galOA O (sQ l g)), apply_ite (toB l O)]
    have h1 := hgal g hstab _ _ (hval (Pi.single j 1))
    rw [hΓ] at h1
    rw [e2, e1]
    exact huniq _ _ _ h1 (hval _)
  conv_lhs => rw [pi_eq_sum_univ' y]
  rw [map_sum, map_sum]
  conv_rhs => rw [pi_eq_sum_univ' (fun i => galOB O (sQ l g) (y i))]
  rw [← Matrix.mulVecLin_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearEquiv.map_smul, actB_smul, hbas, map_smul, Matrix.mulVecLin_apply, LinearEquiv.map_smul]

theorem horiz_of_fix {P : PhiMod O K l e a ι} {T : LocLat (Gl l) ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (hjB : IsCrisCmp I jB) (g : Gl l)
    (Γ : Matrix ι ι (OA l O)) (hΓ : I.IsLMat (sQ l g) g Γ) (ξ : P.MMl) (N : ℕ)
    (hN : (((l ^ N : ℕ) • ξ : P.MMl) : Vec K a ι) ∈ P.MM)
    (hfix : (Γ.map (toOCr l O) *ᵥ fun i => galOCr O (sQ l g) (toCris t ϖ P ⟨_, hN⟩ i)) =
      toCris t ϖ P ⟨_, hN⟩) :
    actB (sQ l) T g (jB (toBcris t ϖ P ξ)) = jB (toBcris t ϖ P ξ) := by
  have hB : (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (toBcris t ϖ P ((l ^ N : ℕ) • ξ) i)) =
      toBcris t ϖ P ((l ^ N : ℕ) • ξ) := by
    funext i
    rw [toBcris_eq_toOB t ϖ _ hN i, ← hfix]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, toBcris_eq_toOB t ϖ _ hN, galOB_toOB,
      Matrix.map_apply, toB, AlgHom.comp_apply]
  rw [map_nsmul] at hB
  have hu : IsUnit ((l ^ N : ℕ) : OB l O) := by
    rw [Nat.cast_pow]; exact isUnit_l_OB.pow N
  have hg : (fun i => galOB O (sQ l g) (((l ^ N : ℕ) • toBcris t ϖ P ξ) i)) =
      (l ^ N : ℕ) • fun i => galOB O (sQ l g) (toBcris t ϖ P ξ i) := by
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  rw [hg, Matrix.mulVec_smul] at hB
  have hfx : (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (toBcris t ϖ P ξ i)) = toBcris t ϖ P ξ := by
    funext i
    have h3 := congrFun hB i
    simp only [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (OB l O), smul_eq_mul] at h3
    exact hu.mul_left_cancel h3
  rw [actB_jB t ϖ I jB hjB g Γ hΓ _, hfx]

end General

end GlobalTheory.HorizXi

namespace GlobalTheory.HorizXi

theorem galois_fixes_xi : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T), IsCrisCmp I jB → ∀ C : Conn P, C.nabla = P.nabla → Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C → IsHoriz (thetaW a LL) ϖ (sQ l) P jB := by
  intro l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB hjB C hC hTay g hg d hξ
  have h1 := hTay ⟨sQ l g, hg⟩
  obtain ⟨Γ, h2⟩ := h1
  have h3 := exists_pow_smul_mem_MM (⟨P.xi d, hξ⟩ : P.MMl)
  obtain ⟨N, hN⟩ := h3
  have hNm : C.N (((l ^ N : ℕ) • (⟨P.xi d, hξ⟩ : P.MMl) : P.MMl) : Vec _ a ι) = 0 := by
    rw [Submodule.coe_smul_of_tower, map_nsmul, Conn.N_apply, hC, PhiMod.nabla_xi, smul_zero, smul_zero]
  exact horiz_of_fix (thetaW a LL) ϖ I jB hjB g Γ h2.1 _ N hN
    (taylor_fix (thetaW a LL) ϖ ⟨sQ l g, hg⟩ C Γ ⟨_, hN⟩ hNm (h2.2 ⟨_, hN⟩))

end GlobalTheory.HorizXi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLnStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ), (∀ χ : Gn g n → ℂ, IsIrr χ → ∃! f, HasLabel L χ f) ∧ (∀ (χ : Gn g n → ℂ) f, HasLabel L χ f → f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1)) ∧ ((Q.map Prod.fst : List _) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f ∧ degL (Q.map Prod.snd) = n ∧ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} = {hcL (Q.map Prod.snd) n} := by
  first | exact @GlobalTheory.GLq.Label.label_main | exact GlobalTheory.GLq.Label.label_main | (intros; apply GlobalTheory.GLq.Label.label_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpsReadingRowAdmStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJumpsReading_rowAdm : ∀ D : D7, AdmissibleParameterJ.AdmRead D := by
  first | exact @GlobalTheory.AdmReadBridge.main | exact GlobalTheory.AdmReadBridge.main | (intros; apply GlobalTheory.AdmReadBridge.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCongruenceFiltrationFiniteTowerBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_congruenceFiltration_finite_tower_bound : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E T : ℕ) (G : ℕ → Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Antitone G → G 0 ≤ lowerRamificationGroup K L 0 → ¬ G 0 ≤ G 1 → (∀ σ ∈ G 0, σ ^ p ∈ G 1) → (∀ j, j + 1 ≤ 2 * T + 8 → ∀ σ ∈ G 0, σ ^ p ∈ G (j + 1) → σ ∈ G j) → (∀ k ≤ 2 * T, Detects p 8 (G k) (G (k + 8))) → 2 ^ T * Nat.card ↥(G 0) < E := by
  first | exact @GlobalTheory.PMon.Ram.finiteTowerBound | exact GlobalTheory.PMon.Ram.finiteTowerBound | (intros; apply GlobalTheory.PMon.Ram.finiteTowerBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerRightRegularRepSubEqIntervalIntegralDerivat
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Unitary

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

theorem coeFn_right_translate {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    R Γ μ g h.toL2 =ᵐ[quotMeasure Γ μ] fun q => φ (sec Γ q * g) := by
  rw [right_translate_toL2]
  refine (h.mul_right g).coeFn_toL2.trans (Filter.Eventually.of_forall fun q => ?_)
  have := (h.1.mul_right g).descend_mk (sec Γ q)
  rwa [mk_sec] at this

theorem inner_right_translate_integral {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) (H : L2 Γ μ) :
    inner ℂ H (R Γ μ g h.toL2) = ∫ q, starRingEnd ℂ (H q) * φ (sec Γ q * g) ∂quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_right_translate h g] with q e
  simp [e, mul_comm]

theorem inner_R_sub_eq_intervalIntegral :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) → inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc h0 f f' hf hf' hcf hd H t hint
  have ftc : ∀ x, ∫ s in (0 : ℝ)..t, f' (x * c s) = f (x * c t) - f (x * 1) := fun x => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd x s)
      ((hcf.comp (continuous_const.mul hc)).intervalIntegrable _ _), h0]
  simp only [inner_right_translate_integral hf']
  rw [MeasureTheory.intervalIntegral_integral_swap hint, ← inner_sub_right, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have e1 := coeFn_right_translate hf 1
  rw [map_one, ContinuousLinearMap.one_apply] at e1
  filter_upwards [coeFn_right_translate hf (c t), e1, Lp.coeFn_sub (R Γ μ (c t) hf.toL2) hf.toL2] with q a b e
  rw [intervalIntegral.integral_const_mul, ftc, e, Pi.sub_apply, a, b]
  simp [mul_comm]

end GlobalTheory.AutomorphicL2Unitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableConjMulTranslatePath
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory

theorem integrable_conj_mul_translate_path {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] (c : ℝ → G) (hc : Continuous c) {f' : G → ℂ} (hf' : MemL2Quotient Γ μ f')
    (_hcont : Continuous f') (H : L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc]; exact measure_Ioc_lt_top⟩
  have hm : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => rmul Γ (c s) q) :=
    measurable_rmul_uncurry.comp (measurable_snd.prodMk (hc.measurable.comp measurable_fst))
  have hp := (MeasurePreserving.id (volume.restrict (Set.uIoc (0 : ℝ) t))).skew_product
    (μc := quotMeasure Γ μ) (μd := quotMeasure Γ μ) hm
    (Filter.Eventually.of_forall fun s => (measurePreserving_rmul (c s)).map_eq)
  have h1 := ((Lp.memLp H).star).comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))
  have h2 := (hf'.2.comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))).comp_measurePreserving hp
  refine (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
  have e : descend Γ f' (rmul Γ (c p.1) p.2) = f' (sec Γ p.2 * c p.1) := by
    rw [← hf'.1.descend_mk, ← rmul_mk, mk_sec]
  change star (H p.2) * descend Γ f' (rmul Γ (c p.1) p.2) = _
  rw [e]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvMemDeRhamFilNegOfExactDegreeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_mem_deRhamFil_neg_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a : ℤ) (u v : P.R.BdR), u * v = 1 → u ∈ (P.PD K).Fil a → u ∉ (P.PD K).Fil (a + 1) → v ∈ (P.PD K).Fil (-a) := by
  first | exact @GlobalTheory.FilInv.inv_mem_Fil_neg | exact GlobalTheory.FilInv.inv_mem_Fil_neg | (intros; apply GlobalTheory.FilInv.inv_mem_Fil_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNegStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_inv_and_hodgeTate_jumps_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  first | exact @GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg | exact GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg | (intros; apply GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfBreuilKisinFrameIsDeRhamStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_breuilKisinFrame_isDeRham : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsDR → Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) := by
  first | exact @GlobalTheory.BKLim.isDR_of_frame_isDR | exact GlobalTheory.BKLim.isDR_of_frame_isDR | (intros; apply GlobalTheory.BKLim.isDR_of_frame_isDR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPrismCoverBreuilKisinCoproductInlStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrismCover_breuilKisinCoproduct_inl : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A), IsFrame bk B t p → ∀ En : Env bk B t p, Cover En.inl := by
  first | exact @GlobalTheory.BSP.env_inl_cover | exact GlobalTheory.BSP.env_inl_cover | (intros; apply GlobalTheory.BSP.env_inl_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointCondH0WallOfCanon
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem jointCond_H0Wall_of_canon : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ∀ F : FonOf D.loc D.locA HW, AdmissibleParameterJ.JumpConditions L → SumRepresentations.Conclusion41 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∃ M0 h0 : ℕ, GlobalTheory.HubX.JointCond_H0Wall D HW F X M0 h0 := by
  intro _ D L HW R X hX F hJ h41 hFont
  obtain ⟨⟨ep, hJa⟩, hJb, hJc, -, hJe, hJf, -⟩ := hJ
  refine ⟨hOf L, hOf L, ?_⟩
  intro i _ _ hsplit u hu π hπ
  have hnI : ¬ TwistedPlaces.InertK D (D.nd.l i) := by
    intro h2
    unfold TwistedPlaces.SplitK at hsplit
    unfold TwistedPlaces.InertK at h2
    rw [hsplit] at h2
    rcases h2 with h2 | h2 <;> cases h2
  rw [hX.dc i hnI] at hu
  unfold dcOf at hu
  split_ifs at hu with hS
  swap
  · simp [KillingConditions.allRows] at hu
  obtain ⟨_, h5, hq, hd, hg, _⟩ := hS.1
  have hu' : u ∈ placesOver D.host.E (D.nd.l i) := ((Exists.choose hS.2).cover u).1 (Or.inr hu)
  have hl2 : D.nd.l i ≠ 2 := by omega
  have hsm : D.nd.l i ∉ D.host.small := fun h => by
    have h' : primeClass D.host.toHostRaw (D.nd.l i) = PrimeClass.splitK := hsplit
    simp [primeClass, h] at h'
  have hKur := GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i hsm hq hd u hu'
  have hgood : Good (D.nbr i u hu').Kw 1 (D.nbr i u hu').LL :=
    (D.self_good i u hu').good_one (D.nbr i u hu').LL_split hl2 (GlobalTheory.HubLoc.le_Ks_one_of_Kur _ hKur)
  have hZ : π ∈ D.nd.Z i := Formalism.MainNotions.LargeLevelLemmas.zgoodSubsetZ i hπ
  have hfam := hX.fam
  have hdec := (GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hfam i π hZ).2.2.2
  have hgr := hfam.good i
  have hcont := hfam.cont i π
  have hWc : Continuous (WpO D.nd i (X.ρ i) π) := by
    have h1 : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
      refine ((D.nd.chi_cont i 1).comp continuous_inv).congr fun g => ?_
      simp only [Function.comp_apply]
      rw [MonoidHom.inv_apply, ← map_inv]
    exact h1.smul hcont
  have hLc := GlobalTheory.WordJumpsCompare.continuous_loc D i u hu' _ hWc
  have hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu') ((WpO D.nd i (X.ρ i) π).comp (decS D.nd u))) g v :=
    fun v => hLc.matrix_mulVec continuous_const
  have hJW := fun τ => GlobalTheory.T.decomposition_local_above D L ep hJa hJb hJc hJe hJf i (X.r i) (X.ρ i) π hgr hZ hdec u hu'
    (TruncatedSeriesCountingIdentities.CoefExt.self i u hu') τ (WpO D.nd i (X.ρ i) π) (Or.inl rfl)
  have hrn : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  have hnV : 1 ≤ D.R.nV := le_trans D.R.t_odd.pos (Nat.le_add_left _ _)
  have hH := GlobalTheory.T.torsionExponent_le_of_jumps_at_embeddings_unramified D.loc HW D.locA (D.nd.l i) (D.nbr i u hu').Kw (D.nbr i u hu').LL hgood (hOf L) D.R.nV
    (4 * D.R.n) (wLat D i (X.ρ i) π u hu' hc) hKur (GlobalTheory.bridge_finrank_le D i u hu') hnV
    (fun τ => by
      obtain ⟨U, hU1, hU2, hU3⟩ := (hJW τ).1
      exact ⟨U, hU1.trans hrn, hU2, hU3⟩)
  refine ⟨hu', 1, hgood, hc, ?_, hH.1, fun τ => (hJW τ).2, ?_⟩
  · exact (GlobalTheory.T.decomposition_local_away D i (X.r i) (X.ρ i) π h41 (hFont i) hgr hcont hdec (hg 0) (hg 1) u hu'
      (TruncatedSeriesCountingIdentities.CoefExt.self i u hu')).2.2.1
  · rw [hX.c0]
    exact hH.2

end GlobalTheory.HubX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointCondH0allCanon
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem jointCondH0all_canon : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → AdmissibleParameterJ.JumpConditions L → SumRepresentations.Conclusion41 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, ∃ M0 h0 : ℕ, GlobalTheory.HubX.DecompositionInvariantsCondition D HW i (X.ρ i) π (X.dc i) (X.c0 i) M0 h0 := by
  intro hF D L HW R X hC hJ h41 hAdm i hTw hg hRA hS π hπ
  obtain ⟨⟨ep, hep⟩, hJb, hJc, hJd, hJe, hJf, hJg⟩ := hJ
  have hls : D.nd.l i ∉ D.host.small := fun h => hRA.1 (Or.inl h)
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hls
  have hlq : D.nd.l i ≠ D.host.q := fun h => hRA.2.1 (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hRA.2.1 (Or.inr h)
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hπZ : π ∈ D.nd.Z i := LargeLevelLemmas.zgoodSubsetZ i hπ
  obtain ⟨-, -, -, hdec⟩ := GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hC.fam i π hπZ
  have hgood := hC.fam.good i
  have hcont := hC.fam.cont i π
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have hrV : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  refine ⟨hOf L, hOf L, hl2, ?_⟩
  intro u _ w hw _
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i hls hlq hld w hw
  refine ⟨GlobalTheory.HubLoc.le_Ks_one_of_Kur _ hur, ?_⟩
  intro C hs hc L2
  have hcrys := (GlobalTheory.T.decomposition_local_away D i (X.r i) (X.ρ i) π h41 (hAdm i) hgood hcont hdec hg0 hg1 w hw C).2.2.2
  have hjump := fun τ => GlobalTheory.T.decomposition_local_above D L ep hep hJb hJc hJe hJf i (X.r i) (X.ρ i) π hgood hπZ hdec w hw C τ
    (T2O D.nd i (X.ρ i) π) (Or.inr rfl)
  have key := GlobalTheory.T.torsionExponent_le_of_jumps_at_embeddings_unramified D.loc HW D.locA (D.nd.l i) (D.nbr i w hw).Kw C.LL hs (hOf L) D.R.r (4 * D.R.n)
    (tTwoLocalLattice D i (X.ρ i) π C hc L2) hur (GlobalTheory.bridge_finrank_le D i w hw) hr1 (fun τ => (hjump τ).1)
  refine ⟨hcrys, key.1, fun τ => (hjump τ).2, ?_⟩
  rw [hC.c0]
  refine key.2.trans ?_
  unfold c0of
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrV)) _

end GlobalTheory.HubX
end

