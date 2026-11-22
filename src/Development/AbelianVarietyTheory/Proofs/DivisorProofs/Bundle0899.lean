import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussIntegralNormFormNonNormCancel
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.Cancel

open ValuativeRel
open scoped Topology NNReal

theorem compact_subset_cball {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {K : Set F} (hK : IsCompact K) :
    ∃ s : Fˣ, K ⊆ GlobalTheory.SplitWeil.cball s := by
  refine hK.elim_directed_cover (fun s : Fˣ => GlobalTheory.SplitWeil.cball s) GlobalTheory.SplitWeil.isOpen_cball ?_ ?_
  · intro x _
    by_cases hx : x = 0
    · exact Set.mem_iUnion.mpr ⟨1, by simp [GlobalTheory.SplitWeil.cball, hx]⟩
    · exact Set.mem_iUnion.mpr ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩
  · intro a b
    rcases le_total (valuation F (a : F)) (valuation F (b : F)) with h | h
    · exact ⟨b, fun x hx => le_trans (show valuation F x ≤ _ from hx) h, fun x hx => hx⟩
    · exact ⟨a, fun x hx => hx, fun x hx => le_trans (show valuation F x ≤ _ from hx) h⟩

theorem punctured_neBot (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : (𝓝[≠] (0 : F)).NeBot := by
  by_contra h
  rw [Filter.not_neBot, ← isOpen_singleton_iff_punctured_nhds] at h
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset (h.mem_nhds rfl)
  exact s.ne_zero (hs (by simp [GlobalTheory.SplitWeil.cball]))

theorem mul_mem_cball_iff {F : Type} [Field F] [ValuativeRel F] (a s : Fˣ) (x : F) :
    valuation F ((a : F) * x) ≤ valuation F (s : F) ↔ valuation F x ≤ valuation F ((a⁻¹ * s : Fˣ) : F) := by
  rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    le_inv_mul_iff₀ (by simp [zero_lt_iff])]

theorem gauss_cancel : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (t : Fˣ), t ∉ (Units.map (Algebra.norm F : E →* F)).range → ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → (∫ z in {z : E | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ (Algebra.norm F z) ∂μ) + (nabs F t : ℂ) * ∫ z in {z : E | (t : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((t : F) * Algebra.norm F z) ∂μ = 0 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE ψ hψ hψ1 hψ0 _ _ μ _ t ht
  borelize F
  obtain ⟨hfd, hring, -, ht2, -, hN, -, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := GlobalTheory.SplitWeil.t2Space F
  haveI := punctured_neBot F
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  haveI : (𝓝[≠] (0 : E)).NeBot := Module.punctured_nhds_neBot F E 0
  haveI : LocallyCompactSpace E := by
    obtain ⟨L, -, h1, h2⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE 1
    exact h1.locallyCompactSpace_of_mem_nhds_of_addGroup (h2.mem_nhds L.zero_mem)
  have hμ0 : μ {0} = 0 := measure_singleton 0
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.SplitWeil.exists_isUnitVol F
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.T.exists_integral_closedBall_addChar_eq_zero F lam ψ hψ hψ1 hψ0
  have hm : ∀ a : F, Measurable fun z : E => a * Algebra.norm F z := fun a =>
    (continuous_const.mul hN).measurable
  let m : Fˣ → Measure F := fun a => μ.map fun z : E => (a : F) * Algebra.norm F z
  let n : Fˣ → Measure F := fun a => distribHaarChar F a • m a
  have hmc : ∀ a, IsFiniteMeasureOnCompacts (m a) := fun a => ⟨fun K hK => by
    obtain ⟨s, hs⟩ := compact_subset_cball hK
    obtain ⟨L, hL, h1, -⟩ := GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic F E c δ hE (a⁻¹ * s)
    rw [Measure.map_apply (hm a) hK.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (h1.measure_lt_top (μ := μ))
    intro z hz
    rw [hL]
    exact (mul_mem_cball_iff a s _).mp (hs hz)⟩
  have hnc : ∀ a, IsFiniteMeasureOnCompacts (n a) := fun a => by
    haveI := hmc a
    exact IsFiniteMeasureOnCompacts.smul_nnreal (m a) _
  have hn0 : ∀ a, n a {0} = 0 := fun a => by
    have : (fun z : E => (a : F) * Algebra.norm F z) ⁻¹' {0} = {0} := by
      ext z; simp [Algebra.norm_eq_zero_iff]
    simp only [n, m, Measure.smul_apply]
    rw [Measure.map_apply (hm a) (measurableSet_singleton 0), this, hμ0, smul_zero]
  have hn1 : ∀ (a : Fˣ) (b : Fˣ), b ∈ (Units.map (Algebra.norm F : E →* F)).range → n (b * a) = n a := by
    rintro a _ ⟨w, rfl⟩
    have h1 := GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul F E c δ hE μ w
    have h2 : m (Units.map (Algebra.norm F : E →* F) w * a) =
        (μ.map fun x => (w : E) * x).map fun z : E => (a : F) * Algebra.norm F z := by
      rw [Measure.map_map (hm a) (measurable_const_mul _)]
      simp only [m]
      congr 1
      funext z
      simp only [Units.val_mul, Units.coe_map, Function.comp, map_mul]
      ring
    simp only [n]
    rw [h2, h1, Measure.map_smul, smul_smul, map_mul, mul_right_comm,
      mul_inv_cancel₀ (distribHaarChar_pos).ne', one_mul]
  have hn2 : ∀ a u : Fˣ, (n a).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n (u * a) := by
    intro a u
    simp only [n, m]
    rw [Measure.map_smul, Measure.map_map (measurable_const_mul _) (hm a), smul_smul, map_mul,
      inv_mul_cancel_left₀ (distribHaarChar_pos).ne']
    congr 2
    funext z
    simp [mul_assoc]
  have hhom : ∀ u : Fˣ, (n 1 + n t).map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • (n 1 + n t) := by
    intro u
    rw [Measure.map_add _ _ (measurable_const_mul _), hn2, hn2, ← smul_add]
    congr 1
    by_cases hu : u ∈ (Units.map (Algebra.norm F : E →* F)).range
    · rw [hn1 _ _ hu, hn1 _ _ hu]
    · have h1 := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE u t hu ht
      have h2 := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE t t ht ht
      have h3 := hn1 1 _ h1
      have h4 := hn1 t _ (mul_mem h1 (inv_mem h2))
      rw [mul_one] at h3
      have h5 : u * t * (t * t)⁻¹ * t = u * 1 := by group
      rw [h5] at h4
      rw [h3, h4, add_comm]
  haveI := hnc 1
  haveI := hnc t
  haveI : IsFiniteMeasureOnCompacts (n 1 + n t) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  obtain ⟨r, hr⟩ := GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField F lam (n 1 + n t) (by rw [Measure.add_apply, hn0, hn0, add_zero]) hhom
  refine ⟨s₀, fun s hs => ?_⟩
  have hB := GlobalTheory.SplitWeil.isCompact_cball s
  have hint : ∀ a : Fˣ, ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂(n a) = (nabs F a : ℂ) *
      ∫ z in {z : E | (a : F) * Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s}, ψ ((a : F) * Algebra.norm F z) ∂μ := by
    intro a
    simp only [n, m]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure,
      setIntegral_map hB.measurableSet hψ.aestronglyMeasurable (hm a).aemeasurable]
    rfl
  have h1 : ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂(n 1 + n t) = 0 := by
    rw [hr, Measure.restrict_smul, integral_smul_nnreal_measure, hs₀ s hs, smul_zero]
  rw [Measure.restrict_add, integral_add_measure (hψ.continuousOn.integrableOn_compact hB)
    (hψ.continuousOn.integrableOn_compact hB), hint, hint] at h1
  simpa [GlobalTheory.SplitWeil.nabs_one] using h1

end GlobalTheory.KSp.Cancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharacterCoxeterTorusInvEqAtInverseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenCuspidalCharacterCoxeterTorus_inv_eq_at_inverse : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (θ : LevelCuspCharacters.Tor p (Fintype.card ι) →* Kˣ) (h h' : Matrix ι ι (ZMod p)), h * h' = 1 → LevelCuspCharacters.cuspChar θ⁻¹ h = LevelCuspCharacters.cuspChar θ h' := by
  first | exact @GlobalTheory.CuspInv.cuspChar_inv | exact GlobalTheory.CuspInv.cuspChar_inv | (intros; apply GlobalTheory.CuspInv.cuspChar_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomOfProportionalGeneratingCombinationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpHom_of_proportional_generating_combinations : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (T : Scheme.{0}) (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Ψ : A'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(T, ⊤)), Hyps L M k bA bB eA eB → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → Ψ ≫ GlobalTheory.HomFixUniv.fA B = A'.hom ≫ t → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom Ψ c → GlobalTheory.HomFixUniv.Normal t c αA βB → ∃ Φ : A' ⟶ B', IsMonHom Φ ∧ Φ.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B = Ψ := by
  first | (exact @GlobalTheory.HomFixUniv.hom_of_proport) | (exact GlobalTheory.HomFixUniv.hom_of_proport) | (intros; apply GlobalTheory.HomFixUniv.hom_of_proport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorObjectPullback_comp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → Nonempty (ObjMap o₁ o₃ (f ≫ g)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp | exact GlobalTheory.UPel.HT.objMap_comp | (intros; apply GlobalTheory.UPel.HT.objMap_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOnePara
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem continuous_heisV_snd {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (u : VA F N) (g : VA F N → ℂ) (hg : Continuous g)
    (x : Fin N → AF F) : Continuous fun y : Fin N → AF F => heisV ψ u g (x, y) := by
  unfold heisV symV
  have h1 : Continuous fun y : Fin N → AF F => (x, y).1 ⬝ᵥ u.2 - u.1 ⬝ᵥ (x, y).2 := by
    simp only [dotProduct]
    fun_prop
  refine (hψ.comp (continuous_const.mul h1)).mul (hg.comp ?_)
  fun_prop

theorem heisV_zero {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (g : VA F N → ℂ) : heisV ψ 0 g = g := by
  funext w
  simp [heisV, symV, AddChar.map_zero_eq_one]

open GlobalTheory.GaugeEx in
theorem hasDerivAt_invV_heisV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ (f f' : VA F N → ℂ) (C : ℝ), Continuous f → Continuous f' → (∀ w, ‖f w‖ ≤ C) → (∀ w, ‖f' w‖ ≤ C) → ∀ M : ℝ →+ VA F N, Continuous M → (∀ w s, HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (heisV ψ (M s) f' w) s) → ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0 := by
  intro F _ _ N _ ψ lam ν hC 𝓓 _ h1 f f' C hf hf' hfC hf'C M _ hM x
  have hψ := hC.2.1
  haveI : IsFiniteMeasure ((muV N ν).restrict 𝓓) := isFiniteMeasure_restrict.2 (by rw [h1]; simp)
  have hcont : ∀ (u : VA F N) (g : VA F N → ℂ), Continuous g →
      Continuous fun y : Fin N → AF F => heisV ψ u g (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
    intro u g hg
    refine (continuous_heisV_snd ψ hψ.1 u g hg x).mul (hψ.1.comp ?_)
    simp only [dotProduct]
    fun_prop
  have hnorm : ∀ (u : VA F N) (g : VA F N → ℂ), (∀ w, ‖g w‖ ≤ C) → ∀ y : Fin N → AF F,
      ‖heisV ψ u g (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))‖ ≤ C := by
    intro u g hg y
    simp only [heisV, norm_mul, hψ.2.1, one_mul, mul_one]
    exact hg _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (muV N ν).restrict 𝓓)
    (F := fun t y => heisV ψ (M t) f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))))
    (F' := fun t y => heisV ψ (M t) f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))))
    (x₀ := (0 : ℝ)) (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcont _ f hf).aestronglyMeasurable)
    (Integrable.of_bound (hcont _ f hf).aestronglyMeasurable C (Filter.Eventually.of_forall (hnorm _ f hfC)))
    (hcont _ f' hf').aestronglyMeasurable
    (ae_of_all _ fun y t _ => hnorm _ f' hf'C y)
    (integrable_const C)
    (ae_of_all _ fun y t _ => (hM (x, y) t).mul_const _)
  have e : (fun y => heisV ψ (M 0) f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))) =
      fun y => f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
    rw [map_zero, heisV_zero]
  have k2 := key.2
  simp only [e] at k2
  exact k2

end GlobalTheory.ThetaTransform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherDegreeClassDiesOnFinerEtaleNeighbourhood
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.KillFiner

theorem pull_spMap_comp (q : ℕ) {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (ρ : R →+* S) (ψ : S →+* T)
    (n i : ℤ) (z : Ht q (sp R) n i) :
    pull _ (spMap (ψ.comp ρ)) _ _ z = pull _ (spMap ψ) _ _ (pull _ (spMap ρ) _ _ z) := by
  have e : spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
    show sch.map (Spec.map (CommRingCat.ofHom (ψ.comp ρ))) = sch.map (Spec.map (CommRingCat.ofHom ψ)) ≫ sch.map (Spec.map (CommRingCat.ofHom ρ))
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]
  rw [e, pull_comp]

theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsNbhd B A' f → ∀ (m i : ℤ), 2 ≤ m → ∀ z : Ht q (sp (Localization.Away (algebraMap B A' f))) m i, ∃ (A'' : Type) (_ : CommRing A'') (_ : Algebra B A'') (_ : Algebra.Etale B A'') (φ : A' →ₐ[B] A''), IsNbhd B A'' f ∧ pull _ (spMap (awayHom φ f)) _ _ z = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf hfu A' _ _ _ hN
  set f' : A' := algebraMap B A' f with hf'
  intro m i hm z
  set R := Localization.Away f'
  have hBf : ¬ IsField B := fun hB => hfu (by
    letI := hB.toField; exact isUnit_iff_ne_zero.mpr hf)
  have hqR : IsUnit (q : R) := by
    have := ((hq.map (algebraMap k B)).map (algebraMap B A')).map (algebraMap A' R)
    simpa only [map_natCast] using this

  have hFR : Subsingleton (Ht q (sp (FractionRing R)) m i) := by
    obtain ⟨hArt, hRed⟩ := GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced B f A'
    refine GlobalTheory.T.cohomology_vanishes_artinian q _ m i (fun M => ?_)
    obtain ⟨alg, halg⟩ := GlobalTheory.T.etale_maximal_quotient_algebraic k B hBf f hf A' M
    have hqM : IsUnit (q : FractionRing R ⧸ M.asIdeal) := by
      have := (hqR.map (algebraMap R (FractionRing R))).map (Ideal.Quotient.mk M.asIdeal)
      rwa [map_natCast, map_natCast] at this
    haveI := M.isMaximal
    letI : Field (FractionRing R ⧸ M.asIdeal) := Ideal.Quotient.field _
    exact GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing R ⧸ M.asIdeal) hqM m i hm

  obtain ⟨g, hg, hz⟩ := GlobalTheory.T.class_vanishes_away_nonZeroDivisor q R hqR m i z (Subsingleton.elim _ _)

  have hf'reg : IsSMulRegular A' f' := by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A') (mem_nonZeroDivisors_of_ne_zero hf)
    intro x y hxy
    apply h
    simpa [Algebra.smul_def, hf'] using hxy
  have hpow : ∀ (N : ℕ) (y : A'), f' ^ N * y = 0 → y = 0 := by
    intro N y hy
    induction N generalizing y with
    | zero => simpa using hy
    | succ N ih =>
      apply ih
      apply hf'reg
      simp only [smul_eq_mul, mul_zero]
      rw [← hy]; ring

  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f') g
  simp only at hs
  have ha : a ∈ nonZeroDivisors A' := by
    suffices key : ∀ y : A', y * a = 0 → y = 0 from
      mem_nonZeroDivisors_iff.mpr ⟨fun y hy => key y (by rw [mul_comm]; exact hy), key⟩
    intro y hy
    have h1 : algebraMap A' R y * g = 0 := by
      have hsu : IsUnit (algebraMap A' R (s : A')) := IsLocalization.map_units R s
      apply hsu.mul_left_injective
      simp only [zero_mul]
      rw [mul_assoc, hs, ← map_mul, hy, map_zero]
    have h2 : algebraMap A' R y = 0 := (mem_nonZeroDivisors_iff.mp hg).2 _ h1
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f')] at h2
    obtain ⟨⟨c, N, rfl⟩, hc⟩ := h2
    exact hpow N y hc

  let J : Ideal A' :=
    { carrier := {x | ∃ N : ℕ, a ∣ x * f' ^ N}
      add_mem' := by
        rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨N₁ + N₂, ?_⟩
        have e : (x + y) * f' ^ (N₁ + N₂) = (x * f' ^ N₁) * f' ^ N₂ + (y * f' ^ N₂) * f' ^ N₁ := by ring
        rw [e]
        exact dvd_add (h₁.mul_right _) (h₂.mul_right _)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨N, h⟩
        refine ⟨N, ?_⟩
        rw [smul_eq_mul, mul_assoc]
        exact h.mul_left c }
  have hJ : J ⊔ Ideal.span {f'} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hfM : f' ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨t, htM, N, hN⟩ := GlobalTheory.T.exists_dvd_mul_pow_etale_nbhd_zeroLocus B A' f hf hN a ha M hM hfM
    exact htM (hle (Ideal.mem_sup_left ⟨N, hN⟩))
  have h1 : (1 : A') ∈ J ⊔ Ideal.span {f'} := by rw [hJ]; trivial
  obtain ⟨h, ⟨N, hhN⟩, y, hy, hhy⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy

  refine ⟨Localization.Away h, inferInstance, inferInstance, inferInstance,
    IsScalarTower.toAlgHom B A' (Localization.Away h), GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one B A' f h c hN (by rw [← hhy]; ring), ?_⟩
  set φ := IsScalarTower.toAlgHom B A' (Localization.Away h)
  set S := Localization.Away (algebraMap B (Localization.Away h) f)
  have hcomp : ∀ x : A', awayHom φ f (algebraMap A' R x) = algebraMap _ S (φ x) := fun x =>
    RingHom.congr_fun (awayHom_comp_algebraMap φ f) x
  have hfS : IsUnit (algebraMap _ S (φ f')) := by
    rw [hf', AlgHom.commutes]; exact IsLocalization.Away.algebraMap_isUnit _
  have hhS : IsUnit (algebraMap _ S (φ h)) :=
    (IsLocalization.Away.algebraMap_isUnit h).map (algebraMap _ S)
  have haS : IsUnit (algebraMap _ S (φ a)) := by
    apply isUnit_of_dvd_unit (y := algebraMap _ S (φ (h * f' ^ N)))
    · exact map_dvd _ (map_dvd _ hhN)
    · rw [map_mul, map_pow, map_mul, map_pow]; exact hhS.mul (hfS.pow N)
  have hgS : IsUnit (awayHom φ f g) := by
    have e : awayHom φ f g * awayHom φ f (algebraMap A' R s) = algebraMap _ S (φ a) := by
      rw [← map_mul, hs, hcomp]
    rw [← e] at haS
    exact isUnit_of_mul_isUnit_left haS
  have hfac : (IsLocalization.Away.lift g hgS).comp (algebraMap R (Localization.Away g)) = awayHom φ f :=
    IsLocalization.Away.lift_comp g hgS
  rw [← hfac, pull_spMap_comp, hz, map_zero]
end GlobalTheory.KillFiner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
section
namespace GlobalTheory.HookDiagram

theorem hookProd_eq_of_mem (μ : YoungDiagram) (n : ℕ) (a : ℕ → ℕ)
    (h : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i) :
    Formalism.LatticeIndexTer.hookProd μ = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hrow : ∀ r, r < n → μ.rowLen r = a r := by
    intro r hr
    apply le_antisymm
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, a r) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hlt
      exact lt_irrefl _ ((h r (a r)).mp hm).2
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, μ.rowLen r) ∈ μ := (h r _).mpr ⟨hr, hlt⟩
      exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)
  have hcol : ∀ r c, Finset.filter (fun r' => c < a r') (Finset.Ioo r n) =
      Finset.Ioo r (μ.colLen c) := by
    intro r c
    ext r'
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, YoungDiagram.mem_iff_lt_colLen.mp ((h r' c).mpr ⟨h2, h3⟩)⟩
    · rintro ⟨h1, h2⟩
      have hm := (h r' c).mp (YoungDiagram.mem_iff_lt_colLen.mpr h2)
      exact ⟨⟨h1, hm.1⟩, hm.2⟩
  have hrc : ∀ r c, r < n → c < a r → r < μ.colLen c := fun r c hr hc =>
    YoungDiagram.mem_iff_lt_colLen.mp ((h r c).mpr ⟨hr, hc⟩)
  unfold Formalism.LatticeIndexTer.hookProd GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd
  rw [Finset.prod_finset_product μ.cells (Finset.range n) (fun r => Finset.range (a r))]
  · apply Finset.prod_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    apply Finset.prod_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    dsimp only
    rw [hcol r c, Nat.card_Ioo, hrow r hr]
    have := hrc r c hr hc
    omega
  · rintro ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_range]
    exact h i j

theorem hookOf_eq (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hsort : ((List.range n).map a).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem
      (fun {x y} _ hy hxy => ha x y hxy.le (List.mem_range.mp hy))
  have hL : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a :=
    hsort.insertionSort_eq
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf
  apply hookProd_eq_of_mem
  intro i j
  rw [YoungDiagram.mem_ofRowLens]
  simp only [hL, List.length_map, List.length_range, List.getElem_map, List.getElem_range,
    exists_prop]

theorem hookOf_pos_log (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a ∧
      Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) = Formalism.BasicNotions.DV.logHook n (fun k => (a k : ℝ)) := by
  rw [hookOf_eq n a ha]
  have hm := GlobalTheory.LiftSizeCompare.hookProd_mul n a ha
  have hinner : ∀ r ∈ Finset.range n,
      0 < ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) := by
    intro r _
    apply Finset.prod_pos
    intro l hl
    rw [Finset.mem_Ioo] at hl
    omega
  have hPpos : 0 < ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) :=
    Finset.prod_pos hinner
  have hHpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
    rcases Nat.eq_zero_or_pos (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a) with h0 | h0
    · have hF : 0 < ∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial :=
        Finset.prod_pos fun r _ => Nat.factorial_pos _
      rw [h0, zero_mul] at hm
      omega
    · exact h0
  refine ⟨hHpos, ?_⟩
  have hmR : (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a : ℝ) =
      ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) /
        ((∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) : ℕ) : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hPpos.ne'), ← Nat.cast_mul, hm]
  have hFpos : (0 : ℝ) < ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun r _ => Nat.factorial_pos _
  rw [hmR, Real.log_div hFpos.ne' (by exact_mod_cast hPpos.ne')]
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      have hg : (a r : ℝ) + n - r = ((a r + n - 1 - r : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (show r ≤ a r + n - 1 by omega), Nat.cast_sub (show 1 ≤ a r + n by omega)]
        push_cast
        ring
      rw [hg, Real.Gamma_nat_eq_factorial]
    · intro r _
      exact_mod_cast (Nat.factorial_pos _).ne'
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.cast_prod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mem_Ioo] at hl
        have hal : a l ≤ a r := ha r l hl.1.le hl.2
        congr 1
        rw [Nat.cast_add, Nat.cast_sub hal, Nat.cast_sub hl.1.le]
        ring
      · intro l hl
        rw [Finset.mem_Ioo] at hl
        have hpos : 0 < a r - a l + (l - r) := by omega
        exact_mod_cast hpos.ne'
    · intro r hr
      exact_mod_cast (hinner r hr).ne'

end GlobalTheory.HookDiagram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenRowVectorOrbitCompactOpenGLStatement
section
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_rowVector_orbit_compactOpen_GL : ∀ {F : Type} [NormedField F] {n : ℕ} (B : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B : Set (GL (Fin n) F)) → ∀ r₀ : Fin n → F, r₀ ≠ 0 → IsClopen {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} := by
  first | exact @GlobalTheory.JSW.Orbit.isClopen_orbit | exact GlobalTheory.JSW.Orbit.isClopen_orbit | (intros; apply GlobalTheory.JSW.Orbit.isClopen_orbit <;> assumption)
end

