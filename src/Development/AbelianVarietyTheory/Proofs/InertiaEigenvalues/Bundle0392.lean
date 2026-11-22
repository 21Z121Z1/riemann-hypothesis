import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0010
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.Integers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0357
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LayersOfExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import ReciprocityTheory.Hypotheses.GalCohDefs
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeLocalizedOfTorsionBounded
section
noncomputable section

open GlobalTheory.Prism

namespace GlobalTheory.BSP

def fracMap {A : Type} [CommRing A] {N P : Type} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (S : Submonoid A) (L : P →ₗ[A] N) (s : ↥S) : P →ₗ[A] LocalizedModule S N where
  toFun y := LocalizedModule.mk (L y) s
  map_add' x y := by
    rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp [mul_smul]⟩
  map_smul' c x := by
    rw [map_smul, RingHom.id_apply, LocalizedModule.smul'_mk]

theorem isLocalizedModule_fracMap {A : Type} [CommRing A] (t : A) {N P : Type} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (L : P →ₗ[A] N) (n : ℕ) (hk : ∀ y, L y = 0 → t ^ n • y = 0)
    (hc : ∀ x, ∃ y, L y = t ^ n • x) (s : ↥(Submonoid.powers t)) :
    IsLocalizedModule (Submonoid.powers t) (fracMap (Submonoid.powers t) L s) where
  map_units := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers t) N)
  surj z := by
    induction z using LocalizedModule.induction_on with
    | _ m r =>
      obtain ⟨y, hy⟩ := hc m
      refine ⟨⟨(s : A) • y, r * ⟨t ^ n, n, rfl⟩⟩, ?_⟩
      change ((r : A) * t ^ n) • LocalizedModule.mk m r = LocalizedModule.mk (L ((s : A) • y)) s
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq, map_smul, hy]
      refine ⟨1, ?_⟩
      simp only [Submonoid.smul_def, smul_smul]
      congr 1
      ring
  exists_of_eq {x y} h := by
    change LocalizedModule.mk (L x) s = LocalizedModule.mk (L y) s at h
    rw [LocalizedModule.mk_eq] at h
    obtain ⟨c, h⟩ := h
    refine ⟨⟨t ^ n, n, rfl⟩ * (c * s), ?_⟩
    have h1 := hk (((c : A) * s) • (x - y)) (by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero, mul_smul, mul_smul]
      exact h)
    rw [smul_smul, smul_sub, sub_eq_zero] at h1
    exact h1

theorem semiBC_localized (A : Type) [CommRing A] (φ : A →+* A) (t : A) (N : Type) [AddCommGroup N] [Module A N]
    (P : Type) [AddCommGroup P] [Module A P] (u : N →ₛₗ[φ] P) (hu : SemiBC u) (L : P →ₗ[A] N) (n a : ℕ)
    (hk : ∀ y, L y = 0 → t ^ n • y = 0) (hc : ∀ x, ∃ y, L y = t ^ n • x)
    (Φ : N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N)
    (hΦ : ∀ x, IsFrac t (Φ x) (L (u x)) a) : SemiBC Φ := by
  intro Q _ _ v
  letI : Module A Q := Module.compHom Q (algebraMap A (Localization.Away t))
  haveI : IsScalarTower A (Localization.Away t) Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let s : ↥(Submonoid.powers t) := ⟨t ^ a, a, rfl⟩
  haveI := isLocalizedModule_fracMap t L n hk hc s
  have hb := IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
    (fracMap (Submonoid.powers t) L s)
  have hΦ' : ∀ x, Φ x = fracMap (Submonoid.powers t) L s (u x) := hΦ
  let v' : N →ₛₗ[φ] Q :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun c x => v.map_smulₛₗ c x }
  obtain ⟨w₀, hw₀, hun⟩ := hu Q v'
  refine ⟨hb.lift w₀, fun x => ?_, fun w hw => ?_⟩
  · rw [hΦ', hb.lift_eq]
    exact hw₀ x
  · refine hb.algHom_ext _ _ fun y => ?_
    rw [hb.lift_eq, ← hun ((w.restrictScalars A).comp (fracMap (Submonoid.powers t) L s))
      fun x => (congrArg w (hΦ' x).symm).trans (hw x)]
    rfl

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitBdRPlusMatrixOfCongrOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.UnitFil

theorem isUnit_of_congr_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) → (∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l 1) → IsUnit B := by
  intro l _ K bk d k β B h1 h2
  obtain ⟨-, hker, hunit, haD, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    exact this
  have hl0 : ((l : ℂ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hB : ∀ i j, Per.θD l (B i j) = (1 : Matrix (Fin d) (Fin d) ℂ_[l]) i j := by
    intro i j
    have ha := (hker _).2 (h2 i j)
    obtain ⟨c, hc⟩ := h1 i j
    have hb : bk.ev (β i j) = (l : Ainf l) ^ k * bk.ev ((1 : Matrix (Fin d) (Fin d) bk.S) i j) + bk.ev bk.E * bk.ev c := by
      have : β i j = (l : bk.S) ^ k * (1 : Matrix (Fin d) (Fin d) bk.S) i j + bk.E * c := by
        rw [← hc]; simp [Matrix.sub_apply, Matrix.smul_apply]
      rw [this, map_add, map_mul, map_mul, map_pow, map_natCast]
    rw [map_sub, haD, hb, map_add, map_mul, map_mul, hE, zero_mul, add_zero, map_mul] at ha
    simp only [map_pow, map_natCast] at ha
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, mul_one] at ha ⊢
      have ha' : ((l : ℂ_[l]) ^ k) * Per.θD l (B i i) = (l : ℂ_[l]) ^ k * 1 := by
        rw [mul_one]; push_cast at ha; linear_combination -ha
      exact mul_left_cancel₀ hl0 ha'
    · simp only [Matrix.one_apply_ne hij, map_zero, mul_zero] at ha ⊢
      push_cast at ha
      have ha' : ((l : ℂ_[l]) ^ k) * Per.θD l (B i j) = 0 := by linear_combination -ha
      exact (mul_eq_zero.1 ha').resolve_left hl0
  have hmap : B.map (Per.θD l) = 1 := Matrix.ext hB
  rw [Matrix.isUnit_iff_isUnit_det]
  apply hunit
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]
  exact one_ne_zero

end GlobalTheory.BKLim.UnitFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpSumKernelCoboundaryCharLeSixMul
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_kernel_le_six_mul :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∃ σ, ¬ (p : ℤ) ^ r ∣ a σ) → ∃ J : Subgroup (L ≃ₐ[F] L), (∀ σ, σ ∈ J ↔ (p : ℤ) ^ r ∣ a σ) ∧ jumpSum (wild F L) ⊤ J ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r x a hp hE hord hax hx hne
  have hadd : ∀ σ τ : L ≃ₐ[F] L, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := fun σ τ =>
    GlobalTheory.T.integer_coboundary_additive_mod_prime_pow F L p E r ⊤ x a hp hE hord (fun σ _ => hx σ) σ (Subgroup.mem_top _) τ (Subgroup.mem_top _)
  obtain ⟨J, hJn, σ₁, c, hJ, hc, hpc⟩ := GlobalTheory.T.character_mod_prime_pow_kernel_generator (L ≃ₐ[F] L) p r a hp hadd hne
  refine ⟨J, hJ, ?_⟩

  have hp0 : (p : L) ≠ 0 := by
    intro h0
    have h1 : ((p : 𝒪[L]) : L) = 0 := by simpa using h0
    have h2 : (p : 𝒪[L]) = 0 := Subtype.ext (by simpa using h1)
    unfold OrdIs at hord
    rw [h2, AddValuation.map_zero] at hord
    exact ENat.top_ne_coe E hord
  set M := IntermediateField.fixedField J with hM
  haveI : IsGalois F M := IsGalois.of_fixedField_normal_subgroup J
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_integer_fixedField_trace_eq_sq_mul_of_ax F L p r x a J σ₁ c hp0 hax hx (fun σ hσ => (hJ σ).1 hσ) hc
  obtain ⟨e, hordF, hEe, -⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hord
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hEe; omega
    · exact h

  have hdM : differentExponent F M < ramificationIndex F M * (3 * e) := by
    by_contra hle
    push_neg at hle
    obtain ⟨w, hw, hwt⟩ := GlobalTheory.T.exists_trace_mem_maximalIdeal_pow_of_differentExponent F M (3 * e) hle z
    exact GlobalTheory.T.sq_mul_not_mem_maximalIdeal_pow_three_mul F p e c hp he hordF hpc w hw (hwt.trans hz)
  have htow := differentExponent_tower F M L
  have hram := ramificationIndex_tower F M L
  have hjs : jumpSum (wild F L) ⊤ J + 2 * differentExponent M L ≤ 2 * differentExponent F L := GlobalTheory.T.ramificationJumpSum_add_two_mul_differentExponent_le F L J
  have key : jumpSum (wild F L) ⊤ J ≤ 2 * (ramificationIndex M L * differentExponent F M) := by omega
  have hML : ramificationIndex M L * differentExponent F M ≤ ramificationIndex M L * (ramificationIndex F M * (3 * e)) :=
    Nat.mul_le_mul_left _ hdM.le
  have : ramificationIndex M L * (ramificationIndex F M * (3 * e)) * 2 = 6 * E := by
    rw [hEe, hram]; ring
  nlinarith

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsGoodOfAttached
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.Jumps

theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem map_round_cast (S : Multiset ℂ) (h : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    (S.map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id S]
  refine Multiset.map_congr rfl fun z hz => ?_
  obtain ⟨n, rfl⟩ := h z hz
  simp

theorem exists_jumpsAre_goodJ : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → ∃ ι J, JumpsAre bkP i s ι J ∧ GoodJ D J := by
  classical
  rintro D bkP i s ⟨ι, π₁, π, -, hA, hR, -⟩
  let S : (D.host.E →+* ℂ) → Multiset ℂ := fun τc =>
    (D.naut.infG π τc).map fun z => -z - ((((1 - (D.R.t : ℝ)) / 2 : ℝ)) : ℂ)
  have hint : ∀ τc, ∀ w ∈ S τc, ∃ n : ℤ, w = (n : ℂ) := by
    intro τc w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hw
    obtain ⟨n, rfl⟩ := (((D.naut.ralg_def π).1 hR.ralg) τc).2 z hz
    obtain ⟨a, ha⟩ := odd_rank D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨-n - a + b, ?_⟩
    rw [ha, hb]
    push_cast
    ring
  have hinj : Function.Injective (fun n : ℤ => (n : ℂ)) := Int.cast_injective
  have hcast : ∀ τc, ((S τc).map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S τc :=
    fun τc => map_round_cast _ (hint τc)
  refine ⟨ι, fun τc => (S τc).map fun z => ⌊z.re⌋, ?_, ?_⟩
  · intro v hv τ τc hτ a
    rw [hA.jumps v hv τ τc hτ a]
    have := Multiset.count_map_eq_count' (fun n : ℤ => (n : ℂ)) ((S τc).map fun z => ⌊z.re⌋) hinj a
    rw [hcast] at this
    rw [← this]
  · intro τc
    refine ⟨?_, ?_, ?_⟩
    · simp only [S, Multiset.card_map, D.naut.infG_card]
    · apply Multiset.map_injective hinj
      rw [hcast]
      have : (((S τc).map fun z => ⌊z.re⌋).map (fun a => (D.R.t : ℤ) - 1 - a)).map (fun n : ℤ => (n : ℂ))
          = (((S τc).map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ))).map (fun w => (D.R.t : ℂ) - 1 - w) := by
        simp only [Multiset.map_map, Function.comp_def]
        push_cast
        rfl
      rw [this, hcast]
      simp only [S, hR.anti τc, Multiset.map_map, Function.comp_def]
      refine Multiset.map_congr rfl fun z _ => ?_
      push_cast
      ring
    · intro a ha
      have h1 : (a : ℂ) ∈ S τc := by
        rw [← hcast τc]
        exact Multiset.mem_map_of_mem _ ha
      obtain ⟨z, hz, hza⟩ := Multiset.mem_map.1 h1
      refine hR.window τc z hz a ?_
      rw [← hza]
      push_cast
      ring

end GlobalTheory.TripleGal.Jumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevLawsOfEvLaw
section
noncomputable section

namespace GlobalTheory.NL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

section Generic

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
    [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
    {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

def levOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) O⟦X⟧)

omit [CharZero L] [Algebra ℚ L] in

theorem lev_eq_levOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) (f : LetA O n) :
    W.lev i ζ f = levOne W i ζ (f i) := by
  have h := W.lev_letter i ζ (f - Pi.constAlgHom O (ZMod n) O⟦X⟧ (f i)) (sub_self (f i))
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem levOne_X (W : LocWach PD L O v n) (i : ZMod n) {ζ : L} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    levOne W i ζ X = C ζ * exp L - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ h
  have hE : E = exp L := Ser.ode_unique 1 (by rw [map_one, one_mul]; exact h1)
    (by rw [map_one, one_mul]; exact derivative_exp L) (by rw [h0, constantCoeff_exp])
  rw [← hE, ← h2, add_sub_cancel_left]
  rfl

theorem levLaws_of_evLaw [IsDomain O] (hl0 : (l : O) ≠ 0) (hlu : ¬ IsUnit (l : O)) (W : LocWach PD L O v n)
    (hp : PD.p = l) (c : W.Gam → ℤ_[l]) (hc : ∀ g, algebraMap ℤ_[l] O (c g) = (W.χΓ g : O))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : Ser.EvLaw l (O := O) v inferInstance) : LevLaws W := by
  have hc' : ∀ g, algebraMap O L (W.χΓ g : O) = algebraMap ℤ_[l] L (c g) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hpr : PD.p.Prime := hp ▸ (Fact.out : l.Prime)
  have hφX : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, hp]
  have hφ : W.φ₀ = GlobalTheory.Fon.phi0 l O :=
    GlobalTheory.Cyc.algHom_ext_of_constantCoeff_zero _ _ (by rw [hφX, GlobalTheory.Fon.cyclotomicFrobeniusPowerSeries_X]) (by rw [hφX]; simp)
  have hγ : ∀ g, W.γ₀ g = GlobalTheory.Fon.gam O (c g) := fun g =>
    GlobalTheory.Cyc.algHom_ext_of_constantCoeff_zero _ _
      (GlobalTheory.Cyc.eq_of_commute_pow l hl0 hlu W.φ₀ _ _ hφX (W.γ₀_comm g _) (by rw [hφ]; exact GlobalTheory.Fon.cyclotomicFrobenius_comm_gammaAction _ _ _)
        (W.γ₀_X g).1 (GlobalTheory.Fon.constantCoeff_gam_X _ _)
        (by rw [(W.γ₀_X g).2, GlobalTheory.Fon.coeff_one_gam_X, hc])) (W.γ₀_X g).1
  constructor
  · rintro g i ζ _ j a h hj rfl f
    rw [hc'] at hj ⊢
    rw [lev_eq_levOne, lev_eq_levOne]
    change levOne W i ζ (W.γ₀ g (f i)) = _
    rw [hγ]
    exact Ser.ev_gam H (hp ▸ h.pow_eq_one) _ (hv _ j a hj) (levOne_X W i ⟨j, h⟩)
      (levOne_X W i (root_pow hpr ⟨j, h⟩ a)) (f i)
  · rintro i ζ ⟨j, h⟩ f
    rw [lev_eq_levOne, lev_eq_levOne]
    change levOne W i ζ (W.φ₀ (f (i - 1))) = _
    have := Ser.ev_gam H (hp ▸ h.pow_eq_one) (l : ℤ_[l]) (a := l) (by simp) (levOne_X W i ⟨j, h⟩)
      (levOne_X W (i - 1) (root_pow hpr ⟨j, h⟩ l)) (f (i - 1))
    rw [GlobalTheory.Fon.gam_l, map_natCast] at this
    rw [hφ, hp]
    exact this

end Generic

section Concrete

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem levLaws : LevLaws (H.W K s LL h) := by
  obtain ⟨_, -, h0, hu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨c, hc⟩ := Ser.exists_padic_char (GamL H h)
  refine levLaws_of_evLaw h0 hu _ (P.PD_p K) (fun g => (c g : ℤ_[l])) hc (Ser.dvd_of_le_v P) ?_
  convert Ser.evLaw_integers P LL using 1
  exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

theorem ioLaws_tie : IoLaws (F.E K s LL h).tie :=
  ⟨GlobalTheory.HWL.Back.ioE_φ (O := ↥(OL LL)) Subtype.val_injective _,
    GlobalTheory.HWL.Back.ioE_γ (O := ↥(OL LL)) Subtype.val_injective _⟩

theorem one_crys : IsCrys (P.PD K) (H.W K s LL h).one.ρ :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  GlobalTheory.TrivCrys.isCrys_lat_of_trivial _ (H.W K s LL h).one_triv

theorem laws_of_cmp (C : LocCmpT l P AI H F) : Laws H F h :=
  ⟨⟨(C.C K s LL h).tie.lev_Γ, (C.C K s LL h).tie.lev_φ⟩, ioLaws_tie H F h, one_crys H h⟩

end Concrete

theorem laws : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL), Laws H F h :=
  fun H F _ _ _ h => ⟨levLaws H h, ioLaws_tie H F h, one_crys H h⟩

end GlobalTheory.NL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDegPosAndSumLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.LocDegPos

theorem locDeg_pos_and_sum_le : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → (∀ v : HeightOneSpectrum (𝓞 E), 0 < Formalism.MainNotions.N.locDeg E v) ∧ ∀ s : Finset (HeightOneSpectrum (𝓞 E)), (∀ v ∈ s, v ∈ placesOver E l) → ∑ v ∈ s, Formalism.MainNotions.N.locDeg E v ≤ Module.finrank ℚ E := by
  intro E _ _ l hl
  refine ⟨fun v => ?_, fun s hs => ?_⟩
  · haveI := v.isPrime
    exact Nat.mul_pos (Ideal.ramificationIdx_pos v.asIdeal ℤ) (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  · classical
    haveI : Fact l.Prime := ⟨hl⟩
    have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} := by
      have hf : ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).Finite :=
        IsDedekindDomain.primesOver_finite _ _
      refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)
        (hf.subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ?_⟩
      rw [Ideal.liesOver_span_iff v.isPrime.ne_top (Nat.prime_iff_prime_int.1 hl)]
      simpa using hv
    letI : Fintype {v : HeightOneSpectrum (𝓞 E) // ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} := hfin.fintype
    have hsum := GlobalTheory.Proof.LocalDegreeSum.sum_locDeg E l
    rw [← hsum, ← Finset.sum_subtype_of_mem (fun v => Formalism.MainNotions.N.locDeg E v) (p := fun v : HeightOneSpectrum (𝓞 E) => ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (fun v hv => hs v hv)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end GlobalTheory.Proof.LocDegPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localInertia_iff_mem_placeInertia : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p)),
      (∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x)) →
      ∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  first | exact @GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | exact GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | (intros; apply GlobalTheory.DecInertia.inertiaK_iff_mem_Ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInvariantsKilledStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariants_killed_alt : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  first | exact @GlobalTheory.NewPrime.LocInv.local_invariants_killed | exact GlobalTheory.NewPrime.LocInv.local_invariants_killed | (intros; apply GlobalTheory.NewPrime.LocInv.local_invariants_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (x : Om l), ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = (x : ℂ_[l]) → C.o x = aDp l (wA l a w) := by
  first | exact @GlobalTheory.SeedSec.o_eq_aDp_wA | exact GlobalTheory.SeedSec.o_eq_aDp_wA | (intros; apply GlobalTheory.SeedSec.o_eq_aDp_wA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixPhiEquationToFamilyEquationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_phi_equation_to_family_equation : ∀ (R C : Type) [CommRing R] [CommRing C] (i : R →+* C) (φ : C → C) (e e' : R), Associated e e' → ∀ (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') R) (Q Q' : Matrix (Fin d) (Fin d) R), Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R) → ∀ Δ : Matrix (Fin d') (Fin d) C, i e' ^ a • (P.map i * Δ.map φ) = i e ^ a' • (Δ * Q.map i) → ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → R), ∀ j : Fin d' × Fin d, i e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * i (c k j) := by
  first | exact @GlobalTheory.BSP.matrix_phi_eq_family | exact GlobalTheory.BSP.matrix_phi_eq_family | (intros; apply GlobalTheory.BSP.matrix_phi_eq_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_breuilKisinIdeal_pow_of_norm_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), (∀ x : A, (l : A) * x = 0 → x = 0) → (∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x) → ∀ (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s := by
  first | exact @GlobalTheory.BSP.mem_J_pow_of_norm_le | exact GlobalTheory.BSP.mem_J_pow_of_norm_le | (intros; apply GlobalTheory.BSP.mem_J_pow_of_norm_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatioStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxUnramified_of_crystallineRatio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a b : P.R.B) (x : Om l), b ≠ 0 → P.ιB a = algebraMap (Om l) P.R.BdR x * P.ιB b → x ∈ MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.FracAlg.mem_Kur_of_ratio | exact GlobalTheory.FracAlg.mem_Kur_of_ratio | (intros; apply GlobalTheory.FracAlg.mem_Kur_of_ratio <;> assumption)
end

