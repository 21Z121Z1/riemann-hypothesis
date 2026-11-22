import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComponentEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0573
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import GroundTheory.GlobalFields.TateThesis.AdelicChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfExtensionLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ExtLatCrys

theorem isCrys_comp_extRep {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (K : FinExt l) (Pl : LocPrime l)
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL (Gl l) V)
    (hT : IsCrys (Pl.PD K) (ρ.comp (inclG K) : Representation LL ↥(GK K) V)) (z : ↥(continuousCocycles ρ))
    (hz : (z : Gl l → V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    IsCrys (Pl.PD K) ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep ρ z).comp (inclG K) : Representation LL ↥(GK K) (V × LL)) := by
  let ρ' : Representation LL ↥(GK K) V := ρ.comp (inclG K)
  have hρ' : ∀ g, ρ' g = ρ (inclG K g) := fun _ => rfl
  have hc : (fun g => (z : Gl l → V) (inclG K g)) ∈ continuousCocycles ρ' :=
    ⟨z.2.1.comp (continuous_subtype_val.subtype_mk _), fun g k => by
      have := z.2.2 (inclG K g) (inclG K k)
      rw [← map_mul] at this
      exact this⟩
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt ρ' ⟨_, hc⟩
  have h2 : ∀ (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Pl.R.B), actVB (Pl.PD K) ρ' g y =
      actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ (inclG K g) y := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, Pl.PD_actB, hρ']; rfl
    | add u w hu hw => rw [map_add, map_add, hu, hw]
  have h1 := (GlobalTheory.CrysExt.isCrystalline_iff_mem_H1f (Pl.PD K) (ρ := ρ') hT h0.1 ⟨_, hc⟩ h0.2).mpr
    ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.mk_mem_H1fSub (Pl.PD K) ρ' ⟨_, hc⟩).mpr (by
      obtain ⟨-, x, hx⟩ := hz
      refine ⟨hc, x, fun g => ?_⟩
      rw [h2]
      exact hx (inclG K g)))
  exact h1

theorem isCrys_comp_extRep_lat {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (K : FinExt l) (Pl : LocPrime l)
    (T : LocLat (Gl l) ℚ_[l] LL O)
    (hT : IsCrys (Pl.PD K) (T.ρ.comp (inclG K) : Representation LL ↥(GK K) T.V)) (z : ↥(continuousCocycles T.ρ))
    (hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ) :
    IsCrys (Pl.PD K) ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep T.ρ z).comp (inclG K) : Representation LL ↥(GK K) (T.V × LL)) :=
  isCrys_comp_extRep K Pl T.ρ hT z hz

theorem isCrys_resF_extLat : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL), IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ := by
  intro l _ a e _ _ ϖ LL _ _ Pl T hT z hz
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact isCrys_comp_extRep_lat (ϖ.field a) Pl T hT ⟨z, z.2.1⟩ hz

end GlobalTheory.ExtLatCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
section
noncomputable section

namespace GlobalTheory.TopSteps.CrysRules

open GlobalTheory.AdmLoc Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct Module
open GlobalTheory.TwistJump GlobalTheory.Cmp.JumpDict GlobalTheory.Cmp.SmallJumps

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem multV_of_only_zero {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (h : ∀ a, IsJumpV PD ρ τ a → a = 0) (a : ℤ) :
    multV PD ρ τ a = if a = 0 then (finrank LL (DdRE PD ρ τ) : ℤ) else 0 := by
  have hs : ∀ a : ℤ, a ≠ 0 → FildR PD ρ τ (a + 1) = FildR PD ρ τ a := fun a ha => by
    by_contra hne
    exact ha (h a hne)
  split_ifs with ha
  · subst ha
    have h0 : ∀ b ≤ (0 : ℤ), FildR PD ρ τ b = FildR PD ρ τ 0 := fun b hb => by
      induction b, hb using Int.le_induction_down with
      | base => rfl
      | pred n hn ih => rw [← hs (n - 1) (by omega), sub_add_cancel, ih]
    have h1 : ∀ b ≥ (1 : ℤ), FildR PD ρ τ b = FildR PD ρ τ 1 := fun b hb => by
      induction b, hb using Int.le_induction with
      | base => rfl
      | succ n hn ih => rw [hs n (by omega), ih]
    have e0 : FildR PD ρ τ 0 = DdRE PD ρ τ := by
      refine le_antisymm inf_le_left fun x hx => ?_
      obtain ⟨b, hb⟩ := filV_exh PD (LL := LL) x
      rw [← h0 (min b 0) (min_le_right _ _)]
      exact ⟨hx, filV_anti PD (min_le_left b 0) hb⟩
    have e1 : FildR PD ρ τ (0 + 1) = ⊥ := by
      rw [eq_bot_iff, zero_add]
      intro x hx
      refine filV_sep PD (LL := LL) x fun b => ?_
      rw [← h1 (max b 1) (le_max_right _ _)] at hx
      exact filV_anti PD (le_max_left b 1) hx.2
    rw [multV, e0, e1]
    simp
  · rw [multV, hs a ha, sub_self]

theorem ddRE_ne_bot [Algebra.IsSeparable Qp K] (hs : ∃ s ∈ PD.Fil (-1), PD.ι PD.t * s = 1)
    (ν : Representation LL G LL) (χ : G → LL) (hν : ∀ g x, ν g x = χ g • x)
    {m : ℕ} (k : Fin m → ℤ) (β : Fin m → BdR) (d : Fin m → LL ⊗[Qp] BdR)
    (hd : ∀ i, d i ∈ DdR PD ν ∧ d i ∈ FilV PD (LL := LL) (V := LL) (k i))
    (h1 : (1 : LL ⊗[Qp] BdR) =
      ∑ i, AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (LinearMap.mulLeft Qp (β i)) (d i))
    (τ : K →ₐ[Qp] LL) : DdRE PD ν τ ≠ ⊥ := by
  intro h0
  have hm := GlobalTheory.BlockJumps.multV_twist PD hs (1 : Representation LL G LL) 0 (fun g x => by simp) τ 0
  have hb : FildR PD (1 : Representation LL G LL) τ 0 = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hz : ∀ i, act LL (AlgHom.id LL LL) (d i) y = 0 := fun i => by
      have := act_maps PD (AlgHom.id LL LL) 1 ν τ (hd i).2 (fun g y hy => by
        have hi : actVdR PD ν g (d i) = d i := by
          have := (Submodule.mem_iInf _).1 (hd i).1 g
          simpa [sub_eq_zero] using this
        rw [actVdR_twist PD 1 ν g (χ g) (fun x => by simp [hν]), actVdR_act, hy, ← LinearMap.smul_apply,
          ← map_smul, ← actVdR_char PD ν g (χ g) (hν g), hi]) y hy
      have h2 := this.1
      rw [h0] at h2
      exact h2
    have : y = act LL (AlgHom.id LL LL) (1 : LL ⊗[Qp] BdR) y := by rw [map_one]; rfl
    rw [Submodule.mem_bot, this, h1, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mulLeft, map_mul, Module.End.mul_apply, hz, map_zero]
  rw [multV, hb] at hm
  simp at hm
  omega

end Generic

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (K LL : FinExt l)
include T

theorem exists_inverse_fontaineElement_mem_fil_neg_one : ∃ s ∈ (P.PD K).Fil (-1), (P.PD K).ι (P.PD K).t * s = 1 := by
  obtain ⟨s, hs, h⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  refine ⟨s, ?_, by rw [P.PD_ι, P.period_datum_t_eq, h]⟩
  rw [← SetLike.mem_coe, P.PD_Fil K (Formalism.MainNotions.LocalSituation.botExt l)]
  exact hs

theorem isDR {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (h : IsCrys (P.PD K) ρ) :
    IsDR (P.PD K) ρ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  refine (GlobalTheory.DRFil.isDR_of_isCrys (P.PD K) (fun m c hc b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m c hc b ?_) ρ h2 h).1
  simpa only [P.PD_ι] using hb

theorem multV_shift {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (θ : ↥(GK K) →* (↥LL.1)ˣ)
    (hρ : ∀ g x, ρ' g x = (θ g : ↥LL.1) • ρ g x) (hθ : IsCrys (P.PD K) (charRep θ))
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ)
    (h : ∀ a, multV (P.PD K) (charRep θ) τ a = (({b} : Multiset ℤ).count a : ℤ)) (a : ℤ) :
    multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  haveI := (P.PD K).finK
  obtain ⟨m, k, β, d, hd, h1⟩ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL ↥LL.1 (charRep θ) (isDR T K LL _ hθ) 0 1
    ⟨1 ⊗ₜ ⟨1, (P.PD K).one_mem⟩, rfl⟩
  have key := finrank_twist (P.PD K) (AlgHom.id ↥LL.1 ↥LL.1) ρ ρ' (charRep θ) (fun g => (θ g : ↥LL.1))
    (fun _ _ => rfl) hρ k β d hd h1 τ b (fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl)
  rw [multV, multV, add_right_comm, key, key]

theorem isCrys_iff {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (θ : ↥(GK K) →* (↥LL.1)ˣ)
    (hρ : ∀ g x, ρ' g x = (θ g : ↥LL.1) • ρ g x) (hθ : IsCrys (P.PD K) (charRep θ)) :
    IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ' := by
  obtain ⟨hq, ht, hd⟩ := GlobalTheory.RegularRing.quot_tensor_dual_crys l P AI (GlobalTheory.Per.IsStd.of_tied T)
  exact GlobalTheory.TwistCrys.isCrys_twist_iff (P.PD K) (ht K LL) (hq K LL) (hd K LL) ρ ρ' (charRep θ)
    (fun g => (θ g : ↥LL.1)) LinearMap.id 1 rfl (fun _ _ => rfl) hρ hθ

variable {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))

theorem crysWith_cyc (θ : ↥(GK K) →* (↥LL.1)ˣ) (e : ℕ) (hθ : θ = cycLL (P.PD K) ↥LL.1 ^ (-(e : ℤ))) :
    CrysWith (P.PD K) emb (charRep θ) (fun _ => {(e : ℤ)}) := by
  haveI := (P.PD K).finK
  haveI := LL.2
  subst hθ
  refine ⟨GlobalTheory.BlockCrys.isCrys_cyc_zpow (P.PD K) _, fun i τ _ a => ?_⟩
  rw [GlobalTheory.BlockJumps.multV_twist (P.PD K) (exists_inverse_fontaineElement_mem_fil_neg_one T K) _ e (fun g x => ?_) τ a, Multiset.count_singleton]
  · split_ifs <;> rfl
  · simp [charRep, cycLL]

theorem crysWith_inv (θ : ↥(GK K) →* (↥LL.1)ˣ) (a : ZMod n → ℤ)
    (h : CrysWith (P.PD K) emb (charRep θ) (fun i => {a i})) :
    CrysWith (P.PD K) emb (charRep θ⁻¹) (fun i => {-a i}) := by
  have h1 := crysWith_cyc T K LL emb 1 0 (by simp)
  have hρ : ∀ g x, charRep (1 : ↥(GK K) →* (↥LL.1)ˣ) g x = (θ g : ↥LL.1) • charRep θ⁻¹ g x := fun g x => by
    simp [charRep]
  refine ⟨(isCrys_iff T K LL _ _ θ hρ h.1).2 h1.1, fun i τ hτ c => ?_⟩
  rw [← multV_shift T K LL _ _ θ hρ h.1 τ (a i) (h.2 i τ hτ) c, h1.2 i τ hτ, Multiset.count_singleton,
    Multiset.count_singleton]
  congr 1
  exact if_congr (by omega) rfl rfl

theorem isCrysChar_inv (θ : ↥(GK K) →* (↥(OL LL))ˣ) (a : ZMod n → ℤ) (h : IsCrysChar (P.PD K) emb θ a) :
    IsCrysChar (P.PD K) emb θ⁻¹ (fun i => -a i) := by
  refine ⟨(h.1.comp continuous_inv).congr fun g => by
    rw [Function.comp_apply, map_inv, MonoidHom.inv_apply], ?_⟩
  have e : chiLL ↥LL.1 θ⁻¹ = (chiLL ↥LL.1 θ)⁻¹ := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.inv_apply, ← map_inv]
    exact congrArg (Units.map _) (map_inv θ g).symm
  rw [e]
  exact crysWith_inv T K LL emb _ a h.2

theorem multV_char_zero (hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1)
    (θ : ↥(GK K) →* (↥LL.1)ˣ) (hθ : IsCrys (P.PD K) (charRep θ)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (h : ∀ a, IsJumpV (P.PD K) (charRep θ) τ a → a = 0) (a : ℤ) :
    multV (P.PD K) (charRep θ) τ a = (({0} : Multiset ℤ).count a : ℤ) := by
  classical
  haveI := (P.PD K).finK
  have hdr := isDR T K LL _ hθ
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL ↥LL.1 (charRep θ)).1
  obtain ⟨m, k, β, d, hd, h1⟩ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL ↥LL.1 (charRep θ) hdr 0 1
    ⟨1 ⊗ₜ ⟨1, (P.PD K).one_mem⟩, rfl⟩
  have hpos : ∀ τ', 1 ≤ finrank ↥LL.1 (DdRE (P.PD K) (charRep θ) τ') := fun τ' => by
    haveI : FiniteDimensional ↥LL.1 (DdRE (P.PD K) (charRep θ) τ') :=
      Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) (charRep θ)) inf_le_left
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact ddRE_ne_bot (P.PD K) (exists_inverse_fontaineElement_mem_fil_neg_one T K) (charRep θ) (fun g => (θ g : ↥LL.1)) (fun _ _ => rfl) k β d
      (fun i => ⟨(hd i).1, (hd i).2.1⟩) h1 τ'
  rw [Nat.card_eq_fintype_card] at hc
  have hsum := (GlobalTheory.DeRhamSplit.finrank_split (P.PD K) hc (charRep θ)).1
  rw [hdr, finrank_self, mul_one, ← hc, ← Finset.card_univ, Finset.card_eq_sum_ones] at hsum
  have hone := (Finset.sum_eq_sum_iff_of_le fun τ' _ => hpos τ').1 hsum τ (Finset.mem_univ _)
  rw [multV_of_only_zero (P.PD K) _ τ h, ← hone, Multiset.count_singleton]
  split_ifs <;> rfl

omit T in

theorem card_emb {lam : ↥(OL LL)} (h : Standing P K LL emb lam) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  have e : K0 K = K.1 := inf_eq_left.2 h.2.1.1
  rw [← Nat.card_congr ((IntermediateField.equivOfEq e).arrowCongr (AlgEquiv.refl : ↥LL.1 ≃ₐ[ℚ_[l]] ↥LL.1)),
    ← Nat.card_congr (Equiv.ofBijective _ h.2.2.2.1), Nat.card_zmod, h.2.2.1]

end Tied

theorem crysCalc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    (S : TopSit P) : S.CrysCalc := by
  obtain ⟨T⟩ := hT
  refine ⟨fun A A' A'' U U' e he h h' => ⟨?_, fun i τ hτ a => ?_⟩,
    fun A U θ a h hθ => ⟨⟨?_, fun i τ hτ c => ?_⟩, isCrysChar_inv T _ _ _ θ a hθ⟩, ?_, fun μ hc hμ => ?_⟩
  · refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ e.symm (fun g x => ?_)
      (GlobalTheory.Cmp.WachMonoidal.isCrys_prod _ h.1 h'.1)
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
    rfl
  · haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T S.K S.LL _ A.ρ).1
    haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T S.K S.LL _ A'.ρ).1
    rw [GlobalTheory.HTW.SumJumps.multV_add _ e he, h.2 i τ hτ, h'.2 i τ hτ, Multiset.count_add, Nat.cast_add]
  · exact (isCrys_iff T _ _ _ _ (chiLL ↥S.LL.1 θ) (fun _ _ => rfl) hθ.2.1).1 h.1
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + a i := ⟨c - a i, by ring⟩
    rw [multV_shift T _ _ A.ρ _ (chiLL ↥S.LL.1 θ) (fun _ _ => rfl) hθ.2.1 τ (a i) (hθ.2.2 i τ hτ) c, h.2 i τ hτ,
      Multiset.count_map_eq_count' _ _ (add_left_injective (a i))]
  · have hε := S.hyp.2.1.2.2.2
    have e : chiLL ↥S.LL.1 S.Γ.ε = cycLL (P.PD S.K) ↥S.LL.1 := by
      ext g : 2
      exact hε g
    refine ⟨(GlobalTheory.Survey.SlowDecayFunctions.continuous_cyc P S.K S.LL).congr fun g => (hε g).symm, ?_⟩
    have := crysWith_inv T _ _ S.emb _ (fun _ => ((1 : ℕ) : ℤ))
      (crysWith_cyc T S.K S.LL S.emb (cycLL (P.PD S.K) ↥S.LL.1)⁻¹ 1 (by simp))
    rw [inv_inv, ← e] at this
    exact this
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.unramified_isCrys_and_jump_eq_zero l P AI T S.K S.LL (charLat ℚ_[l] Subtype.val_injective μ hc)
      (fun g hg x => by
        change (chiLL ↥S.LL.1 μ g : ↥S.LL.1) • x = x
        simp [hμ g hg])
    exact ⟨hc, h1, fun i τ _ a => multV_char_zero T _ _ (card_emb _ _ _ S.hyp.1) _ h1 τ (h2 τ) a⟩

end GlobalTheory.TopSteps.CrysRules
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShiftStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_twist_crystallineCharacter_jumps_shift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (χ : ↥(GK K) →* (↥LL.1)ˣ), IsTwistRep χ ρ ρ' → IsCrys (P.PD K) (charRep χ) → IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ' ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a b : ℤ), IsJumpV (P.PD K) (charRep χ) τ b → multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  first | exact @GlobalTheory.TwistRepCrys.isCrys_and_multV_twist | exact GlobalTheory.TwistRepCrys.isCrys_and_multV_twist | (intros; apply GlobalTheory.TwistRepCrys.isCrys_and_multV_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalBlockAverageLastColumnEqZeroStatement
section
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_blockAverage_lastColumn_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ), Continuous F → (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) → GlobalTheory.CuspRep.IsCuspidal F → ∀ r : ℕ, 0 < r → r ≤ a - 1 → ∀ g : GA E a, GlobalTheory.CuspGeneric.avg (GlobalTheory.CuspGeneric.ratV E (GlobalTheory.CuspGeneric.UnipotentBlockColumnIndex a r (a - 1))) (fun x => F ((GlobalTheory.CuspGeneric.blkU x : GA E a) * g)) = 0 := by
  first | exact @GlobalTheory.CuspGeneric.avg_blk_last_eq_zero | exact GlobalTheory.CuspGeneric.avg_blk_last_eq_zero | (intros; apply GlobalTheory.CuspGeneric.avg_blk_last_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutBoundOfSteps
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

noncomputable section

namespace GlobalTheory.Pass

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cutBound_of_steps : StepsNoCut → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CT : ℕ), SumRepresentations.adm5 D → ElementDenominator.adm12 D → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → GaloisFamilyConditions (D := D) → admG5 (D := D) → admG6 (D := D) → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → LocalGlobalCompatibilityAlt (D := D) → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → CongruenceAtTypePrimes (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π) := by
  rintro ⟨_hCI, _hCen, hDeg, hType, hPotD, hPotDu, hJD, hJDu, hLift, hSub, hCont, hLocD, hLocDu, hHf, hRes, hGlob⟩
  intro D P HW F CT h5 h12 hIne hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB hBK hBC hLGC hFont htie0 hChi
  obtain ⟨hDJ, hPDR, hPT, hBr, hIE⟩ := GlobalTheory.Closing.closing_at_record D
  intro i k k' _hkk' hlk r ρ hr hdec eta s S sg U hs _hlog hCT _hsg hHost hSQ hsFin hSha π hπ Xs hπXs hTL
  have hπZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  have hHG : HG D.nd D.naut i := GlobalTheory.EigenProjector.HG_of_mem_Zgood D i π hπ
  have hdecπ := hdec π hπZ
  have hTLGC : TypeLGC P := hType D P hDZ htie0 hBC hLGC h5
  have hPH : PairedCharacterCondition.tiePH (D := D) := D.loc_tie
  have hl2 : D.nd.l i ≠ 2 := hlk ▸ Formalism.L2.Pj.g_ne_two D k
  have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw ∧
      LocBoundP i w hw r Xs (WpO D.nd i ρ π) (2 * D.R.r * eMax D CT eta) ∧
      ∀ c ∈ Finset.Icc 1 D.R.t, LocBoundP i w hw r Xs (chiRatO D.nd i c) (2 * 1 * eMax D CT eta) := by
    intro w hw
    have hdeg1 := (hDeg D hBr i k hlk).2 w hw
    have hPot : PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) :=
      hPotD D P hTLGC hFont htie0 hBr hPH hChi hIE h12 hPT hIne i k hlk r ρ hr π hπZ hdecπ Xs hπXs hTL w hw
    have hCT' : CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i := hlk ▸ hCT
    have hH : eta + D.R.t + 1 < s + S := by omega
    have hsub := hSub D i r ρ hr π hdecπ Xs hπXs
    have key : ∀ (kk : ℕ) (M : GE D.nd →* Matrix (Fin kk) (Fin kk) (D.nd.O i)), SubTw i r Xs M →
        LocBoundP i w hw r Xs M (2 * kk * eMax D CT eta) := by
      intro kk M hM
      cases hsw : sg w
      · have hPotDu' := hPotDu D hPT i r hr Xs w hw _ hPot
        have hJ := hJDu D hDJ hPDR i r hr eta s S sg U hs hHost Xs w hw _ hsw hPot
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rDuO D.nd i r x)
          (fun x => (hCont D i r hr x).2) eta (s + S) hH hCT' hPotDu' hJ
        exact hLocDu D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
      · have hJ := hJD D i r eta s S sg U hs hHost Xs w hw hsw
        have hL := hLift D CT hT hFont i w hw hdeg1 (↥Xs) (fun x => rTwO D.nd i r x)
          (fun x => (hCont D i r hr x).1) eta (s + S) hH hCT' hPot hJ
        exact hLocD D hLOC hBK hFont hPDR i r hr Xs w hw hdeg1 _ _ hPot hL kk M hM
    exact ⟨hHf D P HW F hTB hIE i k hlk hl2 w hw hdeg1, key _ _ hsub.1, fun c hc => key _ _ (hsub.2 c hc)⟩
  have hG1 : TruncatedSeriesCountingIdentities.admG1 (D := D) i r := by
    intro g kk
    obtain ⟨f, hf⟩ := (hG14 i r hr).1 g kk
    have e : (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff kk) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [e]
    exact f.2
  have hG4 : TruncatedSeriesCountingIdentities.admG4 (D := D) i r := by
    intro x v hl hS hQ g hg
    exact (hG14 i r hr).2.2.2 x v hl hS hQ (D.nd.plOm.1 v) (D.nd.plOm.2 v) g hg
  obtain ⟨S0, hS0, -⟩ := ((hN5g i k hlk hHG r ρ hr).2 π hπZ hdecπ).1 hπZ
  have hG := hGlob D i r ρ π Xs (2 * D.R.r * eMax D CT eta) (2 * 1 * eMax D CT eta) hr hG1
    (hRes D hRbar hG14 i r ρ hr π hπ hdecπ) hG4 (galois_condition_five_of D i r hG5 hHG hr)
    (GlobalTheory.TameDesign.main D i).2 (galois_condition_six_of D i r hG6 hHG hr) hdecπ (coefficient_compatibility_of D i (hBr i)) hSQ
    ⟨S0, hS0⟩ hπZ hπXs hloc (hsFin π hπ) hSha
  have hcard : (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f := (hDeg D hBr i k hlk).1
  have hnat : (placesOver D.host.E (D.nd.l i)).ncard * (2 * D.R.r * eMax D CT eta + D.R.t * (2 * 1 * eMax D CT eta)) =
      D.R.f * (2 * ((2 * D.R.r + D.R.t * 2) * (CT * ((D.R.nV + 1) * ((D.R.nV + 1) ^ 2 / 4) +
        (eta + D.R.t + 1) * ((D.R.nV + 1) + (D.R.nV + 1) ^ 2 / 4))))) := by
    rw [hcard]; unfold eMax; ring
  rw [hnat] at hG
  have hrn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr2 : 2 ≤ D.R.r := hRbar.1
  refine ⟨D.R.nV + 1, (D.R.nV + 1) ^ 2 / 4, by omega, le_refl _, ?_, Nat.mul_div_le _ _, ?_⟩
  · have h9 : 9 ≤ (D.R.nV + 1) ^ 2 := by nlinarith
    omega
  · have hG' := (Rat.cast_le (K := ℝ)).2 hG
    push_cast at hG' ⊢
    linarith

end GlobalTheory.Pass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonMatrixMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discPeriod_comparison_matrix_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  first | exact @GlobalTheory.BSP.Height.rel_mul | exact GlobalTheory.BSP.Height.rel_mul | (intros; apply GlobalTheory.BSP.Height.rel_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHomStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discPeriod_comparison_relation_map_prismHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B B' : Obj l ↥(OL K)) (f₀ f g : Hom bk.prism B) (f₀' : Hom bk.prism B') (k : Hom B B') (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → (∃ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap k.f Fk) ∧ ∀ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap k.f Fk → ht.Rel (BK.hf f₀' X) (k.comp f) (k.comp g) (ε.map Fk) := by
  first | exact @GlobalTheory.BSP.Height.rel_map | exact GlobalTheory.BSP.Height.rel_map | (intros; apply GlobalTheory.BSP.Height.rel_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantPhiModuleMatrixMemOE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.EquivOE

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem not_dvd_E : ¬ (l : bk.S) ∣ bk.E := by
  rintro ⟨t, ht⟩
  have h := congrArg (coeff bk.Ep.natDegree) ht
  rw [← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, Polynomial.coeff_coe, bk.monic.coeff_natDegree] at h
  have h2 := congrArg (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) h
  rw [map_mul, map_natCast, map_one, CharP.cast_eq_zero, zero_mul] at h2
  exact one_ne_zero h2

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (X : Matrix (Fin d') (Fin d) (WCb l)), (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) →
    bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) →
    ∀ i j, X i j ∈ bk.OE := by
  intro l _ K bk d d' S S' X hg hφ
  obtain ⟨u, hu, heu⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.1 bk.E (not_dvd_E bk)
  have hA : S.A.map bk.evW * S.A'.map bk.evW = bk.evW bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, S.A_mul]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h1 : X = (u ^ (S'.a + S.b) * bk.evW bk.E ^ S.a) •
      (S'.A.map bk.evW * X.map (frobW l) * S.A'.map bk.evW) := by
    rw [mul_smul, ← Matrix.smul_mul, hφ, Matrix.smul_mul, Matrix.mul_assoc, hA, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, smul_smul, mul_assoc, ← pow_add, ← mul_pow, mul_comm u, heu, one_pow, one_smul]
  intro i j
  refine GlobalTheory.T.mem_OE_of_invariant_frobenius_solution l K bk (Fin d' × Fin d) (fun p => X p.1 p.2)
    (fun p q => u ^ (S'.a + S.b) * bk.evW bk.E ^ S.a * bk.evW (S'.A q.1 p.1) * bk.evW (S.A' p.2 q.2))
    (fun p q => ?_) (fun q => ?_) (fun g h q => ?_) (i, j)
  · exact bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.mul_mem (bk.OE.pow_mem hu _) (bk.OE.pow_mem (evW_mem bk _) _))
      (evW_mem bk _)) (evW_mem bk _)
  · have h2 := congrFun (congrFun h1 q.1) q.2
    rw [h2, Fintype.sum_prod_type_right]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => by ring
  · exact congrFun (congrFun (hg g h) q.1) q.2

end GlobalTheory.BSP.EquivOE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasureStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleUnitsHaarMeasureDivAbs_isHaarMeasure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → BorelSpace A.Kˣ ∧ (LinDesc.unitsMeas A μK).IsHaarMeasure ∧ ∀ h : A.K → ℂ, ∫ s, h (s : A.K) ∂(LinDesc.unitsMeas A μK) = ∫ t in {t : A.K | IsUnit t}, h t * ((A.absK t : ℂ))⁻¹ ∂μK := by
  first | exact @GlobalTheory.JR.LinDesc.unitsMeas_isHaar | exact GlobalTheory.JR.LinDesc.unitsMeas_isHaar | (intros; apply GlobalTheory.JR.LinDesc.unitsMeas_isHaar <;> assumption)
end

