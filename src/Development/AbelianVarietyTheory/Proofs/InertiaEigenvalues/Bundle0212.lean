import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0200
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0175
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargestModel
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem exists_greatest_of_sup_closed {S V ι : Type} [CommRing S] [IsNoetherianRing S] [AddCommGroup V]
    [Module S V] [Finite ι] (C : (ι → Submodule S V) → Prop) (P N₀ : ι → Submodule S V) (h₀ : C N₀)
    (hP : ∀ i, (P i).FG) (hle : ∀ N, C N → ∀ i, N i ≤ P i)
    (hsup : ∀ N N', C N → C N' → C (fun i => N i ⊔ N' i)) :
    ∃ N, C N ∧ ∀ N', C N' → ∀ i, N' i ≤ N i := by
  classical
  have one : ∀ i, ∃ N, C N ∧ ∀ N', C N' → N' i ≤ N i := by
    intro i
    haveI : IsNoetherian S (P i) := isNoetherian_of_fg_of_noetherian _ (hP i)
    obtain ⟨_, ⟨N, hN, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 this
      {Q : Submodule S (P i) | ∃ N, C N ∧ (N i).comap (P i).subtype = Q} ⟨_, N₀, h₀, rfl⟩
    refine ⟨N, hN, fun N' hN' x hx => ?_⟩
    have h1 := hmax _ ⟨_, hsup N N' hN hN', rfl⟩
    have h2 : (N i).comap (P i).subtype = (N i ⊔ N' i).comap (P i).subtype :=
      (Submodule.comap_mono le_sup_left).eq_of_not_lt h1
    have h3 : (⟨x, hle N' hN' i hx⟩ : P i) ∈ (N i ⊔ N' i).comap (P i).subtype :=
      Submodule.mem_sup_right hx
    rw [← h2] at h3
    exact h3
  have all : ∀ s : Finset ι, ∃ N, C N ∧ ∀ N', C N' → ∀ i ∈ s, N' i ≤ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨N₀, h₀, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨N, hN, h⟩ := ih
      obtain ⟨N₁, hN₁, h₁⟩ := one a
      refine ⟨_, hsup N N₁ hN hN₁, fun N' hN' i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_sup_of_le_right (h₁ N' hN')
      · exact le_sup_of_le_left (h N' hN' i hi)
  haveI := Fintype.ofFinite ι
  obtain ⟨N, hN, h⟩ := all Finset.univ
  exact ⟨N, hN, fun N' hN' i => h N' hN' i (Finset.mem_univ i)⟩

theorem exists_largest_model : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N₀ : Lats k n A.m), M.Model A N₀ → ∃ N, M.Model A N ∧ ∀ N', M.Model A N' → ∀ i, N' i ≤ N i := by
  intro k G _ _ l n _ _ _ R F r Dt M A N₀ h₀
  obtain ⟨-, hl₀, hab₀, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M A N₀ h₀
  refine exists_greatest_of_sup_closed (fun N => M.Model A N)
    (fun i => sh (-(sg l Dt.h i : ℤ)) (N₀ i)) N₀ h₀ (fun i => ((hl₀ i).shift _).1) (fun N hN i => ?_)
    (fun N N' => GlobalTheory.T.model_sup_alt F M A N N')
  obtain ⟨-, hl, hab, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M A N hN
  have h := sh_le_sh (-(sg l Dt.h i : ℤ)) (GlobalTheory.T.phiGamma_lattice_families_shift_inclusion (F.D A) Dt.h Dt.w N N₀ hl hl₀ hab hab₀ i)
  rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitRep
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem exists_limit_rep : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∃ r : Γ →* GL (Fin a) (PadicAlgCl l), Continuous r ∧ IsSSRep r ∧ (∀ j, trc r (x j) = θ j) ∧ PolyApprox (trc r) (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx θ L hL hθL C hC hA
  have hU := GlobalTheory.T.approximatedTraceSystem_locally_cauchy l Γ a J x θ C hC hA
  obtain ⟨T, hTc, hTx⟩ := GlobalTheory.Cong.extend_of_locallyCauchy l Γ J x hx θ L hL hθL hU
  have hA' : PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) := by
    have : (fun j => T (x j)) = θ := funext hTx
    rw [this]; exact hA
  have hT : PolyApprox T (trc '' C) := GlobalTheory.Cong.polyApprox_of_denseRange l Γ a J x hx T hTc C hC hA'
  have hP : IsPsChar a T := GlobalTheory.T.isPseudoCharacter_of_approximatedByTraces l Γ a T C hT
  obtain ⟨r, hr, htr⟩ := GlobalTheory.PsChar.exists_ssRep Γ (PadicAlgCl l) a T hP
  have htrc : trc r = T := funext fun g => htr g
  refine ⟨r, ?_, hr, fun j => by rw [htrc]; exact hTx j, by rw [htrc]; exact hT⟩
  refine GlobalTheory.SSCont.continuous_of_continuous_trace Γ (PadicAlgCl l) a r hr ?_
  have : (fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)).trace) = T := htrc
  rw [this]; exact hTc

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowPSmulMemOneFractionRing
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem padicCoeff_exists_pow_smul_mem_one :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O],
    PadicCoeff p O → ∀ y : FractionRing O,
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := by
  intro p O _ _ _ _ hP y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ϖ ∣ (p : O) := by
    have h := hP.p_mem
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
    exact h
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  dsimp only
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hbk : (b : O) ∣ (p : O) ^ k := by
    rw [hu]
    exact (Units.mul_left_dvd).mpr (pow_dvd_pow_of_dvd hdvd k)
  obtain ⟨c, hc⟩ := hbk
  refine ⟨k, ?_⟩
  rw [Submodule.mem_comap, LinearMap.lsmul_apply, Submodule.mem_one]
  refine ⟨c * a, ?_⟩
  rw [Algebra.smul_def, hc, map_mul, map_mul, mul_assoc, mul_left_comm, IsLocalization.mk'_spec']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueEv
section
namespace GlobalTheory.HWL.SeriesEval

open PowerSeries IsLocalRing Filter Topology

section Shift

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem X_add_C_mem {c : O} (hc : c ∈ maximalIdeal O) : (X + C c : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simpa using hc

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem exists_shift {c : O} (hc : c ∈ maximalIdeal O) :
    ∃ s : O⟦X⟧ →ₐ[O] O⟦X⟧, s X = X + C c := by
  have : IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := ReciprocityTheory.P1.isAdicComplete_ps
  exact ⟨GlobalTheory.mvEvalAdic (σ := Unit) O (maximalIdeal O⟦X⟧) (fun _ => X + C c)
    (fun _ => X_add_C_mem hc), GlobalTheory.mvEvalAdic_X (σ := Unit) _ _ _ ()⟩

theorem exists_div {c : O} (hc : c ∈ maximalIdeal O) (b : O⟦X⟧) :
    ∃ (r : O) (q : O⟦X⟧), b = C r + (X - C c) * q := by
  have : IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := ReciprocityTheory.P1.isAdicComplete_ps
  obtain ⟨s, hs⟩ := exists_shift hc
  obtain ⟨s', hs'⟩ := exists_shift (neg_mem hc)
  have hC : ∀ r, s' (C r) = C r := fun r => s'.commutes r
  have hX : (s'.comp s) X = X := by
    rw [AlgHom.comp_apply, hs, map_add, hs', hC, map_neg]; ring
  have h : s'.comp s = AlgHom.id O O⟦X⟧ :=
    GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff (σ := Unit) (maximalIdeal O⟦X⟧)
      (fun _ => by
        change (s'.comp s) X ∈ _
        rw [hX]; simpa using X_add_C_mem (zero_mem (maximalIdeal O)))
      (fun _ => hX)
  refine ⟨constantCoeff (s b), s' (mk fun p => coeff (p + 1) (s b)), ?_⟩
  have h1 : s' (s b) = b := DFunLike.congr_fun h b
  conv_lhs => rw [← h1, eq_X_mul_shift_add_const (s b)]
  rw [map_add, map_mul, hs', hC, map_neg]
  ring

variable {L : Type*} [CommRing L] [Algebra O L]

theorem exists_ev {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) : ∃ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x := by
  obtain ⟨s, hs⟩ := exists_shift hc
  have hy : HasSubst (x - C (algebraMap O L c)) :=
    HasSubst.of_constantCoeff_zero' (by simp [hx])
  refine ⟨(substAlgHom hy).comp s, ?_⟩
  have hC : (substAlgHom hy : O⟦X⟧ →ₐ[O] L⟦X⟧) (C c) = C (algebraMap O L c) :=
    ((substAlgHom hy : O⟦X⟧ →ₐ[O] L⟦X⟧).commutes c).trans (PowerSeries.algebraMap_apply (r := c))
  rw [AlgHom.comp_apply, hs, map_add, substAlgHom_X, hC]
  ring

theorem ev_div {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) :
    ∃ z : L⟦X⟧, ∀ b : O⟦X⟧, ∃ (r : O) (q : O⟦X⟧), ∀ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x →
      ev b = C (algebraMap O L r) + X * (z * ev q) := by
  refine ⟨mk fun p => coeff (p + 1) x, fun b => ?_⟩
  obtain ⟨r, q, rfl⟩ := exists_div hc b
  refine ⟨r, q, fun ev hev => ?_⟩
  have hC : ∀ r, ev (C r) = C (algebraMap O L r) := fun r =>
    (ev.commutes r).trans PowerSeries.algebraMap_apply
  rw [map_add, map_mul, map_sub, hC, hC, hev, ← hx, ← mul_assoc]
  congr 2
  rw [sub_eq_iff_eq_add]
  exact eq_X_mul_shift_add_const x

theorem ev_unique {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) (ev ev' : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (h' : ev' X = x) : ev = ev' := by
  obtain ⟨z, hz⟩ := ev_div hc x hx
  have key : ∀ (k : ℕ) (b : O⟦X⟧), X ^ k ∣ ev b - ev' b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro b
      obtain ⟨r, q, hq⟩ := hz b
      have : ev b - ev' b = X * (z * (ev q - ev' q)) := by rw [hq ev h, hq ev' h']; ring
      rw [this, pow_succ']
      exact mul_dvd_mul_left _ ((ih q).mul_left z)
  refine AlgHom.ext fun b => PowerSeries.ext fun k => ?_
  have := X_pow_dvd_iff.1 (key (k + 1) b) k k.lt_succ_self
  rwa [map_sub, sub_eq_zero] at this

variable {K : Type*} [NormedField K] (i : L →+* K)

theorem ev_bounded (hi : ∀ r : O, ‖i (algebraMap O L r)‖ ≤ 1) {c : O} (hc : c ∈ maximalIdeal O)
    (x : L⟦X⟧) (hx : constantCoeff x = algebraMap O L c) (ev : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (k : ℕ) : ∃ B : ℝ, ∀ b, ‖i (coeff k (ev b))‖ ≤ B := by
  obtain ⟨z, hz⟩ := ev_div hc x hx
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · refine ⟨1, fun b => ?_⟩
      obtain ⟨r, q, hq⟩ := hz b
      simpa [hq ev h] using hi r
    · choose! B hB using ih
      refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ‖i (coeff p.1 z)‖ * B p.2, fun b => ?_⟩
      obtain ⟨r, q, hq⟩ := hz b
      rw [hq ev h, map_add, coeff_succ_X_mul, coeff_C, if_neg k.succ_ne_zero, zero_add, coeff_mul,
        map_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
      rw [map_mul, norm_mul]
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact mul_le_mul_of_nonneg_left (hB _ (by omega) _) (norm_nonneg _)

theorem ev_tendsto (hi : ∀ r : O, ‖i (algebraMap O L r)‖ ≤ 1) {c : O} (hc : c ∈ maximalIdeal O)
    (hc1 : ‖i (algebraMap O L c)‖ < 1)
    (x : L⟦X⟧) (hx : constantCoeff x = algebraMap O L c) (ev : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (a : O⟦X⟧) (k : ℕ) :
    Tendsto (fun m : ℕ => i (coeff k (ev ((trunc m a : Polynomial O) : O⟦X⟧)))) atTop
      (𝓝 (i (coeff k (ev a)))) := by
  obtain ⟨B, hB⟩ := ev_bounded i hi hc x hx ev h k
  have hC : ev (C c) = C (algebraMap O L c) := (ev.commutes c).trans PowerSeries.algebraMap_apply
  rw [← tendsto_add_atTop_iff_nat k, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (g := fun n => ‖i (algebraMap O L c)‖ ^ n * B)
    (fun n => ?_) (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hc1).mul_const B)
  obtain ⟨b, hb⟩ : X ^ (n + k) ∣ ((trunc (n + k) a : Polynomial O) : O⟦X⟧) - a :=
    X_pow_dvd_iff.2 fun m hm => by simp [coeff_trunc, hm]
  have hmem : (C c + (X - C c) : O⟦X⟧) ^ (n + (k + 1) - 1) ∈
      Ideal.span {C c ^ n, (X - C c) ^ (k + 1)} :=
    Ideal.add_pow_add_pred_mem_of_pow_mem_of_commute _
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) (Commute.all _ _)
  rw [add_sub_cancel, show n + (k + 1) - 1 = n + k by omega, Ideal.mem_span_pair] at hmem
  obtain ⟨u, v, huv⟩ := hmem
  have hy : X ∣ x - C (algebraMap O L c) := X_dvd_iff.2 (by simp [hx])
  have h0 : coeff k ((x - C (algebraMap O L c)) ^ (k + 1) * ev (v * b)) = 0 :=
    X_pow_dvd_iff.1 ((pow_dvd_pow_of_dvd hy _).mul_right _) k k.lt_succ_self
  have he : ev (X ^ (n + k) * b) = C (algebraMap O L c ^ n) * ev (u * b) +
      (x - C (algebraMap O L c)) ^ (k + 1) * ev (v * b) := by
    rw [← huv]
    simp only [map_mul, map_add, map_pow, map_sub, hC, h]
    ring
  rw [← map_sub, ← map_sub, ← map_sub, hb, he, map_add, h0, add_zero, coeff_C_mul, map_mul,
    norm_mul, map_pow, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

end Shift

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem existsUnique_ev : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (x : PowerSeries ↥LL.1),
    ‖((PowerSeries.constantCoeff x : ↥LL.1) : Om l)‖ < 1 →
    (∃! ev : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1, ev PowerSeries.X = x) ∧
    ∀ ev : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1, ev PowerSeries.X = x →
      ∀ (a : PowerSeries ↥(OL LL)) (k : ℕ), Filter.Tendsto (fun m : ℕ =>
        ((PowerSeries.coeff k (ev ((PowerSeries.trunc m a : Polynomial ↥(OL LL)) :
          PowerSeries ↥(OL LL))) : ↥LL.1) : Om l)) Filter.atTop
        (nhds ((PowerSeries.coeff k (ev a) : ↥LL.1) : Om l)) := by
  intro l _ LL x hx
  obtain ⟨_, hcomp, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hfin := LL.2
  have hn : ∀ y : ↥LL.1, ‖GlobalTheory.DiscEval.fieldEmb LL.1 y‖ = ‖(y : Om l)‖ := fun y => by
    rw [GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hi : ∀ r : ↥(OL LL), ‖algebraMap ↥LL.1 (Om l) (algebraMap ↥(OL LL) ↥LL.1 r)‖ ≤ 1 :=
    fun r => (hn r).ge.trans ((GlobalTheory.DiscEval.mem_integralClosure_iff_norm LL.1 r).1 r.2)
  let c : ↥(OL LL) := ⟨constantCoeff x,
    (GlobalTheory.DiscEval.mem_integralClosure_iff_norm LL.1 _).2 ((hn _).trans_le hx.le)⟩
  have hxc : constantCoeff x = algebraMap ↥(OL LL) ↥LL.1 c := rfl
  have hc : c ∈ maximalIdeal ↥(OL LL) := fun hu =>
    ((hn _).trans_lt hx).ne ((GlobalTheory.DiscEval.isUnit_iff_norm LL.1 c).1 hu)
  have hinst : ((OL LL).toAlgebra : Algebra ↥(OL LL) (↥LL.1)⟦X⟧) = MvPowerSeries.instAlgebra :=
    Algebra.algebra_ext _ _ fun r =>
      (PowerSeries.algebraMap_apply (R := ↥(OL LL)) (A := ↥LL.1) (r := r)).symm
  generalize ((OL LL).toAlgebra : Algebra ↥(OL LL) (↥LL.1)⟦X⟧) = inst at hinst ⊢
  subst hinst
  refine ⟨?_, fun ev hev a k =>
    ev_tendsto (algebraMap ↥LL.1 (Om l)) hi hc hx x hxc ev hev a k⟩
  obtain ⟨ev, hev⟩ := exists_ev hc x hxc
  exact ⟨ev, hev, fun ev' hev' => ev_unique hc x hxc ev' ev hev' hev⟩

end GlobalTheory.HWL.SeriesEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDuality
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.FinIsoDualLattice

theorem finIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : FinIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO i D hD
  obtain ⟨hR, hC, hT2, hA, hpm, hp0⟩ := hO
  haveI := hR; haveI := hC; haveI := hT2; haveI := hD.t2'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hFin, hFree⟩ := GlobalTheory.T.dualLat_finite_free_of_isLatticeIn D.bT D.T hD.lat hD.perf
  haveI := hFin; haveI := hFree
  obtain ⟨hcpl, hsep⟩ := GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer hA ϖ hϖ
  obtain ⟨hcT, hsT⟩ := GlobalTheory.freeModule_adicComplete_separated ϖ hcpl hsep (↥D.T')
  obtain ⟨hcomp, hopen, hemb⟩ := GlobalTheory.T.finite_free_module_compact_adic_dvr hA (M := ↥D.T') ϖ hϖ
  haveI := hcomp
  have hρ : ContAction D.ρTl' := sub_contAction D.contT' D.T' D.stT'
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rwa [← Irreducible.maximalIdeal_eq hϖ]
  obtain ⟨s, hs⟩ := GlobalTheory.T.modUniformiser_cocycles_finite_classes_local hT hK i D.ρTl' hρ ϖ hpϖ hopen
  have hl := GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary D.ρTl' hρ ϖ hemb.isEmbedding s hs
  have hd : ∀ t : ↥D.T', d0 D.ρTl' t ∈ Z1 D.ρTl' := fun t => by
    refine ⟨?_, fun g h => ?_⟩
    · exact (hρ.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]; abel
  let d : ↥D.T' →ₗ[O] ↥(Z1 D.ρTl') := LinearMap.codRestrict _ (d0 D.ρTl') hd
  have hdN : LinearMap.range d ≤ (B1 D.ρTl').comap (Z1 D.ρTl').subtype := by
    rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩
  have hZ : ∀ c : ↥(Z1 D.ρTl'), (∀ n : ℕ, ∃ z : ↥(Z1 D.ρTl'), c = ϖ ^ n • z) → c = 0 := by
    intro c hc
    apply Subtype.ext; funext g
    exact hsT _ fun n => by
      obtain ⟨z, hz⟩ := hc n
      exact ⟨(z : G → ↥D.T') g, by rw [hz]; rfl⟩
  refine GlobalTheory.finite_quotient_of_complete_nakayama ϖ hcpl hcT hZ d _ hdN s fun c => ?_
  obtain ⟨a, c', x, hx⟩ := hl c
  refine ⟨a, c', x, Subtype.ext ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, d, LinearMap.codRestrict_apply]
  exact hx

end GlobalTheory.FinIsoDualLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2TwistFromOpenUnion
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem h2_twist_exists_of_iUnion_open : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ε : G →* Oˣ) {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ z : H2 (twist ε M), ∃ n, ∃ z' : H2 (twist ε (N n)),
      mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype) z' = z := by
  intro O _ _ G _ _ _ ε M _ _ _ _ _ N hmono hopen hcov z
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hK : IsCompact (Set.range f.1) := isCompact_range f.2.1
  have hmono' : Monotone (fun n => (N n : Set M)) := fun a b h => SetLike.coe_subset_coe.mpr (hmono h)
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => (N n : Set M)) hopen
    (fun x _ => Set.mem_iUnion.mpr (hcov x)) hmono'.directed_le
  let f' : G × G → N n := fun x => ⟨f.1 x, hn ⟨x, rfl⟩⟩
  have hc : Continuous f' := f.2.1.subtype_mk _
  have hcoc : f' ∈ Z2 (twist ε (N n)) := by
    refine ⟨hc, fun g h k => ?_⟩
    apply Subtype.ext
    have e := f.2.2 g h k
    have key : ∀ x : N n, ((twist ε (N n) g x : N n) : M) = twist ε M g (x : M) := fun x => rfl
    simpa [f', key] using e
  refine ⟨n, Submodule.Quotient.mk ⟨f', hcoc⟩, ?_⟩
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZero
section
open ReciprocityTheory.Gal
open Formalism.NG
namespace GlobalTheory

theorem hcLC_exists_pow_smul_eq_zero : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ G _ _ _ M _ _ ρ ϖ hM x hx
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
  have hlc : IsLocallyConstant (c : G → M) := hc
  classical
  let f : M → ℕ := fun m => Classical.choose (hM m)
  have hf : ∀ m, ϖ ^ f m • m = 0 := fun m => Classical.choose_spec (hM m)
  have hfin : (Set.range (c : G → M)).Finite := hlc.range_finite
  obtain ⟨N, hN⟩ := (hfin.image f).bddAbove
  refine ⟨N, ?_⟩
  have hc0 : ϖ ^ N • c = 0 := by
    apply Subtype.ext
    funext g
    have hk : f ((c : G → M) g) ≤ N := hN ⟨_, ⟨g, rfl⟩, rfl⟩
    show ϖ ^ N • (c : G → M) g = 0
    rw [← Nat.sub_add_cancel hk, pow_add, mul_smul, hf, smul_zero]
  rw [← LinearMap.map_smul, hc0, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

theorem gA_teichmuller (ρ : ℝ) (y : Formalism.Per.Fl l) :
    gA l ρ (Formalism.Per.tm y) = ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((Formalism.Per.tm y : Formalism.Per.Ainf l).coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n = if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0 := by
    intro n
    split_ifs with h
    · subst h
      simp
    · rw [WittVector.teichmuller_coeff_pos l y n (Nat.pos_of_ne_zero h), GlobalTheory.GaussSlope.untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  unfold gA
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0) ≤
      ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := fun n => by split_ifs <;> simp
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0)
      ⟨_, Set.forall_mem_range.2 hall⟩ 0 (by simp))

theorem isGauss_unit_eq_one {ρ : ℝ} (hρ : 0 < ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    {x : Formalism.Per.Acris l} (hx : IsUnit x) : N x = 1 := by
  obtain ⟨h01, -, -, hmul, halg⟩ := hN
  have hl : N (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, halg]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  have h1 : N 1 = 1 := by
    have := hmul (l : Formalism.Per.Acris l) 1
    rw [mul_one, hl] at this
    exact (mul_left_cancel₀ hρ.ne' (this.symm.trans (mul_one ρ).symm))
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h2 := hmul x y
  rw [hy, h1] at h2
  refine le_antisymm (h01 x).2 ?_
  rw [h2]
  exact mul_le_of_le_one_right (h01 x).1 (h01 y).2

theorem gC_basic_values : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ 1 = 1 ∧ gC l ρ (l : Formalism.Per.Acris l) = ρ ∧ (∀ c : ℤ_[l], c ≠ 0 → gC l ρ (zc l c) = ρ ^ c.valuation) ∧ (∀ y : Formalism.Per.Fl l, gC l ρ (tc l y) = ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖) ∧ ∀ a : Formalism.Per.Ainf l, IsUnit a → gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = 1 := by
  intro l _ ρ h0 h1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, hN.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  refine ⟨isGauss_unit_eq_one hρ hN isUnit_one, hl, fun c hc => ?_, fun y => ?_,
    fun a ha => isGauss_unit_eq_one hρ hN (ha.map _)⟩
  · have e : zc l c = (l : Formalism.Per.Acris l) ^ c.valuation * zc l (PadicInt.unitCoeff hc : ℤ_[l]) := by
      conv_lhs => rw [PadicInt.unitCoeff_spec hc]
      rw [map_mul, map_pow, map_natCast, mul_comm]
    rw [e, GlobalTheory.GaussSlope.map_pow_mul _ hN.2.2.2.1, hl,
      isGauss_unit_eq_one hρ hN ((PadicInt.unitCoeff hc).isUnit.map (zc l)), mul_one]
  · rw [tc, hN.2.2.2.2, gA_teichmuller]

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightsCloseOfHeightGammaConditionsStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senWeights_close_of_height_gamma_conditions : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) {r : ℕ} (Dt : TopData n r) (N₁ N₂ : Lats k n m), ABC D Dt.w Dt.wst N₁ → ABC D Dt.w Dt.wst N₂ → ∀ i y, sen (D.γ i) (N₂ i) y ≠ 0 → ∃ j : ℤ, |j| ≤ Dt.sg l i ∧ sen (D.γ i) (N₁ i) (y + j) ≠ 0 := by
  first | exact @GlobalTheory.Models.sen_near_of_abc | exact GlobalTheory.Models.sen_near_of_abc | (intros; apply GlobalTheory.Models.sen_near_of_abc <;> assumption)
end

