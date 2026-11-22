import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0143
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0336
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory

open Polynomial

theorem dixmier_aeval_injective {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))) (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Injective (aeval T p) := by
  have hs := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have key : ∀ m : Multiset ℂ, Function.Injective (aeval T (m.map fun a => X - C a).prod) := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
      exact Function.injective_id
    | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
      refine Function.Injective.comp ?_ ih
      rw [hlin]; exact hT a
  rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
  refine Function.Injective.comp ?_ (key _)
  rw [aeval_C, Algebra.algebraMap_eq_smul_one]
  intro x y hxy
  simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
  exact smul_right_injective V (leadingCoeff_ne_zero.mpr hp) hxy

theorem dixmier_commutant_scalar (ι V : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (T : Module.End ℂ V) (hT : ∀ i, T * ρ i = ρ i * T) : ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hcomm : ∀ c : ℂ, ∀ i, (T - c • 1) * ρ i = ρ i * (T - c • 1) := by
    intro c i; rw [sub_mul, mul_sub, hT i, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr (LinearMap.ker (T - c • 1)) (fun i x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply, hx, map_zero]) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (T - c • 1)) (fun i x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨ρ i y, by rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply]⟩) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → ℂ[X] := fun c => ∏ d ∈ s.erase c, (X - C d)
    have hq : ∀ c ∈ s, aeval T (∏ d ∈ s, (X - C d)) (w c) = aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (aeval T (∏ d ∈ s, (X - C d))) hsum
      rw [map_zero, map_sum] at h2
      rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (dixmier_aeval_injective T hinj _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [eval_finset_sum, Finset.sum_eq_single i] at h3
    · simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul, eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulOfStableGraph
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem eq_smul_of_stable_graph : ∀ (D : D7) (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi), IsIrred X Pi rf rl → Module.rank ℂ Pi ≤ Cardinal.aleph0 → ∀ S : Submodule ℂ (Pi × Pi), (∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S) → (∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0) → (∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0) → (∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S) → ∃ c : ℂ, c ≠ 0 ∧ ∀ x y : Pi, ((x, y) : Pi × Pi) ∈ S → y = c • x := by
  intro D X Pi rf rl hirr hrank S hf hl h1 h2 hon
  classical
  haveI : Nontrivial Pi := hirr.1
  choose t ht using hon
  have huniq : ∀ x y, ((x, y) : Pi × Pi) ∈ S → t x = y := by
    intro x y hxy
    have h0 : (((0 : Pi), t x - y) : Pi × Pi) ∈ S := by
      have := S.sub_mem (ht x) hxy
      simpa using this
    exact sub_eq_zero.1 (h2 _ h0)
  let T : Module.End ℂ Pi :=
    { toFun := t
      map_add' := fun a b => huniq _ _ (by simpa using S.add_mem (ht a) (ht b))
      map_smul' := fun r a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (by simpa using S.smul_mem r (ht a)) }
  have hTf : ∀ g ∈ GfC X, ∀ x, T (rf g x) = rf g (T x) := fun g hg x => huniq _ _ (hf g hg _ (ht x))
  have hTl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, T (rl τ Y x) = rl τ Y (T x) := fun τ Y hY x => huniq _ _ (hl τ Y hY _ (ht x))
  obtain ⟨c, hc⟩ := GlobalTheory.LocGL.exists_not_isUnit_sub hrank T
  set A := T - algebraMap ℂ (Module.End ℂ Pi) c with hA
  have hAx : ∀ x, A x = T x - c • x := fun x => by simp [hA]
  have hAf : ∀ g ∈ GfC X, ∀ x, A (rf g x) = rf g (A x) := by
    intro g hg x; rw [hAx, hAx, hTf g hg, map_sub, map_smul]
  have hAl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x, A (rl τ Y x) = rl τ Y (A x) := by
    intro τ Y hY x; rw [hAx, hAx, hTl τ Y hY, map_sub, map_smul]
  have hA0 : A = 0 := by
    rcases hirr.2 (LinearMap.ker A)
        (fun g hg x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAf g hg, hx, map_zero])
        (fun τ Y hY x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hAl τ Y hY, hx, map_zero]) with hk | hk
    · rcases hirr.2 (LinearMap.range A)
          (fun g hg x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rf g z, hAf g hg z⟩)
          (fun τ Y hY x hx => by obtain ⟨z, rfl⟩ := hx; exact ⟨rl τ Y z, hAl τ Y hY z⟩) with hr | hr
      · exact LinearMap.range_eq_bot.1 hr
      · exact absurd ((Module.End.isUnit_iff _).2 ⟨LinearMap.ker_eq_bot.1 hk, LinearMap.range_eq_top.1 hr⟩) hc
    · exact LinearMap.ker_eq_top.1 hk
  have hTc : ∀ x, t x = c • x := fun x => by
    have := congrArg (fun f : Module.End ℂ Pi => f x) hA0
    simp only [hAx, LinearMap.zero_apply] at this
    exact sub_eq_zero.1 this
  refine ⟨c, ?_, fun x y hxy => by rw [← huniq x y hxy, hTc]⟩
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : Pi)
  exact hx (h1 x (by simpa [hTc] using ht x))

end GlobalTheory.SquareAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyExistsDoubleCosetAntiInvolutionUnitary
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section
namespace GlobalTheory.AntiInvLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_isUnram : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  have hfin := (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 E))).image
    (fun P : HeightOneSpectrum (𝓞 E) => P.under (𝓞 F))
  refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv
  rw [GlobalTheory.LFun.isUnram_iff] at hv
  push_neg at hv
  obtain ⟨P, hP, h1⟩ := hv
  refine ⟨P, ?_, hP⟩
  simp only [Set.mem_setOf_eq]
  by_contra hnd
  haveI := not_dvd_differentIdeal_iff.1 hnd
  exact h1 Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)}

theorem exists_antiInv_split (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsLattice E L)
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hd : IsSelfDualAt σ J L v) :
    ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  obtain ⟨w, -, -, hw, -⟩ := id hv
  have h : w.under (𝓞 F) = v := HeightOneSpectrum.ext hw
  obtain ⟨e, ⟨-, he⟩, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart hc hJ hL.fg hL.span_eq_top h hv hd
  refine ⟨fun g => e.symm (Formalism.UG.P.heckecomm_tr (e g)), fun x y => ?_, fun x => ?_, fun g => ?_⟩
  · simp only [map_mul, Formalism.UG.P.heckecomm_tr_mul]
  · simp only [MulEquiv.apply_symm_apply, Formalism.UG.P.heckecomm_tr_tr, MulEquiv.symm_apply_apply]
  · obtain ⟨a, b, hab⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n (e g)
    refine ⟨e.symm a, (he _).2 (by simpa using a.2), e.symm b, (he _).2 (by simpa using b.2), ?_⟩
    show e.symm _ = _
    rw [hab]
    apply e.injective
    simp

theorem exists_antiInv_inert (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsLattice E L)
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (hd : IsSelfDualAt σ J L v) :
    ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨-, ⟨c, hc', -⟩, -, -, hrest⟩ := (GlobalTheory.LFun.exists_isInertChart σ hc v).2 w h hw
  obtain ⟨⟨ϖ, hU⟩, hch⟩ := hrest c hc'
  obtain ⟨e, ⟨-, -, he⟩, -⟩ := hch n J L hJ hL.fg hL.span_eq_top hd
  refine ⟨fun g => g⁻¹, mul_inv_rev, inv_inv, fun g => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := GlobalTheory.LFun.ConjParam.inv_mem hU (e g)
  refine ⟨e.symm k₁, (he _).2 (by simpa using hk₁), e.symm k₂, (he _).2 (by simpa using hk₂), ?_⟩
  apply e.injective
  simp [hk]

theorem eventually_exists_antiInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L → ∀ᶠ v in cofinite, ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  intro F E _ _ _ _ _ σ hc n J hJ L hL
  filter_upwards [eventually_isUnram (F := F) (E := E), GlobalTheory.AdelicU.SelfDual.eventually_isSelfDualAt (σ := σ) hJ.2 hL] with v hu hd
  rcases (GlobalTheory.LFun.exists_isInertChart σ hc v).1 hu with hs | ⟨w, hw⟩
  · exact exists_antiInv_split hc hJ hL hs hd
  · exact exists_antiInv_inert hc hJ hL hw hd

end GlobalTheory.AntiInvLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel

variable {D : D7}

theorem gram_det_ne_zero (S : HSp D) : S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv0
  set x : S.V := ∑ j, v j • S.frame j with hxdef
  have hfr : ∀ i, S.hT (S.frame i) x = 0 := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rw [hxdef, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Formalism.BasicNotions.HSpace.gram, mul_comm]
  have hx : S.hT.flip x = 0 := S.frame.ext fun i => by simpa using hfr i
  have hx0 : x = 0 := S.nondeg.2 x fun y => by
    have := LinearMap.congr_fun hx y
    simpa using this
  funext j
  exact Fintype.linearIndependent_iff.1 S.frame.linearIndependent v hx0 j

theorem isUnit_det_incM (S : HSp D) (c : D.host.E) (hc : c ≠ 0) :
    IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)).det := by
  have h1 : (c • S.gram).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (gram_det_ne_zero S)
  have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)).det =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F)) (c • S.gram).det := by
    rw [RingHom.map_det]; rfl
  rw [h2]
  exact (isUnit_iff_ne_zero.2 h1).map _

variable {R : Type} [CommRing R]

def coordsEquiv {n m d : ℕ} (e : Fin m ≃ Fin d) (G : Matrix (Fin n) (Fin n) R) (hG : IsUnit G.det) :
    Matrix (Fin n) (Fin d) R ≃+ Matrix (Fin m) (Fin n) R where
  toFun u := uᵀ.submatrix e id * G
  invFun x := ((x * G⁻¹).submatrix e.symm id)ᵀ
  left_inv u := by
    dsimp only
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ hG, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
      Function.comp_id, Matrix.submatrix_id_id, Matrix.transpose_transpose]
  right_inv x := by
    dsimp only
    rw [Matrix.transpose_transpose, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id,
      Matrix.submatrix_id_id, Matrix.nonsing_inv_mul_cancel_right _ _ hG]
  map_add' u v := by
    show (u + v)ᵀ.submatrix e id * G = uᵀ.submatrix e id * G + vᵀ.submatrix e id * G
    rw [Matrix.transpose_add, ← Matrix.add_mul]
    rfl

theorem coords (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (c : D.host.E) (hc : c ≠ 0) :
    ∃ f : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      ∀ u, f u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)) :
        Matrix (Fin X.rank) (Fin S.rank) (AE D)) :=
  ⟨coordsEquiv e _ (isUnit_det_incM S c hc), fun _ => rfl⟩

end GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_sum {κ : Type} [Fintype κ] (g : κ → AF F) : evI F (∑ i, g i) = ∑ i, evI F (g i) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem mul_realAd_eq_zero {a : AF F} (ha : evI F a = 0) (t : ℝ) : a * realAd F t = 0 := by
  have h1 : a.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha
  have h2 : (realAd F t).2 = 0 := rfl
  show ((a.1 * (realAd F t).1, a.2 * (realAd F t).2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
  rw [h1, h2, zero_mul, mul_zero]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def trForm {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
      (∑ i, (LinearMap.mulRight ℝ (evI F (y i))).comp (LinearMap.proj i)))

theorem trForm_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    trForm F y z = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * evI F (y i)) := by
  simp [trForm, LinearMap.sum_apply]

variable (F) in

def mult {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
  (-(2 * Real.pi * Complex.I)) • (Complex.ofRealCLM.comp (trForm F y))

theorem mult_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = -(2 * Real.pi * Complex.I) * (trForm F y z : ℂ) := by
  simp [mult]

variable (F) in

def heisD {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) :
    SInf F κ →ₗ[ℂ] SInf F κ :=
  (LineDeriv.lineDerivOpCLM ℂ (SInf F κ) v + SchwartzMap.smulLeftCLM ℂ (⇑(mult F y))).toLinearMap

theorem heisD_apply {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) (f : SInf F κ)
    (z : κ → mixedEmbedding.mixedSpace F) :
    heisD F v y f z = fderiv ℝ f z v + mult F y z * f z := by
  have h : (⇑(mult F y)).HasTemperateGrowth := (mult F y).hasTemperateGrowth
  simp [heisD, h, SchwartzMap.lineDerivOp_apply_eq_fderiv]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem exists_heisLine_deriv {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f (D f) := by
  set x₁ := (M.co.e u).1 with hx₁
  set y₁ := (M.co.e u).2 with hy₁
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv
  refine ⟨heisD F v y₁, fun f r hr x => ?_⟩
  set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F y₁ z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ
  have hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x) := by
    intro t
    have he : M.co.e (realAd F t • u) = realAd F t • M.co.e u := map_smul _ _ _
    simp only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]
    have hAt1 : At (evI F) (realAd F t • x₁) := fun a ha => by
      rw [smul_smul, mul_realAd_eq_zero ha, zero_smul]
    rw [hr.1 x _ hAt1]
    set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add,
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    rw [hψ.2.2 A hAt2, htr, harg]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (r x))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  simp only [tens, heisD_apply, mult_apply, ← hz, ← hP]
  simp
  ring

end GlobalTheory.HeisDeriv

open GlobalTheory.HeisDeriv in

theorem GlobalTheory.HeisDeriv.exists_actsD_heisLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f (D f) :=
  fun M ψ hψ u _ => exists_heisLine_deriv M ψ hψ u
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_weilDatum_exchangedPair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T), IsWeilDatumO ψ S T χS χT ω → ∃ ω' : WRep T S, IsWeilDatumO ψ T S χT χS ω' ∧ ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), ω' (h, g) (dag S T f) = dag S T (ω (g, h) f) := by
  first | exact @GlobalTheory.WeilConj.exists_conj_weilDatum | exact GlobalTheory.WeilConj.exists_conj_weilDatum | (intros; apply GlobalTheory.WeilConj.exists_conj_weilDatum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_mem_compact_of_isotropicAnnihilator : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  first | exact @GlobalTheory.IsoMeanAnnih.finPart_mem_compact | exact GlobalTheory.IsoMeanAnnih.finPart_mem_compact | (intros; apply GlobalTheory.IsoMeanAnnih.finPart_mem_compact <;> assumption)
end

