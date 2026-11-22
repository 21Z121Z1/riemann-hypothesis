import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import ReciprocityTheory.DualLattices.Bundle0024
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0225
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0226
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem mem_iff (K : FinExt l) (a : ℤ) (x : P.R.BdR) :
    x ∈ (P.PD K).Fil a ↔ x ∈ (P.PD (botExt l)).Fil a := by
  have h := P.PD_Fil K (botExt l) a
  rw [← SetLike.mem_coe, h, SetLike.mem_coe]

theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ (P.PD (botExt l)).Fil 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := ((P.PD K).Fil 0).smul_mem ⟨x, hK⟩ (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact (mem_iff K 0 _).1 h

theorem t_isUnit (P : LocPrime l) : IsUnit (P.ιB P.tB) := by
  have hu := (P.PD (botExt l)).t_unit
  rw [P.period_datum_t_eq] at hu
  exact hu.map P.ιB

def tU (P : LocPrime l) : P.R.BdRˣ := (t_isUnit P).unit

theorem tU_val : ((tU P : P.R.BdRˣ) : P.R.BdR) = P.ιB P.tB := rfl

theorem act_mem {a : ℤ} (g : GQ l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) :
    P.actQdR g x ∈ (P.PD (botExt l)).Fil a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_bot g⟩ a x hx
  rwa [P.PD_actdR] at this

theorem actQdR_periodT_eq_cyclotomic_bottom (g : GQ l) :
    P.actQdR g (P.ιB P.tB) = algebraMap ℚ_[l] P.R.BdR (P.χQ g) * P.ιB P.tB := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_bot g⟩
  rw [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ P.tB
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  rw [← h3, h, map_smul, Algebra.smul_def]

theorem act_zpow (g : GQ l) (n : ℤ) :
    P.actQdR g ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ n : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) := by
  have h : Units.map ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →* P.R.BdR) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.BdR : ℚ_[l] →* P.R.BdR) (P.χQ g) * tU P :=
    Units.ext (actQdR_periodT_eq_cyclotomic_bottom g)
  have h2 := congrArg (fun u : P.R.BdRˣ => ((u ^ n : P.R.BdRˣ) : P.R.BdR)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at h2
  rw [map_zpow P.χQ] at h2
  exact h2

variable {AI : LocAinf l P} (J : ThetaL P AI)
include J

theorem zpow_mem (n : ℤ) : ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil n := by
  have h1 : ((tU P : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have h2 : (((tU P)⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil (-1) := by
    obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t (-1) 1).1 (by simpa using (P.PD (botExt l)).one_mem)
    rw [← tU_val] at e
    rwa [Units.inv_eq_of_mul_eq_one_right e.symm]
  induction n using Int.induction_on with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h1
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, sub_eq_add_neg]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h2

theorem shift_iff (a b : ℤ) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil b ↔
      x ∈ (P.PD (botExt l)).Fil (a + b) := by
  constructor
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J a) h
    rwa [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul] at this
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J (-a)) h
    rwa [neg_add_cancel_left] at this

omit J in

theorem exists_symbol : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI →
    ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ,
      (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧
      (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a,
        sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧
      (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧
      ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a,
        sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  intro l _ P AI J K
  refine ⟨fun a x => J.θ (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x), fun a => ?_⟩
  have key : ∀ x ∈ (P.PD K).Fil a,
      ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil 0 := fun x hx =>
    (shift_iff J a 0 x).2 (by rw [add_zero]; exact (mem_iff K a x).1 hx)
  refine ⟨fun x hx y hy => ?_, fun c x hx => ?_, fun x hx => ?_, fun g x hx => ?_⟩
  · beta_reduce
    rw [mul_add, J.θ_add _ (key x hx) _ (key y hy)]
  · beta_reduce
    rw [mul_left_comm, J.θ_mul _ (om_mem c) _ (key x hx), J.θ_Om]
  · beta_reduce
    rw [J.θ_ker _ (key x hx), shift_iff J, mem_iff K]
  · beta_reduce
    have e : ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
        algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l])) *
          P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
      rw [← IsScalarTower.algebraMap_apply, map_mul, act_zpow, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
        map_one, one_mul]
    rw [e, J.θ_mul _ (om_mem _) _ (act_mem g (key x hx)), J.θ_Om, J.θ_act g _ (key x hx)]
    rfl

end GlobalTheory.DeRhamSymbol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFamilyAdaptedToSeparatedFiltration
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_family_adapted_filtration :
    ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W) (d : ℕ), Module.Finite E ↥D → Module.finrank E ↥D = d → (∀ a, F (a + 1) ≤ F a) → (∀ x, ∃ a, x ∈ F a) → (∀ x, (∀ a, x ∈ F a) → x = 0) → ∃ (x : Fin d → W) (u : Fin d → ℤ), (∀ k, x k ∈ D ∧ x k ∈ F (u k)) ∧ ∀ (a : ℤ) (c : Fin d → E), (∀ k, u k ≠ a → c k = 0) → ∑ k, c k • x k ∈ F (a + 1) → ∀ k, c k = 0 := by
  intro E W _ _ _ D F d hfin hd hF hex hsep
  have anti : Antitone F := antitone_int_of_succ_le hF
  induction d generalizing D with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  | succ d ih =>
    have hne : D ≠ ⊥ := by
      rintro rfl
      simp at hd
    have hinh : ∃ z, D ≤ F z := by
      obtain ⟨s, hs⟩ : D.FG := Module.Finite.iff_fg.mp hfin
      choose g hg using hex
      obtain ⟨m, hm⟩ := (s.image g).bddBelow
      refine ⟨m, ?_⟩
      rw [← hs, Submodule.span_le]
      intro y hy
      exact anti (hm (by simpa using ⟨y, hy, rfl⟩)) (hg y)
    have hbdd : ∃ b : ℤ, ∀ z, D ≤ F z → z ≤ b := by
      obtain ⟨y, hyD, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have : ∃ b, y ∉ F b := by
        by_contra h
        push Not at h
        exact hy0 (hsep y h)
      obtain ⟨b, hb⟩ := this
      refine ⟨b, fun z hz => ?_⟩
      by_contra h
      exact hb (anti (not_le.mp h).le (hz hyD))
    obtain ⟨lo, hlo, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
    have hnot : ¬ D ≤ F (lo + 1) := fun h => by have := hmax _ h; omega
    obtain ⟨x0, hx0D, hx0F⟩ := SetLike.not_le_iff_exists.mp hnot
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hx0F
    have hx0 : x0 ∉ D ⊓ LinearMap.ker f := fun h => hf0 h.2
    have hfin' : Module.Finite E ↥(D ⊓ LinearMap.ker f) :=
      Submodule.finiteDimensional_of_le (inf_le_left : D ⊓ LinearMap.ker f ≤ D)
    have hsup : (D ⊓ LinearMap.ker f) ⊔ Submodule.span E {x0} = D := by
      apply le_antisymm
      · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hx0D)
      · intro y hy
        have h1 : y - (f y / f x0) • x0 ∈ D ⊓ LinearMap.ker f := by
          refine ⟨D.sub_mem hy (D.smul_mem _ hx0D), ?_⟩
          simp [LinearMap.mem_ker, div_mul_cancel₀ _ hf0]
        have h2 : (f y / f x0) • x0 ∈ Submodule.span E {x0} :=
          Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        simpa using Submodule.add_mem_sup h1 h2
    have hd' : Module.finrank E ↥(D ⊓ LinearMap.ker f) = d := by
      have hne0 : x0 ≠ 0 := fun h => hf0 (by simp [h])
      have := Submodule.finrank_sup_add_finrank_inf_eq (D ⊓ LinearMap.ker f) (Submodule.span E {x0})
      rw [hsup, hd, ((Submodule.disjoint_span_singleton' hne0).mpr hx0).eq_bot, finrank_bot,
        finrank_span_singleton hne0] at this
      omega
    obtain ⟨x, u, h1, h2⟩ := ih _ hfin' hd'
    refine ⟨Fin.cons x0 x, Fin.cons lo u, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ⟨hx0D, hlo hx0D⟩
      · exact ⟨(h1 j).1.1, (h1 j).2⟩
    · intro a c hc hs
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      have hc0 : c 0 = 0 := by
        by_cases ha : lo = a
        · subst ha
          have h3 := hf hs
          rw [LinearMap.mem_ker, map_add, map_sum, map_smul] at h3
          have h4 : ∑ j : Fin d, f (c j.succ • x j) = 0 :=
            Finset.sum_eq_zero fun j _ => by
              rw [map_smul, (LinearMap.mem_ker.mp (h1 j).1.2), smul_zero]
          rw [h4, add_zero, smul_eq_mul] at h3
          exact (mul_eq_zero.mp h3).resolve_right hf0
        · exact hc 0 ha
      rw [hc0, zero_smul, zero_add] at hs
      have h5 := h2 a (fun j => c j.succ) (fun j hj => hc j.succ hj) hs
      intro k
      exact Fin.cases hc0 h5 k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem actC_eq_σC (g : GQ l) (y : PadicComplex l) : AI.actC g y = Formalism.Per.σC g y := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (by apply GlobalTheory.RingIface.sigC_cont)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem actT_eq_σF (g : GQ l) (x : OCb l) : AI.actT g x = Formalism.Per.σF g x := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g x n y hy.symm
  have h3 : y' = Formalism.Per.σO g y := Subtype.ext ((h1.trans (actC_eq_σC AI g y)).trans
    (by symm; apply GlobalTheory.RingIface.sigO_coe))
  refine h2.trans ?_
  rw [h3]
  exact (GlobalTheory.AdicMaps.coeff_galois l g x n y hy.symm).symm

theorem ζ_add_pow (j n : ℕ) : AI.ζ (j + n) ^ l ^ n = AI.ζ j := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem coeff_εroot (j n : ℕ) : PreTilt.coeff n (AI.εroot j) =
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (j + n)) := by
  rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]

theorem untilt_εroot (j : ℕ) : (AI.εroot j).untilt = AI.ζ j := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ?_
  refine ⟨AI.ζ (j + n), (coeff_εroot AI j n).symm, ?_⟩
  rw [ζ_add_pow]

theorem isTheta_fontaineTheta : IsTheta AI (WittVector.fontaineTheta (OC l) l) := by
  have hprim : IsPrimitiveRoot (((frobeniusEquiv (OCb l) l).symm AI.ε).untilt) l := by
    have h : ((frobeniusEquiv (OCb l) l).symm AI.ε).untilt = AI.ζ 1 := untilt_εroot AI 1
    rw [h]
    have h1 : AI.ζ 1 ^ l = 1 := (AI.ζ_succ 0).trans AI.ζ_zero
    have h2 := IsPrimitiveRoot.orderOf (AI.ζ 1)
    rwa [orderOf_eq_prime h1 AI.ζ_one] at h2
  refine ⟨fun x y h => ?_, ?_, fun g a => ?_, fun a => ?_, fun j => ?_⟩
  · rw [← Ideal.Quotient.eq, WittVector.fontaineTheta_teichmuller, ← h]
    exact PreTilt.mk_untilt_eq_coeff_zero x
  · exact ReciprocityTheory.PGsh.Ainf.theta_surj l (OC l) (PadicComplexInt.integers l)
  · have e : AI.actW g a = Formalism.Per.σA g a := WittVector.ext fun n =>
      (actT_eq_σF AI g (a.coeff n)).trans (by symm; apply GlobalTheory.RingIface.sigA_coeff)
    rw [e, actC_eq_σC]
    exact (congrArg Subtype.val (GlobalTheory.RingBasics.θ_σA g a)).trans (by apply GlobalTheory.RingIface.sigO_coe)
  · rw [← RingHom.mem_ker,
      ReciprocityTheory.PGsh.Ainf.ker_theta l (OC l) (PadicComplexInt.integers l) AI.ε hprim,
      Ideal.mem_span_singleton]
    rfl
  · rw [WittVector.fontaineTheta_teichmuller, untilt_εroot]

theorem exists_isTheta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    ∃ θ : Ainf l →+* OC l, IsTheta AI θ :=
  fun _ _ _ AI => ⟨_, isTheta_fontaineTheta AI⟩

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenerator
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LineLattice

theorem exists_generator {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V) [Module.Free O T]
    (hsp : Submodule.span LL (T : Set V) = ⊤) (h1 : Module.finrank LL V = 1) :
    ∃ v : V, v ≠ 0 ∧ T = Submodule.span O {v} := by
  classical
  have hfin : Module.Finite LL V := Module.finite_of_finrank_eq_succ h1
  let b := Module.Free.chooseBasis O T
  have hli : LinearIndependent O (fun i => (b i : V)) :=
    b.linearIndependent.map' T.subtype T.ker_subtype
  have hli' : LinearIndependent LL (fun i => (b i : V)) :=
    (LinearIndependent.iff_fractionRing O LL).1 hli
  have hT : T = Submodule.span O (Set.range fun i => (b i : V)) := by
    have h := congrArg (Submodule.map T.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h.symm
  have hfi : Finite (Module.Free.ChooseBasisIndex O T) := hli'.finite
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex O T)
  have hc := hli'.fintype_card_le_finrank
  rw [h1] at hc
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) :=
    Fintype.card_le_one_iff_subsingleton.1 hc
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex O T) with he | ⟨⟨i⟩⟩
  · exfalso
    rw [Set.range_eq_empty, Submodule.span_empty] at hT
    have hb : Submodule.span LL (T : Set V) = ⊥ := by
      rw [hT]; simp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h1
    exact bot_ne_top (hb.symm.trans hsp)
  · refine ⟨b i, hli.ne_zero i, ?_⟩
    refine hT.trans ?_
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      rw [Subsingleton.elim j i]; rfl
    · rintro rfl
      exact ⟨i, rfl⟩

theorem lattice_rank_one {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [IsDomain O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (h1 : Module.finrank LL V = 1) :
    (∃ e : LL ≃ₗ[LL] V, ∀ x : LL, e x ∈ L.T ↔ x ∈ Set.range (algebraMap O LL)) ∧
    ∀ a : O, a ≠ 0 →
      Nonempty (↥(Submodule.torsionBy O (V ⧸ L.T) a) ≃ₗ[O] (O ⧸ Ideal.span {a})) := by
  haveI := L.free
  obtain ⟨v, hv, hT⟩ := exists_generator L.T L.span h1
  have hsurj : ∀ w : V, ∃ c : LL, c • v = w := (finrank_eq_one_iff_of_nonzero' v hv).1 h1
  have hmem : ∀ x : LL, x • v ∈ L.T ↔ x ∈ Set.range (algebraMap O LL) := by
    intro x
    rw [hT, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← algebraMap_smul LL c v] at hc
      exact smul_left_injective LL hv hc
    · rintro ⟨c, rfl⟩
      exact ⟨c, (algebraMap_smul LL c v).symm⟩
  refine ⟨⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton LL V v)
    ⟨smul_left_injective LL hv, hsurj⟩, hmem⟩, ?_⟩
  intro a ha
  have ha' : algebraMap O LL a ≠ 0 := by
    simpa using ha
  have hx : L.T.mkQ ((algebraMap O LL a)⁻¹ • v) ∈ Submodule.torsionBy O (V ⧸ L.T) a := by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem,
      mul_inv_cancel₀ ha']
    exact ⟨1, map_one _⟩
  let f : O →ₗ[O] Submodule.torsionBy O (V ⧸ L.T) a :=
    LinearMap.toSpanSingleton O _ ⟨_, hx⟩
  have hf : ∀ c : O, (f c : V ⧸ L.T) =
      L.T.mkQ ((algebraMap O LL c * (algebraMap O LL a)⁻¹) • v) := by
    intro c
    rw [← smul_smul, algebraMap_smul, map_smul]
    rfl
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := L.T.mkQ_surjective y
    obtain ⟨x, rfl⟩ := hsurj w
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, Subtype.ext ?_⟩
    rw [hf, hc, mul_comm (algebraMap O LL a) x, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  have hk : LinearMap.ker f = Ideal.span {a} := by
    ext c
    rw [LinearMap.mem_ker, Subtype.ext_iff, hf, Ideal.mem_span_singleton']
    rw [Submodule.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, IsFractionRing.injective O LL ?_⟩
      rw [map_mul, hd, mul_assoc, inv_mul_cancel₀ ha', mul_one]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      rw [map_mul, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  exact ⟨(f.quotKerEquivOfSurjective hfs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

end GlobalTheory.LineLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemGKChiPowNeOne
section
namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

private lemma norm_one_add_prime_padic (l : ℕ) [Fact l.Prime] : ‖(1 : ℚ_[l]) + l‖ = 1 := by
  have h1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hne : ‖(1 : ℚ_[l])‖ ≠ ‖(l : ℚ_[l])‖ := by rw [norm_one]; exact ne_of_gt h1
  first
  | rw [padicNormE.add_eq_max_of_ne hne, norm_one]; exact max_eq_left h1.le
  | rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]; exact max_eq_left h1.le

private lemma zmod_pow_ne_one_of_pow_mod_ne_one (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) :
    ((1 : ℚ_[l]) + l) ^ n ≠ 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have key : (1 + l) ^ n ≠ 1 := (Nat.one_lt_pow (by omega) (by omega)).ne'
  intro h
  apply key
  exact_mod_cast h

theorem exists_mem_GK_chi_pow_ne_one : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ →
    ∀ (K : FinExt l) (e : ℕ), 0 < e → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
  intro l _ χ hχ K e he

  obtain ⟨σ, -, hσ⟩ := exists_chi_eq K χ hχ _ (norm_one_add_prime_padic l)
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2

  let f : ℕ → (↥K.1 →ₐ[ℚ_[l]] Om l) := fun n =>
    (AlgEquiv.toAlgHom (σ ^ n : Om l ≃ₐ[ℚ_[l]] Om l)).comp (IntermediateField.val K.1)
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f

  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
    intro a b hab hfab
    refine ⟨σ ^ (b - a), ?_, ?_⟩
    · unfold GK
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (σ ^ a) x = (σ ^ b) x :=
        congrArg (fun φ : ↥K.1 →ₐ[ℚ_[l]] Om l => φ ⟨x, hx⟩) hfab
      have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hb, AlgEquiv.mul_apply] at h1
      exact ((σ ^ a).injective h1).symm
    · rw [map_pow, Units.val_pow_eq_pow_val, hσ, ← pow_mul]
      exact zmod_pow_ne_one_of_pow_mod_ne_one l _ (Nat.mul_pos (by omega) he)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij
  · exact key j i h hfij.symm

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinfStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusIntegrality_wittTilt_ainf : ∀ (l : ℕ) [Fact l.Prime] (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (WCb l)) (S : Matrix p p (Ainf l)) (S' : Matrix q q (Ainf l)) (Y : Matrix p q (Ainf l)), Z.map (frobW l) = S.map (inclW l) * Z * S'.map (inclW l) + Y.map (inclW l) → ∀ a b, Z a b ∈ Set.range (inclW l) := by
  first | exact @GlobalTheory.FrobInt.frobenius_integrality | exact GlobalTheory.FrobInt.frobenius_integrality | (intros; apply GlobalTheory.FrobInt.frobenius_integrality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionSubMemSpanPowSuccStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaAction_sub_mem_span_pow_succ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ g ∈ W.GKs, ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k, W.γA (W.resΓ g) a - a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  first | exact @GlobalTheory.GamFilt.gamma_sub_mem_pow_succ | exact GlobalTheory.GamFilt.gamma_sub_mem_pow_succ | (intros; apply GlobalTheory.GamFilt.gamma_sub_mem_pow_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRingStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_tiltField_and_valuationRing : ∀ (l : ℕ) [Fact l.Prime], IsAlgClosed (Cb l) ∧ ValuationRing (OCb l) := by
  first | exact @GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing | exact GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing | (intros; apply GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFilStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unramified_of_frobenius_iterate_fixed_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c → (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) → ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  first | exact @GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt | exact GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt | (intros; apply GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt <;> assumption)
end

