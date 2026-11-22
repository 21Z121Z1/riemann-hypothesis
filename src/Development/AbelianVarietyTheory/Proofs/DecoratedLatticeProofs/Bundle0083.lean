import Mathlib
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.Bundle0028
import Formalism.LocalToGlobal.Columns.Bundle0015
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStepG
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FnOfMapInjective
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Core

theorem fnOf_map_injective {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (sh : ι → ℤ) (s : K →+* ℂ) {F F' : MvPolynomial (ι × Fin n × Fin n) K}
    (h : fnOf G sh 1 (MvPolynomial.map s F) = fnOf G sh 1 (MvPolynomial.map s F')) : F = F' :=
  MvPolynomial.map_injective s s.injective
    (Formalism.L2.Col.fnOf_injective G sh 1 (fun _ => by simp)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}) h)

theorem exists_ptVal_at (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K) (x : (D.fm u).ptLat.V)
    (c : (D.fm u).clsP) : ∃ F : VV D.what₂.LL (sgT u),
      W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL F.1) := by
  obtain ⟨P, hP, hv⟩ := ((W.rat _).1 ⟨x, rfl⟩).2 c
  have e : Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) = Formalism.L2.Col.RatSpanG D.what₂.embLL (D.fm u).sg :=
    Formalism.L2.Col.RatSpanG_shW D.what₂.embLL (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
  have hP' : P ∈ Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) := by rw [e]; exact hP
  obtain ⟨F, hF, rfl⟩ := Formalism.L2.Col.exists_VV_of_mem_RatSpanG _ _ hP'
  exact ⟨⟨F, hF⟩, hv⟩

theorem exists_ptVal : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K), ∃ val : (D.fm u).ptLat.V →ₗ[D.what₂.LL] ((D.fm u).clsP → VV D.what₂.LL (sgT u)), (∀ x c, W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (val x c).1)) := by
  intro D u K W
  choose val hval using exists_ptVal_at D u K W
  refine ⟨{ toFun := val, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hval⟩
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    rw [← hval, Pi.add_apply, Submodule.coe_add, map_add, map_add, map_add, map_add, ← hval, ← hval, Pi.add_apply]
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    have e : MvPolynomial.map D.what₂.embLL (a • (val x c).1) =
        D.what₂.embLL a • MvPolynomial.map D.what₂.embLL (val x c).1 := by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    rw [← hval, RingHom.id_apply, Pi.smul_apply, Submodule.coe_smul, e, LinearMap.map_smul, ← hval,
      LinearMap.map_smulₛₗ, LinearEquiv.map_smul, Pi.smul_apply]

end GlobalTheory.Core
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfSqrtDetTwist
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section

namespace GlobalTheory.CoverDS.TwistTypes

variable {p q : ℕ}

theorem sum_rhoNC (lam : Ix p q → ℚ) : ∑ a, rhoNC lam a = 0 := by
  have symm : ∀ a b : Ix p q, sameBlock a b ↔ sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  have k1 : ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => ¬ sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  have k2 : ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam b < lam a).card : ℚ) =
      ∑ a, ((Finset.univ.filter fun b => sameBlock a b ∧ lam a < lam b).card : ℚ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [symm a b]
  simp only [rhoNC, Finset.sum_sub_distrib, ← Finset.sum_div, k1, k2, sub_self, zero_div]

theorem normSq_add_half (lam : Ix p q → ℚ) :
    normSq (fun a => lam a + 1 / 2) =
      normSq lam + ∑ a, (lam a + 1 / 2) - (Fintype.card (Ix p q) : ℚ) / 4 := by
  have e : ∀ a, (lam a + 1 / 2) ^ 2 = lam a ^ 2 + (lam a + 1 / 2) - 1 / 4 := fun a => by ring
  simp only [normSq, e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem casimir_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) :
    casimir (Cover.twAct act) v = casimir act v - act 1 v + ((Fintype.card (Ix p q) : ℂ) / 4) • v := by
  have hterm : ∀ a b, Cover.twAct act (Eab a b) (Cover.twAct act (Eab b a) v) =
      act (Eab a b) (act (Eab b a) v) - if a = b then act (Eab a a) v - (1 / 4 : ℂ) • v else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [Cover.twAct_apply, if_true, Eab, Matrix.trace_single_eq_same, map_sub, map_smul]
      module
    · simp [Cover.twAct_apply, hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab,
        Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)]
  have h1 : act 1 v = ∑ a, act (Eab a a) v := by
    rw [← Matrix.sum_single_one, map_sum, LinearMap.sum_apply]
    rfl
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h1, Finset.sum_const, Finset.card_univ]
  module

theorem hwSub_twAct (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) :
    hwSub (Cover.twAct act) μ = hwSub act fun a => μ a + 1 / 2 := by
  ext v
  by_cases hv : v = 0
  · subst hv
    exact iff_of_true (Submodule.zero_mem _) (Submodule.zero_mem _)
  · exact ⟨fun h => ((Cover.isHW_twAct act μ v).1 ⟨hv, h⟩).2, fun h => ((Cover.isHW_twAct act μ v).2 ⟨hv, h⟩).2⟩

theorem sum_of_inCone {lam μ : Ix p q → ℚ} (h : InCone lam μ) : ∑ a, μ a = ∑ a, lam a := by
  obtain ⟨m, -, rfl⟩ := h
  have e : ∑ c, ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib, e, blattner, sum_rhoNC, add_zero]

theorem inCone_add {lam μ : Ix p q → ℚ} (c : ℚ) (h : InCone lam fun a => μ a - c) :
    InCone (fun a => lam a + c) μ := by
  obtain ⟨m, hm, hμ⟩ := h
  refine ⟨m, fun a b hab => add_lt_add_left (hm a b hab) c, funext fun a => ?_⟩
  have := congrFun hμ a
  rw [Cover.blattner_add]
  simp only at this ⊢
  linarith

theorem hasTypes_of_twist (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ)
    (h : HasTypes (Cover.twist R) lam) : HasTypes R fun a => lam a + 1 / 2 := by
  have h1 : Module.finrank ℂ ↥(hwSub (Cover.twAct R.HK.act) (blattner lam)) = 1 := h.1
  have h2 : ∀ v, casimir (Cover.twAct R.HK.act) v = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • v := h.2.1
  have h3 : ∀ (μ : Ix p q → ℚ) v, IsHW (Cover.twAct R.HK.act) μ v → InCone lam μ := h.2.2
  have hcone : ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (fun a => lam a + 1 / 2) μ := fun μ v hv =>
    inCone_add _ (h3 _ v ((Cover.isHW_twAct _ _ v).2 (by simpa only [sub_add_cancel] using hv)))
  refine ⟨by rwa [Cover.blattner_add, ← hwSub_twAct], fun v => ?_, hcone⟩
  set c : ℂ := ((∑ a, (lam a + 1 / 2) : ℚ) : ℂ) with hc
  have htop : LinearMap.ker (R.HK.act 1 - c • LinearMap.id) = ⊤ := by
    refine GlobalTheory.T.kStable_submodule_eq_top_of_highestWeight_le p q R.HK _ (fun X _ w hw => ?_) fun μ w hw => ?_
    · have e := congrArg (fun f : Module.End ℂ R.HK.V => f w) (R.HK.lie X 1)
      simp only [Matrix.mul_one, Matrix.one_mul, sub_self, map_zero, LinearMap.zero_apply, LinearMap.sub_apply,
        Module.End.mul_apply] at e
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw ⊢
      rw [← sub_eq_zero.1 e.symm, hw, map_smul]
    · by_cases h0 : w = 0
      · rw [h0]
        exact Submodule.zero_mem _
      have e := sum_of_inCone (hcone μ w ⟨h0, hw⟩)
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      rw [hc, ← e, ← Matrix.sum_single_one, map_sum, LinearMap.sum_apply, Rat.cast_sum, Finset.sum_smul]
      exact Finset.sum_congr rfl fun a _ => ((mem_hwSub_iff _ _ _).1 hw).1 a
  have hv : R.HK.act 1 v = c • v := by
    simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      using Submodule.eq_top_iff'.1 htop v
  have e := casimir_twAct R.HK.act v
  rw [h2, hv] at e
  rw [normSq_add_half, Rat.cast_sub, Rat.cast_sub, Rat.cast_add, ← hc]
  rw [Rat.cast_sub] at e
  push_cast
  linear_combination (norm := module) -e

end GlobalTheory.CoverDS.TwistTypes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HighestWeightLineOfKTypeMultiplicityOne
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.RealPar.HwLine

open GlobalTheory.RealPar.HwGen (PosRoot mono drop drop_cons mono_weight mono_stable weight_of_mem_span cnt)

variable {p q n : ℕ}

def ht : Ix p q → ℝ := Sum.elim (fun i => -(i : ℝ)) (fun j => -(j : ℝ))

theorem ht_lt {a b : Ix p q} (h : posC a b) : ht b < ht a := by
  rcases a with i | i <;> rcases b with j | j <;> simp [posC] at h <;> simp [ht] <;> exact_mod_cast h

theorem ht_drop_cons (r : PosRoot p q) (l : List (PosRoot p q)) :
    ∑ x, ht x * drop l x < ∑ x, ht x * drop (r :: l) x := by
  have hr := ht_lt r.2
  simp only [drop_cons, mul_add, Finset.sum_add_distrib, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

theorem ht_drop_nonneg (l : List (PosRoot p q)) : 0 ≤ ∑ x, ht x * drop l x := by
  induction l with
  | nil => simp [drop, cnt]
  | cons r l ih => exact (lt_of_le_of_lt ih (ht_drop_cons r l)).le

theorem eq_smul_of_mem_span {V : Type*} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V} (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) {w : V}
    (hw : w ∈ Submodule.span ℂ (Set.range (mono act v))) (hwt : ∀ a, act (Eab a a) w = ((μ a : ℚ) : ℂ) • w) :
    ∃ c : ℂ, c • v = w := by
  classical
  let m' : {l : List (PosRoot p q) // l ≠ []} → V := fun l => mono act v l.1
  have hle : Submodule.span ℂ (Set.range (mono act v)) ≤
      Submodule.span ℂ {v} ⊔ Submodule.span ℂ (Set.range m') := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    cases l with
    | nil => exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    | cons r l =>
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨r :: l, List.cons_ne_nil r l⟩, rfl⟩)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hw)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  by_contra hne
  have hz0 : z ≠ 0 := fun h0 => hne (by rw [h0, add_zero])
  have hzw : ∀ a, act (Eab a a) z = ((μ a : ℚ) : ℂ) • z := by
    intro a
    have h1 := hwt a
    rw [map_add, map_smul, hv a, smul_add, smul_comm c] at h1
    exact add_left_cancel h1
  obtain ⟨⟨l, hl0⟩, hl⟩ := weight_of_mem_span (fun a => act (Eab a a)) m'
    (fun l a => ((((μ a : ℚ) : ℝ) - drop l.1 a : ℝ) : ℂ)) (fun l a => mono_weight h hv l.1 a)
    (fun a => ((μ a : ℚ) : ℂ)) z hz hz0 hzw
  have hd : ∀ a, drop l a = 0 := by
    intro a
    have h1 : ((((μ a : ℚ) : ℝ) - drop l a : ℝ) : ℂ) = (((μ a : ℚ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_ratCast]; exact congrFun hl a
    have h2 := Complex.ofReal_injective h1
    linarith
  obtain ⟨r, l', rfl⟩ := List.exists_cons_of_ne_nil hl0
  have h3 := ht_drop_cons r l'
  have h4 := ht_drop_nonneg l'
  simp only [hd, mul_zero, Finset.sum_const_zero] at h3
  linarith

variable {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} {T : GrpData p q} (R : DSRep T)
  {σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)}

theorem isKTypeOf_span (h : BlockOrd e ε) (hσ : Factors R.U e σ) (μ : Ix p q → ℚ) {v : R.HK.V}
    (hv : Formalism.BasicNotions.TH.IsHW R.HK.act μ v) :
    IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) ((Submodule.span ℂ (Set.range (mono R.HK.act v))).map R.ι) := by
  classical
  set W := Submodule.span ℂ (Set.range (mono R.HK.act v)) with hWdef
  have hlie : IsLieAct R.HK.act := R.HK.lie
  have hv0 : v ≠ 0 := hv.1
  obtain ⟨hvw, hvr⟩ := (mem_hwSub R.HK.act μ v).1 hv.2
  have hvW : v ∈ W := Submodule.subset_span ⟨[], rfl⟩
  have hWst : KStable R.HK.act W := mono_stable hlie hvw hvr
  have hWle : ∀ W' : Submodule ℂ R.HK.V, v ∈ W' → KStable R.HK.act W' → W ≤ W' := by
    intro W' hvW' hW'
    rw [hWdef, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact hvW'
    | cons r l ih => exact hW' _ (HwGen.isKC_Eab r.2) _ ih
  obtain ⟨W0, hW0f, hvW0, hW0s⟩ := R.HK.kfin v
  have := hW0f
  have hWf : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (hWle W0 hvW0 hW0s)
  have hι : Function.Injective R.ι := R.ι_inj
  have hKs : IsKStableOn ε σ (W.map R.ι) := isKStableOn_of_kStable p q n e ε T R σ h hσ W hWf hWst
  refine ⟨inferInstance, hKs, ?_, ?_, ?_⟩
  · intro S' hS'le hS'
    have hS'f : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'le
    have : CompleteSpace S' := FiniteDimensional.complete ℂ S'
    have hCK : IsKStableOn ε σ (S'ᗮ ⊓ W.map R.ι) := fun g hg x hx =>
      Submodule.mem_inf.2 ⟨kstable_orthogonal R h hσ hS' g hg x (Submodule.mem_inf.1 hx).1,
        hKs g hg x (Submodule.mem_inf.1 hx).2⟩
    have hCf : FiniteDimensional ℂ ↥(S'ᗮ ⊓ W.map R.ι) := Submodule.finiteDimensional_of_le inf_le_right
    obtain ⟨-, hS0map, hS0st⟩ := comap_kstable R h hσ hS'f hS'
    obtain ⟨-, -, hC0st⟩ := comap_kstable R h hσ hCf hCK
    have hdisj : ∀ x, x ∈ S'.comap R.ι → x ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι → x = 0 := by
      intro x hx1 hx2
      apply hι
      rw [map_zero]
      have hbot := Submodule.inf_orthogonal_eq_bot S'
      rw [Submodule.eq_bot_iff] at hbot
      exact hbot _ (Submodule.mem_inf.2 ⟨hx1, (Submodule.mem_inf.1 hx2).1⟩)
    have hsup : S' ⊔ S'ᗮ ⊓ W.map R.ι = W.map R.ι :=
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hS'le
    have hιv : R.ι v ∈ S' ⊔ S'ᗮ ⊓ W.map R.ι := hsup.symm ▸ Submodule.mem_map_of_mem hvW
    obtain ⟨s', hs', c', hc', hsc⟩ := Submodule.mem_sup.1 hιv
    obtain ⟨s, hsW, rfl⟩ := Submodule.mem_map.1 (hS'le hs')
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hc').2
    have hs : s ∈ S'.comap R.ι := Submodule.mem_comap.2 hs'
    have ht : t ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι := Submodule.mem_comap.2 hc'
    have hvst : v = s + t := hι (by rw [map_add]; exact hsc.symm)
    have hsw : ∀ a, R.HK.act (Eab a a) s = ((μ a : ℚ) : ℂ) • s := by
      intro a
      have hK : IsKC (Eab a a) := isKC_Eab ((h.sameBlock_iff a a).2 rfl)
      have e1 := hvw a
      rw [hvst, map_add, smul_add] at e1
      have hm1 : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s ∈ S'.comap R.ι :=
        Submodule.sub_mem _ (hS0st _ hK _ hs) (Submodule.smul_mem _ _ hs)
      have hm2 : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι := by
        have he : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s =
            ((μ a : ℚ) : ℂ) • t - R.HK.act (Eab a a) t := by
          rw [sub_eq_sub_iff_add_eq_add, e1]; abel
        rw [he]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ht) (hC0st _ hK _ ht)
      exact sub_eq_zero.1 (hdisj _ hm1 hm2)
    obtain ⟨c, hc⟩ := eq_smul_of_mem_span hlie hvw hsW hsw
    by_cases hc0 : c = 0
    · left
      have htv : t = v := by rw [hvst, ← hc, hc0, zero_smul, zero_add]
      have hWC : W ≤ (S'ᗮ ⊓ W.map R.ι).comap R.ι := hWle _ (htv ▸ ht) hC0st
      have hS0bot : S'.comap R.ι = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.1 (hS'le (Submodule.mem_comap.1 hx))
        obtain rfl : y = x := hι hyx
        exact hdisj y hx (hWC hyW)
      rw [← hS0map, hS0bot, Submodule.map_bot]
    · right
      have hvS0 : v ∈ S'.comap R.ι := by
        have hv' : v = c⁻¹ • s := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hv']
        exact Submodule.smul_mem _ _ hs
      have hWS : W ≤ S'.comap R.ι := hWle _ hvS0 hS0st
      refine le_antisymm hS'le ?_
      calc W.map R.ι ≤ (S'.comap R.ι).map R.ι := Submodule.map_mono hWS
        _ = S' := hS0map
  · refine ⟨R.ι v, Submodule.mem_map_of_mem hvW, fun h0 => hv0 (hι (by rw [h0, map_zero])), ?_⟩
    refine (TorusWt.isWtOn_iff p q n e ε T R σ h hσ _ v).2 fun a => ?_
    simp only [hvw a, Equiv.symm_apply_apply, Complex.ofReal_ratCast]
  · intro ν x hx hx0 hxw
    obtain ⟨w, hwW, rfl⟩ := Submodule.mem_map.1 hx
    have hw0 : w ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
    have hww := (TorusWt.isWtOn_iff p q n e ε T R σ h hσ ν w).1 hxw
    obtain ⟨l, hl⟩ := weight_of_mem_span (fun a => R.HK.act (Eab a a)) (mono R.HK.act v)
      (fun l a => ((((μ a : ℚ) : ℝ) - drop l a : ℝ) : ℂ)) (fun l a => mono_weight hlie hvw l a)
      (fun a => ((ν (e a) : ℝ) : ℂ)) w hwW hw0 hww
    have hl' : ∀ a, ((μ a : ℚ) : ℝ) - drop l a = ν (e a) :=
      fun a => Complex.ofReal_injective (congrFun hl a)
    have key : ∀ x, ∑ i, ∑ j, (cnt l (e.symm i) (e.symm j) : ℝ) * Formalism.REAL.root i j (e x) = drop l x := by
      intro x
      rw [← Equiv.sum_comp e]
      refine (Finset.sum_congr rfl fun a _ => (Equiv.sum_comp e _).symm).trans ?_
      simp only [Equiv.symm_apply_apply, root_apply e, drop]
    refine ⟨fun i j => cnt l (e.symm i) (e.symm j), fun i j hij => ?_, ?_⟩
    · have := (h.posC_iff _ _).1 (HwGen.posC_of_cnt l _ _ hij)
      simpa using this
    · funext k
      obtain ⟨x, rfl⟩ := e.surjective k
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply]
      linarith [key x, hl' x]

theorem finrank_hwSub_eq_one : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ μ : Ix p q → ℚ, (∃ S, IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S) → (∀ S S', IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S → IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S' → S = S') → Module.finrank ℂ ↥(hwSub R.HK.act μ) = 1 := by
  intro p q n e ε T R σ h hσ μ hex huniq
  classical
  obtain ⟨S, hS⟩ := hex
  obtain ⟨v, hv⟩ := isHW_of_isKTypeOf R h hσ μ hS
  have hlie : IsLieAct R.HK.act := R.HK.lie
  obtain ⟨hvw, -⟩ := (mem_hwSub R.HK.act μ v).1 hv.2
  rw [finrank_eq_one_iff_of_nonzero' (⟨v, hv.2⟩ : hwSub R.HK.act μ)
    (fun h0 => hv.1 (congrArg Subtype.val h0))]
  rintro ⟨w, hw⟩
  by_cases hw0 : w = 0
  · exact ⟨0, Subtype.ext (by simp [hw0])⟩
  have hwHW : Formalism.BasicNotions.TH.IsHW R.HK.act μ w := ⟨hw0, hw⟩
  obtain ⟨hww, -⟩ := (mem_hwSub R.HK.act μ w).1 hw
  have hEq := huniq _ _ (isKTypeOf_span R h hσ μ hv) (isKTypeOf_span R h hσ μ hwHW)
  have hιw : R.ι w ∈ (Submodule.span ℂ (Set.range (mono R.HK.act v))).map R.ι := by
    rw [hEq]; exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨[], rfl⟩)
  obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 hιw
  obtain rfl : y = w := R.ι_inj hyw
  obtain ⟨c, hc⟩ := eq_smul_of_mem_span hlie hvw hy hww
  exact ⟨c, Subtype.ext hc⟩

end GlobalTheory.RealPar.HwLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InConeOfKTypesAbove
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverCone

theorem inCone_of_kTypesAbove : GlobalTheory.Dec.KTypesAbove → ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (blockPar P e) μ := by
  intro KTA p q n e P T R σ hb hσ hds μ v hv
  obtain ⟨S, hS⟩ := GlobalTheory.RealPar.isKTypeOf_of_isHW R hb hσ μ ⟨v, hv⟩
  obtain ⟨c, hc, hμ⟩ := KTA n P.sgn P.lam R.U.H σ P.hc hds _ S hS
  refine ⟨fun a b => c (e a) (e b), fun a b hab => ?_, ?_⟩
  · have h2 := P.hc.1 (hc _ _ hab)
    rw [← GlobalTheory.RealPar.ratEntry_cast, ← GlobalTheory.RealPar.ratEntry_cast] at h2
    exact_mod_cast h2
  · funext x
    apply Rat.cast_injective (α := ℝ)
    have hx := congrFun hμ (e x)
    simp only [Equiv.symm_apply_apply] at hx
    push_cast
    rw [hx, GlobalTheory.RealPar.blattner_eq P hb (lam := GlobalTheory.RealPar.blockPar P e) (fun a => GlobalTheory.RealPar.ratEntry_cast P (e a)) x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.RealPar.root_apply]
    split_ifs <;> simp

end GlobalTheory.CoverCone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryFiniteDatumBoundedLevelSize
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.EntryDatumS

open GlobalTheory.ColNorms.EntryDatum

theorem smallDatum_xiEntry_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.unfoldedEntry_typePrime_support_period_size
  refine ⟨C, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p' => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hg : ∀ i, Pr.g i = N.g i := H.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (p : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j p P x
    have hP := h1 P.1 P.2
    unfold frsF
    rw [dif_pos hP]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ p.deco ⟨P.1, hP⟩).1 x
  have key := smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 p'.deco.1 p'.deco.2 (frsF sel mu p) (frsF sel mu p')
    (hfr p) (hfr p') (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P => XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) _
    (hC CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be)
  have e : ∏ P : rowSG Pr sel mu, (Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2) =
      ((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    rw [Finset.prod_pow, ← Nat.cast_prod, h4, hg 0, hg 1]
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [e] at key
  exact key

end GlobalTheory.Core.Ht2.EntryDatumS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHarishChandraParamRevEqWeylWeightTopStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_harishChandraParam_rev_eq_weylWeight_top : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → ∀ τ (i : Fin D.sp.X'.rank), -M.lam τ (Fin.rev i) = (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℝ) + ((rhoVec D.sp.X'.rank i : ℚ) : ℝ) := by
  first | exact @GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq | exact GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq | (intros; apply GlobalTheory.Core.Rk.TopParam.neg_lam_rev_eq <;> assumption)
end

