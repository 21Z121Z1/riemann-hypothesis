import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0369
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureCrtCombine
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

attribute [local instance] CategoryTheory.Hom.group CategoryTheory.Hom.commGroup

namespace GlobalTheory.RealMult.LevelComb

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}}

def actHom (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) :
    𝓞 F →+ Additive (T ⟶ X.A) :=
  AddMonoidHom.mk' (fun c ↦ Additive.ofMul (u ≫ z ≫ X.rm.act c)) (fun a b ↦ by
    simp only [X.rm.add, comp_mul]; rfl)

theorem comp_act_add (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (a b : 𝓞 F) :
    u ≫ z ≫ X.rm.act (a + b) = (u ≫ z ≫ X.rm.act a) * (u ≫ z ≫ X.rm.act b) := by
  simp only [X.rm.add, comp_mul]

theorem comp_act_zsmul (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (n : ℤ)
    (c : 𝓞 F) : u ≫ z ≫ X.rm.act (n • c) = (u ≫ z ≫ X.rm.act c) ^ n := by
  have h := map_zsmul (actHom X u z) n c
  exact congrArg Additive.toMul h

theorem comp_pow_act (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (m : ℕ)
    (c : 𝓞 F) : u ≫ (z ^ m) ≫ X.rm.act c = (u ≫ z ≫ X.rm.act c) ^ m := by
  haveI := X.rm.hom c
  rw [pow_comp, comp_pow]

end GlobalTheory.RealMult.LevelComb

open GlobalTheory.RealMult.LevelComb in

theorem GlobalTheory.RealMult.Obj.Level.comb : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, Nat.Coprime N N' → ∀ (β : X.Level N) (β' : X.Level N'),
    ∃ ξ : X.Level (N * N'), (∀ i, ξ.pt i ^ N' = β.pt i) ∧ ∀ i, ξ.pt i ^ N = β'.pt i := by
  intro F _ _ 𝔠 S X N N' hc β β'
  obtain ⟨p, q, hpq⟩ : IsCoprime (N : ℤ) (N' : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  let pt : Fin 2 → (𝟙_ (Over S) ⟶ X.A) := fun i ↦ β.pt i ^ q * β'.pt i ^ p
  have h1 : ∀ i, pt i ^ N' = β.pt i := by
    intro i
    have hb : β.pt i ^ (q * (N' : ℤ)) = β.pt i := by
      rw [show q * (N' : ℤ) = 1 - (N : ℤ) * p by linarith, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
        β.tors i, one_zpow, inv_one, _root_.mul_one]
    have hb' : β'.pt i ^ (p * (N' : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, β'.tors i, one_zpow]
    show (β.pt i ^ q * β'.pt i ^ p) ^ N' = β.pt i
    rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, hb, hb', _root_.mul_one]
  have h2 : ∀ i, pt i ^ N = β'.pt i := by
    intro i
    have hb : β'.pt i ^ (p * (N : ℤ)) = β'.pt i := by
      rw [show p * (N : ℤ) = 1 - (N' : ℤ) * q by linarith, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
        β'.tors i, one_zpow, inv_one, _root_.mul_one]
    have hb' : β.pt i ^ (q * (N : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, β.tors i, one_zpow]
    show (β.pt i ^ q * β'.pt i ^ p) ^ N = β'.pt i
    rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, hb, hb', _root_.one_mul]
  refine ⟨{ pt := pt, tors := ?_, inj := ?_, surj := ?_ }, h1, h2⟩
  · intro i
    rw [mul_comm, pow_mul, h1, β.tors]
  · intro Ω _ _ t a b h
    set u := toUnit (Over.mk t)
    have hβ : (u ≫ β.pt 0 ≫ X.rm.act a) * (u ≫ β.pt 1 ≫ X.rm.act b) = 1 := by
      rw [← h1, ← h1, comp_pow_act, comp_pow_act, ← mul_pow, h, one_pow]
    have hβ' : (u ≫ β'.pt 0 ≫ X.rm.act a) * (u ≫ β'.pt 1 ≫ X.rm.act b) = 1 := by
      rw [← h2, ← h2, comp_pow_act, comp_pow_act, ← mul_pow, h, one_pow]
    obtain ⟨ha, hb⟩ := β.inj Ω t a b hβ
    obtain ⟨ha', hb'⟩ := β'.inj Ω t a b hβ'
    have hco : IsCoprime ((N : 𝓞 F)) ((N' : 𝓞 F)) := by
      simpa using (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 F))
    rw [Nat.cast_mul]
    exact ⟨hco.mul_dvd ha ha', hco.mul_dvd hb hb'⟩
  · intro Ω _ _ t y hy
    set u := toUnit (Over.mk t)
    have hy1 : (y ^ N') ^ N = 1 := by rw [← pow_mul, mul_comm, hy]
    have hy2 : (y ^ N) ^ N' = 1 := by rw [← pow_mul, hy]
    obtain ⟨a, b, hab⟩ := β.surj Ω t (y ^ N') hy1
    obtain ⟨a', b', hab'⟩ := β'.surj Ω t (y ^ N) hy2
    rw [← h1, ← h1, comp_pow_act, comp_pow_act] at hab
    rw [← h2, ← h2, comp_pow_act, comp_pow_act] at hab'
    refine ⟨((N : ℤ) * p) • a' + ((N' : ℤ) * q) • a, ((N : ℤ) * p) • b' + ((N' : ℤ) * q) • b, ?_⟩
    rw [comp_act_add, comp_act_add, comp_act_zsmul, comp_act_zsmul, comp_act_zsmul, comp_act_zsmul]
    have hy0 : y = y ^ ((N : ℤ) * p + (N' : ℤ) * q) := by
      rw [show (N : ℤ) * p + (N' : ℤ) * q = 1 by linarith, zpow_one]
    rw [hy0, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hab, hab', mul_zpow, mul_zpow,
      zpow_mul, zpow_mul, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
    exact mul_mul_mul_comm _ _ _ _

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructurePowerSplit
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult.LevelPow

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}}

theorem comp_act_natCast_mul (X : Obj F 𝔠 S) {T : Over S} (x : T ⟶ X.A) (k : ℕ) (a : 𝓞 F) :
    x ≫ X.rm.act ((k : 𝓞 F) * a) = (x ≫ X.rm.act a) ^ k := by
  induction k with
  | zero =>
    have h0 : X.rm.act 0 = 1 := by
      have h := X.rm.add 0 0
      rw [add_zero] at h
      exact (mul_eq_left.1 h.symm)
    rw [Nat.cast_zero, zero_mul, h0, pow_zero, MonObj.comp_one]
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, _root_.one_mul, X.rm.add, MonObj.comp_mul, ih, pow_succ]

theorem pow_comp_act (X : Obj F 𝔠 S) {T : Over S} (x : T ⟶ X.A) (k : ℕ) (a : 𝓞 F) :
    (x ^ k) ≫ X.rm.act a = x ≫ X.rm.act ((k : 𝓞 F) * a) := by
  haveI := X.rm.hom a
  rw [MonObj.pow_comp, comp_act_natCast_mul]

theorem natCast_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hn

theorem dvd_of_mul_dvd_mul {M M' : ℕ} (hM' : M' ≠ 0) {a : 𝓞 F}
    (h : ((M * M' : ℕ) : 𝓞 F) ∣ (M' : 𝓞 F) * a) : (M : 𝓞 F) ∣ a := by
  rw [Nat.cast_mul, mul_comm] at h
  exact (mul_dvd_mul_iff_left (natCast_ne_zero hM')).1 h

theorem exists_level_pow {X : Obj F 𝔠 S} {L M M' : ℕ} (hL : L = M * M') (hM : M ≠ 0) (hM' : M' ≠ 0)
    (ξ : X.Level L) : ∃ β : X.Level M, ∀ i, β.pt i = ξ.pt i ^ M' := by
  subst hL
  refine ⟨{ pt := fun i ↦ ξ.pt i ^ M', tors := ?_, inj := ?_, surj := ?_ }, fun _ ↦ rfl⟩
  · intro i
    rw [← pow_mul, mul_comm M' M, ξ.tors i]
  · intro Ω _ _ t a b h
    simp only [pow_comp_act] at h
    obtain ⟨ha, hb⟩ := ξ.inj Ω t _ _ h
    exact ⟨dvd_of_mul_dvd_mul hM' ha, dvd_of_mul_dvd_mul hM' hb⟩
  · intro Ω _ _ t y hy
    have hy' : y ^ (M * M') = 1 := by rw [pow_mul, hy, one_pow]
    obtain ⟨a, b, hab⟩ := ξ.surj Ω t y hy'
    have hN : (toUnit (Over.mk t) ≫ ξ.pt 0 ≫ X.rm.act ((M : 𝓞 F) * a)) *
        (toUnit (Over.mk t) ≫ ξ.pt 1 ≫ X.rm.act ((M : 𝓞 F) * b)) = 1 := by
      rw [← hy, hab, mul_pow]
      simp only [← Category.assoc, comp_act_natCast_mul, MonObj.comp_pow]
    obtain ⟨ha, hb⟩ := ξ.inj Ω t _ _ hN
    rw [mul_comm M M'] at ha hb
    obtain ⟨a', rfl⟩ := dvd_of_mul_dvd_mul hM ha
    obtain ⟨b', rfl⟩ := dvd_of_mul_dvd_mul hM hb
    refine ⟨a', b', ?_⟩
    rw [hab, pow_comp_act, pow_comp_act]

end GlobalTheory.RealMult.LevelPow

open GlobalTheory.RealMult.LevelPow in

theorem GlobalTheory.RealMult.Obj.Level.exists_pow_levels : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, N ≠ 0 → N' ≠ 0 → ∀ ξ : X.Level (N * N'),
    (∃ β : X.Level N, ∀ i, β.pt i = ξ.pt i ^ N') ∧ ∃ β' : X.Level N', ∀ i, β'.pt i = ξ.pt i ^ N := by
  intro F _ _ 𝔠 S X N N' hN hN' ξ
  exact ⟨exists_level_pow rfl hN hN' ξ, exists_level_pow (mul_comm N N') hN' hN ξ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraBaseChangeIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj
open GlobalTheory.Serre GlobalTheory.FlatRow.EigLocal

theorem lieBaseChange_equiv : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R]
    [CommRing R'] [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap (algebraMap R R')) φ →
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, ∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v) := by
  intro F _ _ 𝔠 R R' _ _ _ X X' φ h
  set f := algebraMap R R' with hf
  obtain ⟨ρ, hρ, -⟩ := exists_res h.grp X.rm X'.rm h.act
  letI : Module R X'.Lie := Module.compHom X'.Lie f
  haveI : IsScalarTower R R' X'.Lie := ⟨fun r s v => by
    show (r • s) • v = f r • (s • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let ρR : X.Lie →ₗ[R] X'.Lie :=
    { toFun := ρ, map_add' := ρ.map_add, map_smul' := fun r v => ρ.map_smulₛₗ r v }
  let e₀ : R' ⊗[R] X.Lie →ₗ[R'] X'.Lie := LinearMap.liftBaseChange R' ρR
  have he₀ : ∀ (c : R') v, e₀ (c ⊗ₜ v) = c • ρ v := fun c v => by
    simp [e₀, ρR, LinearMap.liftBaseChange_tmul]
  have corr : ∀ v v', LieCorr f φ v v' ↔ v' = ρ v := fun v v' =>
    ⟨fun e => Serre.Lie.ext ((existsUnique_isVecOver h.grp.1 v.hom).unique e (hρ v)), fun e => e ▸ hρ v⟩
  have hsm := X.dim.smooth
  have hsm' := X'.dim.smooth

  have loc : ∀ (q : Ideal R') [q.IsPrime], (∀ z, e₀ z = 0 → ∃ u ∉ q, u • z = 0) ∧
      ∀ y, ∃ u ∉ q, u • y ∈ LinearMap.range e₀ := by
    intro q _
    let T := Localization.AtPrime q
    let gT := algebraMap R' T
    letI : GrpObj ((Over.pullback (spMap gT)).obj X'.A) := Functor.grpObjObj
    haveI : IsCommMonObj ((Over.pullback (spMap gT)).obj X'.A) := Functor.isCommMonObj_obj
    have hq := isGrpPullback_pullback X'.A (spMap gT)
    obtain ⟨aq, haq⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X'.rm hq
    obtain ⟨ρq, hρq, -⟩ := exists_res hq X'.rm aq haq
    have hc : IsGrpPullback ((Over.pullback (spMap gT)).obj X'.A) X.A (spMap (gT.comp f))
        (pullback.fst X'.A.hom (spMap gT) ≫ φ) := by
      have := hq.comp h.grp
      rwa [spMap_comp_spMap] at this
    set p := q.comap f with hp
    obtain ⟨n, w₀, hw₀, hw⟩ := GlobalTheory.T.tangent_vectors_localization_lift X.A hsm p
    let w : Fin n → X.Lie := fun i => Serre.Lie.mk X.rm (w₀ i) (hw₀ i)
    have hmax : (IsLocalRing.maximalIdeal T).comap (gT.comp f) = p := by
      rw [← Ideal.comap_comap]
      exact congrArg (Ideal.comap f) (Localization.AtPrime.comap_maximalIdeal (I := q))
    have hB := GlobalTheory.T.tangent_frame_localization_spans hsm p w₀ hw T (gT.comp f) hmax _ _ hc
      (fun i => (ρq (ρ (w i))).hom) fun i => by
        have e1 := hρq (ρ (w i))
        have e2 := hρ (w i)
        unfold IsVecOver at e1 e2 ⊢
        rw [← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, spMap_comp_spMap,
          ← Chart.dualMapR_comp]
        rfl
    rw [Serre.Lie.isLieBasis_iff] at hB
    refine ⟨fun z hz => ?_, fun y => ?_⟩
    ·
      have span : ∀ z : R' ⊗[R] X.Lie, ∃ s ∉ p, ∃ c : Fin n → R', f s • z = ∑ i, c i ⊗ₜ w i := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => exact ⟨1, p.primeCompl.one_mem, 0, by simp⟩
        | tmul r l =>
          obtain ⟨s, hs, hl⟩ := GlobalTheory.T.tangent_frame_localization_independent hsm X.rm p w (fun G' _ ψ hψ v hv => hw G' ψ hψ v hv) l
          obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hl
          refine ⟨s, hs, fun i => f (b i) * r, ?_⟩
          calc f s • (r ⊗ₜ[R] l) = (s • r) ⊗ₜ[R] l := by
                rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
            _ = r ⊗ₜ[R] (s • l) := TensorProduct.smul_tmul _ _ _
            _ = _ := by
                rw [← hb, TensorProduct.tmul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
        | add z₁ z₂ h₁ h₂ =>
          obtain ⟨s₁, hs₁, c₁, e₁⟩ := h₁
          obtain ⟨s₂, hs₂, c₂, e₂⟩ := h₂
          refine ⟨s₁ * s₂, p.primeCompl.mul_mem hs₁ hs₂, fun i => f s₂ * c₁ i + f s₁ * c₂ i, ?_⟩
          have e₃ : f (s₁ * s₂) • (z₁ + z₂) = f s₂ • (f s₁ • z₁) + f s₁ • (f s₂ • z₂) := by
            rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm (f s₂)]
          rw [e₃, e₁, e₂]
          simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.add_tmul,
            Finset.sum_add_distrib]
      obtain ⟨s, hs, c, hc⟩ := span z
      have h0 : ∑ i, c i • ρ (w i) = 0 := by
        have := congrArg e₀ hc
        rw [map_smul, hz, smul_zero, map_sum] at this
        simpa [he₀] using this.symm
      have h1 : Fintype.linearCombination T (fun i => ρq (ρ (w i))) (fun i => gT (c i)) = 0 := by
        have := congrArg ρq h0
        rw [map_sum, map_zero] at this
        simpa [Fintype.linearCombination_apply] using this
      have h2 : ∀ i, gT (c i) = 0 := fun i => by
        have := hB.1 (h1.trans (map_zero _).symm)
        exact congrFun this i
      choose u hu using fun i => (IsLocalization.map_eq_zero_iff q.primeCompl T (c i)).1 (h2 i)
      refine ⟨(∏ i, (u i : R')) * f s, q.primeCompl.mul_mem (q.primeCompl.prod_mem fun i _ => (u i).2) hs, ?_⟩
      rw [mul_smul, hc, Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_right_comm, hu i, zero_mul, TensorProduct.zero_tmul]
    ·
      obtain ⟨c, hcy⟩ := hB.2 (ρq y)
      obtain ⟨⟨t, ht⟩, hta⟩ := IsLocalization.exist_integer_multiples q.primeCompl (Finset.univ : Finset (Fin n)) c
      choose a ha using fun i => hta i (Finset.mem_univ i)
      have hx0 : ρq (t • y - ∑ i, a i • ρ (w i)) = 0 := by
        rw [map_sub, map_smulₛₗ, map_sum, ← hcy, Fintype.linearCombination_apply, Finset.smul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_smulₛₗ, smul_smul, ha i, Algebra.smul_def, sub_self]
      haveI := hsm'
      obtain ⟨r, hr, hrx⟩ := exists_smul_eq_zero X'.rm q (t • y - ∑ i, a i • ρ (w i)) (by
        have e1 := hρq (t • y - ∑ i, a i • ρ (w i))
        have e0 := hρq 0
        rw [hx0] at e1
        rw [map_zero] at e0
        unfold IsVecOver at e1 e0
        exact e1.symm.trans e0)
      refine ⟨r * t, q.primeCompl.mul_mem hr ht, ∑ i, (r * a i) ⊗ₜ w i, ?_⟩
      rw [smul_sub, sub_eq_zero, Finset.smul_sum] at hrx
      rw [map_sum]
      simp only [he₀]
      rw [mul_smul, hrx]
      simp only [smul_smul]
  refine ⟨LinearEquiv.ofBijective e₀ ⟨?_, ?_⟩, fun v v' => (corr v v').trans ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact eq_zero_of_loc fun q _ => (loc q).1 z hz
  · intro y
    have : Submodule.Quotient.mk (p := LinearMap.range e₀) y = 0 := eq_zero_of_loc fun q _ => by
      obtain ⟨u, hu, hm⟩ := (loc q).2 y
      exact ⟨u, hu, by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hm⟩
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  · show v' = ρ v ↔ v' = e₀ (1 ⊗ₜ v)
    rw [he₀, one_smul]
end GlobalTheory.RealMult.Obj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFreeRankDegree
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Lie.free_finrank_of_isLocalRing : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (R : Type) [CommRing R] [IsLocalRing R] (X : Obj F 𝔠 (Sp R)),
    Module.Free R X.Lie ∧ Module.Finite R X.Lie ∧ Module.finrank R X.Lie = Module.finrank ℚ F := by
  intro F _ _ 𝔠 R _ _ X
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank X
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R X.Lie := Module.free_of_flat_of_isLocalRing
  refine ⟨inferInstance, hfin, ?_⟩
  have h := hrk (IsLocalRing.closedPoint R)
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm

namespace GlobalTheory.HeightParts

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X}

def lieCoordLat (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G) :
    Submodule (𝓞 K) (Fin n → K) where
  carrier := {c | ∃ w : TanM xO t.G, bcTan (algebraMap (𝓞 K) K) hx w = ∑ i, c i • b i}
  add_mem' := by
    rintro c c' ⟨w, hw⟩ ⟨w', hw'⟩
    refine ⟨w + w', ?_⟩
    rw [map_add, hw, hw', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨w, hw⟩
    refine ⟨a • w, ?_⟩
    rw [map_smulₛₗ, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Algebra.smul_def, mul_smul]

end Lat

variable {D : D7} (O : Setup D)

def IsLieAt (y : Pt O.s) (K : Type) [Field K] [NumberField K] (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K))
    (h : HermFam K (Fin (D.R.f * O.N) → K)) : Prop :=
  ∃ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (io : K →+* Qb) (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z)
    (xO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = yK ≫ genι O.s.T.Z)
    (hio : spMap io ≫ yK = y.y) (e : Fin (D.R.f * O.N) ≃ Letter O.S.Dw)
    (b : Fin (D.R.f * O.N) → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G),
    O.CoreWith x P ∧ yK ≫ genStr O.s.T.Z = spMap fK ∧
    (∀ i, (tv (bcTan io (by rw [← Category.assoc, hio]) (b i))).left = y.u (e i).1 (e i).2) ∧
    L = lieCoordLat O.s.T.Z.t hx b ∧
    ∀ (σ : K →+* ℂ) (z : CxPts (genStr O.s.T.Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin (D.R.f * O.N) → K),
      h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i))
        (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i))

end GlobalTheory.HeightParts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFiltrationSpannedCorrespondenceStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_filtration_spanned_correspondence : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ),
    Submodule.span R' {x' | ∃ x, m.Corr x x'} = ⊤ ∧
      Fil X'.A ≤ Submodule.span R' {x' | ∃ x ∈ Fil X.A, m.Corr x x'} ∧
      ∀ x x', x ∈ Fil X.A → m.Corr x x' → x' ∈ Fil X'.A := by
  first | exact @GlobalTheory.DeRham.span_corr_baseChange | exact GlobalTheory.DeRham.span_corr_baseChange | (intros; apply GlobalTheory.DeRham.span_corr_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondenceStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_image_correspondence : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ) {x : HdR X.A} {x' : HdR X'.A},
    m.Corr x x' → ∀ {v : X.Lie} {v' : X'.Lie}, IsLieImage x v.hom → IsLieImage x' v'.hom →
    Obj.LieCorr σ φ v v' := by
  first | exact @GlobalTheory.RealMult.Obj.lieCorr_of_isLieImage | exact GlobalTheory.RealMult.Obj.lieCorr_of_isLieImage | (intros; apply GlobalTheory.RealMult.Obj.lieCorr_of_isLieImage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImagePolynomialEndomorphism
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieImagePoly

theorem exists_isLieImage_aeval (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g)
    (α : A ⟶ A) [IsMonHom α] (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (hD : ∀ z, u.ex (D z) = u.ex z ≫ α)
    (h : HdR A) (v : epsR ℂ ⟶ A) (w : Fin g → ℂ) (c : ℂ) (hv : IsLieImage h v) (hw : u.IsDiff w v)
    (hc : D w = c • w) (Q : Polynomial ℂ) :
    ∃ v', IsLieImage (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) Q h) v' ∧ u.IsDiff (Q.eval c • w) v' := by
  induction Q using Polynomial.induction_on with
  | C a =>
    refine ⟨GlobalTheory.GrpTangent.epsScale a ≫ v, ?_, ?_⟩
    · rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      exact hv.smul a
    · rw [Polynomial.eval_C]
      exact GlobalTheory.PeriodLattice.isDiff_epsScale u hw a
  | add p q hp hq =>
    obtain ⟨v₁, h₁, d₁⟩ := hp
    obtain ⟨v₂, h₂, d₂⟩ := hq
    refine ⟨v₁ * v₂, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply]
      exact h₁.add h₂
    · rw [Polynomial.eval_add, add_smul]
      exact GlobalTheory.UnifDifferential.isDiff_mul u ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 h₁.1)
        ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 h₂.1) d₁ d₂
  | monomial n a ih =>
    obtain ⟨v₁, h₁, d₁⟩ := ih
    refine ⟨v₁ ≫ α, ?_, ?_⟩
    · have e : Polynomial.C a * Polynomial.X ^ (n + 1) = Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
      rw [e, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
      exact h₁.push α
    · have e : Polynomial.eval c (Polynomial.C a * Polynomial.X ^ (n + 1)) =
          c * Polynomial.eval c (Polynomial.C a * Polynomial.X ^ n) := by simp [pow_succ]; ring
      have k := GlobalTheory.UnifLieBasis.isDiff_comp u α D hD h₁.1 d₁
      rwa [map_smul, hc, smul_smul, mul_comm, ← e] at k

end GlobalTheory.LieImagePoly
end

