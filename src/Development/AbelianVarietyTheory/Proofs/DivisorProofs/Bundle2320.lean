import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementOfDvrTestPoints
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory

theorem dvd_of_norm_le_of_padicComplexInt (p : ℕ) [Fact p.Prime] (V' : Type) [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (kO : V' →+* 𝓞_ℂ_[p]) (hkO : Function.Injective kO)
    (hpT : (p : V') ∈ IsLocalRing.maximalIdeal V') (a b : V') (hb : b ≠ 0)
    (hle : ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a)‖ ≤ ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO b)‖) : b ∣ a := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpC : ‖(p : ℂ_[p])‖ < 1 := by
    have h3 : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [h3, norm_algebraMap', Padic.norm_p]
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ this
  let N : V' → ℝ := fun y => ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO y)‖
  have hNmul : ∀ y z, N (y * z) = N y * N z := fun y z => by
    simp only [N, map_mul, norm_mul]
  have hN0 : ∀ y, 0 ≤ N y := fun y => norm_nonneg _
  have hOC : ∀ z : ℂ_[p], z ∈ 𝓞_ℂ_[p] → ‖z‖ ≤ 1 := by
    intro z hz
    have h : z ∈ 𝓞_ℂ_[p] ↔ ‖z‖ ≤ 1 := by
      rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
      exact (Valued.toNormedField.norm_le_one_iff).symm
    exact h.1 hz
  have hN1 : ∀ y, N y ≤ 1 := fun y => hOC _ (kO y).2
  have hNpos : ∀ y, y ≠ 0 → 0 < N y := fun y hy => by
    apply norm_pos_iff.2
    intro h0
    exact hy (hkO (Subtype.val_injective (by simpa using h0)))
  have hNone : N 1 = 1 := by simp only [N, map_one, norm_one]
  have hNu : ∀ w : V'ˣ, N w = 1 := fun w => by
    have h1 : N (w : V') * N ((w⁻¹ : V'ˣ) : V') = 1 := by
      rw [← hNmul, Units.mul_inv, hNone]
    have := hN1 (w : V'); have := hN1 ((w⁻¹ : V'ˣ) : V')
    nlinarith [hN0 (w : V'), hN0 ((w⁻¹ : V'ˣ) : V')]
  have hNpow : ∀ y (m : ℕ), N (y ^ m) = N y ^ m := fun y m => by
    simp only [N, map_pow, norm_pow]
  have hNp : N (p : V') < 1 := by
    have : N (p : V') = ‖(p : ℂ_[p])‖ := by simp only [N, map_natCast]
    rw [this]; exact hpC
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V'
  have hNϖ : N ϖ' < 1 := by
    have hp0' : (p : V') ≠ 0 := by
      intro h
      have : (kO (p : V') : ℂ_[p]) = 0 := by rw [h, map_zero]; rfl
      rw [map_natCast] at this
      exact hp0 (by exact_mod_cast this)
    obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0' hϖ'
    have hm : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, _root_.mul_one] at hw
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hpT
      exact hpT (hw ▸ w.isUnit)
    have hNpm : N (p : V') = N ϖ' ^ m := by
      rw [hw, hNmul, hNu, _root_.one_mul, hNpow]
    by_contra hge
    have h1 : N ϖ' = 1 := le_antisymm (hN1 _) (not_lt.1 hge)
    rw [hNpm, h1, one_pow] at hNp
    exact lt_irrefl _ hNp
  rcases ValuationRing.dvd_total b a with h | ⟨d, hd⟩
  · exact h
  · by_cases hdu : IsUnit d
    · obtain ⟨w, rfl⟩ := hdu
      exact ⟨((w⁻¹ : V'ˣ) : V'), by rw [hd, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
    · exfalso
      have hdm : d ∈ IsLocalRing.maximalIdeal V' := (IsLocalRing.mem_maximalIdeal _).2 hdu
      rw [hϖ'.maximalIdeal_eq, Ideal.mem_span_singleton'] at hdm
      obtain ⟨d', rfl⟩ := hdm
      have hNd : N (d' * ϖ') < 1 := by
        rw [hNmul]
        calc N d' * N ϖ' ≤ 1 * N ϖ' := mul_le_mul_of_nonneg_right (hN1 _) (hN0 _)
          _ < 1 := by rw [_root_.one_mul]; exact hNϖ
      have hb0 := hNpos _ hb
      have h2 : N b = N a * N (d' * ϖ') := by rw [hd, hNmul]
      have hle' : N a ≤ N b := hle
      have h4 := mul_le_mul_of_nonneg_right hle' (hN0 (d' * ϖ'))
      have h5 := mul_lt_mul_of_pos_left hNd hb0
      linarith

end GlobalTheory

namespace GlobalTheory

theorem mem_range_of_norm_le_one_at_points_away : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra V A] [Algebra.FiniteType V A], Function.Injective (algebraMap V A) → ∀ e : A, e ≠ 0 → ∀ x : Localization.Away (p : A), (∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (kO.comp φ) → ‖ψ x‖ ≤ 1) → ∃ a : A, algebraMap A (Localization.Away (p : A)) a = x := by
  intro F _ _ V _ p _ hp A _ _ _ _ _ hinj e he x hx
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfin : Finite (IsLocalRing.ResidueField V) :=
    (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hp0 hp).2
  have hpV : ((p : V)) ∈ IsLocalRing.maximalIdeal V := by
    rw [ValuationSubring.valuation_lt_one_iff]
    rw [ValuationSubring.mem_nonunits_iff] at hp
    simpa using hp
  have hpV0 : ((p : V)) ≠ 0 := by
    intro h
    have : ((p : V) : F) = 0 := by rw [h]; rfl
    exact hp0 (by exact_mod_cast this)
  let O' := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hinj0 : Function.Injective (algebraMap V O') := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  haveI : CharZero O' := charZero_of_injective_algebraMap hinj0
  haveI : IsLocalHom (algebraMap V O') := inferInstance
  have hfinO' : Finite (IsLocalRing.ResidueField O') :=
    Finite.of_surjective _ (AdicCompletion.residueField_map_bijective V).2
  let L := Localization.Away (p : A)
  have hpA0 : (p : A) ≠ 0 := by
    intro h
    apply hpV0
    apply hinj
    rw [map_natCast, h, map_zero]
  let Ω := FractionRing A
  have hu : IsUnit (algebraMap A Ω (p : A)) :=
    IsUnit.mk0 _ (fun h => hpA0 (IsFractionRing.injective A Ω (by rw [h, map_zero])))
  let j : L →+* Ω := IsLocalization.Away.lift (p : A) hu
  have hj : ∀ a, j (algebraMap A L a) = algebraMap A Ω a := fun a => IsLocalization.lift_eq _ a
  have hjinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (p : A) y
    have h1 : algebraMap A Ω a = 0 := by rw [← hj, ← ha, map_mul, hy, zero_mul]
    have h2 : a = 0 := IsFractionRing.injective A Ω (by rw [h1, map_zero])
    have h3 : IsUnit (algebraMap A L (p : A) ^ n) := (IsLocalization.Away.algebraMap_isUnit (p : A)).pow n
    rw [h2, map_zero] at ha
    exact h3.mul_left_eq_zero.1 ha
  obtain ⟨s, hs1, hsint⟩ := GlobalTheory.isIntegral_mul_of_bounded_at_points V O' hinj0
    (GlobalTheory.exists_integral_point_of_complete_case
      (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
      V O' hinj0)
    A Ω hinj e he (j x) (fun V' _ _ _ _ _ φ hφ hφe a b hab hb => by
      obtain ⟨-, hloc', hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr O' V'
      let T : CDVR := { V := V' }
      have hT : T.FinRes := hfin' hfinO'
      obtain ⟨q, hq, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
      have hpT : (p : V') ∈ IsLocalRing.maximalIdeal V' := by
        have h1 : (p : V') = algebraMap O' V' (algebraMap V O' (p : V)) := by
          rw [map_natCast, map_natCast]
        rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu'
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hpV
        exact hpV (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu'))
      obtain rfl := GlobalTheory.FlatModel.eq_of_mem_maximalIdeal_of_padicComplexInt T p q hpT kO
      have hkO : Function.Injective kO := fun a b hab => by
        apply IsFractionRing.injective T.V T.Fr
        apply k.injective
        rw [← hk, ← hk, hab]
      let g : A →+* ℂ_[p] := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (kO.comp φ)
      have hgu : IsUnit (g (p : A)) := by
        rw [map_natCast]
        exact IsUnit.mk0 _ (by exact_mod_cast hp0)
      let ψ : L →+* ℂ_[p] := IsLocalization.Away.lift (p : A) hgu
      have hψ : ψ.comp (algebraMap A L) = g := IsLocalization.Away.lift_comp (p : A) hgu
      have hxle : ‖ψ x‖ ≤ 1 := hx T kO φ hT hkO hφe ψ hψ
      have hxb : x * algebraMap A L b = algebraMap A L a := by
        apply hjinj
        rw [map_mul, hj, hj, hab]
      have hgab : ψ x * g b = g a := by
        rw [← hψ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hxb]
      refine GlobalTheory.dvd_of_norm_le_of_padicComplexInt p V' kO hkO hpT (φ a) (φ b) hb ?_
      change ‖g a‖ ≤ ‖g b‖
      rw [← hgab, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hxle
      )
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hsint
  have hsc : algebraMap A L s * x = algebraMap A L c := by
    apply hjinj
    rw [map_mul, hj, hj, hc]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs1' : s - 1 ∈ Ideal.span {algebraMap V A ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hs1
    exact hs1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hs1'
  have hcop : IsCoprime s (algebraMap V A ϖ) := ⟨1, -t, by linear_combination (-1 : A) * ht⟩
  obtain ⟨k, u, hpu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hpV0 hϖ
  obtain ⟨n, a0, ha0⟩ := IsLocalization.Away.surj (p : A) x
  have hpA : ((p : A)) ^ n = algebraMap V A ((u ^ n : Vˣ) : V) * algebraMap V A ϖ ^ (k * n) := by
    rw [← map_natCast (algebraMap V A), hpu, ← map_pow, ← map_pow, ← map_mul, mul_pow, ← pow_mul,
      Units.val_pow_eq_pow_val]
  have hcopU : IsCoprime s (algebraMap V A ((u ^ n : Vˣ) : V)) := by
    obtain ⟨w, hw⟩ := ((u ^ n).isUnit.map (algebraMap V A))
    exact ⟨0, ((w⁻¹ : Aˣ) : A), by rw [← hw]; simp⟩
  have hcopP : IsCoprime s ((p : A) ^ n) := by
    rw [hpA]
    exact hcopU.mul_right (hcop.pow_right)
  obtain ⟨α, β, hαβ⟩ := hcopP
  refine ⟨α * c + β * a0, ?_⟩
  have hαβ' : algebraMap A L α * algebraMap A L s + algebraMap A L β * algebraMap A L (p : A) ^ n = 1 := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_add, hαβ, map_one]
  rw [map_add, map_mul, map_mul]
  linear_combination (-(algebraMap A L α)) * hsc + (-(algebraMap A L β)) * ha0 + x * hαβ'

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfPowEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.TowerWeil

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem eq_one_of_pow_eq_one {R : Type} [CommRing R] {J : Ideal R} (hJ : J ≤ Ideal.jacobson ⊥) {n : ℕ}
    (hn : IsUnit (n : R)) {w : R} (hw : w ^ n = 1) (h : w - 1 ∈ J) : w = 1 := by
  have hs : (∑ i ∈ Finset.range n, w ^ i) - n ∈ J := by
    have e : (∑ i ∈ Finset.range n, w ^ i) - n = ∑ i ∈ Finset.range n, (w ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow w 1 i
    rw [one_pow] at hq
    rw [hq]
    exact J.mul_mem_right _ h
  obtain ⟨v, hv⟩ := hn
  have hu : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    have e : (∑ i ∈ Finset.range n, w ^ i) = (v : R) * (((∑ i ∈ Finset.range n, w ^ i) - n) * (↑v⁻¹ : R) + 1) := by
      rw [mul_add, mul_comm ((∑ i ∈ Finset.range n, w ^ i) - n), ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul, _root_.mul_one, hv]
      ring
    rw [e]
    exact v.isUnit.mul ((Ideal.mem_jacobson_bot.1 (hJ hs)) _)
  have h0 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by rw [geom_sum_mul, hw, sub_self]
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom (c : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_bijective {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem exists_weilIs_root {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (P : LB (G2 A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) (N : ℕ) (hN : 0 < N) {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) :
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N x y c₀ := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP r₁ r₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP r₁ r₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag hP hB hB' (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG hA hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG hA hD hp (e₁' ▸ hc₁), hc₀⟩

theorem unitOn_pow' {R : Type} [CommRing R] (u : Rˣ) (m : ℕ) : unitOn (u ^ m) = unitOn u ^ m := by
  unfold unitOn; exact map_pow _ u m

theorem unitOn_zpow' {R : Type} [CommRing R] (u : Rˣ) (m : ℤ) : unitOn (u ^ m) = unitOn u ^ m := by
  unfold unitOn; exact map_zpow _ u m

theorem unitOn_one' {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := by
  unfold unitOn; exact map_one _

theorem exists_spMap {R K : Type} [CommRing R] [CommRing K] (x : Sp K ⟶ Sp R) : ∃ f : R →+* K, spMap f = x :=
  ⟨(Spec.preimage x).hom, by simp [spMap]⟩

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem weil_geom : ∀ g n : ℕ, 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (β : cycAway n →+* R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp R)) ⟶ A)), (∀ a a', lev (a + a') = lev a * lev a') → (∀ a, lev a ^ n = 1) → ∀ (c₀ : SiegPre g n (zetaAway n) (spMap ((Ideal.Quotient.mk (I ^ (0 + 1))).comp β))), c₀.Principal → ∀ (φ : c₀.A.left ⟶ A.left) (φ₂ : (G2 c₀.A).left ⟶ (G2 A).left), IsGrpPullback c₀.A A (spMap (Ideal.Quotient.mk (I ^ (0 + 1)))) φ → IsSquare φ φ₂ → LBIso c₀.P (P.pull φ₂) → (∀ a, (c₀.lev a).left ≫ φ = spMap (Ideal.Quotient.mk (I ^ (0 + 1))) ≫ (lev a).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R) (ψ : cycAway n →+* k) (z : kˣ), x ≫ spMap β = spMap ψ → (z : k) = ψ (zetaAway n) → ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  intro g n hn3 hodd R _ _ I hI β A _ _ hA P hP r₁ r₂ hsym hamp lev ladd ltors c₀ hc₀ φ φ₂ hpb hsq hiso hlev k _ _ x ψ z hx hz a b
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hn0 : n ≠ 0 := by omega
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨u, hun, hu⟩ := exists_weilIs_root hA P hP r₁ r₂ hamp n (by omega) (ltors a) (ltors b)
  obtain ⟨uR, rfl⟩ : ∃ uR : Rˣ, unitOn uR = u := unitOn_bijective.2 u
  have hz1 : zetaAway n ^ n = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one
  let ζR : Rˣ := Units.map β.toMonoidHom (cycBase hn0).ζ
  have hζR : (ζR : R) = β (zetaAway n) := rfl
  have hζn : ζR ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζR, ← map_pow, hz1, map_one, Units.val_one])
  have huR : uR ^ n = 1 := unitOn_bijective.1 (by rw [unitOn_pow', hun, unitOn_one'])
  have hnR : IsUnit (n : R) := by simpa using (isUnit_natCast hn0).map β
  set e : ℤ := 2 * omegaStd a b with he

  have key : uR = ζR ^ e := by
    let w : Rˣ := uR * (ζR ^ e)⁻¹
    have hw : w ^ n = 1 := by
      have h1 : (ζR ^ e) ^ n = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζn, one_zpow]
      rw [mul_pow, inv_pow, h1, huR, inv_one, _root_.mul_one]
    let mk := Ideal.Quotient.mk (I ^ (0 + 1))
    have hmk : Units.map mk.toMonoidHom w = 1 := by
      refine unitOn_bijective.1 ?_
      rw [unitOn_one']
      refine GlobalTheory.ObjTheta.root_ext (n := n) ?_ (by rw [← unitOn_pow', ← map_pow, hw, map_one, unitOn_one']) (one_pow n) ?_
      · have := (hnR.map mk).map (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (0 + 1)))).inv.hom
        rwa [map_natCast, map_natCast] at this
      · intro K _ _ x₀
        obtain ⟨φ₀, rfl⟩ := exists_spMap x₀
        rw [map_unitOn, map_one, ← unitOn_one']
        congr 1
        let z₀ : Kˣ := Units.map (φ₀.comp mk).toMonoidHom ζR
        obtain ⟨-, -, g₃⟩ := c₀.geom K (spMap φ₀) (φ₀.comp (mk.comp β)) z₀ (spMap_comp' _ _) rfl
        have W₀ := g₃ a b
        have W₁ := (GlobalTheory.weilIs_grpPullback_of_comm (Sp R) (Sp (R ⧸ I ^ (0 + 1))) A c₀.A (spMap mk) φ
          (P.pull (lift (𝟙 A) (𝟙 A)).left) (c₀.P.pull (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) hD (pull_isLB c₀.isLB _) hpb
          (SiegelPull.diag_iso hsq hiso) (Over.mk (spMap φ₀)) n _ _
          (toUnit (Over.mk (spMap φ₀ ≫ spMap mk)) ≫ lev a) (toUnit (Over.mk (spMap φ₀ ≫ spMap mk)) ≫ lev b) _
          (by simp [hlev]) (by simp [hlev])).1 W₀
        have W₂ := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk (spMap φ₀ ≫ spMap mk))) hu
        have E := CommutatorPairing.weilIs_unique hG hA hD W₂ W₁
        have h₁ : (toUnit (Over.mk (spMap φ₀ ≫ spMap mk))).left = spMap (φ₀.comp mk) := by simp [spMap_comp']
        rw [h₁, map_unitOn] at E
        have E' := unitOn_bijective.1 E
        have h₂ : Units.map φ₀.toMonoidHom (Units.map mk.toMonoidHom w) = Units.map (φ₀.comp mk).toMonoidHom w := by
          ext; rfl
        rw [h₂, map_mul, map_inv, map_zpow, show Units.map (φ₀.comp mk).toMonoidHom uR = z₀ ^ e from E']
        exact mul_inv_cancel _
    have hmem : (w : R) - 1 ∈ I := by
      have e₁ := congrArg (fun q : (R ⧸ I ^ (0 + 1))ˣ => (q : R ⧸ I ^ (0 + 1))) hmk
      simp only [Units.coe_map, Units.val_one, MonoidHom.coe_coe] at e₁
      have e₂ : mk (w : R) = mk 1 := by rw [map_one]; exact e₁
      have := Ideal.Quotient.eq.1 e₂
      simpa using this
    have hw1 : (w : R) = 1 := eq_one_of_pow_eq_one (IsAdicComplete.le_jacobson_bot I) hnR
      (by rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]) hmem
    exact mul_inv_eq_one.1 (Units.ext hw1)
  have hpull := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk x)) hu
  obtain ⟨φx, rfl⟩ := exists_spMap x
  have hφ : φx.comp β = ψ := by
    rw [spMap_comp'] at hx
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 hx)
  have hval : Units.map (toUnit (Over.mk (spMap φx))).left.appTop.hom.toMonoidHom (unitOn uR) = unitOn (z ^ e) := by
    have h₁ : (toUnit (Over.mk (spMap φx))).left = spMap φx := by simp
    rw [h₁, map_unitOn, key, map_zpow]
    congr 2
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hz, ← hφ, hζR, RingHom.comp_apply]
  rw [← hval]
  exact hpull

end GlobalTheory.TowerWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqUnitMulZpowRegularLocalModelDimTwoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_unit_mul_zpow_regularLocalModel_dimTwo : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ E : Place cL, E.IsPrimeOf Q → E.ord (u : L) = 1 →
  ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
  ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G := by
  first | exact @GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow | exact GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow | (intros; apply GlobalTheory.FieldPair.AdjUnit.eq_unit_mul_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEntireMulEqZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.FrameAut

theorem eq_zero_of_entire_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hne
  have hc : ContinuousAt D z := hD.continuousAt (hS.mem_nhds hz)
  have he : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hc.eventually_ne hne, hS.mem_nhds hz] with w hw hwS
    exact (mul_eq_zero.1 (h w hwS)).resolve_right hw
  have ha : AnalyticOnNhd ℂ θ Set.univ := SCV.analyticOnNhd_of_differentiable hθ Set.univ
  exact h0 (funext fun w =>
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) he (Set.mem_univ w))

end GlobalTheory.MBLow.Cl.FrameAut

namespace GlobalTheory.MBLow.Cl

theorem frame_eq_autV_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ M N (i : x.P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = autV τ a b M N z * u.fr i (z + perV τ M N) := by
  intro g x hg u τ a b c W hNF M N i z hz
  obtain ⟨hs, hp, ha, hb, hc, hΛ, _, hth, _⟩ := hNF
  obtain ⟨hd, ⟨z₀, hz₀⟩, hlaw⟩ := GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy g τ a b hs hp ha hb
  have hdc : Differentiable ℂ (fun w => c * thetaChar τ a b w) := (differentiable_const c).mul hd
  have h0 : (fun w => c * thetaChar τ a b w) ≠ 0 := fun h => by
    have := congrFun h z₀
    simp only [Pi.zero_apply, mul_eq_zero] at this
    exact this.elim hc hz₀
  have hl : u.ex (perV τ M N) = 1 := (u.ker _).2 ((hΛ _).2 ⟨M, N, rfl⟩)
  have he : ∀ w, u.ex (w + perV τ M N) = u.ex w := fun w => by rw [u.ex_add, hl, _root_.mul_one]
  have hS : IsOpen {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} := (u.hol _ 0).1
  have htr : ∀ w, ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (u.ex (w + perV τ M N)).left ⁻¹ᵁ x.P.L.U i :=
    fun w hw => by rw [he]; exact hw
  have hcf := (u.fr_hol i).continuousOn
  have haut : Continuous (autV τ a b M N) := by
    unfold autV dotProduct
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - autV τ a b M N w * u.fr i (w + perV τ M N))
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i} :=
    hcf.sub (haut.continuousOn.mul (hcf.comp (continuous_add_const _).continuousOn fun w hw => htr w hw))
  refine sub_eq_zero.1 (FrameAut.eq_zero_of_entire_mul_eq_zero hdc h0 hS hD (fun w hw => ?_) hz)
  have h1 := hth i w hw
  have h2 := hth i _ (htr w hw)
  beta_reduce at h1 h2 ⊢
  rw [he, h1, hlaw] at h2
  linear_combination h2

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalizationFiniteTypeComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.essFiniteType_of_localization_finiteType_complex : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := by
  first | exact @GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div | exact GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div | (intros; apply GlobalTheory.EssFiniteDescent.essFiniteType_of_eq_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedFormStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothCone_interior_definite_balancedForm : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ β ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < β x x) → ∃ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), IsCone bar φ γ ∧ 0 < k ∧ (∀ j, 0 < c j) ∧ k • β = ∑ j, c j • γ j := by
  first | exact @GlobalTheory.Poinc.Cover.exists_cone | exact GlobalTheory.Poinc.Cover.exists_cone | (intros; apply GlobalTheory.Poinc.Cover.exists_cone <;> assumption)
end

