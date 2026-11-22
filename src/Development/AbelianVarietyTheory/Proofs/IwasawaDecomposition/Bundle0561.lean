import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralQuotientDominatingValuationSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.DomValInt

theorem isIntegral_of_forall_valuationSubring (W : Type) [CommRing W] (F : Type) [Field F]
    [Algebra W F] (y : F)
    (hy : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → y ∈ V) :
    IsIntegral W y := by
  have hcl : IsIntegrallyClosedIn (integralClosure W F).toSubring F :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure W F) F)
  by_contra hn
  have hsn : y ∉ (integralClosure W F).toSubring := hn
  obtain ⟨V, hV, hyV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hsn
  exact hyV (hy V fun w => hV (Subalgebra.algebraMap_mem _ w))

theorem split_rel {F : Type} [Field F] (c : ℕ → F) (x : F) (n j : ℕ) (hjn : j ≤ n)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    (∑ i ∈ Finset.range j, c i * x ^ i) +
      x ^ j * ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k = 0 := by
  rw [← hrel, show n + 1 = j + (n + 1 - j) by omega, Finset.sum_range_add, Finset.mul_sum,
    show j + (n + 1 - j) - j = n + 1 - j by omega]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add]; ring

theorem tail_mem {F' : Type} [Field F'] (V : ValuationSubring F') (c : ℕ → F') (hc : ∀ i, c i ∈ V) (x : F')
    (n j : ℕ) (hjn : j ≤ n) (hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    (∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k) ∈ V ∧
      (∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k) * x ∈ V := by
  have hsplit := split_rel c x n j hjn hrel
  set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs
  by_cases hxV : x ∈ V
  · have : s ∈ V := by
      rw [hs]
      exact sum_mem fun k _ => mul_mem (hc _) (pow_mem hxV k)
    exact ⟨this, mul_mem this hxV⟩
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
  have hxi : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  rcases j with _ | j'
  · simp at hsplit
    rw [hsplit]; simp
  · set A' := ∑ i ∈ Finset.range (j' + 1), c i * x⁻¹ ^ (j' - i) with hA'
    have hA'V : A' ∈ V := sum_mem fun i _ => mul_mem (hc _) (pow_mem hxi _)
    have hA'x : A' * x ^ j' = ∑ i ∈ Finset.range (j' + 1), c i * x ^ i := by
      rw [hA', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show x ^ j' = x ^ (j' - i) * x ^ i by rw [← pow_add]; congr 1; omega, inv_pow]
      field_simp
    have hsx : s * x = -A' := by
      have hpow : x ^ j' ≠ 0 := pow_ne_zero _ hx0
      apply mul_right_cancel₀ hpow
      rw [neg_mul, hA'x, _root_.mul_assoc, ← pow_succ']
      linear_combination hsplit
    have htV : s * x ∈ V := by rw [hsx]; exact neg_mem hA'V
    refine ⟨?_, htV⟩
    have : s = (s * x) * x⁻¹ := by field_simp
    rw [this]; exact mul_mem htV hxi

end GlobalTheory.DomValInt

namespace GlobalTheory.DomValInt

theorem exists_integral_quotient :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra.IsAlgebraic (FractionRing W) F] [Algebra W F]
    [IsScalarTower W (FractionRing W) F] (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ x ∈ O, ∃ s t : F, IsIntegral W s ∧ IsIntegral W t ∧ O.valuation s = 1 ∧ s * x = t := by
  intro W _ _ _ F _ _ _ _ _ O hW hmax x hxO

  have hK : ∀ a : FractionRing W, algebraMap (FractionRing W) F a ∈ O →
      ∃ w : W, algebraMap W F w = algebraMap (FractionRing W) F a := by
    intro a ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact ⟨w, by rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw]⟩
    · by_cases ha0 : a = 0
      · exact ⟨0, by simp [ha0]⟩
      by_cases hu : IsUnit w
      · refine ⟨↑hu.unit⁻¹, ?_⟩
        have h1 : a⁻¹ * algebraMap W (FractionRing W) ↑hu.unit⁻¹ = 1 := by
          rw [← hw, ← map_mul, IsUnit.mul_val_inv, map_one]
        have h2 := (inv_mul_eq_one₀ ha0).mp h1
        rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, ← h2]
      · have hwm : w ∈ maximalIdeal W := (mem_maximalIdeal _).mpr hu
        have h2 := (O.mem_nonunits_iff).mp (hmax w hwm)
        have h3 := (O.valuation_le_one_iff _).mpr ha
        have h4 : algebraMap (FractionRing W) F a * algebraMap W F w = 1 := by
          rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw, ← map_mul,
            mul_inv_cancel₀ ha0, map_one]
        have h5 : O.valuation (algebraMap (FractionRing W) F a * algebraMap W F w) < 1 := by
          rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) h2
        rw [h4, map_one] at h5
        exact absurd h5 (lt_irrefl _)

  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing W) x
  set n := p.natDegree with hn
  set b : ℕ → F := fun i => algebraMap (FractionRing W) F (p.coeff i) with hb
  set v := O.valuation with hv
  obtain ⟨i0, hi0, hi0max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => v (b i)) ⟨0, by simp⟩
  set M := v (b i0) with hM
  set S := (Finset.range (n + 1)).filter (fun i => v (b i) = M) with hS
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S id
    ⟨i0, Finset.mem_filter.mpr ⟨hi0, rfl⟩⟩
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hjS).1)
  have hjM : v (b j) = M := (Finset.mem_filter.mp hjS).2
  have hcoeff0 : ∀ i, n < i → b i = 0 := fun i hi => by
    simp [b, Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega)]
  have hle : ∀ i, v (b i) ≤ M := fun i => by
    by_cases hi : i ≤ n
    · exact hi0max i (Finset.mem_range.mpr (by omega))
    · rw [hcoeff0 i (by omega), map_zero]; exact zero_le'
  have hM0 : M ≠ 0 := by
    intro h
    have h1 : v (b n) = 0 := le_antisymm (h ▸ hle n) zero_le'
    rw [Valuation.zero_iff] at h1
    have h2 : p.leadingCoeff = 0 := (algebraMap (FractionRing W) F).injective (by rw [map_zero]; exact h1)
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h2)
  have hlt : ∀ i, j < i → v (b i) < M := by
    intro i hi
    rcases lt_or_eq_of_le (hle i) with h | h
    · exact h
    exfalso
    by_cases hin : i ≤ n
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
      have := hjmax i hiS
      simp only [id] at this
      omega
    · rw [hcoeff0 i (by omega), map_zero] at h
      exact hM0 h.symm
  have hbj : b j ≠ 0 := fun h => hM0 (by rw [← hjM, h, map_zero])
  have hMpos : 0 < M := zero_lt_iff.mpr hM0
  set c : ℕ → F := fun i => b i / b j with hc
  have hcle : ∀ i, v (c i) ≤ 1 := fun i => by
    simp only [c, map_div₀, hjM]
    exact (div_le_one₀ hMpos).mpr (hle i)
  have hclt : ∀ i, j < i → v (c i) < 1 := fun i hi => by
    simp only [c, map_div₀, hjM]
    exact (div_lt_one₀ hMpos).mpr (hlt i hi)
  have hcW : ∀ i, ∃ w : W, algebraMap W F w = c i := fun i => by
    have hci : c i = algebraMap (FractionRing W) F (p.coeff i / p.coeff j) := by
      simp [c, b, map_div₀]
    rw [hci]
    exact hK _ (by rw [← hci]; exact (O.valuation_le_one_iff _).mp (hcle i))
  have hcj : c j = 1 := div_self hbj
  have hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0 := by
    have h := hpx
    rw [Polynomial.aeval_eq_sum_range] at h
    simp only [c, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [div_eq_zero_iff]
    left
    simpa [Algebra.smul_def, b] using h
  set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs
  have hmemV : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → s ∈ V ∧ s * x ∈ V :=
    fun V hV => tail_mem V c (fun i => by obtain ⟨w, hw⟩ := hcW i; rw [← hw]; exact hV w)
      x n j hjn hrel
  refine ⟨s, s * x, isIntegral_of_forall_valuationSubring W F s fun V hV => (hmemV V hV).1,
    isIntegral_of_forall_valuationSubring W F _ fun V hV => (hmemV V hV).2, ?_, rfl⟩
  have hxle : v x ≤ 1 := (O.valuation_le_one_iff x).mpr hxO
  rw [hs, show n + 1 - j = (n - j) + 1 by omega, Finset.sum_range_succ', Nat.add_zero, pow_zero,
    _root_.mul_one, hcj, Valuation.map_add_eq_of_lt_right, map_one]
  rw [map_one]
  apply Valuation.map_sum_lt _ one_ne_zero
  intro k _
  rw [map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hxle _)) (hclt _ (by omega))

end GlobalTheory.DomValInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenTors

theorem exists_torsMap_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∃ f : QkPt P.D.toPre F k → (TF (R := R) F ⟶ t.G),
      (∀ q v, GlobalTheory.FlatTors.IsImage P F k q v ↔ v = (f q).left) ∧ (∀ q, f q ^ k = 1) ∧ (∀ x, x ^ k = 1 → ∃ q, f q = x) ∧
      (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
      (∀ p p' τ, p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        GlobalTheory.UU.CubWeil t.cub k (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y)))) ∧
      ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
  intro E _ _ _ H R _ _ _ t P _ hR F _ _ _ k hk
  letI := H.starRing
  obtain ⟨f₀, h1, h2, -, h4, -, h6⟩ := GlobalTheory.FlatTors.torsionIso_holds E H R (maximalIdeal R) hR t P F k hk
  obtain ⟨g₁, g₂, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv g₁ (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have hpow : ∀ q, f₀ q ^ k = 1 := fun q => by
    obtain ⟨w, hw⟩ := P.U.toUnifPre.ext
    exact ((h1 q (f₀ q)).2 rfl w hw).1
  have hpow' : ∀ q, e (f₀ q) ^ k = 1 := fun q => by rw [← map_pow, hpow, map_one]
  refine ⟨fun q => e (f₀ q), ?_, hpow', ?_, ?_, ?_, ?_⟩
  · intro q v
    constructor
    · rintro ⟨a, ha, hq⟩
      rw [(h1 q a).1 hq] at ha
      rw [← ha, he]
    · intro hv
      exact ⟨f₀ q, by rw [hv, he], (h1 q (f₀ q)).2 rfl⟩
  · intro x hx
    obtain ⟨q, hq⟩ := h2 (e.symm x) (by rw [← map_pow, hx, map_one])
    exact ⟨q, by simp only [hq, MulEquiv.apply_symm_apply]⟩
  · intro p p' p'' h
    simp only [h4 p p' p'' h, map_mul]
  · intro p p' τ hy hτ
    have hw : WeilIs P.A.A P.A.L k (f₀ p) (f₀ p') (unitOn (τ (Multiplicative.ofAdd p'.y))) :=
      (h6 p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
    have hpr : IsProper (pullback.snd t.G.hom (jK R)) := by
      have := P.A.isAb.proper
      have := isIso_inv_left P.U.gen.symm
      have h : IsProper ((Over.pullback (jK R)).obj t.G).hom := by
        rw [← Over.w P.U.gen.symm.inv]; infer_instance
      exact h
    have one : ∀ c : Fˣ, GlobalTheory.UU.CubWeil t.cub k (e (f₀ p)) (e (f₀ p')) (unitOn c) →
        WeilIs P.A.A P.A.L (k : ℤ) (f₀ p) (f₀ p') (unitOn c) := fun c h =>
      (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ t.G P.A.A (jK R) _ t.PP.L P.A.L t.PP.isLB P.A.isLB g₁ g₂
        (TFK (R := R) F) k (f₀ p) (f₀ p') (e (f₀ p)) (e (f₀ p')) (unitOn c) (he _) (he _)).2
        (GlobalTheory.FlatTors.weilIs_of_cubWeil_of_proper (jK R) t.G t.semi hpr t.cub k (TFK (R := R) F) _ _ _ h)
    obtain ⟨ζ, hζ, -⟩ := (GlobalTheory.UU.cubWeil_basic _ t.G t.PP t.cub k _).1 (e (f₀ p)) (e (f₀ p')) (hpow' p) (hpow' p')
    obtain ⟨c, rfl⟩ : ∃ c : Fˣ, unitOn c = ζ :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom ζ,
        Units.ext ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _)⟩
    have ec : c = τ (Multiplicative.ofAdd p'.y) :=
      GlobalTheory.weilIs_unique_fieldPoint _ P.A.A P.A.L P.A.isLB F _ k (f₀ p) (f₀ p') c _ (one c hζ) hw
    exact ec ▸ hζ
  · intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR P.D P.A t.G t.semi P.U F F σ k hk p
    obtain ⟨x', hx'⟩ := hx (f₀ p)
    have e' : x' = f₀ p' := (h1 p' x').1 ((hiff p' (f₀ p) x' hpp' hx').1 ((h1 p (f₀ p)).2 rfl))
    subst e'
    rw [he, he, hx', Category.assoc]

end GlobalTheory.GenTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTraitNonlocalTorusExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.NonlocalTrait

theorem exists_common_ext {F L₁ L₂ : Type} [Field F] [Field L₁] [Field L₂] (a : F →+* L₁) (b : F →+* L₂) :
    ∃ (L : Type) (_ : Field L) (i : L₁ →+* L) (j : L₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct F L₁ L₂)
  letI := Ideal.Quotient.field m
  refine ⟨TensorProduct F L₁ L₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := F) (A := L₁) (B := L₂)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  congr 1
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

theorem torusExtension_iterate {K : Type} [Field K] {S S₁ : Scheme.{0}} (a : S₁ ⟶ S)
    (b : Spec (CommRingCat.of K) ⟶ S₁) (G : Over S) [GrpObj G]
    (h : Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G))) :
    Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G))) := by
  obtain ⟨T⟩ := h
  exact ⟨torusExtOfIso (pullCompIso b a G) T⟩

theorem torusExtension_compose {K : Type} [Field K] {S S₁ : Scheme.{0}} (a : S₁ ⟶ S)
    (b : Spec (CommRingCat.of K) ⟶ S₁) (G : Over S) [GrpObj G]
    (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G)) := by
  obtain ⟨T⟩ := h
  haveI : IsMonHom (pullCompIso b a G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso b a G).inv)
  exact ⟨torusExtOfIso (pullCompIso b a G).symm T⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.NonlocalTrait

open GlobalTheory.NonlocalTrait in

theorem GlobalTheory.exists_trait_nonlocal_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), ¬ IsLocalHom g →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ψ : R →+* V)
      (Ω : Type) (_ : Field Ω) (α : FractionRing V →+* Ω) (β : W →+* Ω),
      IsLocalHom ψ ∧ (∀ x ∈ maximalIdeal W, β x = 0) ∧
      (α.comp (algebraMap V (FractionRing V))).comp ψ = β.comp g ∧
      Nonempty (TorusExtension ((Over.pullback (spMap ((algebraMap V (FractionRing V)).comp ψ))).obj G)) := by
  intro R _ _ _ _ G _ hG W _ _ g hg
  set p : Ideal R := Ideal.comap g (maximalIdeal W) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime g (maximalIdeal W)
  obtain ⟨r₀, hr₀u, hr₀⟩ : ∃ r, IsUnit (g r) ∧ ¬ IsUnit r := by
    by_contra h
    push_neg at h
    exact hg ⟨fun r hr => h r hr⟩
  have hr₀p : r₀ ∉ p := fun h => ((mem_maximalIdeal _).1 (Ideal.mem_comap.1 h)) hr₀u
  have hpm : p ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  haveI : IsLocalRing (R ⧸ p) := .of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hunit : ∀ r : R, IsUnit (Ideal.Quotient.mk p r) → IsUnit r := by
    intro r hr
    obtain ⟨b, hb⟩ := hr.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_contra hru
    have h1 : r * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hru
    have h2 : r * y - 1 ∈ maximalIdeal R :=
      hpm (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_sub, map_mul, hb, map_one, sub_self]))
    have h3 := (maximalIdeal R).sub_mem h1 h2
    rw [sub_sub_cancel] at h3
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hA : ¬ IsField (R ⧸ p) := by
    intro hF
    have h0 : Ideal.Quotient.mk p r₀ ≠ 0 := fun h => hr₀p (Ideal.Quotient.eq_zero_iff_mem.1 h)
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h0
    exact hr₀ (hunit r₀ (Units.mkOfMulEqOne _ b hb).isUnit)
  let k₀ := FractionRing (R ⧸ p)
  let φ₀ : R →+* k₀ := (algebraMap (R ⧸ p) k₀).comp (Ideal.Quotient.mk p)
  let σ : k₀ →+* AlgebraicClosure k₀ := algebraMap k₀ (AlgebraicClosure k₀)
  let G₀ := (Over.pullback (spMap φ₀)).obj G
  have hG₀ : IsSemiAbelian G₀ := IsSemiAbelian.pullback _ G hG
  haveI := hG₀.smooth
  haveI := hG₀.quasiCompact
  haveI := hG₀.separated
  have T₀ : Nonempty (TorusExtension ((Over.pullback (spMap σ)).obj G₀)) :=
    torusExtension_iterate _ _ G (by rw [← spMap_comp']; exact hG.fibres _ _)
  obtain ⟨T⟩ := T₀
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range σ G₀ T
  haveI : Finite s := hs.to_subtype
  let k' := IntermediateField.adjoin k₀ s
  haveI : FiniteDimensional k₀ k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  letI : Algebra (R ⧸ p) k' := ((algebraMap k₀ k').comp (algebraMap (R ⧸ p) k₀)).toAlgebra
  haveI : IsScalarTower (R ⧸ p) k₀ k' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨V, hV, hdom⟩ := (discreteValuationRing_dominating_noetherian_local (R := R ⧸ p) (K := k₀) k').1 hA
  rw [LocalSubring.le_def] at hdom
  obtain ⟨hsub, hloc⟩ := hdom
  have hmem : ∀ a : R ⧸ p, algebraMap (R ⧸ p) k' a ∈ V := fun a => hsub ⟨a, rfl⟩
  have hinjA : Function.Injective (algebraMap (R ⧸ p) k') :=
    (algebraMap k₀ k').injective.comp (IsFractionRing.injective (R ⧸ p) k₀)
  let ψA : (R ⧸ p) →+* V := (algebraMap (R ⧸ p) k').codRestrict V hmem
  let ψ : R →+* V := ψA.comp (Ideal.Quotient.mk p)
  have hψ : IsLocalHom ψ := by
    refine ⟨fun r hr => hunit r ?_⟩
    set a := Ideal.Quotient.mk p r
    have h1 : IsUnit (Subring.inclusion hsub ⟨algebraMap (R ⧸ p) k' a, a, rfl⟩) := hr
    obtain ⟨⟨u, v, huv, _⟩, hu⟩ := hloc.map_nonunit _ h1
    have hu' : u = ⟨algebraMap (R ⧸ p) k' a, a, rfl⟩ := hu
    subst hu'
    obtain ⟨b, hb⟩ := v.2
    refine (Units.mkOfMulEqOne a b (hinjA ?_)).isUnit
    have := congrArg Subtype.val huv
    rw [map_mul, map_one, hb]
    exact this
  let κ := ResidueField W
  let gA : (R ⧸ p) →+* κ := Ideal.Quotient.lift p ((residue W).comp g) (fun a ha => by
    show residue W (g a) = 0
    exact (residue_eq_zero_iff _).2 (Ideal.mem_comap.1 ha))
  have hgA : Function.Injective gA := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : residue W (g r) = 0 := ha
    have : g r ∈ maximalIdeal W := (residue_eq_zero_iff _).1 ha'
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.2 this)
  let g₀ : k₀ →+* κ := IsFractionRing.lift hgA
  let e : k' ≃ₐ[V] FractionRing V := IsLocalization.algEquiv (nonZeroDivisors V) k' (FractionRing V)
  let α₀ : k₀ →+* FractionRing V := e.toRingEquiv.toRingHom.comp (algebraMap k₀ k')
  let β₀ : FractionRing V →+* AlgebraicClosure k₀ := (algebraMap k' (AlgebraicClosure k₀)).comp e.symm.toRingEquiv.toRingHom
  have hβα : β₀.comp α₀ = σ := by
    ext x
    simp [α₀, β₀, σ]
  have hsr : s ⊆ Set.range β₀ := fun x hx =>
    ⟨e ⟨x, IntermediateField.subset_adjoin k₀ s hx⟩, by simp [β₀]⟩
  have T₂ := torusExtension_compose _ _ G (H (FractionRing V) α₀ β₀ hβα hsr)
  have key : α₀.comp φ₀ = (algebraMap V (FractionRing V)).comp ψ := by
    ext r
    show e (algebraMap k₀ k' (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) =
      algebraMap V (FractionRing V) (ψA (Ideal.Quotient.mk p r))
    rw [← e.commutes]
    rfl
  obtain ⟨L, _, i, j, hij⟩ := exists_common_ext α₀ g₀
  refine ⟨V, inferInstance, inferInstance, hV, ψ, L, inferInstance, i, j.comp (residue W), hψ, ?_, ?_, ?_⟩
  · intro x hx
    simp [(residue_eq_zero_iff x).2 hx]
  · rw [RingHom.comp_assoc, ← key]
    ext r
    have h1 := congrArg (fun f => f (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) hij
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 ⊢
    show i (α₀ (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) = _
    rw [h1]
    simp [g₀, gA, φ₀, IsFractionRing.lift_algebraMap]
  · rw [← key, spMap_comp']
    exact T₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusPart

theorem extend_torus_hom_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (G₁ : Over (Sp (FractionRing V))) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left),
    IsGrpPullback G₁ G (spMap (algebraMap V (FractionRing V))) φ₁ → Nonempty (TorusExtension G₁) →
    ∀ (Ω : Type) [Field Ω] (α : FractionRing V →+* Ω) (G' : Over (Sp Ω)) [GrpObj G'] (φ : G'.left ⟶ G.left)
      (h : IsGrpPullback G' G (spMap (α.comp (algebraMap V (FractionRing V)))) φ)
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp Ω) X ⟶ G'), IsMonHom i →
      ∃ j : splitTorus (Sp V) X ⟶ G, IsMonHom j ∧ GlobalTheory.TorusPart.pullTorus h j = i := by
  intro V _ _ _ G _ _ hG G₁ _ φ₁ h₁ hT Ω _ α G' _ φ h X _ _ _ i hi
  obtain ⟨T⟩ := hT
  letI := T.addCommGroup; letI := T.grpB
  haveI := T.free; haveI := T.finite
  have := T.i_hom; have := T.q_hom; have := T.isAbelian.proper
  set a := algebraMap V (FractionRing V)
  have ef : spMap (α.comp a) = spMap α ≫ spMap a := by
    rw [← Spec.map_comp]; rfl

  let ψ : G'.left ⟶ G₁.left := h₁.1.lift φ (G'.hom ≫ spMap α) (by
    rw [Category.assoc, ← ef]; exact h.1.w)
  have hψ : ψ ≫ φ₁ = φ := h₁.1.lift_fst _ _ _
  have h₂ : IsGrpPullback G' G₁ (spMap α) ψ :=
    h₁.cancel (h.congr ef hψ.symm) (h₁.1.lift_snd _ _ _)

  obtain ⟨q', hq', hk⟩ := exists_isKernel_pullTorus h₂ T.i T.q T.isKernel
  have : IsProper ((Over.pullback (spMap α)).obj T.B).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have hiq : i ≫ q' = toUnit _ ≫ η[(Over.pullback (spMap α)).obj T.B] :=
    splitTorus_hom_proper_trivial_local Ω X _ (i ≫ q') inferInstance
  have : Mono (pullTorus h₂ T.i) := ⟨fun x y e => hk.hom_ext e (toUnit_unique _ _)⟩
  let u' := hk.lift i (toUnit _) hiq
  have hu' : u' ≫ pullTorus h₂ T.i = i := hk.lift_fst _ _ _
  have : IsMonHom u' := Serre.isMonHom_of_mul_comp u' fun S x y => by
    rw [← cancel_mono (pullTorus h₂ T.i), MonObj.mul_comp (x ≫ u'), Category.assoc, Category.assoc,
      Category.assoc, hu', MonObj.mul_comp]
  haveI : ConnectedSpace (Sp Ω) := SplitTorus.connectedSpace_of_isLocalRing Ω
  obtain ⟨u, hu⟩ := SplitTorus.exists_eq_torusMap u'

  obtain ⟨e, he, heφ⟩ := grpPullback_iso h₁ (isGrpPullback_pullback G (spMap a))
  let j₁ : splitTorus (Sp (FractionRing V)) X ⟶ G₁ := SplitTorus.torusMap _ u ≫ T.i
  have : IsMonHom j₁ := inferInstance
  let f := (SplitTorus.bcIso (spMap a) X).inv ≫ j₁ ≫ e.hom
  have : IsMonHom f := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := homExtension_semiAbelian_dvr V (FractionRing V) (splitTorus (Sp V) X) G
    inferInstance hG f inferInstance
  refine ⟨F, hF, ?_⟩
  have hj₁ : pullTorus h₁ F = j₁ := by
    rw [eq_comm, eq_pullTorus_iff]
    have k : f.left ≫ pullback.fst G.hom (spMap a) =
        pullback.fst (splitTorus (Sp V) X).hom (spMap a) ≫ F.left := by
      rw [← hF']; exact pullback.lift_fst _ _ _
    have k2 := congrArg ((SplitTorus.bcIso (spMap a) X).hom.left ≫ ·) k
    simp only [f, Over.comp_left, Category.assoc, heφ] at k2
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp,
      SplitTorus.bcIso_hom_fst_assoc] at k2
    exact k2
  rw [← pullTorus_pullTorus h₂ h₁ h ef hψ.symm, hj₁, pullTorus_torusMap_comp, ← hu, hu']

end GlobalTheory.TorusPart
end
end

