import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0728
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFibreClassEqZeroOfSmulPullbackEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {q' : Y' ⟶ Sp R'} {χ : Y' ⟶ Y}
    (k : IsPullback χ q' q (spMap σ)) : IsClosedImmersion χ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) k.flip this

theorem tmul_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → CohomZeroIsConstants (OAff q') → ∀ (u : HO1 s₀) (y : HO1 s), TMul h₀.w t u y → pullHO1 w y = 0 → pullHO1 w₀ u = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀
    _hψ' hψ₀ hE _hs hq hC u y hT hy
  obtain ⟨hσ, hker, hσ₀, hker₀⟩ := hE
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_surj hσ k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_surj hσ₀ k₀
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_surj hσ₀ h₀
  have ht : σ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  obtain ⟨f, c, hcf, hcy, hred⟩ := hT

  have h1 : (pairPull w).pull1 y = 0 := by
    have e := isPullO_pullHO1 w y
    unfold IsPullO at e
    rw [e, hy, map_zero]
  rw [← hcy, CoefMap.pullCohomologyOne_class, GlobalTheory.CatCoh.H1.mk_eq_zero] at h1
  obtain ⟨g, hg⟩ := h1
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 (OPair ψ q), ∀ T T' (a : T ⟶ T'),
      f₁ T T' a = (pairPull w).α T' (f _ _ ((pairPull w).G.map a)) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hg' : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'), g T' - mp (OPair ψ q) a (g T) = t • f₁ T T' a := by
    intro T T' a
    have e := congrFun (congrFun (congrFun hg T) T') a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [e, hf₁, hcf, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, (pairPull w).smul, RingHom.id_apply]

  let gb : C0 (pairFst ψ ⋙ OPre χ q') := fun T ↦ preα χ q q' ((pairFst ψ).obj T) (g T)
  have hgb : d0 _ gb = 0 := by
    funext T T' a
    rw [amitsur_d0_apply]
    have nat : preα χ q q' _ (mp (OAff q) ((pairFst ψ).map a) (g T)) =
        mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) := (preCoef k.w).naturality _ _
    change preα χ q q' _ (g T') - mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) = 0
    rw [← nat]
    change preα χ q q' _ (g T') - preα χ q q' _ (mp (OPair ψ q) a (g T)) = 0
    have sm : ∀ U (r0 : R) b, preα χ q q' U (r0 • b) = σ r0 • preα χ q q' U b := (preCoef k.w).smul
    rw [← map_sub, hg', sm, ht, zero_smul]
  obtain ⟨r', hr', -⟩ := (GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion R' X Y Y' ψ χ q').2.2 hC gb hgb
  obtain ⟨r, rfl⟩ := hσ r'
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ⟨hσ, hker, hσ₀, hker₀⟩ hq
  have hex : ∀ T : (Pair ψ)ᵒᵖ, ∃ e, g T - algebraMap R _ r = t • e := by
    intro T
    refine ((hsec ((pairFst ψ).obj T)).2.1 _).1 ?_
    have e : preα χ q q' ((pairFst ψ).obj T) (algebraMap R ((OPair ψ q).obj T) r) =
        algebraMap R' ((pairFst ψ ⋙ OPre χ q').obj T) (σ r) :=
      SemiHom.map_algebraMap ((preCoef k.w).smul _) r
    rw [map_sub, e]
    exact sub_eq_zero.2 (hr' T)
  choose g₁ hg₁ using hex
  have hkill : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'),
      t • (f₁ T T' a - (g₁ T' - mp (OPair ψ q) a (g₁ T))) = 0 := by
    intro T T' a
    rw [smul_sub, smul_sub, ← map_smul (mp (OPair ψ q) a), ← hg₁ T', ← hg₁ T, map_sub, AlgHom.commutes,
      ← hg' T T' a]
    abel

  obtain ⟨c₀, hc₀, hc₀'⟩ :=
    (GlobalTheory.T.cohomologyClass_pullback_reduction_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hψ₀ inferInstance).1 f u hred
  have hz : (CoefMap.restrict (OAff q₀) (pairFst ψ ⋙ preAff χ₀)).pull1 (pullHO1 w₀ u) = 0 := by
    rw [← hc₀', GlobalTheory.CatCoh.H1.mk_eq_zero]
    refine ⟨fun T ↦ preα χ₀ q q₀ ((pairFst ψ).obj T) (g₁ T), ?_⟩
    funext T T' a
    rw [hc₀, amitsur_d0_apply, ← hf₁]
    have e1 := ((hsec ((pairFst ψ).obj T')).2.2.2 _).2 (hkill T T' a)
    rw [map_sub, map_sub, sub_eq_zero] at e1
    have nat : preα χ₀ q q₀ _ (mp (OAff q) ((pairFst ψ).map a) (g₁ T)) =
        mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) := (preCoef k₀.w).naturality _ _
    change _ - mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) = _
    rw [← nat]
    exact e1.symm
  exact (GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion R₀ X Y Y₀ ψ χ₀ q₀).1.1 (hz.trans (map_zero _).symm)

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftCuspidalVanishing
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_cusp_kills_of_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hnd hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F
  haveI := Fintype.ofFinite F'
  haveI : Fact (Module.finrank F F').Prime := ⟨hl⟩
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcard' : Nat.card F' = q ^ l := by
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F)]
  set K := k * ∑ i ∈ Finset.range l, q ^ (n * i) with hK_def
  obtain ⟨hregK, a, ha⟩ := GlobalTheory.T.regular_pair_lift_to_prime_power_field q l n k hq2 hl hn hnd hreg
  have hregK' : Reg (Nat.card F') n K := by rw [hcard']; exact hregK
  obtain ⟨hYchar, -⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F' θ hθ n K hn hregK'
  have hYs : ∀ g, cusp θ n K (galAct F F' n s g) = cusp θ n K g := by
    intro g
    obtain ⟨⟨i, hi⟩, hi'⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 s
    simp only at hi'
    obtain ⟨r, hp, hr⟩ := FiniteField.card F (ringChar F)
    have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
    have hsx : ∀ x, s.toRingEquiv x = x ^ (ringChar F' ^ ((r : ℕ) * i)) := by
      intro x
      change s x = _
      rw [← hi', AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hr, hchar, pow_mul]
    have h1 := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ s.toRingEquiv ((r : ℕ) * i) hsx n K g
    have hpq : ringChar F' ^ ((r : ℕ) * i) = q ^ i := by
      rw [hchar, pow_mul, ← hr, hq_def, Nat.card_eq_fintype_card]
    rw [hpq] at h1
    have hpow : ∀ j, K * q ^ j ≡ K * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
      intro j
      induction j with
      | zero => simp only [pow_zero, mul_zero, mul_one]; exact Nat.ModEq.refl _
      | succ j ih =>
        have e1 : K * q ^ (j + 1) = (K * q ^ j) * q := by ring
        have e2 : K * Nat.card F' ^ (a * (j + 1)) = (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) := by
          rw [hcard']; ring
        rw [e1, e2]
        calc K * q ^ j * q ≡ K * Nat.card F' ^ (a * j) * q [MOD Nat.card F' ^ n - 1] := ih.mul_right _
          _ = (K * q) * Nat.card F' ^ (a * j) := by ring
          _ ≡ (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
            apply Nat.ModEq.mul_right
            rw [hcard']; exact ha
    have h2 := GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq F' θ hθ n K (K * q ^ i) (a * i) hn (hpow i)
    rw [galAct_apply]
    exact h1.trans (congrFun h2 g)
  obtain ⟨X0, hX0, hX0a, hX0b⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc_def
  have hc2 : c * c = 1 := by rw [hc_def, ← mul_pow]; simp
  have hcstar : star c = c := by rw [hc_def]; simp
  set X : GHat F F' n → ℂ := fun x => c * X0 x with hX_def
  have hX : X ∈ Virt ℂ ℂ (GHat F F' n) := by
    have e : X = ((-1 : ℤ) ^ (n - 1)) • X0 := by
      funext x
      simp only [hX_def, Pi.smul_apply, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, hc_def]
    rw [e]
    exact AddSubgroup.zsmul_mem _ hX0 _
  have hfun : (fun δ => X (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := by
    funext δ
    simp only [hX_def, hX0b]
    by_cases h : ∃ γ, IsNorm s δ γ <;> simp [shLift, cusp, h, hc_def]
  have hcl : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    have := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y
    simp only [cusp]
    rw [this]
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy h
    apply hinj
    refine hθ _ _ ?_ ?_ h
    · exact fun h0 => hx (hinj (h0.trans (map_zero ι).symm))
    · exact fun h0 => hy (hinj (h0.trans (map_zero ι).symm))
  obtain ⟨-, hnormF⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hΓ : Nat.card (F' ≃ₐ[F] F') = l := IsGalois.card_aut_eq_finrank F F'
  have htop : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := fun t => by
    rw [zpowers_eq_top_of_prime_card hΓ hs]; trivial
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s htop n _ _ hcl hcl
  rw [hnormF] at hiso
  have hnorm : ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    have e : ∀ g, X (inl g * inr s) * star (X (inl g * inr s)) =
        shLift s (cusp (pullθ ι θ) n k) g * star (shLift s (cusp (pullθ ι θ) n k) g) := fun g => by
      rw [← congrFun hfun g]
    rw [finsum_congr e]
    have hpos : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    apply mul_left_cancel₀ hpos
    rw [hiso, mul_comm]
  set S : F'[X] → ℂ := fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) with hS_def
  have hS1 : S 1 = 0 := by
    simp only [hS_def, Polynomial.map_one]
    apply Finset.prod_eq_zero (Finset.mem_univ 1)
    simp [rootSum]
  have hSprod : S = fun P => ∏ j : Fin l, rootSum θ (k * q ^ (j : ℕ)) P := by
    funext P
    simp only [hS_def]
    rw [GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k P, Fin.prod_univ_eq_prod_range (fun j => rootSum θ (k * q ^ j) P) l]
  have hprim := GlobalTheory.T.psi_sum_eq_char_sum_against_cusp_form F' θ S n K hS1
  have hprod := GlobalTheory.T.primitiveFunctionCharpoly_pair_prod_rootSum F' θ hθ n K l (fun j => k * q ^ (j : ℕ)) hn
  rw [hcard'] at hprod
  set cnt := (Finset.univ.filter fun a : Fin l → Fin n =>
    K ≡ ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ n - 1]).card with hcnt_def
  have hcnt : cnt ≡ 1 [MOD l] := GlobalTheory.T.card_exponent_tuples_modEq_one_of_prime_not_dvd q l n k hq2 hl hn hnd hreg
  have hz : ∑ᶠ g, X (inl g) * star (cusp θ n K g) = ((cnt : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [finsum_eq_sum_of_fintype] at hprim hprod ⊢
    have e1 : ∀ g, X (inl g) * star (cusp θ n K g) = c * (psiG S n g * star (cusp θ n K g)) := fun g => by
      simp only [hX_def, hX0a]; ring
    rw [Finset.sum_congr rfl (fun g _ => e1 g), ← Finset.mul_sum, hprim]
    have e2 : ∀ g, chG S n g * star (cusp θ n K g) = star (cusp θ n K g * star (chG S n g)) := fun g => by
      rw [star_mul, star_star, mul_comm]
    rw [Finset.sum_congr rfl (fun g _ => e2 g), ← star_sum]
    have e3 : ∀ g, cusp θ n K g * star (chG S n g) = c * (psiG (rootSum θ K) n g * star (chG S n g)) :=
      fun g => by simp only [cusp, hc_def]; ring
    rw [Finset.sum_congr rfl (fun g _ => e3 g), ← Finset.mul_sum, hSprod, hprod, star_mul', hcstar, ← mul_assoc, hc2,
      one_mul, star_mul', star_natCast, star_natCast]
    push_cast
    ring
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (cnt : ℤ)) := by
    rw [hΓ, Int.natCast_dvd_natCast]
    intro h
    have h1 : cnt % l = 1 % l := hcnt
    rw [(Nat.dvd_iff_mod_eq_zero).1 h, Nat.mod_eq_of_lt hl.one_lt] at h1
    exact zero_ne_one h1
  have key := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X hX hnorm (cusp θ n K)
    hYchar hYs (cnt : ℤ) hz hndvd
  rw [hfun] at key
  exact key

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeEqTopOfLiftSemi
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem span_range_eq_top_of_liftSemi {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (f : M →ₛₗ[algebraMap R R'] M')
    (h : Function.Surjective (liftSemi f)) : Submodule.span R' (Set.range f) = ⊤ := by
  refine eq_top_iff.2 fun c _ ↦ ?_
  obtain ⟨z, rfl⟩ := h c
  induction z with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)
  | tmul x c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem liftSemi_comp_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M M' M'' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] [AddCommGroup M''] [Module R' M'']
    (f : M →ₛₗ[algebraMap R R'] M') (l : M' →ₗ[R'] M'') (k : M →ₛₗ[algebraMap R R'] M'')
    (e : ∀ c, l (f c) = k c) : ⇑(liftSemi k) = l ∘ liftSemi f := by
  funext z
  induction z with
  | zero => simp
  | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  | tmul x c => simp only [Function.comp_apply, liftSemi_tmul, map_smul, e]

theorem isBC_augmented : GlobalTheory.Published.AbelianDeRham.BaseChange → GlobalTheory.Published.AbelianDeRham.Rigid → ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  intro hB hR A₀ _ g hA hg D _ _ π κ hκ hπ k
  obtain ⟨A', _, q, i, hA', hg', hq, hi, e⟩ := GlobalTheory.T.abelian_scheme_deformation_complex A₀ g hA hg D π hπ
  have h1 : Function.Bijective (liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor hq).pull) :=
    (hB ℂ A₀ g hA hg D A' q hq).1
  have h2 := hR D A' g hA' hg' _ κ hκ ℂ π (fun a ↦ ⟨_, hπ a⟩) rfl A₀ i hi
  have h3 : Function.Bijective (liftSemi k.pull) := by
    rw [liftSemi_comp_eq (GlobalTheory.Published.AbelianDeRham.bcMor hq).pull (liftMor κ hi).pull k.pull
      (GrpMor.pull_pull _ _ k (fun _ ↦ rfl) e)]
    exact h2.comp h1
  exact ⟨h3, span_range_eq_top_of_liftSemi _ h3.2⟩

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryNearOneEqChartMulStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitary_near_one_eq_chart_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), IsOrth X x → 0 < ρ → σ 0 = 1 → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∃ w : ChartSp X, ‖w‖ < δ ∧ σ w.1 * t w.2 = g := by
  first | exact @GlobalTheory.eq_chart_mul_of_near_one | exact GlobalTheory.eq_chart_mul_of_near_one | (intros; apply GlobalTheory.eq_chart_mul_of_near_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormSmoothSectionSubGluedLeStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.n0_sub_glue_le_card_mul_sum_lintegral : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n0 A la (F0 - glue C la u) ≤ (C.m : ℝ≥0∞) * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  first | exact @GlobalTheory.GlueDist.sq_norm_smoothSection_sub_glued_le | exact GlobalTheory.GlueDist.sq_norm_smoothSection_sub_glued_le | (intros; apply GlobalTheory.GlueDist.sq_norm_smoothSection_sub_glued_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomial
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens {A B : Type} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (maximalIdeal B).comap f = maximalIdeal A := by
  ext x
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

open IsLocalRing Polynomial in
open scoped TensorProduct in
private lemma locPiecesEtale_localization_atPrime {R A : Type} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] :
    _root_.GlobalTheory.LocAcyc.LocPiecesEtale R (Localization.AtPrime q) := by
  unfold _root_.GlobalTheory.LocAcyc.LocPiecesEtale
  exact ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
    fun _ => ⟨(), Algebra.mem_top⟩, fun _ => ⟨A, inferInstance, inferInstance, inferInstance, q,
      inferInstance, ⟨Subalgebra.topEquiv.symm⟩⟩⟩

open IsLocalRing Polynomial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.strictHenselisation_etale_over_polynomial : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S)
      (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  intro T E _ _ _ _ _ _ _ _ y _
  obtain ⟨S, _, _, _, _, hsep, hflat, -, -, hpieces⟩ := _root_.GlobalTheory.exists_strictHenselisation
    (Localization.AtPrime y) (SeparableClosure (ResidueField (Localization.AtPrime y)))
  haveI := hsep
  have hP : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Localization.AtPrime y) S := hpieces
  letI : Algebra E S :=
    ((algebraMap (Localization.AtPrime y) S).comp (algebraMap E (Localization.AtPrime y))).toAlgebra
  letI : Algebra T S := ((algebraMap E S).comp (algebraMap T E)).toAlgebra
  letI : Algebra (Polynomial T) S := ((algebraMap E S).comp (algebraMap (Polynomial T) E)).toAlgebra
  haveI : IsScalarTower E (Localization.AtPrime y) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (Polynomial T) E S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T (Polynomial T) S := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E S (algebraMap T E x) =
      algebraMap E S (algebraMap (Polynomial T) E (algebraMap T (Polynomial T) x))
    exact congrArg _ (IsScalarTower.algebraMap_apply T (Polynomial T) E x)
  haveI : IsScalarTower (Polynomial T) (Localization.AtPrime y) S :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap (Localization.AtPrime y) S (algebraMap E (Localization.AtPrime y)
          (algebraMap (Polynomial T) E x)) =
        algebraMap (Localization.AtPrime y) S (algebraMap (Polynomial T) (Localization.AtPrime y) x)
      exact congrArg _ (IsScalarTower.algebraMap_apply (Polynomial T) E (Localization.AtPrime y) x).symm
  have hcomap : (maximalIdeal S).comap (algebraMap E S) = y := by
    rw [IsScalarTower.algebraMap_eq E (Localization.AtPrime y) S, ← Ideal.comap_comap,
      _root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
    exact Localization.AtPrime.comap_maximalIdeal ..
  haveI : Module.Flat E (Localization.AtPrime y) := IsLocalization.flat _ y.primeCompl
  haveI := hflat
  have hflatE : Module.Flat E S := Module.Flat.trans E (Localization.AtPrime y) S
  have hpiecesE : _root_.GlobalTheory.LocAcyc.LocPiecesEtale E S :=
    _root_.GlobalTheory.indEtale_localPieces_trans E (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := E) (A := E) y) hP
  have hpiecesT : _root_.GlobalTheory.LocAcyc.LocPiecesEtale (Polynomial T) S :=
    _root_.GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) S
      (locPiecesEtale_localization_atPrime (R := Polynomial T) (A := E) y) hP
  obtain ⟨P, _, φ, hφc, hφs⟩ := _root_.GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T S hpiecesT
  have hPy : P = y.comap (algebraMap (Polynomial T) E) := by
    haveI : IsLocalHom φ := hφs.2.2.1
    calc P = ((maximalIdeal S).comap φ).comap (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
          rw [_root_.GlobalTheory.comap_maximalIdeal_of_localHom_strictHens]
          exact (Localization.AtPrime.comap_maximalIdeal ..).symm
      _ = (maximalIdeal S).comap (algebraMap (Polynomial T) S) := by
          rw [Ideal.comap_comap, hφc]
      _ = y.comap (algebraMap (Polynomial T) E) := by
          rw [IsScalarTower.algebraMap_eq (Polynomial T) E S, ← Ideal.comap_comap, hcomap]
  subst hPy
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcomap, hflatE, hpiecesE, φ, hφc, hφs⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubInStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) → In (J * N) (subst (up Q u) f - subst (up Q v) f) := by
  first | exact @GlobalTheory.KatzCongr.subst_sub_in | exact GlobalTheory.KatzCongr.subst_sub_in | (intros; apply GlobalTheory.KatzCongr.subst_sub_in <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCupOneFormsZeroImpCoordinatesZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • toO F (a k) = 0 := by
  first | exact @GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup | exact GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup | (intros; apply GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
section
noncomputable section
namespace GlobalTheory.FockParts
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.FockDeg

variable {p q r s : ℕ}

theorem sum_lineMatrixKroneckerLeftFactor (Z : Mat p q) (F : Ln p q r s → Ln p q r s → ℂ → Pol p q r s)
    (hF : ∀ l l', F l l' 0 = 0) :
    ∑ l, ∑ l', F l l' (kr1 r s Z l l') = ∑ a, ∑ b, ∑ c, F (a, c) (b, c) (Z a b) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (f := fun b c => F (a, c) (b, c) (Z a b))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single c]
  · simp [kr1]
  · intro d _ hd
    simp [kr1, Ne.symm hd, hF]
  · simp

theorem sum_lineMatrixKroneckerRightFactor (Z : Mat r s) (F : Ln p q r s → Ln p q r s → ℂ → Pol p q r s)
    (hF : ∀ l l', F l l' 0 = 0) :
    ∑ l, ∑ l', F l l' (kr2 p q Z l l') = ∑ c, ∑ d, ∑ a, F (a, c) (a, d) (Z c d) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm (f := fun d a => F (a, c) (a, d) (Z c d))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [kr2]
  · intro b _ hb
    simp [kr2, Ne.symm hb, hF]
  · simp

theorem explicit_parts : ∀ (p q r s : ℕ), (∀ Z : Mat p q, IsPC Z → ∀ P : Pol p q r s, plusPart (fockAct1 p q r s Z) P = ∑ a, ∑ b, ∑ c, (if linePos ((a, c) : Ln p q r s) = true then Z a b • (X (a, c) * X (b, c) * P) else 0) ∧ minusPart (fockAct1 p q r s Z) P = ∑ a, ∑ b, ∑ c, (if linePos ((a, c) : Ln p q r s) = true then 0 else -(Z a b • pderiv (a, c) (pderiv (b, c) P)))) ∧ (∀ Z : Mat r s, IsPC Z → ∀ P : Pol p q r s, plusPart (fockAct2 p q r s Z) P = ∑ c, ∑ d, ∑ a, (if linePos ((a, c) : Ln p q r s) = true then Z c d • (X (a, c) * X (a, d) * P) else 0) ∧ minusPart (fockAct2 p q r s Z) P = ∑ c, ∑ d, ∑ a, (if linePos ((a, c) : Ln p q r s) = true then 0 else -(Z c d • pderiv (a, c) (pderiv (a, d) P)))) := by
  intro p q r s
  refine ⟨fun Z hZ P => ⟨?_, ?_⟩, fun Z hZ P => ⟨?_, ?_⟩⟩
  · rw [fockAct1_eq, plusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ), upOp_apply,
      sum_lineMatrixKroneckerLeftFactor Z (fun l l' z => (if linePos l then z else 0) • (X l * X l' * P)) (by simp)]
    simp only [ite_smul, zero_smul]
  · rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ), downOp_apply,
      sum_lineMatrixKroneckerLeftFactor Z (fun l l' z => (if linePos l then 0 else -z) • pderiv l (pderiv l' P)) (by simp)]
    simp only [ite_smul, zero_smul, neg_smul]
  · rw [fockAct2_eq, plusPart_omAct (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ), upOp_apply,
      sum_lineMatrixKroneckerRightFactor Z (fun l l' z => (if linePos l then z else 0) • (X l * X l' * P)) (by simp)]
    simp only [ite_smul, zero_smul]
  · rw [fockAct2_eq, minusPart_omAct (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ), downOp_apply,
      sum_lineMatrixKroneckerRightFactor Z (fun l l' z => (if linePos l then 0 else -z) • pderiv l (pderiv l' P)) (by simp)]
    simp only [ite_smul, zero_smul, neg_smul]

end GlobalTheory.FockParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgeGlobalOneFormsEqZeroIffStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumWedgeGlobalOneForms_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  first | exact @GlobalTheory.AbCoh.wsum_eq_zero_iff | exact GlobalTheory.AbCoh.wsum_eq_zero_iff | (intros; apply GlobalTheory.AbCoh.wsum_eq_zero_iff <;> assumption)
end

