import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneGeneratedOfSplitIdempotent
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.NormOneSplit

open Polynomial in

theorem exists_good {K : Type} [Field K] [CharZero K] (a p q : K) (ha : a ≠ 0) :
    ∃ m : K, m ≠ 0 ∧ a - m * p ≠ 0 ∧ a - m⁻¹ * q ≠ 0 ∧ 2 * a - m * p - m⁻¹ * q ≠ 0 := by
  set P1 : K[X] := C a - C p * X with hP1
  set P2 : K[X] := C a * X - C q with hP2
  set P3 : K[X] := C (2 * a) * X - C p * X ^ 2 - C q with hP3
  have h1 : P1 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 0) h
    simp [hP1] at this
    exact ha this
  have h2 : P2 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 1) h
    simp [hP2, Polynomial.coeff_X, Polynomial.coeff_C] at this
    exact ha this
  have h3 : P3 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 1) h
    simp [hP3, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at this
    exact ha this
  have hP : (X * P1 * P2 * P3 : K[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero X_ne_zero h1) h2) h3
  have hex : ∃ m : K, (X * P1 * P2 * P3 : K[X]).eval m ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hP (Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_univ.mono fun m _ => hcon m))
  obtain ⟨m, hm⟩ := hex
  simp only [eval_mul, eval_X] at hm
  have hm0 : m ≠ 0 := fun h => hm (by simp [h])
  have e1 : a - m * p ≠ 0 := by
    intro h
    apply hm
    have : eval m P1 = 0 := by simp [hP1]; linear_combination h
    simp [this]
  have e2 : a * m - q ≠ 0 := by
    intro h
    apply hm
    have : eval m P2 = 0 := by simp [hP2]; linear_combination h
    simp [this]
  have e3 : 2 * a * m - p * m ^ 2 - q ≠ 0 := by
    intro h
    apply hm
    have : eval m P3 = 0 := by simp [hP3]; linear_combination h
    simp [this]
  refine ⟨m, hm0, e1, ?_, ?_⟩
  · intro h
    apply e2
    have : a * m - q = m * (a - m⁻¹ * q) := by field_simp
    rw [this, h, mul_zero]
  · intro h
    apply e3
    have : 2 * a * m - p * m ^ 2 - q = m * (2 * a - m * p - m⁻¹ * q) := by field_simp
    rw [this, h, mul_zero]

section Ring

variable {K R : Type} [Field K] [CharZero K] [CommRing R] [Nontrivial R] [Algebra K R]

theorem normOneGen_of_idem (c : R →+* R) (hK : ∀ a : K, c (algebraMap K R a) = algebraMap K R a)
    (e : R) (he : e * e = e) (hs : e + c e = 1) (hz : e * c e = 0)
    (hsp : ∀ r : R, ∃ a b : K, r = algebraMap K R a * e + algebraMap K R b * c e) :
    NormOneGen c := by
  set f := c e with hf
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hcf : c f = e := by
    have h := congrArg c hs
    rw [map_add, map_one] at h
    have : c f = 1 - f := by rw [← h]; ring
    rw [this, ← hs]; ring
  have he0 : e ≠ 0 := by
    intro h
    have hf0 : f = 0 := by rw [hf, h, map_zero]
    rw [h, hf0, add_zero] at hs
    exact zero_ne_one hs
  have hinj : ∀ x : K, algebraMap K R x * e = 0 → x = 0 := by
    intro x hx
    by_contra hne
    apply he0
    calc e = algebraMap K R (x⁻¹ * x) * e := by rw [inv_mul_cancel₀ hne, map_one, one_mul]
      _ = algebraMap K R x⁻¹ * (algebraMap K R x * e) := by rw [map_mul]; ring
      _ = 0 := by rw [hx, mul_zero]
  have hunit : ∀ x y : K, x ≠ 0 → y ≠ 0 → IsUnit (algebraMap K R x * e + algebraMap K R y * f) := by
    intro x y hx hy
    refine IsUnit.of_mul_eq_one (algebraMap K R x⁻¹ * e + algebraMap K R y⁻¹ * f) ?_
    have h1 : algebraMap K R x * algebraMap K R x⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    have h2 : algebraMap K R y * algebraMap K R y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hy, map_one]
    calc _ = (algebraMap K R x * algebraMap K R x⁻¹) * (e * e)
          + (algebraMap K R y * algebraMap K R y⁻¹) * (f * f)
          + (algebraMap K R x * algebraMap K R y⁻¹ + algebraMap K R y * algebraMap K R x⁻¹) * (e * f) := by ring
      _ = 1 := by rw [h1, h2, he, hff, hz, mul_zero, add_zero, one_mul, one_mul]; exact hs
  intro α p hα hcα
  obtain ⟨a, b, hab⟩ := hsp α
  obtain ⟨p₁, p₂, hp⟩ := hsp p
  have hba : a = b := by
    have h := hcα
    rw [hab, map_add, map_mul, map_mul, hK, hK, hcf, ← hf] at h
    have h' := congrArg (fun t => t * e) h
    have : algebraMap K R (a - b) * e = 0 := by
      rw [map_sub]
      linear_combination (-1 : R) * h' + (algebraMap K R b - algebraMap K R a) * he
        + (algebraMap K R a - algebraMap K R b) * hz
    exact sub_eq_zero.1 (hinj _ this)
  subst hba
  have ha : a ≠ 0 := by
    rintro rfl
    have h0 : α * e = 0 := by
      rw [hab, map_zero, zero_mul, zero_mul, add_zero, zero_mul]
    exact he0 (hα.mul_right_eq_zero.1 h0)
  obtain ⟨m, hm, c1, c2, c3⟩ := exists_good a p₁ p₂ ha
  have hmm : algebraMap K R m * algebraMap K R m⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hm, map_one]
  have hμp : (algebraMap K R m * e + algebraMap K R m⁻¹ * f) * p =
      algebraMap K R (m * p₁) * e + algebraMap K R (m⁻¹ * p₂) * f := by
    rw [hp, map_mul, map_mul]
    linear_combination (algebraMap K R m * algebraMap K R p₁) * he +
      (algebraMap K R m⁻¹ * algebraMap K R p₂) * hff +
      (algebraMap K R m * algebraMap K R p₂ + algebraMap K R m⁻¹ * algebraMap K R p₁) * hz
  refine ⟨algebraMap K R m * e + algebraMap K R m⁻¹ * f, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, hK, hcf]
    rw [← hf]
    linear_combination (algebraMap K R m * algebraMap K R m⁻¹) * he +
      (algebraMap K R m * algebraMap K R m⁻¹) * hff +
      (algebraMap K R m ^ 2 + algebraMap K R m⁻¹ ^ 2) * hz + (e + f) * hmm + hs
  · rw [hμp, hab]
    have := hunit (a - m * p₁) (a - m⁻¹ * p₂) c1 c2
    convert this using 1
    simp only [map_sub]; ring
  · rw [hμp, hab]
    simp only [map_add, map_mul, hK, hcf]
    have := hunit (2 * a - m * p₁ - m⁻¹ * p₂) (2 * a - m * p₁ - m⁻¹ * p₂) c3 c3
    convert this using 1
    simp only [map_sub, map_mul, map_ofNat]; ring

end Ring

end GlobalTheory.CompanionTheory.SaGen.NormOneSplit

open GlobalTheory.CompanionTheory.SaGen.NormOneSplit in

theorem GlobalTheory.CompanionTheory.SaGen.normOneGen_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → NormOneGen (sigR K σ) := by
  intro F E _ _ _ _ _ σ hcm K _ _ e he hs hz
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hrank : Module.finrank K (K ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hcm.2.2.1
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hK : ∀ a : K, sigR K σ (algebraMap K (K ⊗[F] E) a) = algebraMap K (K ⊗[F] E) a := by
    intro a
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  refine normOneGen_of_idem (K := K) (sigR K σ) hK e he hs hz ?_
  set f := sigR K σ e with hf
  have he0 : e ≠ 0 := by
    intro h
    have hf0 : f = 0 := by rw [hf, h, map_zero]
    rw [h, hf0, add_zero] at hs
    exact zero_ne_one hs
  have hf0 : f ≠ 0 := by
    intro h
    have h1 : e = 1 := by rw [h, add_zero] at hs; exact hs
    have : f = 1 := by rw [hf, h1, map_one]
    rw [this] at h
    exact one_ne_zero h
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hli : LinearIndependent K ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def] at hst
    have h1 : algebraMap K (K ⊗[F] E) s * e = 0 := by
      linear_combination e * hst - algebraMap K (K ⊗[F] E) s * he - algebraMap K (K ⊗[F] E) t * hz
    have h2 : algebraMap K (K ⊗[F] E) t * f = 0 := by
      linear_combination f * hst - algebraMap K (K ⊗[F] E) s * hz - algebraMap K (K ⊗[F] E) t * hff
    have key : ∀ (x : K) (y : K ⊗[F] E), y ≠ 0 → algebraMap K (K ⊗[F] E) x * y = 0 → x = 0 := by
      intro x y hy hxy
      by_contra hx
      apply hy
      calc y = algebraMap K (K ⊗[F] E) (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx, map_one, one_mul]
        _ = algebraMap K (K ⊗[F] E) x⁻¹ * (algebraMap K (K ⊗[F] E) x * y) := by rw [map_mul]; ring
        _ = 0 := by rw [hxy, mul_zero]
    exact ⟨key s e he0 h1, key t f hf0 h2⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp [hrank])
  intro r
  have hr : r ∈ Submodule.span K (Set.range ![e, f]) := by rw [htop]; trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hr
  obtain ⟨a, b, hab⟩ := hr
  exact ⟨a, b, by rw [← hab, Algebra.smul_def, Algebra.smul_def]⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeCriterion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Krull

theorem stalkMap_germ_appLE {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) (W : Y.Opens) (U : Z.Opens)
    (h : U ≤ ψ ⁻¹ᵁ W) (z : Z) (hz : z ∈ U) (hy : ψ z ∈ W) (a : Γ(Y, W)) :
    ψ.stalkMap z (Y.presheaf.germ W (ψ z) hy a) = Z.presheaf.germ U z hz (ψ.appLE W U h a) := by
  simp [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]

theorem isUnit_germ_fromSpec {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (c : Γ(Z, U)) :
    IsUnit (Z.presheaf.germ U _ hz c) ↔ c ∉ q.asIdeal := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (hU.fromSpec q)) := (Z.presheaf.germ U _ hz).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal := hU.isLocalization_stalk' q hz
  rw [← Ideal.mem_primeCompl_iff]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal c

theorem exists_mul_eq_of_germ_eq {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (c d : Γ(Z, U))
    (e : Z.presheaf.germ U _ hz c = Z.presheaf.germ U _ hz d) :
    ∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * c = v * d := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (hU.fromSpec q)) := (Z.presheaf.germ U _ hz).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal := hU.isLocalization_stalk' q hz
  obtain ⟨⟨v, hv⟩, hvcd⟩ :=
    (IsLocalization.eq_iff_exists q.asIdeal.primeCompl (Z.presheaf.stalk (hU.fromSpec q))).mp e
  exact ⟨v, hv, hvcd⟩

theorem exists_frac_stalk {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (y : Y) (hy : y ∈ W)
    (s : Y.presheaf.stalk y) :
    ∃ a u : Γ(Y, W), IsUnit (Y.presheaf.germ W y hy u) ∧
      s * Y.presheaf.germ W y hy u = Y.presheaf.germ W y hy a := by
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨a, u⟩, hs⟩ := IsLocalization.surj (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl s
  exact ⟨a, u.1, IsLocalization.map_units (Y.presheaf.stalk y) u, hs⟩

theorem exists_mul_eq_zero_of_germ {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (y : Y)
    (hy : y ∈ W) (a : Γ(Y, W)) (e : Y.presheaf.germ W y hy a = 0) :
    ∃ u : Γ(Y, W), IsUnit (Y.presheaf.germ W y hy u) ∧ u * a = 0 := by
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨u, hu⟩, hua⟩ :=
    (IsLocalization.map_eq_zero_iff (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) a).mp e
  exact ⟨u, IsLocalization.map_units (Y.presheaf.stalk y) (⟨u, hu⟩ : (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), hua⟩

theorem isIso_stalkMap_of_isIso_restrict {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) (W : Y.Opens)
    (h : IsIso (ψ ∣_ W)) (z : Z) (hz : z ∈ ψ ⁻¹ᵁ W) : IsIso (ψ.stalkMap z) := by
  haveI : IsIso ((ψ ∣_ W).stalkMap ⟨z, hz⟩) := by
    first
    | infer_instance
    | (haveI : IsOpenImmersion (ψ ∣_ W) := inferInstance; infer_instance)
    | (haveI : IsOpenImmersion (ψ ∣_ W) := IsOpenImmersion.of_isIso _; infer_instance)
    | exact PresheafedSpace.IsOpenImmersion.stalk_iso (ψ ∣_ W).toPshHom ⟨z, hz⟩
  have e := morphismRestrictStalkMap ψ W ⟨z, hz⟩
  show IsIso (ψ.stalkMap (⟨z, hz⟩ : (ψ ⁻¹ᵁ W : Z.Opens)).1)
  rw [Arrow.iso_w' e]
  infer_instance

theorem chart_fractions_of_isIso_stalkMap {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) {U : Z.Opens} (hU : IsAffineOpen U) (h : U ≤ ψ ⁻¹ᵁ W)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (hiso : IsIso (ψ.stalkMap (hU.fromSpec q))) :
    (∀ c : Γ(Z, U), ∃ a u : Γ(Y, W), ψ.appLE W U h u ∉ q.asIdeal ∧
      ∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * (ψ.appLE W U h u * c) = v * ψ.appLE W U h a) ∧
    (∀ a : Γ(Y, W), (∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * ψ.appLE W U h a = 0) →
      ∃ u : Γ(Y, W), ψ.appLE W U h u ∉ q.asIdeal ∧ u * a = 0) := by
  have hy : ψ (hU.fromSpec q) ∈ W := h hz
  have hbij := (ConcreteCategory.isIso_iff_bijective (ψ.stalkMap (hU.fromSpec q))).mp hiso
  constructor
  · intro c
    obtain ⟨s, hs0⟩ := hbij.2 (Z.presheaf.germ U _ hz c)
    obtain ⟨a, u, hu, hs⟩ := exists_frac_stalk hW (ψ (hU.fromSpec q)) hy s
    have hs' := congrArg (ψ.stalkMap (hU.fromSpec q)) hs
    rw [map_mul, hs0, stalkMap_germ_appLE ψ W U h _ hz hy u, stalkMap_germ_appLE ψ W U h _ hz hy a] at hs'
    have hu' : IsUnit (Z.presheaf.germ U _ hz (ψ.appLE W U h u)) := by
      rw [← stalkMap_germ_appLE ψ W U h _ hz hy u]
      exact hu.map _
    rw [isUnit_germ_fromSpec hU q hz] at hu'
    refine ⟨a, u, hu', ?_⟩
    apply exists_mul_eq_of_germ_eq hU q hz
    rw [map_mul, mul_comm, hs']
  · rintro a ⟨v, hv, hva⟩
    have h0 : Z.presheaf.germ U _ hz (ψ.appLE W U h a) = 0 := by
      have hvu : IsUnit (Z.presheaf.germ U _ hz v) := (isUnit_germ_fromSpec hU q hz v).mpr hv
      have hh := congrArg (Z.presheaf.germ U _ hz) hva
      rw [map_mul, map_zero] at hh
      exact hvu.mul_right_eq_zero.mp hh
    have h1 : Y.presheaf.germ W _ hy a = 0 := by
      apply hbij.1
      rw [map_zero, stalkMap_germ_appLE ψ W U h _ hz hy a, h0]
    obtain ⟨u, hu, hua⟩ := exists_mul_eq_zero_of_germ hW _ hy a h1
    refine ⟨u, ?_, hua⟩
    rw [← isUnit_germ_fromSpec hU q hz, ← stalkMap_germ_appLE ψ W U h _ hz hy u]
    exact hu.map _

theorem chart_fractions_subscheme {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}}
    (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V))
    (hiso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f))) (U : Z.Opens) (hU : IsAffineOpen U)
    (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V) (q : Ideal Γ(Z, U)) (hq : q.IsPrime)
    (hf : (ψ ≫ J.subschemeι).appLE V U h f ∉ q) :
    (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t ∉ q ∧
      ∃ v : Γ(Z, U), v ∉ q ∧ v * ((ψ ≫ J.subschemeι).appLE V U h t * c) =
        v * (ψ ≫ J.subschemeι).appLE V U h b) ∧
    (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * (ψ ≫ J.subschemeι).appLE V U h b = 0) →
      ∃ t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t ∉ q ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  let p : PrimeSpectrum Γ(Z, U) := ⟨q, hq⟩
  have hz : hU.fromSpec p ∈ (U : Set Z) := by
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self _
  have hunit : IsUnit (Z.presheaf.germ U _ hz ((ψ ≫ J.subschemeι).appLE V U h f)) :=
    (isUnit_germ_fromSpec hU p hz _).mpr hf
  have hb : hU.fromSpec p ∈ Z.basicOpen ((ψ ≫ J.subschemeι).appLE V U h f) :=
    (Z.mem_basicOpen _ _ hz).mpr hunit
  have e1 : Z.basicOpen ((ψ ≫ J.subschemeι).appLE V U h f) =
      U ⊓ Z.basicOpen ((ψ ≫ J.subschemeι).app V f) := Z.basicOpen_res _ (homOfLE h).op
  have hb2 : hU.fromSpec p ∈ Z.basicOpen ((ψ ≫ J.subschemeι).app V f) :=
    (TopologicalSpace.Opens.mem_inf.mp (e1 ▸ hb)).2
  have e2 := Scheme.preimage_basicOpen (ψ ≫ J.subschemeι) f
  have hmem : hU.fromSpec p ∈ ψ ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ X.basicOpen f) := by
    have hh : hU.fromSpec p ∈ (ψ ≫ J.subschemeι) ⁻¹ᵁ X.basicOpen f := e2 ▸ hb2
    exact hh
  have hist : IsIso (ψ.stalkMap (hU.fromSpec p)) := isIso_stalkMap_of_isIso_restrict ψ _ hiso _ hmem
  have hW' : IsAffineOpen (J.subschemeι ⁻¹ᵁ V) := hV.preimage J.subschemeι
  obtain ⟨H1, H2⟩ := chart_fractions_of_isIso_stalkMap ψ hW' hU h p hz hist
  have hce : ∀ t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t =
      ψ.appLE (J.subschemeι ⁻¹ᵁ V) U h (J.subschemeι.app V t) := by
    intro t
    rw [Scheme.Hom.comp_appLE]
    rfl
  have hsurj := J.subschemeι_app_surjective ⟨V, hV⟩
  constructor
  · intro c
    obtain ⟨a, u, hu, v, hv, hvc⟩ := H1 c
    obtain ⟨b, rfl⟩ := hsurj a
    obtain ⟨t, rfl⟩ := hsurj u
    refine ⟨b, t, ?_, v, hv, ?_⟩
    · rw [hce]
      exact hu
    · rw [hce, hce]
      exact hvc
  · rintro b ⟨v, hv, hvb⟩
    rw [hce] at hvb
    obtain ⟨u, hu, hub⟩ := H2 (J.subschemeι.app V b) ⟨v, hv, hvb⟩
    obtain ⟨t, rfl⟩ := hsurj u
    refine ⟨t, ?_, ?_⟩
    · rw [hce]
      exact hu
    · rw [← J.ker_subschemeι_app ⟨V, hV⟩, RingHom.mem_ker, map_mul]
      exact hub

theorem stalk_over_isoLocus : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ q : Ideal Γ(Z, U), q.IsPrime → f ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) → (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ ∃ v : Γ(Z, U), v ∉ q ∧ v * (algebraMap Γ(X, V) Γ(Z, U) t * c) = v * algebraMap Γ(X, V) Γ(Z, U) b) ∧ (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * algebraMap Γ(X, V) Γ(Z, U) b = 0) → ∃ t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  intro X J Z ψ V hV f hiso U hU h q hq hf
  exact chart_fractions_subscheme J ψ V hV f hiso U hU h q hq hf

end GlobalTheory.CompanionTheory.GE.Krull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct
open TopologicalSpace Opposite

namespace GlobalTheory.CompanionTheory.GE.PushCoh

abbrev overAffine {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) :
    (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) :=
  ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩

attribute [local instance] algebraOfOver

lemma algebraMap_overAffine {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (b : Γ(X, V)) :
    letI := overAffine φ hV
    Z.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      φ.app V b := by
  letI := overAffine φ hV
  have s1 : algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b = (φ ∣_ V).appTop (V.topIso.inv b) := by
    change (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (RelSerre.app_eqToHom_apply φ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp

def zerothCohomologyToSections {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) (M : Z.Modules) :
    letI := overAffine φ hV
    Sheaf.H.{0} (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward φ).obj M, V) :=
  letI := overAffine φ hV
  { toFun := fun x => M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (Sheaf.H.equiv₀ (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x :
        Γ(M, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
    map_add' := fun x y => by
      rw [map_add]
      exact map_add _ _ _
    map_smul' := fun b x => by
      rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
      refine (RelSerre.smul_restrict_top M (φ ⁻¹ᵁ V) _ _).trans ?_
      refine (congrArg (· • _) (algebraMap_overAffine φ hV b)).trans ?_
      exact (smul_pushforward φ M b _).symm }

lemma zeroth_cohomology_to_sections_surjective {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (M : Z.Modules) : Function.Surjective (zerothCohomologyToSections φ hV M) := by
  letI := overAffine φ hV
  exact ((ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op)).comp
    (Sheaf.H.equiv₀ (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop).bijective).2

theorem isCoherent_pushforward_of_isProper {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X)
    (hφ : IsProper φ) {G : Z.Modules} (hG : IsCoherent G) :
    IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  haveI := hG.1
  refine ⟨isQuasicoherent_pushforward_of_qcqs φ G, fun V hV => ?_⟩
  letI := overAffine φ hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : IsProper ((φ ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(X, V))) := by
    change IsProper (φ ∣_ V ≫ hV.isoSpec.hom)
    infer_instance
  have hfin := finite_H_of_isProper (A := Γ(X, V)) (G.restrict (φ ⁻¹ᵁ V).ι) (hG.restrict _) 0
  exact Module.Finite.of_surjective (zerothCohomologyToSections φ hV G) (zeroth_cohomology_to_sections_surjective φ hV G)

end GlobalTheory.CompanionTheory.GE.PushCoh

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionAnisotropicTrace
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem anis_trace_sq_sub_four_ne_sq :
    ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 →
      (∀ x : Q d β K, qn x = 0 → x = 0) → ∀ b : Q d β K, qn b = 1 → b.re ^ 2 ≠ 1 →
      ∀ r : K, r ^ 2 ≠ (2 * b.re) ^ 2 - 4 := by
  intro F K _ _ _ d β h2 han b hb hre r hr
  have hz : qn (⟨r, 2 * b.imI, 2 * b.imJ, 2 * b.imK⟩ : Q d β K) = 0 := by
    simp only [qn] at hb ⊢
    linear_combination hr + 4 * hb
  have h0 := han _ hz
  have hI : b.imI = 0 := by
    have := congrArg QuaternionAlgebra.imI h0
    simpa [h2] using this
  have hJ : b.imJ = 0 := by
    have := congrArg QuaternionAlgebra.imJ h0
    simpa [h2] using this
  have hK : b.imK = 0 := by
    have := congrArg QuaternionAlgebra.imK h0
    simpa [h2] using this
  apply hre
  simpa [qn, hI, hJ, hK] using hb

end GlobalTheory.CompanionTheory.PlaneSA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientFiltrationBijectiveOfCoverStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_filtration_bijective_of_cover : KH.KIso → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (U : Cov q) (s u : ℕ), (∀ α, U.d α < u) → u ≤ s → ∀ (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ (j : ℕ),
    Function.Bijective (quoK q (KS q s 𝒱) (u : ℤ) j) := by
  first | exact @GlobalTheory.CompanionTheory.QuoK.quoK_bijective | exact GlobalTheory.CompanionTheory.QuoK.quoK_bijective | (intros; apply GlobalTheory.CompanionTheory.QuoK.quoK_bijective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_pullback_sections : ∀ {X : Scheme.{0}} {E : X.Modules} (D S : Subobject E) (V : X.Opens), secs ((Subobject.pullback D.arrow).obj S) V = (D.arrow.app V) ⁻¹' secs S V := by
  first | exact @GlobalTheory.CompanionTheory.GE.secs_pullback_arrow | exact GlobalTheory.CompanionTheory.GE.secs_pullback_arrow | (intros; apply GlobalTheory.CompanionTheory.GE.secs_pullback_arrow <;> assumption)
end

