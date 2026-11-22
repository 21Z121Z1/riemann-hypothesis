import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsBaseTwoWords
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumerator
section
set_option autoImplicit false

namespace GlobalTheory.ScalarUnit

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open scoped nonZeroDivisors

section Ideals

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem smul_eq_idlE_mul (J : Ideal (𝓞 E)) (M : Submodule (𝓞 E) E) : J • M = idlE J * M := by
  unfold idlE
  apply le_antisymm
  · refine Submodule.smul_le.mpr fun r hr m hm => ?_
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul (Submodule.mem_map_of_mem hr) hm
  · refine Submodule.mul_le.mpr fun x hx m hm => ?_
    obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hx
    rw [Algebra.linearMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr hm

omit [NumberField E] in
theorem idlE_mul (I J : Ideal (𝓞 E)) : idlE (I * J) = idlE I * idlE J := IsLocalization.coeSubmodule_mul E I J

theorem idlE_cancel {G : Ideal (𝓞 E)} (hG : G ≠ ⊥) {X Y : Submodule (𝓞 E) E} (h : idlE G * X = idlE G * Y) :
    X = Y := by
  have hG' : (G : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hG
  have e : idlE G = ((G : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := rfl
  have key : ∀ Z : Submodule (𝓞 E) E,
      (((G : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) *
        (idlE G * Z) = Z := by
    intro Z
    rw [e, ← mul_assoc, ← FractionalIdeal.coe_mul, inv_mul_cancel₀ hG', FractionalIdeal.coe_one, one_mul]
  rw [← key X, h, key Y]

theorem index_coprime {n p : ℕ} (hp : p.Prime) (Λ : GenLat E n) (h : Λ.TrivAt p)
    (h0 : (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ≠ 0) :
    Nat.Coprime (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index p := by
  obtain ⟨k, hk, hk1, -⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero h0
  let _ := Fintype.ofFinite (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup)
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hdvd' : p ∣ Fintype.card
      (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) := by
    rw [← Nat.card_eq_fintype_card]; exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd'
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hmem : k • y ∈ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup := by
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    have hc : ((k • y : Λ.La.toAddSubgroup) : Fin n → E) = (k : 𝓞 E) • (y : Fin n → E) := by
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    rw [hc]
    have h1 : (k : 𝓞 E) • (y : Fin n → E) ∈ Ideal.span {(k : 𝓞 E)} • Λ.La :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) y.2
    show (k : 𝓞 E) • (y : Fin n → E) ∈ Λ.La ⊓ stdLat E n
    exact Submodule.mem_inf.mpr ⟨Λ.La.smul_mem _ y.2, hk1 h1⟩
  have hz : k • (QuotientAddGroup.mk y :
      Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hmem
  have hpk : p ∣ k := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hz
  exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hk.symm hpk)

theorem val_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p a : ℕ}
    (hp : (p : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime a p) : la.valuation K (a : K) = 1 := by
  have hnot : (a : 𝓞 K) ∉ la.asIdeal := by
    intro ha
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
    have huv' : u * (a : 𝓞 K) + v * (p : 𝓞 K) = 1 := by simpa using huv
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv']
    exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left u ha) (la.asIdeal.mul_mem_left v hp)
  rw [← map_natCast (algebraMap (𝓞 K) K) a]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := la) (K := K)).mpr hnot

variable [IsCMField E]

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem map_bar_bar (H : Host E) (J : Ideal (𝓞 E)) :
    (J.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) = J := by
  rw [Ideal.map_map]
  have hid : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar H a
  rw [hid, Ideal.map_id]

theorem conjI_eq (H : Host E) (J : Ideal (𝓞 E)) : GlobalTheory.SW.conjI J = J.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    exact (H.bar_eq b).trans hab.symm
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, H.bar_eq b⟩

theorem exists_numerator (H : Host E) {n : ℕ} (Λ : GenLat E n) (h : Λ.Unimod) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ≠ 0 ∧
    ∃ cc : Ideal (𝓞 E), cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      Submodule.span (𝓞 E) (detSet Λ.La) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc ∧
      (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℕ) : 𝓞 E) ∈ cc := by
  obtain ⟨J, hJ0, hJn, hJd, hJc, -⟩ := GlobalTheory.DetIdeal.detIdeal_selfDual E n Λ h
  refine ⟨?_, ?_⟩
  · rw [← hJn]
    exact fun h0 => hJ0 (Ideal.absNorm_eq_zero_iff.mp h0)
  have hrel : idlE J * Submodule.span (𝓞 E) (detSet Λ.La) = idlE (J.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
    rw [← smul_eq_idlE_mul, ← hJd, hJc, conjI_eq H]
    rfl
  obtain ⟨A, hA⟩ : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) ∣ J := Ideal.dvd_iff_le.mpr le_sup_left
  have hG0 : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := fun h0 => hJ0 (eq_bot_iff.mpr (h0 ▸ le_sup_left))
  have hGbar : (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) =
      J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [Ideal.map_sup, map_bar_bar, sup_comm]
  have hJbar : J.map (H.bar : 𝓞 E →+* 𝓞 E) =
      (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * A.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    conv_lhs => rw [hA]
    rw [Ideal.map_mul, hGbar]
  have hcop : A ⊔ A.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
    have e : (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * (A ⊔ A.map (H.bar : 𝓞 E →+* 𝓞 E)) =
        (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * ⊤ := by
      rw [Ideal.mul_sup, ← hA, ← hJbar, Ideal.mul_top]
    exact mul_left_cancel₀ hG0 e
  have hJA : J ≤ A := by
    rw [hA]
    exact Ideal.mul_le_right
  refine ⟨A.map (H.bar : 𝓞 E →+* 𝓞 E), ?_, ?_, ?_⟩
  · rw [map_bar_bar, sup_comm]
    exact hcop
  · rw [map_bar_bar, mul_comm]
    apply idlE_cancel hG0
    rw [← mul_assoc, ← idlE_mul, ← hA, hrel]
    conv_lhs => rw [hJbar]
    rw [idlE_mul]
  · have hm : (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℕ) : 𝓞 E) ∈ J := by
      rw [← hJn]
      exact Ideal.absNorm_mem J
    have h2 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hm
    rw [map_natCast] at h2
    exact Ideal.map_mono hJA h2

end Ideals

end GlobalTheory.ScalarUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulus
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.RayRootOfUnity

theorem norm_pos_of_pos_real {K : Type} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (h : ∀ τ : K →+* ℝ, 0 < τ x) : 0 < Algebra.norm ℚ x := by
  classical
  let c : (K →ₐ[ℚ] ℂ) → (K →ₐ[ℚ] ℂ) := fun φ =>
    { (starRingEnd ℂ).comp φ.toRingHom with
      commutes' := fun a => by
        change starRingEnd ℂ (φ (algebraMap ℚ K a)) = _
        rw [φ.commutes]; simp }
  have hc : ∀ φ e, c φ e = starRingEnd ℂ (φ e) := fun _ _ => rfl
  have hφ : ∀ φ : K →ₐ[ℚ] ℂ, φ x ≠ 0 := fun φ => (map_ne_zero _).2 hx
  have hn : ∀ φ : K →ₐ[ℚ] ℂ, (‖φ x‖ : ℂ) ≠ 0 := fun φ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hφ φ))
  have h1 : ∏ φ : K →ₐ[ℚ] ℂ, (φ x / (‖φ x‖ : ℂ)) = 1 := by
    refine Finset.prod_involution (fun φ _ => c φ) (fun φ _ => ?_) (fun φ _ hne he => ?_)
      (fun _ _ => Finset.mem_univ _) (fun φ _ => ?_)
    · rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have := hn φ
      push_cast
      field_simp
    · apply hne
      have hr : ∀ e, ((φ e).re : ℂ) = φ e := fun e =>
        Complex.conj_eq_iff_re.1 (by rw [← hc, he])
      let τ : K →+* ℝ :=
        { toFun := fun e => (φ e).re, map_one' := by simp, map_zero' := by simp,
          map_add' := by simp, map_mul' := fun a b => by
            apply Complex.ofReal_injective
            rw [Complex.ofReal_mul, hr, hr, hr, map_mul] }
      have hτ : 0 < (φ x).re := h τ
      rw [← hr x, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      exact div_self (by exact_mod_cast hτ.ne')
    · ext e; simp [hc]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun φ _ => hn φ),
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x] at h1
  have h2 : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ φ : K →ₐ[ℚ] ℂ, ‖φ x‖ := by
    apply Complex.ofReal_injective
    push_cast
    rw [← h1]
    rfl
  have : (0 : ℝ) < ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    rw [h2]; exact Finset.prod_pos fun φ _ => norm_pos_iff.2 (hφ φ)
  exact_mod_cast this

theorem absNorm_modEq_one {K : Type} [Field K] [NumberField K] {𝔮 : Ideal (𝓞 K)} {p : ℕ}
    (hq : 𝔮 ≤ Ideal.span {(p : 𝓞 K)}) {I : Ideal (𝓞 K)} {α β : 𝓞 K} (hαβ : RayPair 𝔮 α β)
    (hI : I * Ideal.span {β} = Ideal.span {α}) : Ideal.absNorm I ≡ 1 [MOD p] := by
  obtain ⟨hα, hβ, _, hcβ, hd, hpos⟩ := hαβ
  have hpos' : 0 < Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have hx : ((α * β : 𝓞 K) : K) ≠ 0 := by simpa using mul_ne_zero hα hβ
    have := norm_pos_of_pos_real hx fun τ => by
      have := hpos τ
      simpa [map_mul] using this
    rw [← Algebra.coe_norm_int, map_mul] at this
    exact_mod_cast this
  have h1 := congrArg Ideal.absNorm hI
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at h1
  have h2 : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β * Algebra.norm ℤ β = Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have e := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, Int.natCast_natAbs, Int.natCast_natAbs] at e
    have e2 : (Ideal.absNorm I : ℤ) * |Algebra.norm ℤ β| * |Algebra.norm ℤ β| =
        |Algebra.norm ℤ α| * |Algebra.norm ℤ β| := by rw [e]
    rw [mul_assoc, abs_mul_abs_self, ← abs_mul, abs_of_pos hpos'] at e2
    rw [mul_assoc]; exact e2
  have h3 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (hq hd)
  obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hcβ
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have h4 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (x := b * β) (y := 1) (by
    have : b * β - 1 = -v := by linear_combination huv
    rw [this]; exact neg_mem (hq hv))
  rw [map_mul, map_one] at h4
  have h5 := congrArg (Int.cast : ℤ → ZMod p) h2
  push_cast at h4 h5
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  linear_combination ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * h5 +
    ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * ((Algebra.norm ℤ β : ℤ) : ZMod p) * h3 +
    (((Algebra.norm ℤ b : ℤ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) + 1) * (1 - (Ideal.absNorm I : ZMod p)) * h4

end GlobalTheory.RayRootOfUnity

namespace GlobalTheory.RayRootOfUnity

theorem exists_isPrimitiveRoot_of_isRay : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∃ ζ : H, IsPrimitiveRoot ζ n := by
  intro K H _ _ _ _ _ _ n hn hR
  classical
  have hRF : GlobalTheory.Mem.Fld.IsRayField K H (Ideal.span {(n : 𝓞 K)}) := ⟨inferInstance, hR⟩
  have h𝔮 : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by simpa using hn
  let ψ : H →+* ℂ := (IsAlgClosed.lift : H →ₐ[ℚ] ℂ).toRingHom
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨S, hSa, hS⟩ := GlobalTheory.Mem.BaseField.exists_gens H
  obtain ⟨L, hfd, hgal, hSL, -, -⟩ := GlobalTheory.exists_galois_subfield_conj_stable (insert z S) (by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    exacts [GlobalTheory.Mem.BaseField.isAlgebraic_exp n, hSa w hw])
  have hψL : ∀ x, ψ x ∈ L := hS L (fun w hw => hSL w (Finset.mem_insert_of_mem hw)) ψ
  have hzL : z ∈ L := hSL z (Finset.mem_insert_self _ _)
  have : NumberField L := {}
  letI : Algebra H L := (ψ.codRestrict L hψL).toAlgebra
  letI : Algebra K L := ((ψ.codRestrict L hψL).comp (algebraMap K H)).toAlgebra
  have : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  obtain ⟨x, hx⟩ := GlobalTheory.Mem.RayZeta.root_mem_rayField K H L _ n hn le_rfl hRF
    (GlobalTheory.RayMaximal.closure_isFrob_eq_top L h𝔮)
    (fun I α β hαβ hI => absNorm_modEq_one le_rfl hαβ hI) ⟨z, hzL⟩
    (Subtype.ext (by simpa using hz.pow_eq_one))
  have e : ψ x = z := congrArg Subtype.val hx
  exact ⟨x, IsPrimitiveRoot.of_map_of_injective (f := ψ) (by rw [e]; exact hz) ψ.injective⟩

end GlobalTheory.RayRootOfUnity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedWittElementEq
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

namespace GlobalTheory.WittCompat

theorem u_eq_aB (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (c : ↥(MaximalUnramifiedExtension l))
    (hw : ((Per.θ l (wA l a w) : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (c : Om l)) :
    C.u c = Per.aB l (wA l a w) := by
  have ho := GlobalTheory.SeedSec.o_eq_aDp_wA l a C w (c : Om l) hw
  apply (GlobalTheory.MemLoc.ULaws.u_laws l C).2.2.2.1
  have hB : C.ι (Per.aB l (wA l a w)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l a w)) :=
    GlobalTheory.MemLoc.ULaws.iota_aB C (wA l a w)
  rw [hB, ← ho, C.ι_u]

theorem exists_unramified_witt_element : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (w : W0 K),
    ∃ c : ↥(K0 K), algebraMap ↥(K0 K) ↥K.1 c = oK K (thetaW (fK K) K w) ∧
      algebraMap ↥(K0 K) P.R.B c = T.eB.symm (Per.aB l (wA l (fK K) w)) := by
  intro l _ P AI T K w
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have h1 : ((Per.θ l (wA l (fK K) w) : Per.OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) :=
    (congrArg (fun y : Per.OC l => (y : ℂ_[l])) (intToOC_thetaW (fK K) K w)).symm
  have h2 : ((Per.θ l (wA l (fK K) w) : Per.OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (GlobalTheory.TameFrob.iotaO l (fK K) w) :=
    (congrArg (fun y : Per.OC l => (y : ℂ_[l])) (intToOC_thetaW (fK K) (unrExt l (fK K)) w)).symm
  have h3 : ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) = GlobalTheory.TameFrob.iotaO l (fK K) w :=
    (algebraMap (Om l) ℂ_[l]).injective (h1.symm.trans h2)
  have hm : ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) ∈ K0 K := by
    rw [h3, ← Kunr_fK K]
    exact GlobalTheory.TameFrob.iotaO_mem l (fK K) w
  refine ⟨⟨_, hm⟩, Subtype.ext rfl, ?_⟩
  rw [RingEquiv.eq_symm_apply]
  exact (hC.u ⟨_, hm.2⟩).trans (u_eq_aB l (fK K) C w ⟨_, hm.2⟩ h1)

end GlobalTheory.WittCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPair
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerCharH1

theorem le_of_pow_le {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  push_neg at hab
  have key : ∀ r : ℕ, q ^ r ≤ C := by
    intro r
    have h1 := h r
    have hpos : 0 < q ^ (r * b) := pow_pos (by omega) _
    have : q ^ (r * a) ≥ q ^ (r * b) * q ^ r := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    have : q ^ (r * b) * q ^ r ≤ C * q ^ (r * b) := le_trans this h1
    rw [mul_comm (q ^ (r * b))] at this
    exact Nat.le_of_mul_le_mul_right this hpos
  have h2 := key C
  have h3 : C < 2 ^ C := Nat.lt_two_pow_self
  have h4 : 2 ^ C ≤ q ^ C := Nat.pow_le_pow_left hq C
  omega

theorem stableSub_span_smul {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (c : O) :
    StableSub L (Ideal.span {c} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  rw [Submodule.ideal_span_singleton_smul] at hx ⊢
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨actT L g y, Submodule.mem_top, (map_smul _ _ _).symm⟩

end GlobalTheory.EulerCharH1

namespace GlobalTheory.EulerCharH1

theorem natCast_not_isUnit (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (hint : ∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔
      RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) :
    ¬ IsUnit ((l : ℕ) : O) := by
  rintro ⟨u, hu⟩
  have hl0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hy : algebraMap O LL ((u⁻¹ : Oˣ) : O) = algebraMap ℚ_[l] LL (((l : ℕ) : ℚ_[l])⁻¹) := by
    rw [map_inv₀, map_natCast]
    have h1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_natCast] at h1
    exact eq_inv_of_mul_eq_one_left h1
  obtain ⟨p, hpm, hp⟩ := (hint _).mp ⟨_, hy⟩
  rw [← Polynomial.hom_eval₂] at hp
  have hp' : p.eval₂ (algebraMap ℤ_[l] ℚ_[l]) (((l : ℕ) : ℚ_[l])⁻¹) = 0 :=
    (algebraMap ℚ_[l] LL).injective (by rw [hp, map_zero])
  have hI : IsIntegral ℤ_[l] (((l : ℕ) : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI
  have hlw : ((l : ℕ) : ℤ_[l]) * w = 1 := by
    apply IsFractionRing.injective ℤ_[l] ℚ_[l]
    rw [map_mul, hw, map_natCast, map_one, mul_inv_cancel₀ hl0]
  exact PadicInt.p_nonunit (IsUnit.of_mul_eq_one _ hlw)

end GlobalTheory.EulerCharH1

namespace GlobalTheory.EulerCharH1

theorem two_le_card (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) : 2 ≤ Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) := by
  obtain ⟨hint, -, hfin, -⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  have hf : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by
    simpa using hfin 1
  have : Nontrivial (O ⧸ Ideal.span {((l : ℕ) : O)}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit l LL O hint)
  exact Finite.one_lt_card

theorem eq_of_bounds {q a h0 h0' d C1 C2 C3 C4 : ℕ} (X Y H H' : ℕ → ℕ) (hq : 2 ≤ q)
    (hX : ∀ r, q ^ (r * a) ≤ X r ∧ X r ≤ C1 * q ^ (r * a))
    (hY : ∀ r, X r ≤ Y r ∧ Y r ≤ C2 * X r)
    (hE : ∀ r, Y r = H r * H' r * q ^ (r * d))
    (hH : ∀ r, q ^ (r * h0) ≤ H r ∧ H r ≤ C3 * q ^ (r * h0))
    (hH' : ∀ r, q ^ (r * h0') ≤ H' r ∧ H' r ≤ C4 * q ^ (r * h0')) :
    a = h0 + h0' + d := by
  have key : ∀ r : ℕ, q ^ (r * a) ≤ C3 * C4 * q ^ (r * (h0 + h0' + d)) ∧
      q ^ (r * (h0 + h0' + d)) ≤ C2 * C1 * q ^ (r * a) := by
    intro r
    obtain ⟨hX1, hX2⟩ := hX r
    obtain ⟨hY1, hY2⟩ := hY r
    obtain ⟨hH1, hH2⟩ := hH r
    obtain ⟨hH1', hH2'⟩ := hH' r
    have hpow : q ^ (r * (h0 + h0' + d)) = q ^ (r * h0) * q ^ (r * h0') * q ^ (r * d) := by
      rw [← pow_add, ← pow_add]; ring_nf
    constructor
    · calc q ^ (r * a) ≤ X r := hX1
        _ ≤ Y r := hY1
        _ = H r * H' r * q ^ (r * d) := hE r
        _ ≤ (C3 * q ^ (r * h0)) * (C4 * q ^ (r * h0')) * q ^ (r * d) := by
          gcongr
        _ = C3 * C4 * q ^ (r * (h0 + h0' + d)) := by rw [hpow]; ring
    · calc q ^ (r * (h0 + h0' + d)) = q ^ (r * h0) * q ^ (r * h0') * q ^ (r * d) := hpow
        _ ≤ H r * H' r * q ^ (r * d) := by gcongr
        _ = Y r := (hE r).symm
        _ ≤ C2 * X r := hY2
        _ ≤ C2 * (C1 * q ^ (r * a)) := by gcongr
        _ = C2 * C1 * q ^ (r * a) := by ring
  have h1 := le_of_pow_le hq (fun r => (key r).1)
  have h2 := le_of_pow_le hq (fun r => (key r).2)
  omega

theorem finite_and_finrank_H1V : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL],
    GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m →
    Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) +
      finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  intro hTD hEC l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨LA, LA', hLL, -⟩ := GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm
  have hfinT : Module.Finite O (LatticeCohomology LA) := GlobalTheory.T.finite_H1_period_datum hTD l P K LL O hO A LA
  obtain ⟨hfinV, C1, -, hX⟩ := GlobalTheory.T.H1_lattice_rank_growth_of_goodO l K LL O hO A LA hfinT
  obtain ⟨C2, -, hY⟩ := GlobalTheory.T.H1_reduction_index_bound_of_tateDuality hTD l P K LL O hO A A' LA LA' m hLL
  obtain ⟨C3, -, hH⟩ := GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice l K LL O hO A LA
  obtain ⟨C4, -, hH'⟩ := GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice l K LL O hO A' LA'
  exact ⟨hfinV, eq_of_bounds _ _ _ _ (two_le_card l LL O hO) hX
    (fun r => hY r (stableSub_span_smul LA _))
    (fun r => GlobalTheory.T.H1_lattice_index_growth_of_tateDuality_eulerChar hTD hEC l P K LL O hO A A' LA LA' m hLL r
      (stableSub_span_smul LA _) (stableSub_span_smul LA' _))
    (fun r => hH r (stableSub_span_smul LA _)) (fun r => hH' r (stableSub_span_smul LA' _))⟩

end GlobalTheory.EulerCharH1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinftyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k := by
  first | exact @GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf | exact GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf | (intros; apply GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf <;> assumption)
end

