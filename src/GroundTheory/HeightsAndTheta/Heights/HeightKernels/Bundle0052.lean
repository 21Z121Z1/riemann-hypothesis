import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionIndexNorm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointNagata
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointResidue

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionQuotFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SectionQuotientFinite

variable {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')

omit [Fintype T] in

theorem mem_blockFnField_of_mem_chartRingZ (t : T) {b : K'} (hb : b ∈ chartRingZ y (fun _ => t)) :
    b ∈ blockFnField y := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem exists_int_mul_coord_mem : ∃ D : ℤ, D ≠ 0 ∧ ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K' := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_integral_multiples ℤ ℚ (L := K') (Finset.univ.image fun t => y ⟨(), t⟩)
  refine ⟨D, hD0, fun t => ?_⟩
  have h := hD (y ⟨(), t⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  rw [zsmul_eq_mul] at h
  exact h

theorem int_mul_mem_of_mem_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) {D : ℤ}
    (hD : ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K') {m : K'} (hm : m ∈ sectionMod y) :
    (D : K') * m ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' ((D : K') * m) ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' _ hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hmt : m / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
    SectionIndexNormAlt.mem_chartLat_iff.mp hm t hyt
  have h1 : v.valuation K' (m / y ⟨(), t⟩) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).mp
      (CurveAffineCharts.mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _)) hmt)
  have h2 : v.valuation K' ((D : K') * y ⟨(), t⟩) ≤ 1 := by
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 K', algebraMap (𝓞 K') K' r = (D : K') * y ⟨(), t⟩ :=
      ⟨⟨_, hD t⟩, rfl⟩
    rw [← hr]
    exact HeightOneSpectrum.valuation_le_one v r
  have e : (D : K') * m = m / y ⟨(), t⟩ * ((D : K') * y ⟨(), t⟩) := by
    field_simp
  rw [e, map_mul]
  exact mul_le_one' h1 h2

theorem fg_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) : AddGroup.FG (sectionMod y) := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_coord_mem y
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : sectionMod y →+ integralClosure ℤ K' :=
    { toFun := fun m => ⟨(D : K') * m, int_mul_mem_of_mem_sectionMod y hy hD m.2⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun a b => Subtype.ext (mul_add _ _ _) }
  have hinj : Function.Injective f := fun a b h => by
    have h' : (D : K') * a = (D : K') * b := congrArg (fun z : integralClosure ℤ K' => (z : K')) h
    exact Subtype.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hD0) h')
  have hfin : Module.Finite ℤ (sectionMod y) := Module.Finite.of_injective f.toIntLinearMap hinj
  exact Module.Finite.iff_addGroup_fg.mp hfin

omit [NumberField K'] in

theorem aeval_ne_zero {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1))
    (hsP : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  apply hsP
  change s ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
  rw [h0, map_zero, zero_mul]

theorem exists_nat_mul_mem_span (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {m : K'} (hm : m ∈ sectionMod y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * m ∈ Submodule.span (curveRing y) {aeval y s} := by
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := aeval_ne_zero y hs hsP
  obtain ⟨t, ht⟩ := CurveAffineCharts.exists_chart y hy
  have hmt : m / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.mem_chartLat_iff.mp hm t ht)
  have hxt : x / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.aeval_div_mem hs t)
  have hq : m / x ∈ blockFnField y := by
    have e : m / x = (m / y ⟨(), t⟩) / (x / y ⟨(), t⟩) := by
      field_simp
    rw [e]
    exact div_mem hmt hxt
  obtain ⟨n, hn, hnq⟩ := CurveAffineCharts.exists_nat_mul_mem_curveRing y hq
  refine ⟨n, hn, Submodule.mem_span_singleton.mpr ⟨⟨_, hnq⟩, ?_⟩⟩
  rw [Subring.smul_def, smul_eq_mul]
  field_simp

theorem isTorsion (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) (q : sectionQuot y (aeval y s)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • q = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, hnm⟩ := exists_nat_mul_mem_span y hy hs hsP m.2
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rw [Submodule.subtype_apply]
  simpa [nsmul_eq_mul] using hnm

end SectionQuotientFinite

open SectionQuotientFinite in

theorem SectionQuotFinite.closed : SectionQuotFinite.Statement := by
  intro T _ K' _ _ y s hy hs hsP
  have hfg : AddGroup.FG (sectionQuot y (aeval y s)) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _)
      (hG := fg_sectionMod y hy)
  let _ : Module ℤ (sectionQuot y (aeval y s)) := AddCommGroup.toIntModule _
  have hfin : Module.Finite ℤ (sectionQuot y (aeval y s)) := Module.Finite.iff_addGroup_fg.mpr hfg
  refine Module.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨n, hn, hnq⟩ := isTorsion y hy hs hsP q
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩
  change ((n : ℤ)) • q = 0
  rw [natCast_zsmul]
  exact hnq

theorem SectionQuotFinite.proof (_hC : CurveCharts.Statement) : SectionQuotFinite.Statement :=
  SectionQuotFinite.closed

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointMultChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace VerticalPointMultiplicityChart

theorem length_localizedModule_quotient {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  have := IsLocalization.linearMap_compatibleSMul p.primeCompl
  let e := (IsLocalizedModule.linearEquiv p.primeCompl
    (I.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p)))
    (LocalizedModule.mkLinearMap p.primeCompl (R ⧸ I))).restrictScalars (Localization.AtPrime p)
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ (Ideal.localized'_eq_map _ _ I)).length_eq

theorem length_quotient_of_surjective {A N : Type*} [CommRing A] [CommRing N] (Φ : A →+* N)
    (hΦ : Function.Surjective Φ) (J : Ideal A) (hJ : RingHom.ker Φ ≤ J) :
    Module.length A (A ⧸ J) = Module.length N (N ⧸ J.map Φ) := by
  let _ := Φ.toAlgebra
  have hs : Function.Surjective (algebraMap A (N ⧸ J.map Φ)) :=
    (Ideal.Quotient.mk_surjective).comp hΦ
  have hker : RingHom.ker (Algebra.ofId A (N ⧸ J.map Φ)) = J := by
    ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (Φ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hΦ,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hJ]
  let e := (Ideal.quotientEquivAlgOfEq A hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A (N ⧸ J.map Φ)) hs)
  rw [e.toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective hΦ

theorem aeval_C_mul_X {T : Type} [Fintype T] {S : Type*} [CommRing S] (r : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) (d : ℕ) (hf : IsMultiHomog f (fun _ => d)) :
    eval₂ (Int.castRingHom (Polynomial S)) (fun p => Polynomial.C (r p) * Polynomial.X) f =
      Polynomial.C (eval₂ (Int.castRingHom S) r f) * Polynomial.X ^ d := by
  classical
  rw [eval₂_eq, eval₂_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : ∑ i, m ⟨(), i⟩ = d := hf m hm ()
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Fintype.sum_sigma, Fintype.sum_unique, hmd, map_mul, map_prod]
  simp only [map_pow, eq_intCast, map_intCast]
  ring

end VerticalPointMultiplicityChart

open VerticalPointMultiplicityChart in

theorem VertPointMultChart.proof (hCh : VertPointChart.Statement) (hN : VertPointNagata.Statement) :
    VertPointMultChart.Statement := by
  intro T _ K' _ _ y s hP hs hsP W hW t ht a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh T K' y s hP hs hsP W hW t ht
  have hWp : W.IsPrime := hW.1.1.1
  have hmp : (curvePtIdeal y W).IsPrime := hmax.isPrime
  choose a' b' hb' hab' using hrat
  obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN T K' y s hP hs hsP W hW t ht a' b' hb' hab'
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    apply ht
    apply hPW
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

  have hunit : ∀ x : (curvePtIdeal y W).primeCompl, IsUnit ((curveRing y).subtype x) := fun x =>
    isUnit_iff_ne_zero.mpr fun h => x.2 (by
      rw [show (x : curveRing y) = 0 from Subtype.ext h]; exact zero_mem _)
  let ι : Localization.AtPrime (curvePtIdeal y W) →+* K' := IsLocalization.lift hunit
  have hinj : Function.Injective ι := by
    rw [IsLocalization.lift_injective_iff]
    intro x z
    rw [(IsLocalization.injective (M := (curvePtIdeal y W).primeCompl) (Localization.AtPrime (curvePtIdeal y W))
      (le_nonZeroDivisors_of_noZeroDivisors fun h => h (zero_mem _))).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hbc : b ∈ (curvePtIdeal y W).primeCompl := hb
  have hbc' : ∀ u, b' u ∈ (curvePtIdeal y W).primeCompl := hb'
  let r : (Σ _ : Unit, T) → Localization.AtPrime (curvePtIdeal y W) := fun p =>
    IsLocalization.mk' _ (a' p.2) (⟨b' p.2, hbc' p.2⟩ : (curvePtIdeal y W).primeCompl)
  have hιr : ∀ p, ι (r p) = y p / y ⟨(), t⟩ := by
    rintro ⟨⟨⟩, u⟩
    exact (IsLocalization.lift_mk'_spec _ _ _ _).mpr (hab' u).symm
  have hιa : ∀ f : MRing (fun _ : Unit => T), ι (aeval r f) = aeval (fun p => ι (r p)) f := fun f => by
    induction f using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have hsr : aeval r s = IsLocalization.mk' _ a (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl) := by
    apply hinj
    rw [hιa, funext hιr, VerticalPointResidue.aeval_div y t s 1 hs]
    symm
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    change (a : K') = (b : K') * (aeval y s * (y ⟨(), t⟩ ^ 1)⁻¹)
    rw [pow_one, ← mul_assoc, hab, mul_assoc, mul_inv_cancel₀ hyt, mul_one]

  have hX : (Polynomial.X : Polynomial (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (Polynomial.C : _ →+* Polynomial _)).primeCompl := by
    intro h
    have h1 := Ideal.mem_map_C_iff.mp h 1
    rw [Polynomial.coeff_X_one] at h1
    exact (IsLocalRing.maximalIdeal _).ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hbu : IsUnit (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
      (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl)) := by
    exact isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ b, (IsLocalization.mk'_spec _ _ _).trans (map_one _)⟩
  have hΦs : Φ (algebraMap _ _ s) =
      algebraMap (Localization.AtPrime (curvePtIdeal y W)) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (algebraMap (curveRing y) _ a) *
      (algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (Polynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
          (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W))) Polynomial.X) := by
    have hΦ' : Φ (algebraMap _ _ s) = algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W)))
        (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (aeval (fun p => Polynomial.C (r p) * Polynomial.X) s) := hΦ s
    rw [hΦ', aeval_def, RingHom.ext_int (algebraMap ℤ (Polynomial (Localization.AtPrime (curvePtIdeal y W))))
      (Int.castRingHom (Polynomial (Localization.AtPrime (curvePtIdeal y W)))), aeval_C_mul_X r s 1 hs,
      ← RingHom.ext_int (algebraMap ℤ (Localization.AtPrime (curvePtIdeal y W)))
        (Int.castRingHom (Localization.AtPrime (curvePtIdeal y W))), ← aeval_def, hsr, IsLocalization.mk'_eq_mul_mk'_one, pow_one, map_mul, map_mul,
      map_mul, IsScalarTower.algebraMap_apply (Localization.AtPrime (curvePtIdeal y W))
        (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing _), Polynomial.algebraMap_eq,
      mul_assoc]
  have hv : IsUnit (algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (Polynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
          (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W))) Polynomial.X) :=
    ((hbu.map Polynomial.C).map _).mul (IsLocalization.map_units _ ⟨_, hX⟩)

  have hJ : ((mCoordIdeal y ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).map Φ =
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a}).map
        (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) := by
    rw [Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge, bot_sup_eq,
      Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Set.image_singleton, hΦs, Ideal.span_singleton_mul_right_unit hv]

  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
      (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) =
      IsLocalRing.maximalIdeal (nagataRing (Localization.AtPrime (curvePtIdeal y W))) := by
    rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (curvePtIdeal y W))
      (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing _), ← Ideal.map_map,
      Polynomial.algebraMap_eq, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsLocalHom (algebraMap (Localization.AtPrime (curvePtIdeal y W))
      (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hx'
    have h1 : x ∈ IsLocalRing.maximalIdeal _ := hx'
    have h2 := Ideal.mem_map_of_mem (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) h1
    rw [hmap] at h2
    exact h2 hx
  have hfib : Module.length (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
      (nagataRing (Localization.AtPrime (curvePtIdeal y W)) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
          (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W))))) = 1 := by
    rw [hmap]
    have : IsSimpleModule (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (nagataRing (Localization.AtPrime (curvePtIdeal y W)) ⧸
          IsLocalRing.maximalIdeal (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _

  rw [multAt, dif_pos hWp, locLen, dif_pos hmp]
  congr 1
  rw [length_localizedModule_quotient, length_localizedModule_quotient,
    length_quotient_of_surjective Φ hsurj _ (hker.le.trans (Ideal.map_mono le_sup_left)), hJ,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a})).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, hfib, mul_one, Ideal.map_span, Set.image_singleton]

end

end GroundTheory.Heights₂.Heights
end

