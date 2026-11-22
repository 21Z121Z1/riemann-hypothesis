import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SacSuccAbove

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DecompBlock0
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable abbrev sub0 (x : Fin (d.N + 1) → K) : KTp K d.D d.N →ₐ[K] KTp K d.D d.N :=
  MvPolynomial.aeval (fun v : TVar d.D d.N =>
    if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v)

set_option synthInstance.maxHeartbeats 400000 in

theorem finYX4 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI := d.algLE h c
    letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
    FiniteDimensional (FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c))) := by
  letI := d.algLE h c
  letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
  letI := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    classical
    obtain ⟨e, -, -, hsp⟩ := hd.a4
    refine ⟨⟨Finset.univ.image (fun k : Fin d.del => algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))), ?_⟩⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨q, hq, p, hp⟩ := hsp (fun c' => if hc : c' = c then hc ▸ y else 0)
    have hpc : d.sH c q * y = ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      have h1 := hp c
      first
        | (simp only [dif_pos (rfl : c = c)] at h1; exact h1)
        | simpa using h1
    have hq0 := hq c
    have hKT : ∀ r : KTp K d.D d.N, d.KTtoS h c (algebraMap _ _ r) = d.sH c r := fun r => by
      simp [Data.KTtoS]
    have hy : y = ∑ k, (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (p k) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) •
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_div₀, hKT,
        div_mul_eq_mul_div, ← Finset.sum_div, ← hpc]
      first
        | exact (mul_div_cancel_left₀ y hq0).symm
        | field_simp
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  exact Module.Finite.of_equiv_equiv d.eLX4 (d.eEX4 c)
    (RingHom.ext fun q => (d.fieldEquiv_compat_liftY h c q).symm)

set_option synthInstance.maxHeartbeats 400000 in
theorem decomp_block0 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ (L E : Type) (_ : Field L) (_ : Field E) (_ : Algebra L E) (_ : FiniteDimensional L E)
      (eL : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (eE : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) E)),
      (∀ q : KTf K d.D d.N, eE (d.KTtoS h c q) = VariableBasisExtension.liftY (eL q)) ∧
      (∀ r : Ω c, ∃ e : E, eE (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) =
        algebraMap (MvPolynomial (Fin (d.N + 1)) E) (FractionRing (MvPolynomial (Fin (d.N + 1)) E))
          (MvPolynomial.C e)) ∧
      ∀ l : L, ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x P = P) ∧ (∀ x, d.sub0 x Q = Q) ∧
        eL.symm (algebraMap (MvPolynomial (Fin (d.N + 1)) L)
            (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (MvPolynomial.C l)) =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P / algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q := by
  letI := d.algLE h c
  refine ⟨d.FracFieldPositiveRowsBase, d.FracFieldPositiveRowsOmega c, inferInstance, inferInstance, inferInstance,
    FractionFieldVariableLift.finiteDimensional_of_liftY (σ := Fin (d.N + 1)) (d.finYX4 hd h c), d.eLX4, d.eEX4 c,
    fun q => d.fieldEquiv_compat_liftY h c q, fun r => ?_, fun l => ?_⟩
  · refine ⟨algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c) (MvPolynomial.C r), ?_⟩
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq, d.eEX4_algebraMap, FractionFieldVariableLift.hE_C]
    simp only [FractionFieldVariableLift.toFracY, RingHom.comp_apply, MvPolynomial.map_C]
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := d.PolyRingPositiveRowsBase) l
    have hfix : ∀ (x : Fin (d.N + 1) → K) (p : d.PolyRingPositiveRowsBase),
        d.sub0 x (MvPolynomial.rename Subtype.val p) = MvPolynomial.rename Subtype.val p := by
      intro x p
      have hc : (d.sub0 x).comp (MvPolynomial.rename (R := K)
          (Subtype.val : {v : TVar d.D d.N // v.1 ≠ 0} → TVar d.D d.N)) =
          MvPolynomial.rename Subtype.val := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [Data.sub0, v.2]
      exact AlgHom.congr_fun hc p
    refine ⟨MvPolynomial.rename Subtype.val p, MvPolynomial.rename Subtype.val q, ?_,
      fun x => hfix x p, fun x => hfix x q, ?_⟩
    · exact fun h0 => nonZeroDivisors.ne_zero hq
        (MvPolynomial.rename_injective _ Subtype.val_injective (h0.trans (map_zero _).symm))
    · rw [RingEquiv.symm_apply_eq, map_div₀ d.eLX4, d.eLX4_algebraMap, d.eLX4_algebraMap,
        FractionFieldVariableLift.hL_rename, FractionFieldVariableLift.hL_rename]
      simp only [FractionFieldVariableLift.toFracY, RingHom.comp_apply, MvPolynomial.map_C]
      exact map_div₀ ((algebraMap (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase) _).comp MvPolynomial.C) _ _

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscLocal
section
set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscOmL

open IsDedekindDomain IsLocalRing Module

variable {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R F] in
theorem prod_zpow {κ G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset κ)
    (f : κ → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hx]

theorem disc_local (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c) (hli : LinearIndependent F b)
    (hb : ∀ k c, ∀ w ∈ HNm.OverR R F (L c) p, 0 ≤ w (b k c) + (n c w : WithTop ℤ)) :
    ∃ a s : R, s ∉ p ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
        algebraMap R F g ^ (2 * ∑ c, ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
          (_ : w ∈ HNm.OverR R F (L c) p), (HNm.fz F w : ℤ) * n c w) * algebraMap R F s =
        algebraMap R F a := by
  classical
  let O := Localization.AtPrime p
  letI : Algebra O F := IsLocalization.localizationAlgebraOfSubmonoidLe O F p.primeCompl
    (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsScalarTower R O F := IsLocalization.localization_isScalarTower_of_submonoid_le O F
    p.primeCompl (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsFractionRing O F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl O F
  obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
  haveI := hdvr
  letI : ∀ c, Algebra O (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap O F)).toAlgebra
  haveI : ∀ c, IsScalarTower O F (L c) := fun c => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ c, Algebra R (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap R F)).toAlgebra
  haveI : ∀ c, IsScalarTower R O (L c) := fun c => IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap F (L c) (algebraMap R F x) =
      algebraMap F (L c) (algebraMap O F (algebraMap R O x))
    rw [IsScalarTower.algebraMap_apply R O F x])
  have hded : ∀ c, IsDedekindDomain (integralClosure O (L c)) := fun c =>
    (ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F (L c)).1
  have hfr : ∀ c, IsFractionRing (integralClosure O (L c)) (L c) := fun c =>
    integralClosure.isFractionRing_of_finite_extension F (L c)
  have hset : ∀ c, ValPl.PlacesOver O (L c) = HNm.OverR R F (L c) p := fun c => by
    ext w
    simp only [ValPl.PlacesOver, HNm.OverR, Set.mem_ofPred_eq]
    rw [← ValPl.placesOver_iff_loc (R := R) p w]
    rfl
  have hG : ∀ c, ∃ gc : L c, gc ≠ 0 ∧ (∀ w ∈ ValPl.PlacesOver O (L c), w gc = n c w) ∧
      ∀ y, (∀ w ∈ ValPl.PlacesOver O (L c), 0 ≤ w y + (n c w : WithTop ℤ)) ↔
        gc * y ∈ integralClosure O (L c) := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨gc, hg0, hgv⟩ := HDiscVal.exists_val_eq O F (n c)
    refine ⟨gc, hg0, hgv, fun y => ?_⟩
    rw [HDiscVal.mem_integralClosure_iff O F]
    refine forall₂_congr fun w hw => ?_
    rw [AddValuation.map_mul, hgv w hw, add_comm]
  choose gc hgc0 hgcv hgciff using hG
  have hbI : ∀ k c, gc c * b k c ∈ integralClosure O (L c) := fun k c =>
    (hgciff c _).mp (fun w hw => hb k c w (hset c ▸ hw))
  obtain ⟨nn, t, u, -, hdisc⟩ := HDiscLat.lattice_main (R := O) (F := F) hirr gc hgc0 hm b hbI hli
  set Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
    (_ : w ∈ HNm.OverR R F (L c) p), (HNm.fz F w : ℤ) * n c w with hNc
  have hN : ∀ c, ∃ uc : O, IsUnit uc ∧ Algebra.norm F (gc c) =
      algebraMap R F g ^ Nc c * algebraMap O F uc := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨uc, huc, hn⟩ := ValPl.norm_eq_places (O := O) (F := F) (gc c) (hgc0 c) hirr
    refine ⟨uc, huc, ?_⟩
    rw [hn, ← IsScalarTower.algebraMap_apply R O F g, hset c]
    congr 2
    refine finsum_congr fun w => finsum_congr fun hw => ?_
    rw [← hset c] at hw
    rw [hgcv c w hw, WithTop.untopD_coe]
    rfl
  choose uc huc hNe using hN
  set X := algebraMap R F g with hX
  have hX0 : X ≠ 0 := by
    rw [hX, map_ne_zero_iff _ (IsFractionRing.injective R F)]
    rintro rfl
    have : p = ⊥ := by rw [hg, Ideal.span_singleton_eq_bot]
    subst this
    simp at hp
  let U : Oˣ := ∏ c, (huc c).unit
  have hprod : ∏ c, Algebra.norm F (gc c) = X ^ (∑ c, Nc c) * algebraMap O F (U : O) := by
    rw [Finset.prod_congr rfl fun c _ => hNe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0,
      ← map_prod]
    congr 2
    simp only [U, Units.coe_prod, IsUnit.unit_spec]
  rw [hprod] at hdisc
  set Dt := (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det with hDt
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl
    ((u : O) * ((algebraMap R O g) ^ (2 * nn + t)) * ((U⁻¹ : Oˣ) : O) * ((U⁻¹ : Oˣ) : O))
  refine ⟨a, s, s.2, ?_⟩
  have hsF : algebraMap O F (IsLocalization.mk' O a s) * algebraMap R F s = algebraMap R F a := by
    rw [IsScalarTower.algebraMap_apply R O F s, IsScalarTower.algebraMap_apply R O F a, ← map_mul,
      IsLocalization.mk'_spec]
  simp only at has
  rw [← hsF, has]
  congr 1
  set V := algebraMap O F (U : O)
  set V' := algebraMap O F ((U⁻¹ : Oˣ) : O)
  have hU : V * V' = 1 := by
    simp only [V, V']
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : X ^ (2 * ∑ c, Nc c) = (X ^ (∑ c, Nc c)) ^ 2 := by
    rw [mul_comm, zpow_mul]
    norm_cast
  have e1 : algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t) * ((U⁻¹ : Oˣ) : O) *
      ((U⁻¹ : Oˣ) : O)) = algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t)) * V' * V' := by
    simp only [V', map_mul]
  rw [h2, e1, ← hdisc]
  calc Dt * (X ^ ∑ c, Nc c) ^ 2 = Dt * (X ^ ∑ c, Nc c) ^ 2 * (V * V') * (V * V') := by
        rw [hU]; ring
    _ = Dt * ((X ^ ∑ c, Nc c) * V) ^ 2 * V' * V' := by ring

end HDiscOmL

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAF
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem b_mem (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (k : Fin d.del) (c : ι)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.PlOver la c) :
    0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) +
      ((d.ord c (d.Wres c w) d.wF (hd.a4.choose c) : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  obtain ⟨heF, he0⟩ := he c
  have hadm := (d.admissible_over_prime hd h la c w hw).1
  have hthpF : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  obtain ⟨a, ha⟩ : ∃ a : Ω c, d.thp (hd.sel k) c = a • hd.a4.choose c := by
    have he0' : (⟨hd.a4.choose c, heF⟩ : 𝒜 c d.wF) ≠ 0 := by
      intro h0; exact he0 (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp (hd.finrank_one c d.wF)
      ⟨_, hthpF⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  have hb : d.bvecG hd.sel hd.a4.choose k c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    simp only [bvecG]
    rw [ValuationResidueLemmas.ratio_eq he0 ha]
  rw [hb]
  change 0 ≤ d.Wres c w a + _
  by_cases ha0 : a = 0
  · rw [ha0, AddValuation.map_zero, top_add]
    exact le_top
  have hth0 : d.thp (hd.sel k) c ≠ 0 := by
    rw [ha]; exact smul_ne_zero ha0 he0
  rw [← hd.ord_smul c _ hadm a heF he0 ha0, ← ha]
  have hmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  exact_mod_cast hd.ord_nonneg_Thp c _ hadm _ hmem hth0

theorem b_linIndep (hd : d.AxH 𝒜) (h : d.S1) :
    letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
    LinearIndependent (KTf K d.D d.N) (d.bvecG hd.sel hd.a4.choose) := by
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  classical
  obtain ⟨-, hind, -⟩ := hd.a4.choose_spec
  rw [Fintype.linearIndependent_iff]
  intro q hq
  obtain ⟨⟨s, hs⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (KTp K d.D d.N)) Finset.univ q
  choose p hp using fun k => hint k (Finset.mem_univ k)
  have hsH : ∀ c (x : KTp K d.D d.N),
      d.sH c x = d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) := by
    intro c x
    rw [Data.KTtoS, IsFractionRing.lift_algebraMap]
    rfl
  have hzero : ∀ k, p k = 0 := hind p (fun c => by
    have hc := congrFun hq c
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hc
    simp only [Algebra.smul_def] at hc
    calc ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))
        = d.KTtoS h c (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s) *
            ∑ k, algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N) (q k) *
              d.bvecG hd.sel hd.a4.choose k c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hsH, hp k, Algebra.smul_def, map_mul, mul_assoc]
          rfl
      _ = 0 := by rw [hc, mul_zero])
  intro k
  have hk := hp k
  rw [hzero k, map_zero, Algebra.smul_def] at hk
  exact (mul_eq_zero.mp hk.symm).resolve_left
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)

theorem del_eq (hd : d.AxH 𝒜) (h : d.S1) :
    letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
    d.del = ∑ c, Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
  Finset.sum_congr rfl fun c _ => (d.omS_finite hd h c).2.symm

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPtsB
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial MeasureTheory

theorem countable_numberField (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem ST_scale (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ) (y : Fin (d.N + 1 + d.D) → ℂ)
    (hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0) :
    d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t := by
  ext P
  simp only [ST, Set.mem_setOf_eq, NPB.gpt, Fin.cases_succ]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_eq_zero]
  simp [hy i]

theorem gpt_one (t : Fin d.D → Fin (d.N + 1) → ℂ) (t0 : Fin (d.N + 1) → ℂ) :
    NPB.gpt (fun q => t q.1 q.2) (Fin.addCases t0 (fun _ => (1 : ℂ))) =
      fun v : TVar d.D d.N => Fin.cases (motive := fun _ => ℂ) (t0 v.2) (fun i => t i v.2) v.1 := by
  funext v
  rcases v with ⟨a, j⟩
  refine Fin.cases ?_ (fun i => ?_) a <;> simp [NPB.gpt]

theorem fib (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ)
    (y : Fin (d.N + 1 + d.D) → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 →
      eval₂ sg (NPB.gpt (fun q => t q.1 q.2) y) q ≠ 0) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    (d.ST c sg t).Finite ∧ (d.ST c sg t).ncard = d.delc c ∧
      (∀ g : Ω c, tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))
        = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), P g) ∧
      tauPev sg _ hpt (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) =
        ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
          ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
  letI iA : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iB : Algebra (KTf K d.D d.N) ℂ := (tauPev sg _ hpt).toAlgebra
  obtain ⟨hfd, hrank⟩ := d.omS_finite hd h c
  haveI := hfd
  haveI : CharZero (KTf K d.D d.N) := inferInstance
  haveI : Algebra.IsIntegral (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := Algebra.IsSeparable.of_integral _ _
  have hy : ∀ i, y (Fin.natAdd (d.N + 1) i) ≠ 0 := by
    intro i h0
    apply hpt (MvPolynomial.X (i.succ, 0)) (MvPolynomial.X_ne_zero _)
    simp [NPB.gpt, h0]
  have hST : d.ST c sg (fun i j => NPB.gpt (fun q => t q.1 q.2) y (i.succ, j)) = d.ST c sg t :=
    d.ST_scale c sg t y hy
  obtain ⟨hinj, hrange⟩ := d.fibre_core (hd := hd) (h := h) (c := c) (sg := sg)
    (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt)
  rw [hST] at hrange
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact Set.finite_range _
  · rw [← hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, AlgHom.card, hrank]
  · intro g
    have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ
      (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    exact h1
  · have h1 := Algebra.norm_eq_prod_embeddings (KTf K d.D d.N) ℂ (d.rationalBaseRow c)
    rw [← hrange, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
    refine h1.trans (Finset.prod_congr rfl fun σ _ => ?_)
    have hσ : (σ : OmS (Ω c) d.D d.N →+* ℂ).comp (d.KTtoS h c) = tauPev sg _ hpt :=
      RingHom.ext fun x => σ.commutes x
    simp only [rationalBaseRow, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have he := d.emb_sH (h := h) (c := c) (sg := sg)
      (pt := NPB.gpt (fun q => t q.1 q.2) y) (hpt := hpt) (σ : OmS (Ω c) d.D d.N →+* ℂ) hσ
      (MvPolynomial.X (0, j))
    simp only [AlgHom.coe_toRingHom] at he
    rw [he]
    simp [NPB.gpt]

theorem norm_at_sg_B (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have := countable_numberField K
  filter_upwards [NPB.ae_gen (K := K) (D := d.D) (N := d.N) sg] with z hz
  have hG : ∀ (a : Fin d.D → ℕ) (p : MvPolynomial (Fin d.D × Fin (d.N + 1)) K),
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a p → p ≠ 0 →
        eval₂ sg (fun q => d.tOf z q.1 q.2) p ≠ 0 := hz
  obtain ⟨y1, -, hpt1⟩ := NPB.exists_gen sg (fun q => d.tOf z q.1 q.2) hG 1 one_ne_zero
  obtain ⟨hfin, hcard, -, -⟩ := d.fib hd h c sg (d.tOf z) y1 hpt1
  refine ⟨hfin, hcard, ?_, ?_⟩
  · intro g a b t0 _ _ hab hbt
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a -
        C (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) *
          NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, hn, -⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn g, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, eval_C, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    rw [div_eq_iff hbt]
    exact h2
  · intro a b t0 _ hab hbt
    let cX : MvPolynomial (Fin (d.N + 1 + d.D)) ℂ := ∏ P ∈ hfin.toFinset,
      ∑ j, X (Fin.castAdd d.D j) * C (P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)))
    have hcX : ∀ y, eval y cX = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        ∑ j, y (Fin.castAdd d.D j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) := by
      intro y
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      simp only [cX, map_prod, map_sum, map_mul, eval_X, eval_C]
    have hQ : NPB.psi sg (fun q => d.tOf z q.1 q.2) a - cX * NPB.psi sg (fun q => d.tOf z q.1 q.2) b = 0 := by
      by_contra hQ
      obtain ⟨y, hy, hpt⟩ := NPB.exists_gen sg _ hG _ hQ
      obtain ⟨-, -, -, hn⟩ := d.fib hd h c sg (d.tOf z) y hpt
      apply hy
      have h1 := congrArg (tauPev sg _ hpt) hab
      rw [map_mul, hn, tauPev_apply, tauPev_apply] at h1
      rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, ← h1, sub_self]
    have h2 := congrArg (eval (Fin.addCases t0 (fun _ => (1 : ℂ)))) hQ
    rw [map_sub, map_mul, hcX, NPB.eval_psi, NPB.eval_psi, d.gpt_one, map_zero, sub_eq_zero] at h2
    simp only [Fin.addCases_left] at h2
    rw [div_eq_iff hbt]
    exact h2

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

