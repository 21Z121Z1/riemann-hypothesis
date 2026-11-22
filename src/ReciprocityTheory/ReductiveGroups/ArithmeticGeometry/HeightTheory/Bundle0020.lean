import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.PlaceSumHeights.PlaceSumStatements.PlaceSumTheorem.HtPlacesSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GenericPointHeight.GenericPointStatements.GenericPointTheorem.HtGenericPt

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscPointwise
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

theorem disc_pointwise (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖ ≤
        d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) +
          2 * ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
            -Real.log (d.nrm c d.wF (hd.a4.choose c) P) := by
  classical
  obtain ⟨hb0, habE, m, hm0, hma, hmb⟩ := hab
  have hDe := d.de_ne_zero hd h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at habE
    exact mul_ne_zero hDe ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0) habE.symm
  have heW : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hST := MeasureTheory.ae_all_iff.mpr fun c => d.norm_at_sg hd h c sg
  filter_upwards [hST, d.de_fibre hd h a b ⟨hb0, habE, m, hm0, hma, hmb⟩ sg,
    d.ae_evT_ne_zero sg a ha0 m hm0 hma, d.ae_evT_ne_zero sg b hb0 m hm0 hmb] with z hz hfib haz hbz
  set e := hd.a4.choose with he
  set t := d.tOf z with ht
  set s : Fin d.del → ℝ := fun k => d.supN sg d.wF (d.thp (hd.sel k)) with hsdef
  have hfin : ∀ c, (d.ST c sg t).Finite := fun c => (hz c).1
  have hcard : ∀ c, (d.ST c sg t).ncard = d.delc c := fun c => (hz c).2.1
  let _ : ∀ c, Fintype (d.ST c sg t) := fun c => (hfin c).fintype
  let M : (Σ c, d.ST c sg t) → Fin d.del → ℂ := fun r k =>
    (r.2 : Ω r.1 →+* ℂ) (ratio (Ω := Ω r.1) (d.thp (hd.sel k) r.1) (e r.1))
  let ν : (Σ c, d.ST c sg t) → ℝ := fun r => d.nrm r.1 d.wF (e r.1) r.2
  have hR : Fintype.card (Σ c, d.ST c sg t) = d.del := by
    rw [Fintype.card_sigma]
    unfold Data.del
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hcard c, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hν : ∀ r, 0 < ν r := fun r => hd.nrm_pos r.1 r.2 (heW r.1).1 (heW r.1).2
  have hM : ∀ r k, ‖M r k‖ * ν r ≤ s k := by
    rintro ⟨c, P, hP⟩ k
    have hth : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
    have hline := eq_ratio_smul_on_line d (hd := hd) hth (heW c).1 (heW c).2
    have h1 : ‖P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))‖ * d.nrm c d.wF (e c) P ≤
        d.nrm c d.wF (d.thp (hd.sel k) c) P := by
      by_cases hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c) = 0
      · rw [hr, map_zero, norm_zero, zero_mul]
        rw [hr, zero_smul] at hline
        rw [hline, hd.nrm_zero]
      · have h2 := hd.nrm_smul c P _ (heW c).1 (heW c).2 hr
        rw [← hline] at h2
        rw [h2]
    have hmem : d.thp (hd.sel k) ∈ d.Thp := by
      rw [hd.Thp_span]
      exact Submodule.subset_span ⟨_, rfl⟩
    have h3 : d.nrm c d.wF (d.thp (hd.sel k) c) P ≤ s k :=
      le_ciSup (f := fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 d.wF (d.thp (hd.sel k) p.1) p.2)
        (hd.bdd sg d.wF (d.thp (hd.sel k)) (Or.inr (Or.inl ⟨hmem, rfl⟩))) ⟨c, ⟨P, hP.1⟩⟩
    exact h1.trans h3
  have hG : (Matrix.of fun k l : Fin d.del => ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
        P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) *
          P (ratio (Ω := Ω c) (d.thp (hd.sel l) c) (e c))) =
      Matrix.of fun k l => ∑ r, M r k * M r l := by
    ext k l
    simp only [Matrix.of_apply, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  have hq : d.evT sg 0 t a / d.evT sg 0 t b = (Matrix.of fun k l : Fin d.del => ∑ r, M r k * M r l).det := by
    rw [hfib hbz, hG]
  set D0 := (Matrix.of fun k l : Fin d.del => ∑ r, M r k * M r l).det with hD0
  have hD0ne : D0 ≠ 0 := by
    rw [← hq]
    exact div_ne_zero haz hbz
  have hlhs : Real.log ‖d.evT sg 0 t a‖ - Real.log ‖d.evT sg 0 t b‖ = Real.log ‖D0‖ := by
    rw [← hq, norm_div, Real.log_div (norm_ne_zero_iff.mpr haz) (norm_ne_zero_iff.mpr hbz)]
  have hH := hadamard_gram hR M ν s hν hM
  have hpos : 0 < ‖D0‖ * ∏ r, ν r ^ 2 :=
    mul_pos (norm_pos_iff.mpr hD0ne) (Finset.prod_pos fun r _ => pow_pos (hν r) 2)
  have hRpos : 0 < (d.del : ℝ) ^ d.del * ∏ k, s k ^ 2 := lt_of_lt_of_le hpos hH
  have hlog := Real.log_le_log hpos hH
  have hs : ∀ k, s k ^ 2 ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hRpos.ne')) k (Finset.mem_univ _)
  have hdel : (d.del : ℝ) ^ d.del ≠ 0 := left_ne_zero_of_mul hRpos.ne'
  rw [Real.log_mul (norm_ne_zero_iff.mpr hD0ne)
      (Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero 2 (hν r).ne'),
    Real.log_prod (fun r _ => pow_ne_zero 2 (hν r).ne'),
    Real.log_mul hdel (Finset.prod_ne_zero_iff.mpr fun k _ => hs k),
    Real.log_prod (fun k _ => hs k)] at hlog
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  have hsumν : ∑ r, Real.log (ν r) = ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
      Real.log (d.nrm c d.wF (e c) P) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  have hsumneg : ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), -Real.log (d.nrm c d.wF (e c) P) =
      -∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), Real.log (d.nrm c d.wF (e c) P) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, Finset.sum_neg_distrib]
  rw [hlhs, hsumneg, ← hsumν]
  have e1 : ∑ r, (2 : ℝ) * Real.log (ν r) = 2 * ∑ r, Real.log (ν r) := by rw [Finset.mul_sum]
  have e2 : ∑ k, (2 : ℝ) * Real.log (s k) = 2 * ∑ k, Real.log (s k) := by rw [Finset.mul_sum]
  rw [e1, e2] at hlog
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscA
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

theorem disc_lattice (hd : d.AxH 𝒜) (h : d.S1) :
    d.De hd h ≠ 0 ∧ ∀ la, (d.htOf hd h).Ila la ≠ ⊤ ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la := by
  have key : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (d.htOf hd h).Ila la ≠ ⊤ ∧ d.De hd h ≠ 0 ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la := by
    intro la
    obtain ⟨n, t, N, hI, hN, u, hu, hDe⟩ := d.disc_at hd h la
    have hIL : d.IL h hd.sel hd.a4.choose la = (((d.htOf hd h).Ila la).toNat : ℝ) := rfl
    refine ⟨by rw [hI]; exact ENat.coe_ne_top n, ?_, ?_⟩
    · rw [hDe, algK_unif]
      exact mul_ne_zero (zpow_ne_zero _ ((map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr
        (unifOp_irreducible d.D d.N la).ne_zero))
        ((map_ne_zero_iff _ (OpToKT_injective d.D d.N la)).mpr hu.ne_zero)
    · rw [hIL, hI, d.gOrd_eq la hu hDe, hN, ENat.toNat_natCast]
      push_cast
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  let la0 : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)⟩
  exact ⟨(key la0).2.1, fun la => ⟨(key la).1, (key la).2.2⟩⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces
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

theorem places_over_la (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    (d.PlOver la c).Finite ∧
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
        (d.fze h c w : ℤ) * ramIdx (K := K) (d.Wres c w) la) = d.delc c :=
  HtPlacesSum 𝒜 d hd h la c

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Imports
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

theorem exists_generic (hd : d.AxH 𝒜) (h : d.S1) :
    (∃ x : Fin (d.N + 1) → K, ∀ c, d.wx x c ≠ 0) ∧
    (∃ ta' : ∀ c, A c, ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :=
  HtGenericPt 𝒜 d hd h

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormGenericRatioSpec
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem hx4v2_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {g : V}
    (hg : g ≠ 0) (s : Ω) : ratio (Ω := Ω) (s • g) g = s := by
  unfold ratio
  have hex : ∃ a : Ω, s • g = a • g := ⟨s, rfl⟩
  rw [dif_pos hex]
  exact (smul_left_injective Ω hg hex.choose_spec).symm

theorem hx4v2_eq_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (W : Submodule Ω V) (hW : Module.finrank Ω W = 1) {f g : V} (hf : f ∈ W) (hgW : g ∈ W)
    (hg : g ≠ 0) : f = ratio (Ω := Ω) f g • g := by
  have hg' : (⟨g, hgW⟩ : W) ≠ 0 := fun e => hg (congrArg Subtype.val e)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hgW⟩ : W) hg').mp hW ⟨f, hf⟩
  have hex : ∃ a : Ω, f = a • g := ⟨a, (congrArg Subtype.val ha).symm⟩
  unfold ratio
  rw [dif_pos hex]
  exact hex.choose_spec

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hx4v2_ratio_wx (hd : d.AxH 𝒜) (c : ι) (x : Fin (d.N + 1) → K) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  have := hd.tower c
  have hg := hd.w_base c
  have hrep : ∀ j, d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    fun j => hx4v2_eq_ratio_smul _ (hd.finrank_one c d.wL) (hd.w_mem j c) (hd.w_mem (d.jc c) c) hg
  have hsum : d.wx x c = (∑ j, algebraMap K (Ω c) (x j) *
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [hrep j]
    rw [mul_smul, algebraMap_smul]
  rw [hsum, hx4v2_ratio_smul hg]

theorem norm_generic_ratio_spec (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x Q = Q) ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 →
        (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x P) =
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
              Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
                (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)))) := by
  let _ : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨n, b, Q0, M, hQ0, hQ0s, hMs, hM⟩ := d.basis_block0 hd h c
  let r : Fin (d.N + 1) → OmS (Ω c) d.D d.N := fun j =>
    algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))
  let ι0 : KTp K d.D d.N →+* KTf K d.D d.N := algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
  have hQ0' : ι0 Q0 ≠ 0 := fun e =>
    hQ0 (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (by rw [e, map_zero]))
  have key : ∀ a : Fin (d.N + 1) → KTp K d.D d.N,
      Algebra.norm (KTf K d.D d.N) (∑ j, ι0 (a j) • r j) = ι0 (∑ j, a j • M j).det / ι0 Q0 ^ n := by
    intro a
    rw [Algebra.norm_eq_matrix_det b, map_sum]
    simp_rw [map_smul]
    have hmat : (∑ j, ι0 (a j) • Algebra.leftMulMatrix b (r j)) =
        (ι0 Q0)⁻¹ • (∑ j, a j • M j).map ι0 := by
      ext i i'
      rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.sum_apply, map_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM j, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, map_mul]
      ring
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
    have hdet : ((∑ j, a j • M j).map ι0).det = ι0 (∑ j, a j • M j).det :=
      (RingHom.map_det ι0 _).symm
    rw [hdet, inv_pow, div_eq_mul_inv, mul_comm]
  have hw0 : d.rationalBaseRow c = ∑ j, ι0 (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • r j := by
    simp only [Data.rationalBaseRow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, r]
  refine ⟨(∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det, Q0 ^ n, pow_ne_zero _ hQ0,
    fun x => by rw [map_pow, hQ0s], ?_, ?_⟩
  · show ι0 _ = ι0 (Q0 ^ n) * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)
    rw [hw0, key, map_pow]
    field_simp
  · intro x _
    have hs : d.sub0 x (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det =
        (∑ j, (MvPolynomial.C (x j) : KTp K d.D d.N) • M j).det := by
      have hmd := RingHom.map_det (d.sub0 x : KTp K d.D d.N →+* KTp K d.D d.N)
        (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j)
      rw [RingHom.coe_coe] at hmd
      rw [hmd]
      congr 1
      ext i i'
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum, map_mul, RingHom.coe_coe, hMs]
      simp
    have hr : algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)) =
        ∑ j, ι0 (MvPolynomial.C (x j) : KTp K d.D d.N) • r j := by
      rw [d.hx4v2_ratio_wx hd c x, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      congr 1
      simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N) (x j)).symm
    show ι0 _ = ι0 (Q0 ^ n) * _
    rw [hs, hr, key, map_pow]
    field_simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

