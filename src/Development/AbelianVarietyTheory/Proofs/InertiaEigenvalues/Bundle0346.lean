import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisDiscRingHomExtOfAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.AcrisDiscExt

theorem isUnit_natCast_of {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hu : IsUnit (l : R)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : R) := by
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have h : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm
  have h' := h.map f
  rw [map_natCast] at h'
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (hu.pow v).mul h'

theorem norm_l_disc_le (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) :
    ‖((l : ℕ) : Disc l u ρ)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : Disc l u ρ) = ofPre l u ρ (algebraMap A (PreDisc l u ρ) ((l : A) ^ 1 * u ^ 0) *
      IsLocalization.Away.invSelf (l : A) ^ 0) := by
    simp
  rw [e, norm_ofPre]
  refine gauge_le l u ρ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, ?_, rfl⟩)
  rw [pow_zero, pow_zero, pow_one, one_mul, inv_mul_cancel₀ hl0.ne']

theorem norm_pow_mul_le (l : ℕ) [Fact l.Prime] {K : FinExt l} (bk : BK K) (w : bk.DA bk.ρ₀) (r : ℕ) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r * w‖ ≤ (l : ℝ)⁻¹ ^ r * ‖w‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_l_disc_le l _ _) ih (norm_nonneg _) (by positivity))

theorem acris_disc_ext : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (γ γ' : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = γ' (algebraMap (Ainf l) (Per.Acris l) a)) → (∀ x, ‖γ x‖ ≤ 1) → (∀ x, ‖γ' x‖ ≤ 1) → γ = γ' := by
  intro l hl K bk γ γ' h hγ hγ'

  have h0 : ∀ s : Per.Acris0 l,
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) = γ' (algebraMap (Per.Acris0 l) (Per.Acris l) s) := by
    intro s
    obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
    have e : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a :=
      Subtype.ext (by simpa using hn)
    have e' := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e
    rw [map_mul, map_pow, map_natCast, ← GlobalTheory.RingIface.tower l] at e'
    have e1 := congrArg γ e'
    have e2 := congrArg γ' e'
    rw [map_mul, map_pow, map_natCast] at e1 e2
    refine ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n).mul_right_cancel ?_
    exact e1.trans ((h a).trans e2.symm)
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
  ext x
  have hb : ∀ r : ℕ, ‖γ x - γ' x‖ ≤ 2 * (l : ℝ)⁻¹ ^ r := by
    intro r
    obtain ⟨s, z, rfl⟩ := (acris_basic l).2.2.1 x r
    have hs := h0 s
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, hs, add_sub_add_left_eq_sub,
      ← mul_sub]
    have hw : ‖γ z - γ' z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hγ z, hγ' z])
    refine (norm_pow_mul_le l bk (γ z - γ' z) r).trans ?_
    exact mul_comm ((l : ℝ)⁻¹ ^ r) _ ▸ mul_le_mul_of_nonneg_left hw (by positivity)
  have ht : Filter.Tendsto (fun r : ℕ => 2 * (l : ℝ)⁻¹ ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hl1).const_mul 2
  have hz : ‖γ x - γ' x‖ ≤ 0 := ge_of_tendsto' ht hb
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hz)

end GlobalTheory.AcrisDiscExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZero
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem acris_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  intro l _ x y hxy
  have hl : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hρ0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr hl0
  have hG := isGauss_gC_target l (l : ℝ)⁻¹ le_rfl hρ1
  have hc : gC l (l : ℝ)⁻¹ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l)) = (l : ℝ)⁻¹ := by
    rw [hG.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ0.le
  have h0 : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) = 0 := by
    have h := hG.2.2.2.1 0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l))
    rw [zero_mul, hc] at h
    have : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) * (1 - (l : ℝ)⁻¹) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · linarith
  by_contra h
  push_neg at h
  have hx := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x h.1 (l : ℝ)⁻¹ le_rfl hρ1
  have hy := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y h.2 (l : ℝ)⁻¹ le_rfl hρ1
  have hm := hG.2.2.2.1 x y
  rw [hxy, h0] at hm
  have := mul_pos hx hy
  linarith

end GlobalTheory.PMon.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationRadiusLaws
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable (l : ℕ) [Fact l.Prime]

lemma vrlaw_one_lt : (1 : ℝ) < l := by
  exact_mod_cast (Fact.out : l.Prime).one_lt

lemma vrlaw_rad (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hl := vrlaw_one_lt l
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hl.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)

lemma vrlaw_gC_zero (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hG := isGauss_gC_target l ρ h0 h1
  have hm := hG.2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1] at hm
  have : gC l ρ 0 * (1 - ρ) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h (by linarith)

theorem vr_laws : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), 0 < r → r ≤ 1 →
    (∀ x y : Formalism.Per.Acris l, x ≠ 0 → y ≠ 0 → vr l r (x * y) = vr l r x + vr l r y) ∧
    (∀ x : Formalism.Per.Acris l, x ≠ 0 → φc l x ≠ 0 ∧ vr l r (φc l x) = l * vr l (r / l) x) ∧
    (∀ (x : Formalism.Per.Acris l) (n : ℕ), x ≠ 0 → vr l r ((l : Formalism.Per.Acris l) ^ n * x) = n * r + vr l r x) ∧
    ∀ x : Formalism.Per.Acris l, x ≠ 0 → vr l r x = -Real.logb l (gC l ((l : ℝ) ^ (-r)) x) := by
  intro l _ r hr0 hr1
  have hl := vrlaw_one_lt l
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hρ0, hρ1⟩ := vrlaw_rad l r hr0 hr1
  set ρ : ℝ := (l : ℝ) ^ (-r) with hρ
  have hG := isGauss_gC_target l ρ hρ0 hρ1
  have hpos : ∀ x : Formalism.Per.Acris l, x ≠ 0 → 0 < gC l ρ x := fun x hx => GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ hρ0 hρ1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    simp only [vr]
    rw [← hρ, hG.2.2.2.1 x y, Real.logb_mul (hpos x hx).ne' (hpos y hy).ne']
    ring
  · intro x hx
    have hl' : (0 : ℝ) < l := hl0
    have hrl0 : 0 < r / l := div_pos hr0 hl'
    have hrl1 : r / l ≤ 1 := by
      rw [div_le_one hl']; linarith
    obtain ⟨hσ0, hσ1⟩ := vrlaw_rad l (r / l) hrl0 hrl1
    have he : ρ ^ ((1 : ℝ) / l) = (l : ℝ) ^ (-(r / l)) := by
      rw [hρ, ← Real.rpow_mul hl0.le]
      congr 1
      ring
    have hF := GlobalTheory.T.gaussNormAcris_frobenius_eq_pow_root_radius l ρ hρ0 hρ1 x
    rw [he] at hF
    have hxp : 0 < gC l ((l : ℝ) ^ (-(r / l))) x := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ hσ0 hσ1
    refine ⟨?_, ?_⟩
    · intro h0
      rw [h0, vrlaw_gC_zero l ρ hρ0 hρ1] at hF
      exact (pow_pos hxp l).ne' hF.symm
    · simp only [vr]
      rw [← hρ, hF, Real.logb_pow]
      ring
  · intro x n hx
    have hpow : ∀ m : ℕ, gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', mul_assoc, hG.2.2.2.1, ih, (GlobalTheory.T.gaussNormAcris_basic_values l ρ hρ0 hρ1).2.1]
        ring
    simp only [vr]
    rw [← hρ, hpow n, Real.logb_mul (pow_pos (by rw [hρ]; exact Real.rpow_pos_of_pos hl0 _) n).ne' (hpos x hx).ne', Real.logb_pow,
      hρ, Real.logb_rpow hl0 hl.ne']
    ring
  · intro x _
    rfl

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisExistsComp
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.coeff_mem_of_mem_map {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (i : ι) (J : Ideal S) {y : A} (hy : y ∈ J.map s) : TB.c i y ∈ J := by
  have key : ∀ a, TB.c i (a * y) ∈ J := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      intro a
      rw [mul_comm, TB.c_mul]
      exact J.mul_mem_right _ hw
    | zero => intro a; rw [mul_zero, map_zero]; exact J.zero_mem
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add]; exact J.add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

def TopBasis.comp {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (TB : TopBasis s I ι) {A' : Type} [CommRing A'] {t : A →+* A'} {κ : Type}
    (TB' : TopBasis t (I.map s) κ) : TopBasis (t.comp s) I (ι × κ) where
  b p := t (TB.b p.1) * TB'.b p.2
  c p := (TB.c p.1).comp (TB'.c p.2)
  c_mul p a x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.coe_comp]
    rw [TB'.c_mul, TB.c_mul]
  c_self p := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [TB'.c_mul, TB'.c_self, mul_one, TB.c_self]
  c_ne p q h := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [TB'.c_mul]
    by_cases hj : p.2 = q.2
    · rw [hj, TB'.c_self, mul_one, TB.c_ne]
      intro hi; exact h (Prod.ext hi hj)
    · rw [TB'.c_ne _ _ hj, mul_zero, map_zero]
  fin x n := by
    have hS := TB'.fin x n
    refine ((Set.Finite.biUnion hS fun j _ => TB.fin (TB'.c j x) n).prod hS).subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq, AddMonoidHom.coe_comp, Function.comp_apply] at hp
    have h2 : TB'.c p.2 x ∉ (I.map s) ^ n := fun h =>
      hp (TB.coeff_mem_of_mem_map p.1 _ (by rwa [← Ideal.map_pow] at h))
    exact ⟨Set.mem_biUnion (x := p.2) h2 hp, h2⟩
  approx x n F hF := by
    classical
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.coe_comp] at hF ⊢
    have hS := TB'.fin x n
    set G : Finset κ := F.image Prod.snd ∪ hS.toFinset with hG
    set Fi : Finset ι := F.image Prod.fst with hFi
    have h1 : x - ∑ j ∈ G, t (TB'.c j x) * TB'.b j ∈ (I ^ n).map (t.comp s) := by
      have := TB'.approx x n G (fun j hj => by
        by_contra h
        exact hj (Finset.mem_union_right _ (hS.mem_toFinset.2 h)))
      rwa [← Ideal.map_pow, Ideal.map_map] at this
    have h2 : ∀ j, t (TB'.c j x) * TB'.b j - ∑ i ∈ Fi.filter (fun i => (i, j) ∈ F),
        t (s (TB.c i (TB'.c j x))) * (t (TB.b i) * TB'.b j) ∈ (I ^ n).map (t.comp s) := by
      intro j
      have := TB.approx (TB'.c j x) n (Fi.filter (fun i => (i, j) ∈ F)) (fun i hi => by
        apply hF (i, j)
        intro hij
        exact hi (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hij, hij⟩))
      have h' := Ideal.mem_map_of_mem t this
      rw [Ideal.map_map] at h'
      have h'' := Ideal.mul_mem_right (TB'.b j) _ h'
      convert h'' using 1
      rw [map_sub, map_sum, sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul]; ring
    have hsub : F ⊆ Fi ×ˢ G := fun p hp =>
      Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)⟩
    have h3 : ∑ p ∈ F, t (s (TB.c p.1 (TB'.c p.2 x))) * (t (TB.b p.1) * TB'.b p.2) =
        ∑ j ∈ G, ∑ i ∈ Fi.filter (fun i => (i, j) ∈ F), t (s (TB.c i (TB'.c j x))) * (t (TB.b i) * TB'.b j) := by
      simp_rw [Finset.sum_filter]
      rw [← Finset.sum_product_right (s := Fi) (t := G)
        (f := fun p => if p ∈ F then t (s (TB.c p.1 (TB'.c p.2 x))) * (t (TB.b p.1) * TB'.b p.2) else 0)]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    rw [h3]
    have := Ideal.add_mem _ h1 (Ideal.sum_mem (t := G) _ fun j _ => h2 j)
    convert this using 1
    rw [Finset.sum_sub_distrib]; ring
  complete := by rw [← Ideal.map_map]; exact TB'.complete
  i₀ := (TB.i₀, TB'.i₀)
  b_i₀ := by simp [TB.b_i₀, TB'.b_i₀]

theorem topBasis_comp_exists : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type)
    (TB : TopBasis s I ι) (A' : Type) [CommRing A'] (t : A →+* A') (I' : Ideal A) (κ : Type)
    (TB' : TopBasis t I' κ), I' = I.map s → ∃ TC : TopBasis (t.comp s) I (ι × κ),
      (∀ i j, TC.b (i, j) = t (TB.b i) * TB'.b j) ∧ ∀ i j x, TC.c (i, j) x = TB.c i (TB'.c j x) := by
  intro S A _ _ s I ι TB A' _ t I' κ TB' hI
  subst hI
  exact ⟨TB.comp TB', fun _ _ => rfl, fun _ _ _ => rfl⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroLowCoeffThreeNilpotents
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem exists_pow_mul_pow_mul_pow_dvd_prod_pow {B : Type} [CommRing B] {ι : Type} (t x y : B)
    (ξ : ι → B) (hξ : ∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) (u : ι → ℕ) (s : Finset ι) :
    ∃ a b c : ℕ, a + b + c = ∑ q ∈ s, u q ∧ t ^ a * x ^ b * y ^ c ∣ ∏ q ∈ s, ξ q ^ u q := by
  classical
  induction s using Finset.induction_on
  case empty => exact ⟨0, 0, 0, by simp, by simp⟩
  case insert q s hq ih =>
    obtain ⟨a, b, c, habc, hd⟩ := ih
    rw [Finset.sum_insert hq, Finset.prod_insert hq]
    rcases hξ q with ⟨r, hr⟩ | hx | hy
    · refine ⟨u q + a, b, c, by omega, ?_⟩
      have h := mul_dvd_mul (dvd_mul_right (t ^ u q) (r ^ u q)) hd
      rw [hr, mul_pow]
      convert h using 1
      ring
    · refine ⟨a, u q + b, c, by omega, ?_⟩
      have h := mul_dvd_mul_left (x ^ u q) hd
      rw [hx]
      convert h using 1
      ring
    · refine ⟨a, b, u q + c, by omega, ?_⟩
      have h := mul_dvd_mul_left (y ^ u q) hd
      rw [hy]
      convert h using 1
      ring

theorem aeval_eq_zero_of_low_coeff_of_three_nilpotent :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ)
      (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 →
      (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) →
      (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t x y K m ξ F ht hx hy hξ hF
  classical
  rw [F.as_sum, map_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hu : u.degree < K + m
  · rw [hF u hu, zero_mul]
  · obtain ⟨a, b, c, habc, hd⟩ := exists_pow_mul_pow_mul_pow_dvd_prod_pow t x y ξ hξ u u.support
    have hdeg : u.degree = ∑ q ∈ u.support, u q := rfl
    have hzero : t ^ a * x ^ b * y ^ c = 0 := by
      by_cases hc : m ≤ c
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
        rw [pow_add, hy]
        simp
      · by_cases hb : 2 ≤ b
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
          rw [pow_add, pow_two, hx]
          simp
        · have hK : K ≤ a := by omega
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
          rw [pow_add, ht]
          simp
    rw [hzero, zero_dvd_iff] at hd
    rw [Finsupp.prod]
    simp only [hd, mul_zero]

end GlobalTheory.NewPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfLowCoeffOfNilpotentMultipleStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_of_low_coeff_of_nilpotent_multiple : ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t : B) (K : ℕ) (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → (∀ q, t ∣ ξ q) → (∀ u : ι →₀ ℕ, u.degree < K → algebraMap O B (F.coeff u) = 0) → MvPolynomial.aeval ξ F = 0 := by
  first | exact @GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero | exact GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero | (intros; apply GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfUnitBoundedTeichmullerFlatDenominators
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BddDen

variable {l : ℕ} [hl : Fact l.Prime]

abbrev redMap {K : FinExt l} (bk : BK K) : bk.S →+* (OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) :=
  (Ideal.Quotient.mk _).comp ((Per.θ l).comp bk.ev)

theorem redMap_coe {K : FinExt l} (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    redMap bk (p : bk.S) = p.eval₂ ((redMap bk).comp PowerSeries.C) (redMap bk X) := by
  have h : (redMap bk).comp (Polynomial.coeToPowerSeries.ringHom) =
      Polynomial.eval₂RingHom ((redMap bk).comp PowerSeries.C) (redMap bk X) :=
    Polynomial.ringHom_ext (fun a => by simp) (by simp)
  exact congrArg (fun f => f p) h

theorem redMap_E {K : FinExt l} (bk : BK K) : redMap bk bk.E = redMap bk X ^ bk.Ep.natDegree := by
  rw [BK.E, redMap_coe, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree,
    map_one, one_mul, add_eq_right]
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  have hl0 : ((l : ℕ) : OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.comp_apply, hc, map_mul, map_mul, map_natCast, map_natCast, hl0, zero_mul, zero_mul]

theorem flat_not_isUnit {K : FinExt l} (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  have h0 : redMap bk bk.E = 0 := by
    have hk : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker] at hk
    simp only [redMap, RingHom.comp_apply, hk, map_zero]
  rw [redMap_E, redMap, RingHom.comp_apply, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h0
  have hX : IsUnit (bk.ev X) := bk.ev_X ▸ hu.map (WittVector.teichmuller l)
  exact PI.ArtSch.OC_l_not_unit l (isUnit_of_dvd_unit h0 ((hX.map (Per.θ l)).pow _))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) →
    ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  intro l _ K bk a ha n
  have ha0 : a.coeff 0 ≠ 0 := by
    intro h
    have h1 := ha.map (WittVector.constantCoeff (p := l) (R := Cb l))
    rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, h, map_zero] at h1
    exact not_isUnit_zero h1
  have hv1 : PI.ArtSch.valb l bk.flat < 1 := by
    by_contra h
    push_neg at h
    exact flat_not_isUnit bk (isUnit_of_dvd_one
      (GlobalTheory.ArtinSchreierTilt.tiltDiv l 1 bk.flat (by rw [map_one]; exact h)))
  have hv0 : 0 < PI.ArtSch.valb l (a.coeff 0) := by
    rw [pos_iff_ne_zero]
    exact fun h => ha0 ((PreTilt.map_eq_zero (PadicComplexInt.integers l)).1 h)
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hv0 hv1
  obtain ⟨c, hc⟩ := GlobalTheory.ArtinSchreierTilt.tiltDiv l (bk.flat ^ m₀) (a.coeff 0) (by rw [map_pow]; exact hm₀.le)
  obtain ⟨b, hb⟩ : (l : Ainf l) ∣ a - WittVector.teichmuller l (a.coeff 0) := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  have hxy : WittVector.teichmuller l c * a =
      bk.ev X ^ m₀ + (l : Ainf l) * (WittVector.teichmuller l c * b) := by
    have ha' : a = WittVector.teichmuller l (a.coeff 0) + (l : Ainf l) * b := by linear_combination hb
    have ht : WittVector.teichmuller l c * WittVector.teichmuller l (a.coeff 0) = bk.ev X ^ m₀ := by
      rw [bk.ev_X, ← map_pow, hc, map_mul, mul_comm]
    rw [ha', mul_add, ht]
    ring
  have h2 := geom_sum₂_mul (bk.ev X ^ m₀) (-((l : Ainf l) * (WittVector.teichmuller l c * b))) n
  refine ⟨m₀ * n, WittVector.teichmuller l c * ∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i),
    -((-(WittVector.teichmuller l c * b)) ^ n), ?_⟩
  rw [pow_mul]
  linear_combination (∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i)) * hxy + h2

end GlobalTheory.BSP.BddDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientFiltrationEveryDeclarationStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientFiltration_every_declaration : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.ambFil (D := D) i r ρ π dc := by
  first | exact @GlobalTheory.Per.AmbFil.main | exact GlobalTheory.Per.AmbFil.main | (intros; apply GlobalTheory.Per.AmbFil.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxComplexPadicCoboundaryAlgebraicIntegerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  first | exact @GlobalTheory.PMon.Ram.approx_algebraic_integer | exact GlobalTheory.PMon.Ram.approx_algebraic_integer | (intros; apply GlobalTheory.PMon.Ram.approx_algebraic_integer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMOfParamRec
section
noncomputable section

namespace GlobalTheory.LiftLeaf

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem atMOfParam_rec {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) : AtMOfParam N A i := by
  intro x _ Sig hX σ hW
  obtain ⟨P, hP, hB⟩ := hX
  refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
  rw [hB.2.2.2.1 w hw.1]
  exact A.pt_loc i P x hP w hw

theorem atMOfParam (D : D7) (i : D.nd.Loc) : AtMOfParam D.nd D.naut i :=
  atMOfParam_rec D.nd D.naut i

end GlobalTheory.LiftLeaf
end
end

