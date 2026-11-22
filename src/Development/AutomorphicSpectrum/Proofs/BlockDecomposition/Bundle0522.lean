import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0510
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0507
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariant
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem gramQ_mul_right (D : D7) (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    gramQ V (x * a) = (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * gramQ V x * a := by
  have hm : (x * a).map (D.sp.cm.sig : D.host.E → D.host.E) =
      x.map (D.sp.cm.sig : D.host.E → D.host.E) * a.map (D.sp.cm.sig : D.host.E → D.host.E) :=
    Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
  unfold gramQ
  rw [hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def congrEquiv (D : D7) (V : HSp D) {r : ℕ} (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E)
    (ha : a.det ≠ 0) :
    {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = (congrH a β).1} :=
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hi : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
  have hi' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hu
  have hu' : IsUnit (a⁻¹).det := by
    have := congrArg Matrix.det hi
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at this)
  have hc : ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
      (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have hm : (a * a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) =
        a.map (D.sp.cm.sig : D.host.E → D.host.E) * (a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) :=
      Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [← hm, hi, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  { toFun := fun x => ⟨x.1 * a, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a x.1 hu]
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]; rfl⟩
    invFun := fun x => ⟨x.1 * a⁻¹, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a⁻¹ x.1 hu']
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]
      change ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
        ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a) * a⁻¹ = β.1
      calc _ = (((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
              (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ) * β.1 * (a * a⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = β.1 := by rw [hc, hi, Matrix.one_mul, Matrix.mul_one]⟩
    left_inv := fun x => Subtype.ext (by
      change x.1 * a * a⁻¹ = x.1
      rw [Matrix.mul_assoc, hi, Matrix.mul_one])
    right_inv := fun x => Subtype.ext (by
      change x.1 * a⁻¹ * a = x.1
      rw [Matrix.mul_assoc, hi', Matrix.mul_one]) }

theorem ifrB_congrH : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r)
    (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  intro D V ν r φ β a ha
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = (congrH a β).1},
        φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = β.1},
        pull a φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) := by
    funext h
    rw [← (congrEquiv D V β a ha).tsum_eq]
    refine tsum_congr fun x => ?_
    have hm : (x.1 * a).map (incA D) = HMul.hMul (x.1.map (incA D)) (a.map (incA D)) :=
      Matrix.map_mul (f := incA D)
    change φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((x.1 * a).map (incA D))) =
      φ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D))) (a.map (incA D)))
    rw [hm, Matrix.mul_assoc]
  unfold IfrB
  rw [key]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobPowRead
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem frob_pow_read {l : ℕ} [Fact l.Prime] (N : ℕ) (a y : Tl l) (b : ℕ → Tl l) (D : ℕ) :
    (a - ∑ i ∈ Finset.range D, b i * y ^ i) ^ l ^ N =
      a ^ l ^ N - ∑ i ∈ Finset.range D, b i ^ l ^ N * (y ^ l ^ N) ^ i := by
  rw [sub_pow_char_pow, sum_pow_char_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i]

theorem oc_eq {l : ℕ} [Fact l.Prime] (K : FinExt l) (c : ↥(OL K)) : oc K c = omC (((c : ↥K.1) : Om l)) := rfl

theorem sys_pow_iter {l : ℕ} [Fact l.Prime] {f : ℕ} {u : ℕ → Tl l} (h : ∀ n, u (n + 1) ^ l ^ f = u n)
    (n m : ℕ) : u (n + m) ^ l ^ (f * m) = u n := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : u (n + (m + 1)) ^ l ^ (f * (m + 1)) = (u (n + m + 1) ^ l ^ f) ^ l ^ (f * m) := by
      rw [← pow_mul, ← pow_add, ← add_assoc]
      congr 2
      ring
    rw [e, h, ih]

theorem fix_ringHom {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖) (h1 : ‖oc K π‖ < 1)
    (hfer : ∀ c : ↥(OL K), ‖oc K c ^ l ^ f - oc K c‖ ≤ ‖oc K π‖) :
    ∃ r₀ : ↥(OL K) →+* Tl l, (∀ c, r₀ c ^ l ^ f = r₀ c) ∧ ∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖ := by
  have hex : ∀ c : ↥(OL K), ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - oc K c‖ ≤ ‖oc K π‖ := fun c =>
    GlobalTheory.T.teichmuller_fixed_point_approximation f _ hf hl h1 (oc K c) (norm_oc_le_one K c) (hfer c)
  choose F hF1 hF2 using hex
  have huniq : ∀ (x : Tl l) (A : ↥(OL K)), x ^ l ^ f = x → ‖sh x - oc K A‖ ≤ ‖oc K π‖ → F A = x := by
    intro x A hx hA
    apply fixed_unique hf (hF1 A) hx
    refine lt_of_le_of_lt (norm_sub_le_of_near hl ?_) h1
    have e : sh (F A) - sh x = (sh (F A) - oc K A) - (sh x - oc K A) := by ring
    rw [e]
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF2 A) (by rw [norm_neg]; exact hA))
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hF1, hF2⟩
  · exact huniq 1 1 (one_pow _) (by rw [map_one, sh_one, sub_self, norm_zero]; exact norm_nonneg _)
  · intro a b
    refine huniq _ _ (by rw [mul_pow, hF1, hF1]) ?_
    rw [map_mul]
    exact near_mul (norm_oc_le_one K b) (hF2 a) (hF2 b)
  · exact huniq 0 0 (zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
      (by rw [map_zero, sh_zero, sub_self, norm_zero]; exact norm_nonneg _)
  · intro a b
    refine huniq _ _ (by rw [add_pow_char_pow, hF1, hF1]) ?_
    rw [map_add]
    exact near_add hl (hF2 a) (hF2 b)

theorem tch_eq {l : ℕ} [Fact l.Prime] (f : ℕ) (hf : 0 < f) (x : Tl l) (hx : x ^ l ^ f = x) (y : Om l)
    (hy : sh x = omC y) : tch l x = rB l y := by
  have hq2 : 2 ≤ l ^ f := by
    have := Nat.pow_le_pow_right (Fact.out : l.Prime).pos hf
    have h2 := (Fact.out : l.Prime).two_le
    simp only [pow_one] at this
    omega
  have hyf : y ^ l ^ f = y := by
    apply omC.injective
    rw [map_pow, ← hy, ← sh_pow, hx]
  exact GlobalTheory.T.teichmuller_character_eq_residue_lift (l ^ f) hq2 (dvd_pow_self l hf.ne') x y hx hyf hy

theorem exp_twist {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f) (hqf : qOf π = l ^ f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖) (h1 : ‖oc K π‖ < 1) (hπ0 : π ≠ 0)
    (hmax : (Ideal.span {π}).IsMaximal) (hfin : Finite (↥(OL K) ⧸ Ideal.span {π}))
    (r₀ : ↥(OL K) →+* Tl l) (hr1 : ∀ c, r₀ c ^ l ^ f = r₀ c) (hr2 : ∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖)
    (hrπ : r₀ π = 0) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) :
    ∃ i : ℕ, ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1)) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_extension_of_embedding K μ
  haveI := hmax
  haveI := hfin
  letI : Field (↥(OL K) ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  have hker : ∀ a ∈ Ideal.span {π}, r₀ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hrπ, mul_zero]
  let α : (↥(OL K) ⧸ Ideal.span {π}) →+* Tl l := Ideal.Quotient.lift _ r₀ hker
  obtain ⟨i, hi⟩ := GlobalTheory.T.finite_field_embeddings_differ_frobenius (l := l) (k := ↥(OL K) ⧸ Ideal.span {π}) (D := Tl l) α ((actT g).comp α)
  refine ⟨i, fun c => ?_⟩
  obtain ⟨c', hc'⟩ := GlobalTheory.T.teichmuller_residue_congruence K π f hf hqf hl h1 hπ0 (r₀ c) c (hr1 c) (hr2 c)
  refine ⟨c', ?_⟩
  have h : actT g (r₀ c) = r₀ c ^ l ^ i := hi (Ideal.Quotient.mk _ c)
  rw [← h, sh_actT, hc', oc_eq, galCp_omC, hg]

theorem tch_clause {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ) (hf : 0 < f)
    (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (r₀ : ↥(OL K) →+* Tl l) (hr1 : ∀ c, r₀ c ^ l ^ f = r₀ c) (i : ℕ)
    (hic : ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1))) :
    ∀ c, ∃ c', tch l (((iterateFrobenius (Tl l) l i).comp r₀) c) = oB K μ (c + π * c') := by
  intro c
  obtain ⟨c', hc'⟩ := hic c
  refine ⟨c', ?_⟩
  rw [RingHom.comp_apply, iterateFrobenius_def]
  have hfix : (r₀ c ^ l ^ i) ^ l ^ f = r₀ c ^ l ^ i := by
    rw [← pow_mul, mul_comm, pow_mul, hr1]
  rw [tch_eq f hf _ hfix _ hc']
  simp only [oB, RingHom.comp_apply]
  rfl

theorem gal_clause {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (g : GQ l) (r₀ : R →+* Tl l) (i : ℕ)
    (x : Tl l) (c : ℕ → R) (D : ℕ) (hd : x ^ D ∣ actT g x - ∑ j ∈ Finset.range D, r₀ (c j) * x ^ j) :
    (x ^ l ^ i) ^ D ∣ actT g (x ^ l ^ i) -
      ∑ j ∈ Finset.range D, ((iterateFrobenius (Tl l) l i).comp r₀) (c j) * (x ^ l ^ i) ^ j := by
  have h := pow_dvd_pow_of_dvd hd (l ^ i)
  rw [frob_pow_read] at h
  have e1 : (x ^ l ^ i) ^ D = (x ^ D) ^ l ^ i := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : actT g (x ^ l ^ i) = actT g x ^ l ^ i := map_pow _ _ _
  have e3 : ∀ j, ((iterateFrobenius (Tl l) l i).comp r₀) (c j) = r₀ (c j) ^ l ^ i := fun j => by
    rw [RingHom.comp_apply, iterateFrobenius_def]
  simp only [e1, e2, e3]
  exact h

end GlobalTheory.CompanionTheory.LTPer.Tilt

open GlobalTheory.CompanionTheory.LTPer.Tilt in

theorem GlobalTheory.CompanionTheory.LTPer.Tilt.tilt_period : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l,
    ∃ (r : ↥(OL K) →+* Tl l) (v : ℕ → Tl l),
      (∀ n, v (n + 1) ^ qOf π = v n) ∧ v 0 ≠ 0 ∧ ‖thB l (tch l (v 0))‖ < 1 ∧
      (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) ∧
      (∀ (g : GQ l) (hg : g ∈ GK K) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
        ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) →
        PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ →
        ∀ n D, v n ^ D ∣ actT g (v n) - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * v n ^ i) ∧
      (μ = K.1.val → ∀ n, ‖thB l (tch l (v n)) - ((z n : Om l) : ℂ_[l])‖ ≤ ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖) := by
  intro l _ K χ π z hLT μ
  obtain ⟨hirr, hz0, hz1, hrec, hgal⟩ := hLT
  obtain ⟨hq2, hlq, hπl, hπ1, -⟩ := GlobalTheory.CompanionTheory.LTPer.uniformiser_facts K π hirr
  obtain ⟨hmax, hfin, f, hf, hqf⟩ := GlobalTheory.T.uniformizer_residue_field_finite_power K π hirr
  have hπ1' : ‖oc K π‖ < 1 := by rw [oc_apply]; exact hπ1
  have hl : ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ := by
    obtain ⟨a, ha⟩ := hπl
    have e : (l : ℂ_[l]) = oc K π * oc K a := by rw [← map_mul, ← ha, map_natCast]
    rw [e, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oc_le_one K a)
  have hπ0 : π ≠ 0 := hirr.ne_zero
  obtain ⟨hzlt, hzgt⟩ := GlobalTheory.T.lubin_tate_sequence_norm_bounds K χ π z ⟨hirr, hz0, hz1, hrec, hgal⟩ hq2 hπ1'
  have hrec' : ∀ n, z (n + 1) ^ l ^ f + ((π : ↥K.1) : Om l) * z (n + 1) = z n := by
    intro n
    have h := hrec n
    rwa [show Nat.card (↥(OL K) ⧸ Ideal.span {π}) = l ^ f from hqf] at h
  have hZ : ∀ n, ‖omC (z (n + 1)) ^ l ^ f - omC (z n)‖ ≤ ‖oc K π‖ := by
    intro n
    have e : omC (z (n + 1)) ^ l ^ f - omC (z n) = -(oc K π * omC (z (n + 1))) := by
      rw [← hrec' n, map_add, map_mul, map_pow, oc_eq]
      ring
    rw [e, norm_neg, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hzlt _).le
  obtain ⟨u, hu1, hu2⟩ := GlobalTheory.T.teichmuller_compatible_sequence_approximation f ‖oc K π‖ hf hl hπ1' (fun n => omC (z n)) (fun n => (hzlt n).le) hZ
  have hu0 : ∀ n, u n ≠ 0 := by
    have h2 : ∀ n, 2 ≤ n → u n ≠ 0 := by
      intro n hn h0
      have h := hu2 n
      rw [h0, sh_zero, zero_sub, norm_neg] at h
      exact absurd (hzgt n hn) (not_lt.2 h)
    intro n
    rw [← sys_pow_iter hu1 n 2]
    exact pow_ne_zero _ (h2 _ (by omega))
  have hfer : ∀ c : ↥(OL K), ‖oc K c ^ l ^ f - oc K c‖ ≤ ‖oc K π‖ := by
    intro c
    obtain ⟨a, ha⟩ := GlobalTheory.T.uniformizer_divides_frobenius_difference K π hmax hfin c
    rw [hqf] at ha
    rw [← map_pow, ← map_sub, ha, map_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oc_le_one K a)
  obtain ⟨r₀, hr1, hr2⟩ := fix_ringHom K π f hf hl hπ1' hfer
  have hrπ : r₀ π = 0 := by
    apply fixed_unique hf (hr1 π) (zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
    refine lt_of_le_of_lt (norm_sub_le_of_near hl ?_) hπ1'
    rw [sh_zero, sub_zero]
    have e : sh (r₀ π) = (sh (r₀ π) - oc K π) + oc K π := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr2 π) le_rfl)
  have hexp : ∃ i : ℕ, (μ = K.1.val → i = 0) ∧
      ∀ c, ∃ c' : ↥(OL K), sh (r₀ c ^ l ^ i) = omC (μ ((c + π * c' : ↥(OL K)) : ↥K.1)) := by
    by_cases hμ : μ = K.1.val
    · refine ⟨0, fun _ => rfl, fun c => ?_⟩
      obtain ⟨c', hc'⟩ := GlobalTheory.T.teichmuller_residue_congruence K π f hf hqf hl hπ1' hπ0 (r₀ c) c (hr1 c) (hr2 c)
      refine ⟨c', ?_⟩
      rw [pow_zero, pow_one, hc', hμ]
      rfl
    · obtain ⟨i, hi⟩ := exp_twist K π f hf hqf hl hπ1' hπ0 hmax hfin r₀ hr1 hr2 hrπ μ
      exact ⟨i, fun h => absurd h hμ, hi⟩
  obtain ⟨i, hi0, hic⟩ := hexp
  refine ⟨(iterateFrobenius (Tl l) l i).comp r₀, fun n => u n ^ l ^ i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    show (u (n + 1) ^ l ^ i) ^ qOf π = u n ^ l ^ i
    rw [hqf, ← pow_mul, mul_comm, pow_mul, hu1]
  · exact pow_ne_zero _ (hu0 0)
  · show ‖thB l (tch l (u 0 ^ l ^ i))‖ < 1
    rw [thB_tch, sh_pow, norm_pow]
    have h := hu2 0
    rw [hz0, map_zero, sub_zero] at h
    exact pow_lt_one₀ (norm_nonneg _) (h.trans_lt hπ1') (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  · exact tch_clause K π f hf μ r₀ hr1 i hic
  · intro g hg φ h0 h1 hcomm n D
    have hs := hgal ⟨g, hg⟩ φ h0 h1 hcomm
    have hd := GlobalTheory.T.lubin_tate_teichmuller_sequence_compatibility K π z f hf hl hπ1' hzlt hzgt u hu1 hu2 r₀ hr1 hr2 hu0 g
      (fun k => PowerSeries.coeff k φ) hs n D
    exact gal_clause g r₀ i (u n) (fun k => PowerSeries.coeff k φ) D hd
  · intro hμ n
    show ‖thB l (tch l (u n ^ l ^ i)) - _‖ ≤ _
    rw [hi0 hμ, pow_zero, pow_one, thB_tch, ← omC_apply, ← oc_apply]
    exact hu2 n
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def starLoc (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : R → ℂ) (dx : Measure (Fin n → Fin M → R ⊗[F] E))
    (Φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (b : HermR R σ n) : ℂ :=
  ∫ X, Φ X * ψR (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J X))) ∂dx

def psiFin (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Ainf F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Af F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExists
section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

section Sel

variable {K : Type} [Field K]

def selE (K : Type) [Field K] (r n : ℕ) : Matrix (Fin r) (Fin n) K :=
  fun i j => if (j : ℕ) = i then 1 else 0

theorem selE_mul_transpose {r n : ℕ} (hr : r ≤ n) :
    selE K r n * (selE K r n)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selE, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]
  · by_cases hik : i = k
    · subst hik; simp
    · have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
      simp [hik, hne]
  · intro j _ hj
    have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem transpose_selE_mul {r n : ℕ} (hr : r ≤ n) :
    (selE K r n)ᵀ * selE K r n = eId K n r := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selE, eId, Matrix.diagonal_apply]
  by_cases hj : (j : ℕ) < r
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases hjk : j = k
      · subst hjk; simp [hj]
      · have hne : (k : ℕ) ≠ j := fun h => hjk (Fin.ext h.symm)
        simp [hjk, hne]
    · intro i _ hi
      have hne : (j : ℕ) ≠ i := fun h => hi (Fin.ext h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · simp [hj]
    · intro i _
      have hne : (j : ℕ) ≠ i := fun h => hj (h ▸ i.2)
      simp [hne]

theorem cT_selE (σ : K →+* K) {r n : ℕ} : cT σ (selE K r n) = (selE K r n)ᵀ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, selE]
  split_ifs <;> simp

theorem extB_eq_selE {r n : ℕ} (hr : r ≤ n) (b : Matrix (Fin r) (Fin r) K) :
    extB (n := n) b = (selE K r n)ᵀ * b * selE K r n := by
  ext i j
  simp only [extB, Matrix.mul_apply, Matrix.transpose_apply, selE]
  by_cases hi : (i : ℕ) < r
  · by_cases hj : (j : ℕ) < r
    · rw [dif_pos ⟨hi, hj⟩]
      have e1 : ∀ l : Fin r, (∑ k : Fin r, (if (i : ℕ) = k then (1 : K) else 0) * b k l) = b ⟨i, hi⟩ l := by
        intro l
        rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp
        · intro k _ hk
          have hne : (i : ℕ) ≠ k := fun h => hk (Fin.ext h.symm)
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [e1]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro l _ hl
        have hne : (j : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg (fun h => hj h.2)]
      symm
      apply Finset.sum_eq_zero
      intro l _
      have hne : (j : ℕ) ≠ l := fun h => hj (h ▸ l.2)
      simp [hne]
  · rw [dif_neg (fun h => hi h.1)]
    symm
    apply Finset.sum_eq_zero
    intro l _
    rw [Finset.sum_eq_zero, zero_mul]
    intro k _
    have hne : (i : ℕ) ≠ k := fun h => hi (h ▸ k.2)
    simp [hne]

theorem selE_mul_of_isCompl {r n : ℕ} (hr : r ≤ n) {c : Matrix (Fin r) (Fin n) K}
    {a : Matrix (Fin n) (Fin n) K} (h : IsCompl c a) : selE K r n * a = c := by
  ext i j
  simp only [Matrix.mul_apply, selE]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]
  · have key := congrFun (h.2 ⟨i, lt_of_lt_of_le i.2 hr⟩ i.2) j
    simpa using key
  · intro k _ hk
    have hne : (k : ℕ) ≠ i := fun h' => hk (Fin.ext h')
    simp [hne]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end Sel

theorem exists_hermitian_lowerLeft :
    ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n →
      ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K)
        (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
        IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C →
        ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧
          C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  intro K _ σ hσ n r hr c a C D T L hc hC hLT hH
  have hca : c = selE K r n * a := (selE_mul_of_isCompl hr hc).symm
  have ha : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hc.1
  have hcTc : cT σ c = cT σ a * (selE K r n)ᵀ := by rw [hca, cT_mul, cT_selE]
  have hcTT : cT σ T * cT σ L = 1 := by rw [← cT_mul, hLT, cT_one]
  have h1 : T * c * cT σ D = D * cT σ a * (selE K r n)ᵀ * cT σ T := by
    rw [← hC, hH, hC, cT_mul, hcTc]
    simp only [Matrix.mul_assoc]
  have hM : D * cT σ a * (selE K r n)ᵀ = T * (c * cT σ D * cT σ L) := by
    calc D * cT σ a * (selE K r n)ᵀ = D * cT σ a * (selE K r n)ᵀ * (cT σ T * cT σ L) := by
          rw [hcTT, Matrix.mul_one]
      _ = T * c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, ← h1]
      _ = T * (c * cT σ D * cT σ L) := by simp only [Matrix.mul_assoc]
  refine ⟨c * cT σ D * cT σ L, ?_, ?_⟩
  · rw [cT_mul, cT_mul, cT_cT σ hσ, cT_cT σ hσ, hcTc]
    calc L * (D * (cT σ a * (selE K r n)ᵀ)) = L * (T * (c * cT σ D * cT σ L)) := by
          rw [← hM]; simp only [Matrix.mul_assoc]
      _ = c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, hLT, Matrix.one_mul]
  · have hSP : selE K r n * eId K n r = selE K r n := by
      rw [← transpose_selE_mul hr, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]
    have hSB : selE K r n * extB (n := n) (c * cT σ D * cT σ L) = (c * cT σ D * cT σ L) * selE K r n := by
      rw [extB_eq_selE hr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]
    have hCa : C * a⁻¹ = T * selE K r n := by
      rw [hC, hca, Matrix.mul_assoc T, Matrix.mul_assoc, ha, Matrix.mul_one]
    rw [hCa, Matrix.mul_assoc T (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_one, hSP, hSB,
      sub_self, zero_sub, Matrix.mul_neg, ← transpose_selE_mul hr, ← Matrix.mul_assoc (D * cT σ a), hM]
    simp only [Matrix.mul_assoc, neg_add_cancel]

end GlobalTheory.CompanionTheory.BruhatCell
end

