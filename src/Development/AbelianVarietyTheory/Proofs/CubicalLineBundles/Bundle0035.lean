import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegDualLineCmIdeal
section
noncomputable section

open NumberField Module ReciprocityTheory.GeometryOfNumbersTheory
open scoped nonZeroDivisors

namespace GlobalTheory.CM

open NumberField Module in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.CM.deg_ideal_smul {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V) (Λ : Submodule (𝓞 K) V) {v : V} (hv : v ≠ 0)
    {m : (K →+* ℂ) → ℝ} (hm : ∀ s, 0 < m s) (hf : ∀ s, (h.form s v v).re = m s)
    {𝔠 : FractionalIdeal (𝓞 K)⁰ K} (h𝔠 : 𝔠 ≠ 0) (hΛ : ∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ t ∈ 𝔠) :
    _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = -Real.log (FractionalIdeal.absNorm 𝔠) / finrank ℚ K - _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K m / 2 := by
  set φ : K →ₗ[𝓞 K] V := (LinearMap.toSpanSingleton K V v).restrictScalars (𝓞 K) with hφ
  have hφapp : ∀ t, φ t = t • v := fun t => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    simp only [hφapp] at hab
    exact smul_left_injective K hv hab
  have hΛmap : Λ = (𝔠 : Submodule (𝓞 K) K).map φ := by
    ext z
    rw [hΛ, Submodule.mem_map]
    constructor
    · rintro ⟨t, rfl, ht⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, rfl, ht⟩
  have hform : ∀ s, h.form s v v = (m s : ℂ) := by
    intro s
    have hc := h.conj_symm s v v
    apply Complex.ext
    · simp [hf s]
    · simp only [Complex.ofReal_im]
      exact Complex.conj_eq_iff_im.mp hc
  have hcFG : (𝔠 : Submodule (𝓞 K) K).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔠
  obtain ⟨r, w, hw⟩ := _root_.ReciprocityTheory.GeometryOfNumbersTheory.exists_isFullRankFamily_of_fg (𝔠 : Submodule (𝓞 K) K) hcFG
  have hw' := hw
  unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame at hw'
  obtain ⟨hwmem, hwli, hwspan⟩ := hw'
  have hrange : Set.range (fun i => φ (w i)) = φ '' Set.range w := Set.range_comp φ w
  have hframe : _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K Λ (fun i => φ (w i)) := by
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.IsFrame
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [hΛmap]; exact Submodule.mem_map_of_mem (hwmem i)
    · exact hwli.map' (LinearMap.toSpanSingleton K V v) (LinearMap.ker_toSpanSingleton K hv)
    · intro z hz
      rw [SetLike.mem_coe, hΛ] at hz
      obtain ⟨t, rfl, ht⟩ := hz
      have ht' : t ∈ Submodule.span K (Set.range w) := hwspan ht
      have hmem := Submodule.mem_map_of_mem (f := LinearMap.toSpanSingleton K V v) ht'
      rw [Submodule.map_span, ← Set.range_comp] at hmem
      exact hmem
  have hΛFG : Λ.FG := hΛmap ▸ hcFG.map φ
  have hrel : (Submodule.span (𝓞 K) (Set.range (fun i => φ (w i)))).toAddSubgroup.relIndex
      Λ.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range w)).toAddSubgroup.relIndex
      (𝔠 : Submodule (𝓞 K) K).toAddSubgroup := by
    rw [hΛmap, hrange, ← Submodule.map_span, Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hgram : ∀ σ, h.gram σ (fun i => φ (w i)) = (_root_.GlobalTheory.lineHerm m hm).gram σ w := by
    intro σ
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram
    ext i j
    simp only [Matrix.of_apply, hφapp, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_smul_left, _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam.smul_right, hform]
    unfold _root_.GlobalTheory.lineHerm
    simp only
    ring
  calc _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily h Λ (fun i => φ (w i)) := _root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily h hΛFG hframe
    _ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily (_root_.GlobalTheory.lineHerm m hm) (𝔠 : Submodule (𝓞 K) K) w := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.degreeOfFamily
      rw [hrel]
      simp_rw [hgram]
    _ = _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg (_root_.GlobalTheory.lineHerm m hm) (𝔠 : Submodule (𝓞 K) K) :=
      (_root_.ReciprocityTheory.GeometryOfNumbersTheory.arakelovDegree_eq_degreeOfFamily _ hcFG hw).symm
    _ = _ := _root_.GlobalTheory.deg_lineHerm m hm h𝔠

open NumberField Module in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.CM.two_mul_deg_dual_line : ∀ (E K V : Type) [Field E] [NumberField E] [IsCMField E]
    [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : _root_.ReciprocityTheory.GeometryOfNumbersTheory.HermFam K V)
    (Λ : Submodule (𝓞 K) V) (v : V) (τ : E →+* K) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (β : E) (n : (K →+* ℂ) → ℝ), 𝔞 ≠ 0 → v ≠ 0 → (∀ s, 0 < n s) →
    (∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0) →
    (∀ s, (h.form s v v).re = (s (τ β)).re * n s) →
    (∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ ∀ b ∈ 𝔞, IsIntegral ℤ (t * τ (β * IsCMField.complexConj E b))) →
    2 * _root_.ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ = (2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) +
      Real.log |(Algebra.norm ℚ β : ℚ)|) / Module.finrank ℚ E - _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
  intro E K V _ _ _ _ _ _ _ _ _ h Λ v τ 𝔞 β n h𝔞 hv hn hβ hf hΛ
  have hβ0 : β ≠ 0 := by
    rintro rfl
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    simpa using (hβ s).1
  set 𝔞' : FractionalIdeal (𝓞 E)⁰ E :=
    FractionalIdeal.spanSingleton (𝓞 E)⁰ β * _root_.GlobalTheory.conjFrac 𝔞 with h𝔞'def
  have h𝔞' : 𝔞' ≠ 0 :=
    mul_ne_zero (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
      (_root_.GlobalTheory.conjFrac_ne_zero h𝔞)
  obtain ⟨𝔟, h𝔟, h𝔟span, h𝔟log⟩ := _root_.GlobalTheory.exists_fractionalIdeal_eq_span_image τ h𝔞'
  have hm : ∀ s : K →+* ℂ, 0 < (s (τ β)).re * n s := fun s => mul_pos (hβ (s.comp τ)).1 (hn s)
  have hmemΛ : ∀ z, z ∈ Λ ↔ ∃ t : K, z = t • v ∧ t ∈ 𝔟⁻¹ := by
    intro z
    rw [hΛ]
    refine exists_congr fun t => and_congr_right fun _ => ?_
    rw [FractionalIdeal.mem_inv_iff h𝔟]
    constructor
    · intro H y hy
      rw [← FractionalIdeal.mem_coe, h𝔟span] at hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, hx, rfl⟩ := hx
        rw [SetLike.mem_coe, h𝔞'def, FractionalIdeal.mem_singleton_mul] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [_root_.GlobalTheory.mem_conjFrac] at hz
        have key := H _ hz
        rw [show _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = IsCMField.complexConj E z from rfl,
          IsCMField.complexConj_apply_apply] at key
        exact (_root_.GlobalTheory.mem_one_fractionalIdeal_iff).2 key
      | zero => simp
      | add x y _ _ hx hy =>
        rw [mul_add, ← FractionalIdeal.mem_coe]
        rw [← FractionalIdeal.mem_coe] at hx hy
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [mul_smul_comm, ← FractionalIdeal.mem_coe]
        exact Submodule.smul_mem _ a hx
    · intro H b hb
      rw [← _root_.GlobalTheory.mem_one_fractionalIdeal_iff]
      apply H
      rw [← FractionalIdeal.mem_coe, h𝔟span]
      apply Submodule.subset_span
      refine ⟨β * IsCMField.complexConj E b, ?_, rfl⟩
      rw [SetLike.mem_coe, h𝔞'def, FractionalIdeal.mem_singleton_mul]
      exact ⟨IsCMField.complexConj E b, _root_.GlobalTheory.cc_mem_conjFrac.2 hb, rfl⟩
  have hdeg := _root_.GlobalTheory.CM.deg_ideal_smul h Λ hv hm hf (inv_ne_zero h𝔟) hmemΛ
  have hsumE : ∑ s : E →+* ℂ, Real.log (s β).re = Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| := by
    rw [← Real.log_prod (fun s _ => ne_of_gt (hβ s).1)]
    congr 1
    have hprodC : ((∏ s : E →+* ℂ, (s β).re : ℝ) : ℂ) = (((Algebra.norm ℚ β : ℚ) : ℝ) : ℂ) := by
      push_cast
      have hre : ∀ s : E →+* ℂ, ((s β).re : ℂ) = s β := fun s =>
        Complex.ext (by simp) (by simp [(hβ s).2])
      simp_rw [hre]
      rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun s => s β) (fun σ => σ β)
        (fun s => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ β]
      simp
    have hprod : (∏ s : E →+* ℂ, (s β).re : ℝ) = ((Algebra.norm ℚ β : ℚ) : ℝ) := by
      exact_mod_cast hprodC
    rw [hprod, abs_of_pos]
    rw [← hprod]
    exact Finset.prod_pos fun s _ => (hβ s).1
  have hM : _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => (s (τ β)).re * n s) =
      Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| / finrank ℚ E + _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
    have hsplit : _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => (s (τ β)).re * n s) =
        _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K (fun s => ((s.comp τ) β).re) + _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog K n := by
      unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      exact Real.log_mul (ne_of_gt (hβ (s.comp τ)).1) (ne_of_gt (hn s))
    have hres := _root_.GlobalTheory.meanLog_comp τ (fun s : E →+* ℂ => (s β).re)
    rw [hsplit, hres, ← hsumE]
    unfold _root_.ReciprocityTheory.GeometryOfNumbersTheory.meanLog
    rfl
  have hlog𝔞' : Real.log (FractionalIdeal.absNorm 𝔞' : ℝ) =
      Real.log |((Algebra.norm ℚ β : ℚ) : ℝ)| + Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) := by
    rw [h𝔞'def, map_mul, FractionalIdeal.absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs,
      Real.log_mul, _root_.GlobalTheory.log_absNorm_conjFrac h𝔞]
    · exact abs_ne_zero.mpr (Rat.cast_ne_zero.mpr ((Algebra.norm_ne_zero_iff).mpr hβ0))
    · exact Rat.cast_ne_zero.mpr (fun h0 => _root_.GlobalTheory.conjFrac_ne_zero h𝔞
        (FractionalIdeal.absNorm_eq_zero_iff.mp h0))
  have hinv : -Real.log (FractionalIdeal.absNorm 𝔟⁻¹ : ℝ) / finrank ℚ K =
      Real.log (FractionalIdeal.absNorm 𝔟 : ℝ) / finrank ℚ K := by
    rw [map_inv₀, Rat.cast_inv, Real.log_inv, neg_neg]
  rw [hdeg, hinv, h𝔟log, hlog𝔞', hM]
  ring

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
section
open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

variable {K : Type} [Field K] [NumberField K]

theorem isLocGen_iff_valuation_eq (p : HeightOneSpectrum (𝓞 K)) (c : K) (I : FractionalIdeal (𝓞 K)⁰ K) :
    IsLocGen p c I ↔ p.valuation K c = exp (-FractionalIdeal.count K p I) := by
  constructor
  · rintro ⟨h0, h⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, h]
  · intro h
    have h0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact exp_ne_zero h.symm
    refine ⟨h0, ?_⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, exp_inj] at h
    exact neg_injective h

theorem valuation_le_iff_exists_smul_mem (p : HeightOneSpectrum (𝓞 K)) {I : FractionalIdeal (𝓞 K)⁰ K}
    (hI : I ≠ 0) (c : K) :
    p.valuation K c ≤ exp (-FractionalIdeal.count K p I) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I := by
  constructor
  · intro h
    obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    have hvy : p.valuation K y ≠ 0 := by rw [hv]; exact exp_ne_zero
    have hy0 : y ≠ 0 := by rintro rfl; simp at hvy
    have h1 : p.valuation K (c / y) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hvy), hv]; exact h
    obtain ⟨a, s, hs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p (c / y) h1
    refine ⟨s.1, s.2, ?_⟩
    have : (s.1 : 𝓞 K) • c = a • y := by
      rw [Algebra.smul_def, Algebra.smul_def, ← hs]
      field_simp
    rw [this]
    exact Submodule.smul_mem (I : Submodule (𝓞 K) K) a hy
  · rintro ⟨s, hs, hc⟩
    have h := (GlobalTheory.Idele.mem_iff_valuation_le hI _).1 hc p
    have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
      exact (p.valuation_lt_one_iff_mem s).1 hlt
    rwa [Algebra.smul_def, map_mul, h1, one_mul] at h

theorem mem_iff_forall_exists_smul_mem {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (Λ : Submodule (𝓞 K) V) (z : V) :
    z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  constructor
  · intro hz p
    exact ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hz⟩
  · intro h
    let A : Ideal (𝓞 K) := Λ.comap (LinearMap.toSpanSingleton (𝓞 K) V z)
    have hA : A = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hAm⟩ := Ideal.exists_le_maximal A hne
      have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
      obtain ⟨s, hs, hsz⟩ := h ⟨m, hm.isPrime, hm0⟩
      exact hs (hAm (by simpa [A] using hsz))
    have : (1 : 𝓞 K) ∈ A := hA ▸ Submodule.mem_top
    simpa [A] using this

theorem local_global_ideal_lattice : ∀ (K : Type) [Field K] [NumberField K],
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (cl : HeightOneSpectrum (𝓞 K) → K), I ≠ 0 →
      (∀ p, IsLocGen p (cl p) I) → ∀ c : K,
        c ∈ I ↔ ∀ p : HeightOneSpectrum (𝓞 K), p.valuation K c ≤ p.valuation K (cl p)) ∧
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (p : HeightOneSpectrum (𝓞 K)), I ≠ 0 →
      (∃ cl ∈ I, IsLocGen p cl I) ∧ ∀ cl, IsLocGen p cl I ↔ cl ≠ 0 ∧ ∀ c : K,
        p.valuation K c ≤ p.valuation K cl ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I) ∧
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 K) V] (Λ : Submodule (𝓞 K) V) (z : V),
      z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  intro K _ _
  refine ⟨fun I cl hI hcl c => ?_, fun I p hI => ⟨?_, fun cl => ?_⟩,
    fun V _ _ Λ z => mem_iff_forall_exists_smul_mem Λ z⟩
  · rw [GlobalTheory.Idele.mem_iff_valuation_le hI]
    refine forall_congr' fun p => ?_
    rw [(isLocGen_iff_valuation_eq p _ I).1 (hcl p)]
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    exact ⟨y, hy, (isLocGen_iff_valuation_eq p y I).2 hv⟩
  · constructor
    · intro h
      refine ⟨h.1, fun c => ?_⟩
      rw [(isLocGen_iff_valuation_eq p _ I).1 h]
      exact valuation_le_iff_exists_smul_mem p hI c
    · rintro ⟨-, h⟩
      obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
      refine (isLocGen_iff_valuation_eq p cl I).2 (le_antisymm ?_ ?_)
      · exact (valuation_le_iff_exists_smul_mem p hI cl).2 ((h cl).1 le_rfl)
      · rw [← hv]
        exact (h y).2 ((valuation_le_iff_exists_smul_mem p hI y).1 hv.le)

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilIsOfLbIsoCubeLB
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PairingOfLam

open ReciprocityTheory.ChartRestriction.G.Out DescentPairing AdjointOfPairing

theorem val_ratio {X X' Y Y₀ B : Scheme.{0}} {L : LB X} {N : LB X'} (hL : L.IsLB) (hN : N.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y₀ ⟶ X')} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb N φ' ε') (LB.LinComb L φ ε)) (h : Y ⟶ Y₀)
    (t : LB.Gen (LB.LinComb L (fun k => h ≫ φ k) ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb N (fun k => h ≫ φ' k) ε')) (ht' : t'.IsGen) (p : Y ⟶ B)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (e₁ : r ≫ h = r' ≫ h)
    (e₂ : r ≫ p = r' ≫ p) (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good N z J') :
    val t r z J * (val t' r z J')⁻¹ = val t r' z J * (val t' r' z J')⁻¹ := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ (i : K → L.ι) (i' : K' → N.ι),
      LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart N (fun k => h ≫ φ' k) i' ≤
        h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart N φ' i') := fun i i' y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i i',
      r z ∈ LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart N (fun k => h ≫ φ' k) i' →
      gm r z _ (res inf_le_left (t.s i) * (res (le i i') (pullU h _ (w.s (i, i'))) * res inf_le_right (t'.s i'))⁻¹) =
        gm r z (LB.wchart L (fun k => h ≫ φ k) i) (t.s i) *
          (gm (r ≫ h) z (LB.wchart L φ i ⊓ LB.wchart N φ' i') (w.s (i, i')) *
            gm r z (LB.wchart N (fun k => h ≫ φ' k) i') (t'.s i'))⁻¹ :=
    fun Z r z i i' hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ hz _).trans (gm_pull r h z _ (le i i' hz) _)) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y.Opens)
    (fun i : (K → L.ι) × (K' → N.ι) =>
      LB.wchart L (fun k => h ≫ φ k) i.1 ⊓ LB.wchart N (fun k => h ≫ φ' k) i.2) (fun _ => le_top)
    (fun y _ => by
      choose i hi using fun k => exists_chart hL (φ k (h y))
      choose i' hi' using fun k => exists_chart hN (φ' k (h y))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), Set.mem_iInter.2 hi, Set.mem_iInter.2 hi'⟩)
    (fun i => res inf_le_left (t.s i.1) *
      (res (le i.1 i.2) (pullU h _ (w.s (i.1, i.2))) * res inf_le_right (t'.s i.2))⁻¹)
    (fun i j y hy => by
      have hm : (𝟙 Y ≫ h) y ∈ LB.wchart L φ i.1 ⊓ LB.wchart N φ' i.2 ⊓ (LB.wchart L φ j.1 ⊓ LB.wchart N φ' j.2) :=
        ⟨le _ _ hy.1, le _ _ hy.2⟩
      have e : gm (𝟙 Y ≫ h) y (LB.wchart L φ i.1 ⊓ LB.wchart N φ' i.2) (w.s (i.1, i.2)) =
          trF φ ε (𝟙 Y ≫ h) y i.1 j.1 * (trF φ' ε' (𝟙 Y ≫ h) y i.2 j.2)⁻¹ *
            gm (𝟙 Y ≫ h) y (LB.wchart L φ j.1 ⊓ LB.wchart N φ' j.2) (w.s (j.1, j.2)) :=
        (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y ≫ h) y _) (hw (i.1, i.2) (j.1, j.2))).trans
          ((map_mul _ _ _).trans (congrArg₂ (· * ·)
            ((gm_div (LB.LinComb N φ' ε') (LB.LinComb L φ ε) _ y (i.1, i.2) (j.1, j.2) hm).trans
              (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ ε _ y _ _ hm.1.1 hm.2.1)
                (gm_linComb N φ' ε' _ y _ _ hm.1.2 hm.2.2))) (gm_res _ y _ hm _))))
      have f₁ : trF φ ε (𝟙 Y ≫ h) y i.1 j.1 = trF (fun k => h ≫ φ k) ε (𝟙 Y) y i.1 j.1 := by
        simp only [trF, Category.assoc]
      have f₂ : trF φ' ε' (𝟙 Y ≫ h) y i.2 j.2 = trF (fun k => h ≫ φ' k) ε' (𝟙 Y) y i.2 j.2 := by
        simp only [trF, Category.assoc]
      refine (hv _ _ y _ _ hy.1).trans (Eq.trans ?_ (hv _ _ y _ _ hy.2).symm)
      rw [e, f₁, f₂,
        gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, gen_trans ht' (𝟙 Y) y hy.1.2 hy.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  obtain ⟨a, ha⟩ := hp c.val
  have hcv : ∀ r : Z ⟶ Y, (gm r z ⊤ c).val = gs (r ≫ p) z ⊤ a := fun r =>
    (gs_unit r z ⊤ trivial _).symm.trans ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a))
  have key : ∀ r : Z ⟶ Y, gm r z ⊤ c = val t r z J *
      (gm (r ≫ h) z (LB.wchart L φ (fun k => J ((r ≫ h) ≫ φ k)) ⊓ LB.wchart N φ' (fun k => J' ((r ≫ h) ≫ φ' k)))
        (w.s (fun k => J ((r ≫ h) ≫ φ k), fun k => J' ((r ≫ h) ≫ φ' k))) * val t' r z J')⁻¹ := fun r => by
    have hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) (fun k => J ((r ≫ h) ≫ φ k)) ⊓
        LB.wchart N (fun k => h ≫ φ' k) (fun k => J' ((r ≫ h) ≫ φ' k)) :=
      ⟨Set.mem_iInter.2 fun k => hJ ((r ≫ h) ≫ φ k), Set.mem_iInter.2 fun k => hJ' ((r ≫ h) ≫ φ' k)⟩
    rw [val_of t r z J (fun k => J ((r ≫ h) ≫ φ k)) (fun k => by rw [Category.assoc]),
      val_of t' r z J' (fun k => J' ((r ≫ h) ≫ φ' k)) (fun k => by rw [Category.assoc])]
    exact (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (_, _))).trans (hv Z r z _ _ hz))
  have q : gm r z ⊤ c = gm r' z ⊤ c := Units.ext (by rw [hcv, hcv, e₂])
  rw [key, key, e₁] at q
  apply Additive.ofMul.injective
  have q' := congrArg Additive.ofMul q
  simp only [ofMul_mul, ofMul_inv] at q' ⊢
  linear_combination (norm := abel) q'

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

theorem exists_gen_lam (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N : RigLB A} (cb : CubicalStr A N)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a g : B ⟶ A) [IsMonHom g] (n : ℕ) (y : T ⟶ B)
    (hy : (y ≫ a) ^ n = 1) :
    ∃ t : LB.Gen (LB.LinComb N.L (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T B ≫ y) (snd T B ^ n)).left ≫
        (psum A ![fst B B ≫ a, snd B B ≫ g] I.down).left) (fun I => (-1) ^ (2 - I.down.card))),
      t.IsGen ∧ ∀ (z : T ⟶ B) (e : Γ(T.left, ⊤)ˣ), z ^ n = 1 → WeilIs A N.L n (y ≫ a) (z ≫ g) e →
        ∀ (p : T.left) (J), Good N.L p J →
          val t (lift (𝟙 T) z).left p J = val t (lift (𝟙 T) (1 : T ⟶ B)).left p J * gm (𝟙 T.left) p ⊤ e := by
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_pairing hG hA cb p₀ hT n (y ≫ a) hy
  obtain ⟨σ, hσ⟩ := exists_frame N.isLB (K := Fin 2) ![(y ≫ a).left, (1 : T ⟶ A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen N.isLB
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T B ≫ y) (snd T B ^ n)).left ≫
        (psum A ![fst B B ≫ a, snd B B ≫ g] I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => by
      have e : ∀ I, (lift (fst T B ≫ y) (snd T B ^ n)).left ≫ (psum A ![fst B B ≫ a, snd B B ≫ g] I).left =
          (psum A ![fst T B ≫ y ≫ a, (snd T B ≫ g) ^ n] I).left := fun I => by
        refine congrArg CommaMorphism.left ((psum_hom (preHom (lift (fst T B ≫ y) (snd T B ^ n))) _ I).trans ?_)
        congr 1
        funext i
        fin_cases i
        · show lift _ _ ≫ fst B B ≫ a = fst T B ≫ y ≫ a
          rw [lift_fst_assoc, Category.assoc]
        · show lift _ _ ≫ snd B B ≫ g = (snd T B ≫ g) ^ n
          rw [lift_snd_assoc, MonObj.pow_comp]
      have f : ∏ i : Fin 2, h ((fst T B).left ≫ ![(y ≫ a).left, (1 : T ⟶ A).left] i) ^ ![(-1 : ℤ), 1] i =
          (h (fst T B ≫ y ≫ a).left)⁻¹ * h (fst T B ≫ (1 : T ⟶ A)).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_mulT n (y ≫ a) (fst T B) (snd T B ≫ g) h) f).trans ?_
      simp only [e]
      rw [NormRos.prod_square, MonObj.comp_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen N.L _ _ _ _ (LB.pullGen N.L _ _ u₀ (lift (fst T B) (snd T B ≫ g)).left)
      (LB.pullGen N.L _ _ σ (fst T B).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun z e hz he p J hJ => ?_⟩
  have w : ∀ b : T ⟶ B, val u (lift (𝟙 T) b).left p J =
      val u₀ (lift (𝟙 T) (b ≫ g)).left p J * val σ (𝟙 T :).left p J := fun b => by
    rw [v _ _ p J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd_assoc]
  have w₀ := v₀ (z ≫ g) e (by rw [← MonObj.pow_comp, hz, MonObj.one_comp]) he T (𝟙 T) 1 p J hJ
  rw [Category.id_comp, _root_.mul_one] at w₀
  rw [w, w, w₀, MonObj.one_comp, mul_right_comm]
  rfl

end GlobalTheory.PairingOfLam

namespace GlobalTheory

end GlobalTheory
end
end

