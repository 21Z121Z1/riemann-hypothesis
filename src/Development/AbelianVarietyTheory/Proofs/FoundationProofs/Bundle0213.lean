import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalHermitianOfDiagPosIsSquare
section
open NumberField
open scoped Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.SqDet

section
variable {K : Type} [Field K] [NumberField K] {d : ℕ} {θ : K}

end

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem exists_rat_sum_norm_forms_eq_one {a b d : ℚ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ∃ p₁ q₁ p₂ q₂ : ℚ, a * (p₁ ^ 2 + d * q₁ ^ 2) + b * (p₂ ^ 2 + d * q₂ ^ 2) = 1 := by
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt ℚ
    (![a, a * d, b, b * d, -1] : Fin 5 → ℚ) (by simp)
    (by
      intro i
      fin_cases i <;> simp [ha.ne', hb.ne', hd.ne'])
    (by
      intro τ
      refine ⟨4, 0, ?_, ?_⟩
      · simp
      · simp only [Matrix.cons_val_zero, eq_ratCast]
        exact_mod_cast ha)
  have hx' : a * x 0 ^ 2 + a * d * x 1 ^ 2 + b * x 2 ^ 2 + b * d * x 3 ^ 2 = x 4 ^ 2 := by
    simp [Fin.sum_univ_five] at hx
    linarith
  have t0 : 0 ≤ a * x 0 ^ 2 := by positivity
  have t1 : 0 ≤ a * d * x 1 ^ 2 := by positivity
  have t2 : 0 ≤ b * x 2 ^ 2 := by positivity
  have t3 : 0 ≤ b * d * x 3 ^ 2 := by positivity
  have h4 : x 4 ≠ 0 := by
    intro h4
    rw [h4] at hx'
    have e0 : a * x 0 ^ 2 = 0 := by linarith
    have e1 : a * d * x 1 ^ 2 = 0 := by linarith
    have e2 : b * x 2 ^ 2 = 0 := by linarith
    have e3 : b * d * x 3 ^ 2 = 0 := by linarith
    apply hx0
    funext i
    fin_cases i
    · simpa [ha.ne'] using e0
    · simpa [ha.ne', hd.ne'] using e1
    · simpa [hb.ne'] using e2
    · simpa [hb.ne', hd.ne'] using e3
    · exact h4
  refine ⟨x 0 / x 4, x 1 / x 4, x 2 / x 4, x 3 / x 4, ?_⟩
  field_simp
  linarith

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem sesq_apply_eq_zero_and_of_mem_span_of_forall_mem {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {σ : K →+* K} (h : V →ₗ[K] V →ₛₗ[σ] K) {s : Set V} {w : V}
    (hs : ∀ u ∈ s, h u w = 0 ∧ h w u = 0) {u : V} (hu : u ∈ Submodule.span K s) :
    h u w = 0 ∧ h w u = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx.1, hy.1, hx.2, hy.2]
  | smul c x _ hx => simp [hx.1, hx.2]

open NumberField in
open scoped Matrix ComplexConjugate in
private theorem exists_orthonormal_mem_span_of_diagonal_square_prod {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) {d : ℕ} {θ : K}
    (hd : 0 < d) (hθ2 : θ ^ 2 = -(d : K)) (hθ : σ θ = -θ) :
    ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) →
      (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) →
      ∃ e : Fin r → V, (∀ i j, h (e i) (e j) = if i = j then 1 else 0) ∧
        ∀ i, e i ∈ Submodule.span K (Set.range v) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro v a ha hv hsq
  rcases r with _ | _ | r
  · exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  · obtain ⟨s, hs⟩ := hsq
    rw [Fin.prod_univ_one] at hs
    have hs0 : (s : K) ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        have := ha 0
        rw [hs] at this
        simp at this
      exact_mod_cast this
    refine ⟨fun _ => ((s⁻¹ : ℚ) : K) • v 0, ?_, fun _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨0, rfl⟩)⟩
    intro i j
    have hij : i = j := Fin.ext (by have := i.2; have := j.2; omega)
    subst hij
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hv, if_true, map_ratCast,
      hs]
    push_cast
    field_simp
  · have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    obtain ⟨p₁, q₁, p₂, q₂, hq⟩ := exists_rat_sum_norm_forms_eq_one (ha 0) (ha 1) hdq
    have hqK : (a 0 : K) * ((p₁ : K) ^ 2 + (d : K) * (q₁ : K) ^ 2) +
        (a 1 : K) * ((p₂ : K) ^ 2 + (d : K) * (q₂ : K) ^ 2) = 1 := by
      exact_mod_cast hq
    have h01 : (0 : Fin (r + 2)) ≠ 1 := by simp
    have hss : ∀ i : Fin r, (i.succ.succ : Fin (r + 2)) ≠ 0 ∧ (i.succ.succ : Fin (r + 2)) ≠ 1 := by
      intro i
      refine ⟨Fin.succ_ne_zero _, ?_⟩
      rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]
      exact Fin.succ_ne_zero _
    have hv00 := hv 0 0
    have hv11 := hv 1 1
    have hv01 := hv 0 1
    have hv10 := hv 1 0
    simp only [if_true, h01, h01.symm, if_false] at hv00 hv11 hv01 hv10
    have hvs : ∀ (i : Fin r) (j : Fin (r + 2)), j = 0 ∨ j = 1 →
        h (v i.succ.succ) (v j) = 0 ∧ h (v j) (v i.succ.succ) = 0 := by
      intro i j hj
      rw [hv, hv]
      rcases hj with rfl | rfl
      · simp [(hss i).1, (hss i).1.symm]
      · simp [(hss i).2, (hss i).2.symm]
    set w : V := ((p₁ : K) + (q₁ : K) * θ) • v 0 + ((p₂ : K) + (q₂ : K) * θ) • v 1 with hw
    set w' : V := ((a 1 : K) * ((p₂ : K) - (q₂ : K) * θ)) • v 0 -
      ((a 0 : K) * ((p₁ : K) - (q₁ : K) * θ)) • v 1 with hw'
    have hww : h w w = 1 := by
      simp only [hw, map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, hv00, hv11, hv01, hv10, map_mul, map_ratCast, hθ]
      linear_combination hqK - ((a 0 : K) * (q₁ : K) ^ 2 + (a 1 : K) * (q₂ : K) ^ 2) * hθ2
    have hww' : h w w' = 0 := by
      simp only [hw, hw', map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv00, hv11, hv01, hv10, map_mul,
        map_ratCast, hθ]
      ring
    have hw'w : h w' w = 0 := by
      simp only [hw, hw', map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv00, hv11, hv01, hv10, map_mul,
        map_ratCast, hθ]
      ring
    have hw'w' : h w' w' = ((a 0 * a 1 : ℚ) : K) := by
      simp only [hw', map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hv00, hv11, hv01, hv10, map_mul, map_ratCast, hθ, map_neg]
      push_cast
      linear_combination (a 0 : K) * (a 1 : K) * hqK -
        (a 0 : K) * (a 1 : K) * ((a 0 : K) * (q₁ : K) ^ 2 + (a 1 : K) * (q₂ : K) ^ 2) * hθ2
    have hwv : ∀ i : Fin r, h (v i.succ.succ) w = 0 ∧ h w (v i.succ.succ) = 0 := by
      intro i
      obtain ⟨h1, h1'⟩ := hvs i 0 (Or.inl rfl)
      obtain ⟨h2, h2'⟩ := hvs i 1 (Or.inr rfl)
      constructor
      · simp [hw, h1, h2]
      · simp [hw, h1', h2']
    have hw'v : ∀ i : Fin r, h (v i.succ.succ) w' = 0 ∧ h w' (v i.succ.succ) = 0 := by
      intro i
      obtain ⟨h1, h1'⟩ := hvs i 0 (Or.inl rfl)
      obtain ⟨h2, h2'⟩ := hvs i 1 (Or.inr rfl)
      constructor
      · simp [hw', h1, h2]
      · simp [hw', h1', h2']
    have hwspan : w ∈ Submodule.span K (Set.range v) :=
      add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    have hw'span : w' ∈ Submodule.span K (Set.range v) :=
      sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    let v' : Fin (r + 1) → V := Fin.cons w' (fun i => v i.succ.succ)
    let a' : Fin (r + 1) → ℚ := Fin.cons (a 0 * a 1) (fun i => a i.succ.succ)
    have ha' : ∀ i, 0 < a' i := by
      intro i
      cases i using Fin.cases with
      | zero => exact mul_pos (ha 0) (ha 1)
      | succ i => exact ha _
    have hv' : ∀ i j, h (v' i) (v' j) = if i = j then (a' i : K) else 0 := by
      intro i j
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simpa [v', a'] using hw'w'
        | succ j => simpa [v', a', (Fin.succ_ne_zero j).symm] using (hw'v j).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa [v', a', Fin.succ_ne_zero i] using (hw'v i).1
        | succ j =>
          simp only [v', a', Fin.cons_succ, hv, Fin.succ_inj]
    have hsq' : IsSquare (∏ i, a' i) := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ] at hsq
      rw [Fin.prod_univ_succ]
      simp only [a', Fin.cons_zero, Fin.cons_succ]
      convert hsq using 1
      simp only [Fin.succ_zero_eq_one]
      ring
    obtain ⟨e', he', hspan'⟩ := ih (r + 1) (by omega) v' a' ha' hv' hsq'
    have hwe' : ∀ j, h (e' j) w = 0 ∧ h w (e' j) = 0 := by
      intro j
      refine sesq_apply_eq_zero_and_of_mem_span_of_forall_mem h ?_ (hspan' j)
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact ⟨by simpa [v'] using hw'w, by simpa [v'] using hww'⟩
      | succ i => simpa [v'] using hwv i
    have hle : Submodule.span K (Set.range v') ≤ Submodule.span K (Set.range v) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => simpa [v'] using hw'span
      | succ i => exact Submodule.subset_span ⟨i.succ.succ, rfl⟩
    refine ⟨Fin.cons w e', ?_, ?_⟩
    · intro i j
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simpa using hww
        | succ j => simpa [(Fin.succ_ne_zero j).symm] using (hwe' j).2
      | succ i =>
        cases j using Fin.cases with
        | zero => simpa [Fin.succ_ne_zero i] using (hwe' i).1
        | succ j => simpa [Fin.succ_inj] using he' i j
    · intro i
      cases i using Fin.cases with
      | zero => simpa using hwspan
      | succ i => simpa using hle (hspan' i)

open NumberField in
open scoped Matrix ComplexConjugate in

theorem _root_.GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare :
    ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (d : ℕ) (θ : K), 0 < d → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) → (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) → ∃ e : Fin r → V, ∀ i j, h (e i) (e j) = if i = j then 1 else 0 := by
  intro K V _ _ _ _ σ h d θ hd hθ2 hθ _ r v a ha hv hsq
  obtain ⟨e, he, -⟩ := exists_orthonormal_mem_span_of_diagonal_square_prod σ h hd hθ2 hθ r v a ha hv hsq
  exact ⟨e, he⟩

end GlobalTheory.SqDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
section
open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory

def provisionalShimX (Tau : Type) [Fintype Tau] (N j : ℕ) (lev : Finset ℕ) (hj : 1 ≤ j)
    (hjN : j < N) (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX Tau where
  N := N
  j := j
  j_pos := hj
  j_lt := hjN
  lev := lev
  lev_prime := hlev
  Comp := Unit
  vol := 0
  chern := 0
  chern_homog := fun _ _ _ _ => rfl
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl
  CurveHT := fun _ => Empty
  degHT := fun _ _ _ => 0
  CurveDR := fun _ => Empty
  degDR := fun _ _ _ => 0
  FibComp := fun _ => Empty
  fibInBd := fun _ _ => False
  Pt := Unit
  phiDR := fun _ _ _ => 0
  phiMod := fun _ _ _ => 0
  phiFr := fun _ _ _ => 0
  XC := Unit
  rfn := fun _ => Real.exp 1
  rfn_ge := fun _ => le_rfl
  hLo := fun _ => 1
  hUp := fun _ => 1
  hLo_le := fun _ => ⟨one_pos, le_rfl⟩
  connN := fun _ => 0
  curvN := fun _ => 0
  compOf := fun _ => ()
  normDetInf := fun _ _ => 1
  compPt := fun _ => ()
  normDetT := fun _ _ _ => 1
  normDetH := fun _ _ _ => 1
  htDetT := fun _ _ _ => 0
  ALB := Unit
  arSelf := fun _ => 0
  arSelfC := fun _ _ => 0
  arSelf_sum := fun _ => by simp
  geo := fun _ => 0
  geoC := fun _ _ => 0
  geo_sum := fun _ => by simp
  arVol := fun _ => 0
  semipos := fun _ => True
  nefFib := fun _ => True
  arNef := fun _ => True
  Mbar := fun _ _ _ => ()

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg GlobalTheory.QFam Cardinal

namespace GlobalTheory.KZ.GalUnits

theorem exists_equiv_comp {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  let : Algebra R K := f.toAlgebra
  let : Algebra R L := g.toAlgebra
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' R L
  have h1 : #K = #ι := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' v hv hR hK
  have h2 : #L = #κ :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' w hw hR (hKL ▸ hK)
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.symm.trans (hKL.trans h2))
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis w hw
  let e' : Algebra.adjoin R (Set.range v) ≃ₐ[R] Algebra.adjoin R (Set.range w) :=
    (hv.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R e)).trans hw.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  have hf : f r = algebraMap R K r := rfl
  have hg : g r = algebraMap R L r := rfl
  rw [hf, hg, IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range v)) K,
    IsAlgClosure.equivOfEquiv_algebraMap]
  have : e'.toRingEquiv (algebraMap R _ r) = algebraMap R _ r := e'.commutes r
  rw [this, ← IsScalarTower.algebraMap_apply]

theorem exists_ext {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x : Ω, σ (ε x) = ε (s x) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hR : #Ω ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ Ω).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  exact exists_equiv_comp ε (ε.comp (s : Ω →+* Ω)) hR
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl

theorem mem_range_of_pow_eq_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ε : Ω →+* ℂ) {n : ℕ}
    (hn : 0 < n) {w : ℂ} (hw : w ^ n = 1) : ∃ y, ε y = w := by
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos n Ω hn))
  have hz' : IsPrimitiveRoot z n := Polynomial.isRoot_cyclotomic_iff.1 hz
  have he : IsPrimitiveRoot (ε z) n := hz'.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := he.eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow, hi]⟩

theorem eps_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = ee (x : ℂ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hw : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = x.num * (2 * Real.pi * Complex.I) := by
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_ne_zero
      have : (x : ℂ) = (x.num : ℂ) / x.den := by exact_mod_cast (Rat.num_div_den x).symm
      rw [this]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hex := mem_range_of_pow_eq_one ε x.den_pos hw
  unfold eOm ee
  exact Function.invFun_eq hex

open Classical in

def lc {R : Type} [Zero R] (M : ℕ) (k : ℤ) (A : ℕ → R) (r : ℚ) : R :=
  if h : ∃ n : ℕ, r = ((k : ℚ) + n) / M then A h.choose else 0

theorem lc_eq {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) (k : ℤ) (A : ℕ → R) (n : ℕ) :
    lc M k A (((k : ℚ) + n) / M) = A n := by
  have h : ∃ m : ℕ, ((k : ℚ) + n) / M = ((k : ℚ) + m) / M := ⟨n, rfl⟩
  unfold lc
  rw [dif_pos h]
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have := h.choose_spec
  rw [div_left_inj' hM', add_right_inj] at this
  have : h.choose = n := by exact_mod_cast this.symm
  rw [this]

theorem lc_zero {R : Type} [Zero R] {M : ℕ} {k : ℤ} (A : ℕ → R) {r : ℚ} (h : ∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) :
    lc M k A r = 0 := by
  unfold lc
  rw [dif_neg]
  push_neg
  exact h

theorem lc_map {R S : Type} [Zero R] [Zero S] (M : ℕ) (k : ℤ) (A : ℕ → R) (g : R → S) (hg : g 0 = 0) (r : ℚ) :
    lc M k (fun n => g (A n)) r = g (lc M k A r) := by
  unfold lc
  split_ifs <;> simp [hg]

theorem eq_lc {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) {k : ℤ} {A : ℕ → R} {F : ℚ → R}
    (h1 : ∀ n : ℕ, F (((k : ℚ) + n) / M) = A n) (h2 : ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → F r = 0) :
    ∀ r, F r = lc M k A r := by
  intro r
  by_cases h : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := h
    rw [h1, lc_eq hM]
  · push_neg at h
    rw [h2 r h, lc_zero A h]

theorem lc_unique {M : ℕ} (hM : 0 < M) {f : ℍ → ℂ} {k k' : ℤ} {A A' : ℕ → ℂ}
    (h : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A)
    (h' : HasQ M (fun τ => f τ * ee (-((k' : ℂ) / M) * (τ : ℂ))) A') : lc M k A = lc M k' A' := by
  wlog hk : k ≤ k' generalizing k k' A A'
  · exact (this h' h (le_of_not_ge hk)).symm
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k' = k + m := ⟨(k' - k).toNat, by omega⟩
  have hs : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => if m ≤ n then A' (n - m) else 0) := by
    rw [hasQ_iff] at h' ⊢
    intro τ
    set Q := Complex.exp (2 * Real.pi * Complex.I * τ / M) with hQ
    have h2 := (h' τ).mul_right (Q ^ m)
    have e : f τ * ee (-(((k + m : ℤ) : ℂ) / M) * (τ : ℂ)) * Q ^ m = f τ * ee (-((k : ℂ) / M) * (τ : ℂ)) := by
      rw [mul_assoc]; congr 1
      unfold ee
      rw [hQ, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [e] at h2
    refine (Function.Injective.hasSum_iff (f := fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n)
      (add_left_injective m) ?_).mp ?_
    · intro x hx
      have : ¬ m ≤ x := by
        intro hmx; exact hx ⟨x - m, by simp only; omega⟩
      simp [this]
    · rw [← hQ] at h2
      have e2 : (fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n) ∘ (· + m) = fun i => A' i * Q ^ i * Q ^ m := by
        funext n
        simp only [Function.comp, le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel, pow_add]
        ring
      rw [e2]; exact h2
  have hA := HasQ.coeff_unique hM h hs
  subst hA
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  funext r
  by_cases hr : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := hr
    rw [lc_eq hM]
    by_cases hmn : m ≤ n
    · rw [if_pos hmn]
      have : ((k : ℚ) + n) / M = (((k + m : ℤ) : ℚ) + ((n - m : ℕ) : ℚ)) / M := by
        push_cast [Nat.cast_sub hmn]; ring
      rw [this, lc_eq hM]
    · rw [if_neg hmn, lc_zero]
      intro n' hn'
      rw [div_left_inj' hM'] at hn'
      push_cast at hn'
      have : (n : ℚ) = m + n' := by linarith
      have : n = m + n' := by exact_mod_cast this
      omega
  · push_neg at hr
    rw [lc_zero _ hr, lc_zero]
    intro n' hn'
    apply hr (m + n')
    rw [hn']; push_cast; ring

end GlobalTheory.KZ.GalUnits

namespace GlobalTheory.KZ

open GalUnits

theorem gal_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b d : ℕ) (s : Ω ≃ₐ[ℚ] Ω), 0 < M → a < M → s (eOm ε (1 / M)) = eOm ε (d / M) → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → T.gal s (siegel T c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel T c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] := by
  intro Ω _ _ _ ε T c M a b d s hM ha hs h1 h2
  obtain ⟨σ, hσ⟩ := exists_ext ε s
  have hσM : σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) := by
    have e1 := eps_eOm ε (1 / M)
    have e2 := eps_eOm ε (d / M)
    push_cast at e1 e2
    rw [← e1, hσ, hs, e2]
  obtain ⟨k0, B, hB, hB'⟩ := GlobalTheory.T.smoothedSiegelUnit_coeff_galois_level c M a b d σ hM ha hσM h1 h2
  obtain ⟨k1, A1, hA1, c1, z1⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a b hM ha h1
  obtain ⟨k2, A2, hA2, c2, z2⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a (d * b) hM ha h2
  have L1 := eq_lc hM c1 z1
  have L2 := eq_lc hM c2 z2
  have U1 := lc_unique hM hA1 hB
  have U2 := lc_unique hM hB' hA2
  apply T.exp.toRingHom.injective
  ext r
  apply ε.injective
  show ε ((T.exp (T.gal s _)).coeff r) = ε ((T.exp _).coeff r)
  rw [T.gal_exp, ← hσ, L1, L2, ← lc_map M k1 A1 ε (map_zero ε), U1, ← lc_map M k0 B σ (map_zero σ), U2,
    lc_map M k2 A2 ε (map_zero ε)]

end GlobalTheory.KZ
end
end

