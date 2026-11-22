import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0010

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder

section Poly

variable {J : Type} [Fintype J]

theorem adens_hasFDerivAt_eval (F : MvPolynomial J ℂ) (z : J → ℂ) :
    HasFDerivAt (fun w => eval w F)
      (∑ i, eval z (pderiv i F) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i) z := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const a z
  | add p q hp hq =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p n hp =>
    classical
    have h := hp.mul (hasFDerivAt_apply n z)
    have hf : (fun w : J → ℂ => eval w (p * X n)) = fun w => eval w p * w n := by
      funext w
      simp
    rw [hf]
    refine h.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 : ∀ x, eval z (pderiv x (X n : MvPolynomial J ℂ)) = if x = n then 1 else 0 := by
      intro x
      rw [pderiv_X]
      by_cases hx : x = n
      · subst hx
        simp
      · simp [hx]
    have h2 : ∀ x, eval z (pderiv x (p * X n)) =
        eval z p * (if x = n then 1 else 0) + z n * eval z (pderiv x p) := by
      intro x
      rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, h1, eval_X]
    have h3 : ∑ x, eval z (pderiv x (p * X n)) * v x =
        eval z p * v n + z n * ∑ x, eval z (pderiv x p) * v x := by
      simp only [h2, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h3.symm

end Poly

variable {J : Type} [Fintype J] {D : ℕ}

theorem adens_isConeTangent {P : Ideal (MvPolynomial J ℤ)} {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (hU : IsOpen U) (hγ : AnalyticOnNhd ℂ γ U)
    (hpts : ∀ y ∈ U, γ y ∈ pts P) {y : Fin D → ℂ} (hy : y ∈ U) (ξ : Fin D → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hy] with w hw
    exact (hpts w hw).2 f hf
  have hd := (adens_hasFDerivAt_eval F (γ y)).comp y (hγ y hy).differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin D → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [ContinuousLinearMap.sum_apply, smul_eq_mul] using this

theorem adens_contDiffAt_logρ_id {m : ConeMetric ℂ J} (hsm : IsSmoothMetric m) {z : J → ℂ}
    (hne : z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log (m.ρ w)) z := by
  have hρ : ContDiffAt ℝ 2 m.ρ z :=
    (hsm.contDiffAt (isOpen_ne.mem_nhds hne)).of_le (WithTop.coe_le_coe.2 le_top)
  exact hρ.log (m.pos _ hne).ne'

theorem adens_maDensity_nonneg_of {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {V : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (hV : IsOpen V) (hγ : AnalyticOnNhd ℂ γ V)
    (hpts : ∀ y ∈ V, γ y ∈ pts P) {y : Fin D → ℂ} (hy : y ∈ V) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  have hne : γ y ≠ 0 := (hpts y hy).1
  have h2 := adens_contDiffAt_logρ hsp.1 (hγ y hy) hne
  rw [adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (m.ρ z)) ξ (hγ y hy)
    (adens_contDiffAt_logρ_id hsp.1 hne)
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (m.ρ z)) ∘ γ) y ξ
  rw [hl]
  exact hsp.2 _ (hpts y hy) hne _ (adens_isConeTangent hV hγ hpts hy ξ)

theorem adens_maDensity_nonneg_loc {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {γ : (Fin D → ℂ) → J → ℂ}
    {y : Fin D → ℂ} (hγ : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' ∧ γ y' ∈ pts P) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  obtain ⟨s, hs, hsγ⟩ := hγ.exists_mem
  obtain ⟨V, hVs, hV, hyV⟩ := mem_nhds_iff.1 hs
  exact adens_maDensity_nonneg_of hsp hV (fun w hw => (hsγ w (hVs hw)).1)
    (fun w hw => (hsγ w (hVs hw)).2) hyV

theorem adens_maDensity_nonneg {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (h : IsParam P U γ) {y : Fin D → ℂ} (hy : y ∈ U) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y :=
  adens_maDensity_nonneg_of hsp h.1 h.2.1 h.2.2.1 hy

theorem adens_continuousOn_maDens (φ : Fin D → (Fin D → ℂ) → ℝ) {V : Set (Fin D → ℂ)}
    (hV : IsOpen V) (h : ∀ k, ContDiffOn ℝ 2 (φ k) V) :
    ContinuousOn (ReciprocityTheory.AnForm.maDens φ) V := by
  have hH : ∀ k, ContinuousOn (fun z => fderiv ℝ (fderiv ℝ (φ k)) z) V := fun k =>
    ((h k).fderiv_of_isOpen hV (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl
  have hap : ∀ k (v w : Fin D → ℂ), ContinuousOn (fun z => fderiv ℝ (fderiv ℝ (φ k)) z v w) V :=
    fun k v w => ((hH k).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hE : ∀ k i j, ContinuousOn (fun z => ReciprocityTheory.AnForm.hessC (φ k) z i j) V := by
    intro k i j
    unfold ReciprocityTheory.AnForm.hessC
    simp only []
    refine ContinuousOn.div_const ?_ _
    refine ContinuousOn.add (Complex.continuous_ofReal.comp_continuousOn ((hap _ _ _).add (hap _ _ _)))
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
        ((hap _ _ _).sub (hap _ _ _))))
  have hM : ∀ k, ContinuousOn (fun z => ReciprocityTheory.AnForm.hessC (φ k) z) V := fun k =>
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hE k i j
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.mdisc
  refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
    (continuousOn_const.mul (continuousOn_finsetSum _ fun S _ => continuousOn_const.mul ?_)))
  exact (continuous_id.matrix_det).comp_continuousOn
    (continuousOn_finsetSum _ fun k _ => hM k)

def adensF (m : ConeMetric ℂ J) (γ : (Fin D → ℂ) → J → ℂ) (ν : (Fin D → ℂ) → ℝ)
    (y : Fin D → ℂ) : ℝ :=
  maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y / ((D.factorial : ℝ) * ν y)

theorem adensF_compat {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)}
    (hsm : IsSmoothMetric m) {U U' : Set (Fin D → ℂ)} {γ γ' : (Fin D → ℂ) → J → ℂ}
    {ν ν' : (Fin D → ℂ) → ℝ} (h : IsParam P U γ) (hν : IsDensityFor μ U γ ν)
    (h' : IsParam P U' γ') (hν' : IsDensityFor μ U' γ' ν')
    {O' : Set (J → ℂ)} {q' : (J → ℂ) → Fin D → ℂ} (hO' : IsOpen O') (hq' : AnalyticOnNhd ℂ q' O')
    (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {y : Fin D → ℂ} (hy : y ∈ U) (hyO : γ y ∈ O') :
    adensF m γ' ν' (q' (γ y)) * ((D.factorial : ℝ) * ν y) =
      maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  have hτ : q' (γ y) ∈ U' := (adens_trans_fac h.2.2.1 hOP' hsc' hqγ' hy hyO).1
  have e1 := adens_density_compare h hν h'.1 h'.2.1 hν' hO' hq' hOP' hsc' hqγ' hy hyO
  have e2 := adens_maDensity_compare hsm h h'.2.1 hO' hq' hOP' hsc' hqγ' hy hyO
  have hpos : 0 < ν' (q' (γ y)) := hν'.2.1 _ hτ
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  rw [e1, e2]
  unfold adensF
  field_simp

theorem adensF_nonneg {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) {y : Fin D → ℂ} (hy : y ∈ U) : 0 ≤ adensF m γ ν y := by
  unfold adensF
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  exact div_nonneg (adens_maDensity_nonneg hsp h hy) (mul_pos hD (hν.2.1 y hy)).le

theorem adensF_continuousOn {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    {μ : Measure (J → ℂ)} (hsm : IsSmoothMetric m) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) : ContinuousOn (adensF m γ ν) U := by
  obtain ⟨hU, hγ, hpts, -⟩ := h
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hMA : ContinuousOn (maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w)))) U := by
    refine adens_continuousOn_maDens _ hU fun _ => ?_
    intro y hy
    exact (adens_contDiffAt_logρ hsm (hγ y hy) (hpts y hy).1).contDiffWithinAt
  exact hMA.div (continuousOn_const.mul hν.1.continuousOn) fun y hy =>
    (mul_pos hD (hν.2.1 y hy)).ne'

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AInterpSt
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem interp_rho (m₀ m₁ : ConeMetric ℂ (Ix κ)) (t : ℝ) (z : Ix κ → ℂ) :
    (interp m₀ m₁ t).ρ z = m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t := rfl

theorem fderiv2_lin_comb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} (hS : IsOpen S)
    {f g h : E → ℝ} (a b : ℝ) (hf : ContDiffOn ℝ 2 f S) (hg : ContDiffOn ℝ 2 g S)
    (hh : ∀ y ∈ S, h y = a * f y + b * g y) {z : E} (hz : z ∈ S) :
    fderiv ℝ (fderiv ℝ h) z = a • fderiv ℝ (fderiv ℝ f) z + b • fderiv ℝ (fderiv ℝ g) z := by
  have hfz : ∀ y ∈ S, ContDiffAt ℝ 2 f y := fun y hy => hf.contDiffAt (hS.mem_nhds hy)
  have hgz : ∀ y ∈ S, ContDiffAt ℝ 2 g y := fun y hy => hg.contDiffAt (hS.mem_nhds hy)
  have e1 : fderiv ℝ h =ᶠ[𝓝 z] fun y => a • fderiv ℝ f y + b • fderiv ℝ g y := by
    filter_upwards [hS.mem_nhds hz] with y hy
    have hfd : DifferentiableAt ℝ f y := (hfz y hy).differentiableAt (by first | norm_num | simp)
    have hgd : DifferentiableAt ℝ g y := (hgz y hy).differentiableAt (by first | norm_num | simp)
    have hev : h =ᶠ[𝓝 y] fun w => a * f w + b * g w := by
      filter_upwards [hS.mem_nhds hy] with w hw using hh w hw
    exact (((hfd.hasFDerivAt.const_mul a).add (hgd.hasFDerivAt.const_mul b)).congr_of_eventuallyEq hev).fderiv
  rw [e1.fderiv_eq]
  have hf1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hfz z hz).fderiv_right (m := 1) (by first | norm_num | rfl | simp)).differentiableAt (by first | norm_num | simp)
  have hg1 : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((hgz z hz).fderiv_right (m := 1) (by first | norm_num | rfl | simp)).differentiableAt (by first | norm_num | simp)
  exact ((hf1.hasFDerivAt.const_smul a).add (hg1.hasFDerivAt.const_smul b)).fderiv

theorem isGood_interp {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsGood D x (interp m₀ m₁ t) μ := by
  obtain ⟨ht0, ht1⟩ := ht
  have hS : IsOpen {z : Ix κ → ℂ | z ≠ 0} := isOpen_ne
  have hsm0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀.ρ {z | z ≠ 0} := hg₀.semipos.1
  have hsm1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁.ρ {z | z ≠ 0} := hg₁.semipos.1
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
      | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
      | (norm_cast; exact le_top)
      | decide
  have hl0 : ContDiffOn ℝ 2 (fun z => Real.log (m₀.ρ z)) {z | z ≠ 0} :=
    (hsm0.of_le h2).log fun z hz => (m₀.pos z hz).ne'
  have hl1 : ContDiffOn ℝ 2 (fun z => Real.log (m₁.ρ z)) {z | z ≠ 0} :=
    (hsm1.of_le h2).log fun z hz => (m₁.pos z hz).ne'
  refine ⟨hg₀.arith, hg₀.indep, hg₀.smooth, ?_, ?_, hg₀.conjMu, hg₀.vol⟩
  · unfold IsSemipositiveOn
    refine ⟨?_, ?_⟩
    · show ContDiffOn ℝ _ (fun z => m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) _
      exact (hsm0.rpow_const_of_ne fun z hz => (m₀.pos z hz).ne').mul
        (hsm1.rpow_const_of_ne fun z hz => (m₁.pos z hz).ne')
    · intro z hz hz0 w hw
      have h0 := hg₀.semipos.2 z hz hz0 w hw
      have h1 := hg₁.semipos.2 z hz hz0 w hw
      unfold leviForm at h0 h1 ⊢
      rw [fderiv2_lin_comb (h := fun z => Real.log ((interp m₀ m₁ t).ρ z)) hS (1 - t) t hl0 hl1
        (fun y hy => by
          try dsimp only
          rw [interp_rho, Real.log_mul (Real.rpow_pos_of_pos (m₀.pos y hy) _).ne'
            (Real.rpow_pos_of_pos (m₁.pos y hy) _).ne', Real.log_rpow (m₀.pos y hy),
            Real.log_rpow (m₁.pos y hy)]) hz0]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h0, mul_nonneg ht0 h1]
  · intro z
    rw [interp_rho, interp_rho, hg₀.conjM z, hg₁.conjM z]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NotRelevantOfDimZero
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def killB (T : Finset K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval (fun p => if p.1 ∈ T then 0 else X p)

theorem killB_X (T : Finset K) (p : Σ k, ι k) :
    killB T (X p : MRing ι) = if p.1 ∈ T then 0 else X p := by
  unfold killB
  rw [MvPolynomial.aeval_X]

open Classical in
theorem killB_monomial (T : Finset K) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    killB T (monomial m c : MRing ι) = if (∃ p, p.1 ∈ T ∧ m p ≠ 0) then 0 else monomial m c := by
  unfold killB
  rw [MvPolynomial.aeval_monomial]
  split_ifs with h
  · obtain ⟨p, hpT, hp⟩ := h
    apply mul_eq_zero_of_right
    rw [Finsupp.prod]
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
    simp [hpT, hp]
  · push_neg at h
    rw [Finsupp.prod]
    have hc : ∀ p ∈ m.support, (if p.1 ∈ T then (0 : MRing ι) else X p) ^ m p = X p ^ m p := by
      intro p hp
      rw [if_neg]
      intro hT
      exact (Finsupp.mem_support_iff.mp hp) (h p hT)
    rw [Finset.prod_congr rfl hc, ← Finsupp.prod, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]

theorem killB_multiHomog (T : Finset K) {s : MRing ι} {c : K → ℕ} (hs : IsMultiHomog s c) :
    killB T s = 0 ∨ killB T s = s := by
  classical
  by_cases hT : ∃ k ∈ T, c k ≠ 0
  · left
    obtain ⟨k, hkT, hck⟩ := hT
    rw [s.as_sum, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    have h := hs m hm k
    rw [← h] at hck
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hck
    rw [killB_monomial, if_pos ⟨⟨k, i⟩, hkT, hi⟩]
  · right
    push_neg at hT
    have key : ∀ m ∈ s.support, killB T (monomial m (coeff m s)) = monomial m (coeff m s) := by
      intro m hm
      rw [killB_monomial, if_neg]
      rintro ⟨p, hpT, hp⟩
      have h := hs m hm p.1
      rw [hT p.1 hpT] at h
      exact hp ((Finset.sum_eq_zero_iff.mp h) p.2 (Finset.mem_univ _))
    calc killB T s = killB T (∑ m ∈ s.support, monomial m (coeff m s)) := by rw [← s.as_sum]
      _ = ∑ m ∈ s.support, killB T (monomial m (coeff m s)) := map_sum _ _ _
      _ = ∑ m ∈ s.support, monomial m (coeff m s) := Finset.sum_congr rfl key
      _ = s := s.as_sum.symm

theorem le_comap_killB {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (T : Finset K) :
    P ≤ P.comap (killB T) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases killB_multiHomog T ha with h | h
  · rw [h]; exact Ideal.zero_mem _
  · rw [h]; exact Ideal.subset_span hf

theorem killB_comp {T T' : Finset K} (h : T ⊆ T') :
    (killB T' : MRing ι →ₐ[ℤ] MRing ι).comp (killB T) = killB T' := by
  apply MvPolynomial.algHom_ext
  intro p
  rw [AlgHom.comp_apply, killB_X]
  split_ifs with hp
  · rw [map_zero, killB_X, if_pos (h hp)]
  · rfl

theorem comap_killB_mono {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {T T' : Finset K}
    (h : T ⊆ T') : P.comap (killB T) ≤ P.comap (killB T') := by
  intro x hx
  rw [Ideal.mem_comap] at hx ⊢
  rw [← killB_comp h, AlgHom.comp_apply]
  exact Ideal.mem_comap.mp (le_comap_killB hP T' hx)

theorem card_le_dim {P : Ideal (MRing ι)} (hPp : P.IsPrime) (hPm : IsMultiHomogIdeal P)
    (hrel : IsRelevant P) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ P) := by
  classical
  haveI := hPp
  let T : ℕ → Finset K := fun j => Finset.univ.filter fun k => ((Fintype.equivFin K k : ℕ) < j)
  let Q : ℕ → Ideal (MRing ι) := fun j => P.comap (killB (T j))
  have hQp : ∀ j, (Q j).IsPrime := fun j => Ideal.comap_isPrime _ _
  have hPQ : ∀ j, P ≤ Q j := fun j => le_comap_killB hPm (T j)
  have hT : ∀ j, T j ⊆ T (j + 1) := by
    intro j k hk
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    omega
  have hlt : ∀ j < Fintype.card K, Q j < Q (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (comap_killB_mono hPm (hT j)) ?_
    intro heq
    set k := (Fintype.equivFin K).symm ⟨j, hj⟩ with hk
    have hkv : ((Fintype.equivFin K k : Fin _) : ℕ) = j := by simp [hk]
    obtain ⟨i, hi⟩ := hrel k
    have hin : k ∈ T (j + 1) := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hout : k ∉ T j := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h1 : (X ⟨k, i⟩ : MRing ι) ∈ Q (j + 1) := by
      rw [Ideal.mem_comap, killB_X, if_pos hin]
      exact P.zero_mem
    have h2 : (X ⟨k, i⟩ : MRing ι) ∉ Q j := by
      rw [Ideal.mem_comap, killB_X, if_neg hout]
      exact hi
    exact h2 (heq ▸ h1)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (P : Set (MRing ι)) :=
    fun j => ⟨⟨Q j, hQp j⟩, fun x hx => hPQ j hx⟩
  let s : LTSeries (PrimeSpectrum.zeroLocus (P : Set (MRing ι))) :=
    ⟨Fintype.card K, f, fun j => by
      first
      | exact Subtype.mk_lt_mk.mpr (PrimeSpectrum.asIdeal_lt_asIdeal.mp (hlt j j.isLt))
      | exact (hlt j j.isLt)⟩
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim s

theorem not_relevant_of_dim_zero {W : Ideal (MRing ι)} [W.IsPrime] (hWm : IsMultiHomogIdeal W)
    (hd : ringKrullDim (MRing ι ⧸ W) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {s : MRing ι} {c : K → ℕ} (hs : IsMultiHomog s c) (hsW : s ∉ W) {W' : Ideal (MRing ι)}
    (hW' : W' ∈ (W ⊔ Ideal.span {s}).minimalPrimes) : ¬ IsRelevant W' := by
  classical
  intro hrel
  have hW'p : W'.IsPrime := hW'.1.1
  have hJ : IsMultiHomogIdeal (W ⊔ Ideal.span {s}) := isMultiHomogIdeal_sup_span hWm hs
  have hW'm : IsMultiHomogIdeal W' := by
    let e := Fintype.equivFin K
    letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := lexDecEq (Fintype.card K)
    letI : GradedAlgebra (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) :=
      MvPolynomial.weightedGradedAlgebra ℤ (lexW (ι := ι) e)
    rw [← isHomogeneous_lex_iff e] at hJ ⊢
    have hcore := hW'p.homogeneousCore (𝒜 := weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))
    have hle : W ⊔ Ideal.span {s} ≤
        (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).toIdeal := by
      rw [← hJ.toIdeal_homogeneousCore_eq_self]
      exact Ideal.homogeneousCore_mono _ hW'.1.2
    have hge := hW'.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    have heq : (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).toIdeal = W' :=
      le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) hge
    rw [← heq]
    exact (W'.homogeneousCore (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e))).isHomogeneous
  have h1 := card_le_dim hW'p hW'm hrel
  have hWW' : W ≤ W' := le_trans le_sup_left hW'.1.2
  have hsW' : s ∈ W' :=
    hW'.1.2 ((le_sup_right : Ideal.span {s} ≤ W ⊔ Ideal.span {s}) (Ideal.mem_span_singleton_self s))
  let g : MRing ι ⧸ W →+* MRing ι ⧸ W' := Ideal.Quotient.factor hWW'
  have hg : ∀ a ∈ Ideal.span {Ideal.Quotient.mk W s}, g a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    have : g (Ideal.Quotient.mk W s) = 0 := by
      simp only [g, Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hsW'
    rw [this, mul_zero]
  let f : (MRing ι ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W s} →+* MRing ι ⧸ W' :=
    Ideal.Quotient.lift _ g hg
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk W x), rfl⟩
  have hnz : Ideal.Quotient.mk W s ∈ nonZeroDivisors (MRing ι ⧸ W) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    exact hsW (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have h2 : ((Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    calc ((Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (MRing ι ⧸ W') + 1 := by
          gcongr
      _ ≤ ringKrullDim ((MRing ι ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W s}) + 1 := by
          gcongr
          exact ringKrullDim_le_of_surjective f hf
      _ ≤ ringKrullDim (MRing ι ⧸ W) := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      _ = _ := hd
  rw [zero_add] at h2
  have h3 : (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤ ((Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h2
  have h4 := WithBot.coe_le_coe.mp h3
  have h5 : ((Fintype.card K + 1 : ℕ) : ℕ∞) ≤ ((Fintype.card K : ℕ) : ℕ∞) := h4
  exact absurd (Nat.cast_le.mp h5) (by omega)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

