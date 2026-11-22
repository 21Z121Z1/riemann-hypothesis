import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0001
import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PDeltaRatioIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

theorem DeltaRatioIntegral.proof (hA : SuperlatticeRatio.Statement)
    (hI : HeckeRatioInvariant.Statement) (hE : HeckeRatioExpansion.Statement)
    (hQ : LevelOneQExpansion.Statement) : DeltaRatioIntegral.Statement := by
  intro L L' p hp hle hidx
  obtain ⟨τ, hj, hmem⟩ := hA L L' p hp hle hidx
  set M := heckeRatios ⟨p, hp.pos⟩ τ with hM
  set R := Algebra.adjoin ℤ {(weierstrassCurve L).j}
  have hes : ∀ k, M.esymm k ∈ R := by
    intro k
    obtain ⟨hd, hx⟩ := hE p hp k
    obtain ⟨Q, hQk⟩ := hQ _ hd (fun γ τ' ↦ congrArg (fun m : Multiset ℂ ↦ m.esymm k) (hI p hp γ τ')) hx
    rw [hM, hQk τ, ← hj]
    exact Polynomial.aeval_mem_adjoin_singleton ℤ _
  set P : ℂ[X] := (M.map fun t ↦ X - C t).prod with hP
  have hmon : P.Monic := monic_multiset_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C t
  have hlift : P ∈ lifts (algebraMap R ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ Multiset.card M
    · rw [hP, Multiset.prod_X_sub_C_coeff M hn]
      have hmem' : (-1 : ℂ) ^ (Multiset.card M - n) * M.esymm (Multiset.card M - n) ∈ R :=
        R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) _) (hes _)
      exact ⟨⟨_, hmem'⟩, rfl⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, eq_comm]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hP, natDegree_multiset_prod_X_sub_C_eq_card]
      omega
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  refine ⟨q, hqm, ?_⟩
  rw [eval₂_eq_eval_map, hq, hP, eval_multiset_prod]
  apply Multiset.prod_eq_zero
  rw [Multiset.map_map]
  exact Multiset.mem_map.2 ⟨_, hmem, by simp⟩

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PHeckeRatioExpansion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm PowerSeries Complex
open scoped Real Manifold

noncomputable section

namespace HeckeRatioExpansion

theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

theorem esymm_map_div (s : Multiset ℂ) (d : ℂ) (k : ℕ) :
    (s.map (· / d)).esymm k = s.esymm k / d ^ k := by
  have h := Multiset.pow_smul_esymm d⁻¹ k s
  simp only [smul_eq_mul] at h
  rw [div_eq_mul_inv, ← inv_pow, mul_comm, h]
  simp [div_eq_mul_inv, mul_comm]

theorem intSeriesConv_X (r : ℝ) : IntSeriesConv X r := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff_X, hn]

theorem intSeriesEval_X (z : ℂ) : intSeriesEval X z = z := by
  rw [intSeriesEval, tsum_eq_single 1 (fun n hn ↦ by simp [coeff_X, hn])]
  simp

theorem exists_evalHom (hR : IntSeriesRing.Statement) {r : ℝ} (hr : 0 ≤ r)
    (S : Subring (PowerSeries ℤ)) (hS : ∀ F, F ∈ S ↔ IntSeriesConv F r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ∃ φ : S →+* ℂ, ∀ F : S, φ F = intSeriesEval F z := by
  obtain ⟨-, hmul, hsum, -, -⟩ := hR r hr
  refine ⟨{ toFun := fun F ↦ intSeriesEval F z
            map_one' := ?_
            map_mul' := fun F G ↦ hmul F G ((hS F).1 F.2) ((hS G).1 G.2) z hz
            map_zero' := by simp [intSeriesEval]
            map_add' := fun F G ↦ ?_ }, fun _ ↦ rfl⟩
  · change intSeriesEval 1 z = 1
    rw [intSeriesEval, tsum_eq_single 0 (fun n hn ↦ by simp [coeff_one, hn])]
    simp
  · change intSeriesEval ((F : PowerSeries ℤ) + G) z = intSeriesEval F z + intSeriesEval G z
    refine (hsum _ ((hS _).1 (S.add_mem F.2 G.2)) z hz).unique ?_
    simpa [add_mul] using (hsum F ((hS F).1 F.2) z hz).add (hsum G ((hS G).1 G.2) z hz)

theorem proof (hR : IntSeriesRing.Statement) (hI : IntSeriesInv.Statement)
    (hD : DeltaIntSeries.Statement) (hN : IntSeriesNorm.Statement)
    (hH : HeckeRatioHolo.Statement) : HeckeRatioExpansion.Statement := by
  intro p hp k
  refine ⟨hH _ k, ?_⟩
  rcases k with _ | k
  · simpa [Multiset.esymm] using hasIntegralLaurentQExpansion_const 1
  obtain ⟨D, hD0, hDc, hΔ⟩ := hD
  have hp0 : 0 < p := hp.pos
  set n : ℕ+ := ⟨p, hp.pos⟩ with hn
  have hnp : (n : ℕ) = p := rfl
  have hpne : p ≠ 0 := hp0.ne'

  have hD2 : IntSeriesConv D (1 / 2) := hDc _ (by norm_num) (by norm_num)
  obtain ⟨⟨S₂, hS₂⟩, hmul₂, -, -, -⟩ := hR (1 / 2) (by norm_num)
  have hGc : IntSeriesConv (X * D) (1 / 2) :=
    (hS₂ _).1 (S₂.mul_mem ((hS₂ _).2 (intSeriesConv_X _)) ((hS₂ _).2 hD2))
  have evG : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → intSeriesEval (X * D) w = w * intSeriesEval D w := by
    intro w hw
    rw [hmul₂ _ _ (intSeriesConv_X _) hD2 w hw, intSeriesEval_X]
  obtain ⟨E₁, hE₁c, hE₁⟩ := hN (X * D) (1 / 2) (by norm_num) hGc p hp0 (k + 1)
  obtain ⟨E₀, hE₀c, hE₀⟩ := hN (X * D) (1 / 2) (by norm_num) hGc p hp0 k
  obtain ⟨V, r₁, hr₁, hVc, hDV⟩ := hI D (1 / 2) (by norm_num) hD2 hD0

  set R : ℝ := min ((1 / 2) ^ p) r₁ with hRdef
  have hR0 : 0 < R := lt_min (by positivity) hr₁
  have hRh : R ≤ (1 / 2) ^ p := min_le_left _ _
  have hRr : R ≤ r₁ := min_le_right _ _
  have hRl : R < 1 := hRh.trans_lt (pow_lt_one₀ (by norm_num) (by norm_num) hpne)
  obtain ⟨⟨S, hS⟩, hmul, hsum, -, hexp⟩ := hR R hR0.le
  have mem : ∀ F r', IntSeriesConv F r' → R ≤ r' → F ∈ S := fun F r' h h' ↦
    (hS F).2 ((hR r' (hR0.le.trans h')).2.2.2.1 F R h hR0.le h')
  have hDp : IntSeriesConv D (R ^ p) := hDc _ (by positivity) (pow_lt_one₀ hR0.le hRl hpne)
  let Φ : S := (⟨E₁, mem _ _ hE₁c hRh⟩ + (p : S) ^ 12 * ⟨X, (hS _).2 (intSeriesConv_X R)⟩ ^ p *
      ⟨expand p hpne D, (hS _).2 (hexp p hpne D hDp).1⟩ * ⟨E₀, mem _ _ hE₀c hRh⟩) *
    ⟨V, mem _ _ hVc hRr⟩ ^ (k + 1)
  refine ⟨k + 1, fun n ↦ coeff n (Φ : PowerSeries ℤ), -Real.log R / (2 * π), fun τ hτ ↦ ?_⟩
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hq
  set t := Function.Periodic.qParam p (τ : ℂ) with ht
  have hqR : ‖q‖ < R := by
    have h := (Function.Periodic.norm_qParam_lt_iff one_pos (-Real.log R / (2 * π)) τ).2 hτ
    rwa [show -2 * π * (-Real.log R / (2 * π)) / 1 = Real.log R by field_simp,
      Real.exp_log hR0] at h
  have htq : t ^ p = q := by
    simp only [ht, hq, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have ht0 : t ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hq0 : q ≠ 0 := Function.Periodic.qParam_ne_zero _
  have htle : ‖t‖ ≤ 1 / 2 := by
    refine (lt_of_pow_lt_pow_left₀ p (by norm_num) ?_).le
    rw [← norm_pow, htq]
    exact hqR.trans_le hRh
  have hpt : ∀ a : ℕ, ‖Complex.exp (2 * π * Complex.I * a / p) * t‖ ≤ 1 / 2 := by
    intro a
    rw [norm_mul, Complex.norm_exp]
    simpa using htle
  have hdiv : ∀ a : ℕ, Function.Periodic.qParam 1 (divPoint n a τ) =
      Complex.exp (2 * π * Complex.I * a / p) * t := by
    intro a
    rw [coe_divPoint]
    simp only [ht, Function.Periodic.qParam, ← Complex.exp_add, hnp]
    congr 1
    push_cast
    ring
  have hmulp : Function.Periodic.qParam 1 (mulPoint n τ) = q ^ p := by
    rw [coe_mulPoint]
    simp only [hq, Function.Periodic.qParam, ← Complex.exp_nat_mul, hnp]
    congr 1
    push_cast
    ring
  obtain ⟨φ, hφ⟩ := exists_evalHom hR hR0.le S hS hqR.le
  have hDV' : intSeriesEval D q * intSeriesEval V q = 1 := by
    have := congrArg φ (show (⟨D, mem _ _ hD2 ((hRh.trans (pow_le_of_le_one (by norm_num)
        (by norm_num) hpne)).trans (by norm_num))⟩ : S) * ⟨V, mem _ _ hVc hRr⟩ = 1 from
      Subtype.ext hDV)
    rwa [map_mul, map_one, hφ, hφ] at this
  have hd0 : intSeriesEval D q ≠ 0 := left_ne_zero_of_mul_eq_one hDV'
  have hY : (Multiset.range p).map (fun a ↦ discriminant (divPoint n a τ) /
      discriminant τ) = ((Multiset.range p).map fun a : ℕ ↦
        intSeriesEval (X * D) (Complex.exp (2 * π * Complex.I * a / p) * t)).map
          (· / discriminant τ) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun a _ ↦ ?_
    simp only [Function.comp_apply]
    rw [hΔ (divPoint _ a τ), hdiv a, evG _ (hpt a)]
  have key : q ^ (k + 1) * (heckeRatios n τ).esymm (k + 1) = φ Φ := by
    unfold heckeRatios
    rw [hnp, esymm_cons_succ, hY, esymm_map_div, esymm_map_div, hE₁ t ht0 htle,
      hE₀ t ht0 htle, htq, hΔ τ, hΔ (mulPoint _ τ), hmulp,
      ← (hexp p hpne D hDp).2 q hqR.le]
    simp only [Φ, map_add, map_mul, map_pow, map_natCast]
    simp only [hφ, intSeriesEval_X]
    rw [← hq]
    rw [eq_inv_of_mul_eq_one_right hDV', inv_pow]
    field_simp [hd0, hq0]
    ring
  rw [key, hφ]
  exact hsum _ ((hS _).1 Φ.2) q hqR.le

end HeckeRatioExpansion

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PHeckeRatioHolo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm
open scoped Manifold

noncomputable section

namespace HeckeRatioHolo

theorem mdifferentiable_comp_affine {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℍ → ℍ)
    (α β : ℂ) (hm : ∀ τ : ℍ, (m τ : ℂ) = α * τ + β) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∘ m) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmaps : Set.MapsTo (fun z : ℂ ↦ α * z + β) {z | 0 < z.im} {z | 0 < z.im} := by
    intro z hz
    have h := (m ⟨z, hz⟩).im_pos
    rw [UpperHalfPlane.im, hm] at h
    exact h
  refine (hf.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ ↦ α * z + β) _) hmaps).congr ?_
  intro z hz
  have hmz : m (ofComplex z) = ofComplex (α * z + β) := by
    apply UpperHalfPlane.ext
    rw [hm, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos (hmaps hz)]
  simp only [Function.comp_apply, hmz]

theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

theorem mdifferentiable_esymm (s : Multiset (ℍ → ℂ))
    (hs : ∀ f ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ ↦ (s.map fun f ↦ f τ).esymm k) := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · simpa [Multiset.esymm] using mdifferentiable_const
    · simpa [Multiset.esymm] using mdifferentiable_const
  | cons f s ih =>
    rcases k with _ | k
    · simpa [Multiset.esymm] using mdifferentiable_const
    · simp only [Multiset.map_cons, esymm_cons_succ]
      have hs' : ∀ g ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := fun g hg ↦
        hs g (Multiset.mem_cons_of_mem hg)
      exact (ih hs' (k + 1)).add ((hs f (Multiset.mem_cons_self _ _)).mul (ih hs' k))

theorem proof : HeckeRatioHolo.Statement := by
  intro n k
  have hΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) discriminant := by
    simpa using ModularFormClass.holo CuspForm.discriminant
  let fs : Multiset (ℍ → ℂ) :=
    (fun τ ↦ (n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ) ::ₘ
      (Multiset.range n).map fun a τ ↦ discriminant (divPoint n a τ) / discriminant τ
  have hfs : (fun τ ↦ (heckeRatios n τ).esymm k) = fun τ ↦ (fs.map fun f ↦ f τ).esymm k := by
    funext τ
    simp [heckeRatios, fs, Multiset.map_map]
  rw [hfs]
  apply mdifferentiable_esymm
  intro f hf
  simp only [fs, Multiset.mem_cons, Multiset.mem_map, Multiset.mem_range] at hf
  rcases hf with rfl | ⟨a, -, rfl⟩
  · have h := mdifferentiable_comp_affine hΔ (mulPoint n) n 0 (fun τ ↦ by simp [coe_mulPoint])
    exact (mdifferentiable_const.mul h).div hΔ discriminant_ne_zero
  · have h := mdifferentiable_comp_affine hΔ (divPoint n a) (1 / n) (a / n)
      (fun τ ↦ by rw [coe_divPoint]; ring)
    exact h.div hΔ discriminant_ne_zero

end HeckeRatioHolo

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PJQExpansion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries GroundTheory.Global.Elliptic Function
open scoped MatrixGroups Manifold

noncomputable section

namespace JQExpansion

lemma periodic_comp_ofComplex_of {f : ℍ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.im → f (ofComplex (z + 1)) = f (ofComplex z)) :
    Periodic (f ∘ ofComplex) ((1 : ℝ) : ℂ) := by
  intro w
  simp only [comp_apply, Complex.ofReal_one]
  by_cases hw : 0 < w.im
  · exact hf w hw
  · have hw' : (w + 1).im ≤ 0 := by simpa using hw
    rw [ofComplex_apply_eq_of_im_nonpos hw' (not_lt.mp hw)]

theorem proof : JQExpansion.Statement := by
  set Q : ℍ → ℂ := fun τ ↦ Periodic.qParam 1 τ with hQdef
  set φ : ℍ → ℂ := fun τ ↦ Periodic.qParam 1 τ * modularJ τ with hφdef
  have hqper : ∀ z : ℂ, Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := fun z ↦ by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one, Complex.exp_add,
      Complex.exp_two_pi_mul_I]
  have hQper : Periodic (Q ∘ ofComplex) ((1 : ℝ) : ℂ) :=
    periodic_comp_ofComplex_of fun z hz ↦ by
      have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [hQdef, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1,
]
      exact hqper z
  have hφper : Periodic (φ ∘ ofComplex) ((1 : ℝ) : ℂ) :=
    periodic_comp_ofComplex_of fun z hz ↦ by
      have hE := SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL z
      have hD := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL z
      have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [comp_apply, Complex.ofReal_one, CuspForm.coe_discriminant] at hE hD
      simp only [hφdef, modularJ, hE, hD]
      rw [ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1]
      simp only [hqper]
  have hQhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Q := UpperHalfPlane.mdifferentiable_iff.mpr
    ((Periodic.differentiable_qParam (h := 1)).differentiableOn.congr fun z hz ↦ by
      simp [hQdef, ofComplex_apply_of_im_pos (show 0 < z.im from hz)])
  have hφhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ := UpperHalfPlane.mdifferentiable_iff.mpr
    ((UpperHalfPlane.mdifferentiable_iff.mp hQhol).mul differentiableOn_modularJC)
  have hQb : IsBoundedAtImInfty Q :=
    isBoundedAtImInfty_iff.mpr ⟨1, 0, fun τ _ ↦ (Periodic.norm_qParam_lt_one one_pos τ.im_pos).le⟩
  have hφb : IsBoundedAtImInfty φ := by
    obtain ⟨M, A, hM⟩ := isBoundedAtImInfty_iff.mp (ModularFormClass.bdd_at_infty E₄)
    obtain ⟨C, hC⟩ := exp_isBigO_discriminant.bound
    obtain ⟨A', hA'⟩ := (atImInfty_mem _).mp hC
    refine isBoundedAtImInfty_iff.mpr ⟨C * M ^ 3, max A A', fun τ hτ ↦ ?_⟩
    have h1 := hM τ (le_of_max_le_left hτ)
    have hΔ : 0 < ‖ModularForm.discriminant τ‖ := norm_pos_iff.mpr (discriminant_ne_zero τ)
    have h2 : ‖Periodic.qParam 1 (τ : ℂ)‖ / ‖ModularForm.discriminant τ‖ ≤ C := by
      have h3 := hA' τ (le_of_max_le_right hτ)
      simp only [Set.mem_ofPred_eq, Real.norm_of_nonneg (Real.exp_pos _).le] at h3
      rw [div_le_iff₀ hΔ, Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
      exact h3
    calc ‖φ τ‖ = ‖Periodic.qParam 1 (τ : ℂ)‖ / ‖ModularForm.discriminant τ‖ * ‖E₄ τ‖ ^ 3 := by
          simp only [hφdef, modularJ, norm_mul, norm_div, norm_pow]
          ring
      _ ≤ C * M ^ 3 := mul_le_mul h2 (pow_le_pow_left₀ (norm_nonneg _) h1 3) (by positivity)
          (le_trans (by positivity) h2)
  have hQa := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hQper hQhol hQb
  have hφa := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hφper hφhol hφb
  have hΔa := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  have hE3a := ModularFormClass.analyticAt_cuspFunction_zero (E₄.pow 3) one_pos
    one_mem_strictPeriods_SL

  have hQX : qExpansion 1 Q = X := by
    have hsum : ∀ τ : ℍ, HasSum
        (fun n : ℕ ↦ (if n = 1 then (1 : ℂ) else 0) • Periodic.qParam 1 (τ : ℂ) ^ n) (Q τ) := by
      intro τ
      have e : (fun n : ℕ ↦ (if n = 1 then (1 : ℂ) else 0) • Periodic.qParam 1 (τ : ℂ) ^ n) =
          fun n ↦ if n = 1 then Periodic.qParam 1 (τ : ℂ) else 0 := by
        funext n
        split_ifs with h <;> simp [h]
      rw [e]
      exact hasSum_ite_eq 1 _
    ext m
    have h := UpperHalfPlane.qExpansion_coeff_unique (⟨Q, hQhol.continuous⟩ : C(ℍ, ℂ)) one_pos
      hQa hsum m
    rw [coeff_X]
    exact h.symm

  have hprod : φ * ⇑CuspForm.discriminant = Q * ⇑(E₄.pow 3) := by
    funext τ
    have := discriminant_ne_zero τ
    simp only [Pi.mul_apply, hφdef, hQdef, modularJ, ModularForm.coe_pow, Pi.pow_apply,
      CuspForm.coe_discriminant]
    field_simp
  have hq := congrArg (qExpansion 1) hprod
  obtain ⟨D, hD0, hΔ⟩ := DeltaQExpansionIntegral.proof
  rw [UpperHalfPlane.qExpansion_mul hφa hΔa, UpperHalfPlane.qExpansion_mul hQa hE3a, hQX,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    DeltaQExpansionIntegral.qExpansion_E₄, CuspForm.coe_discriminant, hΔ, map_mul, map_X,
    ← mul_assoc, mul_comm (qExpansion 1 φ) X, mul_assoc] at hq
  have hq' := mul_left_cancel₀ X_ne_zero hq
  set E4Z : PowerSeries ℤ := 1 + (240 : ℤ) • DeltaQExpansionIntegral.sigmaSeries 3 with hE4Z
  set u := invOfUnit D 1 with hu
  have hDu : D * u = 1 := mul_invOfUnit D 1 (by simp [hD0])
  have ha : qExpansion 1 φ = map (Int.castRingHom ℂ) (E4Z ^ 3 * u) := by
    calc qExpansion 1 φ = qExpansion 1 φ * map (Int.castRingHom ℂ) (D * u) := by
          rw [hDu, map_one, mul_one]
      _ = map (Int.castRingHom ℂ) (E4Z ^ 3 * u) := by
          rw [map_mul, ← mul_assoc, hq', map_mul, map_pow]
  refine ⟨fun n ↦ coeff n (E4Z ^ 3 * u), ?_, fun τ ↦ ?_⟩
  · simp [hu, hE4Z, constantCoeff_invOfUnit, DeltaQExpansionIntegral.sigmaSeries]
  · have h := UpperHalfPlane.hasSum_qExpansion one_pos hφper hφhol hφb τ
    have e : ∀ n, coeff n (map (Int.castRingHom ℂ) (E4Z ^ 3 * u)) = ((coeff n (E4Z ^ 3 * u) : ℤ) : ℂ) :=
      fun n ↦ by rw [coeff_map, eq_intCast]
    simp only [ha, e, smul_eq_mul] at h
    exact h

end JQExpansion

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPeriodLatticeCM
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic Module
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem PeriodLatticeCM.proof (S : PrimeDiscriminant K) (F : CMFamily K) :
    PeriodLatticeCM.Statement S F := by
  intro s
  have := S.isTotallyComplex
  have hK : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  obtain ⟨I, c, hc, h⟩ := CMFamily.exists_periodLattice_eq S F s
  let P := idealPeriodPair (F.restrict s) hK I
  let L' : PeriodPair :=
    { ω₁ := c * P.ω₁
      ω₂ := c * P.ω₂
      indep := by
        have := P.indep
        rw [LinearIndependent.pair_iff] at this ⊢
        intro a b hab
        apply this a b
        have hab' : c * (a • P.ω₁ + b • P.ω₂) = 0 := by
          rw [← hab]; simp only [Complex.real_smul]; ring
        exact (mul_eq_zero.1 hab').resolve_left hc }
  have hlat : (L'.lattice : Set ℂ) = (c * ·) '' P.lattice := by
    ext z
    simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, L']
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m * P.ω₁ + n * P.ω₂, ⟨m, n, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨m, n, rfl⟩, rfl⟩
      exact ⟨m, n, by ring⟩
  refine ⟨L', ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [hlat, h, lattice_idealPeriodPair]
  · rw [latticeEnd_eq_of_homothetic hc hlat]
    exact latticeEnd_idealPeriodPair (F.restrict s) hK I

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

