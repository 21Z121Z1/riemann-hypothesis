import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfTwLie
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem open_stab {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

private theorem cmp_lT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, smul_smul, ← Finset.sum_smul]
    rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private def invSub (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) : Submodule ℂ (Sm E a) where
  carrier := {φ | Pf.SInv φ}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, by simp⟩
  add_mem' := by
    intro φ ψ h h'
    refine ⟨fun γ g => congrArg₂ (· + ·) (h.left γ g) (h'.left γ g),
      fun t g => congrArg₂ (· + ·) (h.centre t g) (h'.centre t g), ?_⟩
    have h1 : IsOpen {k | finRep E a k φ = φ} := h.level
    have h2 : IsOpen {k | finRep E a k ψ = ψ} := h'.level
    refine open_stab (finRep E a) _ (h1.inter h2) ⟨by simp, by simp⟩ ?_
    rintro k ⟨e1, e2⟩
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) e1 e2)
  smul_mem' := by
    intro c φ h
    refine ⟨fun γ g => congrArg (c • ·) (h.left γ g), fun t g => congrArg (c • ·) (h.centre t g), ?_⟩
    have h1 : IsOpen {k | finRep E a k φ = φ} := h.level
    refine open_stab (finRep E a) _ h1 (by simp) ?_
    intro k e1
    exact (map_smul _ _ _).trans (congrArg (c • ·) e1)

theorem UpperTheory.V.Lit.Geo.Pf.twLie :
    UpperTheory.V.Lit.Geo.Pf.TwLie := by
  intro E _ _ _ a Ξ r χ hχ X x hx
  let N : Submodule ℂ (Sm E a) := (invSub E a).comap (mulChi a χ).toLinearMap
  have hiff : ∀ y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ), Pf.TwInv χ y ↔ y ∈ tens Ξ.d N := fun y => by
    rw [mem_tens]; rfl
  rw [hiff] at hx
  rw [hiff, hiff]
  have hA : smA Ξ X x ∈ tens Ξ.d N := mem_tens.2 fun j => by
    rw [smA_apply, cmp_rT]
    have h0 : cmp j x ∈ N := mem_tens.1 hx j
    have h1 : lie E a X (cmp j x) + ((r * ell E a X : ℝ) : ℂ) • cmp j x ∈ N := by
      change Pf.SInv (mulChi a χ _)
      rw [← hχ.2]
      exact (Pf.invLie E a _ h0).2 X
    exact (N.add_mem_iff_left (N.smul_mem _ h0)).1 h1
  have hB : smB Ξ X x ∈ tens Ξ.d N := mem_tens.2 fun j => by
    rw [smB_apply, cmp_lT]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (mem_tens.1 hx k)
  constructor
  · have : smLie Ξ X x = smA Ξ X x + smB Ξ X x := by
      simp only [smB, LinearMap.sub_apply, add_sub_cancel]
    rw [this]
    exact Submodule.add_mem _ hA hB
  · rw [smAdj, adj_apply]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hB hA) ?_
    exact Submodule.smul_of_tower_mem _ _ hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullMatBd
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem mul_bd (x y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖∑ k, x i k * y k j‖ ≤ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun k _ => ?_).trans (by simp))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL x i) k).trans (norm_le_pi_norm (toL x) i)
  · exact (norm_le_pi_norm (toL y k) j).trans (norm_le_pi_norm (toL y) k)

private theorem star_bd (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (star x)‖ ≤ ‖toL x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖star (x j i)‖ ≤ _
  rw [norm_star]
  exact (norm_le_pi_norm (toL x j) i).trans (norm_le_pi_norm (toL x) j)

private theorem sand_bd {C : ℝ} (h : GL (Fin a) (Cinf E)) (hC : ‖toL h.val‖ ≤ C) (v : HV E a) :
    ‖sand h v‖ ≤ (a * a * C * C) * ‖v‖ := by
  have h0 : 0 ≤ C := (norm_nonneg _).trans hC
  change ‖toL (h.val * Matrix.of v.1 * star h.val)‖ ≤ _
  have h1 : ‖toL (h.val * Matrix.of v.1)‖ ≤ a * (C * ‖v‖) :=
    (mul_bd _ _).trans (by
      change (a : ℝ) * (‖toL h.val‖ * ‖v‖) ≤ _
      gcongr)
  calc _ ≤ _ := mul_bd _ _
    _ ≤ a * ((a * (C * ‖v‖)) * C) := by
      gcongr
      exact (star_bd _).trans hC
    _ = _ := by ring

private theorem exists_cpt (C : ℝ) : ∃ K : Set (Lie E a), IsCompact K ∧ K ⊆ invSet E a ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → toL h.val ∈ K := by
  have hc : IsClosed {z : Lie E a × Lie E a | toL (Matrix.of z.1 * Matrix.of z.2) = toL 1} := by
    refine isClosed_eq ?_ continuous_const
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun z : Lie E a × Lie E a => ∑ k, z.1 i k * z.2 k j
    fun_prop
  refine ⟨Prod.fst '' ((Metric.closedBall 0 C ×ˢ Metric.closedBall 0 C) ∩ _),
    (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right hc).image continuous_fst, ?_, ?_⟩
  · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
    have e : Matrix.of z.1 * Matrix.of z.2 = 1 := hz
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse e)
  · intro h h1 h2
    exact ⟨(toL h.val, toL (h⁻¹).val), ⟨⟨mem_closedBall_zero_iff.2 h1, mem_closedBall_zero_iff.2 h2⟩,
      congrArg toL h.mul_inv⟩, rfl⟩

private theorem mat_bd (Ξ : AlgRep E a) (C : ℝ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → ∀ y, ‖Ξ.mat h *ᵥ y‖ ≤ B * ‖y‖ := by
  obtain ⟨K, hK, hs, hm⟩ := exists_cpt (E := E) (a := a) C
  have hb : ∀ i j, ∃ b : ℝ, ∀ x ∈ K, ‖extGL (fun y => Ξ.mat y i j) x‖ ≤ b := fun i j =>
    hK.exists_bound_of_continuousOn ((matSmooth E a Ξ i j).1.continuousOn.mono hs)
  choose b hb using hb
  have h0 : 0 ≤ ∑ i, ∑ j, |b i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ i, ∑ j, |b i j|, h0, fun h h1 h2 y => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_⟩
  change ‖∑ j, Ξ.mat h i j * y j‖ ≤ _
  calc _ ≤ ∑ j, |b i j| * ‖y‖ := by
        refine norm_sum_le_of_le _ fun j _ => (norm_mul_le _ _).trans
          (mul_le_mul ?_ (norm_le_pi_norm y j) (norm_nonneg _) (abs_nonneg _))
        have := hb i j _ (hm h h1 h2)
        rw [extGL_val] at this
        exact this.trans (le_abs_self _)
    _ = (∑ j, |b i j|) * ‖y‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, |b i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)) (norm_nonneg _)

end

theorem UpperTheory.V.Lit.Geo.matBd :
    MatBd := by
  intro E _ _ _ a Ξ C
  obtain ⟨B, hB, h⟩ := mat_bd Ξ C
  refine ⟨max B (a * a * C * C), le_max_of_le_left hB, fun g h1 h2 => ⟨fun y => (h g h1 h2 y).trans ?_,
    fun v => (sand_bd g h1 v).trans ?_, fun v => (sand_bd g⁻¹ h2 v).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbD
section
noncomputable section

open UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

theorem pbD : PbD := by
  intro V' V F _ _ _ _ _ _ _ _ q H w p hH hw
  have hr : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  refine ⟨?_, extDeriv_pullback (hw.differentiableAt (by simp)) hH hr⟩
  apply altSmooth V' V' F q (pb H w) p
  intro v
  have h1 : ContDiffAt ℝ ∞ (fun y => w (H y)) p := hw.comp p hH
  have h2 : ∀ i, ContDiffAt ℝ ∞ (fun y => fderiv ℝ H y (v i)) p := fun i =>
    (hH.fderiv_right hinf).clm_apply contDiffAt_const
  have h3 := applySmooth V' V F q (fun y => w (H y)) (fun i y => fderiv ℝ H y (v i)) p h1 h2
  simpa [pb, Function.comp_def] using h3

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullProdDer
section
noncomputable section

open ContinuousAlternatingMap

namespace UpperTheory.V.Lit.Geo

private theorem line_der {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin q]→L[ℝ] F) (h : DifferentiableAt ℝ Ω (p, t)) :
    HasDerivAt (fun r => (Ω (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ))
      ((fderiv ℝ Ω (p, t) (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) t := by
  have h1 : HasDerivAt (fun r : ℝ => (p, r)) ((0 : V), (1 : ℝ)) t := (hasDerivAt_const t p).prodMk (hasDerivAt_id t)
  have h2 : HasDerivAt (fun r : ℝ => Ω (p, r)) (fderiv ℝ Ω (p, t) (0, 1)) t :=
    HasFDerivAt.comp_hasDerivAt t (l := Ω) h.hasFDerivAt h1
  exact (compContinuousLinearMapCLM (ι := Fin q) (F := F) (ContinuousLinearMap.inl ℝ V ℝ)).hasFDerivAt.comp_hasDerivAt t h2

private theorem hasFDerivAt_slice_of_differentiableAt {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin m]→L[ℝ] F)
    (h : DifferentiableAt ℝ Ω (p, t)) :
    HasFDerivAt (fun x : V => Ω (x, t))
      ((fderiv ℝ Ω (p, t)).comp ((ContinuousLinearMap.id ℝ V).prod 0)) p := by
  have hs : HasFDerivAt (fun x : V => ((x, t) : V × ℝ)) ((ContinuousLinearMap.id ℝ V).prod 0) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p)
  exact h.hasFDerivAt.comp p hs

private theorem fderiv_slice_apply_eq_fderiv_prod_inl {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin m]→L[ℝ] F)
    (h : DifferentiableAt ℝ Ω (p, t)) (c : Fin m → V × ℝ) (u : V) :
    fderiv ℝ (fun x : V => Ω (x, t) c) p u = fderiv ℝ Ω (p, t) (u, 0) c := by
  rw [((hasFDerivAt_slice_of_differentiableAt p t Ω h).continuousAlternatingMap_apply_const c).fderiv]
  simp

private theorem removeNth_succ_vecCons' {α : Type*} {n : ℕ} (a : α) (w : Fin (n + 1) → α) (i : Fin (n + 1)) :
    Fin.removeNth i.succ (Matrix.vecCons a w) = Matrix.vecCons a (Fin.removeNth i w) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Fin.removeNth, Fin.succ_succAbove_zero]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

theorem prodDer : ProdDer := by
  intro V F _ _ _ _ p t
  refine ⟨fun Ω h => ?_, fun q Ω h => ?_⟩
  · convert line_der p t Ω h using 1
    ext v
    simp [curryLeft_apply_apply, extDeriv_apply h, fderiv_continuousAlternatingMap_apply_const h]
  · have hβ : DifferentiableAt ℝ
        (fun x => ((Ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) p := by
      have hs := (hasFDerivAt_slice_of_differentiableAt p t Ω h).differentiableAt
      exact ((compContinuousLinearMapCLM (ContinuousLinearMap.inl ℝ V ℝ)).differentiableAt).comp p
        ((((curryLeftLI (𝕜 := ℝ) (E := V × ℝ) (F := F) (n := q)).toContinuousLinearMap.differentiableAt).comp p
          hs).clm_apply (differentiableAt_const _))
    convert line_der p t Ω h using 1
    ext v
    rw [ContinuousAlternatingMap.add_apply, compContinuousLinearMap_apply, curryLeft_apply_apply,
      extDeriv_apply h, Fin.sum_univ_succ, extDeriv_apply hβ]
    have hc : ∀ i : Fin (q + 1), (⇑(ContinuousLinearMap.inl ℝ V ℝ) ∘ Fin.removeNth i v) =
        Fin.removeNth i (⇑(ContinuousLinearMap.inl ℝ V ℝ) ∘ v) := fun i => rfl
    simp only [compContinuousLinearMap_apply, curryLeft_apply_apply, fderiv_slice_apply_eq_fderiv_prod_inl p t Ω h,
      fderiv_continuousAlternatingMap_apply_const h, removeNth_succ_vecCons', hc,
      ContinuousLinearMap.flipAlternating_apply_apply, Matrix.cons_val_succ, Matrix.cons_val_zero,
      Fin.removeNth_zero, Matrix.tail_cons, Fin.tail_cons, Fin.val_succ, Fin.val_zero, pow_zero, one_smul,
      pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, Function.comp_apply,
      ContinuousLinearMap.inl_apply]
    abel

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem retr_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem split_eq (s : {r : ℝ // 0 < r}) :
    splitCentre E a (Real.log s.1 / (a * Module.finrank ℚ E)) = Reduction.centralSection E a s := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Units.ext (Subsingleton.elim _ _)
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [KernelIndexFullLattice.splitEq_holds E a]
  refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log s.2]

private theorem retr_split (g : GA E a) : ∃ t : ℝ, (retractOne g : KernelIndexFullLattice.G1 E a).1 = splitCentre E a t * g :=
  ⟨_, by rw [split_eq (Reduction.detModule E a g)⁻¹, coe_retractOne, ← centralSection_inv_mul_comm, map_inv]⟩

private theorem split_retr (g : GA E a) :
    splitCentre E a (Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)) *
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, split_eq, coe_retractOne, inv_mul_cancel_right]

private theorem cont_inf : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem compact_box (C : ℝ) :
    IsCompact {h : GL (Fin a) (Cinf E) | ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C} := by
  have hB : IsCompact {x : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL x‖ ≤ C} := by
    have h := isCompact_closedBall (0 : Lie E a) C
    have e : Metric.closedBall (0 : Lie E a) C = {x : Lie E a | ‖x‖ ≤ C} := Set.ext fun _ => mem_closedBall_zero_iff
    rw [e] at h
    exact h
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  refine and_congr Iff.rfl ⟨fun hx => ⟨_, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, e⟩
  have e' : y = (x⁻¹).val := MulOpposite.op_injective e
  rwa [e'] at hy

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.retrFacts :
    RetrFacts := by
  intro E _ _ _ a
  refine ⟨retr_split, retr_left, fun C => ?_⟩
  have hc : Continuous fun h : GL (Fin a) (Cinf E) =>
      Real.log (Reduction.detModule E a (infGL E a h)).1 / (a * Module.finrank ℚ E) :=
    ((continuous_subtype_val.comp (Reduction.continuous_detModule.comp cont_inf)).log
      fun h => (Reduction.detModule E a (infGL E a h)).2.ne').div_const _
  obtain ⟨T, hT⟩ := (compact_box (E := E) (a := a) C).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨T, fun g h h1 h2 => ⟨_, hT h ⟨h1, h2⟩, ?_⟩⟩
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, mul_assoc, split_retr]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStepCut
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Geo
open scoped ContDiff Topology

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem cut_chart (Ψ : ℂ → ℂ) (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun h => Ψ (φ h)) g x = Ψ (chart φ g x) := by
  obtain ⟨y, hy⟩ := hx
  obtain rfl : x = toL y.val := hy.symm
  rw [chart_val, chart_val]

private theorem cut_mem {Ψ : ℂ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (φ : Sm E a) : (fun h => Ψ (φ.1 h)) ∈ Sm E a := fun g =>
  (hΨ.comp_contDiffOn (φ.2 g)).congr fun _ hx => cut_chart Ψ φ.1 g hx

private theorem cut_lie {Ψ : ℂ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (φ : Sm E a) (X : Lie E a) (g : GA E a) :
    (lie E a X ⟨_, cut_mem hΨ φ⟩).1 g = fderiv ℝ Ψ (φ.1 g) ((lie E a X φ).1 g) := by
  have hv : chart φ.1 g (oneL E a) = φ.1 g := by simpa using chart_val φ.1 g 1
  rw [← hv]
  change fderiv ℝ (chart (fun h => Ψ (φ.1 h)) g) (oneL E a) X = fderiv ℝ Ψ _ (fderiv ℝ (chart φ.1 g) (oneL E a) X)
  have e : chart (fun h => Ψ (φ.1 h)) g =ᶠ[𝓝 (oneL E a)] Ψ ∘ chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    exact cut_chart Ψ φ.1 g hx
  rw [e.fderiv_eq, fderiv_comp _ (hΨ.differentiable (by simp) _) (differentiableAt_chart φ.2 g)]
  rfl

private theorem cut_unif (φ : Sm E a) (h : BddDer φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : Lie E a) g, ‖(lie E a X φ).1 g‖ ≤ K * ‖X‖ := by
  obtain ⟨K, hK⟩ := banach_steinhaus (g := fun g : GA E a => fderiv ℝ (chart φ.1 g) (oneL E a)) fun X => by
    obtain ⟨C, hC⟩ := h X []
    refine ⟨C, fun g => ?_⟩
    have := hC g
    rw [List.map_singleton, List.prod_singleton] at this
    exact this
  exact ⟨K, (norm_nonneg _).trans (hK 1), fun X g =>
    ((fderiv ℝ (chart φ.1 g) (oneL E a)).le_opNorm X).trans (mul_le_mul_of_nonneg_right (hK g) (norm_nonneg _))⟩

end SlopeTestRemainingChoices

private theorem cut_lip : ∃ M : NNReal, LipschitzWith M Real.smoothTransition := by
  have hs : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    rcases not_and_or.1 hx with h | h
    · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
        (eventually_lt_nhds (not_le.1 h)).mono fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
      rw [e.deriv_eq, deriv_const]
    · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
        (eventually_gt_nhds (not_le.1 h)).mono fun y hy => Real.smoothTransition.one_of_one_le hy.le
      rw [e.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := (hs.continuous_deriv le_rfl).bounded_above_of_compact_support hc
  exact ⟨C.toNNReal, lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (by simp)) fun x => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hC x).trans (Real.le_coe_toNNReal C)⟩

private noncomputable def cutRe (R : ℝ) (z : ℂ) : ℝ := Real.smoothTransition (R + 1 - z.re)

private noncomputable def cutFn (R : ℝ) (z : ℂ) : ℂ := cutRe R z

private theorem cutRe_smooth (R : ℝ) : ContDiff ℝ ∞ (cutRe R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub Complex.reCLM.contDiff)

private theorem cutFn_smooth (R : ℝ) : ContDiff ℝ ∞ (cutFn R) :=
  Complex.ofRealCLM.contDiff.comp (cutRe_smooth R)

private theorem cutFn_der : ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) z, ‖fderiv ℝ (cutFn R) z‖ ≤ M := by
  obtain ⟨M, hM⟩ := cut_lip
  refine ⟨M, M.2, fun R z => norm_fderiv_le_of_lip' ℝ M.2 (Filter.Eventually.of_forall fun w => ?_)⟩
  have h1 := hM.dist_le_mul (R + 1 - w.re) (R + 1 - z.re)
  rw [Real.dist_eq, Real.dist_eq] at h1
  have h2 : |R + 1 - w.re - (R + 1 - z.re)| ≤ ‖w - z‖ := by
    rw [show R + 1 - w.re - (R + 1 - z.re) = -(w - z).re by rw [Complex.sub_re]; ring, abs_neg]
    exact Complex.abs_re_le_norm _
  rw [cutFn, cutFn, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 M.2)

private theorem cutFn_flat (R : ℝ) (z : ℂ) (h : cutRe R z = 0 ∨ cutRe R z = 1) : fderiv ℝ (cutFn R) z = 0 := by
  have h0 : fderiv ℝ (cutRe R) z = 0 := by
    rcases h with h | h
    · exact IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun w => by
        rw [h]; exact Real.smoothTransition.nonneg _)
    · exact IsLocalMax.fderiv_eq_zero (Filter.Eventually.of_forall fun w => by
        rw [h]; exact Real.smoothTransition.le_one _)
  have h1 := (Complex.ofRealCLM.hasFDerivAt.comp z
    ((cutRe_smooth R).differentiable (by simp) z).hasFDerivAt).fderiv
  rw [h0, ContinuousLinearMap.comp_zero] at h1
  exact h1

theorem UpperTheory.V.Lit.Geo.stepCut :
    StepCut := by
  intro E _ _ _ a U f Y C c f₀ H
  obtain ⟨φ, hφ, hb⟩ := H.f_sm
  obtain ⟨K, hK0, hK⟩ := cut_unif φ hb
  obtain ⟨M, hM0, hM⟩ := cutFn_der
  have hc : ∀ t g, f (splitCentre E a t * g) = f g := fun t g => by
    have := H.f_left 1 t g
    rwa [map_one, one_mul] at this
  have hl : ∀ γ g, f (ratGL E a γ * g) = f g := fun γ g => by
    have h1 := H.f_left γ 0 ((splitCentre E a 0)⁻¹ * g)
    have h2 := hc 0 ((splitCentre E a 0)⁻¹ * g)
    rw [mul_assoc, mul_inv_cancel_left] at h1
    rw [mul_inv_cancel_left] at h2
    exact h1.trans h2.symm
  refine ⟨M * K, mul_nonneg hM0 hK0, fun R =>
    ⟨⟨_, cut_mem (cutFn_smooth R) φ⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, fun g => ⟨fun X => ?_, fun hg => ?_, fun hg => ?_⟩⟩⟩
  · intro γ g
    simp only [hφ, hl]
  · intro t g
    simp only [hφ, hc]
  · intro k
    refine Subtype.ext (funext fun g => ?_)
    change cutFn R (φ.1 (g * infGL E a (Unitary.toUnits k))) = cutFn R (φ.1 g)
    rw [hφ, hφ, H.f_cpt]
  · intro k hk
    refine Subtype.ext (funext fun g => ?_)
    change cutFn R (φ.1 (g * finGL E a k)) = cutFn R (φ.1 g)
    rw [hφ, hφ, H.f_lev k hk]
  · intro g
    exact ⟨_, Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _, rfl⟩
  · rw [cut_lie (cutFn_smooth R) φ X g, mul_assoc]
    exact ((fderiv ℝ (cutFn R) _).le_opNorm _).trans (mul_le_mul (hM R _) (hK X g) (norm_nonneg _) hM0)
  · have h1 : cutRe R (φ.1 g) = 1 := by
      rw [hφ, cutRe, Complex.ofReal_re, Real.smoothTransition.one_of_one_le (by linarith)]
    refine ⟨?_, fun X => ?_⟩
    · change cutFn R (φ.1 g) = 1
      rw [cutFn, h1, Complex.ofReal_one]
    · rw [cut_lie (cutFn_smooth R) φ X g, cutFn_flat R _ (Or.inr h1)]
      rfl
  · have h1 : cutRe R (φ.1 g) = 0 := by
      rw [hφ, cutRe, Complex.ofReal_re, Real.smoothTransition.zero_of_nonpos (by linarith)]
    refine ⟨?_, fun X => ?_⟩
    · change cutFn R (φ.1 g) = 0
      rw [cutFn, h1, Complex.ofReal_zero]
    · rw [cut_lie (cutFn_smooth R) φ X g, cutFn_flat R _ (Or.inl h1)]
      rfl
end

