import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorsInDualWeylModule
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.LiftGen

open GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

theorem telescope {n : ℕ} (f : Fin (n + 1) → ℤ) (t : Fin (n + 1)) :
    ∑ i : Fin n, (if t.val < i.val + 1 then f i.castSucc - f i.succ else 0) = f t - f (Fin.last n) := by
  induction n with
  | zero => simp [Fin.eq_zero t, Fin.last]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    induction t using Fin.lastCases with
    | last =>
      rw [Finset.sum_eq_zero, if_neg (by simp)]
      · simp
      · intro i _
        rw [if_neg]
        have := i.isLt
        simp only [Fin.val_last, Fin.val_castSucc]
        omega
    | cast t =>
      have h := ih (fun j => f j.castSucc) t
      have ht := t.isLt
      simp only [Fin.val_castSucc, Fin.succ_castSucc, Fin.val_last, Fin.succ_last] at h ⊢
      rw [h, if_pos (by omega)]
      simp

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

theorem aNum_cast (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (i : Fin n) :
    (aNum lam sg i : ℤ) = sg.w i - lam.w i.succ :=
  Int.toNat_of_nonneg (sub_nonneg.2 (h i).1)

theorem bNum_cast (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (i : Fin n) :
    (bNum lam sg i : ℤ) = lam.w i.castSucc - sg.w i :=
  Int.toNat_of_nonneg (sub_nonneg.2 (h i).2)

theorem sum_ab (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (t : Fin n) :
    ((∑ i : Fin n, (aNum lam sg i * initW n (i.val + 1) t) + ∑ i : Fin n, (bNum lam sg i * initW n (i.val + 1) t) : ℕ) : ℤ)
      = lam.w t.castSucc - lam.w (Fin.last n) := by
  rw [← telescope lam.w t.castSucc, ← Finset.sum_add_distrib, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha := aNum_cast h i
  have hb := bNum_cast h i
  simp only [initW, Fin.val_castSucc]
  split_ifs
  · push_cast; linarith
  · simp

theorem sum_b_succ (b : Fin n → ℕ) (t : Fin n) :
    ∑ i : Fin n, b i * initW n (i.val + 1) t = ∑ i : Fin n, b i * initW n i.val t + b t := by
  have : b t = ∑ i : Fin n, if i = t then b i else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [initW, Fin.ext_iff]
  split_ifs <;> omega

theorem lamN_eq (t : Fin n) : lamN lam t = (lam.w t.castSucc - lam.w (Fin.last n)).toNat := by
  simp only [lamN, DomWeight.natW, DomWeight.detShift, Nat.succ_pos, dif_pos]
  rfl

theorem natW_eq (he : EqualLast lam sg) (t : Fin n) : sg.natW t = (sg.w t - lam.w (Fin.last n)).toNat := by
  have hn : 0 < n := t.pos
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  rw [he ⟨n - 1, by omega⟩ (by simp only; omega)]

theorem shape_lam (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), initW n (i.val + 1)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), initW n (i.val + 1)) = lamN lam := by
  funext t
  have := sum_ab h t
  rw [lamN_eq, ← this, Int.toNat_natCast]
  simp [Finset.sum_apply]

theorem shape_sg (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), initW n (i.val + 1)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), initW n i.val) = sg.natW := by
  funext t
  have h1 := sum_ab h t
  rw [sum_b_succ (bNum lam sg)] at h1
  have hb := bNum_cast h t
  rw [natW_eq he]
  simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Pi.smul_apply]
  omega

theorem shape_b (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ)) = fun s => lamN lam s - sg.natW s := by
  funext t
  have h1 := sum_ab h t
  rw [sum_b_succ (bNum lam sg)] at h1
  have hb := bNum_cast h t
  have h2 : ((∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ))) t = bNum lam sg t := by
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h2, natW_eq he, lamN_eq]
  omega

theorem prod_mem (K : Type) [Field K] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (hg : ∀ k, g k ∈ dualWeyl K r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl K r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (dualWeylMul K r n 0 0 0 0).2
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (dualWeylMul K r n _ _ _ _).1 (hg a) ih

theorem incl_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) (hs' : s ≤ n + 1) :
    incl K n (initMinor K I hs) = initMinor K I hs' := by
  unfold initMinor
  rw [algHom_det_of]
  simp only [incl, rename_X]
  rfl

theorem piGen_mem_and_lift (K : Type) [Field K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) (t : Gen lam sg) :
    piGen K lam sg t ∈ dualWeyl K n n sg.natW ∧
      ∃ G : BP K n, bmLift K n (lamN lam) (fun s => lamN lam s - sg.natW s) (piGen K lam sg t) G ∧
        phiGen K lam sg t = incl K n G := by
  refine ⟨?_, ?_⟩
  · rw [← shape_sg h he]
    exact (dualWeylMul K n n _ _ _ _).1
      (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)
      (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)
  · have h0 := bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ =>
      bmG_prod (Finset.univ : Finset (Fin (aNum lam sg i))) _ _ _ _ fun k _ =>
        bmLift_minor0 K n (t.1 i k) (Nat.succ_le_of_lt i.isLt)
    have h1 := bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ =>
      bmG_prod (Finset.univ : Finset (Fin (bNum lam sg i))) _ _ _ _ fun k _ =>
        bmLift_minor1 K n (t.2 i k) (Nat.succ_le_of_lt i.isLt)
    refine ⟨_, bmG_cast (bmLift_mul h0 h1) (shape_lam h) (shape_b h he) rfl rfl, ?_⟩
    unfold phiGen
    simp only [map_mul, map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
      exact (incl_initMinor K _ _ _).symm
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
      rw [incl_initMinor K _ _ (Nat.succ_le_succ i.isLt.le)]
      refine congrArg (fun I => initMinor K I (Nat.succ_le_succ i.isLt.le)) ?_
      funext p
      induction p using Fin.lastCases with
      | last => simp
      | cast p => simp

end GlobalTheory.BrCompare.LiftGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDiagonalSignatureTracelessBasis
section
noncomputable section

namespace GlobalTheory.SUVol.LieMeasFree

open MeasureTheory Matrix NumberField
open scoped ENNReal
open GlobalTheory.SUVol GlobalTheory.SUVol.DensOne ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.SUVol.LieMeas

theorem riemLie_eq_smul_formLie_of_signs (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (p0 : Ψ → ℕ)
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E) (_hr : 2 ≤ r) (hG : G.det ≠ 0)
    (ho : ∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ))
    (he : ∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0)
    (hli : LinearIndependent (maximalRealSubfield E) e) :
    riemLie Ψ G x = ENNReal.ofReal (Real.sqrt
      ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • formLie Ψ e := by
  classical
  set D : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) with hDdef
  have hD : ∀ τ, D τ * D τ = 1 := by
    intro τ
    rw [hDdef, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext a; unfold sgn; split_ifs <;> simp
  have hDc : ∀ τ, (D τ).map (starRingEnd ℂ) = D τ := by
    intro τ
    rw [hDdef, diagonal_map (map_zero _)]
    congr 1; funext a; simp
  have hxD : ∀ τ, (mat x τ)ᵀ * G.map τ.1 * (mat x τ).map (starRingEnd ℂ) = D τ := fun τ => by
    rw [← gram_eq]; exact ho τ
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ h
    have h1 := congrArg Matrix.det (hxD τ)
    have h2 := congrArg Matrix.det (hD τ)
    rw [det_mul, det_mul, det_transpose, h] at h1
    simp [← h1] at h2
  have hsk : ∀ i, (e i)ᵀ * G + G * (e i).map cc = 0 := fun i => skew_matrix G (he i).2
  have hE : LinearIndependent E e := GlobalTheory.T.real_independent_skew_matrices G hG e hsk hli
  have hR : ∀ τ : Ψ, LinearIndependent ℝ (fun i => (e i).map τ.1) := fun τ => GlobalTheory.T.linear_independent_complex_map τ.1 e hE
  have hmem : ∀ (τ : Ψ) i, ((e i).map τ.1)ᵀ * G.map τ.1 + G.map τ.1 * ((e i).map τ.1).map (starRingEnd ℂ) = 0 ∧
      ((e i).map τ.1).trace = 0 := by
    intro τ i
    refine ⟨map_skew G (hsk i) τ.1, ?_⟩
    have h1 : ((e i).map τ.1).trace = τ.1 (e i).trace := by simp [Matrix.trace, map_sum]
    rw [h1, (he i).1, map_zero]
  have hinj : Function.Injective (coordMap Ψ e) := by
    refine (injective_iff_map_eq_zero (coordMap Ψ e)).2 fun c hc => funext fun τ => funext fun i => ?_
    have h1 := coordMap_apply Ψ e c τ
    rw [hc] at h1
    exact Fintype.linearIndependent_iff.1 (hR τ) (c τ) h1.symm i
  have hsurj : ∀ Z ∈ realLie Ψ G, ∃ c, coordMap Ψ e c = Z := by
    intro Z hZ
    have hX' := (mem_realLie_iff Ψ G Z).1 hZ
    have hspan : ∀ τ : Ψ, Matrix.of (Z τ) ∈ Submodule.span ℝ (Set.range fun i => (e i).map τ.1) :=
      fun τ => GlobalTheory.T.unitary_lie_algebra_spanned (G.map τ.1) (det_map_ne G hG τ.1) _ (hR τ) (hmem τ) _ (hX' τ).1 (hX' τ).2
    choose c hc using fun τ => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan τ)
    refine ⟨c, funext fun τ => ?_⟩
    have h1 := coordMap_apply Ψ e c τ
    rw [hc τ] at h1
    exact h1
  have hin : ∀ c, coordMap Ψ e c ∈ realLie Ψ G := by
    intro c
    refine (mem_realLie_iff Ψ G _).2 fun τ => ?_
    rw [coordMap_apply]
    refine ⟨?_, by simp [trace_sum, (hmem τ _).2]⟩
    have h1 : (∑ i, c τ i • (e i).map τ.1).map (starRingEnd ℂ) =
        ∑ i, c τ i • ((e i).map τ.1).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.sum_apply]
    rw [h1, transpose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hmem τ i).1, smul_zero]
  let f0 : (Ψ → Fin (r ^ 2 - 1) → ℝ) →ₗ[ℝ] (realLie Ψ G).comap (fromFrame x) :=
    ((toFrame x).comp (coordMap Ψ e)).codRestrict _ fun c => by
      change fromFrame x (toFrame x (coordMap Ψ e c)) ∈ realLie Ψ G
      rw [fromFrame_toFrame x hx]; exact hin c
  have hf0 : ∀ c, fromFrame x (f0 c).1 = coordMap Ψ e c := fun c => fromFrame_toFrame x hx _
  have hb : Function.Bijective f0 := by
    refine ⟨fun c d h => hinj (by rw [← hf0, ← hf0, h]), fun Y => ?_⟩
    obtain ⟨c, hc⟩ := hsurj _ Y.2
    refine ⟨c, Subtype.ext ?_⟩
    change toFrame x (coordMap Ψ e c) = Y.1
    rw [hc, toFrame_fromFrame x hx]
  let f := LinearEquiv.ofBijective f0 hb
  let Y : Ψ → Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ := fun τ i => (mat x τ)⁻¹ * (e i).map τ.1 * mat x τ
  have hfY : ∀ τ i σ, Matrix.of (fun a b => (f (Pi.single τ (Pi.single i 1))).1 (σ, a, b)) =
      if σ = τ then Y τ i else 0 := by
    intro τ i σ
    change Matrix.of (fun a b => toFrame x (coordMap Ψ e (Pi.single τ (Pi.single i 1))) (σ, a, b)) = _
    rw [toFrame_apply, coordMap_apply]
    split_ifs with h
    · subst h; simp [Y, Pi.single_apply]
    · simp [h]
  have hgram : (Matrix.of fun p q : Fin (r ^ 2 - 1) × Ψ => inner ℝ (f (Pi.single p.2 (Pi.single p.1 1)))
      (f (Pi.single q.2 (Pi.single q.1 1)))) =
      blockDiagonal fun τ => Matrix.of fun i j => (trace (Y τ i * (Y τ j)ᴴ)).re := by
    ext ⟨i, τ⟩ ⟨j, σ⟩
    rw [Matrix.of_apply, Submodule.coe_inner, inner_eq_sum_trace, blockDiagonal_apply]
    simp only [hfY]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
    by_cases h : τ = σ
    · subst h; simp
    · simp [h]
  have hYli : ∀ τ, LinearIndependent ℝ (Y τ) := by
    intro τ
    refine Fintype.linearIndependent_iff.2 fun g hg => Fintype.linearIndependent_iff.1 (hR τ) g ?_
    have h1 : (mat x τ)⁻¹ * (∑ i, g i • (e i).map τ.1) * mat x τ = 0 := by
      rw [← hg]; simp [Y, Finset.mul_sum, Finset.sum_mul]
    have h2 := congrArg (fun M => mat x τ * M * (mat x τ)⁻¹) h1
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h2
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit] at h2
  have htr : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ), trace ((mat x τ)⁻¹ * M * mat x τ) = trace M := by
    intro τ M
    rw [trace_mul_comm, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hYsk : ∀ τ i, (Y τ i)ᵀ * D τ + D τ * (Y τ i).map (starRingEnd ℂ) = 0 ∧ (Y τ i).trace = 0 := by
    intro τ i
    refine ⟨?_, by rw [htr, (hmem τ i).2]⟩
    have h0 : mat x τ * Y τ i = (e i).map τ.1 * mat x τ := by
      simp only [Y, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
    have h1 := congrArg (fun M => (mat x τ)ᵀ * M * (mat x τ).map (starRingEnd ℂ)) (hmem τ i).1
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
    rw [← hxD τ, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, h0, transpose_mul,
      Matrix.mul_assoc _ ((mat x τ).map _), ← Matrix.map_mul, h0, Matrix.map_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hdetτ : ∀ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      (Matrix.of fun i j => trace (Y τ i * Y τ j)).det := by
    intro τ
    rw [RingHom.map_det]
    congr 1
    ext i j
    have h1 : Y τ i * Y τ j = (mat x τ)⁻¹ * ((e i * e j).map τ.1) * mat x τ := by
      rw [Matrix.map_mul]
      simp only [Y, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
    rw [Matrix.of_apply, h1, htr]
    simp [Matrix.trace, map_sum, Matrix.mul_apply]
  have hcF : Continuous fun Z : (realLie Ψ G).comap (fromFrame x) => fromFrame x Z.1 :=
    (fromFrame x).continuous_of_finiteDimensional.comp continuous_subtype_val
  have hcf : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  unfold riemLie
  rw [volume_eq_sqrt_gram_map f, Measure.map_smul, Measure.map_map hcF.measurable hcf.measurable, hgram,
    det_blockDiagonal, Finset.abs_prod, norm_prod]
  congr 3
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hdetτ, abs_det_re_trace (D τ) (hD τ) (hDc τ) (Y τ) (hYli τ) (hYsk τ)]
  · funext c
    exact hf0 c

end GlobalTheory.SUVol.LieMeasFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionAtIffKottwitzModuleCondi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {S : Scheme.{0}}
  {A : Over S} [GrpObj A] [IsCommMonObj A] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)

theorem spMap_comp_spMap_lieAt {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₂ →+* R₃)
    (g : R₁ →+* R₂) : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem tanScal_iff_lieAt (act : OActN D.O A) (c : 𝓞 D.F) (r : R') (v : epsPtR x ⟶ A) :
    IsTanScal act x (algebraMap (𝓞 D.F) D.O c) r v ↔
      (smT x 0 v = 1 ∧ v ≫ (act.toF D).act c = smT x r v) := by
  have e0 : epsMul (0 : R') = (algebraMap R' (DualNumber R')).comp (TrivSqZeroExt.fstHom R' R' R').toRingHom := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have e1 : ((1 : epsPtR x ⟶ A).left) = spMap (algebraMap R' (DualNumber R')) ≫ (1 : Over.mk x ⟶ A).left := by
    rw [Hom.one_def, Hom.one_def]; rfl
  have e2 : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    rw [spMap_comp_spMap_lieAt]
    have : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (algebraMap R' (DualNumber R')) = RingHom.id R' := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id _
  have t1 : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔
      smT x 0 v = 1 := by
    constructor
    · intro hp
      apply Over.OverMorphism.ext
      rw [smT_left, e1, e0, ← spMap_comp_spMap_lieAt, Category.assoc, hp]
    · intro hp
      have := congrArg (fun V => spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ V.left) hp
      rw [e1, ← Category.assoc, e2, Category.id_comp, smT_left, e0, ← spMap_comp_spMap_lieAt,
        ← Category.assoc, ← Category.assoc, e2, Category.id_comp] at this
      exact this
  have t2 : (v ≫ act.act (algebraMap (𝓞 D.F) D.O c)).left = spMap (epsScaleR r) ≫ v.left ↔
      v ≫ (act.toF D).act c = smT x r v := by
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [smT_left]
      exact h
    · intro h
      have := congrArg (fun V => V.left) h
      rw [smT_left] at this
      exact this
  unfold IsTanScal
  rw [t1, t2]

theorem tv_sum_lieAt {κ : Type} (s : Finset κ) (f : κ → TanM x A) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tv_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, tv_add, ih]

theorem eig_iff_lieAt (act : OActN D.O A) (c : 𝓞 D.F) (r : R') (u : TanM x A) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D) c u = r • u ↔
      tv u ≫ (act.toF D).act c = smT x r (tv u) := by
  constructor
  · intro h
    have := congrArg tv h
    rw [tv_actR, tv_smul] at this
    exact this
  · intro h
    apply tanM_ext
    rw [tv_actR, tv_smul]
    exact h

end

theorem lieAt_iff_lieMod : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S),
    LieAt b act β x ↔
      LieMod (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D)) D.ω (β b.ρ) (fun i => β.comp (b.t i)) := by
  intro p _ D R _ b S A _ _ act R' _ β x
  constructor
  · intro h v hv
    have hv' := (eig_iff_lieAt x act D.ω (β b.ρ) v).1 hv
    obtain ⟨w, hw, hsum⟩ := h (tv v) ((tanScal_iff_lieAt x act D.ω (β b.ρ) (tv v)).2 ⟨tv_mem v, hv'⟩)
    have h0 : ∀ i, smT x 0 (w i) = 1 := fun i => ((tanScal_iff_lieAt x act 0 _ (w i)).1 (hw i 0)).1
    refine ⟨fun i => mkT (w i) (h0 i), fun i => ?_, ?_⟩
    · rw [mem_eigSub]
      intro c
      exact (eig_iff_lieAt x act c _ _).2 ((tanScal_iff_lieAt x act c _ (w i)).1 (hw i c)).2
    · apply tanM_ext
      rw [hsum, tv_sum_lieAt, List.prod_ofFn]
      rfl
  · intro h v hv
    obtain ⟨h0, hω⟩ := (tanScal_iff_lieAt x act D.ω (β b.ρ) v).1 hv
    obtain ⟨w, hw, hsum⟩ := h (mkT v h0) ((eig_iff_lieAt x act D.ω (β b.ρ) (mkT v h0)).2 hω)
    refine ⟨fun i => tv (w i), fun i c => ?_, ?_⟩
    · exact (tanScal_iff_lieAt x act c _ (tv (w i))).2 ⟨tv_mem _, (eig_iff_lieAt x act c _ (w i)).1 ((mem_eigSub.1 (hw i)) c)⟩
    · have := congrArg tv hsum
      rw [tv_mkT, tv_sum_lieAt] at this
      rw [List.prod_ofFn]
      exact this

end GlobalTheory.UPel.HT.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamily
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.LocMatLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem exists_denom (B : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (h : {w | ¬ IntAt w (B w)}.Finite) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ w, IntAt w ((d : K) • B w) := by
  haveI : Finite {w | ¬ IntAt w (B w)} := h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : {w | ¬ IntAt w (B w)} × ι × ι => B p.1.1 p.2.1 p.2.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun w i j => ?_⟩
  by_cases hw : IntAt w (B w)
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one (b : 𝓞 K)) (hw i j)
  · obtain ⟨r, hr⟩ := hb (⟨w, hw⟩, i, j)
    have : ((b : 𝓞 K) : K) • B w i j = algebraMap (𝓞 K) K r := by
      rw [hr]; simp [Algebra.smul_def]
    rw [Matrix.smul_apply, this]
    exact w.valuation_le_one r

omit [DecidableEq ι] in

theorem mulVec_le (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K} (hM : IntAt w M) {x : ι → K}
    (hx : ∀ j, w.valuation K (x j) ≤ 1) (i : ι) : w.valuation K ((M *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i j) (hx j)

theorem isLattice_locLat (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (hA : IsAdelic A) : Submodule.IsLattice K (locLat A) := by
  obtain ⟨hdet, hfin⟩ := hA
  obtain ⟨d, hd0, hd⟩ := exists_denom A (hfin.subset fun w hw h => hw h.1)
  obtain ⟨e, he0, he⟩ := exists_denom (fun w => (A w)⁻¹) (hfin.subset fun w hw h => hw h.2)
  have hdK : (d : K) ≠ 0 := by simpa using hd0
  have heK : (e : K) ≠ 0 := by simpa using he0
  constructor
  · let f : (ι → 𝓞 K) →ₗ[𝓞 K] (ι → K) := (e : K)⁻¹ • (Algebra.linearMap (𝓞 K) K).compLeft ι
    have hf : (LinearMap.range f).FG := by
      rw [← Submodule.map_top]
      exact Submodule.FG.map _ Module.Finite.fg_top
    refine hf.of_le fun x hx => ?_
    have hint : ∀ i, (e : K) * x i ∈ (algebraMap (𝓞 K) K).range := fun i =>
      HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K _ fun w => by
        have h1 := mulVec_le w (he w) (hx w) i
        rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec,
          Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet w)), Matrix.one_mulVec] at h1
        exact h1
    choose y hy using hint
    refine ⟨y, funext fun i => ?_⟩
    change (e : K)⁻¹ * algebraMap (𝓞 K) K (y i) = x i
    rw [hy, inv_mul_cancel_left₀ heK]
  · rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hm : (d : K) • (Pi.basisFun K ι j) ∈ locLat A := fun w i => by
      rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec]
      refine mulVec_le w (hd w) (fun k => ?_) i
      by_cases hk : k = j <;> simp [Pi.single_apply, hk]
    have := Submodule.smul_mem (Submodule.span K (locLat A : Set (ι → K))) (d : K)⁻¹ (Submodule.subset_span hm)
    rwa [inv_smul_smul₀ hdK] at this

end GlobalTheory.LocMatLat
end

