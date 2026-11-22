import Formalism.LocalToGlobal.AlgebraicTheory.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaAdditiveHomogeneousHomothety
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LinearSubstitutionDiagonal
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

-- bundled from Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.JetsInOfOneVariable
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.G (linSub JetsIn JetsIn1)
open Formalism.DworkPowerSeriesWeights (JetsIntegral mfact)
open Formalism.InvariantFactorPaths.G7 (at1)

namespace LinearSubstitutionJets

private theorem sum_C_scl_mul_X {K : Type} [Field K] {p : Type} [Fintype p] [DecidableEq p] (c : K)
    (x : p) :
    (∑ y, MvPowerSeries.C (scl p c x y) * MvPowerSeries.X y : MvPowerSeries p K) =
      MvPowerSeries.C c * MvPowerSeries.X x := by
  rw [Finset.sum_eq_single x]
  · simp [scl]
  · intro y _ hy
    simp [scl, Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

theorem linSub_scl {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] (c : K)
    (f : MvPowerSeries n K) :
    linSub (scl n c) f = MvPowerSeries.rescale (fun _ => c) f := by
  unfold linSub
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext i
  rw [sum_C_scl_mul_X]
  simp [MvPowerSeries.smul_eq_C_mul]

end LinearSubstitutionJets

open LinearSubstitutionJets

theorem product_scaling_jets : ProdScaleJets := by
  intro K _ _ κ n _ _ _ c r H hr hH
  classical
  have hB : ∀ a : K, a ∈ Formalism.G.unitBall K ↔ ‖a‖ ≤ 1 := fun a => Iff.rfl
  refine (Formalism.L2.Th1.G.jetsInNorm K n _).mpr ?_
  rw [linSub_scl]
  obtain ⟨hC, -, hadd, -, hmul⟩ := Formalism.L2.Th1.G.jetsRing K (Formalism.G.unitBall K) n

  have hfac : ∀ k i, JetsIn (Formalism.G.unitBall K)
      (MvPowerSeries.rescale (fun _ => c) (at1 i (H k i) : MvPowerSeries n K)) := by
    intro k i κ'
    rw [MvPowerSeries.coeff_rescale]
    unfold at1
    rw [PowerSeries.coeff_subst_single, hB]
    split_ifs with h
    · have hm : mfact κ' = (κ' i).factorial := by
        conv_lhs => rw [h]
        rw [mfact, Finsupp.prod_single_index (by simp)]
      have hp : (κ'.prod fun _ m => c ^ m) = c ^ (κ' i) := by
        conv_lhs => rw [h]
        rw [Finsupp.prod_single_index (by simp)]
      rw [hm, hp]
      calc ‖((κ' i).factorial : K) * (c ^ κ' i * PowerSeries.coeff (κ' i) (H k i))‖
          = ‖((κ' i).factorial : K) * PowerSeries.coeff (κ' i) (H k i)‖ * ‖c‖ ^ κ' i := by
            rw [norm_mul, norm_mul, norm_mul, norm_pow]
            ring
        _ ≤ 1 := hH k i (κ' i)
    · simp
  have hCr : ∀ k, JetsIn (Formalism.G.unitBall K)
      (MvPowerSeries.rescale (fun _ => c) (MvPowerSeries.C (r k) : MvPowerSeries n K)) := by
    intro k
    have hres : MvPowerSeries.rescale (fun _ => c) (MvPowerSeries.C (r k) : MvPowerSeries n K) =
        MvPowerSeries.C (r k) := by
      ext κ'
      rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
      split_ifs with h
      · subst h
        simp
      · rw [mul_zero]
    rw [hres]
    exact hC _ ((hB _).mpr (hr k))
  unfold Formalism.L2.Th1.E.thetaProd
  rw [map_sum]
  refine Finset.sum_induction _ (JetsIn (Formalism.G.unitBall K)) (fun f g hf hg => hadd f g hf hg) ?_ ?_
  · simpa using hC 0 (Formalism.G.unitBall K).zero_mem
  · intro k _
    rw [map_mul, map_prod]
    exact hmul _ _ (hCr k)
      (Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_prod Formalism.L2.Th1.G.jetsRing _ _ _ fun i _ => hfac k i)

theorem linear_scaling_jets : LinScale := by
  intro K _ n m _ _ _ _ c A f
  have hS : ∀ {p q : Type} [Fintype p] [Fintype q] (B : p → q → K),
      MvPowerSeries.HasSubst
        (fun i => (∑ x, MvPowerSeries.C (B i x) * MvPowerSeries.X x : MvPowerSeries q K)) := by
    intro p q _ _ B
    exact Formalism.L2.Th1.G.hasSubst_lin B
  constructor
  · unfold linSub
    rw [MvPowerSeries.subst_comp_subst_apply (hS A) (hS (scl m c))]
    congr 1
    funext i
    show linSub (scl m c) (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) = _
    rw [← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_mul, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSubHom_apply,
      Formalism.L2.Th1.G.linSub_C, Formalism.L2.Th1.G.linSub_X, sum_C_scl_mul_X, map_mul]
    ring
  · unfold linSub
    rw [MvPowerSeries.subst_comp_subst_apply (hS (scl n c)) (hS A)]
    congr 1
    funext i
    rw [sum_C_scl_mul_X]
    show linSub A (MvPowerSeries.C c * MvPowerSeries.X i) = _
    rw [← Formalism.L2.Th1.G.linSubHom_apply, map_mul, Formalism.L2.Th1.G.linSubHom_apply,
      Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSub_C, Formalism.L2.Th1.G.linSub_X, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_mul]
    ring

end Formalism.L2.AlgTh
end
end

-- bundled from Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.KernelIndexForm
section
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (IsReps opU sumU fixedBy semicharacterHom)
open Formalism.L2.Col (Fields Sp HomE IsSdLat)
open Formalism.L2.Ker (Amb VCx LamC BC AC HV alV embH volC repsOf xiInd xiS hatS indL)

theorem kernel_index_form : KerIndForm := by
  intro X A a b S N N' c x hN hN' hLa hc hvol m₁ m₂ hcop hkill S₁ S₂ h1 h2 z
  classical
  obtain ⟨-, -, -, -, hall⟩ := Formalism.L2.Ker.heisHyp_of A a b S hLa
  obtain ⟨hfix, hcc⟩ := hall N N' hN hN'
  obtain ⟨hsplit, hi1, hi2, -⟩ := hcc c hc
  obtain ⟨hH, -, hB, -, -, -⟩ := hsplit
  have hSA := Formalism.L2.Ker.repsOf_spec _ _ hi1
  have hSB := Formalism.L2.Ker.repsOf_spec _ _ hi2
  set H : Formalism.L2.Th1.H.Sesq (VCx X.Tau a b) := HV A.sc with hHdef
  set α : VCx X.Tau a b → ℂ := alV A.d A.sc with hαdef
  set Λ := LamC (X.embC A.σ₀) A.δ A.AA N N' with hΛdef
  set B := BC (X.embC A.σ₀) A.δ A.AA S N N' c with hBdef
  set SA := repsOf B (Λ ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c) with hSAdef
  set SB := repsOf Λ B with hSBdef
  set e := A.e a b N N' with hedef
  set s := embH (X.embC A.σ₀) A.δ (A.liftW S N N' c x) with hsdef
  set vol := volC A.AA S N N' with hvoldef

  have hsplitSum : ∀ w, (∑ y ∈ SB, α y * opU H y e w) = ∑ y ∈ S₁, α y * opU H y (sumU H α S₂ e) w := by
    intro w
    obtain ⟨hI, hinj⟩ := KerA.image_reps B Λ m₁ m₂ hcop hkill S₁ S₂ h1 h2
    have hinv : ∀ x ∈ B, ∀ m ∈ B, m ∈ Λ → α (x + m) * opU H (x + m) e w = α x * opU H x e w := by
      intro x hx m hmB hmΛ
      rw [← semicharacterHom _ H hH B α hB x hx m hmB e w]
      congr 2
      funext v
      exact hfix m hmΛ v
    rw [Formalism.L2.Ker.sum_reps_eq hSB hI (fun y => α y * opU H y e w) hinv,
      Finset.sum_image (fun q hq q' hq' h => hinj hq hq' h), Finset.sum_product]
    refine Finset.sum_congr rfl fun y₁ hy₁ => ?_
    have hsU : sumU H α S₂ e = fun v => ∑ y₂ ∈ S₂, α y₂ * opU H y₂ e v := rfl
    rw [hsU, Formalism.L2.Th1.H.Inv.opU_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y₂ hy₂ => ?_
    have hy₁B : y₁ ∈ B := (KerA.mem_killIn.1 (h1.1 y₁ hy₁)).1
    have hy₂B : y₂ ∈ B := (KerA.mem_killIn.1 (h2.1 y₂ hy₂)).1
    exact (semicharacterHom _ H hH B α hB y₁ hy₁B y₂ hy₂B e w).symm

  have hxiS : xiS H α vol SA SB (indL B) e =
      fun w => (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ))) * ∑ y ∈ SB, α y * opU H y e w := by
    funext w
    simp only [xiS, sumU]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Formalism.L2.Ker.hatS_ind H hH α B _ hB vol SA hSA (hSB.1 y hy)]
    ring
  have hth : A.thInd S N N' c x z = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiInd H α vol B SA SB e s z := rfl
  rw [hth]
  simp only [xiInd]
  rw [hxiS, Formalism.L2.Th1.H.Inv.opU_const_mul]
  have hF : (fun w => ∑ y ∈ SB, α y * opU H y e w) = fun w => ∑ y ∈ S₁, α y * opU H y (sumU H α S₂ e) w :=
    funext hsplitSum
  rw [hF, Formalism.L2.Th1.H.Inv.opU_finset_sum]
  have hT : ∑ i ∈ S₁, opU H (-s) (fun w => α i * opU H i (sumU H α S₂ e) w) z =
      ∑ y ∈ S₁, α y * opU H (-s) (opU H y (sumU H α S₂ e)) z := by
    refine Finset.sum_congr rfl fun y _ => ?_
    exact Formalism.L2.Th1.H.Inv.opU_const_mul H (-s) (α y) _ z
  rw [hT]
  set T := ∑ y ∈ S₁, α y * opU H (-s) (opU H y (sumU H α S₂ e)) z
  set r : ℂ := ((Real.sqrt vol : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by
    rw [hr]; exact_mod_cast (Real.sqrt_pos.2 hvol).ne'
  have hrr : r * r = ((vol : ℝ) : ℂ) := by
    rw [hr, ← Complex.ofReal_mul, Real.mul_self_sqrt hvol.le]
  have h1' : r⁻¹ * (α s * (r⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * T)) =
      (r⁻¹ * r⁻¹ * (r * r)) * ((SA.card : ℂ)⁻¹ * α s * T) := by
    rw [hrr]; ring
  have h2' : r⁻¹ * r⁻¹ * (r * r) = 1 := by field_simp
  rw [h1', h2', one_mul]

end Formalism.L2.AlgTh
end
end

