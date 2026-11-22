import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartHessCompare
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyCocycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyCocycleAlt

variable {e : ℕ}

def dens (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : (Fin e → ℂ) → ℝ :=
  maDensity (fun j => hermChartPot (s j))

def pairing (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : ℝ :=
  ∫ y, (hermChartPot X y - hermChartPot Y y) * dens s y

def blocks {α : Type*} (a b c : α) (i j : ℕ) : Fin e → α :=
  fun s => if (s : ℕ) < i then a else if (s : ℕ) < i + j then b else c

theorem blocks_posDef {M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hN : N.PosDef)
    (hP : P.PosDef) (i j : ℕ) (s : Fin e) : (blocks M N P i j s).PosDef := by
  unfold blocks
  split_ifs
  exacts [hM, hN, hP]

theorem update_posDef {T : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hT : ∀ j, (T j).PosDef) (p : Fin e)
    {X : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (s : Fin e) : (Function.update T p X s).PosDef := by
  rw [Function.update_apply]
  split_ifs
  exacts [hX, hT s]

theorem integrable_pairing {X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) :
    Integrable (fun y : Fin e → ℂ => (hermChartPot X y - hermChartPot Y y) * dens s y) := by
  have hCmp := HermFormCompare.proof
  have hHess := ChartHessCompare.proof hCmp
  choose C hC using fun j => hHess e (s j) Y (hs j) hY
  obtain ⟨C₀, hC₀⟩ := hHess e Y Y hY hY
  obtain ⟨K, hK⟩ := ChartEnergyIntegrableAlt.pot_sub_bound hCmp hX hY
  set C' : ℝ := 1 + ∑ j, |C j| with hC'
  have hCj : ∀ j, C j ≤ C' := fun j => by
    have h1 := Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 := le_abs_self (C j)
    linarith
  have hbound : ∀ y, ‖dens s y‖ ≤ C' ^ e * maDensity (fun _ : Fin e => hermChartPot Y) y := by
    intro y
    set HN := cxHessian (hermChartPot Y) y with hHN
    set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (hermChartPot (s j)) y with hAdef
    set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((C' : ℝ) : ℂ) • HN with hBdef
    have hNp : HN.PosSemidef := (hC₀ y).1.posSemidef
    have hApsd : ∀ j, (A j).PosSemidef := fun j => (hC j y).1.posSemidef
    have hAB : ∀ j, (B j - A j).PosSemidef := fun j => by
      have h : ((C' : ℝ) : ℂ) • HN - A j = (((C j : ℝ) : ℂ) • HN - A j) + (((C' - C j : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul]
        abel
      show (((C' : ℝ) : ℂ) • HN - A j).PosSemidef
      rw [h]
      exact (hC j y).2.add (hNp.smul (Complex.zero_le_real.2 (sub_nonneg.2 (hCj j))))
    have hmono : (mixedDisc A).re ≤ (mixedDisc B).re := ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB
    have hnn : 0 ≤ (mixedDisc A).re := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2
    have hB : mixedDisc B = ((C' : ℝ) : ℂ) ^ e * HN.det := by
      have h := ReciprocityTheory.AnForm.A.mdisc_const (((C' : ℝ) : ℂ) • HN)
      rw [det_smul, Fintype.card_fin] at h
      exact h
    have hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det := ReciprocityTheory.AnForm.A.mdisc_const HN
    have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
    have hd : dens s y = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re := rfl
    have hd0 : maDensity (fun _ : Fin e => hermChartPot Y) y =
        (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc (fun _ : Fin e => HN)).re := rfl
    rw [hd, hd0, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]
    rw [hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmono
    calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re
        ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (C' ^ e * HN.det.re) :=
          mul_le_mul_of_nonneg_left hmono hc
      _ = _ := by ring
  have hmeas : Measurable (dens s) := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _
  have hmix : Integrable (dens s) :=
    Integrable.mono' ((ChartDensityIntegrable.proof e Y hY).const_mul (C' ^ e)) hmeas.aestronglyMeasurable
      (Eventually.of_forall hbound)
  exact hmix.bdd_mul ((ChartEnergyIntegrableAlt.measurable_hermChartPot X).sub
    (ChartEnergyIntegrableAlt.measurable_hermChartPot Y)).aestronglyMeasurable (Eventually.of_forall hK)

theorem pairing_add {X Y Z : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef) (hZ : Z.PosDef)
    {s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) :
    pairing X Z s = pairing X Y s + pairing Y Z s := by
  unfold pairing
  rw [← integral_add (integrable_pairing hX hY hs) (integrable_pairing hY hZ hs)]
  congr 1
  funext y
  ring

theorem pairing_sub {X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {s t : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) (ht : ∀ j, (t j).PosDef) :
    pairing X Y s - pairing X Y t = ∫ y, (hermChartPot X y - hermChartPot Y y) * (dens s y - dens t y) := by
  unfold pairing
  rw [← integral_sub (integrable_pairing hX hY hs) (integrable_pairing hX hY ht)]
  congr 1
  funext y
  ring

theorem pairing_perm (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (σ : Equiv.Perm (Fin e)) : pairing X Y (s ∘ σ) = pairing X Y s := by
  unfold pairing
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [dens]
  rw [show (fun j => hermChartPot ((s ∘ σ) j)) = (fun j => hermChartPot (s j)) ∘ σ from rfl,
    Inter.maDensity_comp_perm]

theorem step (hS : ChartEnergySymm.Statement) {M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef)
    (hN : N.PosDef) (hP : P.PosDef) {k j : ℕ} (h : k + j < e) :
    pairing M N (blocks M N P k j) - pairing M N (blocks M N P k (j + 1)) =
      -(pairing N P (blocks M N P (k + 1) j) - pairing N P (blocks M N P k (j + 1))) := by
  obtain ⟨p, hpv⟩ : ∃ p : Fin e, (p : ℕ) = k + j := ⟨⟨k + j, h⟩, rfl⟩
  obtain ⟨q, hqv⟩ : ∃ q : Fin e, (q : ℕ) = k := ⟨⟨k, by omega⟩, rfl⟩
  set T := blocks M N P k (j + 1) with hTdef
  have hT : ∀ s, (T s).PosDef := blocks_posDef hM hN hP k (j + 1)
  have hTP : Function.update T p P = blocks M N P k j := by
    funext s
    simp only [Function.update_apply, hTdef, blocks, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  have hTN : Function.update T p N = T := by
    funext s
    simp only [Function.update_apply, hTdef, blocks, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  have key : ∀ s : Fin e, ((Equiv.swap q p s : Fin e) : ℕ) =
      if (s : ℕ) = k then k + j else if (s : ℕ) = k + j then k else s := by
    intro s
    rw [Equiv.swap_apply_def]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> omega
  have hTM : Function.update T p M ∘ Equiv.swap q p = blocks M N P (k + 1) j := by
    funext s
    simp only [Function.comp_apply, Function.update_apply, hTdef, blocks, Fin.ext_iff, key]
    split_ifs <;> first | rfl | omega
  have hsym := hS e M N N P T p hM hN hN hP hT
  have e1 : pairing M N (Function.update T p N) - pairing M N (Function.update T p P) =
      pairing N P (Function.update T p M) - pairing N P (Function.update T p N) := by
    rw [pairing_sub hM hN (update_posDef hT p hN) (update_posDef hT p hP),
      pairing_sub hN hP (update_posDef hT p hM) (update_posDef hT p hN)]
    exact hsym
  rw [← pairing_perm N P (Function.update T p M) (Equiv.swap q p), hTM, hTP, hTN] at e1
  linarith

theorem antidiag_telescope (g : ℕ → ℕ → ℝ) : ∀ e : ℕ,
    ∑ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) =
      ∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k)
  | 0 => by simp
  | e + 1 => by
    have ih := antidiag_telescope g e
    have h1 : ∀ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e + 1 - k), (g (k + 1) j - g k (j + 1)) =
        ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) + (g (k + 1) (e - k) - g k (e - k + 1)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show e + 1 - k = e - k + 1 by omega, Finset.sum_range_succ]
    have h2 : ∑ k ∈ Finset.range (e + 1), (g (k + 1) (e - k) - g k (e - k + 1)) = g (e + 1) 0 - g 0 (e + 1) := by
      have h3 := Finset.sum_range_sub (fun k => g k (e + 1 - k)) (e + 1)
      simp only [Nat.sub_self, Nat.sub_zero] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show e + 1 - (k + 1) = e - k by omega, show e + 1 - k = e - k + 1 by omega]
    rw [Finset.sum_range_succ _ (e + 1), Finset.sum_range_succ (fun k => g k 0 - g 0 k) (e + 1), ← ih,
      Nat.sub_self, Finset.sum_range_zero, add_zero, Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]

theorem chartMixedEnergy_eq (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) :
    chartMixedEnergy X Y k = pairing X Y (fun s : Fin e => if (s : ℕ) < k then X else Y) := by
  unfold chartMixedEnergy pairing dens
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  congr 2
  funext j
  by_cases h : (j : ℕ) < k <;> simp [h]

end ChartEnergyCocycleAlt

open ChartEnergyCocycleAlt in

theorem ChartEnergyCocycle.proof (hS : ChartEnergySymm.Statement) : ChartEnergyCocycle.Statement := by
  intro e M N P hM hN hP
  have hb := blocks_posDef hM hN hP
  set g : ℕ → ℕ → ℝ := fun i j => pairing N P (blocks M N P i j) with hg
  have e1 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy M P k =
      pairing M N (blocks M N P k 0) + g k 0 := by
    intro k _
    rw [chartMixedEnergy_eq, hg]
    have : (fun s : Fin e => if (s : ℕ) < k then M else P) = blocks M N P k 0 := by
      funext s
      simp only [blocks, add_zero]
      split_ifs <;> rfl
    rw [this]
    exact pairing_add hM hN hP (hb k 0)
  have e2 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy M N k = pairing M N (blocks M N P k (e - k)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [chartMixedEnergy_eq]
    congr 1
    funext s
    have := s.isLt
    simp only [blocks]
    split_ifs <;> first | rfl | omega
  have e3 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy N P k = g 0 k := by
    intro k _
    rw [chartMixedEnergy_eq, hg]
    congr 1
    funext s
    simp only [blocks, zero_add]
    split_ifs <;> first | rfl | omega
  have tele : ∀ k ∈ Finset.range (e + 1),
      pairing M N (blocks M N P k 0) - pairing M N (blocks M N P k (e - k)) =
        -∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← Finset.sum_range_sub' (fun j => pairing M N (blocks M N P k j)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact step hS hM hN hP (by omega)
  have hsum : ∑ k ∈ Finset.range (e + 1), (pairing M N (blocks M N P k 0) -
      pairing M N (blocks M N P k (e - k))) = -∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k) := by
    rw [Finset.sum_congr rfl tele, Finset.sum_neg_distrib, antidiag_telescope]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib] at hsum
  linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualLineSemipositiveAlt

open scoped MatrixOrder in

theorem exists_conjTranspose_mul_self {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : ∃ B : Matrix n n ℂ, M = Bᴴ * B := by
  have h0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  refine ⟨CFC.sqrt M, ?_⟩
  rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self M h0]

theorem re_star_dotProduct_mulVec {n : Type} [Fintype n] (B : Matrix n n ℂ) (w : n → ℂ) :
    (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re = ∑ j, ‖(B *ᵥ w) j‖ ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def factor (F : HermLattice K i) (σ : K →+* ℂ) : Matrix (Fin i) (Fin i) ℂ :=
  Classical.choose (exists_conjTranspose_mul_self (F.posDef σ).posSemidef)

theorem factor_spec (F : HermLattice K i) (σ : K →+* ℂ) :
    F.metric σ = (factor F σ)ᴴ * factor F σ :=
  Classical.choose_spec (exists_conjTranspose_mul_self (F.posDef σ).posSemidef)

def coordMap {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    ((Σ _ : Unit, T) → ℂ) →ₗ[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
  (LinearMap.pi fun p : (K →+* ℂ) × Fin i => (LinearMap.proj p.2) ∘ₗ (factor F p.1).mulVecLin ∘ₗ
      (LinearMap.pi fun k => LinearMap.proj (p.1, k))) ∘ₗ (dualRecover b hb).toLinearMap ∘ₗ
    (LinearMap.pi fun t => LinearMap.proj (⟨(), t⟩ : Σ _ : Unit, T))

omit [Fintype T] [DecidableEq T] in

theorem dualLine_h_eq {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) :
    (dualLine F b hb).h z = (fsMetric ((K →+* ℂ) × Fin i)).ρ (coordMap b hb z) := by
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = ‖WithLp.toLp 2 (coordMap b hb z)‖
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [dualNormSq]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [factor_spec F σ, re_star_dotProduct_mulVec]
  rfl

end DualLineSemipositiveAlt

open DualLineSemipositiveAlt in

theorem DualLineSemipositive.proof : DualLineSemipositive.Statement := by
  intro K _ _ i F T _ _ b hb
  set τc : ((Σ _ : Unit, T) → ℂ) →L[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
    LinearMap.toContinuousLinearMap (coordMap b hb) with hτc
  have hh : ∀ z, (dualLine F b hb).h z = (fsMetric ((K →+* ℂ) × Fin i)).ρ (τc z) :=
    dualLine_h_eq b hb
  have hne : ∀ z : (Σ _ : Unit, T) → ℂ, (∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) → τc z ≠ 0 := by
    intro z hz h0
    have hp := (dualLine F b hb).pos z hz
    rw [hh, h0] at hp
    simp [fsMetric] at hp
  have hfun : (dualLine F b hb).h = (fsMetric ((K →+* ℂ) × Fin i)).ρ ∘ τc := funext hh
  refine ⟨?_, fun z hz w _ => ?_⟩
  · intro z hz
    rw [hfun]
    exact ((HilbertSamuel.ProjLine.isSmoothMetric_fs.contDiffAt (isOpen_ne.mem_nhds (hne z hz))).comp z
      (τc.restrictScalars ℝ).contDiff.contDiffAt).contDiffWithinAt
  · change 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log ((dualLine F b hb).h z)) z w
    have hlog : (fun z => Real.log ((dualLine F b hb).h z)) =
        (fun u => Real.log ((fsMetric ((K →+* ℂ) × Fin i)).ρ u)) ∘ τc := by
      funext y
      simp only [Function.comp_apply, hh]
    rw [hlog, ReciprocityTheory.AnForm.levi_comp w (τc.analyticAt z)
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id HilbertSamuel.ProjLine.isSmoothMetric_fs
        (hne z hz.1))]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (hne z hz.1) _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace FubiniStudyLeviForm

variable {ι : Type} [Fintype ι]

theorem levi_sum_nonneg {K : Type} {z : ι → ℂ} (f : K → (ι → ℂ) → ℝ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (hl : ∀ k w, 0 ≤ ReciprocityTheory.AnForm.levi (f k) z w)
    (w : ι → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, f k y) z ∧
      0 ≤ ReciprocityTheory.AnForm.levi (fun y => ∑ k ∈ s, f k y) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using contDiffAt_const, by simp [ReciprocityTheory.AnForm.levi]⟩
  | insert a s ha ih =>
    have heq : (fun y => ∑ k ∈ insert a s, f k y) =
        fun y => (fun y' => ∑ k ∈ s, f k y') y + 1 * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩
    rw [ReciprocityTheory.AnForm.levi_add_smul (f := fun y' => ∑ k ∈ s, f k y') (g := f a) 1 ih.1 (hf a) w]
    have h1 := hl a w
    have h2 := ih.2
    linarith

noncomputable def blockProj {K : Type} (ι : K → Type) (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩

end FubiniStudyLeviForm

open FubiniStudyLeviForm in

theorem FsLineLevi.proof : FsLineLevi.Statement := by
  intro K _ ι _ z w hz
  classical
  set F : K → ((Σ k, ι k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsMulti ι).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hpos : ∀ k, 0 < (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact (fsMetric (ι k)).pos _ fun h0 => hi (congrFun h0 i)
    simp only [fsMulti, HermLine.ofMetrics, zpow_one, hF]
    exact Real.log_prod fun k _ => (hpos k).ne'
  have hblock : ∀ k, ContDiffAt ℝ 2 (F k) z ∧ ∀ v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v := by
    intro k
    have hk0 : (fun i => z ⟨k, i⟩) ≠ 0 := by
      obtain ⟨i, hi⟩ := hz k
      exact fun h0 => hi (congrFun h0 i)
    have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
      (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) hk0
    have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blockProj ι k := rfl
    refine ⟨hFk ▸ hφ.comp z ((blockProj ι k).restrictScalars ℝ).contDiff.contDiffAt, fun v => ?_⟩
    rw [hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj ι k).analyticAt z) hφ]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hk0 _
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev]
  exact (levi_sum_nonneg F (fun k => (hblock k).1) (fun k => (hblock k).2) w Finset.univ).2

end GroundTheory.Heights₂.Heights
end

