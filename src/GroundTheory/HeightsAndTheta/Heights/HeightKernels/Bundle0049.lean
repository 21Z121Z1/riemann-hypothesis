import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0048

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyIntegrableAlt

theorem quad_pos {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (y : Fin e → ℂ) :
    0 < (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re := by
  have hx : (Fin.cons 1 y : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
    have := congr_fun h 0
    simp at this
  exact hM.re_dotProduct_pos hx

theorem measurable_hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    Measurable (hermChartPot M) := by
  have hz : Continuous fun y : Fin e → ℂ => (Fin.cons 1 y : Fin (e + 1) → ℂ) :=
    continuous_const.finCons continuous_id
  have hc : Continuous fun y : Fin e → ℂ =>
      star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) :=
    hz.star.dotProduct (continuous_const.matrix_mulVec hz)
  exact Real.measurable_log.comp (Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp hc.measurable))

theorem pot_sub_bound (hCmp : HermFormCompare.Statement) {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hM : M.PosDef) (hN : N.PosDef) :
    ∃ K : ℝ, ∀ y : Fin e → ℂ, ‖hermChartPot M y - hermChartPot N y‖ ≤ K := by
  obtain ⟨c, hc, h1⟩ := hCmp _ M N hM hN
  obtain ⟨c', hc', h2⟩ := hCmp _ N M hN hM
  refine ⟨|Real.log c| + |Real.log c'|, fun y => ?_⟩
  have hqM := quad_pos hM y
  have hqN := quad_pos hN y
  have a1 := Real.log_le_log hqM (h1 (Fin.cons 1 y))
  have a2 := Real.log_le_log hqN (h2 (Fin.cons 1 y))
  rw [Real.log_mul hc.ne' hqN.ne'] at a1
  rw [Real.log_mul hc'.ne' hqM.ne'] at a2
  simp only [hermChartPot, Real.log_sqrt hqM.le, Real.log_sqrt hqN.le, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log c), le_abs_self (Real.log c'), abs_nonneg (Real.log c),
    abs_nonneg (Real.log c')]

theorem abs_maDensity_mix_le {e : ℕ} {M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (k : ℕ) (C : ℝ) (y : Fin e → ℂ)
    (hMp : (cxHessian (hermChartPot M) y).PosSemidef) (hNp : (cxHessian (hermChartPot N) y).PosSemidef)
    (hle : ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef) :
    ‖maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y‖ ≤
      max C 1 ^ e * maDensity (fun _ : Fin e => hermChartPot N) y := by
  set HM := cxHessian (hermChartPot M) y
  set HN := cxHessian (hermChartPot N) y
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => if (j : ℕ) < k then HM else HN with hAdef
  have hA : (fun j : Fin e => cxHessian (if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) = A := by
    funext j
    simp only [hAdef]
    split_ifs <;> rfl
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((max C 1 : ℝ) : ℂ) • HN with hBdef
  have hApsd : ∀ j, (A j).PosSemidef := fun j => by
    simp only [hAdef]
    split_ifs
    · exact hMp
    · exact hNp
  have hsm : ∀ r : ℝ, 0 ≤ r → (((r : ℝ) : ℂ) • HN).PosSemidef := fun r hr =>
    hNp.smul (Complex.zero_le_real.2 hr)
  have hAB : ∀ j, (B j - A j).PosSemidef := fun j => by
    simp only [hBdef, hAdef]
    split_ifs
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HM = ((C : ℂ) • HN - HM) + (((max C 1 - C : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul]
        abel
      rw [h]
      exact hle.add (hsm _ (sub_nonneg.2 (le_max_left C 1)))
    · have h : ((max C 1 : ℝ) : ℂ) • HN - HN = (((max C 1 - 1 : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul, one_smul]
      rw [h]
      exact hsm _ (sub_nonneg.2 (le_max_right C 1))
  have hmono : (mixedDisc A).re ≤ (mixedDisc B).re := ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB
  have hnn : 0 ≤ (mixedDisc A).re := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2
  have hB : mixedDisc B = ((max C 1 : ℝ) : ℂ) ^ e * HN.det := by
    have h := ReciprocityTheory.AnForm.A.mdisc_const (((max C 1 : ℝ) : ℂ) • HN)
    rw [det_smul, Fintype.card_fin] at h
    exact h
  have hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det := ReciprocityTheory.AnForm.A.mdisc_const HN
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [hA, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]
  rw [hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmono
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (max C 1 ^ e * HN.det.re) :=
        mul_le_mul_of_nonneg_left hmono hc
    _ = _ := by ring

end ChartEnergyIntegrableAlt

open ChartEnergyIntegrableAlt in

theorem ChartEnergyIntegrable.proof (hCmp : HermFormCompare.Statement) (hHess : ChartHessCompare.Statement) :
    ChartEnergyIntegrable.Statement := by
  intro e M N hM hN k
  obtain ⟨C, hC⟩ := hHess e M N hM hN
  obtain ⟨C₀, hC₀⟩ := hHess e N N hN hN
  obtain ⟨K, hK⟩ := pot_sub_bound hCmp hM hN
  have hmix : Integrable (fun y : Fin e → ℂ =>
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y) := by
    refine Integrable.mono' ((ChartDensityIntegrable.proof e N hN).const_mul (max C 1 ^ e))
      (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    exact abs_maDensity_mix_le k C y (hC y).1.posSemidef (hC₀ y).1.posSemidef (hC y).2
  exact hmix.bdd_mul ((measurable_hermChartPot M).sub (measurable_hermChartPot N)).aestronglyMeasurable
    (Eventually.of_forall hK)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCotangentKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualCotangentKernel

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem smul_mem (F : HermLattice K i) (μ : 𝓞 K) {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    (algebraMap (𝓞 K) K μ) • φ ∈ dualLattice F := by
  intro x hx
  rw [smul_dotProduct, smul_eq_mul]
  obtain ⟨r, hr⟩ := hφ x hx
  exact ⟨μ * r, by rw [map_mul, hr]⟩

def mulMap (F : HermLattice K i) (c : 𝓞 K) : dualLattice F →ₗ[ℤ] dualLattice F where
  toFun χ := ⟨algebraMap (𝓞 K) K c • (χ : Fin i → K), smul_mem F c χ.2⟩
  map_add' χ χ' := by ext1; simp [smul_add]
  map_smul' n χ := by
    ext1
    show algebraMap (𝓞 K) K c • ((n • χ : dualLattice F) : Fin i → K) =
      n • (algebraMap (𝓞 K) K c • (χ : Fin i → K))
    rw [Submodule.coe_smul, smul_comm]

def prodSet (F : HermLattice K i) {k : Type} [Field k] (ρ : 𝓞 K →+* k) : Set (dualLattice F) :=
  {v | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
    (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

theorem mulMap_mem (F : HermLattice K i) {k : Type} [Field k] (ρ : 𝓞 K →+* k) (c : 𝓞 K)
    {χ : dualLattice F} (hχ : χ ∈ Submodule.span ℤ (prodSet F ρ)) :
    mulMap F c χ ∈ Submodule.span ℤ (prodSet F ρ) := by
  have hle : Submodule.span ℤ (prodSet F ρ) ≤ (Submodule.span ℤ (prodSet F ρ)).comap (mulMap F c) := by
    rw [Submodule.span_le]
    rintro v ⟨μ, φ, hμ, hv⟩
    refine Submodule.subset_span ⟨c * μ, φ, by rw [map_mul, hμ, mul_zero], ?_⟩
    show algebraMap (𝓞 K) K c • (v : Fin i → K) = _
    rw [hv, smul_smul, ← map_mul]
  exact hle hχ

end DualCotangentKernel

open DualCotangentKernel in

theorem DualCotangentKer.proof : DualCotangentKer.Statement := by
  intro K _ _ i F T _ _b k _ ρ σ hρ hσ hsl ψ hψ
  classical
  change ψ ∈ Submodule.span ℤ (prodSet F ρ)

  choose φ hφ using fun j : Fin i => hσ (Pi.single j 1)
  let w : Option (Fin i) → dualLattice F := fun o => o.elim ψ φ

  have hdep : ¬ LinearIndependent K (fun o => (w o : Fin i → K)) := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin, Module.finrank_fin_fun] at this
    omega
  obtain ⟨g, hg, o, ho⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hJ : RingHom.ker ρ ≠ ⊤ := RingHom.ker_ne_top ρ
  obtain ⟨a, hint, o', -, hnot⟩ :=
    Ideal.exist_integer_multiples_notMem (A := 𝓞 K) (K := K) hJ Finset.univ g (Finset.mem_univ o) ho
  choose c hc using fun x => hint x (Finset.mem_univ x)

  let χ : Option (Fin i) → dualLattice F := fun x => mulMap F (c x) (w x)
  have hsum : ∑ x, χ x = 0 := by
    ext1
    rw [Submodule.coe_sum, Submodule.coe_zero]
    calc ∑ x, ((χ x : dualLattice F) : Fin i → K) = ∑ x, algebraMap (𝓞 K) K (c x) • (w x : Fin i → K) := rfl
      _ = a • ∑ x, g x • (w x : Fin i → K) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hc x, smul_smul]
      _ = 0 := by rw [hg, smul_zero]
  have hσχ : ∀ x, σ (χ x) = ρ (c x) • σ (w x) := fun x => hsl (c x) (w x) (χ x) rfl
  have hσsum : ∑ x, ρ (c x) • σ (w x) = 0 := by
    rw [← map_zero σ, ← hsum, map_sum]
    exact Finset.sum_congr rfl fun x _ => (hσχ x).symm

  have hsome : ∀ j, ρ (c (some j)) = 0 := by
    intro j
    have h := congrFun hσsum j
    rw [Fintype.sum_option] at h
    simp only [w, Option.elim_none, Option.elim_some, hψ, smul_zero, zero_add, hφ, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Pi.zero_apply] at h
    rw [Finset.sum_ite_eq] at h
    simpa using h
  have hnone : ρ (c none) ≠ 0 := by
    intro h0
    apply hnot
    rw [FractionalIdeal.mem_coeIdeal]
    refine ⟨c o', ?_, hc o'⟩
    rw [RingHom.mem_ker]
    cases o' with
    | none => exact h0
    | some j => exact hsome j

  have hgen : ∀ j, χ (some j) ∈ Submodule.span ℤ (prodSet F ρ) := fun j =>
    Submodule.subset_span ⟨c (some j), φ j, hsome j, rfl⟩
  have hχ0 : χ none ∈ Submodule.span ℤ (prodSet F ρ) := by
    have h : χ none = -∑ j, χ (some j) := by
      rw [Fintype.sum_option] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    rw [h]
    exact neg_mem (Submodule.sum_mem _ fun j _ => hgen j)

  obtain ⟨bb, hbb⟩ := hρ (ρ (c none))⁻¹
  have hm : ρ (bb * c none - 1) = 0 := by
    rw [map_sub, map_mul, hbb, inv_mul_cancel₀ hnone, map_one, sub_self]
  have h1 : mulMap F bb (χ none) ∈ Submodule.span ℤ (prodSet F ρ) := mulMap_mem F ρ bb hχ0
  have h2 : mulMap F (bb * c none - 1) ψ ∈ Submodule.span ℤ (prodSet F ρ) :=
    Submodule.subset_span ⟨_, ψ, hm, rfl⟩
  have hψeq : ψ = mulMap F bb (χ none) - mulMap F (bb * c none - 1) ψ := by
    ext1
    simp only [χ, w, Option.elim_none, mulMap, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sub,
      smul_smul, ← map_mul, ← sub_smul, map_sub, map_one]
    rw [sub_sub_cancel, one_smul]
  rw [hψeq]
  exact sub_mem h1 h2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeModPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace DualLatticeModPrimeAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

abbrev locAt (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors

theorem exists_smul_mem (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (L : Submodule (𝓞 K) (Fin i → K)) {x : Fin i → K}
    (hx : x ∈ Submodule.span (locAt 𝔭) (L : Set (Fin i → K))) :
    ∃ s ∈ 𝔭.primeCompl, s • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, 𝔭.primeCompl.one_mem, by rwa [one_smul]⟩
  | zero => exact ⟨1, 𝔭.primeCompl.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, hs₁, hx⟩ := hx
    obtain ⟨s₂, hs₂, hy⟩ := hy
    refine ⟨s₁ * s₂, 𝔭.primeCompl.mul_mem hs₁ hs₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a
    refine ⟨q * s, 𝔭.primeCompl.mul_mem q.2 hs, ?_⟩
    have hq : (q : 𝓞 K) • (IsLocalization.mk' (locAt 𝔭) p q) = algebraMap (𝓞 K) (locAt 𝔭) p := by
      rw [Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    have e : (q * s) • (IsLocalization.mk' (locAt 𝔭) p q • x) = p • (s • x) := by
      rw [mul_comm, mul_smul, ← smul_assoc (q : 𝓞 K), hq, algebraMap_smul, smul_comm]
    rw [e]
    exact L.smul_mem _ hx

theorem span_dual_eq_top (F : HermLattice K i) :
    Submodule.span K (DualLatticeIndexAlt.dual F.lattice : Set (Fin i → K)) = ⊤ := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_le_box F.lattice F.fg
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  have hbox : DualLatticeIndexAlt.box (i := i) (algebraMap (𝓞 K) K e) ≤ DualLatticeIndexAlt.dual F.lattice := by
    have := DualLatticeIndexAlt.dual_anti hle
    rwa [DualLatticeIndexAlt.dual_box (inv_ne_zero heK), inv_inv] at this
  rw [eq_top_iff, ← (Pi.basisFun K (Fin i)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hj : (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) ∈ DualLatticeIndexAlt.dual F.lattice := by
    refine hbox (DualLatticeIndexAlt.mem_box.mpr fun l => ?_)
    by_cases hl : l = j
    · subst hl
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hl]⟩
  have e1 : Pi.basisFun K (Fin i) j = (algebraMap (𝓞 K) K e)⁻¹ • (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) := by
    ext l
    by_cases hl : l = j
    · subst hl
      simp [heK]
    · simp [Pi.basisFun_apply, hl]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hj)

theorem dual_le_span (F : HermLattice K i) :
    ∃ u : Fin i → Fin i → K, DualLatticeIndexAlt.dual F.lattice ≤ Submodule.span (𝓞 K) (Set.range u) := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_box_le F.lattice F.span_eq
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  refine ⟨fun j => Pi.single j (algebraMap (𝓞 K) K e)⁻¹, fun x hx => ?_⟩
  have hx' := DualLatticeIndexAlt.dual_anti hle hx
  rw [DualLatticeIndexAlt.dual_box heK, DualLatticeIndexAlt.mem_box] at hx'
  choose a ha using hx'
  have e1 : x = ∑ j, a j • (Pi.single j (algebraMap (𝓞 K) K e)⁻¹ : Fin i → K) := by
    ext l
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (ha l).symm
  rw [e1]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end DualLatticeModPrimeAlt

open DualLatticeModPrimeAlt in

theorem DualLatticeModPrime.proof : DualLatticeModPrime.Statement := by
  intro K _ _ i F 𝔭 h𝔭
  classical
  have hbot : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField K)
  have : IsDiscreteValuationRing (locAt 𝔭) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hbot (locAt 𝔭)
  set D := DualLatticeIndexAlt.dual F.lattice
  set DA := Submodule.span (locAt 𝔭) (D : Set (Fin i → K))
  obtain ⟨u, hu⟩ := dual_le_span F
  have hDA : DA ≤ Submodule.span (locAt 𝔭) (Set.range u) :=
    Submodule.span_le.mpr fun x hx =>
      Submodule.span_le_restrictScalars (𝓞 K) (locAt 𝔭) _ (hu hx)
  have := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range u)) (R := locAt 𝔭)
  have : Module.Finite (locAt 𝔭) DA := Module.Finite.iff_fg.mpr (isNoetherian_submodule.mp this DA hDA)
  have : Module.IsTorsionFree (locAt 𝔭) DA := inferInstance
  let b := Module.Free.chooseBasis (locAt 𝔭) DA
  have hspan : Submodule.span K (Set.range fun j => (b j : Fin i → K)) = ⊤ := by
    rw [eq_top_iff, ← span_dual_eq_top F, Submodule.span_le]
    intro d hd
    have e0 : d = ∑ j, ((b.repr ⟨d, Submodule.subset_span hd⟩ j • b j : DA) : Fin i → K) := by
      rw [← Submodule.coe_sum, b.sum_repr]
    rw [e0, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Submodule.coe_smul]
    exact Submodule.span_le_restrictScalars (locAt 𝔭) K _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hcard : Fintype.card (Fin i) ≤ Fintype.card (Module.Free.ChooseBasisIndex (locAt 𝔭) DA) := by
    have := finrank_range_le_card (R := K) fun j => (b j : Fin i → K)
    rw [Set.finrank, hspan, finrank_top, Module.finrank_fin_fun] at this
    simpa using this
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ρ : locAt 𝔭 →+* 𝓞 K ⧸ 𝔭 := IsLocalization.lift (M := 𝔭.primeCompl) (g := Ideal.Quotient.mk 𝔭)
    fun s => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv (I := 𝔭) (a := Ideal.Quotient.mk 𝔭 s)
        fun h => s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
      exact ⟨⟨_, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  have hρ : ∀ a, ρ (algebraMap (𝓞 K) (locAt 𝔭) a) = Ideal.Quotient.mk 𝔭 a := fun a =>
    IsLocalization.lift_eq _ _
  have incl : ∀ φ : dualLattice F, (φ : Fin i → K) ∈ DA := fun φ => Submodule.subset_span φ.2
  let ι : dualLattice F →+ DA := AddMonoidHom.mk' (fun φ => ⟨φ, incl φ⟩) fun _ _ => rfl
  let τ : DA →+ (Fin i → 𝓞 K ⧸ 𝔭) := AddMonoidHom.mk' (fun x l => ρ (b.repr x (g l)))
    fun x y => by funext l; simp [map_add]
  have hsmul : ∀ (μ : 𝓞 K) (x : DA), ((algebraMap (𝓞 K) (locAt 𝔭) μ • x : DA) : Fin i → K) =
      algebraMap (𝓞 K) K μ • (x : Fin i → K) := fun μ x => by
    rw [Submodule.coe_smul, algebraMap_smul, algebraMap_smul]
  refine ⟨τ.comp ι, ?_, ?_⟩
  · intro v
    let w : Module.Free.ChooseBasisIndex (locAt 𝔭) DA → 𝓞 K ⧸ 𝔭 := Function.extend g v 0
    choose a ha using fun j => Ideal.Quotient.mk_surjective (I := 𝔭) (w j)
    let x : DA := ∑ j, algebraMap (𝓞 K) (locAt 𝔭) (a j) • b j
    have hx : ∀ j, b.repr x j = algebraMap (𝓞 K) (locAt 𝔭) (a j) := by
      intro j
      simp only [x, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem 𝔭 D x.2
    have hs0 : Ideal.Quotient.mk 𝔭 s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := 𝔭) c
    refine ⟨⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩, ?_⟩
    have e1 : ι ⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩ = algebraMap (𝓞 K) (locAt 𝔭) (t * s) • x := by
      apply Subtype.ext
      rw [hsmul, algebraMap_smul, mul_smul]
      rfl
    funext l
    have key : ∀ y : DA, τ y l = ρ (b.repr y (g l)) := fun _ => rfl
    rw [AddMonoidHom.comp_apply, e1, key, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, hx, hρ,
      map_mul, ht, mul_comm c, hc, one_mul, ha]
    exact g.injective.extend_apply _ _ _
  · intro μ φ ψ h
    have e1 : ι ψ = algebraMap (𝓞 K) (locAt 𝔭) μ • ι φ := by
      apply Subtype.ext
      rw [hsmul]
      exact h
    funext l
    have key : ∀ x : DA, τ x l = ρ (b.repr x (g l)) := fun _ => rfl
    rw [Pi.smul_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e1, key, key, map_smul,
      Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, smul_eq_mul]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcBaseLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalBaseBound

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]

theorem centre_mem {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {k : Type} [Field k] {α : T → k}
    {M : T → Fin i → k} (hres : IsExcResidueData b b' α M) (t : T) :
    C (a t) * graphFirst t ∈ linPrime α M := by
  obtain ⟨ρ, ρ', σ, -, -, -, hker, -, -, hα, -⟩ := hres
  have hmem : ((a t • b' t : dualLattice F') : Fin i → K) ∈ dualLattice F := by
    rw [Submodule.coe_smul_of_tower, ← hab t]
    exact (b t).2
  have h0 : ((a t : ℤ) : k) * α t = 0 := by
    rw [hα t, ← zsmul_eq_mul, ← map_zsmul]
    exact (hker _).mpr hmem
  have h1 : linPointMap α M (C (a t)) = C ((a t : k)) := by simp [linPointMap]
  rw [linPrime, RingHom.mem_ker, map_mul, h1, LinPrimeExample.linPointMap_first, ← mul_assoc, ← C_mul, h0, C_0,
    zero_mul]

end StackedExceptionalBaseBound

open StackedExceptionalBaseBound in

theorem DualStackedExcBaseLe.proof (hBihom : DualStackedGraphBihomog.Statement)
    (hLead : DualStackedExcLeadForm.Statement) : DualStackedExcBaseLe.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ α M hres
  refine sup_le ?_ ?_
  · intro f hf
    obtain ⟨s, g, rfl, hg⟩ := hBihom K i F F' T b b' a hab f hf
    rw [linPrime, RingHom.mem_ker, map_sum]
    exact Finset.sum_eq_zero fun p hp =>
      hLead K i F F' T b b' a hi hlt hcov hab k α M hres p.1 p.2 (g p) (hg p hp).1 (hg p hp).2
  · rw [Ideal.span_le, Set.range_subset_iff]
    exact centre_mem hab hres

end

end GroundTheory.Heights₂.Heights
end

