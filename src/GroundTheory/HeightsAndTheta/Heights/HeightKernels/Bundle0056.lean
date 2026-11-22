import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcCycle
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

namespace StackedExceptionalChart

theorem exists_pow_uniform {A : Type*} [CommRing A] {I J : Ideal A} (hI : I.FG) {s : A}
    (h : ∀ e ∈ I, ∃ n : ℕ, s ^ n * e ∈ J) : ∃ N : ℕ, ∀ e ∈ I, s ^ N * e ∈ J := by
  classical
  obtain ⟨S, rfl⟩ := hI
  have h' : ∀ x ∈ S, ∃ n : ℕ, s ^ n * x ∈ J := fun x hx => h x (Ideal.subset_span hx)
  choose! n hn using h'
  refine ⟨S.sup n, fun e he => ?_⟩
  induction he using Submodule.span_induction with
  | mem x hx =>
    have e1 : s ^ S.sup n * x = s ^ (S.sup n - n x) * (s ^ n x * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := n) hx)]
    rw [e1]
    exact J.mul_mem_left _ (hn x hx)
  | zero => rw [mul_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left r hx

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

section Chart

variable {F' : HermLattice K i} (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (v u : T)

theorem isUnit_chart : IsUnit (excChartMap b' a v u (graphFirst v * graphSecond u)) :=
  IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (excChartIdeal b' a u) (graphFirst v * graphSecond u))

theorem isUnit_second : IsUnit (excChartMap b' a v u (graphSecond u)) := by
  have h : IsUnit (excChartMap b' a v u (graphFirst v) * excChartMap b' a v u (graphSecond u)) := by
    rw [← map_mul]; exact isUnit_chart b' a v u
  exact isUnit_of_mul_isUnit_right h

theorem isUnit_first : IsUnit (excChartMap b' a v u (graphFirst v)) := by
  have h : IsUnit (excChartMap b' a v u (graphFirst v) * excChartMap b' a v u (graphSecond u)) := by
    rw [← map_mul]; exact isUnit_chart b' a v u
  exact isUnit_of_mul_isUnit_left h

theorem first_eq_zero (s : T) : excChartMap b' a v u (C (a s) * graphFirst s) = 0 := by
  have hJ : (C (a s) * graphFirst s) * graphSecond u ∈ excChartIdeal b' a u :=
    StackedExceptionalCycle.mul_mem_first b' a s u
  have h0 : excChartMap b' a v u ((C (a s) * graphFirst s) * graphSecond u) = 0 := by
    rw [excChartMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hJ, map_zero]
  rw [map_mul] at h0
  exact (isUnit_second b' a v u).mul_left_eq_zero.mp h0

theorem exists_pow_mul_mem {e : MRing (stackedBlocks T)} (he : excChartMap b' a v u e = 0) :
    ∃ n : ℕ, (graphFirst v * graphSecond u) ^ n * e ∈ excChartIdeal b' a u := by
  rw [excChartMap, RingHom.comp_apply, IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (excChartIdeal b' a u) (graphFirst v * graphSecond u)))
    (excChartRing b' a v u)] at he
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := he
  refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  rw [map_mul, map_pow]
  exact hn

theorem chart_firstForm_sub (t : T) (e : T → ℤ) :
    excChartMap b' a v u (graphFirstForm fun s => (Pi.single t (1 : ℤ) : T → ℤ) s - e s * a s) =
      excChartMap b' a v u (graphFirst t) := by
  have h1 : ∀ s, excChartMap b' a v u (C ((Pi.single t (1 : ℤ) : T → ℤ) s - e s * a s) * graphFirst s) =
      excChartMap b' a v u (C ((Pi.single t (1 : ℤ) : T → ℤ) s) * graphFirst s) := by
    intro s
    rw [C_sub, C_mul, sub_mul, mul_assoc, map_sub, map_mul (excChartMap b' a v u) (C (e s)), first_eq_zero,
      mul_zero, sub_zero]
  rw [graphFirstForm, map_sum, Finset.sum_congr rfl fun s _ => h1 s, ← map_sum]
  congr 1
  rw [Finset.sum_eq_single t (fun s _ hs => by rw [Pi.single_eq_of_ne hs, C_0, zero_mul])
    (fun h => absurd (Finset.mem_univ t) h), Pi.single_eq_same, C_1, one_mul]

end Chart

section Lattice

variable {F F' : HermLattice K i}

omit [DecidableEq T] in

theorem latCombo_eq (b' : Module.Basis T ℤ (dualLattice F')) (c : T → ℤ) :
    latCombo b' c = ((b'.equivFun.symm c : dualLattice F') : Fin i → K) := by
  rw [Module.Basis.equivFun_symm_apply, latCombo, Submodule.coe_sum]
  rfl

omit [DecidableEq T] in

theorem exists_latCombo (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {ψ : Fin i → K}
    (hψ : ψ ∈ dualLattice F) : ∃ e : T → ℤ, ψ = latCombo b' fun s => e s * a s := by
  refine ⟨b.equivFun ⟨ψ, hψ⟩, ?_⟩
  have h := congrArg Subtype.val (b.sum_equivFun ⟨ψ, hψ⟩)
  rw [Submodule.coe_sum] at h
  refine Eq.trans (h.symm : ψ = _) ?_
  rw [latCombo]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Submodule.coe_smul, hab, mul_smul]

theorem smul_mem_dual {φ : Fin i → K} (hφ : φ ∈ dualLattice F') (ω : 𝓞 K) :
    algebraMap (𝓞 K) K ω • φ ∈ dualLattice F' := by
  intro x hx
  rw [smul_dotProduct, smul_eq_mul]
  exact mul_mem ⟨ω, rfl⟩ (hφ x hx)

end Lattice

end StackedExceptionalChart

open StackedExceptionalChart in

theorem DualStackedExcChart.proof (hC : DualStackedExcChartForms.Statement) : DualStackedExcChart.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ ρ π y₀ m g α M hX v u
  have hX' := hX
  obtain ⟨hρ, -, -, -, hα, -, -, -, -, -, h11, -⟩ := hX'
  refine exists_pow_uniform (IsNoetherian.noetherian _) fun e he => exists_pow_mul_mem b' a v u ?_
  obtain ⟨cv, hcv, hρcv⟩ := hα v
  by_cases hv : α v = 0
  ·
    have hmem : (b' v : Fin i → K) ∈ dualLattice F := h11 _ (b' v).2 cv hcv (hρcv.trans hv)
    obtain ⟨c, hc⟩ := exists_latCombo b b' hab hmem
    rw [latCombo_eq] at hc
    have hc' := congrArg (fun x => b'.equivFun x v) (Subtype.ext hc : b' v = b'.equivFun.symm _)
    simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_self, ↓reduceIte] at hc'
    have hXv : excChartMap b' a v u (graphFirst v) = 0 := by
      have e1 : graphFirst v = C (c v) * (C (a v) * graphFirst v) := by
        rw [← mul_assoc, ← C_mul, ← hc', C_1, one_mul]
      rw [congrArg (excChartMap b' a v u) e1, map_mul, first_eq_zero, mul_zero]
    have hu := isUnit_first b' a v u
    rw [hXv] at hu
    exact (subsingleton_iff_zero_eq_one.mp (isUnit_zero_iff.mp hu)).elim _ _
  · obtain ⟨σ₀, hσ, W, hW⟩ := hC K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hX v u

    have hfirst : ∀ t, σ₀ (α t) * (σ₀ (α v)⁻¹ * excChartMap b' a v u (graphFirst v)) =
        excChartMap b' a v u (graphFirst t) := by
      intro t
      obtain ⟨ω, hω⟩ := hρ (α t * (α v)⁻¹)
      obtain ⟨ct, hct, hρct⟩ := hα t
      have hψ : (b' t : Fin i → K) - algebraMap (𝓞 K) K ω • (b' v : Fin i → K) ∈ dualLattice F := by
        refine h11 _ (sub_mem (b' t).2 (smul_mem_dual (b' v).2 ω)) (ct - ω * cv) ?_ ?_
        · rw [map_sub, map_mul, hct, hcv, sub_dotProduct, smul_dotProduct, smul_eq_mul]
        · rw [map_sub, map_mul, hρct, hρcv, hω, mul_assoc, inv_mul_cancel₀ hv, mul_one, sub_self]
      obtain ⟨e, he⟩ := exists_latCombo b b' hab hψ
      have hlc : latCombo b' (fun s => (Pi.single t (1 : ℤ) : T → ℤ) s - e s * a s) =
          algebraMap (𝓞 K) K ω • (b' v : Fin i → K) := by
        have e2 : latCombo b' (fun s => (Pi.single t (1 : ℤ) : T → ℤ) s - e s * a s) =
            latCombo b' (Pi.single t (1 : ℤ)) - latCombo b' fun s => e s * a s := by
          simp only [latCombo, sub_smul, Finset.sum_sub_distrib]
        have e3 : latCombo b' (Pi.single t (1 : ℤ)) = (b' t : Fin i → K) := by
          rw [latCombo, Finset.sum_eq_single t (fun s _ hs => by rw [Pi.single_eq_of_ne hs, zero_smul])
            (fun h => absurd (Finset.mem_univ t) h), Pi.single_eq_same, one_smul]
        rw [e2, e3, ← he, sub_sub_cancel]
      rw [← chart_firstForm_sub b' a v u t e, ← hσ ω _ hlc, ← mul_assoc, ← map_mul, hω]

    let σ : MvPolynomial (Option (Fin (m + 1))) k →+* excChartRing b' a v u :=
      eval₂Hom σ₀ fun o => o.elim (σ₀ (α v)⁻¹ * excChartMap b' a v u (graphFirst v)) W
    have key : σ.comp (linPointMap α M) = excChartMap b' a v u := by
      refine MvPolynomial.ringHom_ext (fun n => ?_) ?_
      · rw [RingHom.comp_apply, eq_intCast C n, map_intCast, map_intCast, map_intCast]
      · rintro ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, (t : T)⟩
        · show σ (linPointMap α M (graphFirst t)) = excChartMap b' a v u (graphFirst t)
          rw [LinPrimeExample.linPointMap_first, map_mul]
          simp only [σ, eval₂Hom_C, eval₂Hom_X', Option.elim]
          exact hfirst t
        · show σ (linPointMap α M (graphSecond t)) = excChartMap b' a v u (graphSecond t)
          rw [LinPrimeExample.linPointMap_second, map_sum, ← hW t]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [σ, map_mul, eval₂Hom_C, eval₂Hom_X', Option.elim]
    rw [← key, RingHom.comp_apply, RingHom.mem_ker.mp he, map_zero]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcReduced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalReduced

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]

theorem mul_mem_of_mem_base [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (u : T) :
    ∀ x ∈ stackedBase b' a,
      graphSecond u * x ∈ stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u} := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [mul_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ((stackedGraph b' a).mul_mem_left _ hy)) ?_
  clear hx
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [mul_comm (graphSecond u)]
    exact StackedExceptionalCycle.mul_mem_first b' a s u
  | zero => rw [mul_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ r hx

theorem graphFirst_not_mem {k : Type} [Field k] {n : ℕ} {α : T → k} {M : T → Fin n → k} {t : T}
    (h : α t ≠ 0) : graphFirst t ∉ linPrime α M := by
  rw [linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_first]
  exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)

theorem graphSecond_not_mem {k : Type} [Field k] {m : ℕ} {α : T → k} {M : T → Fin (m + 1) → k} {t : T}
    (h : M t 0 ≠ 0) : graphSecond t ∉ linPrime α M := by
  rw [linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_second]
  intro h0
  apply h
  have h1 := congrArg (MvPolynomial.eval fun o : Option (Fin (m + 1)) =>
    o.elim (0 : k) fun j => if j = 0 then 1 else 0) h0
  simpa [Finset.sum_ite_eq'] using h1

end StackedExceptionalReduced

open StackedExceptionalCycle StackedGraphHorizontal StackedExceptionalReduced in

theorem DualStackedExcReduced.proof (hC : DualStackedExcCoords.Statement) (hB : DualStackedExcBase.Statement)
    (hX : DualStackedExcChart.Statement) : DualStackedExcReduced.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab
  obtain ⟨k, _, ρ, π, y₀, m, g, α, M, hd⟩ := hC K i F F' T b b' a hi hlt hcov hab
  have hbase := hB K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hd
  have hchart := hX K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hd
  obtain ⟨-, -, -, -, -, -, -, ⟨v, hv⟩, ⟨u, hu⟩, -⟩ := hd
  have hEp : (linPrime α M).IsPrime := RingHom.ker_isPrime _
  have hXv : graphFirst v ∉ linPrime α M := graphFirst_not_mem hv
  have hYu : graphSecond u ∉ linPrime α M := graphSecond_not_mem hu
  have hrel : IsRelevant (linPrime α M) := by
    rintro (⟨⟩ | ⟨⟩)
    · exact ⟨v, hXv⟩
    · exact ⟨u, hYu⟩
  have hsub : ∀ w : T, stackedGraph b' a ⊔ Ideal.span {C (a w) * graphFirst w} ≤ stackedBase b' a :=
    fun w => sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (first_mem_base b' a w))

  have hkey : ∀ W : Ideal (MRing (stackedBlocks T)), W.IsPrime → IsRelevant W → stackedBase b' a ≤ W →
      linPrime α M ≤ W := by
    intro W hW hWr hBW e he
    obtain ⟨v', hv'⟩ : ∃ v' : T, graphFirst v' ∉ W := hWr (Sum.inl ())
    obtain ⟨u', hu'⟩ : ∃ u' : T, graphSecond u' ∉ W := hWr (Sum.inr ())
    obtain ⟨N, hN⟩ := hchart v' u'
    have h1 : (graphFirst v' * graphSecond u') ^ N * e ∈ W := hBW (hsub u' (hN e he))
    refine (hW.mem_or_mem h1).resolve_left fun h2 => ?_
    rcases hW.mem_or_mem (hW.mem_of_pow_mem N h2) with h3 | h3
    · exact hv' h3
    · exact hu' h3
  have hmin : linPrime α M ∈ (stackedBase b' a).minimalPrimes := by
    refine ⟨⟨hEp, hbase⟩, fun Q hQ hQE => hkey Q hQ.1 (fun κ => ?_) hQ.2⟩
    obtain ⟨j, hj⟩ := hrel κ
    exact ⟨j, fun h => hj (hQE h)⟩
  refine ⟨linPrime α M, ⟨hmin, hrel⟩, fun W hW => ?_, ?_⟩
  · have hEW := hkey W hW.1.1.1 hW.2 hW.1.1.2
    exact le_antisymm (hW.1.2 ⟨hEp, hbase⟩ hEW) hEW
  · obtain ⟨N, hN⟩ := hchart v u
    have hs : (graphFirst v * graphSecond u) ^ N ∉ linPrime α M := fun h =>
      (hEp.mem_or_mem (hEp.mem_of_pow_mem N h)).elim hXv hYu
    rw [← multAt_eq_of_mul_mem (hsub u) hYu (mul_mem_of_mem_base b' a u),
      multAt_eq_of_mul_mem ((hsub u).trans hbase) hs hN]
    have := hEp
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopBasisChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace TopDualBasisChange

theorem hermLine_ext {ι : Unit → Type} [∀ k, Fintype (ι k)] {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂]

omit [DecidableEq T₂] in

theorem subst_subst {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1) (f : MRing (dualBlocks T)) :
    intCoordSubst A (intCoordSubst B f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    show intCoordSubst A (intCoordSubst B (algebraMap ℤ _ a)) = algebraMap ℤ _ a
    rw [AlgHom.commutes, AlgHom.commutes]
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, hf]
    congr 1
    obtain ⟨⟨⟩, t⟩ := p
    have hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T)) := fun a => map_intCast C a
    simp only [intCoordSubst, aeval_X, map_sum, map_mul, eq_intCast, hC, map_intCast, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Int.cast_mul, ← Finset.sum_mul, ← Int.cast_sum]
    have h1 : ∀ x : T, ∑ s, B s t * A x s = (A * B) x t := by
      intro x
      simp [Matrix.mul_apply, mul_comm]
    simp_rw [h1, hAB, Matrix.one_apply]
    simp

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

theorem basis_coe (b : Module.Basis T ℤ (dualLattice F)) (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (s : T₂) (j : Fin i) :
    (b₂ s : Fin i → K) j = ∑ t, (b.toMatrix b₂ t s : K) * (b t : Fin i → K) j := by
  have h := congrArg (fun φ : dualLattice F => (φ : Fin i → K) j) (b.sum_toMatrix_smul_self b₂ s)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, zsmul_eq_mul] at h
  exact h.symm

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

theorem coord_change {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j) (s : T₂) :
    dualLatticeCoord b₂ ⟨(), s⟩ = ∑ t, (A t s : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ := by
  have h : (∑ j, C ((b₂ s : Fin i → K) j) * X j : MvPolynomial (Fin i) K) =
      ∑ t, (A t s : MvPolynomial (Fin i) K) * ∑ j, C ((b t : Fin i → K) j) * X j := by
    simp only [hA, map_sum, map_mul, map_intCast, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  simp only [dualLatticeCoord]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, map_intCast]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

theorem coneMap_subst {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (f : MRing (dualBlocks T₂)) :
    mConeMap (dualLatticeCoord b) (intCoordSubst A f) = mConeMap (dualLatticeCoord b₂) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have hC₂ : ∀ a : ℤ, (C a : MRing (dualBlocks T₂)) = (a : MRing (dualBlocks T₂)) := fun a => map_intCast C a
    rw [hC₂, map_intCast, map_intCast, map_intCast]
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | mul_X f p hf =>
    rw [map_mul, map_mul, map_mul, hf]
    congr 1
    obtain ⟨⟨⟩, s⟩ := p
    have hC : ∀ a : ℤ, (C a : MRing (dualBlocks T)) = (a : MRing (dualBlocks T)) := fun a => map_intCast C a
    simp only [intCoordSubst, aeval_X, map_sum, map_mul, hC, map_intCast, mConeMap, coord_change hA s,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_assoc]

omit [DecidableEq T₂] in

theorem ideal_map {A : Matrix T T₂ ℤ} {B : Matrix T₂ T ℤ} (hAB : A * B = 1)
    {b : Module.Basis T ℤ (dualLattice F)} {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j) :
    (dualIdeal b₂).map (intCoordSubst A) = dualIdeal b := by
  have hsurj : Function.Surjective (intCoordSubst A) := fun f => ⟨intCoordSubst B f, subst_subst hAB f⟩
  have hker : dualIdeal b₂ = (dualIdeal b).comap (intCoordSubst A) := by
    ext f
    simp only [dualIdeal, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, coneMap_subst hA]
  rw [hker, Ideal.map_comap_of_surjective _ hsurj]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

theorem embMatrix_apply {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (s : T₂) (p : (K →+* ℂ) × Fin i) :
    dualEmbMatrix b₂ s p = ∑ t, (A t s : ℂ) * dualEmbMatrix b t p := by
  simp only [dualEmbMatrix, hA, map_sum, map_mul, map_intCast]

omit [DecidableEq T] [Fintype T₂] [DecidableEq T₂] in

theorem recover_eq {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂)))
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (z : (Σ _ : Unit, T) → ℂ) :
    dualRecover b₂ hb₂ (fun s => intCoordPt A z ⟨(), s⟩) = dualRecover b hb (fun t => z ⟨(), t⟩) := by
  rw [dualRecover, LinearEquiv.symm_apply_eq]
  set w := dualRecover b hb (fun t => z ⟨(), t⟩)
  have hw : Matrix.mulVecLin (dualEmbMatrix b) w = fun t => z ⟨(), t⟩ := by
    simp only [w, dualRecover]
    exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective _ hb) _
  funext s
  rw [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [embMatrix_apply hA, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [intCoordPt]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht := congrFun hw t
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at ht
  rw [← ht, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

omit [DecidableEq T₂] in

theorem line_eq {A : Matrix T T₂ ℤ} {b : Module.Basis T ℤ (dualLattice F)}
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {b₂ : Module.Basis T₂ ℤ (dualLattice F)}
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂)))
    (hA : ∀ s j, (b₂ s : Fin i → K) j = ∑ t, (A t s : K) * (b t : Fin i → K) j)
    (hAB : ∃ B : Matrix T₂ T ℤ, A * B = 1) :
    intCoordLine A hAB (dualLine F b₂ hb₂) = dualLine F b hb := by
  refine hermLine_ext rfl (funext fun z => ?_)
  show Real.sqrt (dualNormSq b₂ hb₂ fun s => intCoordPt A z ⟨(), s⟩) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  simp only [dualNormSq, recover_eq hb hb₂ hA z]

end TopDualBasisChange

open TopDualBasisChange in

theorem DualTopBasisChange.proof (hChange : IntCoordChange.Statement) : DualTopBasisChange.Statement := by
  intro K _ _ i F T T₂ _ _ _ _ b hb b₂ hb₂ II hi hII
  have hAB : b.toMatrix b₂ * b₂.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b b₂
  have hBA : b₂.toMatrix b * b.toMatrix b₂ = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₂ b
  have h := hChange T T₂ (b.toMatrix b₂) (b₂.toMatrix b) hAB hBA II hII (dualIdeal b₂) i
    (fun _ => dualLine F b₂ hb₂) hi (DualArithVar.full K i F T₂ b₂ hi)
    (fun _ => (DualLineSemipositive.proof K i F T₂ b₂ hb₂).1)
  rw [ideal_map hAB (basis_coe b b₂), line_eq hb hb₂ (basis_coe b b₂)] at h
  exact h.symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordArInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordArInt.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (_ : A * B = 1) (hBA : B * A = 1) (Q : Ideal (MRing (dualBlocks T))) (e : ℕ)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T))
    (Ab : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) (s : MRing (dualBlocks T)),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm Ab → IsSectionOn Q Ab s →
    arInt (Q.comap (intCoordSubst A)) (intCoordSubst B s) (intCoordLine B ⟨A, hBA⟩ Ab)
        (fun j => intCoordLine B ⟨A, hBA⟩ (L j)) =
      arInt Q s Ab L

def intCoordSwap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem intCoordSwap_mul_self : intCoordSwap * intCoordSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [intCoordSwap, Matrix.mul_apply, Fin.sum_univ_two]

example : intCoordSwap * intCoordSwap = 1 ∧ IsArithVar (⊥ : Ideal (MRing (dualBlocks (Fin 2)))) (1 + 1) ∧
    (∀ j, IsSmoothHerm (![fsLine 2] j)) ∧ IsSmoothHerm (fsLine 2) ∧
    IsSectionOn (⊥ : Ideal (MRing (dualBlocks (Fin 2)))) (fsLine 2) (Xc 2 0) :=
  ⟨intCoordSwap_mul_self, Inter.isArithVar_projLine, fun j => by fin_cases j; exact Inter.isSmoothHerm_fsLine 2,
    Inter.isSmoothHerm_fsLine 2, Inter.isSectionOn_Xc 2 0⟩

end

end GroundTheory.Heights₂.Heights
end

