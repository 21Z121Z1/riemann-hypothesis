import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0030

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.RangeInclSaturated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding GroundTheory.Heights₂.Heights

noncomputable section

theorem range_incl_saturated {K : Type*} [Field K] [NumberField K]
    {E' E E'' : HermitianBundle K} (Y : HermitianExtension E' E E'') (t : 𝓞 K) (x : E.carrier)
    (ht : t ≠ 0) (hx : t • x ∈ LinearMap.range Y.incl) : x ∈ LinearMap.range Y.incl := by
  rw [← Y.exact.linearMap_ker_eq, LinearMap.mem_ker] at hx ⊢
  rw [map_smul] at hx
  exact (smul_eq_zero.mp hx).resolve_left ht

theorem S6.BundleCoordinates.proof (hA : S6.LineCoordinates.Statement)
    (hB : S6.CoordinateDegree.Statement) (hC : S6.QuotientDegreeSplit.Statement)
    (hD : S6.ExtensionDegree.Statement) (hE : S6.SaturatedSpan.Statement) :
    S6.BundleCoordinates.Statement := by
  intro K _ _ E X _ _ L hI hr ho E' E'' Y
  obtain ⟨n, e, a, d, ψ, ha, hd, hc, hψ, hrange, hfin, hline, hmet⟩ := hA K E X L hI hr ho
  obtain ⟨hFG, hspanA⟩ := LinesIdealLatticeFG.full K n a ha
  have hspan : Submodule.span K (LinearMap.range ψ : Set (Fin n → K)) = ⊤ := by
    rw [hrange]; exact hspanA
  have hdeg := hB K E n (diagMetric d) ψ hψ hspan hmet
  refine ⟨n, e, a, d, ha, hd, hc, fun i => ?_, ?_⟩
  ·
    have hu : LinearIndependent K (fun _ : Fin 1 => (Pi.single i 1 : Fin n → K)) :=
      linearIndependent_unique_iff.mpr (by simp)
    have h1 := hdeg (L (e i)) (Fin 1) _ hu (by rw [hline i, hrange, Set.range_const])
    rw [HermitianBundle.normDegree, h1, hrange]
    rfl
  ·
    set G := LinearMap.range Y.incl
    obtain ⟨b, hb, hbmap⟩ := hE K E.carrier n ψ hψ G (range_incl_saturated Y)
    have hGr : Module.finrank (𝓞 K) G = Module.finrank (𝓞 K) E'.carrier :=
      LinearMap.finrank_range_of_inj Y.incl_injective
    have hmk : Module.finrank (𝓞 K) G + E''.rank ⊤ = n := by
      rw [hGr, HermitianBundle.rank, finrank_top, ← hfin, Y.finrank_eq]
    obtain ⟨τ, -, hli⟩ := LinesExtendBasis.full K n _ _ b hb hmk
    refine ⟨_, _, b, fun j => Pi.single (τ j) 1, hli, hmk, rfl, ?_⟩
    have htop : Submodule.span K
        (Set.range (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K))) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by
        rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Module.finrank_fin_fun, hmk])
    have hE1 := hdeg ⊤ _ (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K)) hli (by
      rw [Submodule.map_top, htop, Submodule.restrictScalars_top, inf_top_eq])
    have hG1 := hdeg G _ b hb hbmap
    rw [hC K n (idealLattice a) (diagMetric d) hFG hspanA _ _ b _ hli hmk,
      HermitianBundle.normDegree, hD K E' E E'' Y, hE1, hG1, hrange]
    rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.RelIndexSplitOfLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

noncomputable section

namespace QuotientDegreeSplitAlt

theorem relIndex_split_of_le {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    {A C : AddSubgroup G} (hCA : C ≤ A) :
    C.relIndex A = C.relIndex (A ⊓ π.ker) * (C.map π).relIndex (A.map π) := by
  have h1 : (C.map π).relIndex (A.map π) = (C ⊔ π.ker).relIndex A := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq]
  have hmod : (A ⊓ π.ker) ⊔ C = (C ⊔ π.ker) ⊓ A := by
    ext x
    simp only [AddSubgroup.mem_sup, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨y, ⟨hyA, hyW⟩, z, hz, rfl⟩
      exact ⟨⟨z, hz, y, hyW, add_comm z y⟩, add_mem hyA (hCA hz)⟩
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hA⟩
      refine ⟨z, ⟨?_, hz⟩, y, hy, add_comm z y⟩
      have hz' : z = (y + z) - y := by abel
      rw [hz']
      exact sub_mem hA (hCA hy)
  have h2 : C.relIndex ((C ⊔ π.ker) ⊓ A) = C.relIndex (A ⊓ π.ker) := by
    rw [← hmod, AddSubgroup.relIndex_sup_right]
  rw [h1, ← h2, AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left le_sup_left]

theorem genIndex_split {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    (A C : AddSubgroup G) (hpos : 0 < genIndex A C) :
    genIndex A C = genIndex (A ⊓ π.ker) (C ⊓ π.ker) * genIndex (A.map π) (C.map π) := by
  have hDA : (A ⊓ C).map π ≤ A.map π := AddSubgroup.map_mono inf_le_left
  have hDC : (A ⊓ C).map π ≤ C.map π := AddSubgroup.map_mono inf_le_right
  have hA : C.relIndex A = (A ⊓ C).relIndex (A ⊓ π.ker) * (((A ⊓ C).map π).relIndex
      (A.map π ⊓ C.map π) * (C.map π).relIndex (A.map π)) := by
    rw [← AddSubgroup.inf_relIndex_left A C, relIndex_split_of_le π (inf_le_left : A ⊓ C ≤ A),
      inf_comm (A.map π), AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDC]
  have hC : A.relIndex C = (A ⊓ C).relIndex (C ⊓ π.ker) * (((A ⊓ C).map π).relIndex
      (A.map π ⊓ C.map π) * (A.map π).relIndex (C.map π)) := by
    rw [← AddSubgroup.inf_relIndex_right A C, relIndex_split_of_le π (inf_le_right : A ⊓ C ≤ C),
      AddSubgroup.relIndex_inf_mul_relIndex, inf_of_le_left hDA]
  have hW1 : (C ⊓ π.ker).relIndex (A ⊓ π.ker) = (A ⊓ C).relIndex (A ⊓ π.ker) := by
    rw [← AddSubgroup.inf_relIndex_right (C ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    tauto
  have hW2 : (A ⊓ π.ker).relIndex (C ⊓ π.ker) = (A ⊓ C).relIndex (C ⊓ π.ker) := by
    rw [← AddSubgroup.inf_relIndex_right (A ⊓ π.ker), ← AddSubgroup.inf_relIndex_right (A ⊓ C)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    tauto
  have he : ((((A ⊓ C).map π).relIndex (A.map π ⊓ C.map π) : ℕ) : ℝ) ≠ 0 := by
    intro h0
    have hz : genIndex A C = 0 := by
      unfold genIndex
      rw [hA]
      push_cast
      rw [h0]
      simp
    linarith
  unfold genIndex
  rw [hA, hC, hW1, hW2]
  push_cast
  rw [div_mul_div_comm, mul_left_comm (((A ⊓ C).relIndex (A ⊓ π.ker) : ℕ) : ℝ),
    mul_left_comm (((A ⊓ C).relIndex (C ⊓ π.ker) : ℕ) : ℝ), mul_div_mul_left _ _ he]

end QuotientDegreeSplitAlt

open QuotientDegreeSplitAlt in

theorem S6.QuotientDegreeSplit.proof : S6.QuotientDegreeSplit.Statement := by
  intro K _ _ n Λ H hFG hspan m k b c hli hmk
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) := by
    simp [hmk]
  set B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard with hBdef
  have hB : ⇑B = Sum.elim b c := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hBl : (fun i => B (Sum.inl i)) = b := by
    funext i; simp [hB]
  set W : Submodule (𝓞 K) (Fin n → K) :=
    (Submodule.span K (Set.range b)).restrictScalars (𝓞 K) with hWdef
  set π' : (Fin n → K) →ₗ[𝓞 K] (Fin k → K) := (coordProj B).restrictScalars (𝓞 K) with hπ'
  have hkerK : ∀ v, coordProj B v = 0 ↔ v ∈ Submodule.span K (Set.range b) := by
    intro v
    rw [← LinearMap.mem_ker, KLinesQuotIndex.ker_coordProj, hBl]
  have hb0 : ∀ i, coordProj B (b i) = 0 := fun i =>
    (hkerK _).mpr (Submodule.subset_span ⟨i, rfl⟩)
  have hc1 : ∀ j, coordProj B (c j) = Pi.single j 1 := by
    intro j
    have hcj : c j = B (Sum.inr j) := by simp [hB]
    rw [hcj]
    funext j'
    simp [coordProj, Pi.single_apply, Finsupp.single_apply]
    by_cases h : j = j'
    · subst h; simp
    · simp [h, Ne.symm h]

  set O : Submodule (𝓞 K) (Fin n → K) := Submodule.span (𝓞 K) (Set.range (Sum.elim b c)) with hOdef
  have htop : Submodule.span K (Set.range (Sum.elim b c)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hcard
  have hOspan : Submodule.span K (O : Set (Fin n → K)) = ⊤ := by
    rw [hOdef, Submodule.span_span_of_tower, htop]
  have hΛlat : Submodule.IsLattice ℚ (Λ.restrictScalars ℤ) :=
    LinesIsLattice.full K (Fin n) Λ hFG.restrictScalars hspan
  have hOlat : Submodule.IsLattice ℚ (O.restrictScalars ℤ) :=
    LinesIsLattice.full K (Fin n) O (Submodule.fg_span (Set.finite_range _)).restrictScalars hOspan
  have hpos : 0 < genIndex Λ.toAddSubgroup O.toAddSubgroup :=
    (LinesGenIndexTrans.full (Fin n → K) (Λ.restrictScalars ℤ) (O.restrictScalars ℤ)
      (O.restrictScalars ℤ) hΛlat hOlat hOlat).1

  have hker : (π' : (Fin n → K) →+ (Fin k → K)).ker = W.toAddSubgroup := by
    ext v
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, hWdef, Submodule.restrictScalars_mem,
      ← hkerK]
    rfl

  have hOW : O ⊓ W = Submodule.span (𝓞 K) (Set.range b) := by
    apply le_antisymm
    · rintro x ⟨hxO, hxW⟩
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hxO
      have h0 : π' (∑ i, r i • Sum.elim b c i) = 0 := (hkerK _).mpr hxW
      rw [Fintype.sum_sum_type] at h0 ⊢
      simp only [Sum.elim_inl, Sum.elim_inr] at h0 ⊢
      have hs : ∀ j, r (Sum.inr j) = 0 := by
        intro j
        have h1 := congrFun h0 j
        simp only [map_add, map_sum, map_smul, hπ', LinearMap.restrictScalars_apply, hb0, hc1,
          smul_zero, Finset.sum_const_zero, zero_add, Finset.sum_apply, Pi.smul_apply,
          Pi.single_apply, smul_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          Pi.zero_apply] at h1
        exact (smul_eq_zero.mp h1).resolve_right one_ne_zero
      simp only [hs, zero_smul, Finset.sum_const_zero, add_zero]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · refine le_inf (Submodule.span_mono ?_) (Submodule.span_le_restrictScalars (𝓞 K) K _)
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i, rfl⟩

  have hOmap : O.map π' = Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c)) := by
    have hcomp : ⇑π' ∘ Sum.elim b c = Sum.elim (fun _ => 0) (coordProj B ∘ c) := by
      funext x
      rcases x with i | j
      · exact hb0 i
      · rfl
    rw [hOdef, Submodule.map_span, ← Set.range_comp, hcomp, Set.Sum.elim_range,
      Submodule.span_union]
    have hbot : Submodule.span (𝓞 K) (Set.range (fun _ : Fin m => (0 : Fin k → K))) = ⊥ :=
      Submodule.span_eq_bot.mpr (by rintro _ ⟨i, rfl⟩; rfl)
    rw [hbot, bot_sup_eq]

  have hsplit := genIndex_split (π' : (Fin n → K) →+ (Fin k → K)) Λ.toAddSubgroup O.toAddSubgroup hpos
  rw [hker, ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hOmap] at hsplit
  have hinf1 : Λ.toAddSubgroup ⊓ W.toAddSubgroup = (Λ ⊓ W).toAddSubgroup := rfl
  have hinf2 : O.toAddSubgroup ⊓ W.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup := by
    rw [← hOW]; rfl
  rw [hinf1, hinf2] at hsplit
  have hq := LinesQuotIndex.full K n m k B Λ c
  rw [hBl] at hq

  set x := genIndex (Λ ⊓ W).toAddSubgroup (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup with hx
  set y := genIndex (Λ.map π').toAddSubgroup
    (Submodule.span (𝓞 K) (Set.range (coordProj B ∘ c))).toAddSubgroup with hy
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hxy : 0 < x * y := hsplit ▸ hpos
  have hxne : x ≠ 0 := by rintro h; rw [h, zero_mul] at hxy; exact lt_irrefl _ hxy
  have hyne : y ≠ 0 := by rintro h; rw [h, mul_zero] at hxy; exact lt_irrefl _ hxy
  unfold quotDegree subDegree
  rw [htop, Submodule.restrictScalars_top, inf_top_eq, hq, hsplit, Real.log_mul hxne hyne,
    Finset.sum_sub_distrib]
  ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualEnergyCharts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

def DualEnergyCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      ∀ k : ℕ,
        ptsIntegral (dualIdeal b)
            (pot fun j : Fin (i - 1) =>
              if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
            (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
          ∑ σ : K →+* ℂ, chartMixedEnergy ((A σ)ᴴ * F.metric σ * A σ) ((A σ)ᴴ * A σ) k

example : Σ' (b : Module.Basis Unit ℤ (dualLattice HermLattice.scaledExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧ 1 ≤ 1 ∧
      HermLattice.scaledExample.metric ≠ HermLattice.scaledExample.withStdMetric.metric :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl, fun h => by
    have h1 := congrFun (congrFun (congrFun h (Rat.castHom ℂ)) 0) 0
    simp [HermLattice.scaledExample, HermLattice.withStdMetric] at h1⟩

example : Function.Bijective (1 : Matrix (Fin 1) (Fin (1 - 1 + 1)) ℂ).mulVec := by
  have h : (1 : Matrix (Fin 1) (Fin 1) ℂ).mulVec = id := funext Matrix.one_mulVec
  exact h ▸ Function.bijective_id

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualGeomDegCharts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

def DualGeomDegCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
        ∑ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ)

example : Σ' (b : Module.Basis Unit ℤ (dualLattice HermLattice.scaledExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧ 1 ≤ 1 :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl⟩

example : Function.Bijective (1 : Matrix (Fin 1) (Fin (1 - 1 + 1)) ℂ).mulVec := by
  have h : (1 : Matrix (Fin 1) (Fin 1) ℂ).mulVec = id := funext Matrix.one_mulVec
  exact h ▸ Function.bijective_id

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStdBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualStdBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) * II Unit (PBlk i) ⊥ i (fun _ => fsMulti (PBlk i))

example : ∃ (b : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)))
    (_ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ 1 :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl⟩

example : HermLine (dualBlocks Unit) × HermLine (PBlk 1) :=
  ⟨dualLine (HermLattice.standard ℚ 1) dualBasisStandard dualEmbMatrix_standard_bijective, fsMulti (PBlk 1)⟩

example : (fsMulti (PBlk 1)).h (fun _ => 1) = 1 := by
  simp [fsMulti, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopBasisChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopBasisChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T₂ : Type) [Fintype T]
    [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b₂ : Module.Basis T₂ ℤ (dualLattice F))
    (hb₂ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b₂))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T₂) (dualIdeal b₂) i (fun _ => dualLine F b₂ hb₂) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb)

def dualBasisStandardNeg : Module.Basis (Fin 1) ℤ (dualLattice (HermLattice.standard ℚ 1)) :=
  (dualBasisStandard.map (LinearEquiv.neg ℤ)).reindex (Equiv.ofUnique Unit (Fin 1))

example : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix dualBasisStandard)) ∧
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix dualBasisStandardNeg)) ∧ 1 ≤ 1 ∧
    (dualBasisStandardNeg 0 : Fin 1 → ℚ) ≠ (dualBasisStandard () : Fin 1 → ℚ) := by
  refine ⟨dualEmbMatrix_standard_bijective, DualEmbBijective.proof ℚ 1 _ _ _, le_rfl, fun h => ?_⟩
  have h0 := congrFun h 0
  simp [dualBasisStandardNeg, dualBasisStandard_apply, oneDual] at h0
  norm_num at h0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSubLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopSubLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice ≤ F.lattice →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F'.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def twoVecExample : Fin 1 → ℚ := fun _ => 2

def HermLattice.twiceStandardExample : HermLattice ℚ 1 where
  lattice := Submodule.span (𝓞 ℚ) {twoVecExample}
  fg := Submodule.fg_span (Set.finite_singleton _)
  span_eq := by
    rw [Submodule.span_span_of_tower]
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = (x 0 / 2) • twoVecExample := by
      funext j
      fin_cases j
      simp [twoVecExample]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

theorem twiceStandardExample_le :
    HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice := by
  show Submodule.span (𝓞 ℚ) {twoVecExample} ≤ _
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have h : twoVecExample = (2 : 𝓞 ℚ) • (Pi.single 0 1 : Fin 1 → ℚ) := by
    funext j
    fin_cases j
    simp [twoVecExample, Algebra.smul_def, map_ofNat]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

example : ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T)
    (b' : Module.Basis T ℤ (dualLattice HermLattice.twiceStandardExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')) ∧
      Function.Bijective (Matrix.mulVecLin
        (dualEmbMatrix (F := HermLattice.standard ℚ 1) dualBasisStandard)) ∧
      HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice ∧ 1 ≤ 1 := by
  obtain ⟨T, hT, hdT, ⟨b'⟩⟩ := DualLatticeBasisExists.proof ℚ 1 HermLattice.twiceStandardExample
  exact ⟨T, hT, hdT, b', DualEmbBijective.proof ℚ 1 _ T b', dualEmbMatrix_standard_bijective,
    twiceStandardExample_le, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
end

