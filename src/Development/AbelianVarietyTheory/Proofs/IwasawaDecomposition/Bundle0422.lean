import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0412
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimesDisjointTwistChosenPrimesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimes_disjoint_twistChosenPrimes : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ t : TupU I U, Disjoint (X.B.primes px).vGs (Formalism.L2.Col.QE I.sel t.1) := by
  first | exact @GlobalTheory.Mem.LevDisj.places_disjoint | exact GlobalTheory.Mem.LevDisj.places_disjoint | (intros; apply GlobalTheory.Mem.LevDisj.places_disjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricCharacterInvEqInvDetBlock
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.LamQInv

theorem coarseBlockIndex_single_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

theorem lamQ_castGL_inv : ∀ {κ K : Type} [CommRing κ] [Field K] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (χ : κˣ →* Kˣ)
    (hz : (LiftBrg.castGL h y)⁻¹ * 1 ∈ Formalism.L2.Col.HQ κ n r b),
    Formalism.L2.Col.lamQ χ n r b ⟨_, hz⟩ = (χ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 y))⁻¹ := by
  intro κ K _ _ a n r b h hn y hy χ hz
  subst h
  have hc : LiftBrg.castGL (rfl : a = a) y = y := by
    ext; simp [LiftBrg.castGL]
  have hy' : y ∈ Formalism.L2.Col.blockUT a κ r [b] := by
    intro i j hij
    apply hy
    show Formalism.L2.DIV.blk2 r j < Formalism.L2.DIV.blk2 r i
    rw [← coarseBlockIndex_single_eq_twoBlock hn, ← coarseBlockIndex_single_eq_twoBlock hn]
    exact hij
  have he : (⟨_, hz⟩ : ↥(Formalism.L2.Col.HQ κ a r b)) = (⟨y, hy'⟩ : ↥(Formalism.L2.Col.HQ κ a r b))⁻¹ := by
    ext1
    simp [hc]
  rw [he, map_inv, Formalism.L2.Col.lamQ_apply]
  congr 2
  ext
  rw [Formalism.L2.Col.blkDet_val, Formalism.L2.DIV.diag_block_det_val 1 hy]
  rw [Matrix.toSquareBlock_def]
  let e : {i : Fin a // Formalism.L2.Col.coarse r [b] i.val = 1} ≃ {i : Fin a // Formalism.L2.DIV.blk2 r i = 1} :=
    Equiv.subtypeEquivRight (fun i => by rw [coarseBlockIndex_single_eq_twoBlock hn])
  exact Matrix.det_submatrix_equiv_self e (((y : GL (Fin a) κ) : Matrix (Fin a) (Fin a) κ).submatrix (Subtype.val : {i : Fin a // Formalism.L2.DIV.blk2 r i = 1} → Fin a) Subtype.val)

end GlobalTheory.Mem.R3.LiftBrg.LamQInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuous
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.IsoInteg

open ValuativeRel Filter Topology

section Val

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero_of_lt_one {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero_of_lt_one h)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') :=
    (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun y hy => hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map_le_one (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_continuous i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

theorem map_le_one (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K y ≤ 1) :
    valuation K' (i y) ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hx : x ≠ 0 := fun h0 => hx0 (by simp [h0])
  have hγ : valuation K' (i x) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact (map_ne_zero i).2 hx
  have hpos : (0 : ValueGroupWithZero K') < valuation K' (i y) := zero_lt_one.trans hc
  have hinv : valuation K' (i y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have ht := tendsto_pow_zero_of_lt_one hinv
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K').tendsto_right_iff] at ht
  obtain ⟨n, hn⟩ := (ht _ hγ).exists
  have hxy : valuation K (x * y ^ n) < 1 := by
    rw [map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' h n)) hx1
  have h2 := lt_one_of_continuous i hi hxy
  rw [map_mul, map_pow, map_mul, map_pow] at h2
  simp only [Set.mem_setOf_eq, map_pow, map_inv₀] at hn
  have hpn : (0 : ValueGroupWithZero K') < valuation K' (i y) ^ n := pow_pos hpos n
  rw [inv_pow] at hn
  have := (inv_lt_iff_one_lt_mul₀ hpn).1 hn
  exact absurd h2 (not_lt.2 this.le)

end Val

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem valued_le_one_iff_of_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → ∀ a : v.adicCompletion F, Valued.v (i a) ≤ 1 ↔ Valued.v a ≤ 1 := by
  intro F E _ _ _ _ v w i hi a
  rw [← GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w, ← GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff v]
  exact ⟨le_one_of_map_le_one i.toRingHom hi, map_le_one i.toRingHom hi⟩

end GlobalTheory.IsoInteg

end
end

