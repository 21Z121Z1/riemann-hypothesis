import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0678
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0441
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0679
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnRealDatumFockCombinationLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0680

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicModelInvariantSubStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_model_invariant_sub : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  first | exact @GlobalTheory.SquareAgree.KFinAlg.algD_kFinite | exact GlobalTheory.SquareAgree.KFinAlg.algD_kFinite | (intros; apply GlobalTheory.SquareAgree.KFinAlg.algD_kFinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFrameOfGridLatticeLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFrameOfGridLattice_largeDepth : Big fun ch => BesP ch := by
  first | exact @GlobalTheory.FlatPlace.Big₂ | exact GlobalTheory.FlatPlace.Big₂ | (intros; apply GlobalTheory.FlatPlace.Big₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLastVectorMemHomLatticeIffIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.RowShape.LastBF

open GlobalTheory.GoodPos GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mem_completedHomLattice_iff_selfDual_source {S T : HSp D} {LS : Lat S} (LT : Lat T) (hS : IsSelfDualC S LS) (P : Pl D → Prop) (u : WO S T) :
    u ∈ latO S T (LS : Set _) (LT : Set _) P ↔
      MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  refine ⟨fun hu => ⟨latO_mxAt hu, fun y hy => latO_maps hS hu hy⟩, fun ⟨hP, hmap⟩ => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := exists_dualBasis S hS
  let yv : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)
  have hyv : ∀ i, yv i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨indP D.host.F P, indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hu : u = ∑ i, rowMul S T (s' i) (u *ᵥ yv i) := by
    ext k j
    simp only [Matrix.sum_apply, rowMul, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, yv]
    simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← TensorProduct.tmul_sum, hdual]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; exact (mul_indP (hP k j)).symm
    · intro l _ hl; rw [if_neg hl, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hu]
  exact sum_mem fun i _ => rowMul_mem (hs' i) (hmap _ (hyv i))

theorem last_of_line {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} (LW : Lat W)
    (hM : IsSelfDualC V₀ M) {x : Pl D} {m : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hW : ∀ t ∈ idAt D (· = x), colMul d.jY r t ∈ latA W LW (· = x) ↔
      incA D D.host.xi0 * cA D (m : AE D) * t ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [mem_completedHomLattice_iff_selfDual_source LW hM, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hW _ (Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.LocSD.hermAt_mem_idAt (hsd.1 y hy) _)),
    ← herm_conj V₀ y (((m : AE D) * a) • ratV z), int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1]
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D m * GlobalTheory.IwaPlace.hermAt V₀ y (a • ratV z)) * e3

theorem const_mem_latPi {S : HSp D} (i₀ : Fin S.rank) (I : FI D) (v : Pl D) (s : AE D) :
    (fun _ => s) ∈ latV S (latPi S I) (· = v) ↔ s ∈ idV I v := by
  constructor
  · intro hy
    have key : ∀ y ∈ latV S (latPi S I) (· = v), y i₀ ∈ idV I v := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, a, rfl, z, hz, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨α, hα, h0, z i₀, mem_latPi.1 hz i₀, by simp only [one_mul]⟩
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | neg a _ ha => exact neg_mem ha
    exact key _ hy
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, z, hz, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, fun _ => z, mem_latPi.2 fun _ => hz,
        funext fun i => by rw [one_mul]⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha

theorem AA_mul_rowId (j τ : ℕ) (hj : j + 2 * (τ + 1) + 2 = D.R.m) (p : Fin (D.R.m - 1 - (j + 1))) (hp : p.1 = τ + 1) :
    D.host.AA * rowId D (j + 1) p = FractionalIdeal.spanSingleton _ (star (D.host.xi0 ^ τ)) * lineId D j := by
  have hodd : Odd (j + 1) := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - τ - 2, by omega⟩
  unfold rowId tiltSc lineId stairId
  rw [if_pos hodd, if_neg (by omega), show D.R.m - 1 - (j + 1) - 1 - p.1 = τ by omega,
    show D.R.m - 1 - (j + 1) - p.1 = τ + 1 by omega, show (D.R.m - 2 - j) / 2 = τ + 1 by omega, hp,
    pow_succ D.host.AA (τ + 1)]
  ring

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem last_rowN (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) (hσ : 0 < σ) :
    ∀ a ∈ idAt D (· = v),
    (rowJac G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (G.V (.grid D.R.m (j + 1)))
        (coreL G j : Set _) (rowN G (j + 1) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  obtain ⟨τ, rfl⟩ : ∃ τ, σ = τ + 1 := ⟨σ - 1, by omega⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hL : IsSelfDualC _ (lineL D j) :=
    isSelfDualC_latPi (GlobalTheory.RowShape.nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (G.Λ (.top j)) :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  have hM : IsSelfDualC _ (coreL G j) := GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL
  have ho : OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (coreL G j) (G.Λ (.top j)) (lineL D j) v := GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v (lineId D j) (lineId_ne_zero D j)
  have hx : D.host.xi0 ^ (τ + 1) ≠ 0 := pow_ne_zero _ hξ
  have hm0 : g * (D.host.xi0 ^ (τ + 1))⁻¹ ≠ 0 := mul_ne_zero hg (inv_ne_zero hx)
  have hline : ∀ a ∈ idAt D (· = v),
      a • ratV (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ∈
        latV (GlobalTheory.SeeSaw.Model.nLine D) (lineL D j) (· = v) ↔
      (((inU _ hm0)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = v) := fun a ha => by
    refine (const_mem_latPi (S := GlobalTheory.SeeSaw.Model.nLine D) (0 : Fin 1) (lineId D j) v
      (a * incA D (D.host.xi0 ^ (τ + 1)))).trans ?_
    rw [hgen, and_iff_left (Ideal.mul_mem_right _ _ ha), inU_inv, mul_inv, inv_inv, RingHom.map_mul, mul_assoc, mul_comm a]
  have hU := line_norm (GlobalTheory.SeeSaw.Model.isLineVec_nLine hx) hL hline
  have hN : star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ⬝ᵥ
      (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => D.host.xi0 ^ (τ + 1)) =
      -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) := by
    rw [GlobalTheory.RowShape.nLine_gram, neg_mulVec, one_mulVec, dotProduct_neg]
    exact congrArg Neg.neg (Fin.sum_univ_one (fun _ : Fin 1 => star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)))
  rw [hN] at hU
  refine last_of_line _ _ _ hM (m := inU _ hm0) (Fin.last τ) rfl (fun t ht => ?_)
    (fun a ha => (orth_line _ ho _ a).symm.trans (hline a ha))
  have hc : colMul (rowJac G (j + 1) (by omega) (τ + 1) (by omega)).jY (Fin.last τ) t =
      fun k => t * incA D ((G.rowDec (j + 1) (by omega)).a k
        (Fin.castLE (by omega : τ + 1 ≤ D.R.m - 1 - (j + 1)) (Fin.last τ)).rev) := by
    funext k
    rfl
  have hs : star (D.host.xi0 ^ τ) ≠ 0 := star_ne_zero.2 (pow_ne_zero _ hξ)
  rw [hc, rowN, dif_pos (by omega), (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2,
    AA_mul_rowId j τ hj _ (by simp only [Fin.val_rev, Fin.val_castLE, Fin.val_last]; omega),
    idV_spanSingleton_mul_iff D v _ _ hs t, and_iff_left ht, hgen, and_iff_left (Ideal.mul_mem_left _ _ ht),
    hU _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ht)), inU_val]
  have e : g * (D.host.xi0 ^ (τ + 1))⁻¹ * -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) *
      (g⁻¹ * (star (D.host.xi0 ^ τ))⁻¹) = D.host.xi0 := by
    rw [pow_succ D.host.xi0 τ, star_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    have := pow_ne_zero τ hξ
    field_simp
  have e' := congrArg (incA D) e
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul (incA D) g⁻¹] at e'
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D (incA D (g * (D.host.xi0 ^ (τ + 1))⁻¹)) * t) * e'

end GlobalTheory.RowShape.LastBF

theorem GlobalTheory.RowShape.big_last_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj v hσ =>
    GlobalTheory.RowShape.LastBF.last_rowN ch.G j σ hj v hσ⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedFunctionConvergesContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.JacMean

theorem handP_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ B.L Φ₀ →
    IsThetaFunO ψ J.W B.V Φ →
    (∃ (C : ℝ) (a : ℕ), ∀ h h₁, ‖handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁‖ ≤ C * (quotHeight B.A h₁ * height B.V h) ^ a) ∧
    Continuous fun q : GA D B.V × GA D B.A => handP s vL omz φ Φ₀ (flFB s (s.om (1, q.1) Φ)) q.2 := by
  intro D ψ σ J B s vL χ χz omz homz φ Φ₀ Φ hφ hΦ₀ hΦ
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  have hfin : J.v0.μ J.v0.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨K, hK⟩ : ∃ K : GA D B.V → GA D J.W₀ → GA D B.A → ℂ, K = fun h h₀ h₁ => contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := ⟨_, rfl⟩
  have hKc : Continuous fun q : GA D B.V × GA D J.W₀ × GA D B.A => K q.1 q.2.1 q.2.2 := by
    subst hK; exact GlobalTheory.T.continuous_pairedKernel_flatMap_weilTranslate D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨C, a, hKp⟩ : ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖K h h₀ h₁‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
    subst hK; exact GlobalTheory.T.fourierJacobiToBessel_pairedKernel_heightBound D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  have hKi : ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, K h (γ * h₀) h₁ = K h h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, K h h₀ (γ * h₁) = K h h₀ h₁ := by
    subst hK; exact GlobalTheory.T.flatKernelPairing_rationalPoints_invariant D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  have hKq : ∀ h h₀ h₁, ‖K h h₀ h₁‖ ≤ |C| * 4 ^ a * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) ^ a := by
    intro h h₀ h₁
    obtain ⟨γ, hγ, e1⟩ := exists_height_le_two_mul_quotHeight J.W₀ h₀
    obtain ⟨δ, hδ, e2⟩ := exists_height_le_two_mul_quotHeight B.A h₁
    have k1 : K h h₀ h₁ = K h (γ * h₀) (δ * h₁) := by
      rw [(hKi h).2 δ hδ (γ * h₀) h₁, (hKi h).1 γ hγ h₀ h₁]
    rw [k1]
    have p1 := height_pos J.W₀ (γ * h₀)
    have p2 := height_pos B.A (δ * h₁)
    have p3 := height_pos B.V h
    have q0 := quotHeight_pos J.W₀ h₀
    have q1 := quotHeight_pos B.A h₁
    calc ‖K h (γ * h₀) (δ * h₁)‖ ≤ C * (height J.W₀ (γ * h₀) * height B.A (δ * h₁) * height B.V h) ^ a := hKp _ _ _
      _ ≤ |C| * ((2 * quotHeight J.W₀ h₀) * (2 * quotHeight B.A h₁) * height B.V h) ^ a :=
          mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (mul_pos (mul_pos p1 p2) p3).le
            (mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 p2.le (by linarith)) p3.le) a)
            (pow_pos (mul_pos (mul_pos (by linarith) (by linarith)) p3) a).le (abs_nonneg C)
      _ = _ := by
          rw [show 2 * quotHeight J.W₀ h₀ * (2 * quotHeight B.A h₁) * height B.V h =
            4 * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) by ring, mul_pow]; ring
  obtain ⟨Cφ, hCφ⟩ := hφ.decay a
  have hpt : ∀ h h₀ h₁, ‖φ h₀ * K h h₀ h₁‖ ≤ |Cφ| * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a := by
    intro h h₀ h₁
    rw [norm_mul]
    calc ‖φ h₀‖ * ‖K h h₀ h₁‖ ≤ ‖φ h₀‖ * (|C| * 4 ^ a * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) ^ a) :=
          mul_le_mul_of_nonneg_left (hKq h h₀ h₁) (norm_nonneg _)
      _ = (‖φ h₀‖ * quotHeight J.W₀ h₀ ^ a) * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a := by
          rw [mul_pow]; ring
      _ ≤ |Cφ| * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((hCφ h₀).trans (le_abs_self _)) (by positivity))
            (pow_pos (mul_pos (quotHeight_pos B.A h₁) (height_pos B.V h)) a).le
  have hPeq : ∀ h h₁, handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁ = ∫ h₀ in J.v0.𝓕, φ h₀ * K h h₀ h₁ ∂J.v0.μ := by
    subst hK; intro _ _; rfl
  refine ⟨⟨|Cφ| * (|C| * 4 ^ a) * (J.v0.μ J.v0.𝓕).toReal, a, fun h h₁ => ?_⟩, ?_⟩
  · rw [hPeq]
    have := norm_setIntegral_le_of_norm_le_const hfin fun h₀ _ => hpt h h₀ h₁
    refine this.trans (le_of_eq ?_)
    simp only [Measure.real]
    ring
  · have hmeas : ∀ q : GA D B.V × GA D B.A, AEStronglyMeasurable (fun h₀ => φ h₀ * K q.1 h₀ q.2) (J.v0.μ.restrict J.v0.𝓕) :=
      fun q => (hφ.continuous.mul (hKc.comp ((continuous_const.prodMk (continuous_id.prodMk continuous_const))))).aestronglyMeasurable
    have hc2 : Continuous fun q : GA D B.V × GA D B.A => (height B.A q.2 * height B.V q.1) ^ a :=
      (((continuous_height B.A).comp continuous_snd).mul ((continuous_height B.V).comp continuous_fst)).pow a
    refine (continuous_congr fun q : GA D B.V × GA D B.A => hPeq q.1 q.2).2 ?_
    refine continuous_iff_continuousAt.2 fun q₀ => ?_
    refine continuousAt_of_dominated (bound := fun _ => |Cφ| * (|C| * 4 ^ a) * ((height B.A q₀.2 * height B.V q₀.1) ^ a + 1))
      (.of_forall hmeas) ?_ (integrable_const _) ?_
    · filter_upwards [hc2.continuousAt.eventually (gt_mem_nhds (lt_add_one _))] with q hq
      refine .of_forall fun h₀ => (hpt q.1 h₀ q.2).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact (pow_le_pow_left₀ (mul_pos (quotHeight_pos B.A q.2) (height_pos B.V q.1)).le
        (mul_le_mul_of_nonneg_right (quotHeight_le_height B.A q.2) (height_pos B.V q.1).le) a).trans hq.le
    · exact .of_forall fun h₀ => (continuous_const.mul (hKc.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))).continuousAt

theorem conclusion₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → (∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 (besFun ψ 1 B.d B.o B.ζ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G))) ∧ Continuous fun h => B.per ψ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G) := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ Φ hφ hG hΦ₀ hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨⟨C, a, hP⟩, hPc⟩ := handP_law D ψ σ J B s vL χ χz omz homz φ Φ₀ Φ hφ hΦ₀ hΦ
  set P : GA D B.V → GA D B.A → ℂ := fun h h₁ => handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁ with hPdef
  obtain ⟨C1, a1, h1⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D B.V B.V₀ σ B.d
  obtain ⟨C2, a2, h2⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
  obtain ⟨C3, h3⟩ := (GlobalTheory.RTransDecay.rapidDec_rTrans D B.V G hG).2 (a1 * a2 * a)

  set bd : GA D B.V → ℝ := fun h => |C| * height B.V h ^ a * ((|C2| * |C1| ^ a2) ^ a * (|C3| * height B.V h ^ (a1 * a2 * a))) with hbd
  have hbound : ∀ h (h₁ : GA D B.A) (n : flagN B.d), ‖besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G) h₁ n‖ ≤ bd h := by
    intro h h₁ n
    have hg := h1 n.1 n.2 (B.o.emb (h₁, 1))
    have hq := (h2 h₁).1
    set g : GA D B.V := n.1 * embA B.d B.o h₁ with hgdef
    have hge : n.1 * B.d.emb0 (B.o.emb (h₁, 1)) = g := rfl
    rw [hge] at hg
    have q0 := quotHeight_pos B.V₀ (B.o.emb (h₁, 1))
    have qg := quotHeight_pos B.V g
    have qa := quotHeight_pos B.A h₁
    have ht := height_pos B.V h
    have hA : quotHeight B.A h₁ ≤ |C2| * |C1| ^ a2 * quotHeight B.V g ^ (a1 * a2) := by
      calc quotHeight B.A h₁ ≤ C2 * quotHeight B.V₀ (B.o.emb (h₁, 1)) ^ a2 := hq
        _ ≤ |C2| * (|C1| * quotHeight B.V g ^ a1) ^ a2 :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ q0.le (hg.1.trans
              (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos qg a1).le)) _) (pow_pos q0 a2).le (abs_nonneg _)
        _ = _ := by rw [mul_pow, ← pow_mul]; ring
    have hGg := h3 g h
    have hPb := hP h h₁
    have hnpsi : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) n.1‖ = 1 := hψ.1.2.1 _
    have e1 : ‖besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G) h₁ n‖ = ‖P h h₁‖ * ‖G (g * h)‖ := by
      simp only [besFun, rTrans, norm_mul, norm_star, hnpsi, mul_one]; rfl
    rw [e1]
    calc ‖P h h₁‖ * ‖G (g * h)‖ ≤ (|C| * (quotHeight B.A h₁ * height B.V h) ^ a) * ‖G (g * h)‖ :=
          mul_le_mul_of_nonneg_right (hPb.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_pos (mul_pos qa ht) a).le)) (norm_nonneg _)
      _ ≤ (|C| * ((|C2| * |C1| ^ a2 * quotHeight B.V g ^ (a1 * a2)) * height B.V h) ^ a) * ‖G (g * h)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos qa ht).le
            (mul_le_mul_of_nonneg_right hA ht.le) a) (abs_nonneg C)) (norm_nonneg _)
      _ = |C| * height B.V h ^ a * ((|C2| * |C1| ^ a2) ^ a * (‖G (g * h)‖ * quotHeight B.V g ^ (a1 * a2 * a))) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
      _ ≤ bd h :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGg.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_pos ht _).le)) (by positivity)) (mul_nonneg (abs_nonneg _) (pow_pos ht a).le)
  have hcont : Continuous fun q : GA D B.V × (GA D B.A × flagN B.d) => besFun ψ 1 B.d B.o B.ζ (P q.1) (rTrans q.1 G) q.2.1 q.2.2 := by
    have hn : Continuous fun q : GA D B.V × (GA D B.A × flagN B.d) => (q.2.2 : GA D B.V) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact ((hPc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
      (hG.continuous.comp ((hn.mul (B.d.continuous_embed.comp (B.o.continuous_emb.comp ((continuous_fst.comp continuous_snd).prodMk continuous_const)))).mul continuous_fst))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))
  have hint : ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 (besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G)) := by
    intro h
    refine Integrable.of_bound ?_ (bd h) (.of_forall fun p => hbound h p.1 p.2)
    exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine ⟨hint, ?_⟩
  have heq : ∀ h, B.per ψ (P h) (rTrans h G) = ∫ p, Function.uncurry (besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G)) p
      ∂((B.vA.μ.restrict B.vA.𝓕).prod (B.vN.ν.restrict B.vN.𝓝)) := fun h => by
    rw [integral_prod _ (hint h)]; rfl
  refine (continuous_congr heq).2 ?_
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  have hbc : Continuous bd := by
    exact (continuous_const.mul ((continuous_height B.V).pow a)).mul (continuous_const.mul (continuous_const.mul ((continuous_height B.V).pow _)))
  refine continuousAt_of_dominated (bound := fun _ => bd h₀ + 1) ?_ ?_ (integrable_const _) ?_
  · exact .of_forall fun h => (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hbc.continuousAt.eventually (gt_mem_nhds (lt_add_one (bd h₀)))] with h hh
    exact .of_forall fun p => (hbound h p.1 p.2).trans hh.le
  · exact .of_forall fun p => (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt

end GlobalTheory.JacMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnAtReadsPlacePartLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnAt_reads_placePart_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (w : locPl ch.G t) (eL e' : AE D), IsIdemSum eL {w.1} → e' * eL = eL → ∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), ch.S.colAt t w.1 (fun j => e' • u j) = ch.S.colAt t w.1 u := by
  first | exact @GlobalTheory.ColAtPart.colAt_smul_of_mul_idem | exact GlobalTheory.ColAtPart.colAt_smul_of_mul_idem | (intros; apply GlobalTheory.ColAtPart.colAt_smul_of_mul_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnCombinationsComposeLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnCombinations_compose_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (c : Combs ch.G) (c' c'' : ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ j, j < D.R.m → ∀ f, comb ch.W.ψ _ _ (c'' j) f = comb ch.W.ψ _ _ (c.1 j) (comb ch.W.ψ _ _ (c' j) f)) → ∀ (C : BiFam ch.G) (u : ColPt ch.G), evT (combC ch.W c (combC ch.W (c', 0) C)) 1 u 0 = evT (combC ch.W (c'', 0) C) 1 u 0 := by
  first | exact @GlobalTheory.ColComb.main | exact GlobalTheory.ColComb.main | (intros; apply GlobalTheory.ColComb.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnFlatTensorExpansionLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnFlatTensor_expansion_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (eL : AE D), IsIdemSum eL {w.1} → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∃ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G), (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = eL ∧ IsCombOf ch.W (d i j) ((c i).1 j)) ∧ ∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf eL (y j)) → ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 y) 0 := by
  first | exact @GlobalTheory.LocAsm.colFlat_expansion | exact GlobalTheory.LocAsm.colFlat_expansion | (intros; apply GlobalTheory.LocAsm.colFlat_expansion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnRealDatumFockCombinationLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnRealDatum_fockCombination_largeDepth : Big fun ch => ColFock ch := by
  first | exact @GlobalTheory.ColFockPf.colFock_big | exact GlobalTheory.ColFockPf.colFock_big | (intros; apply GlobalTheory.ColFockPf.colFock_big <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CombinationProducesDatumAllLocalModelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combination_produces_datum_all_localModels : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, IsHalf (p.e + cA D p.e) u) → ∀ T₀, p.IsModel ψ FS FT T₀ → ∀ O Ξ : SB (Matrix Y Y' k), IsOne O → T₀ O ≠ 0 → T₀ Ξ = comb ψ S T c (T₀ O) → p.IsCombAt ψ FS FT c Ξ.1 := by
  first | exact @GlobalTheory.FlatPlace.isCombAt_of_one | exact GlobalTheory.FlatPlace.isCombAt_of_one | (intros; apply GlobalTheory.FlatPlace.isCombAt_of_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definitePeriod_depends_on_productFunction : Big fun ch => TensAt ch := by
  first | exact @GlobalTheory.RowVal.tensAt_big | exact GlobalTheory.RowVal.tensAt_big | (intros; apply GlobalTheory.RowVal.tensAt_big <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth : Big fun ch => LocP ch := by
  first | exact @GlobalTheory.FlatPlaceLoc.localization₂ | exact GlobalTheory.FlatPlaceLoc.localization₂ | (intros; apply GlobalTheory.FlatPlaceLoc.localization₂ <;> assumption)
end

