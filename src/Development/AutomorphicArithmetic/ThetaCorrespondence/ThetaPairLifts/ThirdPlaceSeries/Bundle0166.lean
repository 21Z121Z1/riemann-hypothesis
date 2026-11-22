import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0610
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0163
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0095
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0156
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0812
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0160
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0161
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0115
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0124
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0149
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0159
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0122
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0814
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0088
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0164

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksOfMassStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_frame_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) := by
  first | exact @_root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT | exact _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT | (intros; apply _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtChoice
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.Cp
namespace GlobalTheory.LocalRows
theorem at_choice_alt (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) :
    _root_.GlobalTheory.Fc.R1.SelectionLpBound 𝒜 σ ∧ _root_.GlobalTheory.Fc.R1.SelectionOrderBound 𝒜 σ ∧ R1.H_hTF 𝒜 := by
  let T : _root_.Formalism.L2.TwistSelection (D3 3 𝒜) := fun Fm hc => (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)
  have hB := _root_.GlobalTheory.bothRowsFromSiegelWeil_alt hSW (D3 3 𝒜) T
  have hL : _root_.GlobalTheory.Fc.R1.SelectionLpBound 𝒜 σ :=
    _root_.GlobalTheory.LoopRowsByName.loopRows_of_rowsFinDim_alt GlobalTheory.rowsFinDim_link (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hSW) (D3 3 𝒜) T _ (fun Fm hw => hw.2.2.1)
  exact ⟨hL, GlobalTheory.CarrierGap.offDiag (GlobalTheory.St.swxs_of_siegelWeil hSW) (GlobalTheory.rowNGP_of_siegelWeil hSW) GlobalTheory.rowsFinDim_link (D3 3 𝒜) _
    (fun Fm hc x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).locTied) hB.1 hL, hB.2⟩
theorem sLp_sO_hTF_of_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotLpCondition Q Lk ∧ _root_.GlobalTheory.Fc.R1.SlotOrderCondition Q Lk ∧ _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition Q Lk := fun hSW Q Lk =>
  ⟨Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).1, Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).2.1,
    Row.of_sel fun 𝒜 σ _ => (_root_.GlobalTheory.LocalRows.at_choice_alt hSW 𝒜 σ).2.2⟩
theorem lg1_sLp_sO_hTF : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotLpCondition S Lk) ∧ (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotOrderCondition S Lk) ∧ Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.SlotTorsionFreeCondition S Lk := fun hSW KP Q Q' Lk =>
  ⟨⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).1⟩, ⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).2.1⟩, ⟨_, largeBaseProperty_true, (_root_.GlobalTheory.LocalRows.sLp_sO_hTF_of_siegelWeil hSW _ Lk).2.2⟩⟩
end GlobalTheory.LocalRows
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTriAt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.FrameBlockTriangular
theorem blockTri_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (w.st Z).toD7.R.r) := by
  intro hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.central_frame_split_nontrivial_at_alt hL) (_root_.GlobalTheory.T.exists_residue_ne_zero_ne_one_at_member hL)) ?_
  intro K B f T w Z Wt p0 t nch n c h ad i s k hs hN s' φ b hP hres hfr
  obtain ⟨F, J, χ, ψ₀, ξ, hF, hψ, hJ, hFJ, hS⟩ := h.1 ad i s k hs hN s' φ b hP hres hfr
  have hr : 2 ≤ (w.st Z).toD7.R.r := by
    have h1 := (w.st Z).toD7.R.two_le_m
    have h2 := (w.st Z).toD7.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact GlobalTheory.T.conjugate_blockUpper_of_eigenfunction_unipotentType (t := (w.st Z).toD7.R.t) rfl hr s' φ hres (h.2 _ hP) F hF J χ ψ₀ ξ hψ hJ hFJ b hS
end GlobalTheory.FrameBlockTriangular
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CardMulSuccLeTwoMulNcolCopy
section
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace UpperTheory.Dv.Thin
theorem covers_and_of_covers_of_imp_alt {Q₁ Q₂ Q₃ : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP C : ℝ), Prop}
    (h₁ : _root_.GlobalTheory.CovTop.CoversCondition Q₁) (h₂ : _root_.GlobalTheory.CovTop.CoversCondition Q₂)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (PP C C' : ℝ),
      Q₁ Fm x hx ι p i Y PP C → Q₂ Fm x hx ι p i Y PP C' → (i : ℕ) + 1 < (Fm.D x ι).R.m → GoodCov p i Y →
        Q₃ Fm x hx ι p i Y PP C) : _root_.GlobalTheory.CovTop.CoversCondition Q₃ := by
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (h₁.and h₂).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, h1⟩, ⟨C', _, h2⟩⟩ := hh
  obtain ⟨a, h3⟩ := h1.and h2
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY =>
    h Fm x hx ι p i Y _ C C' ((h3 x hx hle ι p hp).1 i hi Y hY) ((h3 x hx hle ι p hp).2 i hi Y hY) hi hY⟩
private theorem card_mul_succ_le_two_mul_ncol_copy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    Fintype.card (Psi H) * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * GlobalTheory.RefSum.nCol Dw := by
  refine le_trans ?_ (Nat.mul_le_mul_left 2 GlobalTheory.RefSum.sum_le_nCol)
  have h1 : ∀ m : ℕ, ∑ i : Fin m, 2 * (i.val + 1) = m * (m + 1) := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last, ih]; ring
  rw [Fintype.sum_sigma]
  simp only [h1]
  rw [GlobalTheory.RawThetaSup.sum_emb_eq H, Finset.mul_sum, mul_assoc, ← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Datum.mult, if_pos τ.2, Datum.mult, if_neg (conj_not_mem τ)]
  nlinarith [sq_nonneg ((Dw.p : ℤ) - Dw.q)]
private theorem one_le_dimension_function_copy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (hp : 1 ≤ Dw.p) (hne : 0 < Fintype.card (Psi H)) {a : (E →+* ℂ) × ℕ → ℕ} (h : LastPos Dw a) :
    1 ≤ Formalism.L2.Pj.DF Dw a := by
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hne
  have hm : 0 < Dw.mult τ.1 := by rw [Datum.mult, if_pos τ.2]; exact hp
  refine (h τ.1 τ.2 hm).trans_le ?_
  unfold Formalism.L2.Pj.DF
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ : E →+* ℂ => ∑ i : Fin (Dw.mult τ), a (τ, i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ.1))
  exact Finset.single_le_sum (f := fun i : Fin (Dw.mult τ.1) => a (τ.1, i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨Dw.mult τ.1 - 1, by omega⟩)
private theorem frn_le_pow_of_bounds_copy {f r n t : ℝ} (ht : 11 ≤ t) (hf0 : 0 ≤ f) (hr0 : 0 ≤ r) (hf : f ≤ t) (hr : r ≤ t)
    (hn : n ≤ 2 * r * (f * r) + 8 * (f * r) + 8) : f * r * n ≤ t ^ 150 := by
  have h1 : n ≤ 2 * t * (t * t) + 8 * (t * t) + 8 := hn.trans (by gcongr)
  have h2 : n ≤ t ^ 4 := by
    have : 11 * t ^ 3 ≤ t ^ 4 := by rw [pow_succ' t 3]; gcongr
    have : 11 * t ^ 2 ≤ t ^ 3 := by rw [pow_succ' t 2]; gcongr
    nlinarith
  calc f * r * n ≤ f * r * t ^ 4 := by gcongr
    _ ≤ t * t * t ^ 4 := by gcongr
    _ = t ^ 6 := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
set_option maxHeartbeats 1000000 in
theorem cover_dimension_size_bounds_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → (Dom (GlobalTheory.RefSum.aOf p i u1) (GlobalTheory.RefSum.nCol (dat p i)) ∧ LastPos (dat p i) (GlobalTheory.RefSum.aOf p i u1) ∧ Nonempty (ErrX (Fm.D x ι))) ∧ 1000 ≤ (Fm.L x ι).sc.b ∧ (Fm.D x ι).R.r ≤ GlobalTheory.RefSum.nCol (dat p i) ∧ (Fm.D x ι).R.f * (Fm.D x ι).R.r * ((Fm.D x ι).R.r + 1) ≤ 2 * GlobalTheory.RefSum.nCol (dat p i) ∧ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * GlobalTheory.RefSum.nCol (dat p i) ≤ (Fm.L x ι).sc.b ∧ (Fm.D x ι).host.rdE ^ 7 ≤ (Fm.L x ι).sc.b ∧ (Fm.L x ι).sc.b ^ 16 ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ∧ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ (Fm.L x ι).sc.b ^ 70 ∧ 1 ≤ Formalism.L2.Pj.DF (dat p i) (GlobalTheory.RefSum.aOf p i u1) ∧ ((Formalism.L2.Pj.DF (dat p i) (GlobalTheory.RefSum.aOf p i u1) : ℕ) : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 ∧ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) := by
  intro hS
  refine (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) _root_.GlobalTheory.CovTop.WtShape.wtN_z)
    (_root_.GlobalTheory.RefSum.QuoShape.quo_shape_dom_lastPos_weight_eq hS)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨A, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨C3, -, h3⟩⟩ := hh
  obtain ⟨a, ha⟩ := h1.and (h2.and h3)
  refine ⟨0, le_rfl, a, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  have hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6 := (ha x hx hle ι p hp).1 i
  have hW : WtNum p i (Fm.parT x hx ι).PP := (ha x hx hle ι p hp).2.1 i
  obtain ⟨q1, -, q3, q4, q5, q6, q7, q8, -⟩ := (ha x hx hle ι p hp).2.2 i hi u1 hu
  have S := Fm.sizes x hx ι
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := (Fm.D x ι).R.two_le_m
  have a2 := (Fm.D x ι).R.m_add_three_le_k
  have a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t := (Fm.D x ι).R.rank_add_five_le
  have a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k := (Fm.D x ι).R.f_le_k
  have a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r := by
    unfold Formalism.BasicNotions.Ranks.r; omega
  have hf8 := hN.f8
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
  have hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast a5.2.2
  have ht : (11 : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)
  have hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)
  have hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)
  have hb : 1000 ≤ (Fm.L x ι).sc.b := by
    have e1 : Real.exp 10 ≤ (Fm.L x ι).sc.b := Real.exp_le_exp.2 hL10
    have e2 : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := by gcongr; linarith [Real.add_one_le_exp 1]
    rw [← Real.exp_nat_mul] at e2
    norm_num at e2
    linarith
  have hb1 : 1 ≤ (Fm.L x ι).sc.b := by linarith
  have hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) := by
    unfold szCond
    exact UpperTheory.Ram.Rd.rdE_le_cond _
  have hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι) := h1.trans hc
  have hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b :=
    Real.sqrt_le_iff.2 ⟨by linarith, le_self_pow₀ hb1 (by norm_num)⟩
  have hrdb : (Fm.D x ι).host.rdE ^ 7 ≤ (Fm.L x ι).sc.b := by
    have e1 : (Fm.D x ι).host.rdE ^ 7 ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150 :=
      (pow_le_pow_left₀ (by linarith) hc 7).trans ((pow_le_pow_right₀ hc1 (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))
    exact (e1.trans sC).trans hsb
  have htb : ((Fm.D x ι).R.t : ℝ) ^ 150 ≤ (Fm.L x ι).sc.b :=
    ((le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)).trans sC).trans hsb
  have hcard : Fintype.card (Psi p.T.Q.H) = (Fm.D x ι).R.f := Nat.card_eq_fintype_card.symm.trans hW.card
  have hcol := card_mul_succ_le_two_mul_ncol_copy (dat p i)
  rw [hcard, q3] at hcol
  have h2r := GlobalTheory.RefSum.NumPt.two_mul_rank_le_nCol (dat p i)
  rw [q3] at h2r
  have hnle : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * (Fm.D x ι).R.r * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) +
      8 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) + 8 := by exact_mod_cast GlobalTheory.LiftGaps.nCol_le p i _ _ _ hW hN
  have hfrn : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * GlobalTheory.RefSum.nCol (dat p i) ≤ (Fm.L x ι).sc.b :=
    (frn_le_pow_of_bounds_copy ht (by positivity) (by positivity) hft hrt hnle).trans htb
  have hk : (1 : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)
  have hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ) := fun k =>
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  have hg' : ∀ k, ((Fm.D x ι).host.g k : ℝ) ≤ (Fm.L x ι).sc.b ^ 35 := fun k => by
    have h0 : (0 : ℝ) < (Fm.D x ι).host.g k := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    unfold Formalism.BasicNotions.Scale.b
    rw [← Real.exp_nat_mul, ← Real.log_le_iff_le_exp h0]
    push_cast
    linarith only [hN.logg k, hL10]
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := q7.2
  have hDF := (GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) u1 (GlobalTheory.RefSum.nCol (dat p i)) _ q1 hev q4 q5 q6).2.2.2.2
  rw [hN.deg, q3, Nat.mul_div_cancel_left _ two_pos] at hDF
  refine ⟨⟨q7, q8, ⟨(Fm.ex x hx ι).errX⟩⟩, hb, by omega, hcol, hfrn, hrdb, ?_, ?_,
    one_le_dimension_function_copy _ q1 (by rw [hcard]; omega) q8, hDF.trans ?_, GlobalTheory.ThetaSizeBounds.level_ge p i Y hY (by linarith)⟩
  · push_cast
    rw [show 16 = 8 + 8 from rfl, pow_add]
    exact mul_le_mul (hg 0) (hg 1) (by positivity) (by positivity)
  · push_cast
    rw [show 70 = 35 + 35 from rfl, pow_add]
    exact mul_le_mul (hg' 0) (hg' 1) (by positivity) (by positivity)
  · have h5 : (5 : ℝ) ≤ GlobalTheory.RefSum.nCol (dat p i) := by exact_mod_cast (by omega : 5 ≤ GlobalTheory.RefSum.nCol (dat p i))
    have h6 : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * 5 ≤ (Fm.L x ι).sc.b :=
      (mul_le_mul_of_nonneg_left h5 (by positivity)).trans hfrn
    calc ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (2 * (2 * (Fm.L x ι).sc.b) + 1)
        ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (5 * (Fm.L x ι).sc.b) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * 5 * (Fm.L x ι).sc.b := by ring
      _ ≤ (Fm.L x ι).sc.b * (Fm.L x ι).sc.b := mul_le_mul_of_nonneg_right h6 (by linarith)
      _ = _ := by ring
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.thin_divisor_pivot_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ∃ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), rdU (Y.U σ) f y.1 y.2.1 ≠ 0 ∧ ∀ z : FPt (Y.U σ).X, (⟨z.1, z.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 1250)) * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨z.1, z.2.1⟩ ≤ ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ := by
  intro _ _ _ hS _
  refine _root_.UpperTheory.Dv.Thin.covers_and_of_covers_of_imp_alt (_root_.UpperTheory.Dv.Thin.cover_dimension_size_bounds_alt hS) (_root_.GlobalTheory.ThetaSizeBounds.run_params_alt hS) ?_
  intro eps Fm x hx ι p i Y PP C C' hA hB hi hY u1 hu Z σ hσ y hy hM
  obtain ⟨⟨hD, hLP, ⟨EX⟩⟩, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hA u1 hu
  obtain ⟨r1, -, -, r4⟩ := hB
  obtain ⟨hrun, -⟩ := r4 _ s8 s9
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hl : p.T.Q.l.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := p.fw.laws.toLawsM.pins.2.1.1
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split _ p.T.toCore p.fw.laws.toLawsM EX
  obtain ⟨φ, hφ, hg⟩ := cover_transport _ p.T _ Y _ _ p.fw.laws hj hY.1 _ _ hD σ hσ
  have hd := hφ ⟨y.1, y.2.1⟩ y.2.2
  have hσ' : GoodEmb p.T.Q.c (Y.resEmb σ) := Y.good_resEmb hσ
  have hla : ((p.T.U ((i : ℕ) + 1) (Y.resEmb σ)).X (φ ⟨y.1, y.2.1⟩).1).la1 (φ ⟨y.1, y.2.1⟩).2 =
      ((Y.U σ).X y.1).la1 y.2.1 := congrArg Real.sqrt hd.2
  have h0 : 0 ≤ ((Y.U σ).X y.1).firstMinimumSq y.2.1 := ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg _ y.2.2
  have hs1 : (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 ≤ 1 := by
    have h1 := (mul_le_mul_of_nonneg_right s10 h0).trans hM.le
    rw [mul_right_comm] at h1
    exact le_of_mul_le_mul_right (h1.trans_eq (one_mul _).symm) (by linarith only [s1])
  obtain ⟨f, hf, hf0, hfz⟩ := core_ratio (GlobalTheory.LevGeo.laws_core _ p.T _ p.fw.laws hj) α hα1 hα2 hD hLP s1 s2 s3 s4 s5
    (by rw [hl]; exact s6) (by rw [hl]; exact s7) s9 (by rw [hl]; exact hrun) r1 hσ' (φ ⟨y.1, y.2.1⟩).1
    (φ ⟨y.1, y.2.1⟩).2 hd.1 (by rw [hl, hd.2]; exact hs1)
  obtain ⟨g, hg', hgy⟩ := hg f hf
  refine ⟨g, hg', (hgy ⟨y.1, y.2.1⟩ y.2.2).2.mpr hf0, fun z hz => ?_⟩
  rw [(hgy ⟨z.1, z.2.1⟩ z.2.2).1, (hgy ⟨y.1, y.2.1⟩ y.2.2).1, ← hla]
  exact hfz ⟨(φ ⟨z.1, z.2.1⟩).1, (φ ⟨z.1, z.2.1⟩).2, (hφ ⟨z.1, z.2.1⟩ z.2.2).1⟩
end UpperTheory.Dv.Thin
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeliveryFourRowsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fire_realBound_thR_frames_at_all : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.summandRealBound 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.ThresholdPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.FramePointSummands 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.atAll_fourRows' | exact _root_.GlobalTheory.Fc.Ind.atAll_fourRows' | (intros; apply _root_.GlobalTheory.Fc.Ind.atAll_fourRows' <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsEigAdOfState
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.RatSide
theorem exists_eigAd_of_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∃ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig := by
  intro hL
  refine (StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.eigAd_of_rowEig_alt hL) GlobalTheory.HeckeField.Gap.rowEig_mem_fixedField).trans (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx hL' h3 h5
  classical
  refine ⟨fun j σ k Pl => if h : ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) =
      hkNorm x.m.z.R (idxOf (Dof x) j) k Pl *
        GlobalTheory.EigRows.rowEig x.r.Y (idxOf (Dof x) j) σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) then h.choose else 0,
    H.1 P x hx _ ?_⟩
  intro i σ k Pl α Rr hk hg h0
  have t2 := H.2 P x hL' h3 h5 i σ k Pl α Rr hk h0
  have hI := congrArg (fun i' : Fin (Dof x).R.m => hkNorm x.m.z.R i' k Pl *
      GlobalTheory.EigRows.rowEig x.r.Y i' σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k)) (NX.idxOf_succ (Dof x) i)
  have hex : ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) =
      hkNorm x.m.z.R (idxOf (Dof x) (i.1 + 1)) k Pl *
        GlobalTheory.EigRows.rowEig x.r.Y (idxOf (Dof x) (i.1 + 1)) σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) :=
    let ⟨c, hc⟩ := t2; ⟨c, hc.trans hI.symm⟩
  refine Eq.trans ?_ (hex.choose_spec.trans hI)
  simp only [dif_pos hex]
end GlobalTheory.HeightCounting.RatSide
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLiftAtDefiniteBadPlaces
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop
theorem definite_bad_place_lift_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  intro hP hGr hG
  have h1 := _root_.GlobalTheory.T.deformation_class_has_representative_alt hP hG
  have h2 := _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp_alt hP hGr
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  obtain ⟨Γ, _, _, V, _, _, _, π, s, ρ, Pb, lam, ψ, lamb, H, hS, hW, hl, hH, hfree, hT, hB⟩ := a1 i hi
  obtain ⟨ψ₀, hψ₀, hsh⟩ := a2 i
  have hc : ∀ k, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤
      1 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
    intro k
    obtain ⟨X, _, _, _, A, hf, hA, hpm⟩ := hfree k
    obtain ⟨n, hn, hn'⟩ := embReg_of_free_permuted_summands ℂ Γ V X ρ _ hf A hA hpm
    have hle : Pb.comap π ≤ (H k).comap π := fun g hg => (hH k (π g)).2 fun kv _ => (hW.2.1 (π g)).1 hg kv
    have h3 := card_mul_finrank_eig_of_free ℂ Γ V X ρ _ hf A hA hpm (Pb.comap π) hle lamb
    refine ⟨n, hn, ?_⟩
    rw [one_mul]
    exact_mod_cast (hn'.trans h3.symm).le
  choose n hn hn' using hc
  obtain ⟨S, hSb, hbd⟩ := GlobalTheory.BadCount.bad_part_le_locShare (Fm.D x ι) Γ V π s hS ρ Pb lam ψ hW lamb hl H hH n 1 hn hn' ψ₀ hψ₀
  have hs := hsh S hSb
  unfold BadAt
  rw [hT, hB]
  have hr : (0 : ℝ) ≤ (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := Nat.cast_nonneg _
  have hx := Real.exp_pos (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7)))
  calc _ ≤ _ := hbd
    _ ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * (Module.finrank ℂ (eig ρ (Pb.comap π) lamb) : ℝ) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_right hs hr
    _ ≤ _ := by nlinarith
end GlobalTheory.CovTop
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifts_badAt_last_of_green_cuspidal : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → BadAt p i := by
  first | exact @_root_.GlobalTheory.CovTop.definite_bad_place_lift_alt | exact _root_.GlobalTheory.CovTop.definite_bad_place_lift_alt | (intros; apply _root_.GlobalTheory.CovTop.definite_bad_place_lift_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpTh
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
def ysTh_alt (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    NExpRealS (datTw x (thTw (Dof x) th)).R (datTw x (thTw (Dof x) th)).cG ((thTw (Dof x) th).rat l.rat.S) where
  fi := (by with_unfolding_all exact (l.b.YS.fi :))
  geq := (by with_unfolding_all exact (l.b.YS.geq :))
  rho := (by with_unfolding_all exact (l.b.YS.rho :))
  chi := (by with_unfolding_all exact (l.b.YS.chi :))
  eF := (by with_unfolding_all exact (l.b.YS.eF :))
  bsup := (by with_unfolding_all exact (l.b.YS.bsup :))
  act := kc% l.b.YS.act
def exponentOfTheta (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    NExpTied (w.st (oTw x (thTw (Dof x) th)).Z).toD7 :=
  (by with_unfolding_all exact ((bsTw l.b.Bs th).exp :))
def rowPsiOfTheta (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp) :
    ∀ i : Fin (w.st (oTw x (thTw (Dof x) th)).Z).toD7.R.m,
      Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (oTw x (thTw (Dof x) th)).Z).toD7 i)
        (w.st (oTw x (thTw (Dof x) th)).Z).toD7.R.nV :=
  fun i => (by with_unfolding_all exact ((rowPsi (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z (l.mt.ad.PV ((i)))) : _))
end GlobalTheory.HeightCounting.Up
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FixAtHoldsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_fix_at' : GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt | exact _root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodRowCuspParamOfLiftStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspParam_of_definite_liftAll : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → SphericalInertData.Conclusion1 D → SphericalInertData.HypEFK D → SphericalInertData.HypCM D → (∀ j, 1 ≤ j → j ≤ D.R.m → (D.sp.V j).IsDefinite) → LiftAll D Rw → (∀ σ, RowLoc D Rw σ) → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw := by
  first | exact @_root_.GlobalTheory.ParAsm.goodRowCuspParam_of_lift_alt | exact _root_.GlobalTheory.ParAsm.goodRowCuspParam_of_lift_alt | (intros; apply _root_.GlobalTheory.ParAsm.goodRowCuspParam_of_lift_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinalityStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_chain_top_theta_lift_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceX W).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).io := by
  first | exact @_root_.GlobalTheory.BaseChain.stepX_isIo_alt | exact _root_.GlobalTheory.BaseChain.stepX_isIo_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepX_isIo_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEHasGridFldStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_field_has_lattices_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) → RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF := by
  first | exact @_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_hasGrid_fld_alt | exact _root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_hasGrid_fld_alt | (intros; apply _root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_hasGrid_fld_alt <;> assumption)
end
end

