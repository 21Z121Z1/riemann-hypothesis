import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointStarProductNonvanishing
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0050
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0091
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0089
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MiStar2AtRealisation
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
namespace GlobalTheory.MiTop.AtReal
open Formalism.IndefR.Links
section Gen
variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}
end Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem dc_heq_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : HEq (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc W.P.Dc :=
  (congr_arg_heq W.Dcf W.Q.zs).trans (heq_of_eq W.Q.dc)
theorem df1_fc_eq_side3 (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1 = W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs :=
  congrArg (W.P.A3.side3 W.P.Ps W.P.ψs) W.Q.zs
theorem exists_word_heq_of_mem_dc (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (m : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Mem) : ∃ u, HEq m (W.P.I.wU u) := by
  obtain ⟨m', hm⟩ := cols_mem (_root_.GlobalTheory.MiTop.AtReal.df1_fc_eq_side3 W) (_root_.GlobalTheory.MiTop.AtReal.dc_heq_alt W) m
  refine ⟨W.Q.wdD m', ?_⟩
  rw [W.Q.wU_wdD]; exact hm
end GlobalTheory.MiTop.AtReal
namespace GlobalTheory.MiTop.AtReal
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem anchor_word_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (z : GA D (D.sp.Y 0)) (u : D.what₂.Word) (d : _root_.GlobalTheory.MiTop.BottomData W u) (v : (W.Q.Rl.MY 0).Vec)
    (U : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) (r : ℝ) (c : W.P.T → ℂ) (hR : _root_.GlobalTheory.MiTop.BottomRelation W z d)
    (hA : (∀ φ, ∃ C, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ) ∧ (∀ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, ∀ C, ∃ b, _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W, _root_.GlobalTheory.MiTop.IsColumnForm W u C φ ∧ _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0)
    (hr : 0 < r) (hU : ∀ φ, ‖U φ‖ = r * ‖φ‖) (hRel : d.Rel U c)
    (hrow : ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.MiTop.rowFormOfTuple W t F ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W) :
    ∃ (R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u) (p b₀ : ℂ), p ≠ 0 ∧ b₀ ≠ 0 ∧
      ∀ t (φ : D.what₂.Mu u) (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL)
        (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), HEq F F' → ∀ C b, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R (U φ)) →
        _root_.GlobalTheory.MiTop.IsPairing' W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (_root_.GlobalTheory.MiTop.rowFormOfTuple W t F' (PiTensorProduct.tprod ℂ v)) C b →
        c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F)) * b₀ = p * b := by
  obtain ⟨R, hR⟩ := hR
  obtain ⟨-, -, φ₁, C₀, b₀, T₀, hT₀, hC₀, hP₀, hb₀⟩ := hA
  have hinj : Function.Injective U := by
    rw [injective_iff_map_eq_zero]
    intro φ h
    have h1 := hU φ
    rw [h, norm_zero] at h1
    exact norm_eq_zero.1 ((mul_eq_zero.1 h1.symm).resolve_left hr.ne')
  obtain ⟨φ₀, hφ₀⟩ := LinearMap.injective_iff_surjective.1 hinj (R.symm φ₁)
  have hC₁ : _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ (R (U φ₀)) := by rw [hφ₀, LinearIsometryEquiv.apply_symm_apply]; exact hC₀
  obtain ⟨p, hp⟩ := hRel T₀ hT₀
  refine ⟨R, p φ₀, b₀, fun h0 => hb₀ ?_, hb₀, fun t φ F F' hF C b hC hb => ?_⟩
  · obtain ⟨F, hF⟩ := heq_fin' (α := D.what₂.LL)
      (congrArg (fun Df => DefSide.nV Df W.P.A3.A.μ0) (_root_.GlobalTheory.MiTop.AtReal.df1_fc_eq_side3 W)).symm (fun _ => 0)
    have h1 := hp φ₀ φ₀ W.P.A3.A.μ0 F _ hF 1 0 (by rw [h0, mul_zero, zero_mul, add_zero])
    have h2 := hR (U φ₀) (U φ₀) T₀ hT₀ T₀ hT₀ 1 0
      (fun y w => by have h3 := h1 y w; rw [zero_mul] at h3 ⊢; exact h3) _ C₀ C₀ b₀ b₀ hC₁ hC₁ hP₀ hP₀
    rwa [one_mul, zero_mul, add_zero] at h2
  · have h1 := hp φ₀ φ t F F' hF
      (c t * D.what₂.perCol u (W.P.I.tup t) φ (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F))) (-p φ₀) (by ring)
    have h2 := hR (U φ₀) (U φ) T₀ hT₀ _ (hrow t F') _ _ h1 _ C₀ C b₀ b hC₁ hC hP₀ hb
    linear_combination h2
end GlobalTheory.MiTop.AtReal
namespace GlobalTheory.MiTop
open Formalism.IndefR.Links GlobalTheory.MiTop.AtReal
set_option maxHeartbeats 1000000 in
theorem miStar2_at_realisation_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → (∀ t F, (_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) ∈ (_root_.GlobalTheory.MiS.packageCoefficientSpace W).EEl true) → _root_.GlobalTheory.MiTop.JointCondition W → PuNZ D → (_root_.GlobalTheory.MiS.packageCoefficientSpace W).MIstar2 (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB hΘ hJ hPu
  classical
  obtain ⟨z, hzf, hzc, hw⟩ := hJ
  choose d U r c hpin hr hUn hUC hRel using hw
  obtain ⟨V₀, hV₀⟩ := _root_.GlobalTheory.MiTop.exists_isShift_of_center_alt W hB z hzf hzc
  have hMt := _root_.GlobalTheory.MiTop.botHyp_match_alt W hB
  have hS : parB (Ptw D) (min 0 D.R.m) = parB (Ptw D) 0 := by simp
  obtain ⟨v, hv⟩ := GlobalTheory.Core.Mi.exists_conjVec hDS D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) hS hMt.2.1 hB.gap hB.idE
  obtain ⟨κ, hκ, hPF⟩ := _root_.GlobalTheory.T.pairForm_of_conjVec_of_botHyp hDS hCR W hB v hv
  have hCC := _root_.GlobalTheory.MiTop.colCrd_of_real_pack W
  have hrow : ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL), _root_.GlobalTheory.MiTop.rowFormOfTuple W t F ∈ _root_.GlobalTheory.MiTop.BaseRowSpace W :=
    fun t F => hMt.2.2.2.2.2 _ (hΘ t F)
  have hanc := fun u => _root_.GlobalTheory.T.conjugate_vector_central_twist_alt hDS hCR W hB hPu z hzf hzc v hv u
  have hword := fun u => _root_.GlobalTheory.MiTop.AtReal.anchor_word_alt W z u (d u) v (U u) (r u) (c u)
    (_root_.GlobalTheory.T.botRel_of_botHyp_of_pin_central hDS hCR W hB z hzf hzc u (d u) (hpin u)) (hanc u) (hr u) (hUn u) (hRel u) hrow
  choose R p b₀ hp hb₀ hid using hword
  have key : ∀ m : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Mem, ∃ (Um : Matrix (Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.a m)) (Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.a m)) ℂ) (cm : W.P.A3.fam3.base3.Tup → ℂ),
      (∀ x, fnorm ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Xc m W.P.A3.fam3.base3.v0) (Um.mulVec x) = fnorm ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Xc m W.P.A3.fam3.base3.v0) x) ∧
      (∀ t, cm t ≠ 0) ∧ (∀ w (k : D.what₂.LL), W.P.A3.fam3.base3.v0.embedding k = cm ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).μ w) / cm W.P.A3.fam3.base3.μ0 → vw w k = 0) ∧
      ∃ pp bb : ℂ, pp ≠ 0 ∧ bb ≠ 0 ∧ ∀ t (φ : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.a m) → D.what₂.LL) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
        cm t * W.P.A3.fam3.base3.v0.embedding ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Dc.Pt m t φ F) * bb =
          pp * ⟪W.Q.sEE (Tw.map (Formalism.L2.SG.JoinSI.twQ W.P) V₀ ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)))), (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Sp.Pu m (Um.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ))⟫_ℂ := by
    intro m
    obtain ⟨u, hm⟩ := _root_.GlobalTheory.MiTop.AtReal.exists_word_heq_of_mem_dc W m
    obtain ⟨ha, hXc, hPt⟩ := cols_heq (_root_.GlobalTheory.MiTop.AtReal.df1_fc_eq_side3 W) (_root_.GlobalTheory.MiTop.AtReal.dc_heq_alt W) hm
    obtain ⟨hbij, hrat, r', hr', hnorm⟩ := hCC u
    let s := Formalism.L2.SG.JoinSI.twQ W.P
    let cL : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) →ₗ[ℂ] D.what₂.Mu u :=
      { toFun := _root_.GlobalTheory.MiTop.columnOfCoordinates W u
        map_add' := fun x y => by simp only [_root_.GlobalTheory.MiTop.columnOfCoordinates, Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := fun a x => by simp only [_root_.GlobalTheory.MiTop.columnOfCoordinates, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply] }
    let eC : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) ≃ₗ[ℂ] D.what₂.Mu u := LinearEquiv.ofBijective cL hbij
    have heC : ∀ x, eC x = _root_.GlobalTheory.MiTop.columnOfCoordinates W u x := fun x => rfl
    let A : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := ((r u : ℂ))⁻¹ • (((R u).toLinearEquiv : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u) ∘ₗ U u)
    have hAap : ∀ φ, A φ = R u (U u (((r u : ℂ))⁻¹ • φ)) := fun φ => by
      show ((r u : ℂ))⁻¹ • R u (U u φ) = _
      rw [map_smul, map_smul]
    have hA : ∀ φ, ‖A φ‖ = ‖φ‖ := fun φ => by
      show ‖((r u : ℂ))⁻¹ • R u (U u φ)‖ = ‖φ‖
      rw [norm_smul, LinearIsometryEquiv.norm_map, hUn u, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr u).le,
        ← mul_assoc, inv_mul_cancel₀ (hr u).ne', one_mul]
    let f' : (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) →ₗ[ℂ] (Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) :=
      { toFun := fun y => Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s y))))
        map_add' := fun x y => by simp only [Formalism.L2.SG.JoinSI.cjv_add, map_add]
        map_smul' := fun a x => by
          simp only [Formalism.L2.SG.JoinSI.cjv_smul, map_smul, Formalism.IndefR.Links.cj_cj, RingHom.id_apply] }
    obtain ⟨M, hM⟩ := heq_mat ha (LinearMap.toMatrix' f')
    have hcj : ∀ a : D.what₂.LL, W.P.A3.fam3.base3.v0.embedding a = Formalism.IndefR.Links.cj s (D.what₂.embLL a) :=
      _root_.Formalism.L2.SG.JoinSI.embedding_eq_cj_twQ_embLL W.Q
    have hr0 : ((r u : ℂ))⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 (hr u).ne')
    refine ⟨M, fun t => Formalism.IndefR.Links.cj s (c u t), ?_, fun t => (map_ne_zero _).2 ((hUC u).1 t), ?_,
      Formalism.IndefR.Links.cj s (p u), Formalism.IndefR.Links.cj s (κ * ((r u : ℂ))⁻¹ * b₀ u), (map_ne_zero _).2 (hp u),
      (map_ne_zero _).2 (mul_ne_zero (mul_ne_zero hκ hr0) (hb₀ u)), ?_⟩
    · intro x
      obtain ⟨x', hx⟩ := heq_fin ha x
      rw [heq_fnorm ha (hXc _) (heq_mulVec ha hM hx), heq_fnorm ha (hXc _) hx, LinearMap.toMatrix'_mulVec]
      show fnorm _ (Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s x'))))) = _
      conv_rhs => rw [← Formalism.L2.SG.JoinSI.cjv_cjv s x']
      rw [hnorm, hnorm, ← heC, ← heC, LinearEquiv.apply_symm_apply, hA]
    · intro w k hk
      apply (hUC u).2 w k
      rw [hcj, ← map_div₀] at hk
      exact (Formalism.IndefR.Links.cj s).injective hk
    · intro t φ F
      obtain ⟨φ', hφ⟩ := heq_fin ha φ
      have hnV : (W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t = (W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t :=
        congrArg (fun Df => DefSide.nV Df t) (_root_.GlobalTheory.MiTop.AtReal.df1_fc_eq_side3 W)
      obtain ⟨F'', hF⟩ := heq_fin hnV F
      rw [hPt t φ φ' F F'' hφ hF, hcj, hB.hyp.2.2.1 u t (hB.used t) φ' F'']
      set ψ := D.jN u (W.P.I.eNu u φ') with hψ
      have hvec : HEq (M.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ)) (Formalism.L2.SG.JoinSI.cjv s (eC.symm (A ψ))) := by
        refine (heq_mulVec ha hM (heq_cpt _ ha hφ)).trans (heq_of_eq ?_)
        rw [LinearMap.toMatrix'_mulVec]
        show Formalism.L2.SG.JoinSI.cjv s (eC.symm (A (eC (Formalism.L2.SG.JoinSI.cjv s (cpt W.P.A3.fam3.base3.v0.embedding φ'))))) = _
        have e1 : Formalism.L2.SG.JoinSI.cjv s (cpt W.P.A3.fam3.base3.v0.embedding φ') = cpt D.what₂.embLL φ' := by
          funext i
          show Formalism.IndefR.Links.cj s (W.P.A3.fam3.base3.v0.embedding (φ' i)) = D.what₂.embLL (φ' i)
          rw [hcj, Formalism.IndefR.Links.cj_cj]
        rw [e1, heC, hrat]
      have hx' : HEq (eC.symm (A ψ)) (Formalism.L2.SG.JoinSI.cjv s (M.mulVec (cpt W.P.A3.fam3.base3.v0.embedding φ))) := by
        have h2 := heq_cjv s ha hvec
        rw [Formalism.L2.SG.JoinSI.cjv_cjv] at h2
        exact h2.symm
      rw [← Formalism.L2.SG.JoinSI.cjv_cjv s (M.mulVec _)]
      obtain ⟨T, hTc⟩ := (hanc u).1 (_root_.GlobalTheory.MiTop.columnOfCoordinates W u (eC.symm (A ψ)))
      obtain ⟨b, hb⟩ := (hanc u).2.1 (_root_.GlobalTheory.MiTop.rowFormOfTuple W t F) (hrow t F) T
      have hE := (hV₀.2.2 _ (hΘ t F))
      have hPair : _root_.GlobalTheory.MiTop.IsPairing' W u (show GA D (D.sp.Y 0) from W.Q.tS)
          (_root_.GlobalTheory.MiTop.rowFormOfVector W (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) s V₀ ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F))))) (PiTensorProduct.tprod ℂ v)) T b := by
        obtain ⟨φL, hφL, hbL⟩ := hb
        refine ⟨φL, hφL.trans (Filter.EventuallyEq.of_eq ?_), hbL⟩
        funext x
        refine Eq.trans ?_ (congrFun (hV₀.1 (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F))) (PiTensorProduct.tprod ℂ v))
          ((iotaX W.S.X W.Q.instEq).symm x * (show GA D (D.sp.Y 0) from W.Q.tS))).symm
        refine congrArg (_root_.GlobalTheory.MiTop.rowFormOfTuple W t F (PiTensorProduct.tprod ℂ v)) ?_
        show (iotaX W.S.X W.Q.instEq).symm x * (z * (show GA D (D.sp.Y 0) from W.Q.tS)) =
          (iotaX W.S.X W.Q.instEq).symm x * (show GA D (D.sp.Y 0) from W.Q.tS) * z
        rw [mul_assoc, Subgroup.mem_center_iff.1 hzc]
      have hpair := hPF (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) s V₀ ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).Θ t ((_root_.GlobalTheory.MiS.packageCoefficientSpace W).jR t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F))))
        hE u m hm _ _ hx' T b hTc hPair
      refine Eq.trans ?_ (congrArg (fun a => Formalism.IndefR.Links.cj s (p u) * a) hpair.symm)
      show Formalism.IndefR.Links.cj s (c u t) * _ * _ = Formalism.IndefR.Links.cj s (p u) * Formalism.IndefR.Links.cj s (κ * b)
      have hcolR : _root_.GlobalTheory.MiTop.IsColumnForm W u T (R u (U u (((r u : ℂ))⁻¹ • ψ))) := by
        rw [← hAap]; unfold _root_.GlobalTheory.MiTop.IsColumnForm at hTc ⊢; rw [hTc, ← heC, LinearEquiv.apply_symm_apply]
      have hid' := hid u t (((r u : ℂ))⁻¹ • ψ) F'' F hF.symm T b hcolR hb
      rw [GlobalTheory.ExpAtTypePrimes.perCol_smul] at hid'
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      linear_combination κ * hid'
  choose Um cm hUm hc0 hcU hAn using key
  exact GlobalTheory.MiTop.miStar2_of_anchored (_root_.GlobalTheory.MiS.packageCoefficientSpace W) (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs) W.Q.sEE (Tw.map (E := W.Q.Rl.HE.H) (F := W.Q.Rl.HE.H) (Formalism.L2.SG.JoinSI.twQ W.P) V₀) Um cm
    ⟨fun e he => ⟨hV₀.2.2 (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e) he, hV₀.2.1 (Tw.out (s := Formalism.L2.SG.JoinSI.twQ W.P) (E := W.Q.Rl.HE.H) e)⟩, hUm⟩ hAn ⟨hc0, hcU⟩
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoAtChosen
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem onto_at_chosen_alt : _root_.GlobalTheory.BigOn.SurjectiveOntoX → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
    (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ →
    EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 σ :=
  fun h 𝒜 σ hD hR hM =>
    _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigOn.More p)
      (fun C CH _ _ _ p => (p.S false).ON (p.N C CH)) h 𝒜 σ hD hR hM
end GlobalTheory.Fc.Ind
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfHypStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parOf_hyp_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Hyp := by
  first | exact @_root_.GlobalTheory.ExpTie.parOf_hyp_alt | exact _root_.GlobalTheory.ExpTie.parOf_hyp_alt | (intros; apply _root_.GlobalTheory.ExpTie.parOf_hyp_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PermSt
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FramePerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end Point
theorem permSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → PermAt p j P w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ j P W _ _ w _ _ _ => permAt p j P w⟩⟩⟩
end GlobalTheory.FramePerm
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QnNotMem
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
namespace GlobalTheory.ThmAUpper
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ChiGrid in
theorem qn_not_mem_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ)
    (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → ∀ w : HeightOneSpectrum (𝓞 D.what₂.LL), p.R.mu w ≠ p.P.A3.A.μ0 →
      ((Qn d.G (p.R.mu w) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit w hw
  classical
  obtain ⟨htw, hxi⟩ := xiH_twisted p w hw
  have hl : D.ntw.l (ex.nch.twI (D.plEq.symm w)) = D.what₂.places.resChar (D.plEq.symm w) :=
    (hfit.1.setting.1 _ htw).1
  have hQ := hfit.1.cond _ htw
  have hlev := p.charW.base.lev
  have key : ∀ PP ∈ twPl d.G (p.R.mu w),
      ((D.what₂.places.resChar (D.plEq.symm w) : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hlP
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    obtain ⟨hloc, hW0⟩ := hPP
    have hQt : PP ∈ p.R.toRealDat.toLevCh.Q (p.R.mu w) := hloc.resolve_left hW0
    have hS1 : PP.under (𝓞 D.host.F) ∉ S1 D := fun h => hW0 (by
      rw [d.G.pl.w_Q _ PP hQt h]
      exact Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem h))
    have hram : ¬ (p.R.toRealDat.toLevCh.xiH (p.R.mu w)).UnrAt PP := (hlev.Q_ram _ PP).2 (Or.inl hQt)
    rw [hxi] at hram
    by_cases hd : (p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w))).UnrAt PP
    · have hψ : ¬ (p.Tp.psi (D.plEq.symm w)).UnrAt PP := fun h => hram (hd.mul h)
      have hmem : PP ∈ ex.nch.Q (D.plEq.symm w) := by
        by_contra hn
        exact hψ (((p.Tp.psi_is _ htw).ram PP).2 hn)
      have hS0 : PP ∈ D.ntw.S0 (ex.nch.twI (D.plEq.symm w)) := D.ntw.twistExcludedPlaces_contains_residueChar _ (by rw [hl]; exact hlP)
      exact Finset.disjoint_left.1 hQ.2.1 hmem hS0
    · have hover : ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        unfold Formalism.L2.Host.CharFrame.delAt at hd
        split_ifs at hd
        · by_contra h
          exact hd (p.R.C.isDel'.unr PP fun h' => h (Or.inr h'))
        · by_contra h
          exact hd (p.R.C.isDel.unr PP fun h' => h (Or.inl h'))
      apply hS1
      rw [S1_mem_OmF]
      rcases hover with h | h
      · right; right; left
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
      · right; right; right
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
  intro hmem
  rw [Qn, Nat.cast_prod] at hmem
  obtain ⟨PP, hPP, hin⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hmem
  have : NeZero PP.asIdeal := ⟨PP.ne_bot⟩
  have hq : (Ideal.absNorm (PP.asIdeal.under ℤ)).Prime := Nat.absNorm_under_prime PP.asIdeal
  have : PP.asIdeal.LiesOver (Ideal.span {((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ)}) :=
    Int.liesOver_span_absNorm PP.asIdeal
  rw [Ideal.absNorm_eq_pow_inertiaDeg' PP.asIdeal hq, Nat.cast_pow] at hin
  have hqw := w.isPrime.mem_of_pow_mem _ hin
  have hqP : ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h : algebraMap ℤ (𝓞 D.host.E) ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ) ∈ PP.asIdeal :=
      Ideal.absNorm_mem (PP.asIdeal.under ℤ)
    rw [eq_intCast, Int.cast_natCast] at h
    exact h
  have e := resChar_eq (D.plEq.symm w) hq (by rw [Equiv.apply_symm_apply]; exact hqw)
  exact key PP hPP (e ▸ hqP)
end GlobalTheory.ThmAUpper
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInjStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.read_injective : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.readInj_alt | exact _root_.GlobalTheory.BigOn.Exp.readInj_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.readInj_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxMemSup
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd.Supp
section Cut
open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut
set_option synthInstance.maxHeartbeats 200000
variable {D : D7}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Cut
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}
end Level
section Std
open Formalism.L2.Col Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)
end Std
section Main
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
set_option maxHeartbeats 2000000 in
theorem mem_U_iff_mem_levU_of_grpAt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) [NeZero (B.R.N j)] {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
    (hJ : J.Reads) (β : J.Ch₀ j) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop} (hP : ∀ v, P v → ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ GlobalTheory.FinPl.grpAt _ P) (x : TC.GA B (B.R.N j))
    (hxU : x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j)) (hx : x.1 = finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) g) :
    g ∈ J.A.U j β ↔ x ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
      (Formalism.L2.Col.colLevSym I.Ch j).grp := by
  have hj' : j ≤ B.R.m := by omega
  rw [← mem_lev_iff I hW.tr.ok hW.tr.tw l.pr u _ j (by omega) (hJ.is.reads j hj') β (hJ.std j (by omega) β) x hxU fun Q hQ r s => ?_]
  · rw [hJ.is.U j hj']
    refine ⟨fun ⟨_, κ, hκ⟩ => ?_, fun h => ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hg, ⟨x, h⟩, hx⟩⟩
    have e : x = κ.1 := Units.ext (hx.trans hκ.symm)
    rw [e]
    exact κ.2
  · rw [hx]
    refine GlobalTheory.FinMComp.adAt_finM_eq_one _ _ _ P g hg Q (fun h => hP _ h ?_) r s
    obtain ⟨i, hi⟩ := hJ.surj Q ((hW.tq.Q t Q).2 hQ)
    exact ⟨i, ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i).trans (congrArg _ hi)⟩
set_option maxHeartbeats 2000000 in
theorem mem_U_of_mem_U_away_from_twisted (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t' : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
    (hJ : J.Reads) (β : J.Ch₀ j) (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t') (hJ' : J'.Reads) (β' : J'.Ch₀ j) {P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop}
    (hP : ∀ v, P v → ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J v) (hP' : ∀ v, P v → ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J' v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ GlobalTheory.FinPl.grpAt _ P) (h : g ∈ J.A.U j β) : g ∈ J'.A.U j β' := by
  have hj' : j ≤ B.R.m := by omega
  haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
  obtain ⟨hPins⟩ := hW.tr.pins
  have hg1 : gramN (I.rec7 l Z) j hj' = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hW.tr.ok hPins l Z).2.2.2 j hj').1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj') (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := by rw [hg1]; rfl
  obtain ⟨x, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj') (gramN (I.rec7 l Z) j hj') rfl g
  have hxU : x.1 ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N j) := eU ▸ x.2
  exact (_root_.GlobalTheory.LevProd.Supp.mem_U_iff_mem_levU_of_grpAt hW ha hTr j hj J' hJ' β' hP' hg x.1 hxU hx).2 ((_root_.GlobalTheory.LevProd.Supp.mem_U_iff_mem_levU_of_grpAt hW ha hTr j hj J hJ β hP hg x.1 hxU hx).1 h)
set_option maxHeartbeats 2000000 in
theorem cutAt_mem_U_of_mem_relax_not_twAt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t' : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t)
    (hJ : J.Reads) (α : J.Ch j) (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t') (hJ' : J'.Reads) (α' : J'.Ch j)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hg : g ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α) (v : GlobalTheory.FinPl.Pl (I.rec7 l Z)) (hv' : ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J' v) :
    cutAt _ v g ∈ J'.A.U j (J'.ι j α') := by
  obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
  by_cases hv : _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J v
  · obtain ⟨i, rfl⟩ := hv
    obtain ⟨gl, -, h1, h2⟩ := GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
      (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)))
    have hy : _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := (Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i (Set.mem_univ _)
    rw [h2 (cutAt _ (J.G i).q.v g) (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i) (suppAt_cutAt _ _ g)
      ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 (locHom_cutAt _ _ _ hgf).symm)]
    exact _root_.GlobalTheory.T.true_geometry_lattice_open_alt W hW u a ha hTr j hj t' J' hJ' α' t J hJ i hv' gl h1 _ hy
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) ≤ (J.A.U j (J.ι j α)).comap (cutAt _ v) := by
      refine sup_le (fun x hx => ((mem_U_iff hJ.is j (by omega) _ x).1 hx).2 v) fun x hx => ?_
      rw [Subgroup.mem_comap, cutAt_eq_one _ hv hx]
      exact one_mem _
    exact _root_.GlobalTheory.LevProd.Supp.mem_U_of_mem_U_away_from_twisted hW ha hTr j hj J hJ _ J' hJ' _ (P := (· ∈ ({v} : Finset _)))
      (fun w hw h => hv (Finset.mem_singleton.1 hw ▸ h)) (fun w hw h => hv' (Finset.mem_singleton.1 hw ▸ h)) (cutAt_mem _ v g) (hle hsup)
end Main
set_option maxHeartbeats 2000000 in
theorem relax_mem_sup_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j), ∀ g ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α, g ∈ J'.A.U j (J'.ι j α') ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' α' g hg
  have hgf : g ∈ GfC _ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2
  let Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z)) := Finset.univ.image fun i => (J'.G i).q.v
  have hQ : ∀ v, v ∈ Q ↔ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J' v := fun v => by
    simp only [Q, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  have h1 := GlobalTheory.FinPl.SetCut.cutG_mem_Q _ Q g
  have h2 := GlobalTheory.FinPl.SetCut.cutG_mem_Qc _ Q hgf
  have e := GlobalTheory.FinPl.SetCut.cutG_mul_cutG _ Q g
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.idemQ_mul_self Q) g = g₁ at h1 e
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) g = g₂ at h2 e
  have h3 : g₂ ∈ J'.A.U j (J'.ι j α') := by
    refine (mem_U_iff hJ'.is j (by omega) _ g₂).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h2, fun v => ?_⟩
    by_cases hv : v ∈ Q
    · rw [cutAt_eq_one _ (P := (· ∉ Q)) (not_not.2 hv) h2]
      exact one_mem _
    · have h4 := _root_.GlobalTheory.LevProd.Supp.cutAt_mem_U_of_mem_relax_not_twAt hW ha hTr j hj J hJ α J' hJ' α' hg v fun h => hv ((hQ v).2 h)
      rwa [← e, map_mul, cutAt_eq_one _ (P := (· ∈ Q)) hv h1, one_mul] at h4
  rw [← e]
  exact mul_mem (Subgroup.mem_sup_right (grpAt_mono _ (fun v hv => (hQ v).1 hv) h1)) (Subgroup.mem_sup_left h3)
end GlobalTheory.LevProd.Supp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBigStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_parameter_estimates_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ X' A : ℝ, Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (GlobalTheory.ExpTie.parOf (Fm.L x i) j) X' A ∧ Formalism.CohomologicalDescent.LargeParameterEstimates.Big (GlobalTheory.ExpTie.parOf (Fm.L x i) j).L (GlobalTheory.ExpTie.parOf (Fm.L x i) j).x X' A := by
  first | exact @_root_.GlobalTheory.ExpTie.rows_big_alt | exact _root_.GlobalTheory.ExpTie.rows_big_alt | (intros; apply _root_.GlobalTheory.ExpTie.rows_big_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfSizeStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_at_of_size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt <;> assumption)
end
end

