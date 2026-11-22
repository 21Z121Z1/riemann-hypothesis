import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0566
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0075
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2118
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0083
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0073
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0091
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0575
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0552
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0556
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2120
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0572
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0180
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0087
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelIffRelaxStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_tuple_free_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, ∃ c : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k, (∀ i, c i ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ∧ ∀ i, c i * _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i * (c i)⁻¹ ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i))) := by
  first | exact @_root_.GlobalTheory.PenLoc.level_iff_relax_alt | exact _root_.GlobalTheory.PenLoc.level_iff_relax_alt | (intros; apply _root_.GlobalTheory.PenLoc.level_iff_relax_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSqYBoundAtRec
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn
theorem levelSq_yBound_atRec_alt :
    _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun c _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ r O hO => ?_⟩⟩⟩
  obtain ⟨st, td⟩ := hO.1.depth
  letI := hostAlg (Fm.D x i)
  have g1 : O.g1 = (Fm.D x i).host.g 0 := td.jets_eq_fact
  have g2 : O.g2 = (Fm.D x i).host.g 1 := td.g2_eq
  have f1 : O.f = ((Fm.D x i).R.f : ℝ) := td.f_eq
  have k1 : O.k = ((Fm.D x i).R.k : ℝ) := td.k_eq
  have hrec : (R2 p).grp_record := by
    obtain ⟨plg, iso, -, h2, h3, h4⟩ := p.grpRecPin
    exact ⟨p.R.eG.trans p.cG, plg, iso, h2, h3, h4⟩
  have yb : ∀ {large₂ : SizeData₂ (Fm.D x i)} {Pm : ParameterChoice' (Fm.D x i) large₂}, ParamsT (Fm.D x i) large₂ Pm →
      LeafYBound (onOf (R2 p) (F2 p) c (supArgs (R2 p))) := fun {_ Pm} _ =>
    leafYBound (F := F2 p) c (supArgs (R2 p)) Pm
  refine ⟨?_, ?_⟩
  · have := leafLevelSq (F := F2 p) c (supArgs (R2 p)) hrec
    unfold LeafLevelSq
    rw [g1, g2]
    exact this
  · have := yb (Fm.parT x hx i)
    unfold LeafYBound OnObj.y
    rw [g1, g2, f1, k1]
    exact this
end GlobalTheory.BigOn
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LineIdealAtOwnPrime
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
noncomputable section
namespace GlobalTheory.MiTop.LineAtT
variable {D : D7}
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.MiTop.LineAtT
set_option maxHeartbeats 800000 in
open GlobalTheory.MiTop.LineAtT GlobalTheory.MiTop.Scale GlobalTheory.GoodPos GlobalTheory.IwaPlace GlobalTheory.FinPlLoc in
theorem GlobalTheory.MiTop.line_ideal_at_own_prime_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B hP v hv hTv c hc
  obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, hcI, hvI, hVT, hSh, hGP, hGR, hBT, hpr⟩ := _root_.GlobalTheory.MiTop.placedPrim_iff_placedP.2 hP
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m
    obtain ⟨k, hk⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  obtain ⟨i, rfl⟩ := (hSh.pre.tP v).1 ((hVT.tP v).2 hTv)
  have hU := (hSh.pre.char i).2
  have hψ : IsStdChar D W.Q.Rl.ψ (-1) := hcI.std
  have hm := GlobalTheory.StMoves.moves_inv (hVT.moves 0 (by omega) (· = (o.p i).v) fun p hp hg => by
    obtain ⟨PP, h1, h2⟩ := (hVT.gP p).1 hg
    exact hv PP h1 (h2.symm.trans hp))
  refine (hm _ fun r => Ideal.mul_mem_right _ _ hc).symm.trans ?_
  obtain ⟨μ, lam, hml, hz, hτ⟩ := hBT.norm
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))
  have hj : 2 * D.R.rS + 2 * 0 + 2 = D.R.m := by omega
  obtain ⟨lam', hl', hval⟩ := hSh.pre.lam _ hj
  have hll : lam = lam' := smul_left_injective _ (ne_zero_of_line (f.c.bes _ 0 hj).line) ((hτ _ hj).symm.trans hl')
  subst hll
  have uμ : UnitScal (o.p i).v μ := UnitScal.cancel (hml ▸ ((unitAt_of hξ hU.1).pow _).neg) (unitAt_val _ (hval i).1 (hval i).2)
  have hcop : Nat.Coprime (D.mem u).A.T W.S.X.B.g := by
    obtain ⟨M, h1, h2⟩ := GlobalTheory.TorusCong.one_sub_T_zmod D W.S.X u
    exact GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub _ _ _ M (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)) h1 h2
  have ug : UnitScal (o.p i).v (W.S.X.B.g : D.host.E) := unitAt_nat fun hg => by
    obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.F) hcop)
    exact (o.p i).v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hTv) (Ideal.mul_mem_left _ _ hg)))
  obtain ⟨l, hl, he⟩ := first_scale W.S.X W.Q.instEq u _ (W.S.tr u) hW.bot.idE hψ (psiE_ne hψ _ hU o.q) hr B hμ hz
  have ul : UnitScal (o.p i).v l := by
    rcases hl with e | e <;> rw [e]
    exacts [ug, ug.neg]
  have hl0 : l ≠ 0 := by
    have hg : ((W.S.X.B.g : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.Pf.modulus_g_ne_zero W.S.X)
    rcases hl with e | e <;> rw [e]
    exacts [hg, neg_ne_zero.2 hg]
  have ht0 : μ * l ^ D.R.rS ≠ 0 := mul_ne_zero hμ (pow_ne_zero _ hl0)
  have ut := uμ.mul (ul.pow D.R.rS)
  have hQ : ∀ Bl : BesLev D D.R.rS, Bl = f.c.B 0 D.R.rS h0 → ∀ LV : GlobalTheory.FinPl.Lat Bl.V, HEq LV (v'.N 0) → ∀ j,
      ∀ a ∈ idAt D (· = (o.p i).v), colMul Bl.d.jX j a ∈ latV Bl.V LV (· = (o.p i).v) ↔ a ∈ intAt D (· = (o.p i).v) := by
    rintro _ rfl LV hLV
    obtain rfl := eq_of_heq hLV
    intro j a ha
    have hlam : lam ≠ 0 := right_ne_zero_of_mul (by rw [hml]; exact neg_ne_zero.2 (pow_ne_zero _ hξ))
    obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D f.c.ψ hcI.std
    have u1 := isU_alpha hU hSh.pre.line (hα _).1
    have u2 : IsU (o.p i).v ((xiU D * cU α : (AE D)ˣ) : AE D) := (isU_xi hU).mul u1.conj
    have u3 : IsU (o.p i).v ((α * (xiU D * cU α)⁻¹ : (AE D)ˣ) : AE D) := u1.mul (u2.inv (Units.mul_inv _))
    have u4 : IsU (o.p i).v ((xiU D * α * cU α : (AE D)ˣ) : AE D) := ((isU_xi hU).mul u1).mul u1.conj
    have u5 : IsU (o.p i).v (((xiU D * α * cU α) ^ (D.R.rS - j.1) *
        ((α * (xiU D * cU α)⁻¹) ^ (D.R.rS + 1) * inU lam hlam) : (AE D)ˣ) : AE D) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact (u4.pow _).mul ((u3.pow _).mul (isU_of_val _ (hval i).1 (hval i).2))
    refine (iso_line_all hcI hSh hpr (_root_.GlobalTheory.MiTop.rank_X_succ_pos f) hlam hτ (hα _).1 (fun s hs => ?_) _ 0 h0 j a ha).trans
      (u5.inv (Units.mul_inv _) a ha).symm
    rw [(hα _).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  generalize μ * l ^ D.R.rS = t at he ht0 ut
  have hc' : incA D t⁻¹ * c ∈ idAt D (· = (o.p i).v) := Ideal.mul_mem_left _ _ hc
  have e1 : incA D t * (incA D t⁻¹ * c) = c := by
    rw [← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ ht0, RingHom.map_one, one_mul]
  have h1 := (hQ B.lev (hBT.lev h0) (v'.N 0) HEq.rfl ⟨0, hr⟩ _ hc').trans (ut _ hc').symm
  rw [e1] at h1
  refine Iff.trans (iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v'.N 0) (· = (o.p i).v)) (funext fun r => ?_))) h1
  refine Eq.trans ?_ (congrArg (incA D t⁻¹ * c * ·) (he r)).symm
  exact (congrArg (· * _) e1.symm).trans (by rw [mul_comm (incA D t), mul_assoc])
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalComponentMeasureIdentityAltBis
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_identity_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∃ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (dT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, GlobalTheory.FinPl.Frame (o.p i) (y.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)), ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ } ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.tP) (dT j)) ∧ (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) ∧ ∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j) := by
  first | exact @_root_.GlobalTheory.Fam.LatShape.exists_shape_integral_in_normal_frames_alt | exact _root_.GlobalTheory.Fam.LatShape.exists_shape_integral_in_normal_frames_alt | (intros; apply _root_.GlobalTheory.Fam.LatShape.exists_shape_integral_in_normal_frames_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemRelax
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
theorem pl_eq_of_quadratic_data_same_place (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) {t t₂ : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads) (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂)
    (hJ₂ : J₂.Reads) (i : Fin J.r) (i₂ : Fin J₂.r) (h : (J.G i).q.v = (J₂.G i₂).q.v) : J.pl i = J₂.pl i₂ := by
  have h1 := (_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i
  have h2 := (_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t₂ J₂ hJ₂).2 i₂
  exact hW.pk.sel _ _ ⟨t, J.mem i⟩ ⟨t₂, J₂.mem i₂⟩ (h1.symm.trans (h.trans h2))
theorem locHom_gl_eq_self_of_map_pr_eq (j : ℕ) {PP} (h₁ h₂ : _root_.GlobalTheory.Fam.QAllAlt W PP) (hj₁ : j ≤ (a.Q PP h₁).s + 1) (hj₂ : j ≤ (a.Q PP h₂).s + 1)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (a.Q PP h₂).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, (mt _ (gl y)).map (a.Q PP h₂).q.pr = ((a.Q PP h₂).FX j hj₂).β * y.val * ((a.Q PP h₂).FX j hj₂).γ) (y) :
    GlobalTheory.LevIdx.locHom (a.Q PP h₁).q _ ((a.Q PP h₁).FX j hj₁) (gl y) = y :=
  ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y)).symm
end GlobalTheory.LevOnto
end
namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
theorem gl_mem_relax_of_supp_at_and_map_pr (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t₂ : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads)
    (α : J.Ch j) (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂) (hJ₂ : J₂.Reads) (i : Fin J₂.r)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr =
      ((J₂.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj; omega)).β * y.val * ((J₂.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj; omega)).γ)
    (y) (hy : y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)) : gl y ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α := by
  have hAt : ∀ P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop, P (J₂.G i).q.v → gl y ∈ GlobalTheory.FinPl.grpAt _ P :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt (· = (J₂.G i).q.v) rfl)⟩, ?_⟩
  · by_cases hv : _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J (J₂.G i).q.v
    · exact Subgroup.mem_sup_right (hAt _ hv)
    · exact Subgroup.mem_sup_left (_root_.GlobalTheory.T.true_geometry_lattice_open_alt W hW u a ha hTr j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy)
  · rw [Subgroup.mem_comap, Subgroup.mem_pi]
    intro i' _
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl y) ∈ KO (J.G i').k _
    by_cases hv : (J.G i').q.v = (J₂.G i).q.v
    · have e := _root_.GlobalTheory.LevOnto.pl_eq_of_quadratic_data_same_place hW ha hTr J hJ J₂ hJ₂ i' i hv
      have key : ∀ P (hP : P ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (hj₁ : j ≤ (a.Q P ⟨t, hP⟩).s + 1), P = J₂.pl i →
          GlobalTheory.LevIdx.locHom (a.Q P ⟨t, hP⟩).q _ ((a.Q P ⟨t, hP⟩).FX j hj₁) (gl y) ∈ KO (a.Q P ⟨t, hP⟩).k
            (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) := by
        rintro P hP hj₁ rfl
        rw [_root_.GlobalTheory.LevOnto.locHom_gl_eq_self_of_map_pr_eq j _ _ hj₁ _ gl (fun y => (hgl y).2) y]
        exact hy
      exact key _ (J.mem i') _ e
    · rw [locHom_eq_one (J₂.G i).q (J.G i').q _ _ (gl y) (hgl y).1 (Ne.symm hv)]
      exact one_mem _
theorem onto_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.Ch j → ∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj, _root_.GlobalTheory.LevProd.localHomProduct J j hj g = x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α x hx
  have hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  have hUp : _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj = _root_.GlobalTheory.LevProd.relaxedLevelSubgroup hex.choose_spec.choose j hj hex.choose_spec.choose_spec.2.some := by
    unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
    rw [dif_pos hex]
  have hJ₀ : hex.choose_spec.choose.Reads := hex.choose_spec.choose_spec.1
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
  choose gl _ hglp _ using hgl
  refine ⟨((List.finRange J.r).map fun i => gl i (x i)).prod, ?_, ?_⟩
  · rw [hUp]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact _root_.GlobalTheory.LevOnto.gl_mem_relax_of_supp_at_and_map_pr hW ha hTr j hj _ hJ₀ _ J hJ i (gl i) (hglp i) (x i) (hx i)
  · rw [map_list_prod, List.map_map]
    have hphi : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
      intro i
      funext i'
      show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
      by_cases h : i' = i
      · subst h
        rw [Pi.mulSingle_eq_same]
        exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
      · rw [Pi.mulSingle_eq_of_ne h]
        refine locHom_eq_one (J.G i).q (J.G i').q _ _ _ (hglp i (x i)).1 fun hv => h ?_
        exact hJ.inj (_root_.GlobalTheory.LevOnto.pl_eq_of_quadratic_data_same_place hW ha hTr J hJ J hJ i' i hv.symm)
    simp only [Function.comp_def, hphi]
    exact list_prod_mulSingle x
end GlobalTheory.LevOnto
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemUlocBadGStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_measure_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → _root_.GlobalTheory.FamTrace.InLevelGroup a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Uloc v := by
  first | exact @_root_.GlobalTheory.FamTrace.AtG.mem_Uloc_badG_alt | exact _root_.GlobalTheory.FamTrace.AtG.mem_Uloc_badG_alt | (intros; apply _root_.GlobalTheory.FamTrace.AtG.mem_Uloc_badG_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MmTieStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafMinimalMass_of_setAt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumProdStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_step_vector_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) → ∃ κ : ℂ, κ ≠ 0 ∧ ∃ Lp : Fin n → GlobalTheory.SeeSaw.LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M', (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, (Lp i).e = (G i).eg j) ∧ (∀ i, IntIn (Lp i).q (Yc D j) (Lp i).FS (v.N j) ∧ IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FT (v.N (j + 1))) ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∃ F, IsThetaFunO f.c.ψ (Yc D j) (Yc D (j + 1)) F ∧ IsThetaAt f.c.ψ (symplO (Yc D j) (Yc D (j + 1))) (heisO f.c.ψ (Yc D j) (Yc D (j + 1))) (∑ i, (Lp i).q.e) (latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) fun _ => True) 1 ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) (GlobalTheory.SeeSaw.prodDat Lp) F ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • F := by
  first | exact @_root_.GlobalTheory.MidDat.moved_datum_prod_alt | exact _root_.GlobalTheory.MidDat.moved_datum_prod_alt | (intros; apply _root_.GlobalTheory.MidDat.moved_datum_prod_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonemptyHypsOfAllRows
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc
theorem nonempty_hyps_of_allRows_alt : StandardLattice.SiegelMassRatioCM → LitThin → Formalism.L2.SG.Pf.WuDecayOfGap → Formalism.L2.SG.RowsDef.RowsFinDim → Formalism.L2.SG.RowsPos.TypeP → Formalism.L2.SG.RowsPos.RowNGP → Formalism.L2.SG.RowsPos.RowMainEqP → (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop) (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType), (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧ GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') → ExBL KP Q Q' Lk → _root_.GlobalTheory.Fc.AllRowsAlt KP Q Q' Lk N DR → Nonempty (_root_.GlobalTheory.Fc.HypsAlt N DR) := by
  intro hP hLit hWu hRF hTy hNG hM hU hG KP Q Q' Lk N DR hc hx hA
  obtain ⟨R30, hR30, c30, cIc, hb30, hpos, r30⟩ := hA.c30
  have rTu := Row.rowL (KP := KP) (Q := Q) largeBaseProperty_true (_root_.GlobalTheory.T.hTu_cTmin_of_genusMass hU hG Q' Lk)
  have hall := RowL.and (hA.hn4 : RowL KP Q Q' Lk fun 𝒜 _ => R0.ClassCountBoundAllPoints 𝒜) <|
    RowL.and (hA.jOn : RowL KP Q Q' Lk fun 𝒜 _ => R0.H_jOn 𝒜) <|
    RowL.and (hA.hInstR : RowL KP Q Q' Lk fun 𝒜 _ => ClassTwoEntries.H_hInstR 𝒜) <|
    RowL.and (hA.aC2 : RowL KP Q Q' Lk fun 𝒜 _ => ClassTwoEntries.DivisionSecondComplementAdmissible 𝒜) <|
    RowL.and (hA.aP10 : RowL KP Q Q' Lk fun 𝒜 _ => AllBundlePointProperties.LevelPrimeColumnValuationsClosed 𝒜) <|
    RowL.and (hA.aAtG : RowL KP Q Q' Lk fun 𝒜 _ => AllBundlePointProperties.H_aAtG 𝒜) <|
    RowL.and (hA.aPt0 : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.ReferenceChainEvaluationAdmissible 𝒜) <|
    RowL.and (hA.aPtTw : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPtTw 𝒜) <|
    RowL.and (hA.aPer0 : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPer0 𝒜) <|
    RowL.and (hA.aPerTw : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_aPerTw 𝒜) <|
    RowL.and (hA.tie : RowL KP Q Q' Lk fun 𝒜 _ => PeriodEntriesOverColumns.H_tie 𝒜) <|
    RowL.and (hA.hRB : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.P_hRB_alt)) <|
    RowL.and (hA.hTw : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.TwistBundleCondition)) <|
    RowL.and (hA.hPA : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition)) <|
    RowL.and (hA.hLamP : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.LambdaPrimeBundleCondition)) <|
    RowL.and (hA.hDivG : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition)) <|
    RowL.and (hA.hDcPtG : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.DecompositionPointBundle)) <|
    RowL.and (hA.selJ : RowL KP Q Q' Lk (AtAll _root_.GlobalTheory.Fc.R1.SelectionJumpBundleCondition)) <|
    RowL.and (hA.sLp : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionLpBound) <|
    RowL.and (hA.sO : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionOrderBound) <|
    RowL.and (hA.hServ : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionServesFamily) <|
    RowL.and (hA.zL : RowL KP Q Q' Lk _root_.GlobalTheory.Fc.R1.SelectionZeroLocus) <|
    RowL.and (hA.hTF : RowL KP Q Q' Lk fun 𝒜 _ => R1.H_hTF 𝒜) <|
    RowL.and (hA.rRows : RowL KP Q Q' Lk (_root_.GlobalTheory.Fc.R1.SelectionDefiniteRows DR)) <|
    RowL.and (hA.nRest : RowL KP Q Q' Lk fun 𝒜 _ => N (GlobalTheory.Cp.D3 3 𝒜)) <|
    RowL.and (⟨R30, hR30, r30⟩ : RowL KP Q Q' Lk _) rTu
  obtain ⟨𝒜, σ, hE, hD, -, hn4, jOn, hInstR, aC2, aP10, aAtG, aPt0, aPtTw, aPer0, aPerTw, tie, hRB, hTw, hPA, hLamP, hDivG,
    hDcPtG, selJ, sLp, sO, hServ, zL, hTF, rRows, nRest, ⟨h30, irrC⟩, hTu⟩ :=
    UpperTheory.Top.classSel hP (fun D => hU D) KP Q Q' _root_.GlobalTheory.Fc.BundleCondition Lk _ (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y) hc hx hall
  have s3 : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm := fun Fm h => ((GlobalTheory.T.workingFamClass_copies_eq_frozen.1 𝒜 _ Fm).1).1 h
  have s1 : ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm → W1 𝒜 Fm :=
    fun Fm h => ((GlobalTheory.T.workingFamClass_copies_eq_frozen.1 𝒜 _ Fm).2).1 h
  exact ⟨{
    𝒜 := 𝒜
    σ := σ
    cT := fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y
    hEx := fun hM la G hla hH => working_classes_frozen.2 _ _ (fun hM' => hE hM' la G hla hH) hM
    hduty := fun Fm h => GlobalTheory.T.workingFamClass_copies_eq_frozen.2 _ Fm (hD _ Fm h).1
    hRB := fun Fm hc x hx _ i => hRB Fm hc x hx i
    hTw := fun Fm hc x hx _ i => hTw Fm hc x hx i
    hPA := fun Fm hc x hx _ i => hPA Fm hc x hx i
    hLamP := fun Fm hc x hx _ i => hLamP Fm hc x hx i
    hDivG := fun Fm hc x hx _ i => hDivG Fm hc x hx i
    hDcPtG := fun Fm hc x hx _ i => hDcPtG Fm hc x hx i
    hTu := hTu
    hn4 := Formalism.MainNotions.Pk.Closed.sub hn4 s1
    hLit := hLit
    hWu := hWu
    hRF := hRF
    hTF := hTF
    c30 := c30
    hc30 := hb30
    sTy := hTy
    sNG := hNG
    sM := hM
    sLp := sLp
    sO := sO
    h30 := h30
    hInstR := fun Fm hc x hx _ i => hInstR Fm hc x hx i
    selJ := fun Fm hc x hx _ i => Classical.choice (selJ Fm hc x hx i)
    jOn := Formalism.MainNotions.Pk.Closed.sub jOn s3
    hMt := fun Fm h => (hD _ Fm h).2
    rRows := rRows
    aPt0 := Formalism.MainNotions.Pk.Closed.sub aPt0 s3
    aPtTw := Formalism.MainNotions.Pk.Closed.sub aPtTw s3
    aPer0 := Formalism.MainNotions.Pk.Closed.sub aPer0 s3
    aPerTw := Formalism.MainNotions.Pk.Closed.sub aPerTw s3
    aP10 := Formalism.MainNotions.Pk.Closed.sub aP10 s3
    aAtG := Formalism.MainNotions.Pk.Closed.sub aAtG s3
    aC2 := Formalism.MainNotions.Pk.Closed.sub aC2 s3
    hServ := hServ
    cIc := cIc
    hcI := hpos
    irrC := irrC
    zL := zL
    tie := Formalism.MainNotions.Pk.Closed.sub tie s3
    hU := hU
    hG := hG
    nRest := nRest }⟩
end GlobalTheory.Fc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormSqBlockValue
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAut
theorem norm_sq_blockValue_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ ν hν Q
  have h := norm_sq_firstValA p.R.toRealDat p.F.lv2 p.charW.base.lev p.charW.base.fam j (p.R.mu w) Q.1 Q.2
  obtain rfl : ν = fun Q => Formalism.L2.Col.firstValA (p.P.A3.A.muVal j (p.R.mu w)) p.P.A3.A.etaVal p.P.A3.A.q p.P.A3.A.r Q.1 :=
    List.mem_singleton.1 hν
  have e : (blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t = p.P.A3.A.r := Nat.add_sub_cancel ..
  rw [e]
  exact h
end GlobalTheory.FrameAut
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPtOfSizeStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_point_statement_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.NumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' | exact _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' | (intros; apply _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' <;> assumption)
end
end

