import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0478
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

open Formalism.L2.SG.HidaSetting in

theorem argT_finE_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (Yc D 0)) :
    argT X h (finE (Yc D 0) κ) = cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h)
      (GlobalTheory.FlagBasis.chiArg X.B.I X.e0 X.f0 X.z0 X.bw X.bwd ((iotaX X h).toMulEquiv κ).2) := by
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h
  subst h
  have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  have e2 : finE (Yc D 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (EAf D)) :=
    (congrArg (finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
  rw [e2]
  rfl

theorem intAf_cast {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : TensorProduct X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) (hc : c ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) c ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h
  subst h
  exact hc

theorem chiS_cast {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : TensorProduct X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) :
    chiS X h (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) c) =
      X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g c) := by
  rw [chiS_rfl]
  congr 2
  exact cast_cast _ _ c |>.trans (cast_eq _ c)

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar

theorem argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (κ : GA D (Yc D 0)), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ X.chi2 ((iotaX X h).toMulEquiv κ).2 = GlobalTheory.SeeConjChar.chiS X h (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) := by
  intro D X h κ hK
  rw [argT_finE_eq X h κ]
  refine ⟨intAf_cast X h _ ?_, ?_⟩
  · obtain ⟨hef, hz0, hb⟩ := X.vectorsInLattice
    have hnxt : ∀ a, Formalism.L2.SG.HidaSetting.nxt X.e0 X.z0 a ∈ X.B.I.Lf := fun a => by
      unfold Formalism.L2.SG.HidaSetting.nxt
      split_ifs
      exacts [(hef _).1, hz0]
    unfold GlobalTheory.FlagBasis.chiArg
    refine Subring.add_mem _ (Subring.sum_mem _ fun a _ => ?_) (Subring.sum_mem _ fun i _ => ?_)
    · exact Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (hef a).2 (Formalism.L2.SG.Pf.unitaryCongruence.K_mv _ hK (hnxt a))
    · split_ifs with hi
      · exact Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (hb i).2 (Formalism.L2.SG.Pf.unitaryCongruence.K_mv _ hK (hb _).1)
      · exact Subring.zero_mem _
  · exact (chiS_cast X h _).symm

end GlobalTheory.SeeConjChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelIndicatorThetaFockLatticeVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IndVac

variable {D : D7} {S T : HSp D}

theorem mem_of_indL_ne {L : AddSubgroup (WO S T)} {t : WO S T} (h : GlobalTheory.LiftLevel.indL L t ≠ 0) : t ∈ L := by
  by_contra hn
  exact h (by simp only [GlobalTheory.LiftLevel.indL, hn, if_false])

theorem isSBHalf_indL (a : AE D) (Λ L : AddSubgroup (WO S T)) (hL : ∀ x ∈ L, IsHalf a x)
    (h1 : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ Λ) (h2 : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ Λ, IsHalf a x → m • x ∈ L) :
    IsSBHalf a Λ (GlobalTheory.LiftLevel.indL L) := by
  obtain ⟨m, hm, hm1⟩ := h1
  obtain ⟨n, hn, hn2⟩ := h2
  refine ⟨fun t ht => hL t (mem_of_indL_ne ht), m * n, Nat.mul_pos hm hn, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have hk : (m * n) • u ∈ L := by
      rw [← smul_smul]
      exact L.nsmul_mem (hn2 u hu hu') m
    simp only [GlobalTheory.LiftLevel.indL, L.add_mem_cancel_right hk]
  · rw [mul_comm, ← smul_smul]
    exact Λ.nsmul_mem (hm1 t (mem_of_indL_ne ht)) n

theorem partAt_eq (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := rfl

theorem symplO_half_eq_zero {a b : AE D} (hab : cA D b * a = 0) {r x : WO S T}
    (hr : r ∈ GlobalTheory.PlaceModel.half S T b) (hx : x ∈ GlobalTheory.PlaceModel.half S T a) : symplO S T r x = 0 := by
  rw [← (GlobalTheory.PlaceModel.mem_half S T).1 hr, ← (GlobalTheory.PlaceModel.mem_half S T).1 hx, GlobalTheory.PlaceModel.symplO_smul,
    smul_smul, hab, zero_smul, GlobalTheory.PlaceModel.symplO_zero_right]

theorem heisO_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    (r : WO S T) (hr0 : heisO ψ S T r f₀ = f₀) (hx : ∀ x, IsHalf a x → symplO S T r x = 0)
    (hy : ∀ y, IsHalf (cA D a) y → symplO S T r y = 0)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) : heisO ψ S T r (Tm Φ) = Tm Φ := by
  have hc : ∀ w, symplO S T r w = 0 → ∀ g, heisO ψ S T r (heisO ψ S T w g) = heisO ψ S T w (heisO ψ S T r g) :=
    fun w hw g => by
      have := GlobalTheory.PlaceModel.heisL_comm S T ψ r w g
      rw [hw, AddChar.map_zero_eq_one, one_smul] at this
      exact this
  have h' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀
      ((GlobalTheory.PlaceModel.heisL S T ψ r).comp Tm) :=
    { trans := fun Φ hΦ x hxa => by
        change heisO ψ S T r (Tm _) = heisO ψ S T x (heisO ψ S T r (Tm Φ))
        rw [hTm.trans Φ hΦ x hxa, hc x (hx x hxa)]
      modul := fun Φ hΦ y hya => by
        change heisO ψ S T r (Tm _) = heisO ψ S T y (heisO ψ S T r (Tm Φ))
        rw [hTm.modul Φ hΦ y hya, hc y (hy y hya)]
      vac := by
        change heisO ψ S T r (Tm _) = f₀
        rw [hTm.vac, hr0] }
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hS hT ha hinf h' hTm hΦ

theorem heisenbergTranslate_add_three_fixes_of_trivial_phase (ψ : AddChar (AF D.host.F) ℂ) {f : WO S T → ℂ} {x y z : WO S T}
    (hx : heisO ψ S T x f = f) (hy : heisO ψ S T y f = f) (hz : heisO ψ S T z f = f)
    (p1 : ψ (symplOH S T y z) = 1) (p2 : ψ (symplOH S T x (y + z)) = 1) : heisO ψ S T (x + (y + z)) f = f := by
  have e1 := GlobalTheory.PlaceModel.heisL_heisL S T ψ y z f
  have e2 := GlobalTheory.PlaceModel.heisL_heisL S T ψ x (y + z) f
  change heisO ψ S T y (heisO ψ S T z f) = _ • heisO ψ S T (y + z) f at e1
  change heisO ψ S T x (heisO ψ S T (y + z) f) = _ • heisO ψ S T (x + (y + z)) f at e2
  rw [hz, hy, p1, one_smul] at e1
  rw [← e1, hx, p2, one_smul] at e2
  exact e2.symm

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem indL_theta_fock_latVac : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ f₀ : WO S T → ℂ, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel C.ψ (symplO S T) (heisO C.ψ S T) (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ L : AddSubgroup (WO S T), (∀ x ∈ L, IsHalf (cA D e) x) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) → IsSBHalf (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (GlobalTheory.LiftLevel.indL L) ∧ C.IsTh (Tm (GlobalTheory.LiftLevel.indL L)) ∧ C.IsFock B (Tm (GlobalTheory.LiftLevel.indL L)) ∧ ∀ Λ'' : AddSubgroup (WO S T), (∀ u ∈ Λ'', GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → IsLatVac (heisO C.ψ S T) Λ'' (Tm (GlobalTheory.LiftLevel.indL L)) := by
  intro D S T C B hB ΛT hT P e he f₀ hvac Tm hTm L hL hm1 hm2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hea : e * cA D e = 0 := he.2
  have ha : cA D e * cA D e = cA D e := ho.conj.idem
  have hcc : cA D (cA D e) = e := cA_cA e
  have hS := GlobalTheory.Ker.Base.selfDualC_stdL C.m.gS
  have hψ := C.std
  have hinf : infPart D (cA D e) = 0 := ho.conj.infPart_eq
  have hinf' : infPart D (cA D (cA D e)) = 0 := ho.conj.conj.infPart_eq
  have hSB := isSBHalf_indL (cA D e) _ L hL hm1 hm2
  have hth : IsThetaAt C.ψ (symplO S T) (heisO C.ψ S T) (cA D e)
      (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      1 f₀ (GlobalTheory.LiftLevel.indL L) (Tm (GlobalTheory.LiftLevel.indL L)) :=
    ⟨⟨Tm, hTm⟩, fun T' hT' => GlobalTheory.PlaceVec.placeModel_unique hψ hS hT ha hinf hTm hT' hSB⟩
  have hθf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ C.inf hth hvac.2.theta
  refine ⟨hSB, hθf, fun τ => GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 C.inf hinf hinf' hth hvac.2.theta hθf
    (hvac.2.fock τ), ?_⟩
  obtain ⟨b, hbd⟩ : ∃ b : AE D, b = 1 - e - cA D e := ⟨_, rfl⟩
  have hb : b * b = b := by rw [hbd]; linear_combination hee + ha + 2 * hea
  have hcb : cA D b = b := by rw [hbd, map_sub, map_sub, map_one, hcc]; ring
  have hba : cA D b * cA D e = 0 := by rw [hcb, hbd]; linear_combination -hea - ha
  have hbe : cA D b * e = 0 := by rw [hcb, hbd]; linear_combination -hee - hea
  have hfix_a : ∀ x ∈ L, heisO C.ψ S T x (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun x hx => by
    rw [← hTm.trans _ hSB x (hL x hx)]
    congr 1
    funext t
    simp only [GlobalTheory.LiftLevel.indL, L.add_mem_cancel_right hx]
  have hfix_e : ∀ y, IsHalf e y → (∀ t ∈ L, C.ψ (symplO S T t y) = 1) →
      heisO C.ψ S T y (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun y hy ht => by
    rw [← hTm.modul _ hSB y (by rw [hcc]; exact hy)]
    congr 1
    funext t
    by_cases h : t ∈ L
    · simp only [GlobalTheory.LiftLevel.indL, h, if_true, ht t h, one_mul]
    · simp only [GlobalTheory.LiftLevel.indL, h, if_false, mul_zero]
  have hfix_r : ∀ r ∈ GlobalTheory.PlaceModel.half S T b, heisO C.ψ S T r f₀ = f₀ →
      heisO C.ψ S T r (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun r hr hr0 =>
    heisO_fix hψ hS hT ha hinf hTm r hr0
      (fun x hx => symplO_half_eq_zero hba hr ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx))
      (fun y hy => symplO_half_eq_zero (by rw [hcc]; exact hbe) hr ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy)) hSB
  have hdec : ∀ u : WO S T, u = cA D e • u + (e • u + b • u) := fun u => by
    rw [← add_smul, ← add_smul, show cA D e + (e + b) = 1 by rw [hbd]; ring, one_smul]
  have hbmem : ∀ u : WO S T, b • u ∈ GlobalTheory.PlaceModel.half S T b := fun u => by
    show b • b • u = b • u
    rw [smul_smul, hb]
  have hemem : ∀ u : WO S T, e • u ∈ GlobalTheory.PlaceModel.half S T e := fun u => by
    show e • e • u = e • u
    rw [smul_smul, hee]
  have hamem : ∀ u : WO S T, cA D e • u ∈ GlobalTheory.PlaceModel.half S T (cA D e) := fun u => by
    show cA D e • cA D e • u = cA D e • u
    rw [smul_smul, ha]
  have hez : ∀ u : WO S T, symplO S T (e • u) (b • u) = 0 := fun u => by
    rw [GlobalTheory.PlaceModel.symplO_skew, symplO_half_eq_zero hbe (hbmem u) (hemem u), neg_zero]
  have haz : ∀ u : WO S T, symplO S T (cA D e • u) (b • u) = 0 := fun u => by
    rw [GlobalTheory.PlaceModel.symplO_skew, symplO_half_eq_zero hba (hbmem u) (hamem u), neg_zero]
  intro Λ'' hΛ''
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hΛ'' u hu
    rw [partAt_eq] at h1 h3
    simp only [partAt_eq] at h2
    rw [← hbd] at h3
    have e2u : 2 • u = 2 • (cA D e • u) + (2 • (e • u) + 2 • (b • u)) := by
      conv_lhs => rw [hdec u]
      rw [smul_add, smul_add]
    rw [e2u]
    have h2' : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
      norm_num
    refine heisenbergTranslate_add_three_fixes_of_trivial_phase C.ψ (hfix_a _ (L.nsmul_mem h1 2))
      (hfix_e _ ((GlobalTheory.PlaceModel.isHalf_iff S T).2 ((GlobalTheory.PlaceModel.half S T e).nsmul_mem (hemem u) 2))
        fun t ht => by rw [two_nsmul, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul, h2 t ht, one_mul])
      (hfix_r _ ((GlobalTheory.PlaceModel.half S T _).nsmul_mem (hbmem u) 2) (hvac.2.lat.1 _ h3)) ?_ ?_
    · simp only [symplOH, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, hez, add_zero,
        mul_zero, AddChar.map_zero_eq_one]
    · have hs : symplOH S T (2 • (cA D e • u)) (2 • (e • u) + 2 • (b • u)) =
          symplO S T (cA D e • u) (e • u) + symplO S T (cA D e • u) (e • u) := by
        simp only [symplOH, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, haz, add_zero]
        linear_combination (2 * symplO S T (cA D e • u) (e • u)) * h2'
      rw [hs, AddChar.map_add_eq_mul, h2 _ h1, one_mul]
  · obtain ⟨h1, h2, h3⟩ := hΛ'' u hu
    rw [partAt_eq] at h1 h3
    simp only [partAt_eq] at h2
    rw [← hbd] at h3
    have hu' : u ∈ GlobalTheory.PlaceModel.half S T e' := (GlobalTheory.PlaceModel.isHalf_iff S T).1 hh
    have hin : ∀ c : AE D, c • u ∈ GlobalTheory.PlaceModel.half S T e' := fun c => by
      rw [GlobalTheory.PlaceModel.mem_half, smul_comm, (GlobalTheory.PlaceModel.mem_half S T).1 hu']
    have hae : symplO S T (cA D e • u) (e • u) = 0 :=
      symplO_half_eq_zero (by rw [mul_comm]; exact he'.2.1) (hin _) (hin _)
    rw [hdec u]
    refine heisenbergTranslate_add_three_fixes_of_trivial_phase C.ψ (hfix_a _ h1) (hfix_e _ ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (hemem u)) h2)
      (hfix_r _ (hbmem u) (hvac.2.lat.2 e' he' _ h3 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (hin _)))) ?_ ?_
    · rw [symplOH, hez, mul_zero, AddChar.map_zero_eq_one]
    · rw [symplOH, GlobalTheory.PlaceModel.symplO_add_right, hae, haz, add_zero, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.IndVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalLevelPointFinitePartMemLevelGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLevelPoint_finitePart_mem_levelGroup : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (γ : GL (Fin T.rank) D.host.E) (κ : Lv.J), Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) κ → ∀ (a f g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), a ∈ GinfC T → f ∈ GfC T → IsRatOf T γ (a * f) → g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤ → (mapL γ L).FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ (mapL γ L) → C.LevK Lv (g₂⁻¹ * f * g₁) κ := by
  first | exact @GlobalTheory.Ker.LevMove.levK_of_rat_moves | exact GlobalTheory.Ker.LevMove.levK_of_rat_moves | (intros; apply GlobalTheory.Ker.LevMove.levK_of_rat_moves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueCoordinatesInFrameLinearStabiliserStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), IsFrame β Λ → ∀ PP : Pl E, (∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP (v + w) = redV β PP v + redV β PP w) ∧ (∀ (c : Formalism.L2.Herm.intAf F E), ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) = resS F PP c • redV β PP v) ∧ (∀ M ∈ St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) = ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) *ᵥ redV β PP v) := by
  first | exact @GlobalTheory.SeeConjGroup.redV_add_smul_stab | exact GlobalTheory.SeeConjGroup.redV_add_smul_stab | (intros; apply GlobalTheory.SeeConjGroup.redV_add_smul_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueIdempotentConjAtLevelPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_idempotent_conj_at_levelPlace : ∀ {D : D7} (g : ℕ) (ew : (II D).E ⊗[(II D).F] Af (II D).F), ew * ew = ew → ew * sigA (II D) ew = 0 → ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → (∀ y ∈ (II D).Lf, (1 - ew - sigA (II D) ew) • y ∈ mL (II D) g) → ∀ PP : Pl D.host.E, ((g : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h2 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (GlobalTheory.StdFrames.cpt PP ew = 1 → resS D.host.F PP ⟨ew, h1⟩ = 1 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 0) ∧ (GlobalTheory.StdFrames.cpt PP ew ≠ 1 → resS D.host.F PP ⟨ew, h1⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 1) := by
  first | exact @GlobalTheory.SeeConjIdem.resS_idem_conj | exact GlobalTheory.SeeConjIdem.resS_idem_conj | (intros; apply GlobalTheory.SeeConjIdem.resS_idem_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtAbsNormLeProdNormCmTypeEmbeddingsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_absNorm_le_prod_norm_cmTypeEmbeddings : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (u : 𝓞 D.host.E), u ∈ 𝔪 → u ≠ 0 → Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, ‖tauE D τ (u : D.host.E)‖ := by
  first | exact @GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE | exact GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE | (intros; apply GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameIntegralityConditionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_frame_integrality_conditions : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (J U W : Matrix (Fin n) (Fin n) (EAf D)) (Q : Pl D.host.E) (d : Fin n → EAf D), (∀ i j, (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * U) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * W) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ a, Valued.v (GlobalTheory.StdFrames.cpt Q (d a)) = 1) → (∀ a b, SmallAt Q ((Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a b - if a = b then d a else 0)) → Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * W).det) = 1 := by
  first | exact @GlobalTheory.SeeConjRead.DetUnit.det_unit | exact GlobalTheory.SeeConjRead.DetUnit.det_unit | (intros; apply GlobalTheory.SeeConjRead.DetUnit.det_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionProdConjEqOfHeisenbergFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_prod_conj_eq_of_heisenbergFixed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := by
  first | exact @GlobalTheory.ThetaFixedProd.prod_eq_of_fixed | exact GlobalTheory.ThetaFixedProd.prod_eq_of_fixed | (intros; apply GlobalTheory.ThetaFixedProd.prod_eq_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

namespace GlobalTheory.VacuumCharacter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem signBlockDeterminant_diagonalPhases_zpow {n : ℕ} (ε : Fin n → Bool) (t : Fin n → ℝ) (x : Bool → ℤ) :
    signBlockDeterminant ε true (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x true *
      signBlockDeterminant ε false (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x false =
      Complex.exp (Complex.I * ∑ j, (x (ε j) : ℂ) * t j) := by
  have key : ∀ e : Bool, signBlockDeterminant ε e (diagonal fun j => Complex.exp (Complex.I * t j)) ^ x e =
      Complex.exp (Complex.I * ∑ j ∈ Finset.univ.filter (fun j => ε j = e), (x e : ℂ) * t j) := by
    intro e
    rw [signBlockDeterminant, submatrix_diagonal _ _ Subtype.val_injective, det_diagonal]
    simp only [Function.comp_apply]
    rw [← Complex.exp_sum,
      ← Complex.exp_int_mul,
      Finset.sum_subtype (Finset.univ.filter fun j => ε j = e) (p := fun j => ε j = e) (by simp)]
    congr 1
    try simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [key, key, ← Complex.exp_add, ← mul_add,
    ← Finset.sum_fiberwise (M := ℂ) (s := (Finset.univ : Finset (Fin n))) (g := ε)
      (f := fun j : Fin n => (x (ε j) : ℂ) * (t j : ℂ)), Fintype.sum_bool]
  congr 3 <;> refine Finset.sum_congr rfl fun j hj => ?_ <;> rw [(Finset.mem_filter.1 hj).2]

theorem diag_mem_Kset {n : ℕ} (ε : Fin n → Bool) (t : Fin n → ℝ) :
    (diagonal fun j => Complex.exp (Complex.I * t j)) ∈ Formalism.REAL.Kset ε := by
  have hu : ∀ j, star (Complex.exp (Complex.I * t j)) * Complex.exp (Complex.I * t j) = 1 := by
    intro j
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    exact hu j
  · rw [Formalism.REAL.Jm, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext j
    ring

theorem torusVac_of_compactFock {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ)
    (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ) (h : CompactFock ψ θ M M' ω f τ aS aT) :
    TorusVac θ M M' ω f τ aS aT := by
  obtain ⟨x, y, hx, hy, hK⟩ := h
  intro t t'
  have hact := hK _ (diag_mem_Kset (M.ε τ) t) _ (diag_mem_Kset (M'.ε τ) t') 1
  rw [map_one, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.ptOf_one] at hact
  rw [hact, signBlockDeterminant_diagonalPhases_zpow, signBlockDeterminant_diagonalPhases_zpow, ← Complex.exp_add, ← mul_add]
  have hx' : ∀ j, ((x (M.ε τ j) : ℤ) : ℂ) = ((wtS (M'.ε τ) aT (M.ε τ j) : ℚ) : ℂ) := fun j => by
    rw [← hx j]; push_cast; rfl
  have hy' : ∀ i, ((y (M'.ε τ i) : ℤ) : ℂ) = ((wtT (M.ε τ) aS (M'.ε τ i) : ℚ) : ℂ) := fun i => by
    rw [← hy i]; push_cast; rfl
  simp only [hx', hy']

theorem vacChar : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  intro D V W S S' M M' θ ψ χS χT ω f τ aS aT hθ hW hS hT hV
  have hF := GlobalTheory.ChainFr.isVacF_of_isVacVec hV
  have hK := GlobalTheory.T.compact_subgroups_act_on_fock_vectors_all_signatures D V W (GlobalTheory.ChainFr.Fr.ofModel M) (GlobalTheory.ChainFr.Fr.ofModel M') θ ψ χS χT ω f τ aS aT
    hθ hW hS hT hF hV.ne
  have hL := GlobalTheory.T.lieAction_fockOperators_scalars_trace D V W (GlobalTheory.ChainFr.Fr.ofModel M) (GlobalTheory.ChainFr.Fr.ofModel M') θ ψ χS χT ω f τ aS aT
    hθ hW hS hT hF
  have hC : CompactFock ψ θ M M' ω f τ aS aT := by
    obtain ⟨x, y, hx, hy, hk⟩ := hK
    refine ⟨x, y, hx, hy, fun g hg k hk' P => ?_⟩
    have e := hk g hg k hk' P
    rwa [GlobalTheory.ChainFr.ptF_ofModel] at e
  refine ⟨torusVac_of_compactFock ψ θ M M' ω f τ aS aT hC, hC, ?_, ?_⟩
  · intro X hX P z
    have e := hL.1 X hX P z
    rw [GlobalTheory.ChainFr.ptF_ofModel] at e
    rw [sub_eq_add_neg, ← neg_smul]
    exact e
  · intro Y hY P z
    have e := hL.2 Y hY P z
    rw [GlobalTheory.ChainFr.ptF_ofModel] at e
    exact e

end GlobalTheory.VacuumCharacter

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLevelMovesDualVectorUpperStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentLevel_moves_dualVector_upper : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ x : I.Gf, x ∈ I.Kset → K2cong I g e0 z0 bw x → ∀ j : Fin k, (I.fmat x - 1) *ᵥ bwd j ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (Set.range e0 ∪ bwd '' {l | j < l}) := by
  first | exact @GlobalTheory.SeeConjBwd.bwd_move | exact GlobalTheory.SeeConjBwd.bwd_move | (intros; apply GlobalTheory.SeeConjBwd.bwd_move <;> assumption)
end

