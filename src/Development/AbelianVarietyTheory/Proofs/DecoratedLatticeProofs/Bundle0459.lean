import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MonoAtOfJacFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceComponentRingHomIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section
namespace GlobalTheory.FinPl.SplitPhi
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  have h := p.sec_pr 1
  rw [mul_one] at h
  rw [← h, p.pr_sec, map_one]

theorem prV_toEAf_e_ne (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.F)} (hw : w ≠ p.v) :
    Formalism.UG.prV (E := D.host.E) w (toEAf D p.e) = 0 := by
  obtain ⟨ε, hε, he⟩ := p.above
  obtain ⟨h1, h2, -⟩ := p.split
  have : p.e = algebraMap (AF D.host.F) (AE D) ε * p.e := by
    rw [← he, add_mul, h1, mul_comm (cA D p.e), h2, add_zero]
  rw [this]
  exact GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw _

theorem prV_toEAf_eps (p : SplitPt D k) {ε : AF D.host.F} (hε : IsPlaceIdem D p.v ε) :
    Formalism.UG.prV (E := D.host.E) p.v (toEAf D (algebraMap (AF D.host.F) (AE D) ε)) = 1 := by
  obtain ⟨α, rfl, h1, -⟩ := hε
  have h1' : (Formalism.UG.evalV D.host.F p.v) ((sndA D.host.F) (pairA D.host.F 0 α)) = 1 := h1
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [Formalism.IndefR.Datum.toEAf, finPart, Formalism.UG.prV]
  rw [h1']
  rfl

theorem prF_eq_zero (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (y : EAf D) (hy : Formalism.UG.prV (E := D.host.E) p.v y = 0) : p.prF he y = 0 := by
  have h0 : toEAf D p.e * y = 0 := by
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [hy, mul_zero]
    · rw [prV_toEAf_e_ne p hw, zero_mul]
  have : p.prF he y = p.prF he (toEAf D p.e * y) := by
    rw [map_mul, p.prF_toEAf he, pr_e, one_mul]
  rw [this, h0, map_zero]

theorem prF_IE_prV (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (y : EAf D) : p.prF he (Formalism.UG.P.afsplitIE p.v (Formalism.UG.prV (E := D.host.E) p.v y)) = p.prF he y := by
  rw [← sub_eq_zero, ← map_sub]
  apply prF_eq_zero p he
  rw [map_sub, Formalism.UG.P.afsplit_prV_IE, sub_self]

def phi (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) :
    D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k where
  toFun x := p.prF he (Formalism.UG.P.afsplitIE p.v x)
  map_one' := by
    have := prF_IE_prV p he 1
    rw [map_one (Formalism.UG.prV (E := D.host.E) p.v), map_one (p.prF he)] at this
    exact this
  map_mul' x y := by simp only [map_mul]
  map_zero' := by simp only [map_zero]
  map_add' x y := by simp only [map_add]

theorem phi_apply (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (x : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F) :
    phi p he x = p.prF he (Formalism.UG.P.afsplitIE p.v x) := rfl

theorem phi_prV (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (a : AE D) : phi p he (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a := by
  rw [phi_apply, prF_IE_prV, p.prF_toEAf he]

theorem phi_inclE (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (c : D.host.E) : phi p he (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c) := by
  rw [← phi_prV p he]
  rfl

theorem tensInt_iff (v : HeightOneSpectrum (𝓞 D.host.F)) (z : D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    z ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
        (v.adicCompletionIntegers D.host.F).toSubring ↔
      Formalism.UG.P.afsplitIE v z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine ⟨Formalism.UG.P.afsplit_IE_int v z, fun h => ?_⟩
  have := Formalism.UG.P.afsplit_prV_int v _ h
  rwa [Formalism.UG.P.afsplit_prV_IE] at this

theorem sigR_sigR (z : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (· ⊗ₜ[D.host.F] x) (star_star a)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem toEAf_cA (a : AE D) : toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul y e => rfl

theorem sigR_mem_iff (s : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈
    Formalism.L2.Herm.intAf D.host.F D.host.E ↔ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine ⟨fun h => ?_, GlobalTheory.LevSplit.sigR_int⟩
  have := GlobalTheory.LevSplit.sigR_int h
  rwa [sigR_sigR] at this

theorem one_sub_e_mul (p : SplitPt D k) (y : EAf D)
    (hy : ∀ w, w ≠ p.v → Formalism.UG.prV (E := D.host.E) w y = 0) :
    (1 - toEAf D p.e) * y = toEAf D (cA D p.e) * y := by
  obtain ⟨ε, hε, he⟩ := p.above
  rw [← sub_eq_zero, ← sub_mul, sub_sub, ← RingHom.map_add, he]
  refine Formalism.UG.P.afsplit_inj _ fun w => ?_
  rw [map_mul]
  by_cases hw : w = p.v
  · subst hw; rw [map_sub, map_one, prV_toEAf_eps p hε, sub_self, zero_mul]
  · rw [hy w hw, mul_zero]

theorem sigR_inclE (v : HeightOneSpectrum (𝓞 D.host.F)) (c : D.host.E) :
    Formalism.UG.sigR (sigD D) (v.adicCompletion D.host.F) (Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) c) =
      Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (sigD D c) := by
  simp only [Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem exists_ringHom_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∃ φ : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k,
      (∀ a : AE D, φ (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a) ∧
      (∀ c : D.host.E, φ (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c)) ∧
      (∀ c : D.host.E, φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F)
          (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c)) = p.pr (incA D (sigD D c))) ∧
      ∀ z, z ∈ Formalism.UG.tensInt (F := D.host.F) (p.v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
          (p.v.adicCompletionIntegers D.host.F).toSubring ↔
        φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p PP he
  refine ⟨phi p he, phi_prV p he, phi_inclE p he, fun c => by rw [sigR_inclE]; exact phi_inclE p he (sigD D c), fun z => ?_⟩
  set y := Formalism.UG.P.afsplitIE p.v z with hy
  have hsup : ∀ w, w ≠ p.v → Formalism.UG.prV (E := D.host.E) w y = 0 := fun w hw =>
    Formalism.UG.P.afsplit_prV_IE_ne p.v w hw z
  have hsig : Formalism.UG.P.afsplitIE p.v (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y := by
    rw [hy]; exact (Formalism.UG.P.afsplit_sigR_IE (sigD D) p.v z).symm
  have h1 := tensInt_iff p.v z
  have h2 := p.mem_intAf_iff he y
  have h3 := one_sub_e_mul p y hsup
  have h4 := p.prF_mem_iff he (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y)
  have h5 : toEAf D (cA D p.e) * y = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
      (toEAf D p.e * Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) := by
    rw [RingHom.map_mul, sigR_sigR, toEAf_cA]
  refine h1.trans (h2.trans ?_)
  rw [h3, h5, sigR_mem_iff, ← h4]
  have e1 : phi p he z = p.prF he y := phi_apply p he z
  have e2 : phi p he (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) =
      p.prF he (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) := (phi_apply p he _).trans (congrArg _ hsig)
  rw [e1, e2]
  exact and_comm

end GlobalTheory.FinPl.SplitPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraProjectionLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLevelP

theorem eq_mul_of_inv_mul {a b c d : ℂ} (ha : a ≠ 0) (h : a⁻¹ * b = c * d) : b = a * c * d := by
  rw [mul_assoc, ← h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

theorem mul_eq_of {a c d u v p q : ℂ} (h1 : u = a * p) (h2 : v = c * d * q) : u * v = a * (c * d) * (p * q) := by
  rw [h1, h2]; ring

theorem const_eq {a b c I : ℂ} (hb : b ≠ 0) : a * b⁻¹ * (b * c) * I = c * a * I := by
  field_simp

set_option maxHeartbeats 800000 in

theorem ioX_levChi_gen {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ)
    (hL : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T)
    (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (hF : F.1 ∈ CXP R P t) (κ : GA D (Yc D (D.R.m - 1)))
    (hκ : κ ∈ levS (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P)) (φ x g) :
    (R.ioX t F).1 (R.ItX φ x) (g * κ) =
      levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ * (R.ioX t F).1 (R.ItX φ x) g := by
  have hθ : IsInfFam R.θ := hm.inf
  have hio := hc.ioX t
  have hκG : κ ∈ GfC (Yc D (D.R.m - 1)) := hκ.1
  have hκP : Lev.finE (Yc D (D.R.m - 1)) κ ∈ parLev D.sp.cm (Yc D (D.R.m - 1)).gram (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) := hκ.2.1
  have hκH : rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ) ∈ P.H := hκ.2.2
  have hκl : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)
      (rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ)) κ := ⟨hκG, hκP, rfl⟩
  refine (GlobalTheory.Fam.FamInhab.lifts_top (R := R) hL t
    (rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ))).elim fun κ' hκ' => ?_
  have hlaw := GlobalTheory.StepLaw.last_step_law R hL hθ hc.ωX hc.vX t _ κ κ' hκl hκ'
  have hsS : levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' ≠ 0 := levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)⁻¹ •
      R.ωX t (κ, κ') (R.vX t) =
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ • R.vX t := hlaw
  have hv : R.ωX t (κ, κ') (R.vX t) =
      (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ *
        (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹) • R.vX t := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ _ _ _ _ (R.ωX t) hθ (hc.ωX t)
    _ _ _ _ (R.vX t) (hc.ptX t) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ _ _ _ _ (R.ωX t) (hc.ωX t)
    (R.ptX t φ) (hc.ptX t φ)
  have e1 : levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ =
      ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := R.datYt t (D.R.m - 1) R.triv) P, extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hfd : (R.νX t).IsHaarMeasure ∧ IsFundamentalDomain (GQ D.sp.X') (R.fdX t) (R.νX t) :=
    ⟨(hm.νX t).1.1, (hm.νX t).2⟩
  have hi := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable D.sp.X'
  haveI i1 := hi.1
  haveI i2 := hi.2.1
  haveI i3 := hi.2.2.1
  haveI i4 := hi.2.2.2
  have htg : IsTopologicalGroup (GA D D.sp.X') := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig D.sp.X'.gram))
  haveI := hfd.1
  haveI hR : (R.νX t).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') (R.νX t) = R.νX t := map_mul_right_eq_self _ κ'
  have hFv := (GlobalTheory.StepLevelP.IoLevPf.multT_val R.θ R.MX _ _ F.1 hF x).1
  have hF1 := ((GlobalTheory.Fam.FamInhab.cxp_iff P t F.1).1 hF).2 ⟨_, hκH⟩ κ' hκ' x
  have hF2 : ∀ h, F.1 x (h * κ') =
      levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' * ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * F.1 x h := fun h =>
    eq_mul_of_inv_mul hsT (hF1 h)
  have hpt' : R.ωX t (κ, κ') (R.ptX t φ) = (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹) • R.ptX t φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ D.sp.X') (R.νX t)
    (R.fdX t) hfd.2 κ' hmap
    (fun h => thetaKO (R.ωX t) (g * κ) h (R.ptX t φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D (D.R.m - 1))).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, hFv γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO (R.ωX t) (g * κ) (h * κ') (R.ptX t φ) * F.1 x (h * κ') =
      (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' * ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ))) * (thetaKO (R.ωX t) g h (R.ptX t φ) * F.1 x h) := fun h => by
    exact mul_eq_of (hth g h) (hF2 h)
  refine (hio.eq F φ x (g * κ)).symm.trans (hint.2.symm.trans ?_)
  refine (congrArg (fun f => ∫ h in R.fdX t, f h ∂(R.νX t)) (funext hpw)).trans ((integral_const_mul _ _).trans ?_)
  refine (const_eq hsT).trans ?_
  exact congrArg₂ (· * ·) e1.symm (hio.eq F φ x g)

theorem ioX_levChi : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t (F : LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e)), F.1 ∈ CXP (pk W) (lvP W) t → ∀ κ ∈ levS (Yc D (D.R.m - 1)) ((pk W).βY (D.R.m - 1)) ((pk W).datYt t (D.R.m - 1) (lvP W)), ∀ φ x g, ((pk W).ioX t F).1 ((pk W).ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) ((pk W).βY (D.R.m - 1)) ((pk W).datYt t (D.R.m - 1) (lvP W)) κ * ((pk W).ioX t F).1 ((pk W).ItX φ x) g :=
  fun W hW t F hF κ hκ φ x g => ioX_levChi_gen (pk W) (lvP W) hW.bot.hyp.2.2.2.1.lev hW.bot.hyp.2.2.2.1.models
    hW.bot.hyp.2.2.2.1.chain t F hF κ hκ φ x g

end GlobalTheory.StepLevelP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiLatticeSplitsAtNormalFramePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam

theorem monoW_of_normalFrames : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.jac j ρ h).lev (a.x (j + 1)).vol).d (N (j + 1)) (a.x (j + 1)).L (PP.under (𝓞 D.host.F)) := by
  intro D ψ _ a y βT PP l FY sc hN hx N M hsdN hIntN _ _ j ρ h
  have hs := l.hs
  have hc : j + 1 + 2 * ρ = l.s + 1 := by omega
  have hm := GlobalTheory.JacMono.monoAt_of_jacFrame l.q l.unit ((y.jac j ρ h).lev (a.x (j + 1)).vol)
    (hsdN (j + 1) (by omega)) (hx (j + 1) (by omega)).sd (hN.1 j) (hN.2.2.1 j ρ h) (hN.2.2.2.2.1 j ρ h _ hc)
    (hIntN (j + 1) _ hc) (l.latX (j + 1) (by omega))
  rw [l.under] at hm
  exact hm

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocallyPrincipalAdelicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_locallyPrincipal_adelic : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.idV_principal_at | exact GlobalTheory.FinPl.idV_principal_at | (intros; apply GlobalTheory.FinPl.idV_principal_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameVectorLatticeCriterionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_vector_lattice_criterion : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (c : ℕ) (hc : 0 + c = G.s + 1) (L : Lat (d.st 0).V), Formalism.L2.DIV.IsFrame (d.st 0).β (d.st 0).Λ → Moves (d.st 0).V (d.t 0) (d.st 0).Λ L (· = G.q.v) → ∀ y : GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin c → G.k, (fun r => G.q.sec (((G.FY 0 c hc).β *ᵥ y) r)) ∈ latV (d.st 0).V L (· = G.q.v) ↔ (∀ a, y (Sum.inl a) ∈ 𝒪[G.k]) ∧ ∀ i : Fin c, ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k] := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.latV_normalFrame_zero | exact GlobalTheory.Core.Mi.LatMatch.latV_normalFrame_zero | (intros; apply GlobalTheory.Core.Mi.LatMatch.latV_normalFrame_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAComponentsMemCompletedLatticeOffPrimesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfA_components_mem_completedLattice_offPrimes : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.HalfAComp.zmem | exact GlobalTheory.HalfAComp.zmem | (intros; apply GlobalTheory.HalfAComp.zmem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfASignTraceIsIntegerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfA_signTrace_isInteger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (LinearMap.toMatrix' x') (LinearMap.toMatrix' x')) := by
  first | exact @GlobalTheory.TraceInt.trace_int | exact GlobalTheory.TraceInt.trace_int | (intros; apply GlobalTheory.TraceInt.trace_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfBComponentsMemCompletedLatticeOffConjStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfB_components_mem_completedLattice_offConj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) - ((LinearMap.toMatrix' y').map fun r => cA D e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.HalfBComp.ybmem | exact GlobalTheory.HalfBComp.ybmem | (intros; apply GlobalTheory.HalfBComp.ybmem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharUnramifiedAtQuotientSameResidual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResUnr

open Formalism.L2.Host

theorem exists_int_div {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (k : E)
    (hk : P.valuation E k = 1) :
    ∃ a s : 𝓞 E, a ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧ k * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
  obtain ⟨n, d, h | h⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := E) k
  · refine ⟨n, d, ?_, d.2, h⟩
    rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E), ← h, map_mul, hk, one_mul,
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact d.2
  · refine ⟨d, n, d.2, ?_, h⟩
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, hk, one_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) (r := (d : 𝓞 E)) P).2 d.2] at h2
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).1 h2

theorem loc_eq_of_isRes {D : D7} {H₁ H₂ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {ξ : (kP PP)ˣ →* ℂˣ}
    (h₁ : IsRes H₁ PP ξ) (h₂ : IsRes H₂ PP ξ) (x : (PP.adicCompletion D.host.E)ˣ) (hx : IsUnitAt PP x) :
    H₁.loc PP x = H₂.loc PP x := by
  have hc : IsClopen {x : (PP.adicCompletion D.host.E)ˣ | IsUnitAt PP x} := by
    have := (Valued.isClopen_sphere (PP.adicCompletion D.host.E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := PP.adicCompletion D.host.E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  have hK : ∀ k : D.host.Eˣ, PP.valuation D.host.E (k : D.host.E) = 1 → H₁.locK PP k = H₂.locK PP k := by
    intro k hk
    obtain ⟨a, s, ha, hs, hks⟩ := exists_int_div PP (k : D.host.E) hk
    haveI : PP.asIdeal.IsMaximal := PP.isMaximal
    have hne : ∀ b : 𝓞 D.host.E, b ∉ PP.asIdeal → algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := fun b hb h0 =>
      hb (by rw [(IsFractionRing.injective (𝓞 D.host.E) D.host.E) (h0.trans (map_zero _).symm)]; exact PP.asIdeal.zero_mem)
    have hq : ∀ b : 𝓞 D.host.E, b ∉ PP.asIdeal → (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun b hb h0 =>
      hb (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let A : D.host.Eˣ := Units.mk0 _ (hne a ha)
    let S : D.host.Eˣ := Units.mk0 _ (hne s hs)
    let ua : (kP PP)ˣ := Units.mk0 _ (hq a ha)
    let us : (kP PP)ˣ := Units.mk0 _ (hq s hs)
    have hkS : k * S = A := Units.ext hks
    have e1 : H₁.locK PP A = H₂.locK PP A := ((h₁ a A ua rfl rfl).symm.trans (h₂ a A ua rfl rfl))
    have e2 : H₁.locK PP S = H₂.locK PP S := ((h₁ s S us rfl rfl).symm.trans (h₂ s S us rfl rfl))
    rw [← hkS, map_mul, map_mul, e2] at e1
    exact mul_right_cancel e1
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin PP).induction_on
    (p := fun x => IsUnitAt PP x → H₁.loc PP x = H₂.loc PP x) x ?_
    (fun k hk => hK k ((PP.valuedAdicCompletion_eq_valuation' _).symm.trans hk)) hx
  exact isClosed_imp hc.2 (isClosed_eq (H₁.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele PP))
    (H₂.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele PP)))

theorem unrAt_div_of_isRes : ∀ (D : D7) (c₁ c₂ : (AE D)ˣ →* Circle) (H₁ H₂ : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), ChrEq c₁ H₁ → ChrEq c₂ H₂ → IsRes H₁ PP ξ → IsRes H₂ PP ξ → GlobalTheory.LFun.UnrAt (F := D.host.F) (c₁ * c₂⁻¹) PP := by
  intro D c₁ c₂ H₁ H₂ PP ξ hc₁ hc₂ h₁ h₂ x hx
  have e : GlobalTheory.LFun.locChar (c₁ * c₂⁻¹) PP x = GlobalTheory.LFun.locChar c₁ PP x * (GlobalTheory.LFun.locChar c₂ PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq hc₁, GlobalTheory.LFun.locChar_eq_of_chrEq hc₂, loc_eq_of_isRes h₁ h₂ x hx, mul_inv_cancel]

end GlobalTheory.ResUnr
end

