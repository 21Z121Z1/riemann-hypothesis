import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ChainTw.TwLaw
variable {D : D7}

theorem levChi_flag (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    Lev.levChi V β (Lev.flagL (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) κ =
      Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) κ := by
  unfold Lev.levChi levFn
  congr 3
  simp only [Lev.flagL, Lev.withP, Lev.datY, LevelP.full, LevelP.triv, if_true]
  exact (Lev.subgroupCharExtension_one_apply _ _).trans (Lev.subgroupCharExtension_one_apply _ _).symm

theorem lift_one_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) (hκ : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) :
    Lev.IsLevelLift V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) 1 κ := by
  refine ⟨(Subgroup.mem_inf.1 hκ).1, hκ.2.1, ?_⟩
  have h2 := hκ.2.2
  simp only [Lev.datY, LevelP.triv, if_true] at h2
  exact Subgroup.mem_bot.1 h2

theorem lift_one_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β L 1 = 1 := by
  unfold Lev.levChi
  rw [map_one]
  have : levFn β L 1 = 1 := (levChar D.sp.cm V.gram β L).map_one
  rw [this, Units.val_one]

set_option maxHeartbeats 1000000 in
open Classical in

theorem vecLawQ (D : D7) (c : Com D) (w : Twist D) (hw : w.Is c) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D)
    (hs : IsStage c w k s) (hs' : IsStage c w (k + 1) s') (p : Step c s s') (hp : IsStep w (k + 1) p) :
    VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L)
      (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  obtain ⟨hr, hL, hfs⟩ := hs
  obtain ⟨hr', hL', hfs'⟩ := hs'
  obtain ⟨f₀, hv⟩ := hp.vec
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
  rw [hw.union] at hres uS uT
  have hG : ∀ PP ∈ w.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.chi (k + 1) PP)⁻¹ ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.chi (k + 1) PP)⁻¹ := fun PP hP => by
    rw [← hw.chiPg (k + 1) PP hP]; exact hres PP (Finset.mem_union_left _ hP)
  have hQ : ∀ PP ∈ w.Q, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.ξ PP) ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.ξ PP) := fun PP hP => by
    have := hres PP (Finset.mem_union_right _ hP)
    rwa [hw.chiQ (k + 1) PP hP, inv_inv] at this
  rw [hL] at hv
  have ea : s.V.rank = D.R.r + k * D.R.t := hfs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hfs'.rank
  have law := fun {g0 : G0 w.Pg D.R.r} {g : GA D s.V} {h : GA D s'.V} =>
    @GlobalTheory.StepVecLaw.step_law D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β f₀ p.f
      hp.weil hfs.sigOK hfs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
      hfs.selfDual hfs'.selfDual hfs.frame hfs'.frame D.R.r D.R.t k hr hr' ea eb w.Pg w.Q hw.disj w.chi w.ξ hv hG hQ uS uT g0 g h
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · rw [hL] at hκ ⊢
    have h1 := law (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ) (lift_one_one _ _ _)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    have hne : Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t k hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B) κ ≠ 0 := by
      unfold Lev.levChi; exact Units.ne_zero _
    exact (inv_smul_eq_iff₀ hne).1 h1
  · rw [hL'] at hκ ⊢
    have h1 := law (lift_one_one _ _ _) (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    exact h1

theorem levelLawQ : ∀ D : D7, LevelLawQ D := by
  intro D _ c w hw k hk s s' hs hs' p hp φ
  obtain ⟨h1, h2⟩ := vecLawQ D c w hw k hk s s' hs hs' p hp
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      κ (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ (h1 κ hκ) φ
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      1 (one_mem _) κ (Subgroup.mem_inf.1 hκ).1 _ (h2 κ hκ) φ

end GlobalTheory.ChainTw.TwLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitVectorRowsConjugate
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.LineV

open GlobalTheory.PiTensorInner

theorem tprod_eq_smul_of_prod_inner {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (a b : ∀ i, E i) (l : ℂ)
    (h : ∀ x : ∀ i, E i, ∏ i, ⟪a i, x i⟫_ℂ = l * ∏ i, ⟪b i, x i⟫_ℂ) :
    PiTensorProduct.tprod ℂ a = (starRingEnd ℂ l) • PiTensorProduct.tprod ℂ b := by
  set w := PiTensorProduct.tprod ℂ a - (starRingEnd ℂ l) • PiTensorProduct.tprod ℂ b with hw
  have hy : ∀ y, ipT y w = 0 := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [hw, map_smul, LinearMap.smul_apply, map_sub, map_smulₛₗ, ipT_tprod, ipT_tprod, h x]
      simp
    | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  by_contra hne
  have := ipT_pos w (sub_ne_zero.2 hne)
  rw [hy w] at this
  simp at this

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop.LineV

theorem eq_of_evS_ae {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {θ : InfFam D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {J : Set (GA D (D.sp.Y 0))}
    {χ : GA D (D.sp.Y 0) → ℂ} (t : GA D (D.sp.Y 0)) {T T' : SmT M →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)}
    (hT : T ∈ MultT θ M J χ) (hT' : T' ∈ MultT θ M J χ) (a b : M.Vec)
    (he : evS X h t (T (PiTensorProduct.tprod ℂ a)) =ᵐ[muX X] evS X h t (T' (PiTensorProduct.tprod ℂ b))) :
    T (PiTensorProduct.tprod ℂ a) = T' (PiTensorProduct.tprod ℂ b) := by
  have hU := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 ((mem_multT θ M J χ T).1 hT)
  have hU' := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 ((mem_multT θ M J χ T').1 hT')
  have hva : (PiTensorProduct.lift.symm T : MMap M) a = T (PiTensorProduct.tprod ℂ a) := by
    simp [PiTensorProduct.lift_symm]
  have hvb : (PiTensorProduct.lift.symm T' : MMap M) b = T' (PiTensorProduct.tprod ℂ b) := by
    simp [PiTensorProduct.lift_symm]
  have hc := (hU.aut a).cont
  have hl := (hU.aut a).left
  have hc' := (hU'.aut b).cont
  have hl' := (hU'.aut b).left
  rw [← hva, ← hvb] at he ⊢
  generalize (PiTensorProduct.lift.symm T : MMap M) a = f at hc hl he ⊢
  generalize (PiTensorProduct.lift.symm T' : MMap M) b = f' at hc' hl' he ⊢
  let ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA := iotaX X h
  have hQ : ∀ γ ∈ X.B.I.GFset, ι.symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    refine (Formalism.IndefR.RationalEmbedding.iota_rat D (ι.symm γ)).2 ?_
    show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact GlobalTheory.TranslatedEvalInj.castGA_symm_mem _ γ hγ
  let φ : X.B.I.GA → ℂ := fun x => f (ι.symm x * t) - f' (ι.symm x * t)
  have hφc : Continuous φ := by
    have hm : Continuous fun x : X.B.I.GA => ι.symm x * t := ι.symm.continuous.mul continuous_const
    exact (hc.comp hm).sub (hc'.comp hm)
  have hφi : ∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y := by
    intro γ hγ y
    simp only [φ, map_mul, mul_assoc]
    rw [hl _ (hQ γ hγ), hl' _ (hQ γ hγ)]
  have hae : φ =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
    have he' : evS X h t f =ᵐ[muX X] evS X h t f' := he
    filter_upwards [he'] with x hx
    simp only [φ, Pi.zero_apply, sub_eq_zero]
    exact hx
  have hz := GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hφc hφi hae
  funext g
  have e := hz (ι (g * t⁻¹))
  simp only [φ, ContinuousMulEquiv.symm_apply_apply, inv_mul_cancel_right, sub_eq_zero] at e
  exact e

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop.LineV

theorem line_of_eq {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {θ : InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ)
    {T T' : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hT : T ∈ MultT θ M J χ) (hT' : T' ∈ MultT θ M J χ) (v₀ v : M.Vec)
    (h1 : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) (hT0 : T ≠ 0)
    (he : T (PiTensorProduct.tprod ℂ v₀) = T' (PiTensorProduct.tprod ℂ v)) :
    ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  obtain ⟨ν, 𝓖, hν, h𝓖⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  have hUm := (mem_multT θ M J χ T).1 hT
  have hUm' := (mem_multT θ M J χ T').1 hT'
  have hU := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 hUm
  set U : MMap M := PiTensorProduct.lift.symm T with hUd
  set U' : MMap M := PiTensorProduct.lift.symm T' with hUd'
  have hval : ∀ x, U x = T (PiTensorProduct.tprod ℂ x) := fun x => by simp [U, PiTensorProduct.lift_symm]
  have hval' : ∀ x, U' x = T' (PiTensorProduct.tprod ℂ x) := fun x => by simp [U', PiTensorProduct.lift_symm]
  have hUv : U v₀ = U' v := by rw [hval, hval', he]
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ hz => by
    have h1τ := h1 τ
    rw [hz, norm_zero] at h1τ
    exact zero_ne_one h1τ
  have hU0 : U v₀ ≠ 0 := by
    intro hz
    apply hT0
    have h0 : U = 0 := GlobalTheory.TranslatedEvalInj.eq_zero_of_value hU v₀ hne hz
    have : T = PiTensorProduct.lift U := (PiTensorProduct.lift.apply_symm_apply T).symm
    rw [this, h0, map_zero]
  obtain ⟨c1, hc1⟩ := GlobalTheory.MultFinite.schurMult hP ν 𝓖 hθ hν h𝓖 U hUm U hUm
  obtain ⟨c2, hc2⟩ := GlobalTheory.MultFinite.schurMult hP ν 𝓖 hθ hν h𝓖 U' hUm' U hUm
  have hpos := GlobalTheory.SchurConst.re_pos_of_isMultIP M ν 𝓖 hν h𝓖 U hc1 v₀ (hU.aut v₀).cont (hU.aut v₀).left hU0
  have hc10 : c1 ≠ 0 := fun hz => by simp [hz] at hpos
  have key : ∀ x : M.Vec, ∏ τ, ⟪v₀ τ, x τ⟫_ℂ = (c2 / c1) * ∏ τ, ⟪v τ, x τ⟫_ℂ := by
    intro x
    have e1 := (hc1 v₀ x).2
    have e2 := (hc2 v x).2
    rw [hUv, e2] at e1
    have e3 : ∏ τ, ⟪v₀ τ, x τ⟫_ℂ = ∏ τ, ⟪(v₀ τ : M.H τ), (x τ : M.H τ)⟫_ℂ := rfl
    have e4 : ∏ τ, ⟪v τ, x τ⟫_ℂ = ∏ τ, ⟪(v τ : M.H τ), (x τ : M.H τ)⟫_ℂ := rfl
    rw [e3, e4, div_mul_eq_mul_div, eq_div_iff hc10, mul_comm, e1]
  have hl := tprod_eq_smul_of_prod_inner v₀ v _ key
  refine ⟨_, ?_, hl⟩
  intro hz
  rw [hz, zero_smul] at hl
  have hp := GlobalTheory.PiTensorInner.ipT_tprod v₀ v₀
  simp only [hl, map_zero] at hp
  have : ∏ τ, ⟪v₀ τ, v₀ τ⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    show ((‖(v₀ τ : M.H τ)‖ : ℂ)) ^ 2 = 1
    rw [h1]; simp
  rw [this] at hp
  exact zero_ne_one hp

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop

theorem unit_vector_line_conjugate : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → ∀ (v₀ v : (W.Q.Rl.MY 0).Vec), ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → (∀ τ, ‖(v₀ τ : (W.Q.Rl.MY 0).H τ)‖ = 1) → ∀ T ∈ ThetaLiftSpaceZero W, T ≠ 0 → ∀ φ : L2X W.S.X, (φ : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) → star φ ∈ HHX W.S.X → ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB v₀ v hv hn T hTm hT0 φ hφ hst
  obtain ⟨-, hθ, -, hM, -, -⟩ := GlobalTheory.T.bottom_hypothesis_matching_central W hB
  have hMt : Matches W.S.X W.Q.instEq (rJ W) (rChi W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
    have := hM 1 (one_mem _) (Subgroup.one_mem _)
    rwa [one_mul] at this
  obtain ⟨⟨j, hj, hjT⟩, -⟩ := GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (rJ W) (rChi W)
    (show GA D (D.sp.Y 0) from W.Q.tS) v (by simp) hθ hB.gap hB.idE hMt hv
  obtain ⟨T', hT'⟩ := hj.2 ⟨star φ, hst⟩
  have h1 := hjT T'
  rw [hT'] at h1
  have he : evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX W.S.X]
      evS W.S.X W.Q.instEq (show GA D (D.sp.Y 0) from W.Q.tS) (T'.1 (PiTensorProduct.tprod ℂ v)) := by
    filter_upwards [hφ, h1, Lp.coeFn_star φ] with x a1 a2 a3
    rw [← a1]
    have a4 := a3.symm.trans a2
    simpa using congrArg star a4
  exact LineV.line_of_eq hCR hθ hTm T'.2 v₀ v hn hT0 (LineV.eq_of_evS_ae W.S.X W.Q.instEq _ hTm T'.2 v₀ v he)

end GlobalTheory.MiTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.WeilTup

variable {D : D7}

theorem hecke_mul {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') : IsHeckeChar D (χ * χ') :=
  ⟨by show Continuous (fun x => χ x * χ' x); exact h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem hecke_inv {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨by rw [show ⇑χ⁻¹ = fun x => (χ x)⁻¹ from funext fun x => MonoidHom.inv_apply χ x]; exact h.1.inv,
    fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem resEta_of_diff {μ χ : (AE D)ˣ →* Circle} {n : ℕ} (hA : ResEta D μ (n + 1)) (hB : ResEta D (μ * χ⁻¹) n) :
    ResEta D χ 1 := by
  refine ⟨hA.1, fun e he a => ?_⟩
  have h1 := hA.2 e he a
  have h2 := hB.2 e he a
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, pow_succ] at h2
  rw [pow_one]
  exact (mul_left_cancel (mul_inv_eq_iff_eq_mul.1 h2)).symm

theorem weilOK_fam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c), f.RowOK → f.ColOK → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t, WeilOK (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR hC hτ t
  have hmE : ¬ Odd D.R.m := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hX := hP.bot.hyp.2.2.2.1.chain.ωX t
  simp only [Formalism.IndefR.Lift.chrStep, if_neg hmE] at hX
  have hη : ∀ j' (h' : j' + 2 * 0 + 2 = D.R.m), IsHeckeChar D (pk W).eta ∧ ResEta D (pk W).eta 1 := by
    intro j' h'
    have e : j' + 1 + 1 = D.R.m := by omega
    have hk := hC.kom t (j' + 1) (by omega)
    have hμH : IsHeckeChar D ((pk W).toLevCh.mu t D.R.m) := by
      have h1 : IsHeckeChar D ((pk W).toLevCh.mu t (j' + 1 + 1)) := hk.hecS
      rw [e] at h1; exact h1
    have hμR : ResEta D ((pk W).toLevCh.mu t D.R.m) (D.sp.X'.rank + 1) := by
      have h1 : ResEta D ((pk W).toLevCh.mu t (j' + 1 + 1)) (D.sp.X (j' + 1 + 1)).rank := hk.resT
      have h2 : D.sp.X'.rank + f.c.Lz.rank = (D.sp.X (j' + 1 + 1)).rank := (f.c.oT (j' + 1 + 1) e).rank_add
      rw [← h2, (hτ j' h').1, e] at h1
      exact h1
    have hH : IsHeckeChar D (pk W).eta := by
      have h1 := hecke_mul (hecke_inv hX.hecT) hμH
      rwa [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right] at h1
    exact ⟨hH, resEta_of_diff hμR hX.resT⟩
  refine ⟨?_, ?_, hτ⟩
  · intro j σ h
    obtain ⟨hHη, hRη⟩ := hη (j + 2 * σ + 2) (by omega)
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j (σ + 1) h
    obtain ⟨-, -, fV, fW⟩ := (hR.row t).sFB j σ h
    have hL := (f.c.bes j (σ + 1) h).line.1
    have hL' := (f.c.bes (j + 1 + 1) σ (idx_step h)).line.1
    obtain ⟨omz, homz⟩ := hE (f.c.bes j (σ + 1) h).L (D.sp.X (j + 1)) (pk W).ψ (pk W).eta⁻¹ ((pk W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omz', homz'⟩ := hE (D.sp.X (j + 1)) (f.c.bes (j + 1 + 1) σ (idx_step h)).L (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1))
      (pk W).eta⁻¹ hk1.std hk1.hecS hzH hk1.resS (by rw [hL']; exact hzR)
    refine ⟨(pk W).toLevCh.mu t (j + 1), (pk W).toLevCh.mu t (j + 1 + 1), (pk W).eta⁻¹, omz, omz', bV, fW, ?_, ?_, ?_, ?_⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [fV]; exact hk1
    · rw [fV]; exact homz'
  · intro j h
    have e : j + 1 + 1 = D.R.m := by omega
    obtain ⟨hHη, hRη⟩ := hη j h
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j 0 h
    have hL := (f.c.bes j 0 h).line.1
    have hXH : IsHeckeChar D ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) := by rw [e]; exact hX.hecT
    have hXR : ResEta D ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) D.sp.X'.rank := by rw [e]; exact hX.resT
    obtain ⟨omz, homz⟩ := hE (f.c.bes j 0 h).L (D.sp.X (j + 1)) (pk W).ψ (pk W).eta⁻¹ ((pk W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omT', homT⟩ := hE (D.sp.X (j + 1)) D.sp.X' (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1))
      ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹) hk1.std hk1.hecS hXH hk1.resS hXR
    obtain ⟨omz'', homz''⟩ := hE (D.sp.X (j + 1)) f.c.Lz (pk W).ψ ((pk W).toLevCh.mu t (j + 1 + 1)) (pk W).eta⁻¹⁻¹
      hk1.std hk1.hecS (by rw [inv_inv]; exact hHη) hk1.resS (by rw [(hτ j h).1, inv_inv]; exact hRη)
    have hμ1 : (pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹ * (pk W).eta⁻¹⁻¹ = (pk W).toLevCh.mu t (j + 1 + 1) := by
      rw [inv_inv, inv_mul_cancel_right]
    have key : ∀ n (e' : D.R.m - 1 = n), IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X' ((pk W).toLevCh.mu t (j + 1 + 1))
        ((pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹)
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX t) e') := by
      intro n e'
      subst e'
      rw [e]
      exact hX
    refine ⟨(pk W).toLevCh.mu t (j + 1), (pk W).eta⁻¹, (pk W).toLevCh.mu t (j + 1 + 1),
      (pk W).toLevCh.mu t (j + 1 + 1) * (pk W).eta⁻¹, omz, omT', omz'', bV, ?_, ?_, ?_, homT, key (j + 1) (idx_top h), homz''⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [hμ1]; exact hk1

end GlobalTheory.Fam.WeilTup

end
end

