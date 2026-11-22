import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0544
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0551
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0554
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem GlobalTheory.FinPl.flatFB_om_shift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LW : Lat B.V) (v : Pl D), IsSelfDualC J.W LV → IsSelfDualC B.V LW → Tame D v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ (x : GA D B.V) (κ : GA D B.V), InK B.V LW (· = v) κ → flatFB s (s.om (1, n * x * κ) f) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s (s.om (1, x) f) := by
  intro D ψ σ J B s LV LW v hLV hLW hv hu f hf n hn hnv x κ hκ
  have hmul : s.om (1, n * x * κ) f = s.om (1, n) (s.om (1, x) (s.om (1, κ) f)) := by
    have : ((1 : GA D J.W), n * x * κ) = (1, n) * (1, x) * (1, κ) := by simp
    rw [this, map_mul, map_mul]; rfl
  have hκf : s.om (1, κ) f = f := by
    refine GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hLV hLW (· = v) ?_ f hf 1 κ ?_ hκ
    · rintro w rfl; exact ⟨hv, hu.1, hu.2⟩
    · refine ⟨one_mem _, ?_⟩
      intro y _
      simp
  have hth : IsThetaFunO ψ J.W B.V (s.om (1, x) f) := s.weil.om_pres _ _ hf.1
  have h := ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B s).equiv _ hth n hn hnv 1 (one_mem _)
  have he : B.o.emb (1, 1) = 1 := map_one B.o.emb
  have he₀ : s.om₀ ((1 : GA D J.W₀), (1 : GA D B.V₀)) = 1 := map_one s.om₀
  rw [map_one, mul_one, he, he₀, Module.End.one_apply] at h
  rw [hmul, hκf, h]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.VacSecondPf

variable {D : D7}

theorem latO_of_none (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (hP : ∀ v, ¬ P v) : latO S T LS LT P = ⊥ := by
  rw [eq_bot_iff, latO, AddSubgroup.closure_le]
  rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
  have h0 : α = 0 := by
    ext v : 1
    exact hα v (hP v)
  subst h0
  rw [SetLike.mem_coe, AddSubgroup.mem_bot]
  have hp : pairA D.host.F 0 0 = 0 := rfl
  ext i j
  simp [hp]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem vac_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (P : Pl D → Prop), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v ∧ UnrAt s v) → ∀ f, Vac ψ J.W B.V LV LW P f → ∀ h₁ ∈ grpOff J.W P, ∀ h₂ ∈ grpOff B.V P, Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s (s.om (h₁, h₂) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ P hP f hf h₁ hh₁ h₂ hh₂
  have hflat : ∀ Q : Pl D → Prop, IsFlatFB s Q (flatFB s) := fun Q => (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ Q).2 σ J B s
  have htheta : IsThetaFunO ψ J.W B.V (s.om (h₁, h₂) f) := s.weil.om_pres _ _ hf.1
  have hth0 : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (h₁, h₂) f)) := (hflat P).Heisenberg₂.theta _ htheta
  by_cases hne : ∃ v, P v
  · obtain ⟨v₀, hv₀⟩ := hne
    have a₀ := (hP v₀ hv₀).1
    have hT : ∀ v, P v → Tame D v := fun v hv => (hP v hv).1.tame
    have L1 := GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW a₀.sdV a₀.sdW P hT
    have L0 := GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ a₀.sdV₀ a₀.sdW₀ P hT
    have hg : Vac ψ J.W B.V LV LW P (s.om (h₁, h₂) f) := (L1 f).2.1 hf h₁ hh₁ h₂ hh₂
    have hgv := ((L1 _).1.mp hg).2
    refine (L0 _).1.mpr ⟨hth0, fun v hv => ?_⟩
    exact (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B s LV LV₀ LW LW₀ v (hP v hv).1 (hP v hv).2 (flatFB s) (hflat (· = v))
      ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B s) _ (hgv v hv)).1
  · push_neg at hne
    have hbot := latO_of_none J.W₀ B.V₀ (LV₀ : Set _) (LW₀ : Set _) P hne
    refine ⟨hth0, ?_, ?_⟩
    · intro u hu
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [two_nsmul, add_zero, heisO_zero]
    · intro e _ u hu _
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [heisO_zero]

end GlobalTheory.VacSecondPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepValueFixedLevelPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.GValMid

theorem one_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), c.Is → v.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))) f₁ f₂,
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = G.q.v) f₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (G.eg j) f₁) (comb c.ψ _ _ (G.eg (j + 1)) f₂) =
      C • biComb c.ψ _ _ _ (G.cg j) (G.cg (j + 1)) (c.ctr j σ h s₁ s₂ f₁ f₂) := by
  intro D c v G hc hv j σ h
  have hs := G.hs
  have H : j + 1 + 1 + 2 * σ = G.s := by omega
  obtain ⟨C, hC, key⟩ := GlobalTheory.LocMod.GValProof.gval_of_laws D (GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D))
    (GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)) (GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor)
    (GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds) G.k G.ν G.unitVol (GlobalTheory.LocMod.ofSplit G.q) G.s D.R.k
    G.S (Fin D.R.t) c.ψ G.char j (2 * σ) H
  refine ⟨C, hC, fun s₁ s₂ f₁ f₂ h₁ h₂ => ?_⟩
  have a₀ : j + (2 * σ + 1 + 1 + 1) = G.s + 1 := by omega
  have a₁ : j + 1 + (2 * σ + 1 + 1) = G.s + 1 := by omega
  have a₂ : j + 1 + 1 + (2 * σ + 1) = G.s + 1 := by omega
  have hne : G.sc j ≠ 0 := fun e => by
    have := G.sc_unit j
    rw [e, map_zero] at this
    exact zero_ne_one this
  let F : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit G.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) _ _ _ (2 * σ) :=
    ⟨G.sc j, hne, G.FX j (by omega), G.FX (j + 1) (by omega), G.FX (j + 1 + 1) (by omega), G.FY j _ a₀, G.FY (j + 1) _ a₁,
      G.FY (j + 1 + 1) _ a₂, G.bes j (σ + 1) h _ a₀, G.jac j (σ + 1) h _ a₁,
      G.sc_step j ▸ G.bes (j + 1 + 1) σ (idx_step h) _ a₂⟩
  obtain ⟨T₁, m₁, e₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY j _ a₀) (G.FY (j + 1) _ a₁) c.ψ G.S.ψ hc.std G.char G.S.cond
    _ _ (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (G.latY j _ a₀) (G.latY (j + 1) _ a₁)).2 f₁ h₁
  obtain ⟨T₂, m₂, e₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY (j + 1) _ a₁) (G.FY (j + 1 + 1) _ a₂) c.ψ G.S.ψ hc.std G.char
    G.S.cond _ _ (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) (by omega)) (G.latY (j + 1) _ a₁) (G.latY (j + 1 + 1) _ a₂)).2 f₂ h₂
  obtain ⟨O₁, o₁, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  obtain ⟨O₂, o₂, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1) ⊕ Fin (2 * σ + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
  have b₁ : j + (2 * σ + 1 + 1) = G.s := by omega
  have b₂ : j + 1 + (2 * σ + 1) = G.s := by omega
  have g₁ := (G.eg_is j _ b₁).2 T₁ m₁ O₁ ⟨_, (GModel.phi_sb G).1 j _ b₁⟩ o₁ rfl
  have g₂ := (G.eg_is (j + 1) _ b₂).2 T₂ m₂ O₂ ⟨_, (GModel.phi_sb G).1 (j + 1) _ b₂⟩ o₂ rfl
  have := key σ _ _ _ F s₁ s₂ (c.lnk j σ h) (c.vL j σ h) (G.cg j) (G.cg (j + 1)) (G.cg_mid j _ b₂) (G.cg_mid (j + 1) _ H)
    T₁ T₂ m₁ m₂ ⟨_, (GModel.phi_sb G).1 j _ b₁⟩ ⟨_, (GModel.phi_sb G).1 (j + 1) _ b₂⟩ O₁ O₂ rfl rfl o₁ o₂
  rw [← e₁ O₁ o₁, ← e₂ O₂ o₂, ← g₁, ← g₂]
  exact this

theorem vac_foldr : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∀ j, j + 1 + 1 ≤ D.R.m →
  ∀ (i : Fin n) (L : List (Fin n)), i ∉ L → ∀ Ψ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ →
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) (L.foldr (fun i' f => comb c.ψ _ _ ((G i').eg j) f) Ψ) := by
  intro D c v n G hc _ hG j hj i L hi Ψ hΨ
  induction L with
  | nil => exact GlobalTheory.SeeSawRhs.vac_mono (fun p hp => (hG.places p).2 ⟨i, hp⟩) hΨ
  | cons a L ih =>
    have hs := (G a).hs
    have hai : (G a).q.v ≠ (G i).q.v := fun e => hi (by rw [hG.inj e]; exact List.mem_cons_self)
    have hat : CombAt (· = (G a).q.v) ((G a).eg j) := fun u hu r s => by
      rw [← ((G a).eg_is j ((G a).s - j) (by omega)).1 u hu r s]
      exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.FrameLat.sum_mem_idAt (G a).q)
    exact ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· = (G a).q.v) (· = (G i).q.v) fun p h1 h2 => hai (h1.symm.trans h2)).2.1 _ hat).2
      _ _ _ (ih fun hm => hi (List.mem_cons_of_mem _ hm))

section Alg

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} {ι : Type} (a : ι → WO A S →₀ ℂ) (b : ι → WO S A' →₀ ℂ)

theorem comb_foldr (d : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) (L : List ι) (u : WO A S) (w : WO S A') :
    comb ψ S A' d (fun w' => L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => C u' w') u) w =
      L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => comb ψ S A' d (C u') w) u := by
  induction L generalizing u with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldr_cons]
    refine (GlobalTheory.SeeSawRhs.comb_comm2 ψ A S A' (a i) d
      (fun u'' w' => L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => C u' w') u'') u w).trans ?_
    congr 1
    funext u''
    exact ih u''

theorem biComb_foldr (C : WO A S → WO S A' → ℂ) (L : List ι) (u : WO A S) (w : WO S A') :
    L.foldr (fun i C' => biComb ψ A S A' (a i) (b i) C') C u w =
      L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => L.foldr (fun i f => comb ψ S A' (b i) f) (C u') w) u := by
  induction L generalizing u w with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldr_cons]
    unfold biComb
    congr 1
    funext u'
    refine Eq.trans ?_ (comb_foldr ψ a (b i) (fun u'' => L.foldr (fun i f => comb ψ S A' (b i) f) (C u'')) L u' w)
    congr 1
    funext w'
    exact ih u' w'

theorem theta_foldr (C : WO A S → WO S A' → ℂ) (hC : ∀ w, IsThetaFunO ψ A S fun u => C u w) (L : List ι) (w : WO S A') :
    IsThetaFunO ψ A S fun u => L.foldr (fun i f => comb ψ S A' (b i) f) (C u) w := by
  induction L generalizing w with
  | nil => exact hC w
  | cons i L ih => exact GlobalTheory.SeeSawRhs.theta_comb_left (fun u => L.foldr (fun i f => comb ψ S A' (b i) f) (C u)) ih (b i) w

variable {ψ}

theorem theta_left {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C) (w : WO S A') : IsThetaFunO ψ A S fun u => C u w := by
  obtain ⟨U, hU, hl⟩ := h.levL
  refine ⟨fun γ u => h.quasiL γ u w, ⟨U, hU, fun x hx h0 => hl x hx h0 w⟩,
    h.cont.comp (continuous_id.prodMk continuous_const), fun k L hL h0 u => ?_⟩
  simpa using h.smooth k L 0 hL continuous_const h0 (fun t => Matrix.map_zero _ (finPart D).map_zero) u w

theorem theta_right {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C) (u : WO A S) : IsThetaFunO ψ S A' (C u) := by
  obtain ⟨U, hU, hl⟩ := h.levR
  refine ⟨fun γ w => h.quasiR γ u w, ⟨U, hU, fun x hx h0 => hl x hx h0 u⟩,
    h.cont.comp (continuous_const.prodMk continuous_id), fun k L hL h0 w => ?_⟩
  simpa using h.smooth k 0 L continuous_const hL (fun t => Matrix.map_zero _ (finPart D).map_zero) h0 u w

end Alg

theorem biComb_dG : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G → ∀ j, j + 1 < D.R.m →
  ∀ C : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ,
    (∀ w, IsThetaFunO c.ψ _ _ fun u => C u w) → (∀ u, IsThetaFunO c.ψ _ _ (C u)) →
    biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) C =
      (List.finRange n).foldr (fun i C' => biComb c.ψ _ _ _ ((G i).cg j) ((G i).cg (j + 1)) C') C := by
  intro D c v n G hG j hj C h₁ h₂
  funext u w
  rw [biComb_foldr, ← hG.dG j (by omega) _ (theta_foldr c.ψ (fun i => (G i).cg (j + 1)) C h₁ _ w)]
  unfold biComb
  congr 1
  funext u'
  rw [hG.dG (j + 1) hj _ (h₂ u')]

theorem gValue_mid : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
  intro D c v n G hc hv hG j σ h
  choose C hC key using fun i => one_place D c v (G i) hc hv j σ h
  refine ⟨((List.finRange n).map C).prod, List.prod_ne_zero fun h0 => ?_, fun s₁ s₂ Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
  · obtain ⟨i, -, hi⟩ := List.mem_map.1 h0
    exact hC i hi
  have ind : ∀ L : List (Fin n), L.Nodup →
      c.ctr j σ h s₁ s₂ (L.foldr (fun i f => comb c.ψ _ _ ((G i).eg j) f) Ψ₁)
          (L.foldr (fun i f => comb c.ψ _ _ ((G i).eg (j + 1)) f) Ψ₂) =
        (L.map C).prod • L.foldr (fun i C' => biComb c.ψ _ _ _ ((G i).cg j) ((G i).cg (j + 1)) C') (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
    intro L hL
    induction L with
    | nil => simp
    | cons i L ih =>
      obtain ⟨hi, hL'⟩ := List.nodup_cons.1 hL
      simp only [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [key i s₁ s₂ _ _ (vac_foldr D c v n G hc hv hG j (by omega) i L hi Ψ₁ h₁)
        (vac_foldr D c v n G hc hv hG (j + 1) (by omega) i L hi Ψ₂ h₂), ih hL', GlobalTheory.SeeSawRhs.biComb_smul, smul_smul]
  have hb : IsBiTheta c.ψ _ _ _ (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) :=
    (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hc.std _ _ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (flatBF s₁ Ψ₁) (flatFB s₂ Ψ₂)
      (((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D c.ψ fun _ => True).1 _ _ _ s₁).Heisenberg₂.theta _ h₁.1)
      (((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D c.ψ fun _ => True).2 _ _ _ s₂).Heisenberg₂.theta _ h₂.1)).1
  rw [hG.eG j (by omega) _ h₁.1, hG.eG (j + 1) (by omega) _ h₂.1, ind _ (List.nodup_finRange n),
    biComb_dG D c v n G hG j (by omega) _ (theta_left hb) (theta_right hb)]

end GlobalTheory.SeeSaw.GValMid

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepFinitelyManyCellsUniformProo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl.FinOneProof

set_option maxHeartbeats 4000000 in

theorem finOne : ∀ D : D7, FinOne D := by
  intro D ψ hstd σ S Q a
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have hFL := GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D
  have hFLs := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D
  have hBF := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D hFL hFLs hOm
  have hFB := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D hFL hFLs hOm
  have hCo := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.T.heisenbergInvariant_factors_contraction
  obtain ⟨-, hchar, hxi, -, hcomp⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D Q.k (ofSplit Q.q) ψ hstd
  obtain ⟨hψc, hψ1⟩ := hchar Q.ψk Q.char
  haveI := Q.unitVol.1
  have hsd : IsSelfDual Q.ψk Q.ν := isSelfDual_of_isUnitVol Q.ν Q.cond Q.unitVol
  have hc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  obtain ⟨μV, hμV⟩ := hcomp S.s₁.χV
  obtain ⟨μW, hμW⟩ := hcomp S.s₁.χW
  obtain ⟨μV', hμV'⟩ := hcomp S.s₂.χV
  obtain ⟨μW', hμW'⟩ := hcomp S.s₂.χW
  obtain ⟨C₀, hC₀⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D Q.k (ofSplit Q.q) _ (σ + 1) Q.F.s Q.F.s_ne).1 S.B Q.F.F₀).1
  obtain ⟨C₂, hC₂⟩ := ((GlobalTheory.T.bessel_fourierJacobi_normalFrames_exist_splitPlace D Q.k (ofSplit Q.q) _ σ (Q.F.s * (ofSplit Q.q).xi)
    (mul_ne_zero Q.F.s_ne hxi)).1 S.B' Q.F.F₂).1
  have hsb := GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective Q.k Q.ψk Q.ν hψc inferInstance
  have hjac' : (ofSplit Q.q).IsJacFrame S.J Q.F.s (-(ofSplit Q.q).xi ^ 2 * (ofSplit Q.q).hz S.B') Q.F.F₁ Q.F.G₁ :=
    GlobalTheory.LocMod.GSuppTwo.hz_link (ofSplit Q.q) S.l ▸ Q.F.jac

  let ca : ℂ := (((μV * μW⁻¹) (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ)
  let Φa : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) := ca • Q.Φ₁

  let cx : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → ℂ := fun x => (((μV' * μW'⁻¹) (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)
  let Φx : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k → SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
    fun x => cx x • Q.Φ₂

  have step₁ : ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ g ∈ GlobalTheory.FinPl.grpOff S.B.V (· = Q.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v),
      ∀ x, ∃ U, (ofSplit Q.q).IsModel ψ C₀ Q.F.F₁ U ∧ ∀ Ψ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k),
        Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1) →
        flatBF S.s₁ (S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) (comb ψ _ _ Q.D₁ f₁)) = U Ψ := by
    intro f₁ f₂ hvac g hg h₁ hh₁ x
    obtain ⟨⟨Tm, O, hTm, hO, hTO⟩, -⟩ := hvac
    have hcomb : comb ψ _ _ Q.D₁ f₁ = Tm Q.Φ₁ := by
      rw [← hTO]; exact (Q.dat₁.2 Tm hTm O Q.Φ₁ hO rfl).symm
    let Φ' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) :=
      ⟨om μV⁻¹ a x Φa.1, om_mem_SB _ _ _ Φa.2⟩
    have hloc : S.s₁.om (Q.gl₀ a, Q.gl₁ x) (Tm Q.Φ₁) = Tm Φ' :=
      hOm Q.k (ofSplit Q.q) ψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil μV μW hμV hμW _ _ Q.F.G₀ Q.F.G₁ Tm hTm
        (Q.gl₀ a) a (Q.gl₁ x) x (Q.loc₀ a) (Q.loc₁ x) Q.Φ₁ Φ' (by
          funext z; simp only [Φ', Φa, ca, om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    have hmod := GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hstd S.B.V S.J.W _ _ S.s₁.om S.s₁.weil _ _ Q.F.G₀ Q.F.G₁
      Tm hTm g hg h₁ hh₁
    obtain ⟨U, hU, hflat⟩ := hBF Q.k (ofSplit Q.q) Q.ν inferInstance ψ Q.ψk Q.char (σ + 1) S.B S.J S.s₁ Q.F.s Q.F.s_ne _ _
      (Q.c + 1 + 1) Q.F.F₀ C₀ Q.F.G₀ Q.F.F₁ Q.F.G₁ hC₀ Q.F.bes Q.F.jac _ hmod
    refine ⟨U, hU, fun Ψ hΨ => ?_⟩
    have hm : S.s₁.om (g * Q.gl₀ a, h₁ * Q.gl₁ x) = S.s₁.om (g, h₁) * S.s₁.om (Q.gl₀ a, Q.gl₁ x) := by
      rw [← map_mul, Prod.mk_mul_mk]
    rw [hcomb, hm, Module.End.mul_apply, hloc]
    exact hflat Φ' Ψ hΨ

  have step₂ : ∀ f₁ f₂, Q.Vac f₁ f₂ → ∀ h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (· = Q.q.v),
      ∀ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (· = Q.q.v), ∀ x y, ∃ U, (ofSplit Q.q).IsModel ψ Q.F.F₁ C₂ U ∧
        ∀ Ψ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k), Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) (om μV'⁻¹ x y (Φx x).1) →
        flatFB S.s₂ (S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) (comb ψ _ _ Q.D₂ f₂)) = U Ψ := by
    intro f₁ f₂ hvac h₁ hh₁ h₂ hh₂ x y
    obtain ⟨-, ⟨Tm, O, hTm, hO, hTO⟩⟩ := hvac
    have hcomb : comb ψ _ _ Q.D₂ f₂ = Tm Q.Φ₂ := by
      rw [← hTO]; exact (Q.dat₂.2 Tm hTm O Q.Φ₂ hO rfl).symm
    let Φ' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) :=
      ⟨om μV'⁻¹ x y (Φx x).1, om_mem_SB _ _ _ (Φx x).2⟩
    have hloc : S.s₂.om (Q.gl₁ x, Q.gl₂ y) (Tm Q.Φ₂) = Tm Φ' :=
      hOm Q.k (ofSplit Q.q) ψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil μV' μW' hμV' hμW' _ _ Q.F.G₁ Q.F.G₂ Tm hTm
        (Q.gl₁ x) x (Q.gl₂ y) y (Q.loc₁ x) (Q.loc₂ y) Q.Φ₂ Φ' (by
          funext z; simp only [Φ', Φx, cx, om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    have hmod := GlobalTheory.LocModMove.isModel_weil_off D Q.k Q.q ψ hstd S.J.W S.B'.V _ _ S.s₂.om S.s₂.weil _ _ Q.F.G₁ Q.F.G₂
      Tm hTm h₁ hh₁ h₂ hh₂
    obtain ⟨U, hU, hflat⟩ := hFB Q.k (ofSplit Q.q) Q.ν inferInstance ψ Q.ψk Q.char σ S.J S.B' S.s₂ Q.F.s Q.F.s_ne _ _
      (Q.c + 1) Q.F.F₁ Q.F.G₁ Q.F.F₂ C₂ Q.F.G₂ hjac' hC₂ Q.F.bes' _ hmod
    refine ⟨U, hU, fun Ψ hΨ => ?_⟩
    have hm : S.s₂.om (h₁ * Q.gl₁ x, h₂ * Q.gl₂ y) = S.s₂.om (h₁, h₂) * S.s₂.om (Q.gl₁ x, Q.gl₂ y) := by
      rw [← map_mul, Prod.mk_mul_mk]
    rw [hcomb, hm, Module.End.mul_apply, hloc]
    exact hflat Φ' Ψ hΨ
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.fourierJacobi_flatMap_support_finite_cells Q.k Q.ψk hψc hψ1 Q.ν inferInstance Q.n₁ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1) (by omega) (by omega)
    μV⁻¹ Q.L₁.J Q.co₁.1 Φa a
  refine ⟨T₁, ?_, ?_⟩
  · intro f₁ f₂ hvac g hg h₁ hh₁ x hne
    obtain ⟨U, -, hU⟩ := step₁ f₁ f₂ hvac g hg h₁ hh₁ x
    let Ψ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ (om_mem_SB μV⁻¹ a x Φa.2)⟩
    rw [hU Ψ rfl] at hne
    have hne' : GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1) ≠ 0 := by
      intro h0
      apply hne
      have : Ψ = 0 := Subtype.ext h0
      rw [this, map_zero]
    obtain ⟨β, r, hr, t, ht, j, hj, hx⟩ := hT₁ x hne'
    refine ⟨t, ht, colE (Q.c + 1 + 1) (σ + 1 + 1) β * r, ?_, j, hj, hx⟩
    exact (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D Q.k (ofSplit Q.q)).2.1 Q.n₁ (Q.c + 1 + 1) (σ + 1) S.J Q.F.s _ Q.F.F₁ Q.F.G₁ Q.F.jac _ β r hr
      (Q.loc₁ _)
  · intro x
    obtain ⟨T₂, hT₂⟩ := GlobalTheory.T.localFlatMapContraction_support_finitelyManyCells Q.k Q.ψk hψc hψ1 Q.ν hsd Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) (by omega) μV⁻¹ μV'⁻¹
      Q.L₂.J Q.co₂.1 Φa (Φx x) a x
    refine ⟨T₂, ?_⟩
    intro f₁ f₂ hvac g hg h₁ hh₁ h₂ hh₂ y hne
    obtain ⟨U₁, hU₁, hf₁⟩ := step₁ f₁ f₂ hvac g hg h₁ hh₁ x
    obtain ⟨U₂, hU₂, hf₂⟩ := step₂ f₁ f₂ hvac h₁ hh₁ h₂ hh₂ x y
    let Ψ₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 _ (om_mem_SB μV⁻¹ a x Φa.2)⟩
    let Ψ₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) :=
      ⟨_, ((hsb _ _ (Q.c + 1) (σ + 1) (by omega)).2 (by omega)).1 _ (om_mem_SB μV'⁻¹ x y (Φx x).2)⟩
    obtain ⟨Λ, -, hΛ⟩ := hCo Q.k (ofSplit Q.q) Q.ν inferInstance ψ hstd Q.ψk Q.char (σ + 1) σ S.B S.B' S.l S.J.W₀ S.vL
      Q.F.s Q.F.s_ne _ _ _ Q.F.F₀ C₀ Q.F.F₁ Q.F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
    obtain ⟨Ξ, hΞ, hΞΛ⟩ := hΛ Ψ₁ Ψ₂
    unfold Dbl2.con at hne
    rw [hf₁ Ψ₁ rfl, hf₂ Ψ₂ rfl, hΞΛ] at hne
    have hne' : GlobalTheory.LocFlat.contr Q.ψk Q.ν (GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) (om μV⁻¹ a x Φa.1))
        (GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) (om μV'⁻¹ x y (Φx x).1)) ≠ 0 := by
      intro h0
      apply hne
      have : Ξ = 0 := Subtype.ext (hΞ.trans h0)
      rw [this, map_zero]
    obtain ⟨r, hr, t, ht, j, hj, hy⟩ := hT₂ y hne'
    exact ⟨t, ht, r, (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D Q.k (ofSplit Q.q)).2.2 Q.n₂ (Q.c + 1) σ S.B' (Q.F.s * (ofSplit Q.q).xi) Q.F.F₂ Q.F.G₂
      Q.F.bes' _ r hr (Q.loc₂ r), j, hj, hy⟩

end GlobalTheory.QPl.FinOneProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainRealZetaNonvanishingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_realZeta_nonvanishing : GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D → GlobalTheory.ChainOnto.RealZeta D := by
  first | exact @GlobalTheory.RealZetaProof.realZeta | exact GlobalTheory.RealZetaProof.realZeta | (intros; apply GlobalTheory.RealZetaProof.realZeta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_joint_twist_identity : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t,
    QVec (a.fam row col) ((famOf a J row col hCh t).pinTup sc cT) := by
  first | exact @GlobalTheory.QVecJoin.qVec_pinTup | exact GlobalTheory.QVecJoin.qVec_pinTup | (intros; apply GlobalTheory.QVecJoin.qVec_pinTup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeForwardStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_forward : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => True) := by
  first | exact @GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base | exact GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base | (intros; apply GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base <;> assumption)
end

