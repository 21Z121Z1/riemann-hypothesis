import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0410
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0384
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0408
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothWeilOrbitPreservedByHeisenbergDerivatives
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbit

theorem orbit_heis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) → ∀ u, At (evI F) u → ∀ f ∈ G.M.Pol B.ψ B.emb,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f p.2) → (∃ f' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) → ∀ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (G.M.heisLine B.ψ u) f f₁ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ G.M.Pol B.ψ B.emb, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ hγ T hTa u hu f hf hsm hder f₁ hf₁
  obtain ⟨f', hf'P, hf'd⟩ := hder
  have hψ : IsStd B.ψ := hT.base.std
  have hstab : ∀ v : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evI F) v → ∀ g ∈ G.M.Pol B.ψ B.emb,
      ∃ g₁ ∈ G.M.Pol B.ψ B.emb, ∀ y, g₁ y = dOp (archCo G.M.co v).1 (archCo G.M.co v).2 g y := by
    intro v hv g hg
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin a) (Fin (a + a')) (Fin a × Fin (a + a')) B.ψ (incM F G.V.J) (incM F G.W.J)
      G.M.co hψ
    have h0 : ∀ t, G.M.heisLine B.ψ v t 0 = 0 := fun t => by
      funext x
      simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hA : ActsD (evI F) (G.M.heisLine B.ψ v) g (D v g) :=
      (GlobalTheory.RealLift.actsLaws F _ g (D v g) (D v g)).1 _ h0 (hD v hv g).1
    refine ⟨D v g, Submodule.mem_sInf.2 fun N hN => hN.2 v hv g (Submodule.mem_sInf.1 hg N hN) _ hA, fun y => ?_⟩
    rw [(hD v hv g).2 y]
    rfl
  have hrel : ∀ t y, T t f₁ y = dOp (archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1
      (archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2 (T t f) y := fun t =>
    GlobalTheory.T.weil_operator_right_intertwines_heisenberg_derivative G.M B.ψ X.β (X.β / X.α) om hψ hT.weil (γ (Multiplicative.ofAdd t)) (T t) (hTa t) u hu f f₁ hf₁
  obtain ⟨hφ, u', hu', hφd⟩ := GlobalTheory.T.heisenberg_orbit_coefficient_smooth G.M γ hγ u hu
  have hfun : (fun p : ℝ × (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) =
      fun p => dOp (archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd p.1)))ᵀ)).1
        (archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd p.1)))ᵀ)).2 (T p.1 f) p.2 :=
    funext fun p => hrel p.1 p.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GlobalTheory.T.contDiff_heisenbergArchimedeanDiffOperator_family (fun t => T t f) (fun t => (archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1)
      (fun t => (archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2) hsm hφ.fst hφ.snd
  have hT0 : T 0 f = f := by
    have h1 : om (1, γ (Multiplicative.ofAdd 0)) = 1 := by
      rw [ofAdd_zero, map_one]
      exact map_one om
    have hA : Acts (evI F) (om (1, γ (Multiplicative.ofAdd 0))) f f := by
      rw [h1]
      intro r _
      rfl
    exact (GlobalTheory.RealLift.actsLaws F _ f (T 0 f) f).2.2.2.1 _ (hTa 0 f) hA
  have hφ0 : archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd (0 : ℝ))))ᵀ) = archCo G.M.co u := by
    rw [ofAdd_zero, map_one]
    simp [mat]
  obtain ⟨g₁, hg₁P, hg₁⟩ := hstab u hu f' hf'P
  obtain ⟨g₂, hg₂P, hg₂⟩ := hstab u' hu' f hf
  refine ⟨g₁ + g₂, add_mem hg₁P hg₂P, fun x => ?_⟩
  have hP := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have hQ := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have h4 := GlobalTheory.T.heisenbergArchimedeanDiffOperator_hasDerivAt_family (fun t => T t f) (fun t => (archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1)
    (fun t => (archCo G.M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2) f' _ _ hsm hf'd hP hQ x
  simp only [hφ0, hT0] at h4
  rw [SchwartzMap.add_apply, hg₁, hg₂]
  exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrel t x)

end GlobalTheory.HeisOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothWeilOrbitRealPassesToHeisenbergDerivatives
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbitReal

theorem orbit_heis_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) →
          (∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) →
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ →
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  intro F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hW τ _ _ γ hγ T hTa u hu f hf hsm hder f₁ hf₁
  obtain ⟨f', hf'P, hf'd⟩ := hder
  have hstab : ∀ v : Matrix (Fin n) (Fin d) (AE F E), At (evI F) v → ∀ g ∈ M.Pol ψ τ,
      ∃ g₁ ∈ M.Pol ψ τ, ∀ y, g₁ y = dOp (archCo M.co v).1 (archCo M.co v).2 g y := by
    intro v hv g hg
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J)
      M.co hψ
    have h0 : ∀ t, M.heisLine ψ v t 0 = 0 := fun t => by
      funext x
      simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hA : ActsD (evI F) (M.heisLine ψ v) g (D v g) :=
      (GlobalTheory.RealLift.actsLaws F _ g (D v g) (D v g)).1 _ h0 (hD v hv g).1
    refine ⟨D v g, Submodule.mem_sInf.2 fun N hN => hN.2 v hv g (Submodule.mem_sInf.1 hg N hN) _ hA, fun y => ?_⟩
    rw [(hD v hv g).2 y]
    rfl
  have hrel : ∀ t y, T t f₁ y = dOp (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1
      (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2 (T t f) y := fun t =>
    GlobalTheory.T.weil_operator_right_intertwines_heisenberg_derivative M ψ χX χW om hψ hW (γ (Multiplicative.ofAdd t)) (T t) (hTa t) u hu f f₁ hf₁
  obtain ⟨hφ, u', hu', hφd⟩ := GlobalTheory.T.heisenberg_orbit_coefficient_smooth M γ hγ u hu
  have hfun : (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) =
      fun p => dOp (archCo M.co (u * (mat (γ (Multiplicative.ofAdd p.1)))ᵀ)).1
        (archCo M.co (u * (mat (γ (Multiplicative.ofAdd p.1)))ᵀ)).2 (T p.1 f) p.2 :=
    funext fun p => hrel p.1 p.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GlobalTheory.HeisOrbit.dOp_contDiff_family (fun t => T t f) (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1)
      (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2) hsm hφ.fst hφ.snd
  have hT0 : T 0 f = f := by
    have h1 : om (1, γ (Multiplicative.ofAdd 0)) = 1 := by
      rw [ofAdd_zero, map_one]
      exact map_one om
    have hA : Acts (evI F) (om (1, γ (Multiplicative.ofAdd 0))) f f := by
      rw [h1]
      intro r _
      rfl
    exact (GlobalTheory.RealLift.actsLaws F _ f (T 0 f) f).2.2.2.1 _ (hTa 0 f) hA
  have hφ0 : archCo M.co (u * (mat (γ (Multiplicative.ofAdd (0 : ℝ))))ᵀ) = archCo M.co u := by
    rw [ofAdd_zero, map_one]
    simp [mat]
  obtain ⟨g₁, hg₁P, hg₁⟩ := hstab u hu f' hf'P
  obtain ⟨g₂, hg₂P, hg₂⟩ := hstab u' hu' f hf
  refine ⟨g₁ + g₂, add_mem hg₁P hg₂P, fun x => ?_⟩
  have hP := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have hQ := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have h4 := GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt (fun t => T t f) (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1)
    (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2) f' _ _ hsm hf'd hP hQ x
  simp only [hφ0, hT0] at h4
  rw [SchwartzMap.add_apply, hg₁, hg₂]
  exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrel t x)

end GlobalTheory.HeisOrbitReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridCommonDataPropertiesHold
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreOnto

theorem comOK : ComOK := by
  intro D _ _ T L μ0 _ sc _ G W M _
  have hchi : ∀ k, k < D.R.m → ChrEq (G.ch.chi (D.R.m - k)) (G.ch.chiH (D.R.m - k)) :=
    fun k hk => G.ch.chi_eq _ (by omega) (by omega)
  refine ⟨W.θ_is, W.ψ_std, fun k (hk : k < D.R.m) => ?_, fun k (hk : k < D.R.m) τ => ?_, fun k (hk : k < D.R.m) => ?_,
    fun i k hik (hk : k < D.R.m) τ => ?_, ?_, ?_⟩
  · show IsHeckeChar D (G.ch.chi (D.R.m - k))⁻¹ ∧ Formalism.L2.Theta.ResEta D (G.ch.chi (D.R.m - k))⁻¹ 0
    have hw := W.om_is (.core k) (show k + 1 ≤ D.R.m by omega)
    have e := (G.chr_core (i := k) (by omega)).1
    have hr : (G.pS (.core k)).rank = rankP D (k + 1) := (G.sp.P_is _ (by omega)).rank
    have h1 := hw.hecS
    have h2 := hw.resS
    rw [e] at h1 h2
    rw [hr] at h2
    obtain ⟨a, ha⟩ := even_rankP D (k + 1)
    exact GlobalTheory.StdUnn.isHeckeChar_resEta_inv D _ 0 h1 (Formalism.L2.Theta.resEta_parity h2 (by omega))
  · show HasInfExp D (G.ch.chi (D.R.m - k))⁻¹ τ (-(cen D sc.cGap τ (D.R.m - k) : ℚ))
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - k) : ℚ)) (hchi k hk)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - k), fun τ => by push_cast; ring, G.ch.inf _ (by omega) (by omega)⟩ τ
    exact GlobalTheory.Chain.StepVac.hasInfExp_inv h
  · show GlobalTheory.LFun.UnrOff (G.ch.chi (D.R.m - k))⁻¹ (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F)))
    intro w hw
    have hu : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - k)) w :=
      (GlobalTheory.LFun.unrAt_iff_of_chrEq (hchi k hk) w).2 (G.ch.unr _ (by omega) (by omega) w hw)
    intro x hx
    have := hu x hx
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv] at this ⊢
    rw [this, inv_one]
  · show -(cen D sc.cGap τ (D.R.m - i) : ℚ) ≠ -(cen D sc.cGap τ (D.R.m - k) : ℚ)
    intro h
    have hg : 0 < gap D sc.cGap := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D sc.cGap)
    set g := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D sc.cGap) 0 with hgdef
    have hc : ∀ j, cen D sc.cGap τ j = ⌊g.mid j⌋ := fun j => rfl
    have hga : (g.ga : ℚ) = (gap D sc.cGap : ℚ) := rfl
    have e1 : ((D.R.m - i : ℕ) : ℚ) = ((D.R.m - k : ℕ) : ℚ) + ((k - i : ℕ) : ℚ) := by
      rw [← Nat.cast_add]; congr 1; omega
    have hmid : g.mid (D.R.m - k) = g.mid (D.R.m - i) + (((k - i) * gap D sc.cGap : ℕ) : ℤ) := by
      rw [g.mid_eq (by omega), g.mid_eq (by omega)]
      have := g.a_sub_a (D.R.m - k) (D.R.m - i)
      rw [e1, hga] at this
      push_cast
      linarith
    have hf : cen D sc.cGap τ (D.R.m - k) = cen D sc.cGap τ (D.R.m - i) + (((k - i) * gap D sc.cGap : ℕ) : ℤ) := by
      rw [hc, hc, hmid, Int.floor_add_intCast]
    have h' : cen D sc.cGap τ (D.R.m - i) = cen D sc.cGap τ (D.R.m - k) := by exact_mod_cast neg_inj.1 h
    have hpos : 0 < (k - i) * gap D sc.cGap := Nat.mul_pos (by omega) hg
    omega
  · show 1 ≤ D.R.r + 1
    omega
  · show D.R.r + 1 + 2 ≤ D.R.r + 6 - 1
    omega

end GlobalTheory.CoreOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.StepVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem infPart_idemAt {a : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a PP) : infPart D a = 0 := by
  classical
  have hs : IsIdemSum a {PP} := ⟨⟨fun _ => a, fun Q hQ => by rw [Finset.mem_singleton.1 hQ]; exact h, by simp⟩, h.1.2.1⟩
  exact GlobalTheory.PlaceDatum.infPart_idemSum hs

theorem prime_eq_of_idem {a : AE D} {P P' : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a P)
    (h' : Formalism.L2.NTheta.IsIdemAt a P') : P = P' := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · exact (h.2 x hx).trans (h'.2 x hx).symm

set_option maxHeartbeats 2000000 in
theorem stepVecLocal : ∀ D : D7, StepVecLocal D := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χ Q ξ f₀ f μ 𝓕 t ht Hl cl hP hB hC _ _ hdisj hv
  obtain ⟨hvac, e, ⟨⟨es, hes, rfl⟩, hce⟩, hth⟩ := hv
  have hSd : IsSelfDualC S ΛS := hB.2.2.1
  have hTd : IsSelfDualC T ΛT := hB.2.2.2.1
  have hψ : IsStdChar D ψ (-1) := base_std hB

  generalize hs : LS.Pg ∪ Q = s at *
  have hPs : ∀ PP, PP ∈ LS.Pg → PP ∈ s := fun PP h => hs ▸ Finset.mem_union_left _ h
  have hQs : ∀ PP, PP ∈ Q → PP ∈ s := fun PP h => hs ▸ Finset.mem_union_right _ h
  have hsum := GlobalTheory.T.splitIdempotent_prime_projection_correspondence D
  choose vP φP hφ hpr using fun i : ↥s => hsum.1 (es i.1) i.1 (hes i.1 i.2)
  choose rP hrP using fun i : ↥s => (show ∃ r, IsRedMap (φP i) i.1 r from
    let ⟨r, h⟩ := (GlobalTheory.T.degree_one_prime_reduction_split_place_dictionary D (vP i) (φP i) i.1 (hpr i)).1; ⟨r, h⟩)

  let ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ := fun PP =>
    if h : PP ∈ LS.Pg then gLoc LS PP (Hl ⟨PP, h⟩) (cl ⟨PP, h⟩) (χ PP) else qLoc LS.r PP (ξ PP)
  let Φ : ↥s → WO S T → ℂ := fun i => locFn S T βS βT (es i.1) i.1 (ω i.1)
  have hPi : ∀ i : ↥s, (Formalism.L2.NTheta.IsIdemAt (es i.1) i.1) := fun i => hes i.1 i.2
  have hsplit : ∀ i : ↥s, IsSplitIdem D (es i.1) ∧ es i.1 + cA D (es i.1) = idem D (.inl (vP i)) := fun i =>
    ⟨(hφ i).1, (hφ i).2.1⟩
  obtain ⟨K, hK, hKC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hSd.1 hTd.1 βS βT
  have hsb : ∀ i : ↥s, IsSBHalf (es i.1) (latO S T ΛS ΛT fun _ => True) (Φ i) := fun i =>
    GlobalTheory.PlaceDatum.isSBHalf_of_red (es i.1) _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO hSd.1.fg hTd.1.fg βS βT)
      ⟨K, hK, fun t ht => hKC t (GlobalTheory.PlaceDatum.infPart_of_half (infPart_idemAt (hPi i)) ht)⟩ {i.1}
      (fun y => ω i.1 (y i.1)) (fun y y' h => by rw [h i.1 (Finset.mem_singleton_self _)])

  have hcmpG : ∀ (i : ↥s) (hi : i.1 ∈ LS.Pg) (J : Subgroup (GL (Fin S.rank) ((vP i).adicCompletionIntegers D.host.F)))
      (lam : J →* ℂˣ) (mu : (Fv D.host.F (vP i))ˣ →* ℂˣ), IsLocLevel (φP i) i.1 LS (Hl ⟨i.1, hi⟩) (cl ⟨i.1, hi⟩) J lam →
      LiftsChar (φP i) i.1 mu (χ i.1) →
      onHalf (φP i) S T (frCo (φP i) βS) (frCo (φP i) βT) (es i.1) (fun y => localNewformFunction (vP i) J lam mu (rowsTB ht y)) = Φ i := by
    intro i hi J lam mu hJ hmu
    have h1 : (fun y => localNewformFunction (vP i) J lam mu (rowsTB ht y)) = viaRed (rP i) (ω i.1) := by
      funext y
      rw [GlobalTheory.T.localLevelDatum_eq_function_of_residueReduction D (vP i) (φP i) i.1 (rP i) (hrP i) _ _ t ht LS _ _ J lam hJ mu (χ i.1) hmu y]
      simp only [ω, dif_pos hi]
    rw [h1]
    exact GlobalTheory.T.splitHalf_residueReduction_function_eq_frameLocal D (vP i) (φP i) (es i.1) i.1 (rP i) (hφ i) (hpr i) (hrP i) S T βS βT (ω i.1)
  have hcmpQ : ∀ (i : ↥s) (hi : i.1 ∈ Q) (mu : (Fv D.host.F (vP i))ˣ →* ℂˣ), LiftsChar (φP i) i.1 mu (ξ i.1)⁻¹ →
      onHalf (φP i) S T (frCo (φP i) βS) (frCo (φP i) βT) (es i.1) (phiQ (vP i) LS.r mu) = Φ i := by
    intro i hi mu hmu
    have hn : i.1 ∉ LS.Pg := fun h => Finset.disjoint_left.1 hdisj h hi
    have h1 : phiQ (vP i) LS.r mu = viaRed (b := T.rank) (a := S.rank) (rP i) (ω i.1) := by
      funext y
      rw [GlobalTheory.T.thetaTwistDatum_eq_function_of_residueReduction D (vP i) (φP i) i.1 (rP i) (hrP i) _ _ LS.r mu (ξ i.1) hmu y]
      simp only [ω, dif_neg hn]
    rw [h1]
    exact GlobalTheory.T.splitHalf_residueReduction_function_eq_frameLocal D (vP i) (φP i) (es i.1) i.1 (rP i) (hφ i) (hpr i) (hrP i) S T βS βT (ω i.1)

  have hunder : ∀ i : ↥s, (i.1).asIdeal.under (𝓞 D.host.F) = (vP i).asIdeal := fun i => (hsum.2 _ _ _ (hpr i)).1
  have hcross := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es s
    (fun i hi => (hes i hi).1.1) hce
  have hinj : Function.Injective vP := by
    intro i j hij
    have h1 := (hsplit i).2
    have h2 := (hsplit j).2
    rw [hij] at h1
    have h3 := GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp (hes i.1 i.2).1.1 (hes i.1 i.2).1.2.1 (hes j.1 j.2).1.1 (hes j.1 j.2).1.2.1
      (h1.trans h2.symm) (hcross _ i.2 _ j.2) (hcross _ j.2 _ i.2)
    exact Subtype.ext (prime_eq_of_idem (hes i.1 i.2) (h3 ▸ hes j.1 j.2))

  have hid : ∀ (i : ↥s) (v : FinPl D) (φ : SplitProj D v) (e' : AE D), IsIdemOf φ e' → IsProjAt φ i.1 →
      ∃ hv : v = vP i, e' = es i.1 ∧ hv ▸ φ = φP i := by
    intro i v φ e' h1 h2
    obtain ⟨hu, -, h3⟩ := hsum.2 v φ i.1 h2
    have hv : v = vP i := HeightOneSpectrum.ext (hu.symm.trans (hunder i))
    subst hv
    obtain ⟨-, h4, h5⟩ := h3 e' h1
    have h6 := h4 _ (hPi i)
    refine ⟨rfl, h6.symm, (h5 _ (h6 ▸ hφ i)).symm⟩

  have hmodel : ∀ i : ↥s, ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (es i.1) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm :=
    fun i => (GlobalTheory.T.split_idempotent_base_function_identity D ψ θ S T sS sT ΛS ΛT f₀ hB (vP i) (es i.1) (hsplit i).1 (hsplit i).2).1
  choose xθ hxθ using fun i : ↥s => GlobalTheory.PlaceDatum.exists_isThetaAt hψ hSd hTd (hes i.1 i.2).1.1
    (infPart_idemAt (hPi i)) (hmodel i) (hsb i)
  refine ⟨?_, ?_⟩
  · let x : Place D → WO S T → ℂ :=
      Sum.elim (fun v => if h : ∃ i, vP i = v then xθ h.choose else f₀) fun _ => f₀
    have hxi : ∀ i, x (.inl (vP i)) = xθ i := by
      intro i
      have h : ∃ j, vP j = vP i := ⟨i, rfl⟩
      show (if h : ∃ j, vP j = vP i then xθ h.choose else f₀) = xθ i
      rw [dif_pos h, hinj h.choose_spec]
    refine ⟨x, ⟨fun τ => rfl, fun v hv => ?_⟩, ?_⟩
    · show (if h : ∃ i, vP i = v then xθ h.choose else f₀) = f₀
      refine dif_neg ?_
      rintro ⟨i, rfl⟩
      exact hv i.1 i.2 (hunder i)
    · intro v φ e' he' mu
      refine ⟨fun PP hpp hmu J lam hJ => ?_, fun PP hq hpp hmu => ?_⟩
      · obtain ⟨hv, rfl, hφ'⟩ := hid ⟨PP.1, hPs _ PP.2⟩ v φ e' he' hpp
        subst hv
        obtain rfl : φ = φP ⟨PP.1, hPs _ PP.2⟩ := hφ'
        rw [hcmpG ⟨PP.1, hPs _ PP.2⟩ PP.2 J lam mu hJ hmu, hxi]
        exact hxθ _
      · obtain ⟨hv, rfl, hφ'⟩ := hid ⟨PP, hQs _ hq⟩ v φ e' he' hpp
        subst hv
        obtain rfl : φ = φP ⟨PP, hQs _ hq⟩ := hφ'
        rw [hcmpQ ⟨PP, hQs _ hq⟩ hq mu hmu, hxi]
        exact hxθ _
  · rintro x ⟨⟨hx1, hx2⟩, hloc⟩
    have hθ : ∀ i : ↥s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (es i.1) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i)
        (x (.inl (vP i))) := by
      intro i
      by_cases hi : i.1 ∈ LS.Pg
      · obtain ⟨mu, hmu⟩ := (GlobalTheory.T.degree_one_prime_reduction_split_place_dictionary D (vP i) (φP i) i.1 (hpr i)).2 (χ i.1)
        obtain ⟨J, lam, hJ⟩ := GlobalTheory.T.exists_isLocalLevelAtPrimeOfLevelDatum D (vP i) (φP i) i.1 (rP i) (hrP i) _ LS (Hl ⟨i.1, hi⟩) (cl ⟨i.1, hi⟩)
        have h := (hloc (vP i) (φP i) (es i.1) (hφ i) mu).1 ⟨i.1, hi⟩ (hpr i) hmu J lam hJ
        rwa [hcmpG i hi J lam mu hJ hmu] at h
      · have hq : i.1 ∈ Q := (Finset.mem_union.1 (hs ▸ i.2)).resolve_left hi
        obtain ⟨mu, hmu⟩ := (GlobalTheory.T.degree_one_prime_reduction_split_place_dictionary D (vP i) (φP i) i.1 (hpr i)).2 (ξ i.1)⁻¹
        have h := (hloc (vP i) (φP i) (es i.1) (hφ i) mu).2 i.1 hq (hpr i) hmu
        rwa [hcmpQ i hq mu hmu] at h
    have hoff : ∀ p, (∀ i ∈ (Finset.univ : Finset ↥s), p ≠ .inl (vP i)) → x p = f₀ := by
      rintro (v | τ) h
      · refine hx2 v fun PP hPP hu => h ⟨PP, hPP⟩ (Finset.mem_univ _) ?_
        exact congrArg Sum.inl (HeightOneSpectrum.ext (hu.symm.trans (hunder ⟨PP, hPP⟩)))
      · exact hx1 τ
    have hsumes : ∑ i : ↥s, es i.1 = ∑ PP ∈ s, es PP := Finset.sum_coe_sort s es
    have hprod : ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP),
        omegaG LS χ y * omegaQ Q LS.r ξ 1 y = ∏ PP ∈ s, ω PP (y PP) := by
      intro y
      rw [← hs, Finset.prod_union hdisj, GlobalTheory.T.levelDatumValue_eq_prod_localResidueValues D _ _ LS χ Hl cl hP y, GlobalTheory.T.twistDatumValue_eq_prod_localResidueValues D _ _ LS.r Q ξ y,
        ← Finset.prod_coe_sort LS.Pg fun PP => ω PP (y PP)]
      congr 1
      · refine Finset.prod_congr rfl fun PP _ => ?_
        simp only [ω, dif_pos PP.2]
      · refine Finset.prod_congr rfl fun PP hq => ?_
        simp only [ω, dif_neg fun h => Finset.disjoint_left.1 hdisj h hq]
    rw [← hsumes] at hth
    refine GlobalTheory.T.thetaFunction_splitProductDatum_isPureTensor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC ↥s Finset.univ vP (fun i => es i.1) (fun i _ => hsplit i)
      hinj.injOn Φ (fun i _ => hsb i) x f _ (fun i _ => hθ i) hoff ?_ ?_ hth
    · intro t' ht'
      have h := GlobalTheory.T.prod_residueFunctions_half_sum_idempotents D S T βS βT s es hes ω t' (hsumes ▸ ht')
      have h2 : ∏ i : ↥s, Φ i (es i.1 • t') = ∏ PP ∈ s, locFn S T βS βT (es PP) PP (ω PP) (es PP • t') :=
        Finset.prod_coe_sort s fun PP => locFn S T βS βT (es PP) PP (ω PP) (es PP • t')
      show (if _ then _ else _) = ∏ i : ↥s, Φ i (es i.1 • t')
      rw [h2, ← h]
      by_cases hI : IsIntM (frMapO S T βS βT t')
      · rw [if_pos ⟨ht', hI⟩, if_pos hI]
        exact hprod _
      · rw [if_neg fun h => hI h.2, if_neg hI]
    · intro t' ht'
      exact if_neg fun h => ht' h.1

end GlobalTheory.StepVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRankSubmoduleChainBoundedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_rank_submodule_chain_bounded : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (χ : GL (Fin n) k →* ℂˣ), IsOpen {g | χ g = 1} → ∀ ρ : ℕ,
    ∃ L : ℕ, ∀ (r : ℕ) (N : Fin r → Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)),
      StrictMono N → (∀ i, GlobalTheory.ThetaGLSub.IsSub χ (N i) ∧
        GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m (ρ + 1) ≤ N i ∧
        N i ≤ GlobalTheory.ThetaGLSub.aug m χ ⊔ GlobalTheory.ThetaGLRank.rkSub k n m ρ) → r ≤ L := by
  first | exact @GlobalTheory.ThetaGLLayer.layer_bound | exact GlobalTheory.ThetaGLLayer.layer_bound | (intros; apply GlobalTheory.ThetaGLLayer.layer_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAtSplitPlaceLocalBasesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_at_splitPlace_localBases : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z, π₁ (cA σ z) = π₂ z) → ∀ g : GlobalTheory.DblVac.UD σ W,
  (Matrix.fromBlocks (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))))ᵀ *
    Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) *
    (Matrix.fromBlocks (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₁₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))
      (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₁.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (GlobalTheory.DblVac.matD g).toBlocks₂₂.map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) =
  Matrix.fromBlocks ((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) 0 0 (-((b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)))) := by
  first | exact @GlobalTheory.UnitFv.unitary_split | exact GlobalTheory.UnitFv.unitary_split | (intros; apply GlobalTheory.UnitFv.unitary_split <;> assumption)
end

