import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepVanOfStepX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumHeckeIdentitySplitPlaceCharts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.HSplitChart

lemma opOf_dualC_splitC {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : GA D V →* Module.End ℂ M) (P : Formalism.L2.DIV.Pl D.host.E) (n : ℕ) (z : ℕ → ℂ) :
    GlobalTheory.Hk3.opOf π P (GlobalTheory.Hk3.dualC (GlobalTheory.Hk3.splitC n z)) =
      ∑ j ∈ Finset.range (n + 1), z j • GlobalTheory.Hk3.opOf π P (Finsupp.single (dualLab (splitLab n j)) 1) := by
  unfold GlobalTheory.Hk3.opOf GlobalTheory.Hk3.dualC GlobalTheory.Hk3.splitC
  rw [Finsupp.mapDomain_finset_sum, ← Finsupp.sum_finset_sum_index]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.mapDomain_single, Finsupp.sum_single_index, Finsupp.sum_single_index, one_smul]
    · simp
    · simp
  · intro a; simp
  · intro a b1 b2; simp [add_smul]

theorem hecke_vac_split_chart : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ eS eT, IsSplitChart D.sp.cm.sig S.gram (frameLat S) h eS → IsSplitChart D.sp.cm.sig T.gram (frameLat T) h eT → ∀ f, VacFin ψ S T v f → (∀ k ∈ Kv S v, ∀ k' ∈ Kv T v, om (embV S v k, embV T v k') f = f) ∧ ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ k ≤ T.rank, heckeVec (((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom) (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f = ∑ j ∈ Finset.range (S.rank + 1), (if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) * (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k * (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0) • heckeVec (((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom) (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
  intro D ψ S T χS χT om hW t ht v w h hsp hunr eS eT hcS hcT f hf
  obtain ⟨hA, hB, hC, hD, hE⟩ := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have hconj : Formalism.DivisionValues.conjPl w ≠ w := hA.1 hsp
  have huS : GlobalTheory.Hk3.UnrPl w χS := hB χS (fun w' hw' => (hunr w' hw').1)
  have huT : GlobalTheory.Hk3.UnrPl w χT := hB χT (fun w' hw' => (hunr w' hw').2)
  obtain ⟨hfix, hmatch⟩ := GlobalTheory.Hk3.SplitMatch.match_split ψ S T χS χT om w hW hconj huS huT
  have hvac : GlobalTheory.Hk3.IsVacAt ψ S T w f := hD ψ S T f hf
  have hK : ∀ k ∈ Kv S v, ∀ k' ∈ Kv T v, om (embV S v k, embV T v k') f = f := by
    intro k hk k' hk'
    exact hfix f hvac _ ((hC S _).2 ⟨k, hk, rfl⟩) _ ((hC T _).2 ⟨k', hk', rfl⟩)
  refine ⟨hK, ?_⟩
  intro ϖ hϖ k hk
  obtain ⟨e, ϖ', x, he, h1, h2, hx, hval⟩ := hE hsp χS (hunr w h).1
  have hχS := hval χS (hunr w h).1
  have hχT := hval χT (hunr w h).2
  have hM := (hmatch e ϖ' x t he h1 h2 hx).1 ht k hk f hvac
  have hTfix : ∀ k ∈ Kv T v, (om.comp (MonoidHom.inr _ _)) (embV T v k) f = f := by
    intro k hk; simpa using hK 1 (one_mem _) k hk
  have hSfix : ∀ k ∈ Kv S v, (om.comp (MonoidHom.inl _ _)) (embV S v k) f = f := by
    intro k hk; simpa using hK k hk 1 (one_mem _)
  rw [← (GlobalTheory.T.split_prime_label_operators_eq_chart_hecke_operators D T v w h hsp eT hcT _ (om.comp (MonoidHom.inr _ _)) f hTfix ϖ hϖ k hk).1, ← hM,
    opOf_dualC_splitC, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [LinearMap.smul_apply, (GlobalTheory.T.split_prime_label_operators_eq_chart_hecke_operators D S v w h hsp eS hcS _ (om.comp (MonoidHom.inl _ _)) f hSfix ϖ hϖ j
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2, hχS, hχT]
  rfl

end GlobalTheory.ChainOnto.HSplitChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevChiLift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Inhab

variable {D : D7}

theorem pt_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (g : ι → WO S T → ℂ) (hg : ∀ i, IsThetaFunO ψ S T (g i)) (φ : PolF D T.rank S.rank) :
    IsThetaFunO ψ S T (∑ i ∈ s, a i • g i) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • g i) φ = ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (g i) φ := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hg i)) ih.1, ?_⟩
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hg i) ih.1 φ, ih.2]

theorem pt_om {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {k : GA D S}
    (hk : k ∈ GfC S) (φ : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (om (k, 1) f) φ = om (k, 1) (pureTensorO ψ θ S T sS sT BS BT f φ) :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT k 1
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f hf φ).2.symm

theorem lift_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {ι : Type} [Fintype ι] (κ : ι → GA D S) (hκ : ∀ i, κ i ∈ GfC S) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hf' : f' = ∑ i, (a i)⁻¹ • om (κ i, 1) f) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (F : GA D T → ℂ) (φ : PolF D T.rank S.rank)
    (hi : ∀ g, IntegrableOn (fun h => thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) 𝓕 ν) (U : GA D S → ℂ)
    (hU : ∀ g, Lift.liftInt ν 𝓕 (thetaKO om) (pureTensorO ψ θ S T sS sT BS BT f φ) F g = U g)
    (hl : ∀ i g, U (g * κ i) = a i * U g) :
    (∀ g, IntegrableOn (fun h => thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h) 𝓕 ν) ∧
      liftS om ν 𝓕 F (pureTensorO ψ θ S T sS sT BS BT f' φ) = (Nat.card ι : ℂ) • U := by
  have e : ∀ g h, thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h =
      ∑ i, (a i)⁻¹ * (thetaKO om (g * κ i) h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) := fun g h => by
    rw [hf', (pt_sum hom.std hθ sS BS sT BT _ _ _ (fun i => hom.om_pres _ _ hf) φ).2]
    unfold thetaKO
    rw [map_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pt_om hom hθ sS BS sT BT hf (hκ i), map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Module.End.mul_apply, ← map_mul,
      Prod.mk_mul_mk, mul_one]
  refine ⟨fun g => ?_, funext fun g => ?_⟩
  · simp only [e]
    exact integrable_finset_sum _ fun i _ => (hi _).const_mul _
  · show ∫ h in 𝓕, thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h ∂ν = _
    simp only [e]
    rw [integral_finset_sum _ fun i _ => (hi _).const_mul _]
    have : ∀ i, ∫ h in 𝓕, (a i)⁻¹ * (thetaKO om (g * κ i) h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) ∂ν = U g := fun i => by
      rw [integral_const_mul]
      have h1 := hU (g * κ i)
      unfold Lift.liftInt at h1
      rw [h1, hl, ← mul_assoc, inv_mul_cancel₀ (ha i), one_mul]
    simp only [this, Finset.sum_const, Finset.card_univ, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem levChi_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (P : LevelP L.Pg L.r ℂ) (p : P.H)
    {κ : GA D V} (hκ : IsLevelLift V β L p.1 κ) : κ ∈ levS V β (withP L P) :=
  ⟨hκ.1, hκ.2.1, by
    show rTup β L (finE V κ) ∈ P.H
    rw [hκ.2.2]; exact p.2⟩

theorem step_eigen {S T : HSp D} {Sp : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (hCR : GlobalTheory.Published.CuspRapidDecay) {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {f : WO S T → ℂ} (hpt : ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P))
    {M : DSModel S Sp} {β : GL (Fin S.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ S.rank} (hL : flag1L L = L)
    {μ : Measure (GA D S)} {𝓔 : Set (GA D S)} (hμ : μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ S) 𝓔 μ)
    {Ds : Type} [AddCommGroup Ds] [Module ℂ Ds] {It : PolF D T.rank S.rank →ₗ[ℂ] Ds →ₗ[ℂ] SmT M} (hIt : It ≠ 0)
    {CC : Submodule ℂ (Ds →ₗ[ℂ] (GA D T → ℂ))} (hCC : ∀ F : CC, ∀ v, ∀ γ ∈ GQ T, ∀ g, F.1 v (γ * g) = F.1 v g)
    {β' : GL (Fin T.rank) (Lev.EAf D)} {L' : LevDat D.host.E ℂ T.rank}
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hν : ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ T) 𝓕 ν)
    {io : CC →ₗ[ℂ] MultT θ M (levS S β L) (levChi S β L)}
    (hio : Lift.IsIo ν 𝓕 (thetaKO om) (pureTensorO ψ θ S T sS sT BS BT f) It CC _ io)
    {g0 : G0 L.Pg L.r} {κ : GA D S} (hκ : IsLevelLift S β L g0 κ) {g0' : G0 L'.Pg L'.r} {κ' : GA D T}
    (hκ' : IsLevelLift T β' L' g0' κ') {a' : ℂ} (hf : (levChi S β (flagL L) κ)⁻¹ • om (κ, κ') f = a' • f)
    (F : CC) {c : ℂ} (hF : ∀ v h, a' * F.1 v (h * κ') = c * F.1 v h) (v : SmT M) (g : GA D S) :
    (levChi S β (flagL L) κ)⁻¹ * (io F).1 v (g * κ) = c * (io F).1 v g := by
  have := GlobalTheory.ChainEquiv.step ψ θ hθ χS χT om hom sS BS sT BT f hpt M β L hL μ hμ.1 𝓔 hμ.2 (GlobalTheory.MultFinite.schurMult hCR _ _)
    It hIt CC hCC β' L' ν hν.1 𝓕 hν.2 io hio g0 κ hκ g0' κ' hκ' a' hf F (c • F) (fun v h => (hF v h).symm) v g
  rw [← this, map_smul]
  rfl

end GlobalTheory.Fam.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevDatYZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevYZero

open Formalism.IndefR.Lev Formalism.L2.DIV

theorem lev_datY_zero {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (r t : ℕ) (hr : r ≤ V.rank) (hn : V.rank = r) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ ξ) (hL : L = datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) (g : GL (Fin V.rank) (Lev.EAf D))
    (hU : g ∈ UA D.sp.cm V.gram) :
    (g ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ g ∈ St β ∧ (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) ∈ P.H) ∧
      ∀ h : (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) ∈ P.H, levFn β L g = P.chi ⟨_, h⟩ := by
  subst hL
  have hP : (datY (D := D) V.rank r t 0 hr Pg ∅ P χ ξ Frm.B).P = P := by simp [datY]
  constructor
  · rw [mem_lev, mem_parLev]
    constructor
    · rintro ⟨⟨-, hS, -, -⟩, hH⟩
      refine ⟨hS, ?_⟩
      rw [hP] at hH
      exact hH
    · rintro ⟨hS, hH⟩
      refine ⟨⟨hU, hS, fun PP _ => ?_, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩
      · rw [mem_blockTri]
        intro i j hij
        exfalso
        have hi : (i : ℕ) < r := hn ▸ i.2
        have hj : (j : ℕ) < r := hn ▸ j.2
        simp [datY, blkOf, hi, hj] at hij
      · show rTup β _ g ∈ _
        rw [hP]
        exact hH
  · intro h
    unfold levFn
    change ext1 P.H P.chi (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) * _ * _ = _
    simp only [datY, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    exact extendOne_of_mem _ h

end GlobalTheory.LevYZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTrivialNearOneOfLocalBadPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section
namespace GlobalTheory.ChiCont

theorem chi_eq_one_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F)))
    (S : StepLevel F E σ J T f bad) (u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (s : Finset (HeightOneSpectrum (𝓞 F)))
    (H : ∀ v ∈ s, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) →
      bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) :
    ∀ κ : S.U, (∀ v ∈ s, bc (prV (E := E) v) κ.1 = bc (prV (E := E) v) u) →
      (∀ v ∈ bad, v ∉ s → bc (prV (E := E) v) κ.1 = 1) → S.chi κ = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    intro κ _ hb
    exact S.chi_triv κ (fun v hv => hb v hv (Finset.notMem_empty v))
  | @insert v s hvs ih =>
    intro κ hu hb
    have hκ := (S.U_eq κ.1).1 κ.2
    set x0 := Formalism.UG.P.afsplitU v (bc (prV (E := E) v) κ.1) 1 with hx0
    have hx0v : bc (prV (E := E) v) x0 = bc (prV (E := E) v) κ.1 := Formalism.UG.P.afsplit_right1 _ _ _
    have hx0w : ∀ w, w ≠ v → bc (prV (E := E) w) x0 = 1 := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      simp
    have hx0U : x0 ∈ S.U := by
      rw [S.U_eq]
      refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ.1 hκ.1) (one_mem _), fun w => ?_⟩
      by_cases hw : w = v
      · subst hw
        rw [hx0v]
        exact hκ.2 w
      · rw [hx0w w hw]
        exact one_mem _
    let x : S.U := ⟨x0, hx0U⟩
    have hchix : S.chi x = 1 :=
      H v (Finset.mem_insert_self v s) x hx0w (by rw [hx0v]; exact hu v (Finset.mem_insert_self v s))
    let κ' : S.U := x⁻¹ * κ
    have hκ'w : ∀ w, w ≠ v → bc (prV (E := E) w) κ'.1 = bc (prV (E := E) w) κ.1 := by
      intro w hw
      show bc (prV (E := E) w) (x0⁻¹ * κ.1) = _
      rw [map_mul, map_inv, hx0w w hw, inv_one, one_mul]
    have hκ'v : bc (prV (E := E) v) κ'.1 = 1 := by
      show bc (prV (E := E) v) (x0⁻¹ * κ.1) = _
      rw [map_mul, map_inv, hx0v, inv_mul_cancel]
    have hchi' : S.chi κ' = 1 := by
      refine ih (fun w hw => H w (Finset.mem_insert_of_mem hw)) κ' ?_ ?_
      · intro w hw
        have hwv : w ≠ v := fun h => hvs (h ▸ hw)
        rw [hκ'w w hwv]
        exact hu w (Finset.mem_insert_of_mem hw)
      · intro w hw hws
        by_cases hwv : w = v
        · subst hwv; exact hκ'v
        · rw [hκ'w w hwv]
          exact hb w hw (by simp [hwv, hws])
    have hk : κ = x * κ' := by rw [mul_inv_cancel_left]
    rw [hk, map_mul, hchix, hchi', one_mul]

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Vs : Set (HeightOneSpectrum (𝓞 F))), Vs.Finite → (∀ v ∈ bad, v ∈ Vs) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ v ∈ Vs, ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) → bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) := by
  intro F E _ _ _ _ _ σ n J T f bad S Vs hVs hbad hloc
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  have hall : ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ v ∈ Vs,
      ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) →
        bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1 :=
    (Filter.eventually_all_finite hVs).2 hloc
  filter_upwards [hall] with u hu κ hκu
  refine chi_eq_one_of_split σ J T f bad S u hVs.toFinset
    (fun v hv => hu v (hVs.mem_toFinset.1 hv)) κ (fun v _ => by rw [hκu]) ?_
  intro v hv hvs
  exact absurd (hVs.mem_toFinset.2 (hbad v hv)) hvs

end GlobalTheory.ChiCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_places_finite : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → Set.Finite {PP : Pl D.host.E | PP ∈ (pk W).Pg ∨ QAll W PP} := by
  first | exact @GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces | exact GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces | (intros; apply GlobalTheory.Fam.finite_levelPlaces_or_tuplePlaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_places_under_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ PP PP' : Pl D.host.E, (PP ∈ (pk W).Pg ∨ QAll W PP) → (PP' ∈ (pk W).Pg ∨ QAll W PP') → PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) → PP = PP' := by
  first | exact @GlobalTheory.Fam.pg_qAll_under_inj | exact GlobalTheory.Fam.pg_qAll_under_inj | (intros; apply GlobalTheory.Fam.pg_qAll_under_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroTypeFrameLocality
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.ReadAtBase

theorem mat_read {k : Type} [CommRing k] {N Y : Type} [Fintype N] [DecidableEq N] [Fintype Y] [DecidableEq Y] (σ : N ≃ Y)
    (β' βi' W Mi M0 : Matrix N N k) (Fb : Matrix N Y k) (Fg : Matrix Y N k) (bs bi X : Matrix Y Y k)
    {Yy G : Matrix _ _ k} (h1 : β' * W * βi' = Mi * Yy * M0) (hY : Yy = Fb * G * Fg) (hG : G = bs * X * bi) (h2 : βi' * β' = 1) (h3 : M0 * Mi = 1)
    (h4 : Fg * Fb = 1) (h5 : bi * bs = 1) (h6 : β' = (Mi * Fb * bs).submatrix id σ) :
    W = X.submatrix σ σ := by
  subst hY hG
  have hs : ∀ (M : Matrix N N k) (P : Matrix N Y k), M * P.submatrix id σ = (M * P).submatrix id σ := fun M P => by
    ext i j; simp [Matrix.mul_apply]
  have hA : β' * W = β' * X.submatrix σ σ := by
    have e1 : β' * W = β' * W * βi' * β' := by rw [Matrix.mul_assoc (β' * W), h2, Matrix.mul_one]
    rw [e1, h1, h6, hs, Matrix.submatrix_mul_equiv _ _ _ σ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc M0 Mi, h3, Matrix.one_mul, ← Matrix.mul_assoc Fg Fb, h4, Matrix.one_mul,
      h5, Matrix.mul_one]
  calc W = βi' * β' * W := by rw [h2, Matrix.one_mul]
    _ = βi' * β' * X.submatrix σ σ := by rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc]
    _ = X.submatrix σ σ := by rw [h2, Matrix.one_mul]

end GlobalTheory.ReadAtBase

namespace GlobalTheory.ReadAtBase

theorem map_mt_conj {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) (V : HSp D) (t y : GA D V) :
    (Formalism.L2.Theta.mt V (t⁻¹ * y * t)).map p.π =
      (Formalism.L2.Theta.mt V t⁻¹).map p.π * (Formalism.L2.Theta.mt V y).map p.π * (Formalism.L2.Theta.mt V t).map p.π := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]

theorem map_mt_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) (V : HSp D) (t : GA D V) :
    (Formalism.L2.Theta.mt V t).map p.π * (Formalism.L2.Theta.mt V t⁻¹).map p.π = 1 := by
  rw [← Matrix.map_mul]
  simp [Formalism.L2.Theta.mt]

theorem map_inv_mul {R k : Type} [CommRing R] [CommRing k] {n : ℕ} (f : R →+* k) (β : GL (Fin n) R) :
    (β⁻¹).val.map f * β.val.map f = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (g : GL (Fin n) A) (i j : Fin n) :
    (Formalism.UG.bc f g).val i j = f (g.val i j) := rfl

theorem intGL_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (w : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (i j : Fin n) :
    (intGL F E n w).val i j = (w.val i j : E ⊗[F] Formalism.L2.Herm.Af F) := rfl
end GlobalTheory.ReadAtBase

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.ReadAtBase.red_of_isLoc : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (hr : D.R.r ≤ (d.st 0).V.rank) (hc : 0 + (G.s + 1) = G.s + 1) (x : G.S.P.J) (y : GA D (d.st 0).V), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) hc) y ((GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t)) (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k))) → Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0) ∈ Formalism.L2.DIV.St (d.st 0).β → G.Red x (Formalism.L2.DIV.upperLeftBlock hr (Formalism.L2.DIV.redFn (d.st 0).β PP (Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)))) := by
  intro D u d τ PP G hr hc x y hL hSt
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D G.k G.q PP G.idem
  have hπ' : ∀ a, π' (toEAf D a) = (GlobalTheory.LocMod.ofSplit G.q).π a := hπ
  obtain ⟨w, hw⟩ := hSt
  rw [← hw, Formalism.L2.DIV.redFn_frGL]
  obtain ⟨e, he, hmv⟩ := G.frame 0 (G.s + 1) hc
  have hβ := GlobalTheory.LocMod.StepVec.map_eq_of_movedTo (GlobalTheory.LocMod.ofSplit G.q) (G.FY 0 (G.s + 1) hc) hπ' _ _ hmv
  have hn : (d.st 0).V.rank ≤ D.R.r := by
    have h1 := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_mul, add_zero] at h1
    have h2 := G.hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  intro a b a' b' ha hb z hz
  have hrb : ((upperLeftBlock hr ((Formalism.UG.bc (resS D.host.F PP)) w)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) =
      (((Formalism.UG.bc (resS D.host.F PP)) w) : Matrix _ _ (kP PP)).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    refine upper_block_val_submatrix hr ?_
    intro i j hij
    exfalso
    have hi : blk2 D.R.r i = 0 := by simp [blk2, show i.val < D.R.r from lt_of_lt_of_le i.2 hn]
    rw [hi] at hij
    exact Nat.not_lt_zero _ hij
  rw [hrb] at hz
  have hpos : ∀ (c : Fin D.R.k ⊕ Fin (G.s + 1)) (c' : Fin D.R.r), c'.val = IndefiniteRowSideFullHecke.FramePositiveSum.framePos D.R.k (G.s + 1) c →
      Fin.castLE hr c' = e (StepData.ixZero _ _ c) := by
    intro c c' hc'
    ext
    rw [Fin.val_castLE, he, hc']
    rcases c with c | c <;> rfl
  rw [Matrix.submatrix_apply, hpos a a' ha, hpos b b' hb] at hz
  have e1 : frGL (d.st 0).β w = (d.st 0).β * Formalism.L2.DIV.intGL _ _ _ w * ((d.st 0).β)⁻¹ := rfl
  have e2 := congrArg Units.val (e1.symm.trans hw)
  rw [Units.val_mul, Units.val_mul] at e2
  have h1 := congrArg (Matrix.map · π') e2
  simp only [Matrix.map_mul] at h1
  have e4 : (finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)).val.map π' =
      (Formalism.L2.Theta.mt (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)).map (GlobalTheory.LocMod.ofSplit G.q).π := by
    ext i j
    exact hπ' _
  have h1' := (h1.trans e4).trans (GlobalTheory.ReadAtBase.map_mt_conj (GlobalTheory.LocMod.ofSplit G.q) _ (d.t 0) y)
  have hG : ((StepData.typeFrame G.S.ϖ (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)).conj
      ((StepData.reGL (StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t))) x)).val =
      ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hc).val *
        (StepData.reGL (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)
          (StepData.reGL (StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t)) (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k))).val *
        (((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hc)⁻¹).val := rfl
  have hW := GlobalTheory.ReadAtBase.mat_read ((e.symm).trans (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)) _ _ _ _ _ _ _ _ _ _ h1' hL.2
    hG (GlobalTheory.ReadAtBase.map_inv_mul _ _)
    (GlobalTheory.ReadAtBase.map_mt_inv _ _ _) (G.FY 0 (G.s + 1) hc).γβ (Units.inv_mul _) hβ
  have h := congrFun (congrFun hW (e (StepData.ixZero _ _ a))) (e (StepData.ixZero _ _ b))
  simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply, StepData.reGL_val] at h
  simp only [GlobalTheory.ReadAtBase.intGL_apply] at h
  simp only [GlobalTheory.ReadAtBase.bc_apply] at hz
  have hz0 : resS D.host.F PP (w.val (e (StepData.ixZero _ _ a)) (e (StepData.ixZero _ _ b)) - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]
    exact sub_self _
  have hv := (hred.ker _).1 hz0
  simp only [RingHom.comp_apply, Subring.coe_subtype, AddSubgroupClass.coe_sub, map_sub, h] at hv
  have e8 : π' ((oToS _ _ z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D) =
      (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := hπ' (incA D (z : D.host.E))
  rw [e8] at hv
  exact hv
end

