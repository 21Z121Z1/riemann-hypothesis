import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0561
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0558
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0562
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairScalar
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop.UnitAtLevel

theorem smulOne_mulVec {R : Type} [CommRing R] {n : ℕ} (c : R) (y : Fin n → R) :
    Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y = c • y := by
  funext i
  rw [Matrix.smul_one_eq_diagonal, Matrix.mulVec_diagonal]
  rfl

theorem inv_of_scalar {R : Type} [CommRing R] {n : ℕ} (hn : 0 < n) (A : GL (Fin n) R) (c : R)
    (hA : A.val = c • (1 : Matrix (Fin n) (Fin n) R)) :
    ∃ ι : R, ι * c = 1 ∧ (A⁻¹).val = ι • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : (A⁻¹).val * A.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  rw [hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] at h2
  refine ⟨(A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩, by rw [mul_comm]; exact h2, ?_⟩
  have h3 : A.val * ((A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
    rw [hA, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, one_smul]
  calc (A⁻¹).val = (A⁻¹).val * (A.val * ((A⁻¹).val ⟨0, hn⟩ ⟨0, hn⟩ • (1 : Matrix (Fin n) (Fin n) R))) := by
        rw [h3, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem mem_of_shift {R : Type} [CommRing R] (O : Subring R) (a u ι : R) (ha : ∃ a', a' * a = 1) (hι : ι * u = 1)
    (key : ∀ c, a * c ∈ O ↔ a * (ι * c) ∈ O) : u ∈ O ∧ ι ∈ O := by
  obtain ⟨a', ha'⟩ := ha
  have e1 : a * a' = 1 := by rw [mul_comm]; exact ha'
  have e2 : a * (ι * a') = ι := by linear_combination ι * e1
  have e3 : a * (ι * (a' * u)) = 1 := by linear_combination (ι * u) * e1 + hι
  have e4 : a * (a' * u) = u := by linear_combination u * e1
  constructor
  · have := (key (a' * u)).2 (by rw [e3]; exact O.one_mem)
    rwa [e4] at this
  · have := (key a').1 (by rw [e1]; exact O.one_mem)
    rwa [e2] at this

end GlobalTheory.MiTop.UnitAtLevel

namespace GlobalTheory.MiTop

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem centralRatio_stabLoc_atLevel : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) = v) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((pk W).ΛY 0) v := by

  intro D L hT Gi Gl Kc Yd cX ex W hW hrS u u' f f' B B' hP hP' a₀ a a₀' a' hA hA' z hz hzc k hk he v hv
  have hm : 0 < D.R.m := by unfold Ranks.rS at hrS; omega
  have hfr := (GlobalTheory.T.self_dual_lattice_frame_chain W hW 0 hm).2
  have hkSt := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) (W.Q.Rl.βY 0) ((pk W).ΛY 0) hfr k).1
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_of_mem_levG hk) v
  obtain ⟨e, α, hl⟩ := GlobalTheory.T.level_place_frame_exists W hW hrS v hv
  obtain ⟨ζ, hζ⟩ := GlobalTheory.T.center_adelicUnitaryGroup_scalar_at_finitePlace D (D.sp.Y 0) z hzc v
  have hpos : 0 < (D.sp.Y 0).rank := by
    have := B.d.rank_add
    omega
  obtain ⟨ι, hιζ, hζinv⟩ := GlobalTheory.MiTop.UnitAtLevel.inv_of_scalar hpos _ ζ hζ
  have htinv : (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f B a₀ a)))⁻¹ =
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k))⁻¹ *
      ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f' B' a₀' a')))⁻¹ *
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z))⁻¹) := by
    rw [he, map_mul, map_mul, map_mul, map_mul, mul_inv_rev, mul_inv_rev]
  have hkinv : ∀ y, y ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v ↔
      Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k))⁻¹).val y ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v := by
    have h := GlobalTheory.AdelicU.mem_stabLoc.1 (inv_mem hkSt)
    intro y
    have h2 := h y
    rw [map_inv] at h2
    exact h2
  have key : ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v ↔
      ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * (ι * c) ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
    intro c
    rw [← hl u f B (GlobalTheory.MiTop.PlacedP.placed f B hP) a₀ a hA c, ← hl u' f' B' (GlobalTheory.MiTop.PlacedP.placed f' B' hP') a₀' a' hA' (ι * c), htinv, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hζinv, GlobalTheory.MiTop.UnitAtLevel.smulOne_mulVec, smul_smul]
    exact (hkinv _).symm
  obtain ⟨hζO, hιO⟩ := GlobalTheory.MiTop.UnitAtLevel.mem_of_shift (GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) _ ζ ι
    ⟨α, Units.mul_inv α⟩ hιζ key
  refine GlobalTheory.AdelicU.mem_stabLoc.2 ?_
  intro y
  rw [hζ, GlobalTheory.MiTop.UnitAtLevel.smulOne_mulVec]
  constructor
  · intro hy
    have := Submodule.smul_mem _ (⟨ζ, hζO⟩ : GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) hy
    rwa [Subring.smul_def] at this
  · intro hy
    have := Submodule.smul_mem _ (⟨ι, hιO⟩ : GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) hy
    rwa [Subring.smul_def, smul_smul, hιζ, one_smul] at this

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondFlatMap_moved_core_lattice_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ γ ∈ grpAt B.V₀ (· = v), ∃ M : Lat B.V₀, IsSelfDualC B.V₀ M ∧ Moves B.V₀ γ LW₀ M (· = v) ∧ Vac ψ J.W₀ B.V₀ LV₀ M (· = v) (flatFB s (s.om (1, B.d.emb0 γ) f)) := by
  first | exact @GlobalTheory.FinPl.movedVac | exact GlobalTheory.FinPl.movedVac | (intros; apply GlobalTheory.FinPl.movedVac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondFlatMap_unipotent_stabilizer_translate_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LW : Lat B.V) (v : Pl D), IsSelfDualC J.W LV → IsSelfDualC B.V LW → Tame D v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ (x : GA D B.V) (κ : GA D B.V), InK B.V LW (· = v) κ → flatFB s (s.om (1, n * x * κ) f) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s (s.om (1, x) f) := by
  first | exact @GlobalTheory.FinPl.flatFB_om_shift | exact GlobalTheory.FinPl.flatFB_om_shift | (intros; apply GlobalTheory.FinPl.flatFB_om_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondFlatMap_vacuum_translate_isVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (P : Pl D → Prop), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v ∧ UnrAt s v) → ∀ f, Vac ψ J.W B.V LV LW P f → ∀ h₁ ∈ grpOff J.W P, ∀ h₂ ∈ grpOff B.V P, Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s (s.om (h₁, h₂) f)) := by
  first | exact @GlobalTheory.VacSecondPf.vac_second | exact GlobalTheory.VacSecondPf.vac_second | (intros; apply GlobalTheory.VacSecondPf.vac_second <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepValueFixedLevelPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.SeeSaw.GValMid.gValue_mid | exact GlobalTheory.SeeSaw.GValMid.gValue_mid | (intros; apply GlobalTheory.SeeSaw.GValMid.gValue_mid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j (h : j + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 →
    (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j 0 h) (c.J j 0 h)) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) Ψ₂ →
    c.lst j h (v.τ j h) s₁ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eGT j h) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.lst j h (v.τ j h) s₁ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.LevelLast.last_value | exact GlobalTheory.LevelLast.last_value | (intros; apply GlobalTheory.LevelLast.last_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawCombinationsCompositeNeZeroOfVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.CombNonzero

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}

theorem comb_o_ne_zero (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') (L : LocPl ψ S T M M')
    {h : WO S T → ℂ} (hv : GlobalTheory.FinPl.Vac ψ S T M M' (· = L.q.v) h) (h0 : h ≠ 0) : comb ψ S T L.o h ≠ 0 := by
  classical
  set p : Place D L.k := ofSplit L.q with hp
  obtain ⟨ε, hε, hs⟩ := L.q.above
  obtain ⟨s1, s2, -⟩ := L.q.split
  have hsc := GlobalTheory.PlaceModelSum.isSplitIdem_cA L.q.split
  have c1 : cA D L.q.e * cA D L.q.e = cA D L.q.e := by rw [← map_mul, s1]
  have he1 : algebraMap (AF D.host.F) (AE D) ε * L.q.e = L.q.e := by
    rw [← hs]; linear_combination s1 + s2
  have he2 : algebraMap (AF D.host.F) (AE D) ε * cA D L.q.e = cA D L.q.e := by
    rw [← hs]; linear_combination c1 + s2

  have fix : ∀ a : AE D, IsSplitIdem D a → algebraMap (AF D.host.F) (AE D) ε * a = a →
      ∀ u ∈ (latO S T (M : Set _) (M' : Set _) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T a, heisO ψ S T u h = h := by
    intro a ha hea u hu
    have hm := GlobalTheory.PlaceModel.idem_smul_mem hε ha.1 hea (AddSubgroup.mem_inf.1 hu).1
    have hua : a • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 (AddSubgroup.mem_inf.1 hu).2
    rw [hua] at hm
    exact hv.2.2 a ha u (AddSubgroup.mem_inf.1 hm).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (AddSubgroup.mem_inf.1 hm).2)
  have hO : GlobalTheory.PlaceModelSum.IsOrthSum L.q.e :=
    ⟨Unit, {()}, fun _ => L.q.e, fun _ _ => L.q.split, fun _ _ _ _ hne => absurd rfl hne, by simp⟩
  obtain ⟨T', hT'⟩ := GlobalTheory.FlatVecExist.exists_model_of_fix hψ hM hM' hO s2 (fix _ L.q.split he1) (fix _ hsc he2)
  let Tm := T'.comp (GlobalTheory.LocMod.Witness.ext p L.FS L.FT)
  have hTm : p.IsModel ψ L.FS L.FT Tm := by
    refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
    · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T M M' hM hM' L.q.e s1 (GlobalTheory.PlaceModelSum.infPart_split L.q.split)
        h hv.1 T' hT' _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ)
    · refine Eq.trans (congrArg T' ?_) (hT'.trans _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ) _
        (GlobalTheory.LocMod.Witness.up_half p L.FS L.FT x))
      funext t
      rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.down_add,
        GlobalTheory.LocMod.Witness.down_up, e]
      exact if_congr (GlobalTheory.LocMod.Witness.half_add (GlobalTheory.LocMod.Witness.up_half p L.FS L.FT x)).symm rfl rfl
    · refine Eq.trans (congrArg T' ?_) (hT'.modul _ (GlobalTheory.LocMod.Witness.ext_sb p L.FS L.FT hM hM' Φ) _ hy)
      funext t
      rw [GlobalTheory.LocMod.Witness.ext_apply, GlobalTheory.LocMod.Witness.ext_apply, e]
      split_ifs with ht
      · rw [GlobalTheory.LocMod.Witness.up_down p L.FS L.FT ht]
      · rw [mul_zero]
  let Φ₀ : SB (Matrix L.Y L.Y' L.k) := ⟨_, GlobalTheory.LatIndSB.indicator_latO_mem_SB D ψ S T M M' hM hM' L⟩
  have hΦ₀ : Tm Φ₀ = h := by
    have e1 : GlobalTheory.LocMod.Witness.ext p L.FS L.FT Φ₀ = (1 : ℂ) • halfInd L.q.e (latO S T (M : Set _) (M' : Set _) fun _ => True) := by
      funext t
      rw [one_smul, GlobalTheory.LocMod.Witness.ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht]
        show Set.indicator {x | p.up L.FS L.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = L.q.v)} (fun _ => (1 : ℂ)) (p.down L.FS L.FT t) = _
        rw [Set.indicator_apply]
        refine if_congr ?_ rfl rfl
        change p.up L.FS L.FT (p.down L.FS L.FT t) ∈ latO S T (M : Set _) (M' : Set _) (· = L.q.v) ↔ _
        rw [GlobalTheory.LocMod.Witness.up_down p L.FS L.FT ht, and_iff_left (show IsHalf L.q.e t from ht)]
        refine ⟨fun hm => GlobalTheory.PlaceModel.latO_le_top _ hm, fun hm => ?_⟩
        have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε s1 he1 hm).1
        have h3 : L.q.e • t = t := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht)
        rw [h3] at h2
        exact h2
      · rw [if_neg ht, if_neg fun hh => ht hh.2]
    change T' (GlobalTheory.LocMod.Witness.ext p L.FS L.FT Φ₀) = h
    rw [e1]
    exact hT'.vac
  obtain ⟨O, hO, hO1⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  have hOne : Tm O = comb ψ S T L.o (Tm Φ₀) := L.o_is Tm hTm Φ₀ O hO rfl
  intro hc
  rw [hΦ₀, hc] at hOne
  have hO0 : O ≠ 0 := by rintro rfl; simp at hO1
  have hz := (GlobalTheory.LocModU.localModel_uniq_transport_exist D L.k p L.Y L.Y' S T L.FS L.FT ψ hψ).1 Tm ((0 : ℂ) • Tm) hTm
    (GlobalTheory.LocMod.Witness.isModel_smul p hTm 0) O hO0 (by rw [hOne]; simp)
  apply h0
  rw [← hΦ₀, hz]
  simp

theorem vac_mono (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M')
    {P Q : GlobalTheory.FinPl.Pl D → Prop} (hQP : ∀ v, Q v → P v) {f : WO S T → ℂ}
    (hf : GlobalTheory.FinPl.Vac ψ S T M M' P f) : GlobalTheory.FinPl.Vac ψ S T M M' Q f := by
  have hiff := (GlobalTheory.DisjComb.main D ψ hψ S T Q (fun v => P v ∧ ¬ Q v) (fun v hq hp => hp.2 hq)).2.2.2.2 M M' f hM hM'
  have e : (fun v => Q v ∨ (P v ∧ ¬ Q v)) = P := by
    funext v
    apply propext
    constructor
    · rintro (hq | hq)
      · exact hQP v hq
      · exact hq.1
    · intro hp
      by_cases hq : Q v
      · exact Or.inl hq
      · exact Or.inr ⟨hp, hq⟩
  rw [e] at hiff
  exact (hiff.1 hf).1

theorem fold_vac (hψ : IsStdChar D ψ (-1)) {n : ℕ} (Lp : Fin n → LocPl ψ S T M M') (P : GlobalTheory.FinPl.Pl D → Prop)
    (l : List (Fin n)) (hl : ∀ i ∈ l, ¬ P (Lp i).q.v) (g : WO S T → ℂ) (hg : GlobalTheory.FinPl.Vac ψ S T M M' P g) :
    GlobalTheory.FinPl.Vac ψ S T M M' P (l.foldr (fun i g' => comb ψ S T (Lp i).o g') g) := by
  induction l with
  | nil => exact hg
  | cons i l ih =>
    rw [List.foldr_cons]
    have hc : GlobalTheory.FinPl.CombAt (· = (Lp i).q.v) (Lp i).o := fun u hu =>
      GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (Lp i).q u ((Lp i).o_at u hu)
    refine ((GlobalTheory.DisjComb.main D ψ hψ S T (· = (Lp i).q.v) P
      (fun v hv hp => hl i List.mem_cons_self (hv ▸ hp))).2.1 _ hc).2 M M' _ ?_
    exact ih fun j hj => hl j (List.mem_cons_of_mem _ hj)

theorem fold_ne_zero (hψ : IsStdChar D ψ (-1)) (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M') {n : ℕ}
    (Lp : Fin n → LocPl ψ S T M M') (hinj : Function.Injective fun i => (Lp i).q.v) (l : List (Fin n)) (hnd : l.Nodup)
    (g : WO S T → ℂ) (hg : GlobalTheory.FinPl.Vac ψ S T M M' (fun v => ∃ i ∈ l, (Lp i).q.v = v) g) (g0 : g ≠ 0) :
    l.foldr (fun i g' => comb ψ S T (Lp i).o g') g ≠ 0 := by
  induction l with
  | nil => exact g0
  | cons i l ih =>
    rw [List.foldr_cons]
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
    refine comb_o_ne_zero hψ hM hM' (Lp i) ?_ (ih hnd' (vac_mono hψ hM hM'
      (fun v ⟨j, hj, e⟩ => ⟨j, List.mem_cons_of_mem _ hj, e⟩) hg))
    refine fold_vac hψ Lp _ l (fun j hj e => hi ?_) g (vac_mono hψ hM hM' (fun v hv => ⟨i, List.mem_cons_self, hv.symm⟩) hg)
    have : j = i := hinj e
    exact this ▸ hj

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (Lp : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (Lp i).q.v) → ∀ g, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) g → g ≠ 0 → (List.finRange n).foldr (fun i g' => comb ψ S T (Lp i).o g') g ≠ 0 := by
  intro D ψ hψ S T M M' hM hM' n Lp hinj g hg g0
  exact fold_ne_zero hψ hM hM' Lp hinj _ (List.nodup_finRange n) g (vac_mono hψ hM hM' (fun _ _ => trivial) hg) g0

end GlobalTheory.CombNonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SmallAllPf

variable {D : D7}

theorem vac_at_place {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}
    {f : WO S T → ℂ} (h : Vac ψ S T LS LT P f) {v : Pl D} (hv : P v) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨α, hα, hP, rest⟩
    exact ⟨α, hα, fun w hw => hP w fun e => hw (e ▸ hv), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem main : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ q χ hχ
  have hSO := GlobalTheory.T.smallPair_pairing_at_one_gluedPlace D
  have hOB := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D
  have hAB := GlobalTheory.T.epsilonFourierProduct_bijective_gluedPlaces D
  choose r e hr hval using fun i => hSO k (p i) n n' q (χ i) (hχ i)
  refine ⟨r, e, hr, ?_⟩
  intro ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT hunr vA vS vT a b s L₁ L₂ L₃ hL₁ hL₂ hL₃ hloc
    Ξ Ξ' Φ₂ hΞ hΦ₂ hO φ hφ F hF
  have hstd : IsStdChar D ψ (-1) := hom₁.std
  have hinj : Function.Injective fun i => (p i).v := hP.inj
  have hPi : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  set c : ι → ℂ := fun i => (r i : ℂ) * chrPow χW ((p i).idele q.unit) (e i) with hc
  set Ψ : ι → Matrix n (n' ⊕ Fin 1) k → ℂ :=
    fun i => tensCol (phiOne (a.P i) (b.Q i)) (charInd (resChar (χ i) (hχ i) q) (s i • b.Q i)) with hΨ

  have keep : ∀ (l : List ι) (f f' : WO V₀ S → ℂ),
      OverAll ψ a.α₀ b.β L₁ L₂ Ψ l f f' → ∀ i, i ∉ l → Vac ψ V₀ S L₁ L₂ (· = (p i).v) f →
        Vac ψ V₀ S L₁ L₂ (· = (p i).v) f' := by
    intro l
    induction l with
    | nil =>
      intro f f' h i _ hv
      have h' : f' = f := h
      rw [h']
      exact hv
    | cons j l ih =>
      intro f f' h i hi hv
      obtain ⟨g, hg, hOj⟩ := h
      have hgv := ih f g hg i (fun hm => hi (List.mem_cons_of_mem j hm)) hv
      have hij : i ≠ j := fun e => hi (e ▸ List.mem_cons_self)
      exact ((hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hOj.2.2.1).2.1 _ _
        hOj).2 L₁ L₂ _ (fun e => hij (hinj e).symm) hgv
  have val : ∀ l : List ι, l.Nodup → ∀ (Ξ₀ Ξ₁ : WO V₀ S → ℂ),
      (∀ i, Vac ψ V₀ S L₁ L₂ (· = (p i).v) Ξ₀) → OverAll ψ a.α₀ b.β L₁ L₂ Ψ l Ξ₀ Ξ₁ →
      ∀ φ, a.Ram φ → smallPair o om₁ omT vA vS vT φ Ξ₀ Φ₂ F =
        (l.map c).prod * smallPair o om₁ omT vA vS vT (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) Ξ₁ Φ₂ F := by
    intro l
    induction l with
    | nil =>
      intro _ Ξ₀ Ξ₁ _ h φ _
      have h' : Ξ₁ = Ξ₀ := h
      subst h'
      simp [PairDat.sAll]
    | cons j l ih =>
      intro hnd Ξ₀ Ξ₁ h1 h φ hφ
      obtain ⟨g, hg, hOj⟩ := h
      have hj : j ∉ l := (List.nodup_cons.1 hnd).1
      have hgv := keep l Ξ₀ g hg j hj (h1 j)
      rw [ih hnd.tail Ξ₀ g h1 hg φ hφ]
      have hR : a.Ram (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) :=
        (hAB k ι p q χ hχ s n' A V₀ a hinj l).1.mapsTo hφ
      have hself := (hOB k (p j) n (n' ⊕ Fin 1) ψ hstd V₀ S (a.α₀ j) (b.β j) L₁ L₂ hL₁ hL₂ g hgv).2.2
        (hP.unit j) _ _ (hloc j).2.1 (hloc j).2.2
      obtain ⟨u1, u2, u3, u4⟩ := hunr _ (hPi j)
      have key := hval j ψ V₀ A L S T o ζ hζ hA hS hT χV χW χS χT om₁ omT hom₁ homT u1 u2 u3 u4 vA vS vT
        (a.α j) (a.α₀ j) (b.β j) (hloc j).1 (a.P j) (b.Q j) (s j) L₁ L₂ L₂ L₃ g g Ξ₁ Φ₂ hself hOj hL₂ hL₃
        (hloc j).2.2 (vac_at_place hΦ₂ (hPi j)) _ (hR.2 j) F hF
      have hcons : a.sAll q (fun i => resChar (χ i) (hχ i) q) s (j :: l) φ =
          sOp (a.α j) (a.P j) q (resChar (χ j) (hχ j) q) (s j)
            (a.sAll q (fun i => resChar (χ i) (hχ i) q) s l φ) := rfl
      rw [key, hcons, List.map_cons, List.prod_cons, hc]
      ring
  exact val I hP.nodup Ξ Ξ' (fun i => vac_at_place hΞ (hPi i)) hO φ hφ

end GlobalTheory.FinPl.SmallAllPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepTrilinearFormPropertiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleStep_trilinearForm_properties : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ T₁ T₂, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ φ, IsContAut S.B.A φ → ∃ (A : Submodule ℂ (GA D S.B'.V → ℂ)) (τ : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) A) (T : SB (Matrix Q.n₁ Q.n₀ Q.k) →ₗ[ℂ] SB (Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), IsSmoothRep τ ∧ (∀ y (f : A), (τ y f).1 = rTrans (Q.gl₂ y) f.1) ∧ (∀ f, IsContAut S.B'.V f → Q.Typed f → f ∈ A) ∧ TriPos Q.ψk Q.μ₁ Q.μ₂ (σ + 1) τ T ∧ (∀ Φ₁ Φ₂ (f : A), HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1)) ∧ ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f : A, T Ξ₁ Ξ₂ f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f.1 1 1 1 := by
  first | exact @GlobalTheory.TriStep.tri | exact GlobalTheory.TriStep.tri | (intros; apply GlobalTheory.TriStep.tri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLineTranslateOffLatticeKillsContractionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLine_translate_off_lattice_kills_contraction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ y : WO B.L S, MxAt P y → (B.o.resS S).symm (0, y) ∉ latO B.V₀ S (M : Set _) (LS : Set _) P → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ = 0 := by
  first | exact @GlobalTheory.FinPl.LineVanish.vanish | exact GlobalTheory.FinPl.LineVanish.vanish | (intros; apply GlobalTheory.FinPl.LineVanish.vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeTwistStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_lattice_twist : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ GlobalTheory.LevProd.Up a j hj ∧ ∀ i, GlobalTheory.LevProd.phi J j hj g i ∈ GlobalTheory.LevProd.H J j hj α i := by
  first | exact @GlobalTheory.LevProd.level_eq_up_inf | exact GlobalTheory.LevProd.level_eq_up_inf | (intros; apply GlobalTheory.LevProd.level_eq_up_inf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof : GlobalTheory.AdForm.TwLev' := by
  first | exact @GlobalTheory.AdForm.twLev_prime | exact GlobalTheory.AdForm.twLev_prime | (intros; apply GlobalTheory.AdForm.twLev_prime <;> assumption)
end

