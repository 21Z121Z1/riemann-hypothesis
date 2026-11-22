import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0363
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardRepsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RepsCard

theorem card_reps_eq : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V), SplitHyp H α A B Λ → ∀ SA SB : Finset V, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) SA → Formalism.L2.Th1.H.IsReps Λ B SB → SA.card = SB.card := by
  intro V _ _ H α A B Λ hyp SA SB hSA hSB
  obtain ⟨hH, -, hB, -, sdB, hΛ, -, -, -, h5⟩ := hyp
  have hBint := (Formalism.L2.Th1.H.semicharacterBasic V H hH B α hB).2.2
  have hΛint := (Formalism.L2.Th1.H.semicharacterBasic V H hH Λ α hΛ).2.2
  have hone : ∀ {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (c : ℂ), Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S →
      ∑ x ∈ S, (if x ∈ Λ₁ then c else 0) = c := by
    intro Λ₁ Λ₂ S c hS
    obtain ⟨x₀, hx₀, hd⟩ := hS.2.2 0 Λ₂.zero_mem
    have hx₀Λ : x₀ ∈ Λ₁ := by simpa using Λ₁.neg_mem hd
    rw [Finset.sum_eq_single x₀]
    · simp [hx₀Λ]
    · intro x hx hne
      rw [if_neg]
      intro hxΛ
      exact hne (hS.2.1 x hx x₀ hx₀ (Λ₁.sub_mem hxΛ hx₀Λ))
    · intro h; exact absurd hx₀ h
  have hcol : ∀ s ∈ SA, ∑ y ∈ SB, brk H y s = if s ∈ B then (SB.card : ℂ) else 0 := by
    intro s hs
    have hsΛ : s ∈ Λ := (hSA.1 s hs).1
    split_ifs with hsB
    · have hsd : s ∈ Formalism.L2.Th1.H.dualLat H B := by rw [sdB]; exact hsB
      rw [Finset.sum_congr rfl fun y hy => brk_one_of_int H (hsd y (hSB.1 y hy))]
      simp
    · by_contra hne
      apply hsB
      have hsd : s ∈ Formalism.L2.Th1.H.dualLat H B := by
        intro y hyB
        by_contra hno
        refine hne (char_sum_zero hSB (fun y => brk H y s) (fun u v => brk_add_left H u v s) ?_ (x₀ := y) hyB ?_)
        · intro m _ hmΛ; exact brk_one_of_int H (hΛint hsΛ m hmΛ)
        · intro h1; exact hno (int_of_brk_one H h1)
      rwa [sdB] at hsd
  have hrow : ∀ y ∈ SB, ∑ s ∈ SA, brk H y s = if y ∈ Λ then (SA.card : ℂ) else 0 := by
    intro y hy
    have hyB : y ∈ B := hSB.1 y hy
    split_ifs with hyΛ
    · rw [Finset.sum_congr rfl fun s hs => brk_one_of_int H (hΛint (hSA.1 s hs).1 y hyΛ)]
      simp
    · by_contra hne
      apply hyΛ
      apply h5 y hyB
      intro a haA haΛ
      by_contra hno
      refine hne (char_sum_zero hSA (fun s => brk H y s) (fun u v => brk_add_right H y u v) ?_ (x₀ := a) ⟨haΛ, haA⟩ ?_)
      · intro m _ hmB; exact brk_one_of_int H (hBint hmB y hyB)
      · intro h1; exact hno (int_of_brk_one H h1)
  have key : ∑ s ∈ SA, ∑ y ∈ SB, brk H y s = ∑ y ∈ SB, ∑ s ∈ SA, brk H y s := Finset.sum_comm
  rw [Finset.sum_congr rfl hcol, Finset.sum_congr rfl hrow, hone _ hSA, hone _ hSB] at key
  exact_mod_cast key.symm

end GlobalTheory.RepsCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFractionalIdealRelations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ChainIdeals

theorem host_ne_zero (D : D7) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ≠ 0 ∧ D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ dI D ≠ 0 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h
  · rw [h, zero_mul, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul, zero_mul] at hP; exact zero_ne_one hP
  · rw [h, mul_zero, zero_mul] at hP; exact zero_ne_one hP
  · rw [dI] at h; rw [h, zero_mul] at hP; exact zero_ne_one hP

theorem step (D : D7) {j : ℕ} (h : j + 1 + 1 ≤ D.R.m) :
    D.host.AA⁻¹ * (dI D * cI D j) = D.host.AA * cI D (j + 1 + 1) ∧
    D.host.AA⁻¹ * (dI D * cI D j) = FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j := by
  obtain ⟨-, hA, hB, -⟩ := host_ne_zero D
  have e1 : D.host.AA⁻¹ * (dI D * cI D j) = FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j := by
    rw [dI]
    calc D.host.AA⁻¹ * (FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AA * D.host.AAbar * cI D j)
        = (D.host.AA⁻¹ * D.host.AA) * (FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hA, one_mul]
  refine ⟨?_, e1⟩
  rw [e1]
  have hs := cI_step D h
  calc FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AAbar * cI D j
      = D.host.AAbar * (FractionalIdeal.spanSingleton _ D.host.xi0 * cI D j) := by ring
    _ = D.host.AAbar * (D.host.AA * D.host.AAbar⁻¹ * cI D (j + 1 + 1)) := by rw [hs]
    _ = (D.host.AAbar * D.host.AAbar⁻¹) * (D.host.AA * cI D (j + 1 + 1)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hB, one_mul]

end GlobalTheory.SeeSaw.ChainIdeals
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainLevelIntegralRealZetaOfTwistedTransformLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainLevelIntegralRealZeta_of_twisted_transform_laws : ∀ D : D7, LevelLawQ D → LevInt D := by
  first | exact @GlobalTheory.ChainTw.LevIntProof.levInt | exact GlobalTheory.ChainTw.LevIntProof.levInt | (intros; apply GlobalTheory.ChainTw.LevIntProof.levInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainProjectionLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLevelP.IoLevPf

theorem multT_val {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    (∀ γ ∈ GQ V, ∀ g, u v (γ * g) = u v g) ∧ ∀ k ∈ J, ∀ g, u v (g * k) = χ k * u v g := by
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 := GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f
    have h3 : ∀ g, u (PiTensorProduct.tprod ℂ f) g = (PiTensorProduct.lift.symm u) f g := fun g => by simp
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3, h3, h2.1 γ hγ g]
    · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3, h3, h2.2.2 k hk g, smul_eq_mul, smul_eq_mul]
      ring
  | add x y hx hy =>
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · rw [map_add, Pi.add_apply, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · rw [map_add, Pi.add_apply, Pi.add_apply, hx.2 k hk g, hy.2 k hk g]
      ring

end GlobalTheory.StepLevelP.IoLevPf

namespace GlobalTheory.StepLevelP

set_option maxHeartbeats 800000 in

theorem io_levChi : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t j, j + 1 < D.R.m → ∀ F : (pk W).CC t (j + 1), F.1 ∈ CP (pk W) (lvP W) t (j + 1) → ∀ κ ∈ levS (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)), ∀ φ x g, ((pk W).ioY t j F).1 ((pk W).ItY j φ x) (g * κ) = levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) κ * ((pk W).ioY t j F).1 ((pk W).ItY j φ x) g := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj F hF κ hκ φ x g
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (pk W).Is W.P.A3.A.μ0 := hC.lev
  have hθ : IsInfFam (pk W).θ := hC.models.inf
  have hio := hC.chain.ioY t j (by omega)
  have hκG : κ ∈ GfC (Yc D j) := hκ.1
  have hκP : Lev.finE (Yc D j) κ ∈ parLev D.sp.cm (Yc D j).gram ((pk W).βY j) ((pk W).datYt t j (pk W).triv) := hκ.2.1
  have hκH : rTup ((pk W).βY j) ((pk W).datYt t j (pk W).triv) (Lev.finE (Yc D j) κ) ∈ (lvP W).H := hκ.2.2
  have hκl : IsLevelLift (Yc D j) ((pk W).βY j) ((pk W).datYt t j (pk W).triv)
      (rTup ((pk W).βY j) ((pk W).datYt t j (pk W).triv) (Lev.finE (Yc D j) κ)) κ := ⟨hκG, hκP, rfl⟩
  obtain ⟨κ', hκ'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain (pk W) hL t (j + 1) hj
    (rTup ((pk W).βY j) ((pk W).datYt t j (pk W).triv) (Lev.finE (Yc D j) κ))
  have hj' : j < D.R.m := by omega
  have hlaw := GlobalTheory.StepLaw.step_law (pk W).toLevCh hL t j (j + 1) rfl hj' hθ (D.sp.Y_sig _) (D.sp.Y_sig _) (r_le_Y _) (r_le_Y _)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (GlobalTheory.Chain.VacVec.cart_isCartanInv _) (hL.βY j hj') (hL.βY (j + 1) hj)
    (hC.chain.ωY t j hj) (hC.chain.vY t j hj) _ κ κ' hκl hκ'
  have hsS : levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ' ≠ 0 :=
    levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ)⁻¹ •
      (pk W).ωY t j (κ, κ') ((pk W).vY t j) =
      (levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ')⁻¹ • (pk W).vY t j := hlaw
  have hv : (pk W).ωY t j (κ, κ') ((pk W).vY t j) =
      (levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ *
        (levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ')⁻¹) •
        (pk W).vY t j := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite (pk W).ψ (pk W).θ _ _ _ _ ((pk W).ωY t j) hθ (hC.chain.ωY t j hj)
    _ _ _ _ ((pk W).vY t j) (hC.chain.ptY t j hj) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right (pk W).ψ _ _ _ _ ((pk W).ωY t j) (hC.chain.ωY t j hj)
    ((pk W).ptY t j φ) (hC.chain.ptY t j hj φ)
  have hκ'H : rTup ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (pk W).triv) (Lev.finE (Yc D (j + 1)) κ') ∈ (lvP W).H := by
    rw [hκ'.2.2]; exact hκH
  have hκ'P : κ' ∈ levS (Yc D (j + 1)) ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (lvP W)) := ⟨hκ'.1, hκ'.2.1, hκ'H⟩
  have e1 : levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) κ =
      (((lvP W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := (pk W).datYt t j (pk W).triv) (lvP W), extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hsub : (⟨_, hκ'H⟩ : (lvP W).H) = ⟨_, hκH⟩ := Subtype.ext hκ'.2.2
  have e2 : levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (lvP W)) κ' =
      (((lvP W).chi ⟨_, hκH⟩ : ℂˣ) : ℂ) *
        levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ' := by
    unfold levChi
    erw [levFn_withP (L := (pk W).datYt t (j + 1) (pk W).triv) (lvP W), extendOne_of_mem _ hκ'H, Units.val_mul, hsub]
    rfl
  have hfd : ((pk W).νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) := by
    rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h | h
    · have := hC.models.νY t (j + 1) h
      exact ⟨this.1.1, this.2⟩
    · have e : j + 1 = D.R.m - 1 := by omega
      rw [e]
      have := hC.models.νY' t
      exact ⟨this.1.1, this.2⟩
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Yc D (j + 1))
  have htg : IsTopologicalGroup (GA D (Yc D (j + 1))) := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Yc D (j + 1)).gram))
  haveI := hfd.1
  haveI hR : ((pk W).νY t (j + 1)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') ((pk W).νY t (j + 1)) = (pk W).νY t (j + 1) := map_mul_right_eq_self _ κ'
  have hFv := fun v => GlobalTheory.StepLevelP.IoLevPf.multT_val (pk W).θ ((pk W).MY (j + 1)) _ _ F.1 hF v
  have hpt' : (pk W).ωY t j (κ, κ') ((pk W).ptY t j φ) = (levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ * (levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ')⁻¹) • (pk W).ptY t j φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ (Yc D (j + 1))) ((pk W).νY t (j + 1))
    ((pk W).fdY t (j + 1)) hfd.2 κ' hmap
    (fun h => thetaKO ((pk W).ωY t j) (g * κ) h ((pk W).ptY t j φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D j)).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, (hFv x).1 γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO ((pk W).ωY t j) (g * κ) (h * κ') ((pk W).ptY t j φ) * F.1 x (h * κ') =
      (levChi (Yc D j) ((pk W).βY j) (flagL ((pk W).datYt t j (pk W).triv)) κ * (levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) (flagL ((pk W).datYt t (j + 1) (pk W).triv)) κ')⁻¹ * levChi (Yc D (j + 1)) ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (lvP W)) κ') * (thetaKO ((pk W).ωY t j) g h ((pk W).ptY t j φ) * F.1 x h) := fun h => by
    rw [hth, (hFv x).2 κ' hκ'P]; ring
  rw [← hio.eq F φ x (g * κ), ← hio.eq F φ x g]
  unfold Lift.liftInt
  rw [← hint.2]
  simp only [hpw]
  rw [integral_const_mul, e1, e2]
  field_simp

end GlobalTheory.StepLevelP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharSymplOHConjHalfRest
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfCocycle

variable {D : D7} {S T : HSp D}

theorem comm4 {R : Type} [CommRing R] (c a h H : R) : c * (a * h * H) = c * a * H * h := by ring

theorem split_half {E R : Type} [Field E] [CharZero E] [CommRing R] (f : E →+* R) (x k : R) :
    x * k = x * (k * f ((2 : ℕ) : E)⁻¹) + x * (k * f ((2 : ℕ) : E)⁻¹) := by
  have h : f ((2 : ℕ) : E)⁻¹ * (1 + 1) = 1 := by
    rw [← map_one f, ← map_add, ← map_mul]
    congr 1
    norm_num
  linear_combination (-(x * k)) * h

theorem half_add {F R : Type} [Field F] [CharZero F] [CommRing R] (g : F →+* R) (t : R) :
    g (1 / 2) * (t + t) = t := by
  have h : g (1 / 2) * (1 + 1) = 1 := by
    rw [← map_one g, ← map_add, ← map_mul]
    congr 1
    norm_num
  linear_combination t * h

theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  have h := GlobalTheory.LatVacSign.hO_smul_smul 1 a x y
  rwa [one_smul, one_mul] at h

theorem hO_nsmul_right (n : ℕ) (x y : WO S T) : hO S T x (n • y) = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hO_nsmul_left (n : ℕ) (x y : WO S T) : hO S T (n • x) y = (n : AE D) * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

set_option maxHeartbeats 1000000 in

theorem char_symplOH_conjHalf_rest : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, (2 : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : ℕ), 0 < c → ∀ (Y Z : WO S T), c • Y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → Z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → e • Y = c • (e • Z) → ψ (symplOH S T (cA D e • Y) ((1 - cA D e) • Y)) = 1 := by
  intro D ψ S T ΛS ΛT hψ hS hT e SS he h2 c hc Y Z hY hZ heq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D (cA D e) = e := GlobalTheory.LatVac.cA_cA e
  have hP : ∀ PP ∈ SS, ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP
    rw [Nat.cast_ofNat]
    exact h2 PP hPP
  have hint : finPart D (e * incA D ((2 : ℕ) : D.host.E)⁻¹) ∈ intAE D :=
    GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.DatumFourier.idem_div_int he two_ne_zero hP)
  have hZ' := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint Z hZ
  have hcA2 : cA D (incA D ((2 : ℕ) : D.host.E)⁻¹) = incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    change incA D (star ((2 : ℕ) : D.host.E)⁻¹) = _
    rw [star_inv₀, star_natCast]
  have k1 : hO S T (cA D e • Y) ((1 - cA D e) • Y) = (c : AE D) * cA D e * hO S T Y Z := by
    have a1 := GlobalTheory.LatVacSign.hO_smul_smul (cA D e) (1 - cA D e) Y Y
    have a2 := hO_smul_right e Y Y
    rw [heq, hO_nsmul_right, hO_smul_right] at a2
    rw [a1, map_sub, map_one, hcc]
    have : cA D e * (1 - e) = cA D e := by
      rw [mul_sub, mul_one, mul_comm, hec, sub_zero]
    rw [this, mul_assoc, ← a2]
  have k2 : hO S T (c • Y) ((e * incA D ((2 : ℕ) : D.host.E)⁻¹) • Z) =
      (c : AE D) * cA D e * hO S T Y Z * incA D ((2 : ℕ) : D.host.E)⁻¹ := by
    rw [hO_nsmul_left, hO_smul_right, map_mul, hcA2]
    exact comm4 _ _ _ _
  rw [symplOH, symplO, k1, split_half (incA D) (incA D D.host.xi0) ((c : AE D) * cA D e * hO S T Y Z), map_add,
    half_add (algebraMap D.host.F (AF D.host.F)), ← k2]
  exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hY hZ'

end GlobalTheory.ConjHalfCocycle

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelExistsAdelicLevelTrivialRealLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.AdForm.LevLift

theorem exists_mem_U_finM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) (β : Ch i) (z : (A.K i hi β).lev.U), ∃ w : A.U i β, z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) w.1 := by
  intro B X I _ _ l Z u a Ch A hA i hi β z
  letI := tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
    (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) ((I.rec7 l Z).sp.X i) _ (rankN (I.rec7 l Z) i hi)
  obtain ⟨g, hg⟩ := e.toMulEquiv.surjective ⟨z.1, (((A.K i hi β).lev.U_eq z.1).1 z.2).1⟩
  have hfin : z.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 := by
    rw [← he g]
    have h2 : (e g : GL _ _) = z.1 := congrArg Subtype.val hg
    rw [h2]
  exact ⟨⟨g.1, (hA.U i hi β g.1).2 ⟨g.2, z, hfin⟩⟩, hfin⟩

end GlobalTheory.AdForm.LevLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevels_keep_standardLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  first | exact @GlobalTheory.AdForm.levels_keep_stdLat | exact GlobalTheory.AdForm.levels_keep_stdLat | (intros; apply GlobalTheory.AdForm.levels_keep_stdLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmulMemPerOOfMemHalfBO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfBCMul

theorem cmul_mem_perO_of_mem_halfBO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (c : D.host.E) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  have h1 := GlobalTheory.CommonReps.natsmul_mem_twO _ c (expS SS) (fun _ => 0) (fun Q => by
    unfold expS; split_ifs <;> omega) hy
  rw [GlobalTheory.CommonReps.mem_twO_zero] at h1
  have e : ((c : 𝓞 D.host.E) • y) = (c : D.host.E) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rwa [e] at h1

end GlobalTheory.HalfBCMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjFixedIntegralIsUnitOrIdemSubUnitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjFixed_integral_isUnit_or_idem_sub_unit : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ x ∈ intAt D (· = v), cA D x = x → (∃ y ∈ intAt D (· = v), x * y = ε) ∨ (∃ y ∈ intAt D (· = v), (ε - x) * y = ε) := by
  first | exact @GlobalTheory.IwaFixed.fixed_unit_or | exact GlobalTheory.IwaFixed.fixed_unit_or | (intros; apply GlobalTheory.IwaFixed.fixed_unit_or <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBoundsStatement
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalTheorem_of_fourPointBounds : ∀ (D : D7) (c : Formalism.L2.SG.ThmSOwn.ConcK D) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Γ₁ Γ₂ Γ : ℝ) (u : D.what₂.Word), 29 ≤ C' → 29 ≤ Cl → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 0 ≤ Γ₁ → 0 ≤ Γ₂ → Γ₁ + Γ₂ ≤ Γ → VanishingGramTermsBound c.Y u → CollS c.Y u → (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).genSet) ≤ Γ₁ * ddC c.X c.Y u u → (c.Y.tO u u).pairSum ((c.Y.tO u u).one (c.Y.tO u u).ngSet) ≤ Γ₂ * ddC c.X c.Y u u → SDiagAt D u Γ (1 / 2) := by
  first | exact @GlobalTheory.Core.Diag.sDiagAt_of_points | exact GlobalTheory.Core.Diag.sDiagAt_of_points | (intros; apply GlobalTheory.Core.Diag.sDiagAt_of_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_reps_half_standardHom_mod_nsmul : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u → ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v := by
  first | exact @GlobalTheory.HalfStdFin.exists_reps_half_stdHom | exact GlobalTheory.HalfStdFin.exists_reps_half_stdHom | (intros; apply GlobalTheory.HalfStdFin.exists_reps_half_stdHom <;> assumption)
end

