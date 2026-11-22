import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0485
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSliceLineSumEqIntertwinerImage
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0488
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceAlongLineDatumOverVacuumSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSrcSlice

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem col_mem_SB {n n' : Type} {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (hΨ : Ψ ≠ 0) : a ∈ SB (n → k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Ψ x₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hΨ (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun y : n → k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => fun i => x i (Sum.inr 0)) ?_ (by fun_prop) (fun y => rfl)
  · have e : a = (Ψ x₀)⁻¹ • fun y : n → k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j) := by
      funext y
      show a y = (Ψ x₀)⁻¹ * (Ψ x₀ * a y)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_const
    · exact (continuous_apply i)

theorem sb_of_sbHalf (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {Φ : WO S T → ℂ} (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    (fun x => Φ (HalfInd.wr α β x)) ∈ SB (Matrix n n' k) := by
  classical
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨-, k0, hk0, hinv, hsup⟩ := hΦ
  obtain ⟨hUc, hUo⟩ := HalfInd.compact_open α β hS hT
  set U := {x : Matrix n n' k | HalfInd.wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧
    IsHalf p.e (HalfInd.wr α β x)} with hU
  have hc : ((k0 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hwr : ∀ z : Matrix n n' k, HalfInd.wr α β (((k0 : ℕ) : k) • z) = k0 • HalfInd.wr α β z := by
    intro z
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · refine ⟨{x' | ((k0 : ℕ) : k)⁻¹ • (x' - x) ∈ U}, hUo.preimage (by fun_prop), ?_, fun x' hx' => ?_⟩
    · show ((k0 : ℕ) : k)⁻¹ • (x - x) ∈ U
      rw [sub_self, smul_zero]
      refine ⟨?_, HalfInd.isHalf_wr α β 0⟩
      rw [map_zero]; exact zero_mem _
    · set z := ((k0 : ℕ) : k)⁻¹ • (x' - x) with hz
      have hx'z : x' = x + ((k0 : ℕ) : k) • z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
      show Φ (HalfInd.wr α β x') = Φ (HalfInd.wr α β x)
      rw [hx'z, map_add, hwr]
      exact hinv _ hx'.1 hx'.2 _
  · refine HasCompactSupport.intro (hUc.image (f := fun z => ((k0 : ℕ) : k)⁻¹ • z) (by fun_prop)) fun x hx => ?_
    by_contra h
    have h1 := hsup _ h
    have h2 : ((k0 : ℕ) : k) • x ∈ U := by
      refine ⟨?_, HalfInd.isHalf_wr α β _⟩
      rw [hwr]; exact h1
    exact hx ⟨_, h2, by beta_reduce; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem extFun_wr (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {Φ : WO S T → ℂ} (hΦ : ∀ t, Φ t ≠ 0 → IsHalf p.e t) :
    extFun α β (fun x => Φ (HalfInd.wr α β x)) = Φ := by
  classical
  funext t
  unfold extFun
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    beta_reduce
    rw [HalfInd.wr_rd α β ht]
  · rw [if_neg ht]
    by_contra h
    exact ht (hΦ t (Ne.symm h))

end GlobalTheory.LastSrcSlice

namespace GlobalTheory.LastSrcSlice

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LA : Lat A) (LS : Lat S), IsSelfDualC A LA → IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ y : WO L S, ∃ g, Over ψ α β LA LS g Ψ (fun u => Ξ ((o.resS S).symm (u, y))) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ _ V₀ A L S o ζ _ α α₀ β hsum Ψ a ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
  obtain ⟨hL₁, hL₂, hf₁, hSB, ⟨T, hT⟩, hall⟩ := hΞ
  have hΞT : Ξ = T (extFun α₀ β (tensCol Ψ a)) := hall T hT
  by_cases hΨ0 : Ψ = 0
  ·
    subst hΨ0
    have hext : extFun α₀ β (tensCol (0 : Matrix n n' k → ℂ) a) = 0 := by
      classical
      funext t
      simp [extFun, tensCol]
    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = 0 := by
      rw [hΞT, hext, map_zero]; rfl
    have hheis0 : ∀ (w : WO A S), heisO ψ A S w (0 : WO A S → ℂ) = 0 := by
      intro w; funext x; simp [heisO]
    refine ⟨0, hLA, hLS, ⟨?_, ?_⟩, Submodule.zero_mem _, ⟨0, ?_⟩, fun T' hT' => ?_⟩
    · exact { quasi := fun γ w => by simp
              level := ⟨⊤, isOpen_univ, fun u _ _ => hheis0 u⟩
              cont := continuous_const
              smooth := fun _ _ _ _ _ => by simpa using contDiff_const }
    · exact ⟨fun u _ => hheis0 _, fun _ _ u _ _ => hheis0 u⟩
    · exact ⟨fun Φ _ x _ => by simp [hheis0], fun Φ _ y' _ => by simp [hheis0], by simp⟩
    · rw [hslice]
      have : extFun α β (0 : Matrix n n' k → ℂ) = 0 := by
        classical
        funext t; simp [extFun]
      beta_reduce
      rw [this, map_zero]
  · have haSB : a ∈ SB (n → k) := col_mem_SB hSB hΨ0
    have hΨSB : Ψ ∈ SB (Matrix n n' k) := TensSB.of_tensCol_mem hSB ha
    set r := o.resS S with hr
    set a' := ExtZero.colFun β ζ a with ha'
    set ΛA := latO A S (LA : Set (Fin A.rank → D.host.E)) (LS : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛA
    set Λ₁ := latO V₀ S (L₁ : Set (Fin V₀.rank → D.host.E)) (L₂ : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛ₁
    set T₁ := ExtZero.restrModel r a' T y with hT₁
    set g := T₁ (halfInd p.e ΛA) with hg
    have hbox : ∀ Φ : WO A S → ℂ, (fun t => Φ (r t).1 * a' (r t).2) = o.boxS S Φ a' := fun Φ => rfl

    have hsb : ∀ Φ, IsSBHalf p.e ΛA Φ → IsSBHalf p.e Λ₁ (fun t => Φ (r t).1 * a' (r t).2) := by
      intro Φ hΦ
      have h1 := sb_of_sbHalf p α β hLA hLS hΦ
      have h2 := extFun_wr p α β (Φ := Φ) hΦ.1
      rw [hbox, ← h2, ← GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum]
      exact OverProof.isSBHalf_extFun D k p _ _ V₀ S α₀ β L₁ L₂ hL₁ hL₂ _ (Comm.tensCol_mem h1 haSB)

    have hmodel : IsPlaceModel ψ (symplO A S) (heisO ψ A S) p.e ΛA 1 g T₁ := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * a' (r t).2) =
            fun t => (fun t => Φ (r t).1 * a' (r t).2) (t + r.symm (x, 0)) := by
          funext t
          simp only [map_add, AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
        rw [hfun, hT.trans _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hx), hr, ExtZero.heisO_resS_symm]
        rfl
      · intro Φ hΦ y' hy'
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => ψ (symplO A S t y') * Φ t) (r t).1 * a' (r t).2) =
            fun t => ψ (symplO V₀ S t (r.symm (y', 0))) * (fun t => Φ (r t).1 * a' (r t).2) t := by
          funext t
          rw [hr, ExtZero.symplO_resS_symm, mul_assoc]
        rw [hfun, hT.modul _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hy'), hr, ExtZero.heisO_resS_symm]
        rfl
      · rw [one_smul]

    have hlat : IsLatVac (heisO ψ A S) ΛA g :=
      Rebase.latVac_image D k p ψ hψ A S LA LA LS LS hLA hLS hLA hLS g T₁ hmodel

    have htheta : IsThetaFunO ψ A S g := by
      obtain ⟨ΨA, hΨA, hΨAe⟩ := HalfInd.exists_SB_extFun_eq_halfInd D k p A S n n' α β LA LS hLA hLS
      have hover := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).1
      obtain ⟨F, hF, -⟩ := hover _ (Comm.tensCol_mem hΨA haSB)
      have hFth := ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).2.1 _ _ hF).1
      have hFT : F = T (extFun α₀ β (tensCol ΨA a)) := hF.2.2.2.2.2 T hT
      rw [GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum, hΨAe] at hFT
      have := GlobalTheory.BoxSlice.isThetaFunO_slice_left o hFth y
      rw [hFT] at this
      exact this
    have hvac : Vac ψ A S LA LS (· = p.v) g := ⟨htheta, hlat⟩

    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = T₁ (extFun α β Ψ) := by
      funext u
      rw [ExtZero.restrModel_apply, hΞT, GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' V₀ A L S o ζ α α₀ β hsum]
      rfl
    refine ⟨g, ?_⟩
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hψ A S α β LA LS hLA hLS g hvac).1 Ψ hΨSB
    have hfT₁ : f = T₁ (extFun α β Ψ) := hf.2.2.2.2.2 T₁ hmodel
    rw [hslice, ← hfT₁]
    exact hf

end GlobalTheory.LastSrcSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalTransferWeilPairingInertPlaces
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

noncomputable section

namespace GlobalTheory.ChainOnto

set_option maxHeartbeats 1000000 in

theorem transferOn_inert : GlobalTheory.Hk3.HoweUnram → ∀ D : D7, TransferOn D fun v => ¬ IsSplit (E := D.host.E) v := by
  intro hH D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hbne
  obtain ⟨hS, hT⟩ := hunr w h
  rcases hx with ⟨hs, -⟩ | ⟨hin, c, ϖ, eS, α, hUI, heS, hxS, rfl⟩
  · exact absurd hs hv
  obtain ⟨-, hodd, hch⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).2 hv
  obtain ⟨eT, heT⟩ := hch c heS.1
  have hf0 : (f : WO S T → ℂ) ≠ 0 := fun h0 => hbne (by rw [show f = 0 from Subtype.ext h0]; simp)
  obtain ⟨δ, ψ', M, ρ0, ω, s, hstd, hsf, hωom, hcT, hcS⟩ :=
    GlobalTheory.T.weilDatum_inertPlace_standard_cayley_pair D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hUI heS heT f hf hf0
  have hq0 : (qV D.host.F v : ℂ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  obtain ⟨hvS, hsegS⟩ := GlobalTheory.T.heckeChar_value_inert_place_and_segment D χS S.rank hW.hecS hW.resS v w h hin hS
  obtain ⟨hvT, -⟩ := GlobalTheory.T.heckeChar_value_inert_place_and_segment D χT T.rank hW.hecT hW.resT v w h hin hT
  refine Or.inr ⟨hin, c, ϖ, eT, liftPar (Units.mk0 _ hq0) S.rank T.rank α, hUI, heT, ?_, ?_⟩
  · set α' := liftPar (Units.mk0 _ hq0) S.rank T.rank α
    have e1S : embV S v (eS.symm 1) = 1 := by rw [map_one, map_one]
    have e1T : embV T v (eT.symm 1) = 1 := by rw [map_one, map_one]
    have e0S : embV S v 1 = 1 := map_one _
    have e0T : embV T v 1 = 1 := map_one _
    obtain ⟨RS, hRS⟩ : ∃ RS : Representation ℂ (GU c S.rank) (WO S T → ℂ),
        ∀ g u, RS g u = om (embV S v (eS.symm g), 1) u :=
      ⟨om.comp ((MonoidHom.inl _ _).comp ((embV S v).comp eS.symm.toMonoidHom)), fun _ _ => rfl⟩
    obtain ⟨RT, hRT⟩ : ∃ RT : Representation ℂ (GU c T.rank) (WO S T → ℂ),
        ∀ g u, RT g u = om (1, embV T v (eT.symm g)) u :=
      ⟨om.comp ((MonoidHom.inr _ _).comp ((embV T v).comp eT.symm.toMonoidHom)), fun _ _ => rfl⟩
    obtain ⟨πS, hπS⟩ : ∃ πS : Representation ℂ (GU c S.rank) U, ∀ g (u : U), ((πS g u : U) : WO S T → ℂ) = RS g u :=
      ⟨GlobalTheory.PRep.sub RS U fun g u hu => by rw [hRS, ← e0T]; exact hU _ _ u hu, fun _ _ => rfl⟩
    obtain ⟨πT, hπT⟩ : ∃ πT : Representation ℂ (GU c T.rank) U, ∀ g (u : U), ((πT g u : U) : WO S T → ℂ) = RT g u :=
      ⟨GlobalTheory.PRep.sub RT U fun g u hu => by rw [hRT, ← e0S]; exact hU _ _ u hu, fun _ _ => rfl⟩
    have hMS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = RS g m := fun g m => by
      rw [hRS, hωom, e1T]
    have hMT : ∀ g (m : M), ((ω (1, g) m : M) : WO S T → ℂ) = RT g m := fun g m => by
      rw [hRT, hωom, e1S]
    have hvac := hstd.2.2.1
    have hfixS : ∀ k ∈ KU c S.rank, πS k f = f := fun k hk => by
      have a4 := hstd.1.fix k 1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 (one_mem _) s hvac
      apply Subtype.ext
      rw [hπS, ← hsf, ← hMS]; exact congrArg Subtype.val a4
    have hfixT : ∀ k ∈ KU c T.rank, πT k f = f := fun k hk => by
      have a4 := hstd.1.fix 1 k (one_mem _) (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).2 s hvac
      apply Subtype.ext
      rw [hπT, ← hsf, ← hMT]; exact congrArg Subtype.val a4
    have hcom1 := GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hUI S.rank
    have hcom2 := GlobalTheory.T.inert_unitary_coset_symmetry_hecke_even _ ϖ c _ hUI T.rank
    have hρ1 : ρ 1 x = x := by rw [map_one]; rfl
    have hbT : ∀ g (u : U), b (πT g u) x = ρ' (eT.symm g) (b u x) := fun g u => by
      have e2 := hb 1 (eT.symm g) u x
      have e : πT g u = ⟨om (embV S v 1, embV T v (eT.symm g)) u, hU _ _ u u.2⟩ :=
        Subtype.ext ((hπT g u).trans ((hRT g u).trans (congrArg (fun z => om (z, embV T v (eT.symm g)) (u : WO S T → ℂ)) e0S.symm)))
      rw [hρ1] at e2
      rw [e, e2]
    have hbS : ∀ g (u : U) y, b (πS g u) (ρ (eS.symm g) y) = b u y := fun g u y => by
      have e2 := hb (eS.symm g) 1 u y
      have e : πS g u = ⟨om (embV S v (eS.symm g), embV T v 1) u, hU _ _ u u.2⟩ :=
        Subtype.ext ((hπS g u).trans ((hRS g u).trans (congrArg (fun z => om (embV S v (eS.symm g), z) (u : WO S T → ℂ)) e0T.symm)))
      rw [map_one ρ', Module.End.one_apply] at e2
      rw [e, e2]
    refine ⟨hbne, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h' hh' => ?_⟩
    · show ρ' (eT.symm k) (b f x) = b f x
      rw [← hbT, hfixT k hk]
    · have : CharZero (w.adicCompletion D.host.E) :=
        charZero_of_injective_algebraMap (algebraMap D.host.E (w.adicCompletion D.host.E)).injective
      obtain ⟨h0, hh0, heq⟩ := GlobalTheory.T.unramified_hecke_vacuum_larger_eq_smaller hH _ ϖ c _ δ ψ' S.rank T.rank M ρ0 ω s hstd h' hh'
      have hsat := GlobalTheory.T.satakeTransform_eq_at_thetaLift_of_vacuum_eq _ ϖ c _ δ ψ' S.rank T.rank M ρ0 ω s hstd hcT hcS (by omega) h0 hh0 h' hh' heq
        (Units.mk0 _ hq0) rfl α
      have sA : b (heckeVec πT (KU c T.rank) h' f) x =
          heckeVec (ρ'.comp eT.symm.toMonoidHom) (KU c T.rank) h' (b f x) :=
        map_heckeVec hcom2.1 hh' (b.flip x) (fun g u => hbT g u) f
      have sB : heckeVec πT (KU c T.rank) h' f = heckeVec πS (KU c S.rank) h0 f := by
        apply Subtype.ext
        have m1 := map_heckeVec hcom2.1 hh' U.subtype (ρ' := RT) (fun g u => hπT g u) f
        have m2 := map_heckeVec hcom2.1 hh' M.subtype (ρ := ω.comp (MonoidHom.inr _ _)) (ρ' := RT) (fun g m => hMT g m) s
        have m3 := map_heckeVec hcom1.1 hh0 M.subtype (ρ := ω.comp (MonoidHom.inl _ _)) (ρ' := RS) (fun g m => hMS g m) s
        have m4 := map_heckeVec hcom1.1 hh0 U.subtype (ρ' := RS) (fun g u => hπS g u) f
        simp only [Submodule.subtype_apply] at m1 m2 m3 m4
        rw [m1, m4, ← hsf, ← m2, ← m3, heq]
      have sC := (GlobalTheory.T.hecke_operator_move_across_invariant_bilinear (GU c S.rank) (KU c S.rank) hcom1.1 hcom1.2.1 U X X' πS (ρ.comp eS.symm.toMonoidHom) b
        (fun g u y => hbS g u y) f (GlobalTheory.LGrp.mem_fixed.2 hfixS) x hxS.2.1 h0 hh0).2
      have hev : (fun g => h0 g⁻¹) = h0 := funext fun g => hcom1.2.2 h0 hh0 g
      rw [← sA, sB, sC, hev, hxS.2.2 h0 hh0, map_smul, hsat]
  · have hc := GlobalTheory.T.baseChange_thetaLiftSatakeParameter_eq_add_segment (Units.mk0 _ hq0) S.rank T.rank (by omega) α
    have ht' : ((T.rank : ℤ) - S.rank) = (t : ℤ) := by omega
    rw [ht'] at hc
    have e := congrArg (Multiset.map (((-1 : ℂˣ) ^ S.rank) * ·)) hc
    simp only [Multiset.map_map, Multiset.map_add, Function.comp_def, mul_inv_cancel_left] at e
    rw [Multiset.map_id'] at e
    rw [e, stepPar, hvS, hvT, hsegS (Units.mk0 _ hq0) _ t rfl]
    congr 1
    · exact Multiset.map_congr rfl fun y _ => by group

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCombinationExtendByZeroOrthSumLine
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem ext_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → β.IsLat LT ΛT → (∀ (Ψ : Matrix n n' k → ℂ) (c : WO A T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ A T LA LT (· = p.v) f₀ → Over ψ α β LA LT f₀ Ψ (comb ψ A T c f₀)) → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α₀ β LS LT f₀ (tensCol Ψ (vecInd ΛT)) (comb ψ S T (extS o T c) f₀)) ∧ ∀ (Ψ : Matrix n' n k → ℂ) (c : WO T A →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ T A LT LA (· = p.v) f₀ → Over ψ β α LT LA f₀ Ψ (comb ψ T A c f₀)) → ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → Over ψ β α₀ LT LS f₀ (tensRow Ψ (dualInd ΛT)) (comb ψ T S (extT o T c) f₀) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ hU S A L T o ζ hζ α α₀ β hsum LA LS LT ΛA ΛT hA hS hT hαA hα₀ hβ
  obtain ⟨ΛT', hΛT', hβ', -⟩ := (GlobalTheory.FrameAt.frame_facts D k p T n β).2.2.2.1 LT hT
  have hΛeq : ΛT' = ΛT := Submodule.ext fun x => (hβ' x).trans (hβ x).symm
  haveI : ΛT.IsLattice k := hΛeq ▸ hΛT'
  have sdA := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ A T LA LT hA hT (· = p.v)
  have sdS := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ S T LS LT hS hT (· = p.v)
  have sdA' := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ T A LT LA hT hA (· = p.v)
  have sdS' := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ T S LT LS hT hS (· = p.v)
  have facS : halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) =
      o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (colFun β ζ (vecInd ΛT)) := by
    rw [← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n (n' ⊕ Fin 1) S T α₀ β LS LT hS hT hU _ _ hα₀ hβ,
      ← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n n' A T α β LA LT hA hT hU _ _ hαA hβ, latInd_lastKer,
      GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' S A L T o ζ α α₀ β hsum]
  have facT : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) =
      o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (rowFun β ζ (dualInd ΛT)) := by
    rw [← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p (n' ⊕ Fin 1) n T S β α₀ LT LS hT hS hU _ _ hβ hα₀,
      ← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n' n T A β α LT LA hT hA hU _ _ hβ hαA, latInd_lastKer_row,
      GlobalTheory.T.extendByZero_target_tensor_row_product D k p n n' S A L T o ζ hζ α α₀ β hsum]
  have latS := GlobalTheory.T.extendByZero_mem_completed_lattice_source D k p n ψ S A L T o ζ β LA LS LT ΛT sdA sdS facS
  have latT := GlobalTheory.T.extension_by_zero_maps_completed_hom_lattice D k p n ψ S A L T o ζ β LA LS LT ΛT sdA' sdS' facT
  have vacS : ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → ∀ y,
      Vac ψ A T LA LT (· = p.v) (fun w => f₀ ((o.resS T).symm (w, y))) := by
    intro f₀ hf y
    refine ⟨GlobalTheory.T.isThetaFunO_source_slice D ψ S A L T o f₀ y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · funext w
      rw [← heisO_resS_symm ψ o (2 • u) f₀ w y]
      have h2 : (o.resS T).symm (2 • u, 0) = 2 • (o.resS T).symm (u, 0) := by
        rw [← map_nsmul]; simp
      rw [h2, hf.2.1 _ (latS u hu)]
    · funext w
      rw [← heisO_resS_symm ψ o u f₀ w y, hf.2.2 e' he' _ (latS u hu) (half_resS_symm o hh)]
  have vacT : ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → ∀ y,
      Vac ψ T A LT LA (· = p.v) (fun w => f₀ ((o.resT T).symm (w, y))) := by
    intro f₀ hf y
    refine ⟨GlobalTheory.T.isThetaFunO_target_slice_orthogonal_sum D ψ S A L T o f₀ y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · funext w
      rw [← heisO_resT_symm ψ o (2 • u) f₀ w y]
      have h2 : (o.resT T).symm (2 • u, 0) = 2 • (o.resT T).symm (u, 0) := by
        rw [← map_nsmul]; simp
      rw [h2, hf.2.1 _ (latT u hu)]
    · funext w
      rw [← heisO_resT_symm ψ o u f₀ w y, hf.2.2 e' he' _ (latT u hu) (half_resT_symm o hh)]
  refine ⟨fun Ψ c _ hyp f₀ hf₀ => ?_, fun Ψ c _ hyp f₀ hf₀ => ?_⟩
  · have hΨ : Ψ ∈ SB (Matrix n n' k) := (hyp _ (vacS f₀ hf₀ 0)).2.2.2.1
    have hΨ' : tensCol Ψ (vecInd ΛT) ∈ SB (Matrix n (n' ⊕ Fin 1) k) :=
      GlobalTheory.FinPl.Comm.tensCol_mem hΨ (GlobalTheory.FinPl.Comm.vecInd_mem ΛT)
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ S T α₀ β LS LT hS hT f₀ hf₀).1 _ hΨ'
    refine ⟨hS, hT, hf₀, hΨ', hf.2.2.2.2.1, fun T' hT' => ?_⟩
    funext t
    obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resS T).symm q = t := ⟨_, (o.resS T).symm_apply_apply t⟩
    have hmod := GlobalTheory.T.schroedinger_intertwiner_slice_restriction_placeModel D ψ (symplO S T) (heisO ψ S T) (symplO A T) (heisO ψ A T) (o.resS T) p.e _ _
      (colFun β ζ (vecInd ΛT)) f₀ T' hT' (fun a F w y => heisO_resS_symm ψ o a F w y)
      (fun t a => symplO_resS_symm o t a) (fun a ha => half_resS_symm o ha) (fun a ha => half_resS_symm o ha)
      (GlobalTheory.T.isSchwartzBruhatHalf_source_box_lattice D k p n S A L T o ζ β LA LS LT ΛT facS) facS y
    have key := congrFun ((hyp _ (vacS f₀ hf₀ y)).2.2.2.2.2 _ hmod) w
    rw [GlobalTheory.T.heisenbergCombination_extendByZero_source_slice] at key
    rw [key, restrModel_apply, GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' S A L T o ζ α α₀ β hsum]
    rfl
  · have hΨ : Ψ ∈ SB (Matrix n' n k) := (hyp _ (vacT f₀ hf₀ 0)).2.2.2.1
    have hΨ' : tensRow Ψ (dualInd ΛT) ∈ SB (Matrix (n' ⊕ Fin 1) n k) :=
      GlobalTheory.FinPl.Comm.tensRow_mem hΨ (GlobalTheory.FinPl.Comm.dualInd_mem ΛT)
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p (n' ⊕ Fin 1) n ψ hψ T S β α₀ LT LS hT hS f₀ hf₀).1 _ hΨ'
    refine ⟨hT, hS, hf₀, hΨ', hf.2.2.2.2.1, fun T' hT' => ?_⟩
    funext t
    obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resT T).symm q = t := ⟨_, (o.resT T).symm_apply_apply t⟩
    have hmod := GlobalTheory.T.schroedinger_intertwiner_slice_restriction_placeModel D ψ (symplO T S) (heisO ψ T S) (symplO T A) (heisO ψ T A) (o.resT T) p.e _ _
      (rowFun β ζ (dualInd ΛT)) f₀ T' hT' (fun a F w y => heisO_resT_symm ψ o a F w y)
      (fun t a => symplO_resT_symm o t a) (fun a ha => half_resT_symm o ha) (fun a ha => half_resT_symm o ha)
      (GlobalTheory.T.isSchwartzBruhatHalf_target_box_dualIndicator D k p n S A L T o ζ β LA LS LT ΛT facT) facT y
    have key := congrFun ((hyp _ (vacT f₀ hf₀ y)).2.2.2.2.2 _ hmod) w
    rw [GlobalTheory.T.heisenbergCombination_extendByZero_target_slice] at key
    rw [key, restrModel_apply, GlobalTheory.T.extendByZero_target_tensor_row_product D k p n n' S A L T o ζ hζ α α₀ β hsum]
    rfl

end GlobalTheory.FinPl.ExtZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterEqAddCharSuperdiagSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelCharacter_eq_addChar_superdiagSum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (x : S.P.J) (M : Matrix (Fin κ) (Fin κ) k), (∀ a b, valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inl a) (Sum.inl b) - M a b) < 1) → (∀ i j : Fin (s + 1), j.val = i.val + 1 → valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val (Sum.inr i) (Sum.inr j)) < 1) → ((S.P.lam x : ℂˣ) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * ∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then M a b else 0) : ℂ) := by
  first | exact @GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near | exact GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near | (intros; apply GlobalTheory.SymChain.SymData.lam_eq_psi_superSum_of_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem thetaKO_eq_tsum_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g h, thetaKO omh g h f = ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, sch ψ A B ν 𝓨 (omh (g, 1) f) (mt B h⁻¹ ⬝ (rat ξ : Mx D B.rank A.rank)) := by
  intro D ψ A B χB omh hW ν 𝓨 hν f hf g h
  have hF := hW.om_pres (g, 1) f hf
  have hG := hW.om_pres (1, h) _ hF
  have e : omh (g, h) f = omh (1, h) (omh (g, 1) f) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  have hs := (GlobalTheory.HeisMixSource.heis_mixS D ψ hW.std (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ _ hG).2.2.2.2 0
  rw [map_zero] at hs
  have hl := (GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ A B χB omh hW ν 𝓨 hν _ hF).1 h
  unfold thetaKO
  rw [e, ← hs.tsum_eq]
  exact tsum_congr fun ξ => hl (rat ξ)

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSliceLineSumEqIntertwinerImageStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSlice_lineSum_eq_intertwiner_image : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LS : Lat S), IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ u : WO A S, ∃ (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ ∧ IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ ∧ T₁ (colFun β ζ a) = fun y => Ξ ((o.resS S).symm (u, y)) := by
  first | exact @GlobalTheory.LastTgtSlice.main | exact GlobalTheory.LastTgtSlice.main | (intros; apply GlobalTheory.LastTgtSlice.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_local_bound : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ t (J : QJ a t), J.Reads → ∀ i, MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i) := by
  first | exact @GlobalTheory.QTw.JoinFrames.movedAt | exact GlobalTheory.QTw.JoinFrames.movedAt | (intros; apply GlobalTheory.QTw.JoinFrames.movedAt <;> assumption)
end

