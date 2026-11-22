import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0503
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCombinationRebaseVacuumLatticesInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacRebase

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem zero_placeModel {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 0 0 := by
  refine ⟨fun _ _ _ _ => ?_, fun _ _ _ _ => ?_, ?_⟩
  · funext w; simp [heisO]
  · funext w; simp [heisO]
  · simp

theorem local_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (p : GlobalTheory.FinPl.Pl D)
    (hsp : ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (hu1 : ∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧
      incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p))
    (hu2 : ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) :
    ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧ (f ≠ 0 → comb ψ S T c f ≠ 0) := by
  obtain ⟨e, ε, he, hε, hs⟩ := hsp
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D p e ε he hε hs
  have hU : q.UnitAA := by
    unfold GlobalTheory.FinPl.SplitPt.UnitAA
    rw [hq]
    exact ⟨hu1, hu2⟩
  rw [← hq]
  obtain ⟨glS, hS1, hS2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D _ q S (Fin S.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  obtain ⟨glT, hT1, hT2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D _ q T (Fin T.rank) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1)
  let α : GlobalTheory.FinPl.Frame q S (Fin S.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glS, hS1, hS2⟩
  let β : GlobalTheory.FinPl.Frame q T (Fin T.rank) := ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, glT, hT1, hT2⟩
  obtain ⟨ΛS, hl1, hαN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α N hN
  obtain ⟨ΛT, hl2, hβN, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β N' hN'
  obtain ⟨ΛSm, hl3, hαM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q S _ α M hM
  obtain ⟨ΛTm, hl4, hβM, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D _ q T _ β M' hM'
  haveI := hl1
  haveI := hl2
  haveI := hl3
  haveI := hl4
  have R := GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D _ q (Fin T.rank) (Fin S.rank) ψ hψ hU S T α β M N M' N' hM hM' hN hN'
  obtain ⟨c, hc, hov⟩ := R.2 (GlobalTheory.LatPair.latInd ΛS ΛT) (GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT)
  refine ⟨c, hc, fun f hf => ?_⟩
  have hO := hov f hf
  have h1 := R.1 ΛS ΛT hαN hβN f _ hO
  refine ⟨h1.1, fun hf0 hg => hf0 ?_⟩
  obtain ⟨⟨Tm, hTm⟩, -⟩ := hO.2.2.2.2
  have hOf : GlobalTheory.FinPl.Over ψ α β M M' f (GlobalTheory.LatPair.latInd ΛSm ΛTm) f := by
    refine ⟨hM, hM', hf, GlobalTheory.LatPair.latInd_mem_SB _ _, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
    rw [GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd D _ q _ _ S T α β M M' hM hM' hU ΛSm ΛTm hαM hβM]
    have hv := hT'.vac
    rw [one_smul] at hv
    exact hv.symm
  have hN0 := h1.2 _ _ hOf
  rw [hg] at hN0
  have := hN0.2.2.2.2.2 0 (zero_placeModel ψ S T _ _)
  simpa using this

end GlobalTheory.VacRebase

namespace GlobalTheory.VacRebase

theorem idAt_mono' {D : D7} {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → P' v) :
    GlobalTheory.FinPl.idAt D P ≤ GlobalTheory.FinPl.idAt D P' := by
  unfold GlobalTheory.FinPl.idAt
  exact inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hp => w.2 (h _ hp)⟩ le_rfl)

theorem foldr_vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) (X : GlobalTheory.FinPl.Pl D → Prop) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p)) → (∀ p ∈ l, ¬ X p) → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T LS LT X f → GlobalTheory.FinPl.Vac ψ S T LS LT X (l.foldr (fun p g => comb ψ S T (c p) g) f) := by
  intro l
  induction l with
  | nil => intro _ _ f hf; exact hf
  | cons p l ih =>
    intro hc hX f hf
    rw [List.foldr_cons]
    have hd : ∀ x, x = p → ¬ X x := fun x hx => hx ▸ hX p List.mem_cons_self
    exact ((GlobalTheory.DisjComb.main D ψ hψ S T (· = p) X hd).2.1 (c p) (hc p List.mem_cons_self)).2 LS LT _
      (ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) (fun x hx => hX x (List.mem_cons_of_mem _ hx)) f hf)

theorem foldr_vac_on {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M N : GlobalTheory.FinPl.Lat S} {M' N' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hN : IsSelfDualC S N)
    (hM' : IsSelfDualC T M') (hN' : IsSelfDualC T N') (c : GlobalTheory.FinPl.Pl D → WO S T →₀ ℂ) :
    ∀ l : List (GlobalTheory.FinPl.Pl D), l.Nodup → (∀ p ∈ l, GlobalTheory.FinPl.CombAt (· = p) (c p) ∧ ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T (c p) f) ∧
        (f ≠ 0 → comb ψ S T (c p) f ≠ 0)) → ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (· ∈ l) f →
      GlobalTheory.FinPl.Vac ψ S T N N' (· ∈ l) (l.foldr (fun p g => comb ψ S T (c p) g) f) ∧
        (f ≠ 0 → l.foldr (fun p g => comb ψ S T (c p) g) f ≠ 0) := by
  intro l
  induction l with
  | nil =>
    intro _ _ f hf
    refine ⟨⟨hf.1, ?_⟩, fun h => h⟩
    rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ (fun x hx => absurd hx List.not_mem_nil)]
    exact hf.2
  | cons p l ih =>
    intro hnd hc f hf
    have hpl : p ∉ l := (List.nodup_cons.1 hnd).1
    have hd : ∀ x, x = p → ¬ x ∈ l := fun x hx => hx ▸ hpl
    have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· = p) (· ∈ l) hd
    have hfun : (fun x => x ∈ p :: l) = fun x => x = p ∨ x ∈ l := by
      funext x; exact propext List.mem_cons
    rw [hfun] at hf ⊢
    have hf2 := (DC.2.2.2.2 M M' f hM hM').1 hf
    obtain ⟨ihv, ihn⟩ := ih (List.nodup_cons.1 hnd).2 (fun x hx => hc x (List.mem_cons_of_mem _ hx)) f hf2.2
    have hgp := foldr_vac_off hψ c (· = p) M M' l (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).1)
      (fun x hx hxp => hpl (hxp ▸ hx)) f hf2.1
    obtain ⟨hcp, hloc⟩ := hc p List.mem_cons_self
    obtain ⟨hv1, hn1⟩ := hloc _ hgp
    rw [List.foldr_cons]
    refine ⟨(DC.2.2.2.2 N N' _ hN hN').2 ⟨hv1, (DC.2.1 (c p) hcp).2 N N' _ ihv⟩, fun h0 => hn1 (ihn h0)⟩

end GlobalTheory.VacRebase

theorem GlobalTheory.VacRebase.rebase_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M N : GlobalTheory.FinPl.Lat S) (M' N' : GlobalTheory.FinPl.Lat T) (Q : Finset (GlobalTheory.FinPl.Pl D)), IsSelfDualC S M → IsSelfDualC S N → IsSelfDualC T M' → IsSelfDualC T N' → (∀ p ∈ Q, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p))) → (∀ p, p ∉ Q → GlobalTheory.FinPl.latV S M (· = p) = GlobalTheory.FinPl.latV S N (· = p) ∧ GlobalTheory.FinPl.latV T M' (· = p) = GlobalTheory.FinPl.latV T N' (· = p)) → ∃ o : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ Q) o ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) f → GlobalTheory.FinPl.Vac ψ S T N N' (fun _ => True) (comb ψ S T o f) ∧ (f ≠ 0 → comb ψ S T o f ≠ 0) := by
  intro D ψ hψ S T M N M' N' Q hM hN hM' hN' hQ hoff
  have hc : ∀ p : GlobalTheory.FinPl.Pl D, ∃ c : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (· = p) c ∧ (p ∈ Q → ∀ f,
      GlobalTheory.FinPl.Vac ψ S T M M' (· = p) f → GlobalTheory.FinPl.Vac ψ S T N N' (· = p) (comb ψ S T c f) ∧
        (f ≠ 0 → comb ψ S T c f ≠ 0)) := by
    intro p
    by_cases hp : p ∈ Q
    · obtain ⟨h1, h2, h3⟩ := hQ p hp
      obtain ⟨c, hc1, hc2⟩ := GlobalTheory.VacRebase.local_step hψ hM hN hM' hN' p h1 h2 h3
      exact ⟨c, hc1, fun _ => hc2⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hp⟩
  choose c hc1 hc2 using hc
  let l := Q.toList
  have hmem : ∀ p, p ∈ l ↔ p ∈ Q := fun p => Finset.mem_toList
  refine ⟨convList ψ S T (l.map c), ?_, fun f hf => ?_⟩
  · refine support_convList (p := GlobalTheory.FinPl.MxAt (· ∈ Q)) (fun i j => Ideal.zero_mem _)
      (fun x y hx hy i j => by rw [Matrix.add_apply]; exact Ideal.add_mem _ (hx i j) (hy i j)) ?_
    intro c' hc' x hx i j
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc'
    exact GlobalTheory.VacRebase.idAt_mono' (fun v hv => hv ▸ (hmem p).1 hp) (hc1 p x hx i j)
  rw [comb_convList]
  have DC := GlobalTheory.DisjComb.main D ψ hψ S T (· ∈ l) (· ∉ l) (fun x h1 h2 => h2 h1)
  have hfun : (fun x => x ∈ l ∨ x ∉ l) = fun _ => True := by
    funext x; exact propext ⟨fun _ => trivial, fun _ => em _⟩
  have hf' : GlobalTheory.FinPl.Vac ψ S T M M' (fun x => x ∈ l ∨ x ∉ l) f := by rw [hfun]; exact hf
  obtain ⟨hin, hout⟩ := (DC.2.2.2.2 M M' f hM hM').1 hf'
  obtain ⟨v1, n1⟩ := GlobalTheory.VacRebase.foldr_vac_on hψ hM hN hM' hN' c l (Finset.nodup_toList Q)
    (fun p hp => ⟨hc1 p, hc2 p ((hmem p).1 hp)⟩) f hin
  have hout' : GlobalTheory.FinPl.Vac ψ S T N N' (· ∉ l) f := by
    refine ⟨hout.1, ?_⟩
    rw [GlobalTheory.T.homLatticeAtPlaces_congr_localLattices D S T N M N' M' hN hM hN' hM' _ (fun x hx => by
      obtain ⟨a, b⟩ := hoff x (fun h => hx ((hmem x).2 h)); exact ⟨a.symm, b.symm⟩)]
    exact hout.2
  have v2 := GlobalTheory.VacRebase.foldr_vac_off hψ c (· ∉ l) N N' l (fun p _ => hc1 p) (fun p hp h => h hp) f hout'
  refine ⟨?_, n1⟩
  rw [← hfun]
  exact (DC.2.2.2.2 N N' _ hN hN').2 ⟨v1, v2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGaussIndicator
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Inhab

theorem exists_gauss_indicator (D : D7) (θ : InfFam D) (A B : HSp D) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin B.rank) (Fin B.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D B τ) (s τ)) :
    ∃ Φ : schwartzA θ B.rank A.rank, Φ.1 ∈ fockA θ B A.rank l s ∧ Φ.1 0 ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := GlobalTheory.T.gaussian_is_schwartz_function D A.rank B l hl s hs
  let W : AddSubgroup (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ intAE D}
      add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (intAE D).zero_mem
      neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin B.rank → Fin A.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin B.rank) (Fin A.rank) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin B.rank → Fin A.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let φ : Mx D B.rank A.rank → ℂ := fun x =>
    f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
  have hφ : φ ∈ schwartzA θ B.rank A.rank := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨⟨φ, hφ⟩, ?_, ?_⟩
  · refine Submodule.subset_span ⟨1, g, hg, ?_⟩
    funext x
    simp only [φ, hf, evalPoly, map_one, one_mul]
    rfl
  · show f _ * g _ ≠ 0
    rw [hf]
    simp [g, gauss, compAt]
    exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin B.rank) (Fin A.rank) _)).2 W.zero_mem

theorem hypotheses_inhabited : ∀ (D : D7) (A B : HSp D), ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (m : Measure (Mx D B.rank A.rank)) (𝓕 : Set (Mx D B.rank A.rank)) (omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)) (H : G D A.rank → ℝ≥0) (l : D.what₂.Tau → ℝ) (s : RealMat B) (Φ : schwartzA θ B.rank A.rank), IsCharAF D.host.F ψ ∧ IsHeckeChar D χ ∧ ResEta D χ B.rank ∧ IsInfFam θ ∧ IsCovolOne (ratMx D B.rank A.rank) m 𝓕 ∧ IsWeilSch ψ χ θ B m omS ∧ IsHeight H ∧ HasRealPar ψ θ l ∧ (∀ τ, IsCartanInv (gramAt D B τ) (s τ)) ∧ Φ.1 ∈ fockA θ B A.rank l s ∧ Φ.1 0 ≠ 0 := by
  intro D A B
  obtain ⟨-, ψ₀, χB, omh, -, ν, 𝓨, -, hω, -, -, hν⟩ :=
    GlobalTheory.SiegelFormula.Model.data_exist GlobalTheory.weilRepresentationUnitaryPair A B
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  obtain ⟨μ, hμ, hp⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨a, ha⟩ := exists_isMaj A
  obtain ⟨p, hpc⟩ := hp A a ha κ hκ
  obtain ⟨omS, hT⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ₀ A B χB omh hω ν 𝓨 hν θ hθ κ
  obtain ⟨lam, hlam, hψ, l, hl, hla⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hω.std θ hθ μ hμ
  obtain ⟨hχ1, hχ2⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χB B.rank hω.hecT hω.resT
  have hc : ∀ τ, ∃ s, IsCartanInv (gramAt D B τ) s := fun τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm B τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit B τ)
  choose s hs using hc
  have hl0 : ∀ τ, l τ ≠ 0 := fun τ h => by
    have e := hla τ
    rw [h, abs_zero] at e
    have h1 : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    have h2 : tauE D τ μ ≠ 0 := (map_ne_zero _).2 hμ.1
    exact div_ne_zero (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2) e.symm
  obtain ⟨Φ, hΦ, hΦ0⟩ := exists_gauss_indicator D θ A B l hl0 s hs
  refine ⟨shift ψ₀ lam, χB⁻¹, θ, ν, 𝓨, omS, hgtStd A a κ p, l, s, Φ, hψ, hχ1, hχ2, hθ, hν, ⟨?_, ?_, ?_⟩,
    GlobalTheory.T.standardUnitaryHeight_isSiegelHeightFunction D A μ hμ κ hκ a p hpc, hl, hs, hΦ, hΦ0⟩
  · exact GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ₀ A B χB omh hω ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam
  · exact GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ₀ A B χB omh hω ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam
  · exact GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ₀ A B χB omh hω ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam

end GlobalTheory.StdUnn.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPrimeMemPl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoPlace

theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : A) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : A) ∈ P :=
  _root_.GlobalTheory.ExistsPrimeMem.exists_prime_mem P hP n hn h

theorem exists_prime_mem_pl {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ PP.asIdeal :=
  exists_prime_mem PP.asIdeal PP.isPrime _ (fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _)

end GlobalTheory.XGeoPlace

theorem GlobalTheory.XGeoPlace.exists_place : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (PP : Pl (I.rec7 l Z).host.E), PP ∈ (pk W).Pg ∨ QAll W PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (_ : MeasurableSpace k) (_ : BorelSpace k) (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP ∧ q.v = PP.under (𝓞 (I.rec7 l Z).host.F) ∧ q.UnitAA ∧ valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u PP hPP
  have hC := hW.pk.bot.hyp.2.2.2.1

  have hnc : ¬ Lev.IsConjPl PP PP := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact GlobalTheory.SeeConjPlaces.pg_not_isConjPl (pk W) W.Q.F.lv2 hC.lev hC.grp PP hg PP hg
    · exact (hC.lev.Q_pl t PP ht).2 PP ht
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hnc
  obtain ⟨k, _, _, _, _, q, hqe, hqv, hint, -⟩ := GlobalTheory.LocMod.SplitCompl.exists_place _ PP e he

  obtain ⟨ℓ, hℓ, hℓP, h2q, hd⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal ∧
      (B.host.QS * B.host.q).Coprime ℓ ∧ B.host.d.Coprime ℓ := by
    rcases hPP with hg | ⟨t, ht⟩
    · have hgg := hW.lev.1.1 PP hg
      rw [Nat.cast_mul] at hgg
      obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((B.host.g i : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rcases PP.isPrime.mem_or_mem hgg with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      have hc : (B.host.g i).Coprime (B.host.QS * B.host.q * B.host.d) := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, B.g_cond i, Nat.gcd_one_left]
      refine ⟨B.host.g i, B.host.g_prime i, hi, (hc.coprime_dvd_right ⟨B.host.d, rfl⟩).symm,
        (hc.coprime_dvd_right (Dvd.intro_left _ rfl)).symm⟩
    · have hoff := (hC.lev.Q_off t PP ht).1
      obtain ⟨ℓ, hℓ, hℓP⟩ := GlobalTheory.XGeoPlace.exists_prime_mem_pl PP
      have key : ∀ m : ℕ, m ∣ B.host.QS * B.host.q * B.host.d * (I.rec7 l Z).sp.T → m.Coprime ℓ := fun m hm =>
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hdv =>
          hoff (Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (hdv.trans hm)) hℓP))
      exact ⟨ℓ, hℓ, hℓP, key _ ⟨B.host.d * (I.rec7 l Z).sp.T, by ring⟩, key _ ⟨B.host.QS * B.host.q * (I.rec7 l Z).sp.T, by ring⟩⟩
  have hv : (ℓ : 𝓞 (I.rec7 l Z).host.F) ∈ q.v.asIdeal := by
    rw [hqv, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
    exact hℓP
  have hcc : (Ideal.absNorm (I.rec7 l Z).host.ccK).Coprime ℓ := by
    show Nat.Coprime (Ideal.absNorm B.host.ccK) _
    rw [B.ccK_top, Ideal.absNorm_top]
    exact Nat.coprime_one_left _
  have hU : q.UnitAA := GlobalTheory.SeeSaw.StdOff.unitAA_of q hℓ hv h2q hd hcc

  have hT : (((B.T u : ℕ)) : 𝓞 (I.rec7 l Z).host.E) ∉ PP.asIdeal := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact Formalism.L2.Col.T_notMem_vGs l.pr u ⟨PP, (hW.lev.2.1 PP).1 hg⟩
    · exact (hC.lev.Q_off t PP ht).2 u
  set π : 𝓞 (I.rec7 l Z).host.E := X.piT u with hπdef
  have hπ : π ∉ PP.asIdeal := fun h => hT (by
    have h2 := PP.asIdeal.mul_mem_left (B.fields.conjO ((B.primes X).piT u)) h
    have h3 : (B.primes X).piT u * B.fields.conjO ((B.primes X).piT u) ∈ PP.asIdeal := by
      rw [mul_comm]
      exact h2
    rw [l.pr.piT_norm u] at h3
    exact h3)
  have hπ0 : (π : (I.rec7 l Z).host.E) ≠ 0 := fun h0 => hπ (by
    rw [show π = 0 from RingOfIntegers.coe_injective (by simpa using h0)]
    exact zero_mem _)
  have e1 : (GlobalTheory.XGeoStd.piE I l Z u) = (π : (I.rec7 l Z).host.E) := rfl
  have hin1 := (hint (π : (I.rec7 l Z).host.E)).2 ⟨π, 1, fun h => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hin2 := (hint (π : (I.rec7 l Z).host.E)⁻¹).2 ⟨1, π, hπ, by simp [hπ0]⟩
  have hinv : (GlobalTheory.LocMod.ofSplit q).pr ((π : (I.rec7 l Z).host.E)⁻¹) = ((GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E))⁻¹ := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _ = (((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _)⁻¹
    exact map_inv₀ _ _
  have hne : (GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E) ≠ 0 := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) (π : (I.rec7 l Z).host.E) ≠ 0
    exact (map_ne_zero _).2 hπ0
  rw [hinv] at hin2
  rw [Valuation.mem_integer_iff] at hin1 hin2
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, borel k, @BorelSpace.mk _ _ (borel k) rfl, q, hqe ▸ he, hqv, hU, ?_⟩
  rw [e1]
  rw [map_inv₀] at hin2
  exact le_antisymm hin1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hne))).1 hin2)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StMoves

variable {D : D7}

set_option maxHeartbeats 1600000 in

theorem mem_latV_iff_latLoc (V : HSp D) (L : Lat V) (hL : L.FG) (v : Pl D) (y : Fin V.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ GlobalTheory.FinPl.latV V L (· = v) ↔
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v := by
  rw [GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ y hy, GlobalTheory.AdelicU.mem_latHat_iff hL]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases e : w = v
  · subst e; exact h
  · have h0 : GlobalTheory.AdelicU.vecLoc w (finPart D ∘ y) = 0 :=
      funext fun i => ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).1 (hy i)).2 w e
    rw [h0]; exact zero_mem _

theorem exists_supp_vecLoc_eq {n : ℕ} (v : Pl D) (z : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) :
    ∃ y : Fin n → AE D, (∀ i, y i ∈ idAt D (· = v)) ∧ GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) = z := by
  choose lift hl1 hl2 using GlobalTheory.KStabBridge.exists_fin_lift (D := D)
  let y' : Fin n → Af D.host.F ⊗[D.host.F] D.host.E := fun i =>
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have h1 : GlobalTheory.AdelicU.vecLoc v y' = z :=
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have h2 : ∀ u, u ≠ v → GlobalTheory.AdelicU.vecLoc u y' = 0 := fun u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have h3 : finPart D ∘ (fun i => lift (y' i)) = y' := funext fun i => hl2 _
  refine ⟨fun i => lift (y' i), fun i => (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).2 ⟨hl1 _, fun w hw => ?_⟩, by rw [h3, h1]⟩
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (lift (y' i))) = 0
  rw [hl2]
  exact congrFun (h2 w hw) i

set_option maxHeartbeats 1600000 in

theorem moves_iff_stabLoc (V : HSp D) (L : Lat V) (hL : L.FG) (v : Pl D) (g : GA D V) :
    Moves V g L L (· = v) ↔
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram L v := by
  have key : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
      (mt V g *ᵥ y ∈ GlobalTheory.FinPl.latV V L (· = v) ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 *ᵥ
          GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v) := fun y hy => by
    rw [mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ g hy), GlobalTheory.FinPl.KOpen.fin_mulVec]
    exact iff_of_eq (congrArg (· ∈ GlobalTheory.AdelicU.latLoc D.host.F L v)
      (GlobalTheory.AdelicU.vecLoc_mulVec D.sp.cm.sig V.gram v g _))
  refine Iff.trans ⟨fun h z => ?_, fun h y hy => ?_⟩ GlobalTheory.AdelicU.mem_stabLoc.symm
  · obtain ⟨y, hy, rfl⟩ := exists_supp_vecLoc_eq v z
    exact (mem_latV_iff_latLoc V L hL v y hy).symm.trans ((h y hy).trans (key y hy))
  · exact (mem_latV_iff_latLoc V L hL v y hy).trans ((h _).trans (key y hy).symm)

theorem moves_mul {V : HSp D} {g h : GA D V} {L M N : Lat V} {P : Pl D → Prop} (hg : Moves V g L M P)
    (hh : Moves V h M N P) : Moves V (h * g) L N P := by
  intro y hy
  rw [hg y hy, hh _ (GlobalTheory.FinPl.KOpen.supp_mulVec V P g hy)]
  show _ ↔ mt V (h * g) *ᵥ y ∈ _
  rw [show mt V (h * g) = mt V h * mt V g from rfl, Matrix.mulVec_mulVec]

theorem moves_inv {V : HSp D} {g : GA D V} {L M : Lat V} {P : Pl D → Prop} (hg : Moves V g L M P) :
    Moves V g⁻¹ M L P := by
  intro y hy
  have h1 := hg (mt V g⁻¹ *ᵥ y) (GlobalTheory.FinPl.KOpen.supp_mulVec V P g⁻¹ hy)
  rw [Matrix.mulVec_mulVec, show mt V g * mt V g⁻¹ = mt V (g * g⁻¹) from rfl, mul_inv_cancel,
    show mt V (1 : GA D V) = 1 from rfl, Matrix.one_mulVec] at h1
  exact h1.symm

theorem moves_conj_iff {V : HSp D} {t : GA D V} (h : GA D V) {L M : Lat V} {P : Pl D → Prop} (ht : Moves V t L M P) :
    Moves V (t⁻¹ * h * t) L L P ↔ Moves V h M M P := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have := moves_mul (moves_mul (moves_inv ht) H) ht
    rwa [show t * (t⁻¹ * h * t * t⁻¹) = h by group] at this
  · have := moves_mul (moves_mul ht H) (moves_inv ht)
    rwa [← mul_assoc] at this

theorem finE_conj_mem_St_iff : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ M : GlobalTheory.FinPl.Lat V), Formalism.L2.DIV.IsFrame β Λ → IsSelfDualC V Λ → IsSelfDualC V M → ∀ t h : GA D V, t ∈ GfC V → h ∈ GfC V → (∀ P, GlobalTheory.FinPl.Moves V t Λ M P) → (Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves V h M M (· = v)) := by
  intro D V β Λ M hβ hΛ _ t h _ _ ht
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E)
  rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
  exact forall_congr' fun v => (moves_iff_stabLoc V Λ hfg v _).symm.trans (moves_conj_iff h (ht _))

end GlobalTheory.StMoves

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorHalfComponentOnVacuumTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_halfComponent_on_vacuumTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ f₀, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') f₀ → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, heisO ψ S T (((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => e * incA D r) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) = alV D.host.d sc (embH (tauE D) δ x') • heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (x')).reindex (finCongr hT.symm) (finCongr hS.symm))) (heisO ψ S T (GlobalTheory.VacUnique.finRat S T ((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm))) f₀) := by
  first | exact @GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq | exact GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq | (intros; apply GlobalTheory.AdForm.HalfHeis.heisO_halfA_eq <;> assumption)
end

