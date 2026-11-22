import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0887
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinMComp

variable {D : D7}

theorem eq_zero_of_le_exp (x : WithZero (Multiplicative ℤ)) (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  have h1 := h (Int.toNat (-(Multiplicative.toAdd m)) + 1)
  have e : ((m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd m) := rfl
  rw [e, WithZero.exp_le_exp] at h1
  omega

theorem afIso_indP (w : GlobalTheory.FinPl.Pl D) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = w) :
    GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w)) P = 1 := by
  have hs := fun n =>
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv D.host.F D.host.E).choose_spec.2.2.2
      (GlobalTheory.FinPl.KOpen.indP D (· = w)) 1 P n
  have h0 : (GlobalTheory.FinPl.KOpen.indP D (· = w)) (P.under (𝓞 D.host.F)) - algebraMap D.host.F _ 1 = 0 := by
    have := GlobalTheory.FinPl.KOpen.evalV_indP (D := D) (· = w) (P.under (𝓞 D.host.F))
    rw [if_pos hP] at this
    rw [map_one, sub_eq_zero]
    exact this
  have h1 : ∀ n : ℕ, Valued.v (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E
      ((1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w)) P
      - algebraMap D.host.E _ (algebraMap D.host.F D.host.E 1)) ≤ WithZero.exp (-(n : ℤ)) := fun n =>
    hs n (by rw [h0, Valuation.map_zero]; exact zero_le')
  have h2 := eq_zero_of_le_exp _ h1
  rw [Valuation.zero_iff, map_one, map_one, sub_eq_zero] at h2
  exact h2

theorem indicatorAdele_mul_eq_zero (w : GlobalTheory.FinPl.Pl D) (z : Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w z = 0) :
    (GlobalTheory.FinPl.KOpen.indP D (· = w) ⊗ₜ[D.host.F] (1 : D.host.E)) * z = 0 := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v 0
  rw [map_mul, map_zero, GlobalTheory.FinPl.KOpen.compFin_e]
  by_cases hv : v = w
  · subst hv; rw [hz, mul_zero]
  · rw [if_neg hv, zero_mul]

theorem adAt_toEAf_eq_zero (w : GlobalTheory.FinPl.Pl D) (a : AE D) (ha : GlobalTheory.FinPl.compAt D w a = 0)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = w) :
    GlobalTheory.Mem.Col2.adAt D.host.F P (toEAf D a) = 0 := by
  have h0 := congrArg (fun y => GlobalTheory.Mem.Col2.adAt D.host.F P
    ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom y))
    (indicatorAdele_mul_eq_zero w (finPart D a) ha)
  simp only [map_mul, map_zero] at h0
  have e1 : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom
      (GlobalTheory.FinPl.KOpen.indP D (· = w) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      (1 : D.host.E) ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = w) := rfl
  rw [e1, GlobalTheory.Mem.Col2.adAt_apply D.host.F P ((1 : D.host.E) ⊗ₜ[D.host.F] _), afIso_indP w P hP, one_mul] at h0
  exact h0

theorem adAt_finM_eq_one : ∀ (D : D7) (V : HSp D) {n : ℕ} (hn : V.rank = n) (Pset : GlobalTheory.FinPl.Pl D → Prop) (h : GA D V),
    h ∈ GlobalTheory.FinPl.grpAt V Pset → ∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ Pset (P.under (𝓞 D.host.F)) → ∀ r k,
      adAt D.host.F P (finM V hn h r k) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion D.host.E)) r k := by
  intro D V n hn Pset h hh P hP r k
  subst hn
  rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply]
  have hmem := (GlobalTheory.FinPl.SetCut.mem_congGrp_iff V _ h).1 hh r k
  have hz := adAt_toEAf_eq_zero _ _ (((GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D Pset _).1 hmem).2 _ hP) P rfl
  have e : Formalism.L2.Theta.mt V h r k = (Formalism.L2.Theta.mt V h - 1) r k + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r k := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [e, RingHom.map_add (toEAf D), RingHom.map_add (GlobalTheory.Mem.Col2.adAt D.host.F P), hz, zero_add]
  by_cases hrk : r = k
  · subst hrk; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, hrk]

end GlobalTheory.FinMComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatWeilRepresentationCores
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.FlatCommBF

variable {D : D7}

theorem sFinite_of_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) (h : ν.IsHaarMeasure) : SFinite ν := by
  haveI := h
  infer_instance

theorem continuous_psiUni (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hv : Continuous fun u : UX D ρ => u.1.1 := Units.continuous_val.comp continuous_subtype_val
  unfold psiUni psiE upSum
  refine hψ.comp (ht.comp ?_)
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  · exact continuous_const

theorem jacT_integral (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) {U : Type} [MeasurableSpace U] (m : Measure U) (G : U → WO S T₀ → ℂ)
    (w : WO S T₀) : jacT ψ d S y n (fun w' => ∫ u, G u w' ∂m) w = ∫ u, jacT ψ d S y n (G u) w ∂m := by
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]

theorem jacT_smul (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) (c : ℂ) (f : WO S T₀ → ℂ) :
    jacT ψ d S y n (c • f) = c • jacT ψ d S y n f := by
  funext w
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 400000 in

theorem flatBF_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ h₀ n hn h'
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨hloc, hsc, -⟩ := GlobalTheory.UnitU.topology D ρ
  haveI := hloc
  haveI := hsc
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := @sFinite_of_haar (UX D ρ) _ _ _ hloc hsc s.vU.ν s.vU.unit.1
  obtain ⟨hbase, -, hx0, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have hlin : LinearIndependent D.host.E J.d.e.transpose := hbase.1
  have hev := GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom' Ψ hΨ
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl

  have e3 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 1 (one_mem _) h'
    rw [map_one, one_mul, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    rw [h]
    simp only [opA, jacT_one]
    rfl
  have e2 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ
      (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 n hn h'
    rw [map_one, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    exact h

  have hmix := GlobalTheory.MixValues.mixed_values D ψ hstd
  have thev : ∀ Φ, IsThetaFunO ψ B.V J.W Φ → ∀ u : UX D ρ, IsThetaFunO ψ B.V₀ J.W₀
      (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun Φ hΦ u => hmix.2 B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _
      (hmix.1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Φ hΦ _) _
  have thom : ∀ p, IsThetaFunO ψ B.V J.W (s.om p Ψ) := fun p => s.weil.om_pres p Ψ hΨ
  have hFL := GlobalTheory.Unf.Flat.flatLaw D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e hlin
    (yZero B.V₀ ρ (vecB B.o B.ζ))
  have thflat : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s (s.om p Ψ)) := fun p => by
    have h := (hFL _ (thom p)).2
    rw [← hx0] at h
    exact h
  obtain ⟨M, hMi, hM⟩ := GlobalTheory.Unf.flatFun_majorant D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hlin
    Ψ hΨ {1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} (Set.toFinite _).isCompact
  simp only [← hx0] at hM
  have bound : ∀ p ∈ ({1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} :
      Set (GA D B.V × GA D J.W)), ∀ (u : UX D ρ) w, ‖star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om p Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w‖ ≤ M u :=
    fun p hp u w => hM p hp _ w u
  have hmc := GlobalTheory.MixCont.mixed_coords_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ
  have hxu : Continuous fun u : UX D ρ => xZero J.d ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have cont : ∀ p, Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) *
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om p Ψ) (xZero J.d ⬝ q.1.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) q.2 := by
    intro p
    have h1 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => ((p, xZero J.d ⬝ q.1.1.1, yZero B.V₀ ρ (vecB B.o B.ζ), q.2) :
        (GA D B.V × GA D J.W) × Mx D J.W.rank ρ × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have h2 := hmc.2.comp h1
    have h3 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) :=
      ((continuous_psiUni ψ hstd.1.1 ρ).comp continuous_fst).star
    exact h3.mul h2
  have hci := GlobalTheory.CommInt.om_integral_comm D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ (UX D ρ) s.vU.ν

  have hF : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) = star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
    fun u => rfl
  have hG : ∀ (u : UX D ρ) w, s.om₀ (1, h') (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF, map_smul, e3]
    rfl
  have step1 : ∀ w, s.om₀ (1, h') (flatBF s Ψ) w = ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (1, h') M
      (fun u => by rw [hF]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev Ψ hΨ u))
      (by have h := cont 1; rw [hom1] at h; exact h)
      (by simp only [hG]; exact cont _)
      hMi
      (fun u w => ⟨by have h := bound 1 (by simp) u w; rw [hom1] at h; exact h, by rw [hG]; exact bound _ (by simp) u w⟩)
      (by have h := thflat 1; rw [hom1] at h; exact h) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG u w))

  have hF2 : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
      star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := fun u => rfl
  have hG2 : ∀ (u : UX D ρ) w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF2, map_smul, e2, hev.1 u h₀ n hn h']
    rfl
  have step2 : ∀ w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν) w =
      ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (B.o.emb (h₀, 1), 1) M
      (fun u => by rw [hF2]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev _ (thom _) u))
      (cont _)
      (by simp only [hG2]; exact cont _)
      hMi
      (fun u w => ⟨bound _ (by simp) u w, by rw [hG2]; exact bound _ (by simp) u w⟩)
      (thflat _) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG2 u w))

  have hopa : opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ) =
      fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    funext w
    have h1 : s.om₀ (1, h') (flatBF s Ψ) = fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν :=
      funext step1
    show jacT ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n (s.om₀ (1, h') (flatBF s Ψ)) w = _
    rw [h1, jacT_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h2 : (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
        star (psiUni ψ u.1) • s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
      rw [e3]; rfl
    dsimp only
    rw [h2, jacT_smul, e2]
    rfl
  rw [hopa]
  funext w
  exact (step2 w).symm

end GlobalTheory.Unf.FlatCommBF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesPl

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPl.KOpen

variable {D : D7}

theorem latV_transfer (S : HSp D) (L : Lat S) {P₁ P₂ : Pl D → Prop} (h : ∀ p, P₁ p → P₂ p)
    {z : Fin S.rank → AE D} (hz : ∀ i, z i ∈ idAt D P₁) : z ∈ latV S L P₁ ↔ z ∈ latV S L P₂ := by
  rw [mem_latV_iff S L P₁ z hz, mem_latV_iff S L P₂ z fun i => idAt_mono h (hz i)]

theorem mem_latV_empty (S : HSp D) (L : Lat S) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· ∈ (∅ : Finset (Pl D)))) : z ∈ latV S L (· ∈ (∅ : Finset (Pl D))) := by
  classical
  rw [mem_latV_iff S L _ z hz]
  have h0 : finPart D ∘ z = 0 := by
    funext i
    rw [Function.comp_apply, ← e_mul_fin (hz i)]
    refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
    change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _
    rw [map_mul, compFin_e, if_neg (Finset.notMem_empty w), zero_mul, Pi.zero_apply, map_zero]
  rw [h0]
  exact zero_mem _

theorem moves_of_places : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : Lat S) (Q : Finset (Pl D)),
    (∀ v ∈ Q, Moves S g L M (· = v)) → Moves S g L M (· ∈ Q) := by
  intro D S g L M Q
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro _ y hy
    exact iff_of_true (mem_latV_empty S L hy) (mem_latV_empty S M (supp_mulVec S _ g hy))
  | insert v Q hv ih =>
    intro hQ y hy
    have hQ' := ih fun w hw => hQ w (Finset.mem_insert_of_mem hw)
    have hvv := hQ v (Finset.mem_insert_self v Q)
    have hgy := supp_mulVec S _ g hy
    have comm : ∀ c : AE D, c • (mt S g *ᵥ y) = mt S g *ᵥ (c • y) := fun c => (mulVec_smul _ _ _).symm
    have s1 : ∀ i, (eQ {v} • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (eQ_off {v}) (hy i)
    have s2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (one_sub_eQ_off {v}) (hy i)
    have i1 : ∀ p, (p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) → p = v := fun p h => Finset.mem_singleton.1 h.2
    have i2 : ∀ p, (p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) → p ∈ Q := fun p h =>
      (Finset.mem_insert.1 h.1).resolve_left fun e => h.2 (Finset.mem_singleton.2 e)
    have t1 : ∀ i, (eQ {v} • y) i ∈ idAt D (· = v) := fun i => idAt_mono i1 (s1 i)
    have t2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (· ∈ Q) := fun i => idAt_mono i2 (s2 i)
    rw [mem_latV_iff_parts S L _ {v} hy, mem_latV_iff_parts S M _ {v} hgy, comm, comm,
      latV_transfer S L i1 s1, latV_transfer S L i2 s2,
      latV_transfer S M i1 (fun i => by rw [← comm]; exact mul_mem_idAt (eQ_off {v}) (hgy i)),
      latV_transfer S M i2 (fun i => by rw [← comm]; exact mul_mem_idAt (one_sub_eQ_off {v}) (hgy i))]
    exact and_congr (hvv _ t1) (hQ' _ t2)

end GlobalTheory.FinPl.MovesPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, IsReps ((I.rec7 l Z).sp.X i) (A.U i β) (A.h i β) ∧ (Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ)) ∧ ∀ c, stabOrd (A.U i β) (A.h i β c) = Nat.card ((I.chain l u a).stab i c.1) := by
  first | exact @GlobalTheory.ChartReps.twDat_reps | exact GlobalTheory.ChartReps.twDat_reps | (intros; apply GlobalTheory.ChartReps.twDat_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilCoefficientFockVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftCoefCont

theorem continuous_l2_weil_action_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ Q₁ Q₂, Continuous fun g : GA D (Wc D i) => l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hc Q₁ Q₂
  obtain ⟨-, -, -, -, -, hom, -, -, hpt, -, -⟩ := h
  have e : ∀ g : GA D (Wc D i), l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) =
      GlobalTheory.RawLift.thetaIP μ 𝓧 (ptAt R i σ BW f Q₂) (ω (1, g) (ptAt R i σ BW f Q₁)) := fun g => by
    rw [← GlobalTheory.RawLift.FockCoef.thetaInner_star, GlobalTheory.RawLift.GoodModulus.thetaInner_eq_star_l2, star_star]
  simp only [e]
  exact GlobalTheory.RawLift.FockCoef.continuous_coef hom hc (hpt Q₂) (hpt Q₁)

end GlobalTheory.LiftCoefCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllCombProof

variable {D : D7}

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (h : ∀ x, Q x → P x) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hmono : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (h v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hmono hu), fun e he u hu hh => hf.2.2 e he u (hmono hu) hh⟩

theorem combAt_mono {S T : HSp D} {P Q : Pl D → Prop} (h : ∀ x, P x → Q x) {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt Q c := fun x hx => GlobalTheory.DisjComb.mxAt_mono h (hc x hx)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_nil {f f' : WO S T → ℂ} : OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {i : ι} {J : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔
      ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem over_unique (hψ : IsStdChar D ψ (-1)) {i : ι} {g f' f'' : WO S T → ℂ}
    (h' : Over ψ (α i) (β i) LS LT g (Ψ i) f') (h'' : Over ψ (α i) (β i) LS LT g (Ψ i) f'') : f' = f'' :=
  ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k (p i) n n' ψ hψ S T (α i) (β i) LS LT h'.1 h'.2.1 g h'.2.2.1).1 (Ψ i) h'.2.2.2.1).unique h' h''

theorem overAll_unique (hψ : IsStdChar D ψ (-1)) (J : List ι) : ∀ f f' f'' : WO S T → ℂ,
    OverAll ψ α β LS LT Ψ J f f' → OverAll ψ α β LS LT Ψ J f f'' → f' = f'' := by
  induction J with
  | nil => intro f f' f'' h' h''; rw [overAll_nil.1 h', overAll_nil.1 h'']
  | cons i J ih =>
    intro f f' f'' h' h''
    obtain ⟨g, hg, h'⟩ := overAll_cons.1 h'
    obtain ⟨g', hg', h''⟩ := overAll_cons.1 h''
    obtain rfl := ih f g g' hg hg'
    exact over_unique hψ h' h''

theorem over_comb (hψ : IsStdChar D ψ (-1)) {i : ι} (hu : (p i).UnitAA) {Q : Pl D → Prop} (hQ : ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) {g f : WO S T → ℂ} (h : Over ψ (α i) (β i) LS LT g (Ψ i) f) :
    Over ψ (α i) (β i) LS LT (comb ψ S T d g) (Ψ i) (comb ψ S T d f) := by
  obtain ⟨c, hc, hcf⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ hu S T (α i) (β i) LS LS LT LT h.1 h.2.1 h.1 h.2.1).2
    (Ψ i) h.2.2.2.1
  have M := GlobalTheory.DisjComb.main D ψ hψ S T Q (· = (p i).v) (fun x hx hx' => hQ (hx' ▸ hx))
  have hf : f = comb ψ S T c g := over_unique hψ h (hcf g h.2.2.1)
  rw [hf, M.1 d c hd hc g]
  exact hcf _ ((M.2.1 d hd).2 LS LT g h.2.2.1)

theorem overAll_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) {Q : Pl D → Prop} (hQ : ∀ i, ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) (J : List ι) (f : WO S T → ℂ) : ∀ f', OverAll ψ α β LS LT Ψ J f f' →
      OverAll ψ α β LS LT Ψ J (comb ψ S T d f) (comb ψ S T d f') := by
  induction J with
  | nil => intro f' h; rw [overAll_nil.1 h]; exact overAll_nil.2 rfl
  | cons i J ih =>
    intro f' h
    obtain ⟨g, hg, h⟩ := overAll_cons.1 h
    exact overAll_cons.2 ⟨_, ih g hg, over_comb hψ (hu i) (hQ i) hd h⟩

theorem exists_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) (hΨ : ∀ i, Ψ i ∈ SB (Matrix n n' k)) (J : List ι) (hJ : J.Nodup) :
    ∃ c : WO S T →₀ ℂ, CombAt (fun x => ∃ i ∈ J, x = (p i).v) c ∧
      ∀ f, (∀ i ∈ J, Vac ψ S T LS LT (· = (p i).v) f) → OverAll ψ α β LS LT Ψ J f (comb ψ S T c f) := by
  induction J with
  | nil =>
    exact ⟨Finsupp.single 0 1, OffTest.combAt_single_zero _ _, fun f _ => overAll_nil.2 (OffTest.comb_single_zero ψ S T f)⟩
  | cons i J ih =>
    obtain ⟨hi, hJ'⟩ := List.nodup_cons.1 hJ
    obtain ⟨c', hc', hf'⟩ := ih hJ'
    obtain ⟨c, hc, hcf⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ (hu i) S T (α i) (β i) LS LS LT LT hLS hLT hLS hLT).2
      (Ψ i) (hΨ i)
    have M := GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ∃ j ∈ J, x = (p j).v) (· = (p i).v) (by
      rintro x ⟨j, hj, rfl⟩ hx
      exact hi (hinj hx ▸ hj))
    obtain ⟨c'', hc'', heq⟩ := M.2.2.2.1 c c' (combAt_mono (fun x hx => Or.inr hx) hc)
      (combAt_mono (fun x hx => Or.inl hx) hc')
    refine ⟨c'', combAt_mono ?_ hc'', fun f hf => ?_⟩
    · rintro x (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
      · exact ⟨i, List.mem_cons_self, rfl⟩
    · rw [heq]
      exact overAll_cons.2 ⟨_, hf' f fun j hj => hf j (List.mem_cons_of_mem _ hj),
        hcf _ ((M.2.1 c' hc').2 LS LT f (hf i List.mem_cons_self))⟩

end GlobalTheory.FinPl.AllCombProof

namespace GlobalTheory.FinPl

open AllCombProof in

theorem allComb : ∀ D : D7, AllComb D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ ψ hψ S T α β LS LT hLS hLT Ψ
  refine ⟨fun hΨ => ?_, overAll_unique hψ I, fun d hd f hf => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc, hf⟩ := exists_comb (α := α) (β := β) hψ hP.unit hP.inj hLS hLT hΨ I hP.nodup
    refine ⟨c, combAt_mono ?_ hc, fun f h => hf f fun i _ => vac_mono ?_ h⟩
    · rintro x ⟨i, -, rfl⟩
      exact (hP.mem _).2 ⟨i, rfl⟩
    · rintro x rfl
      exact (hP.mem _).2 ⟨i, rfl⟩
  · exact ((GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ¬ P x) P fun x hx => hx).2.1 d hd).2 LS LT f hf
  · exact overAll_comb hψ hP.unit (fun i h => h ((hP.mem _).2 ⟨i, rfl⟩)) hd I f

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMethodOfEisensteinFactsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_method_of_eisenstein_facts : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.DoublingMethod := by
  first | exact @GlobalTheory.doublingMethod_of_three | exact GlobalTheory.doublingMethod_of_three | (intros; apply GlobalTheory.doublingMethod_of_three <;> assumption)
end

