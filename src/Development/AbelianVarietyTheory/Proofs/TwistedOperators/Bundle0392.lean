import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TranslatedEvalInj

section Count

open Formalism.MainNotions.S

theorem gfset_countable (I : AutInst) : I.GFset.Countable := by
  classical
  haveI : Countable I.E := (Module.finBasis ℚ I.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin I.n) (Fin I.n) I.E) :=
    inferInstanceAs (Countable (Fin I.n → Fin I.n → I.E))
  haveI : Countable (GL (Fin I.n) I.E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin I.n) I.E → Matrix (Fin I.n) (Fin I.n) I.E)) fun _ _ h => Units.ext h

  let W : GL (Fin I.n) I.E → Set I.GA := fun γ =>
    {x | (∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat x.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))}
  have hsub : I.GFset ⊆ ⋃ γ, W γ := by
    rintro x ⟨γ, -, h1, h2⟩
    exact Set.mem_iUnion.2 ⟨γ, h1, h2⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_)
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((hx1 v).trans (hy1 v).symm))
  · exact Subtype.ext (Units.ext (hx2.trans hy2.symm))

theorem eq_zero_of_ae_fund (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] {fund : Set I.GA}
    (hfund : I.IsFundDom (I.muA μf) fund) {φ : I.GA → ℂ} (hc : Continuous φ)
    (hinv : ∀ γ ∈ I.GFset, ∀ y, φ (γ * y) = φ y) (h0 : φ =ᵐ[(I.muA μf).restrict fund] 0) (y : I.GA) : φ y = 0 := by
  by_contra hy
  obtain ⟨hl, -, -, -, hpos⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf

  have hpre : ∀ γ : I.GA, ∀ A : Set I.GA, I.muA μf A = 0 → I.muA μf ((fun z => γ * z) ⁻¹' A) = 0 := by
    intro γ A hA
    obtain ⟨t, hAt, ht, ht0⟩ := exists_measurable_superset_of_null hA
    refine measure_mono_null (Set.preimage_mono hAt) ?_
    by_cases hf : AEMeasurable (fun z => γ * z) (I.muA μf)
    · rw [← Measure.map_apply_of_aemeasurable hf ht, hl γ]
      exact ht0
    · have hz : I.muA μf = 0 := by rw [← hl γ, Measure.map_of_not_aemeasurable hf]
      rw [hz]
      simp
  have hopen : IsOpen {z | φ z ≠ 0} := isOpen_ne_fun hc continuous_const

  have hnull : I.muA μf ({z | φ z ≠ 0} ∩ fund) = 0 := by
    have h1 : ∀ᵐ z ∂(I.muA μf), z ∈ fund → φ z = 0 := (ae_restrict_iff' hfund.1).1 h0
    rw [ae_iff] at h1
    refine measure_mono_null ?_ h1
    intro z hz
    exact fun h => hz.1 (h hz.2)

  have hcov : {z | φ z ≠ 0} ⊆ ⋃ γ ∈ I.GFset, (fun z => γ * z) ⁻¹' ({z | φ z ≠ 0} ∩ fund) := by
    intro z hz
    obtain ⟨γ, hγ, hγz⟩ := hfund.2.1 z
    refine Set.mem_biUnion hγ ⟨?_, hγz⟩
    show φ (γ * z) ≠ 0
    rw [hinv γ hγ z]
    exact hz
  have hall : I.muA μf {z | φ z ≠ 0} = 0 := by
    refine measure_mono_null hcov ((measure_biUnion_null_iff (gfset_countable I)).2 fun γ _ => ?_)
    exact hpre γ _ hnull
  exact (hpos _ hopen ⟨y, hy⟩).ne' hall

theorem castGA_symm_mem {I I' : AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

end Count

section Cyclic

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Formalism.IndefR.Datum.InfFam D} {M : DSModel V S} {J : Set (GA D V)}
  {χ : GA D V → ℂ}

theorem eq_zero_of_value {T : MMap M} (hT : IsMultMap θ M J χ T) (v₀ : M.Vec) (hv₀ : ∀ τ, (v₀ τ : M.H τ) ≠ 0)
    (h0 : T v₀ = 0) : T = 0 := by
  classical

  have step : ∀ (u : M.Vec) (τ : D.what₂.Tau), T u = 0 → (u τ : M.H τ) ≠ 0 →
      ∀ w : M.sm τ, T (Function.update u τ w) = 0 := by
    intro u τ hu hne w
    funext x
    obtain ⟨ℓ, hℓ, hval⟩ := hT.cont τ u x
    have horb : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ℓ (M.rep τ g (u τ)) = 0 := by
      intro g hg
      have hmem : M.rep τ g (u τ) ∈ M.sm τ := GlobalTheory.ConjMult.rep_mem_sm M τ hg (u τ).2
      have h1 := hval ⟨_, hmem⟩
      rw [hT.equiv τ g hg u ⟨_, hmem⟩ rfl, hu] at h1
      simpa [rTr] using h1
    have h2 := GlobalTheory.SmoothCyclic.eq_zero_of_orbit D V S M τ ℓ hℓ (u τ) (u τ).2 hne horb w w.2
    rw [hval w] at h2
    exact h2

  have key : ∀ s : Finset D.what₂.Tau, ∀ w : M.Vec, T (fun τ => if τ ∈ s then w τ else v₀ τ) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro w
      simpa using h0
    · intro a s ha ih w
      have hne : ((if a ∈ s then w a else v₀ a : M.sm a) : M.H a) ≠ 0 := by
        simp only [ha, if_false]
        exact hv₀ a
      have h3 := step _ a (ih w) hne (w a)
      convert h3 using 2
      funext τ
      rcases eq_or_ne τ a with rfl | hτ
      · simp
      · simp [hτ]
  apply MultilinearMap.ext
  intro w
  simpa using key Finset.univ w

end Cyclic

end GlobalTheory.TranslatedEvalInj

theorem GlobalTheory.TranslatedEvalInj.eq_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), (∀ τ, (v₀ τ : (MP R).H τ) ≠ 0) → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ S' : MMap (R.MY 0), S' = postOn (R.MY 0) R.e0 S - S → ((fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) =ᵐ[muX X] 0) → S' = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hmod t v₀ hv₀ S hS S' hS' hae

  have hsub : ∀ k ∈ (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0))),
      k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) ∧
        levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k =
          levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) k := by
    intro k hk
    have h1 : Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k) = 1 := Subgroup.mem_bot.1 hk.2.2
    refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
    · change Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k) ∈ (R.levR F true).H
      rw [h1]
      exact Subgroup.one_mem _
    · rw [GlobalTheory.FlagAction.levChi_flag1]
      have e1 := Formalism.IndefR.Lev.levFn_withP (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) (R.levR F true)
        (finE (Yc D 0) k)
      have e2 : Formalism.L2.DIV.ext1 (R.levR F true).H (R.levR F true).chi
          (Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k)) = 1 := by
        rw [h1]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      calc levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k
          = ((Formalism.L2.DIV.ext1 (R.levR F true).H (R.levR F true).chi
              (Formalism.L2.DIV.rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) k)) *
              Formalism.L2.DIV.levFn (R.βY 0) (flagL (R.dat0 R.triv)) (finE (Yc D 0) k) : ℂˣ) : ℂ) :=
            congrArg Units.val e1
        _ = ((Formalism.L2.DIV.levFn (R.βY 0) (flagL (R.dat0 R.triv)) (finE (Yc D 0) k) : ℂˣ) : ℂ) := by
            rw [e2, one_mul]
  have hSp : S ∈ Mult R.θ (R.MY 0) (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0)))
      (levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) :=
    GlobalTheory.ProjectedLift.mult_mono hsub hS
  have hS'm : S' ∈ Mult R.θ (R.MY 0) (levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) : Set (GA D (Yc D 0)))
      (levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) := by
    rw [hS']
    exact Submodule.sub_mem _
      (GlobalTheory.ProjectedLift.postOn_gaL_mem (β := R.βY 0) (L := R.dat0 R.triv) hmod.inf R.eG
        (RealDat.eC (A := A) D.what₂.embLL) hSp) hSp
  have hT := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hS'm

  have hQ : ∀ γ ∈ X.B.I.GFset, (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    have h1 := GlobalTheory.TranslatedEvalInj.castGA_symm_mem h.symm γ hγ
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    change Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact h1

  have hfun : ∀ y : X.B.I.GA, S' v₀ ((iotaX X h).symm (y * iotaX X h t)) =
      ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm y) t) := by
    intro y
    rw [map_mul]
    exact congrArg (fun z : GA D (D.sp.Y 0) => S' v₀ ((iotaX X h).symm y * z)) ((iotaX X h).symm_apply_apply t)
  have hv : ∀ y : X.B.I.GA, S' v₀ ((iotaX X h).symm (y * iotaX X h t)) = 0 := by
    have hc : Continuous fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t)) :=
      (hT.aut v₀).cont.comp ((iotaX X h).symm.continuous.comp (continuous_mul_right _))
    have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y,
        S' v₀ ((iotaX X h).symm (γ * y * iotaX X h t)) = S' v₀ ((iotaX X h).symm (y * iotaX X h t)) := by
      intro γ hγ y
      rw [mul_assoc, map_mul]
      exact (hT.aut v₀).left _ (hQ γ hγ) _
    have hae' : (fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t))) =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
      have e : (fun y : X.B.I.GA => S' v₀ ((iotaX X h).symm (y * iotaX X h t))) =
          fun x => ev (MP R) v₀ S' (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) :=
        funext hfun
      rw [e]
      exact hae
    exact GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hc hinv hae'
  have h0 : S' v₀ = 0 := by
    funext g
    have h2 := hv (iotaX X h (g * t⁻¹))
    have e : (iotaX X h).symm (iotaX X h (g * t⁻¹) * iotaX X h t) = g := by
      refine ((congrArg (iotaX X h).symm (map_mul (iotaX X h) (g * t⁻¹) t).symm).trans
        ((iotaX X h).symm_apply_apply _)).trans ?_
      first
        | exact inv_mul_cancel_right g t
        | simp
    rw [e] at h2
    exact h2
  exact GlobalTheory.TranslatedEvalInj.eq_zero_of_value hT v₀ hv₀ h0

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParsevalMixedModelIsotropicThetaProduct
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixParsevalPoint

variable {D : D7}

private theorem heisO_apply (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (g : WO S T → ℂ)
    (z : WO S T) : heisO ψ S T w g z = ψ (symplOH S T z w) * g (z + w) := by
  simp only [heisO]

private theorem symplOH_zero_left_twisted_operators (S T : HSp D) (p : WO S T) : symplOH S T 0 p = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_left (0 : WO S T) 0 p
  rw [zero_add] at h
  linear_combination -h

private theorem mul_mul_conj_mul_eq_of_mul_conj_eq_one (p a b : ℂ) (hp : p * starRingEnd ℂ p = 1) :
    p * a * starRingEnd ℂ (p * b) = a * starRingEnd ℂ b := by
  rw [map_mul]
  linear_combination (a * starRingEnd ℂ b) * hp

theorem psi_mul_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    ψ a * starRingEnd ℂ (ψ a) = 1 := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  norm_num

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  norm_num

theorem symplOH_eq (S T : HSp D) (a b : WO S T) :
    symplOH S T a b = algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T a b := rfl

private theorem heisO_isoPart_incA_add_apply_eq_psi_mul {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) (ψ : AddChar (AF D.host.F) ℂ)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) (u : Mx D W.rank r)
    (ξ : Matrix (Fin W.rank) (Fin r) D.host.E) (y : Mx D W.rank r) :
    heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f (isoPart V W C y + midPart V V' W B x) =
      ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
        heisO ψ V W (isoPart V W C' u) f (isoPart V W C y + midPart V V' W B x) := by
  have orth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hrat : isoPart V W C' (ξ.map (incA D)) ∈ ratL W V := GlobalTheory.TowerRestrict.isoPart_rat C' ⟨ξ, rfl⟩
  have eXU : symplOH V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) = 0 := by
    rw [symplOH_eq, orth.2.2.2 _ _, mul_zero]
  have e1 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) f
  rw [eXU, AddChar.map_zero_eq_one, one_smul, ← GlobalTheory.TowerRestrict.isoPart_add C'] at e1
  rw [← e1, heisO_apply ψ (isoPart V W C' (ξ.map (incA D))) (heisO ψ V W (isoPart V W C' u) f),
    add_comm (isoPart V W C y + midPart V V' W B x) _, GlobalTheory.HeisOrtho.heisO_quasi hf _ _ hrat, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
  have s1 := GlobalTheory.TwFour.symplOH_sub V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))
  have s2 := GlobalTheory.TwFour.symplOH_sub V W (midPart V V' W B x) (isoPart V W C' (ξ.map (incA D)))
  have s3 := GlobalTheory.OrientedHeis.symplO_skew (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x)
  rw [orth.2.2.1 _ _, neg_zero] at s3
  rw [s3] at s2
  linear_combination s1 + s2

theorem coef_eq {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x : WO V' W) (u : Mx D W.rank r) (ξ : Matrix (Fin W.rank) (Fin r) D.host.E) :
    res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x =
      ∫ y in 𝓨, ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
        heisO ψ V W (isoPart V W C' u) f (isoPart V W C y + midPart V V' W B x) ∂μ := by
  simp only [res]
  exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun y => heisO_isoPart_incA_add_apply_eq_psi_mul hs h1 h2 h3 ψ hf x u ξ y)

theorem res_smul {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (c : ℂ) (g : WO V W → ℂ) (x : WO V' W) : res V V' W C B μ 𝓨 (c • g) x = c * res V V' W C B μ 𝓨 g x := by
  simp only [res, Pi.smul_apply, smul_eq_mul]
  exact MeasureTheory.integral_const_mul c _

theorem expand {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hcov : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x : WO V' W) (u y₀ : Mx D W.rank r) :
    Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E =>
      ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x‖) ∧
    HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E =>
      ψ (symplO V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀)) *
        res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x)
      (heisO ψ V W (isoPart V W C' u) f (isoPart V W C y₀ + midPart V V' W B x)) := by
  have orth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hUf : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C' u) f) :=
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _
  have hMf : IsThetaFunO ψ V W (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)) :=
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hUf _
  have hF := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hMf (isoPart V W C y₀)
  obtain ⟨hs1, hs2⟩ := GlobalTheory.TwFour.value_zero_eq_sum_restrictions D V V' W r C C' B hs h1 h2 h3 ψ hψ μ 𝓨 hcov _ hF
  have key : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D)))
        (heisO ψ V W (isoPart V W C y₀) (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)))) 0 =
        ψ (symplO V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀)) *
          res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x := by
    intro ξ
    have eXM : symplO V W (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x) = 0 := orth.2.2.1 _ _
    have eXU : symplOH V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) = 0 := by
      rw [symplOH_eq, orth.2.2.2 _ _, mul_zero]
    have hG : IsThetaFunO ψ V W (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f)) :=
      GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) _
    rw [GlobalTheory.TwFour.heisO_comm (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀),
      GlobalTheory.TwFour.heisO_comm (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x), eXM, AddChar.map_zero_eq_one,
      one_smul, GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) f, eXU,
      AddChar.map_zero_eq_one, one_smul, ← GlobalTheory.TowerRestrict.isoPart_add C', res_smul,
      GlobalTheory.TowerRestrict.res_heis_iso hs hcov hG, GlobalTheory.TowerRestrict.res_heis_mid hs, heisO_apply,
      symplOH_zero_left_twisted_operators, AddChar.map_zero_eq_one, one_mul, zero_add]
  have hAM : symplOH V W (isoPart V W C y₀) (midPart V V' W B x) = 0 := by
    rw [symplOH_eq, orth.2.1 _ _, mul_zero]
  have F0 : heisO ψ V W (isoPart V W C y₀) (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)) 0 =
      heisO ψ V W (isoPart V W C' u) f (isoPart V W C y₀ + midPart V V' W B x) := by
    rw [heisO_apply, heisO_apply ψ (midPart V V' W B x), symplOH_zero_left_twisted_operators, zero_add, hAM,
      AddChar.map_zero_eq_one, one_mul, one_mul]
  refine ⟨hs1.congr fun ξ => ?_, ?_⟩
  · rw [key ξ, norm_mul, hψ.1.2.1, one_mul]
  · rw [← F0]
    convert hs2 using 1
    funext ξ
    exact (key ξ).symm

theorem parseval_point : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (x : WO V' W) (u : Mx D W.rank r), Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₂) x)‖) ∧ HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₂) x)) (∫ y in 𝓨, f₁ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) * starRingEnd ℂ (f₂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u)) ∂μ) := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hcov f₁ f₂ hf₁ hf₂ x u
  have hU₂ := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₂ (isoPart V W C' u)
  obtain ⟨K, hK⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hU₂
  have hμ1 : μ 𝓨 = 1 := hcov.2.2
  have : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top⟩
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable (Matrix (Fin W.rank) (Fin r) D.host.E) := inferInstanceAs (Countable (Fin W.rank → Fin r → D.host.E))
  have hc₂ : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
      ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₂) x‖ ≤
        K * (μ.restrict 𝓨).real Set.univ := by
    intro ξ
    rw [coef_eq hs h1 h2 h3 ψ μ 𝓨 hf₂ x u ξ]
    refine MeasureTheory.norm_integral_le_of_norm_le_const (MeasureTheory.ae_of_all _ fun y => ?_)
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hK _
  have hsum₁ := (expand hs h1 h2 h3 hψ hcov hf₁ x u 0).1
  have hcont₂ : Continuous fun y => heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x) :=
    hU₂.3.comp ((GlobalTheory.TowerRestrict.continuous_isoPart C).add continuous_const)
  have hmain : HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ∫ y in 𝓨,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ)
      (∫ y in 𝓨, heisO ψ V W (isoPart V W C' u) f₁ (isoPart V W C y + midPart V V' W B x) *
        starRingEnd ℂ (heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ) := by
    refine MeasureTheory.hasSum_integral_of_dominated_convergence
      (fun ξ _ => ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x‖ * K)
      (fun ξ => ?_) (fun ξ => MeasureTheory.ae_of_all _ fun y => ?_) (MeasureTheory.ae_of_all _ fun y => hsum₁.mul_right K)
      (MeasureTheory.integrable_const _) (MeasureTheory.ae_of_all _ fun y => ?_)
    · have hI := GlobalTheory.TowerRestrict.integrable_res (C := C) (B := B) hψ hcov
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₂ (isoPart V W C' (ξ.map (incA D) + u))) x
      have hm : MeasureTheory.AEStronglyMeasurable (fun y => ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) (μ.restrict 𝓨) :=
        hI.aestronglyMeasurable.congr (MeasureTheory.ae_of_all _ fun y => heisO_isoPart_incA_add_apply_eq_psi_mul hs h1 h2 h3 ψ hf₂ x u ξ y)
      exact (Complex.continuous_conj.comp_aestronglyMeasurable hm).const_mul _
    · rw [norm_mul, RCLike.norm_conj, norm_mul, hψ.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
    · have hE := ((expand hs h1 h2 h3 hψ hcov hf₁ x u y).2).mul_right
        (starRingEnd ℂ (heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)))
      convert hE using 1
      all_goals try rfl
      funext ξ
      rw [map_mul, GlobalTheory.OrientedHeis.symplO_skew (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y), conj_psi hψ, neg_neg]
      ring
  have hterm : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, (∫ y in 𝓨,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ) =
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₂) x) := by
    intro ξ
    rw [MeasureTheory.integral_const_mul, integral_conj, ← coef_eq hs h1 h2 h3 ψ μ 𝓨 hf₂ x u ξ]
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_)
    (hsum₁.mul_right (K * (μ.restrict 𝓨).real Set.univ)), ?_⟩
  · rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (hc₂ ξ) (norm_nonneg _)
  · convert hmain using 1
    · funext ξ
      exact (hterm ξ).symm
    · refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun y => ?_)
      dsimp only
      rw [heisO_apply, heisO_apply]
      exact (mul_mul_conj_mul_eq_of_mul_conj_eq_one _ _ _ (psi_mul_conj hψ _)).symm

end GlobalTheory.MixParsevalPoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ExtTensorIrr

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

theorem piTensor_isIrreducible : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β]
    (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k)),
    (GlobalTheory.SmGL.piTensor fun j => (s j).ρ).IsIrreducible := by
  intro hBZ k _ _ _ _ β _ c _ _ s
  obtain ⟨hAdm, -, -, -⟩ := hBZ k
  exact GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur (fun j => (s j).ρ) (fun j => (s j).irr)
    fun j φ hφ => GlobalTheory.SchurAdm.schur_admissible (GL (c j) k) (KO k (c j)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO (s j).V (s j).ρ (s j).irr
      (hAdm (c j) (s j).V (s j).ρ (s j).smooth (s j).irr) φ hφ

end GlobalTheory.ExtTensorIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialFockSpaceStableMulTracePairing
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

theorem GlobalTheory.PolMul.pol_mul_pairInf_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ (q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ∀ f ∈ M.Pol ψ τ, ∃ f₁ ∈ M.Pol ψ τ,
          ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ _ τ _ _ q f hf
  exact GlobalTheory.PolMul.model_mul M ψ hψ τ q f hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamiliesStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_classes_iff_local_class_families : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧ (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧ ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧ (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔ (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧ ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧ ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  first | exact @GlobalTheory.TrEll.RatClasses.rat_classes_iff_local | exact GlobalTheory.TrEll.RatClasses.rat_classes_iff_local | (intros; apply GlobalTheory.TrEll.RatClasses.rat_classes_iff_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_restriction_down_witt_tower_surjective : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f', IsThetaFunO ψ V' W f' → ∃ f, IsThetaFunO ψ V W f ∧ f' = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  first | exact @GlobalTheory.TowerSurj.res_surjective | exact GlobalTheory.TowerSurj.res_surjective | (intros; apply GlobalTheory.TowerSurj.res_surjective <;> assumption)
end

