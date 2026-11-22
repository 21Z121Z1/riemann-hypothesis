import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0530
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacter

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopSeparation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.SepRows.SepProof

section
open Classical

theorem atTau_mem_GinfC' {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g ∈ GinfC V := by
  unfold atTau; split_ifs with h
  exacts [h.choose_spec.1, one_mem _]

theorem pairVec_comp_rho {D : D7} {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {a : GA D V}
    (ha : a ∈ GinfC V) : pairVec c (ξ ∘ₗ c.ρ a⁻¹) Ψ = rTr V a (pairVec c ξ Ψ) := by
  funext h
  have e : (finHom V).rangeRestrict (h * a) = (finHom V).rangeRestrict h := by
    rw [map_mul]
    have : (finHom V).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    rw [this, mul_one]
  simp only [rTr, pairVec_apply, e, mul_inv_rev, map_mul, LinearMap.comp_apply, Module.End.mul_apply]

theorem mult_equiv {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    simp only [MultilinearMap.add_apply, h₁, h₂]; rfl
  | smul c T _ h =>
    simp only [MultilinearMap.smul_apply, h]; rfl

end

theorem Bplus_smul_left {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (a : ℂ)
    (φ : GA D (G.V (.top 0)) → ℂ) (F : GA D (G.V (.grid D.R.m 0)) → ℂ) : Bplus W M (a • φ) F = a * Bplus W M φ F := by
  have e : ∀ h n, besInt W (a • φ) F h n = a * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]

theorem Bplus_smul_right {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (a : ℂ)
    (φ : GA D (G.V (.top 0)) → ℂ) (F : GA D (G.V (.grid D.R.m 0)) → ℂ) : Bplus W M φ (a • F) = a * Bplus W M φ F := by
  have e : ∀ h n, besInt W φ (a • F) h n = a * besInt W φ F h n := fun h n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Bplus, e, integral_const_mul]

set_option maxHeartbeats 1000000 in
open Classical in

theorem topSep_of_classicalTheorems : GlobalTheory.FunPr.Hypotheses₂ → TopSep := by
  intro _
  unfold TopSep All
  intro D _ T L μ0 _ sc G W M hM S MB F' hF' Ψ hΨ
  have hθ : IsInfFam W.θ := W.θ_is
  set T' : MMap MB := PiTensorProduct.lift.symm F' with hT'
  have hT'm : T' ∈ Mult W.θ MB ∅ 1 := (mem_multT W.θ MB ∅ 1 F').1 hF'
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_meets_besselTopRationalOrbits W M hM
  have hφ : ∀ ξ, pairVec (coefPlus G W.θ) ξ Ψ ∈ contLeft (G.V (.top 0)) := fun ξ =>
    ⟨GlobalTheory.RowBplus.pairVec_cont G W.θ hθ ξ hΨ, fun γ hγ g => GlobalTheory.RowBplus.pairVec_left G W.θ ξ hΨ hγ g⟩
  have H := fun ξ => GlobalTheory.T.besselPeriodCorankOne_additive_bounded_compact W M hM Ω hΩc hΩ _ (hφ ξ)
  choose C hC using H
  have hadd := fun ξ => (hC ξ).1
  have hadd' := fun ξ => (hC ξ).2.1
  have hbd := fun ξ => (hC ξ).2.2
  have hTt : ∀ u : MB.Vec, F' (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : F' = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply F').symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT MB, F' x ∈ contLeft (G.V (.grid D.R.m 0)) := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft _).smul_mem r (GlobalTheory.Core.Mi.SepPer.mult_mem_contLeft W.θ MB ∅ 1 hT'm u)
    | add x y hx hy =>
      rw [map_add]
      exact (contLeft _).add_mem hx hy
  have pv_add : ∀ ξ ξ', pairVec (coefPlus G W.θ) (ξ + ξ') Ψ = pairVec (coefPlus G W.θ) ξ Ψ + pairVec (coefPlus G W.θ) ξ' Ψ := by
    intro ξ ξ'; funext h; simp [pairVec_apply]
  have pv_smul : ∀ (a : ℂ) ξ, pairVec (coefPlus G W.θ) (a • ξ) Ψ = a • pairVec (coefPlus G W.θ) ξ Ψ := by
    intro a ξ; funext h; simp [pairVec_apply]
  have hBadd : ∀ ξ ξ' F, F ∈ contLeft (G.V (.grid D.R.m 0)) → Bplus W M (pairVec (coefPlus G W.θ) (ξ + ξ') Ψ) F =
      Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F + Bplus W M (pairVec (coefPlus G W.θ) ξ' Ψ) F := by
    intro ξ ξ' F hF; rw [pv_add]; exact hadd' ξ _ (hφ ξ') F hF
  have hBsmul : ∀ (a : ℂ) ξ F, Bplus W M (pairVec (coefPlus G W.θ) (a • ξ) Ψ) F = a * Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) F := by
    intro a ξ F
    rw [pv_smul]; exact Bplus_smul_left W M a _ F
  have hBsmulR : ∀ (a : ℂ) φ F, Bplus W M φ (a • F) = a * Bplus W M φ F := by
    intro a φ F
    exact Bplus_smul_right W M a φ F
  refine ⟨⟨LinearMap.mk₂ ℂ (fun ξ v => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v))
      (fun ξ ξ' v => hBadd ξ ξ' _ (hmem v)) (fun a ξ v => hBsmul a ξ _)
      (fun ξ v v' => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_add v v')).trans (hadd ξ _ (hmem v) _ (hmem v')))
      (fun a ξ v => (congrArg (Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ)) (F'.map_smul a v)).trans (hBsmulR a _ _)), fun ξ v => rfl⟩, ?_⟩
  intro Wt _ _ π e he τ x v
  have hE : ∀ (y y' : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (y + y'))) =
      e (PiTensorProduct.tprod ℂ (Function.update x τ y)) + e (PiTensorProduct.tprod ℂ (Function.update x τ y')) := by
    intro y y'; rw [MultilinearMap.map_update_add, map_add]
  have hEs : ∀ (a : ℂ) (y : Wt τ), e (PiTensorProduct.tprod ℂ (Function.update x τ (a • y))) =
      a • e (PiTensorProduct.tprod ℂ (Function.update x τ y)) := by
    intro a y; rw [MultilinearMap.map_update_smul, map_smul]
  have hV : ∀ (u u' : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (u + u'))) =
      F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) + F' (PiTensorProduct.tprod ℂ (Function.update v τ u')) := by
    intro u u'; rw [MultilinearMap.map_update_add, map_add]
  have hVs : ∀ (a : ℂ) (u : MB.sm τ), F' (PiTensorProduct.tprod ℂ (Function.update v τ (a • u))) =
      a • F' (PiTensorProduct.tprod ℂ (Function.update v τ u)) := by
    intro a u; rw [MultilinearMap.map_update_smul, map_smul]
  have hF1 : ∀ (g : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.grid D.R.m 0)).rank) ℂ),
      g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.grid D.R.m 0)) τ) → ∀ (x₁ y₁ : MB.sm τ), (y₁ : MB.H τ) = MB.rep τ g x₁ →
      F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁)) =
        rTr _ (atTau W.θ _ τ g) (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁))) := by
    intro g hg x₁ y₁ hy
    rw [hTt, hTt]
    have := mult_equiv W.θ MB ∅ 1 hT'm τ hg (Function.update v τ x₁) y₁ (by simpa using hy)
    simpa using this
  obtain ⟨Lw, Cu, hL, hb⟩ := GlobalTheory.Core.Mi.SepPer.mult_bound (θ := W.θ) hθ MB (∅ : Set (GA D (G.V (.grid D.R.m 0)))) 1 hT'm Ω hΩc τ v
  refine ⟨LinearMap.mk₂ ℂ (fun y u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))))
      (fun y y' u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hE y y')).trans (hBadd _ _ _ (hmem _)))
      (fun a y u => (congrArg (fun ξ => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) _) (hEs a y)).trans (hBsmul _ _ _))
      (fun y u u' => (congrArg (Bplus W M _) (hV u u')).trans (hadd _ _ (hmem _) _ (hmem _)))
      (fun a y u => (congrArg (Bplus W M _) (hVs a u)).trans (hBsmulR _ _ _)), ⟨?_, ?_, ?_⟩, fun y u => rfl⟩
  · intro y
    have hℓ0 := fun (u u' : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hV u u')).trans
        (hadd _ _ (hmem _) _ (hmem _))
    have hℓ1 := fun (a : ℂ) (u : MB.sm τ) =>
      (congrArg (Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)) (hVs a u)).trans
        (hBsmulR a _ _)
    let ℓ₀ : MB.sm τ →ₗ[ℂ] ℂ :=
      { toFun := fun u => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
          (F' (PiTensorProduct.tprod ℂ (Function.update v τ u)))
        map_add' := hℓ0
        map_smul' := hℓ1 }
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ u : MB.sm τ, ℓ u = Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) Ψ)
        (F' (PiTensorProduct.tprod ℂ (Function.update v τ u))) := fun u => congrArg (fun m => m u) hℓ
    refine ⟨ℓ, ⟨Lw, C (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) * Cu, hL, fun w hw => ?_⟩, fun u => hℓw u⟩
    have hw' : w ∈ MB.sm τ := Submodule.subset_span hw
    have e1 : ℓ w = ℓ ((⟨w, hw'⟩ : MB.sm τ) : MB.H τ) := rfl
    rw [e1, hℓw]
    have := hbd (e (PiTensorProduct.tprod ℂ (Function.update x τ y))) _ (hmem _) _
      (fun z hz => by rw [hTt]; exact hb ⟨w, hw'⟩ z hz)
    calc _ ≤ _ := this
      _ = _ := by ring
  · intro h hh g hg hEm w x₁ y₁ hy
    have he1 := he τ h hh (Function.update x τ w) (Function.update x τ (π τ h w)) (by simp) (fun τ' hτ' => by simp [hτ'])
    have hp := pairVec_comp_rho (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ
      (atTau_mem_GinfC' W.θ _ τ h)
    have hemb : atTau W.θ (G.V (.grid D.R.m 0)) τ g = embTop G (atTau W.θ (G.V (.top 0)) τ h) :=
      (embRel_iff _ _ _).1 (GlobalTheory.T.embRel_atRealPlace_of_unitaryEmbedding D W.θ hθ _ _ _ τ h g hh hg hEm)
    show Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ (π τ h w)))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) =
      Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ (Function.update x τ w))) Ψ)
      (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [he1, hp, hF1 g hg x₁ y₁ hy, hemb]
    exact GlobalTheory.T.besselPeriodCorankOne_simultaneous_rightTranslate W M hM _ (hφ _) _ (hmem _) _
  · intro u hu w x₁ y₁ hy
    show Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ y₁))) = _ * Bplus W M _ (F' (PiTensorProduct.tprod ℂ (Function.update v τ x₁)))
    rw [hF1 u hu.1 x₁ y₁ hy]
    exact GlobalTheory.T.besselPeriodCorankOne_rightTranslate_unipotent W M hM _ _ (hmem _) _ (GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic D W.θ hθ _ G.besTop.e τ u hu)

end GlobalTheory.SepRows.SepProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpwardThetaLiftNeZeroOfLValueNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardThetaLift_ne_zero_of_lValue_ne_zero : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → ZetaNe D → UpNe D := by
  first | exact @GlobalTheory.EvenOnto.upNe_of_heckeForm | exact GlobalTheory.EvenOnto.upNe_of_heckeForm | (intros; apply GlobalTheory.EvenOnto.upNe_of_heckeForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecIsThetaFunO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vec_isThetaFunO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (S.Z.vec d) := by
  intro D T L sc G W U S t p hp d hd
  have hIn : p.InRange D.R.m := by
    have hn := hp.nodes
    cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega
  exact GlobalTheory.LastVertexInv.vec_theta S hp hIn d hd

end GlobalTheory.TopZeroInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecIsThetaFunOAlt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VecThetaDef

theorem vec_isThetaFunO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U} (Z : Normal W N)
    {t : T} {p : Pair T} (d : FinDatum G t p), DefPair D.R.m p → p.InRange D.R.m → Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) := by
  intro D T L sc G W U N Z t p d hp hIn h
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf]
  exact (W.om_is p hIn).om_pres _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf (Z.vac_is p hp).2.theta)

end GlobalTheory.VecThetaDef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColConv

theorem col_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t j hj Φ hΦ φ hφ h
  obtain ⟨hν, h𝓕⟩ := measX_haar_fd hG j hj.le
  exact thetaKO_mul_cusp_integrableOn_fst hPr.cuspRapidDecay (hG.arrows.col t j hj).weil hR.inf hν h𝓕 hΦ hφ.1 hφ.2.1 h

end GlobalTheory.ColConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelThirdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_theta_level_third : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsCuspFun (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @GlobalTheory.ColCuspDefinite.isCuspFun_col_lift | exact GlobalTheory.ColCuspDefinite.isCuspFun_col_lift | (intros; apply GlobalTheory.ColCuspDefinite.isCuspFun_col_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Kronecker

noncomputable section

namespace GlobalTheory.FockRealNeg

theorem gramAt_negSp {D : D7} (S : HSp D) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.ChiGrid.negSp S) τ = -gramAt D S τ := by
  unfold gramAt
  rw [GlobalTheory.ChiGrid.negSp_gram, Matrix.map_neg _ (map_neg _)]

theorem isCartanInv_neg_one {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G 1) :
    IsCartanInv (-G) (-1) := by
  obtain ⟨-, -, h3⟩ := h
  refine ⟨by simp, by simp, ?_⟩
  simpa using h3

theorem detPlus_neg_one_one {m n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus (-1) 1 a b = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  have e : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (-1 : Matrix (Fin n) (Fin n) ℂ)ᵀ = -1 := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  have e2 : (1 / 2 : ℂ) • ((1 + -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * (b ⊗ₖ aᵀ)) +
      (1 / 2 : ℂ) • (1 - -1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) = 1 := by
    rw [add_neg_cancel, Matrix.zero_mul, smul_zero, zero_add, sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num
  rw [e, e2, Matrix.det_one]

end GlobalTheory.FockRealNeg

namespace GlobalTheory.FockRealNeg

theorem om_pureTensorO_neg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D (GlobalTheory.ChiGrid.negSp S) × GA D T →* Module.End ℂ (WO (GlobalTheory.ChiGrid.negSp S) T → ℂ)), IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS χT om → IsInfFam θ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (e₂ τ : ℚ) = -(b τ - (T.rank : ℚ) / 2)) → ∀ f, IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → (∀ τ, IsFockVacAt (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) θ τ (cplxO (-1) 1) f) → ∀ g ∈ GinfC (GlobalTheory.ChiGrid.negSp S), ∀ h ∈ GinfC T, ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, om (g, h) (pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f P) = (∏ τ, (compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g)).det ^ e₂ τ * (compAt θ τ (Formalism.L2.Theta.mt T h)).det ^ e₁ τ) • pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ).map (starRingEnd ℂ)) (fun τ => ((((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  intro D ψ θ S T χS χT om hom hθ BS BT hBS hBT a b ha hb e₁ e₂ he₁ he₂ f hf hv g hg h hh P
  have hS1 : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBS τ)
  have hT1 : ∀ τ, IsCartanInv (gramAt D T τ) 1 := fun τ => GlobalTheory.FockCompactAction.isCartanInv_one (hBT τ)
  have hSn : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.ChiGrid.negSp S) τ) (-1) := fun τ => by
    rw [gramAt_negSp]; exact isCartanInv_neg_one (hS1 τ)
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (GlobalTheory.ChiGrid.negSp S) (fun τ => hdet (hSn τ)) g hg
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ T (fun τ => hdet (hT1 τ)) h hh
  have c1 : ∀ τ, (fun _ => (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) τ *
      compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) =
      compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * (fun _ => (-1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) τ :=
    fun τ => by simp
  have c2 : ∀ τ, (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ * compAt θ τ (Formalism.L2.Theta.mt T h) =
      compAt θ τ (Formalism.L2.Theta.mt T h) * (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) τ :=
    fun τ => by simp
  have hvac := GlobalTheory.WeilVacChar.vacuum_character D ψ hom.std (GlobalTheory.ChiGrid.negSp S) T θ hθ χS χT om η hη hom
    (fun _ => -1) (fun _ => 1) hSn hT1 g hg h hh c1 c2 x y hx hy f hf hv
  have b1 : ∀ τ, BS τ * (BS τ)⁻¹ = 1 := fun τ => by
    have hB : BS τ * ((BS τ)ᴴ * gramAt D S τ) = 1 := mul_eq_one_comm.1 (hBS τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have b2 : ∀ τ, BT τ * (BT τ)⁻¹ = 1 := fun τ => by
    have hB : BT τ * ((BT τ)ᴴ * gramAt D T τ) = 1 := mul_eq_one_comm.1 (hBT τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have hneg := GlobalTheory.T.fockVector_negSpace_frameChange_conjSubst D ψ θ S T hom.std hθ BS
    (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ) BT
    (fun τ => (BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ) f hf P
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (GlobalTheory.ChiGrid.negSp S) T χS χT om hom hθ (fun _ => -1) (fun _ => -1) BS
      (fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp S) g) * BS τ))
      (fun _ => 1) (fun _ => 1) BT (fun τ => BT τ * ((BT τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ)) g h c1 c2
      (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b1, Matrix.one_mul])
      (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b2, Matrix.one_mul]) f hf P).2,
    hvac, GlobalTheory.FockCompactAction.pureTensorO_smul, hneg]
  congr 1
  simp only [detPlus_neg_one_one, Finset.prod_const_one, mul_one]
  have hx' : ∀ τ, HasInfExp D (χT * (η ^ T.rank)⁻¹) τ ((-e₂ τ : ℤ) : ℚ) := fun τ => by
    have e : ((-e₂ τ : ℤ) : ℚ) = b τ - (T.rank : ℚ) / 2 := by push_cast; rw [he₂]; ring
    rw [e]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (hb τ) (hη.2.2.2 τ) _
  have hy' : ∀ τ, HasInfExp D (χS * (η ^ (GlobalTheory.ChiGrid.negSp S).rank)⁻¹) τ ((e₁ τ : ℤ) : ℚ) := fun τ => by
    rw [he₁]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (ha τ) (hη.2.2.2 τ) _
  rw [Circle.coe_mul, Circle.coe_inv, hxv _ (fun τ => -e₂ τ) hx', hyv _ e₁ hy', ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [_root_.zpow_neg, inv_inv]

end GlobalTheory.FockRealNeg
end
end

