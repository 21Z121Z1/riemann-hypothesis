import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0140
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousBdGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFramesStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ y, IsUnitFr X y → y ∈ X.dom) ∧ (∀ x ∈ X.dom, ∃ y, IsUnitFr X y ∧ ∃ b ∈ Bor X.Ψ r, x = rmul y b) ∧ (∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, IsUnitFr X (rmul y b) → ∃ t : X.Ψ → Fin r → ℝ, b = (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom) ∧ (∀ y, IsUnitFr X y → ∀ γ ∈ X.Γ, IsUnitFr X (lact γ y)) ∧ (∀ y, IsUnitFr X y → ∀ Z ∈ unitLie X, IsUnitFr X (rmul y (expFr Z))) ∧ ∀ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, P (rmul y b) = bchar la b * P y → X.pnorm la P (rmul y b) = ‖P y‖ := by
  first | exact @GlobalTheory.FlagGS.gram_schmidt_frames | exact GlobalTheory.FlagGS.gram_schmidt_frames | (intros; apply GlobalTheory.FlagGS.gram_schmidt_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSchrodingerLinePureTensorZero
section
namespace SchrodingerLinePhase
section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SchrLine

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = fun x : InfiniteAdeleRing F =>
      ((fun v : {w : InfinitePlace F // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
    funext fun x => InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [h]
  exact Continuous.prodMk
    (continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1))
    (continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1))

def arch : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstA F).toRingHom

theorem arch_apply (x : AF F) : arch x = InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := rfl

theorem continuous_arch : Continuous (arch : AF F → mixedEmbedding.mixedSpace F) := by
  have h : (arch : AF F → mixedEmbedding.mixedSpace F) =
      fun x => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := funext fun x => arch_apply x
  rw [h]
  exact continuous_toMixed.comp continuous_fst

def coord (hF : IsTotallyReal F) (w : InfinitePlace F) : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (⟨w, hF.isReal w⟩ : {w : InfinitePlace F // w.IsReal})).comp
    (ContinuousLinearMap.fst ℝ _ _)

theorem re_eq_coord (hF : IsTotallyReal F) (x : Ainf F) (w : InfinitePlace F) :
    re x w = coord hF w (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  have h1 : re x w = (InfinitePlace.Completion.extensionEmbedding w (x w)).re := rfl
  have h2 : coord hF w (InfiniteAdeleRing.ringEquiv_mixedSpace F x) =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w) (x w) := rfl
  rw [h1, h2, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hF.isReal w), Complex.ofReal_re]

theorem arch_line {M : ℝ →+ VA F N} (hM : IsRealLine M) (p : VA F N →+ AF F) (hp : Continuous p) (s : ℝ) :
    arch (p (M s)) = s • arch (p (M 1)) := by
  let f : ℝ →+ mixedEmbedding.mixedSpace F := ((arch (F := F)).toAddMonoidHom).comp (p.comp M)
  have hf : Continuous f := continuous_arch.comp (hp.comp hM.1)
  have h := map_real_smul f hf s 1
  rw [smul_eq_mul, mul_one] at h
  exact h

theorem arch_fst {M : ℝ →+ VA F N} (hM : IsRealLine M) (l : Fin N) (s : ℝ) :
    arch ((M s).1 l) = s • arch ((M 1).1 l) :=
  arch_line hM ((Pi.evalAddMonoidHom (fun _ : Fin N => AF F) l).comp (AddMonoidHom.fst _ _))
    (by show Continuous (fun u : VA F N => u.1 l); exact (continuous_apply l).comp continuous_fst) s

theorem arch_snd {M : ℝ →+ VA F N} (hM : IsRealLine M) (l : Fin N) (s : ℝ) :
    arch ((M s).2 l) = s • arch ((M 1).2 l) :=
  arch_line hM ((Pi.evalAddMonoidHom (fun _ : Fin N => AF F) l).comp (AddMonoidHom.snd _ _))
    (by show Continuous (fun u : VA F N => u.2 l); exact (continuous_apply l).comp continuous_snd) s

def phaseForm (hF : IsTotallyReal F) (lam : InfinitePlace F → ℝ) (B : Fin N → mixedEmbedding.mixedSpace F) :
    (Fin N → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  ∑ w, ∑ l, (lam w * coord hF w (B l)) • (coord hF w).comp (ContinuousLinearMap.proj l)

theorem phaseForm_apply (hF : IsTotallyReal F) (lam : InfinitePlace F → ℝ)
    (B q : Fin N → mixedEmbedding.mixedSpace F) :
    phaseForm hF lam B q = ∑ w, lam w * ∑ l, coord hF w (q l) * coord hF w (B l) := by
  simp only [phaseForm, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem re_fstA_eq_coord_arch (hF : IsTotallyReal F) (u : AF F) (w : InfinitePlace F) :
    re (fstA F u) w = coord hF w (arch u) := by
  first | (rw [re_eq_coord hF, arch_apply]; rfl) | rw [re_eq_coord hF, arch_apply]

theorem phase_line [Invertible (2 : AF F)] (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ}
    {lam : InfinitePlace F → ℝ} (hlam : IsLam ψ lam) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (z : Fin N → AF F) (s : ℝ) :
    ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((s * phaseForm hF lam (fun l => arch ((M 1).2 l)) (fun l => arch (z l)) +
          s ^ 2 * ∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w *
            ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) : ℝ) : ℂ)) := by
  haveI : IsTotallyReal F := hF
  have hy0 : ∀ l, sndA F ((M s).2 l) = 0 := fun l => congrFun (hM.2 s).2 l
  have hsnd : sndA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) = 0 := by
    simp only [dotProduct, map_add, map_mul, map_sum, hy0, mul_zero, Finset.sum_const_zero, add_zero]
  have e1 : ∀ w, re (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) w =
      s * ∑ l, coord hF w (arch (z l)) * coord hF w (arch ((M 1).2 l)) +
        s ^ 2 * (coord hF w (arch ⅟(2 : AF F)) *
          ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) := by
    intro w
    have hxs : ∀ l, arch ((M s).1 l) = s • arch ((M 1).1 l) := fun l => arch_fst hM l s
    have hys : ∀ l, arch ((M s).2 l) = s • arch ((M 1).2 l) := fun l => arch_snd hM l s
    simp only [dotProduct, map_add, map_mul, map_sum, re_add, re_mul, re_sum, re_fstA_eq_coord_arch hF, hxs, hys,
      map_smul, smul_eq_mul]
    first
      | (simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
         refine Finset.sum_congr rfl fun l _ => ?_
         ring)
      | (have h1 : ∑ l, coord hF w (arch (z l)) * (s * coord hF w (arch ((M 1).2 l))) =
            s * ∑ l, coord hF w (arch (z l)) * coord hF w (arch ((M 1).2 l)) := by
           rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
         have h2 : ∑ l, s * coord hF w (arch ((M 1).1 l)) * (s * coord hF w (arch ((M 1).2 l))) =
            s ^ 2 * ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l)) := by
           rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
         rw [h1, h2]
         ring)
  have key : ∑ w, lam w * re (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) w =
      s * phaseForm hF lam (fun l => arch ((M 1).2 l)) (fun l => arch (z l)) +
        s ^ 2 * ∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w *
          ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) := by
    have hms : ∀ (c : ℝ) (h : InfinitePlace F → ℝ), c * ∑ w, h w = ∑ w, c * h w :=
      fun c h => Finset.mul_sum _ _ _
    rw [phaseForm_apply, hms s, hms (s ^ 2), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [e1, re_fstA_eq_coord_arch hF]
    ring
  calc ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))
      = ψ (pairA F (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) 0) := by
        first | (rw [← hsnd]; rfl) | rw [← hsnd]
    _ = _ := by
        have h2 := hlam.2 (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)))
        rw [key] at h2
        exact h2

private theorem hasDerivAt_exp_quadratic_mul_schwartz_line_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (q v : E) (a b : ℝ) (c : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((s * a + s ^ 2 * b : ℝ) : ℂ)) *
        (f (q + s • v) * c))
      ((2 * Real.pi * Complex.I * a * f q + fderiv ℝ f q v) * c) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s * a + s ^ 2 * b) a 0 := by
    have h := ((hasDerivAt_id' (0:ℝ)).mul_const a).add (((hasDerivAt_id' (0:ℝ)).pow 2).mul_const b)
    first
      | exact h.congr_deriv (by simp)
      | (convert h using 1 <;> simp)
  have h3 := (h1.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hl : HasDerivAt (fun s : ℝ => q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add q
  have hf0 : HasFDerivAt (⇑f) (fderiv ℝ f q) (q + (0:ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact f.hasFDerivAt q
  have h4 := (hf0.comp_hasDerivAt (0:ℝ) hl).mul_const c
  have h5 := h3.mul h4
  convert h5 using 1
  all_goals first
    | rfl
    | (simp only [Function.comp_apply]; done)
    | (simp; done)
    | (simp; ring)
    | (funext s; simp [Function.comp_apply])

end GlobalTheory.CompanionTheory.SchrLine

open GlobalTheory.CompanionTheory.SchrLine in

theorem GlobalTheory.CompanionTheory.SchrLine.exists_hasDerivAt_schr_pureA :
    ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F →
    IsCharAF F ψ → ∀ M : ℝ →+ VA F N, IsRealLine M →
    ∀ (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (Fin N → FiniteAdeleRing (𝓞 F) F) →
    ∃ f' : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ z : Fin N → AF F,
      HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) (GlobalTheory.WeilM.pureA F f' g z) 0 := by
  intro F _ _ N _ ψ hF hψ M hM f g hg
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hψ
  let L : (Fin N → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) •
      (Complex.ofRealCLM.comp (phaseForm hF lam (fun l => arch ((M 1).2 l))))
  let v : Fin N → mixedEmbedding.mixedSpace F := fun l => arch ((M 1).1 l)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (⇑L) f + LineDeriv.lineDerivOp v f, fun z => ?_⟩
  let q : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
  let zf : Fin N → FiniteAdeleRing (𝓞 F) F := fun i => (z i).2
  have hfun : ∀ s : ℝ, GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z =
      Complex.exp (2 * Real.pi * Complex.I * ((s * GlobalTheory.CompanionTheory.SchrLine.phaseForm hF lam (fun l => GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).2 l)) (fun l => GlobalTheory.CompanionTheory.SchrLine.arch (z l)) + s ^ 2 * (∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w * ∑ l, GlobalTheory.CompanionTheory.SchrLine.coord hF w (GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).1 l)) * GlobalTheory.CompanionTheory.SchrLine.coord hF w (GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).2 l)))) : ℝ) : ℂ)) *
        (f (q + s • v) * g zf) := by
    intro s
    have hq : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + (M s).1) i).1) = q + s • v := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (z i + (M s).1 i)) = q i + s • v i
      rw [map_add, map_add]
      first
        | exact congrArg₂ (· + ·) rfl (arch_fst hM i s)
        | (congr 1; exact arch_fst hM i s)
    have hz : (fun i => ((z + (M s).1) i).2) = zf := by
      funext i
      show sndA F (z i + (M s).1 i) = (z i).2
      rw [map_add, show sndA F ((M s).1 i) = 0 from congrFun (hM.2 s).1 i]
      exact add_zero _
    show ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) *
        (f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + (M s).1) i).1) *
          g (fun i => ((z + (M s).1) i).2)) = _
    rw [phase_line hF hlam hM z s, hq, hz]
  rw [show (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) = _ from funext hfun]
  refine (hasDerivAt_exp_quadratic_mul_schwartz_line_zero f q v _ _ (g zf)).congr_deriv ?_
  show _ = (SchwartzMap.smulLeftCLM ℂ (⇑L) f + LineDeriv.lineDerivOp v f) q * g zf
  rw [SchwartzMap.add_apply, SchwartzMap.smulLeftCLM_apply_apply L.hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  first
    | rfl
    | (simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply, smul_eq_mul]; rfl)
    | (simp [L, smul_eq_mul]; ring)

end
end

end SchrodingerLinePhase
section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical
theorem _root_.GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin N → FiniteAdeleRing (𝓞 F) F) → ∃ f' : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ z : Fin N → AF F, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) (GlobalTheory.WeilM.pureA F f' g z) 0 :=
  SchrodingerLinePhase.GlobalTheory.CompanionTheory.SchrLine.exists_hasDerivAt_schr_pureA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSobolevContinuousOrbit
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobOrbit

theorem hasDerivAt_sobCont_orbit : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π ℓ → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, HasDerivAt (fun t : ℝ => ℓ (π (NormedSpace.exp (t • X)) v)) (ℓ (dRep π X v)) 0 :=
  fun _ _ _ _ _ _ _ hu hπ _ hv _ hℓ _ hX =>
    (GlobalTheory.UnitarySmVec.smFam_orbit hu hπ hv hX).hasDerivAt_form hu hπ hℓ

end GlobalTheory.SobOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.CMSplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ₁ : E →+* ℂ) :
    ∃ g : E ≃ₐ[ℚ] E, ∀ x, τ₀ (g x) = τ₁ x := by
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    show algebraMap ℚ ℂ q = τ₀ (algebraMap ℚ E q)
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact ⟨(τ₁.toRatAlgHom).restrictNormal' E, fun x => (τ₁.toRatAlgHom).restrictNormal_commutes E x⟩

theorem not_isOfFinOrder_val_of_tame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (hgal : IsGalois ℚ E) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (χ : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ) (ht : ∀ v, χ.TameAt v) (hinf : χ.HasInf (fun w => (τ w).1) n)
    (hn : ∀ w, n w ≠ 0) (p : ℕ) (hp : p.Prime) (W : HeightOneSpectrum (𝓞 E)) (hN : Ideal.absNorm W.asIdeal = p)
    (hsq : (p : 𝓞 E) ∉ W.asIdeal ^ 2) : ¬ IsOfFinOrder (χ.val W) := by
  intro hfin
  classical
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht W (Formalism.L2.Host.unif W)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val W ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ₀ : E →+* ℂ := (τ w₀).1 with hτ₀
  choose g hg using fun w => exists_aut_comp τ₀ (τ w).1
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 = τ₀ (∏ w, (g w z / g w (σ z)) ^ n w) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : τ₀ (g w (σ z)) = starRingEnd ℂ (τ₀ (g w z)) := by
      rw [hg, hg]
      exact hcm.2.2.2 _ _
    have e' : (τ w).1 z = τ₀ (g w z) := (hg w z).symm
    have h0 : τ₀ (g w z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ w, (g w z / g w (σ z)) ^ n w) ^ a = 1 := by
    apply τ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := W) ha (by rw [h6, map_one])
  have hg0 : ∀ x, g w₀ x = x := fun x => τ₀.injective (hg w₀ x)
  have hres : ∀ w, (∀ f : F, τ₀ (algebraMap F E f) = w.embedding f) → w = w₀ := by
    intro w hw
    have e : w.embedding = w₀.embedding := by
      ext f
      rw [← hw f]
      exact (RingHom.congr_fun (τ w₀).2 f)
    rw [← InfinitePlace.mk_embedding w, e, InfinitePlace.mk_embedding]
  have hc : ∀ w, W.valuation E (g w (σ z)) = 1 := by
    intro w
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 ((g w : E →+* E).comp (σ : E →+* E)) fun e => ?_
    have hw : w = w₀ := hres w fun f => by
      have := RingHom.congr_fun e (algebraMap F E f)
      change g w (σ (algebraMap F E f)) = algebraMap F E f at this
      rw [← this, hg, AlgHom.commutes]
      exact RingHom.congr_fun (τ w).2 f
    subst hw
    obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
    have := RingHom.congr_fun e x
    change g w (σ x) = x at this
    rw [hg0] at this
    exact hx this
  have hgw : ∀ w, w ≠ w₀ → W.valuation E (g w z) = 1 := by
    intro w hw
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 (g w : E →+* E) fun e => hw (hres w fun f => ?_)
    have := RingHom.congr_fun e (algebraMap F E f)
    change g w (algebraMap F E f) = algebraMap F E f at this
    rw [← this, hg]
    exact RingHom.congr_fun (τ w).2 f
  rw [map_prod, Finset.prod_eq_single w₀ (fun w _ h => by rw [map_zpow₀, map_div₀, hgw w h, hc w, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hg0, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn w₀ h
  · omega
  · omega

end GlobalTheory.CMSplitValue

namespace GlobalTheory.CMSplitValue

theorem not_isOfFinOrder_val : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → IsGalois ℚ E → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ), H.HasInf (fun w => (τ w).1) n → (∀ w, n w ≠ 0) → ∀ (p : ℕ), p.Prime → ∀ W : HeightOneSpectrum (𝓞 E), Ideal.absNorm W.asIdeal = p → (p : 𝓞 E) ∉ W.asIdeal ^ 2 → ¬ IsOfFinOrder (H.val W) := by
  intro F E _ _ _ _ _ σ hcm hgal τ H n hinf hn p hp W hN hsq hfin
  obtain ⟨N, hN0, hunr⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt E H
  have ht : ∀ v, (H ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (H ^ N).HasInf (fun w => (τ w).1) (fun w => (N : ℤ) * n w) := by
    intro k
    rw [GlobalTheory.SplitValuePow.inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  refine not_isOfFinOrder_val_of_tame F E σ hcm hgal τ (H ^ N) _ ht hinf'
    (fun w => mul_ne_zero (by exact_mod_cast hN0.ne') (hn w)) p hp W hN hsq ?_
  rw [GlobalTheory.SplitValuePow.val_pow]
  exact hfin.pow

end GlobalTheory.CMSplitValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEqStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_congr_of_positiveIndex_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian), A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB → ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  first | exact @GlobalTheory.HermCongruence.congr_of_sigPosH_eq | exact GlobalTheory.HermCongruence.congr_of_sigPosH_eq | (intros; apply GlobalTheory.HermCongruence.congr_of_sigPosH_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOneStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianForm_neg_on_orthogonal_of_positiveIndex_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  first | exact @GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one | exact GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one | (intros; apply GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianOneByOneIsScalar
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

theorem gl_one_conj {R : Type} [CommRing R] (x a : GL (Fin 1) R) : x * a * x⁻¹ = a := by
  have hc : x * a = a * x := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  rw [hc, mul_inv_cancel_right]

theorem toQr_fst_entry {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (r : ℕ) (z : Gr G r) (w : P.cent) :
    (((P.toQr r z w).1 : GL (Fin 1) (Qr p r)) : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 =
      algebraMap ℚ_[p] (Qr p r) ((((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])) := by
  simp only [Pair.toQr, carry, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype, Prod.fst_mul, Prod.fst_inv]
  rw [gl_one_conj]
  have e1 : (locC G w).1 = Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom (w : G.Cˣ × ℚˣ).2 := rfl
  have e2 : ((inclG G r) ((locC G) ↑w)).1 =
      GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom (locC G w).1) := rfl
  rw [e2, e1]
  simp [GeneralLinearGroup.scalar]

theorem sim_norm_le_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r)
    (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) →
    ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom →
      ‖(((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  intro p _ G P r z K g _ hK w hw
  obtain ⟨m, hm0, hmem⟩ := exists_pow_mem_conj K (KHT p G.m G.n r G.Fw) g _ hK hw
  rw [← map_pow] at hmem
  obtain ⟨k, hk, hkeq⟩ := hmem
  have hk1 : k.1 = (P.toQr r z (w ^ m)).1 := by
    have h := congrArg Prod.fst hkeq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Prod.fst_mul, Prod.fst_inv] at h
    rw [← h, gl_one_conj]
  have hent := toQr_fst_entry P r z (w ^ m)
  rw [← hk1] at hent
  obtain ⟨M, hM⟩ := (Subgroup.mem_prod.1 hk).1
  have h00 : (((M : Matrix (Fin 1) (Fin 1) _) 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) r) : Qr p r) =
      ((k.1 : GL (Fin 1) (Qr p r)) : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 := by
    rw [← hM]; rfl
  have hO : algebraMap (Qr p r) (PadicAlgCl p)
      (((M : Matrix (Fin 1) (Fin 1) _) 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) r) : Qr p r) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p :=
    ((M : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) r)) 0 0).2
  rw [h00, hent, ← IsScalarTower.algebraMap_apply, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff,
    PadicAlgCl.norm_extends] at hO
  have hpow : ((((w ^ m : P.cent) : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p]) = ((((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])) ^ m := by
    push_cast; rfl
  rw [hpow, norm_pow] at hO
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 hO

end GlobalTheory.StabFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPointsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧ Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range := by
  first | (exact @GlobalTheory.LKMid.SigIter.main) | (exact GlobalTheory.LKMid.SigIter.main) | (intros; apply GlobalTheory.LKMid.SigIter.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPointStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTripleTrivializations_differ_by_group_point : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (x x' : (R ⊗[ℚ] G.C)ˣ) (t t' : Rˣ), Triv G R β x t → Triv G R β x' t' → ∃ g : UPts G.star R, (g : (R ⊗[ℚ] G.C)ˣ × Rˣ).1 = x' * x⁻¹ := by
  first | (exact @GlobalTheory.LKMid.triv_quot) | (exact GlobalTheory.LKMid.triv_quot) | (intros; apply GlobalTheory.LKMid.triv_quot  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90TensorPadicUnramifiedExtensionStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_of_frobenius_norm_one_tensor_Qr : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ (B : Type) [CommRing B] [Algebra ℚ_[p] B] [Module.Finite ℚ_[p] B] (a : (B ⊗[ℚ_[p]] Qr p r)ˣ), nrmG (Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom) r a = 1 → ∃ g : (B ⊗[ℚ_[p]] Qr p r)ˣ, a = g⁻¹ * Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom g := by
  first | (exact @GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic) | (exact GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic) | (intros; apply GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbeddingStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicShape_integralWeight_goodEmbedding : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → HolShape (R.MW i σ) ∧ (∀ ρ, nNeg ((R.MW i σ).ε ρ) = (D.R.sigW ((i : ℕ) + 1)).2) ∧ ∃ w, WtIs (R.MW i σ) w := by
  first | exact @GlobalTheory.HolDict.holShape_of_good | exact GlobalTheory.HolDict.holShape_of_good | (intros; apply GlobalTheory.HolDict.holShape_of_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelDirectionsIntegralBasisUnramifiedPrimeStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_directions_integral_basis_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), UnramIn E p → ∀ [DecidableEq (Lt1 Dw)], ∃ L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C, (∀ a b, IsIntV (vX_vp X) (L a b)) ∧ L * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 ∧ (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1 := by
  first | exact @GlobalTheory.PrimePart.exists_integral_inverse_lieVec | exact GlobalTheory.PrimePart.exists_integral_inverse_lieVec | (intros; apply GlobalTheory.PrimePart.exists_integral_inverse_lieVec <;> assumption)
end

