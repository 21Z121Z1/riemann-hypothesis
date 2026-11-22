import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntOfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0512
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0522
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0528
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.TFlatFam

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}

theorem om_split (s : StepFB ψ J B) (a : GA D J.W) (h : GA D B.V) (Φ : WO J.W B.V → ℂ) :
    s.om (a, h) Φ = s.om (a, 1) (s.om (1, h) Φ) := by
  have e : ((a, h) : GA D J.W × GA D B.V) = (a, 1) * (1, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]

theorem tFlat_eq_pairKer (hD : Descent D) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank)
    (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ) (hΦ : IsThetaFunO ψ J.W B.V Φ) (h₀ : GA D J.W₀)
    (h : GA D B.V) :
    tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) = pairKer s vL Y (flatFB s (s.om (1, h) Φ)) h₀ 1 := by
  have hc := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ _ hΦ) h₀ 1
  rw [(embA B.d B.o).map_one, ← om_split] at hc
  have h1 : B.o.emb ((1 : GA D B.A), (1 : GA D B.L)) = 1 := B.o.emb.map_one
  rw [h1] at hc
  unfold tFlat pairKer
  rw [hc, h1]

theorem symplOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

theorem star_psi_mul (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : star (ψ a) * ψ a = 1 := by
  have h := Complex.conj_mul' (ψ a)
  rw [hψ.1.2.1 a] at h
  simpa using h

theorem pair_periodic (hψ : IsStdChar D ψ (-1)) (o : OrthDec B.V₀ B.A B.L) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) (y : WO J.W₀ B.L → ℂ)
    (hy : ∀ γ w, y (ratW B.L J.W₀ γ + w) = ψ (-(symplOH J.W₀ B.L (ratW B.L J.W₀ γ) w)) * y w)
    (γ : Mx D B.L.rank J.W₀.rank) (hγ : γ ∈ ratMx D B.L.rank J.W₀.rank) (v : Mx D B.L.rank J.W₀.rank) :
    Ξ ((o.resT J.W₀).symm (0, γ + v)) * star (y (γ + v)) = Ξ ((o.resT J.W₀).symm (0, v)) * star (y v) := by
  obtain ⟨γ₀, rfl⟩ := mem_ratMx.1 hγ
  have hmem : (o.resT J.W₀).symm (0, rat γ₀) ∈ ratL B.V₀ J.W₀ := by
    rw [o.mem_ratL_resT, AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, ⟨γ₀, rfl⟩⟩
  obtain ⟨g₀, hg₀⟩ := hmem
  have hg : ratW B.V₀ J.W₀ g₀ = (o.resT J.W₀).symm (0, rat γ₀) := hg₀
  have hsplit : (o.resT J.W₀).symm (0, rat γ₀ + v) = ratW B.V₀ J.W₀ g₀ + (o.resT J.W₀).symm (0, v) := by
    rw [hg, ← map_add, Prod.mk_add_mk, zero_add]
  have hsym : symplOH J.W₀ B.V₀ (ratW B.V₀ J.W₀ g₀) ((o.resT J.W₀).symm (0, v)) =
      symplOH J.W₀ B.L (ratW B.L J.W₀ γ₀) v := by
    rw [hg, o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]
    rfl
  have hy' := hy γ₀ v
  have hrat : ratW B.L J.W₀ γ₀ = rat γ₀ := rfl
  rw [hrat] at hy'
  rw [hsplit, hΞ.quasi, hsym, hy', hrat, star_mul']
  calc ψ (-symplOH J.W₀ B.L (rat γ₀) v) * Ξ ((o.resT J.W₀).symm (0, v)) *
        (star (ψ (-symplOH J.W₀ B.L (rat γ₀) v)) * star (y v))
      = (star (ψ (-symplOH J.W₀ B.L (rat γ₀) v)) * ψ (-symplOH J.W₀ B.L (rat γ₀) v)) *
        (Ξ ((o.resT J.W₀).symm (0, v)) * star (y v)) := by ring
    _ = _ := by rw [star_psi_mul hψ, one_mul]

end GlobalTheory.Unf.FB.TFlatFam

namespace GlobalTheory.Unf.FB.TFlatFam

theorem flatFB_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (Ψ : WO J.W B.V → ℂ) :
    flatFB s Ψ = flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (x0 B) 0 Ψ := rfl

theorem tFlat_eq_int {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) :
    tFlat s vL y Ψ = ∫ v in vL.𝓕, flatFB s Ψ ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := rfl

theorem main : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → IsThetaFunO ψ J.W B.V Φ → (Continuous fun p : GA D J.W₀ × GA D B.V => tFlat s vL (Y p.1) (s.om (J.d.emb0 p.1, p.2) Φ)) ∧ (∀ γ ∈ GQ J.W₀, ∀ h₀ h, tFlat s vL (Y (γ * h₀)) (s.om (J.d.emb0 (γ * h₀), h) Φ) = tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ∧ ∀ h, handFB s vL Y (flatFB s (s.om (1, h) Φ)) 1 = ∫ h₀ in J.v0.𝓕, tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
  intro D hD ψ σ J B s vL Y Φ hY hΦ
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hflat : ∀ h, IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (1, h) Φ)) := fun h =>
    (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hxo, hx⟩ := GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B
    have hfl := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x hxo.1 Φ hΦ
    rw [hx] at hfl
    let f : Mx D B.L.rank J.W₀.rank × (GA D J.W₀ × GA D B.V) →
        (GA D J.W × GA D B.V) × Mx D J.W₀.rank σ × WO J.W₀ B.V₀ :=
      fun vp => ((J.d.emb0 vp.2.1, vp.2.2), ((0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, vp.1)))
    have hf : Continuous f :=
      ((J.d.continuous_embed.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)).prodMk (continuous_const.prodMk
          ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_fst)))
    have h1 := hfl.comp hf
    let K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.V → ℂ := fun v p =>
      flatFB s (s.om (J.d.emb0 p.1, p.2) Φ) ((B.o.resT J.W₀).symm (0, v)) * star (Y p.1 v)
    have h2 : Continuous fun vp : Mx D B.L.rank J.W₀.rank × (GA D J.W₀ × GA D B.V) => star (Y vp.2.1 vp.1) :=
      continuous_star.comp (hY.cont.comp ((continuous_fst.comp continuous_snd).prodMk continuous_fst))
    have hKc : Continuous (Function.uncurry K) := by
      have e : Function.uncurry K = fun vp => (fun q : (GA D J.W × GA D B.V) × Mx D J.W₀.rank σ × WO J.W₀ B.V₀ =>
          flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (x0 B) q.2.1 (s.om q.1 Φ) q.2.2) (f vp) *
          star (Y vp.2.1 vp.1) := by
        funext vp
        simp only [Function.uncurry, K, f, flatFB_eq]
      rw [e]
      exact h1.mul h2
    have hKp : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ v p, K (γ + v) p = K v p := by
      intro γ hγ v p
      have hΞ : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (J.d.emb0 p.1, p.2) Φ)) :=
        (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
      exact pair_periodic hψ B.o _ hΞ (Y p.1) (hY.quasi p.1) γ hγ v
    have hK := (GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D B.L.rank J.W₀.rank vL (GA D J.W₀ × GA D B.V) K hKc hKp).2.1
    simp only [tFlat_eq_int]
    exact hK
  · intro γ hγ h₀ h
    rw [tFlat_eq_pairKer hD s vL Y Φ hΦ, tFlat_eq_pairKer hD s vL Y Φ hΦ]
    exact (GlobalTheory.T.pairedThetaKernel_continuous_and_rationally_invariant D ψ σ J B s vL Y _ hY (hflat h)).2.1 γ hγ h₀ 1
  · intro h
    unfold handFB
    congr 1
    funext h₀
    exact (tFlat_eq_pairKer hD s vL Y Φ hΦ h₀ h).symm

end GlobalTheory.Unf.FB.TFlatFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairLattice
section
noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LineIdeal

section Loc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc NumberField GlobalTheory.AdelicU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem int_of_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : Af F ⊗[F] E)
    (h : ∀ w, Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) y ∈ intLoc F E w) :
    y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have hfg : (stdLattice E 1).FG := Submodule.fg_pi fun _ => by
    rw [← Submodule.one_eq_range]; exact Submodule.fg_unit 1
  have h1 : (fun _ : Fin 1 => y) ∈ latHat F E (stdLattice E 1 : Set _) :=
    (mem_latHat_iff hfg _).2 fun w => mem_latLoc_stdLattice.2 fun _ => h w
  generalize hA : AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} = A
  have hA' : ∀ a ∈ intAf F, ∀ x : 𝓞 E, a ⊗ₜ[F] (x : E) ∈ A := fun a ha x => hA ▸ AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩
  have key : latHat F E (stdLattice E 1 : Set _) ≤ A.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => Af F ⊗[F] E) 0) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, x, hx, rfl⟩
    obtain ⟨r, hr⟩ := hx 0 trivial
    change b ⊗ₜ[F] x 0 ∈ A
    rw [← hr]
    exact hA' b hb r
  exact key h1

theorem loc_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : Af F ⊗[F] E)
    (h : y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) (w) :
    Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) y ∈ intLoc F E w := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    exact tmul_mem_intLoc (hb w) x
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem exists_mulVec_iff {R : Type} [CommRing R] {n : ℕ} (M : GL (Fin n) R) (P : (Fin n → R) → Prop) (w : Fin n → R) :
    (∃ x, P x ∧ M.1 *ᵥ x = w) ↔ P ((M⁻¹).1 *ᵥ w) := by
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [← e, mulVec_mulVec, Units.inv_mul, one_mulVec]
  · exact fun H => ⟨_, H, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩

variable {D : D7}

theorem int_iff_loc {v : Pl D} {a : AE D} (ha : a ∈ idAt D (· = v)) :
    a ∈ intAt D (· = v) ↔ compAt D v a ∈ intLoc D.host.F D.host.E v := by
  refine ⟨fun h => loc_of_int _ h.2 v, fun h => ⟨ha, int_of_loc _ fun w => ?_⟩⟩
  by_cases e : w = v
  · subst e; exact h
  · have h0 : compAt D w a = 0 := compAt_of_idAt ha e
    change compAt D w a ∈ _
    rw [h0]
    exact zero_mem _

theorem line_loc (V : HSp D) (Λ : Lat V) (hΛ : Λ.FG) (v : Pl D) (g : GA D V) (y₀ : Fin V.rank → AE D)
    (h : ∀ a ∈ idAt D (· = v), mt V g⁻¹ *ᵥ (a • y₀) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ a ∈ intAt D (· = v))
    (c : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    (∃ x ∈ latLoc D.host.F Λ v, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v g)).1 *ᵥ x =
      c • vecLoc v (finPart D ∘ y₀)) ↔ c ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨a, ha, hc⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (n := 1) v fun _ => c
  have hc' : compAt D v (a 0) = c := congrFun hc 0
  have hs : ∀ i, (a 0 • y₀) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ (ha 0)
  have e : vecLoc v (finPart D ∘ (a 0 • y₀)) = c • vecLoc v (finPart D ∘ y₀) := by
    funext i
    rw [← hc']
    exact map_mul (compAt D v) (a 0) (y₀ i)
  have key : ∀ (g : GA D V) y, vecLoc v (finPart D ∘ (mt V g *ᵥ y)) =
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v g)).1 *ᵥ vecLoc v (finPart D ∘ y) := fun g y => by
    rw [GlobalTheory.FinPl.KOpen.fin_mulVec]
    exact vecLoc_mulVec D.sp.cm.sig V.gram v g _
  rw [← hc', ← int_iff_loc (ha 0), ← h _ (ha 0), hc',
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hΛ v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ _ hs), key, e, map_inv, map_inv]
  exact exists_mulVec_iff _ (· ∈ latLoc D.host.F Λ v) _

end Loc

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos

section Word

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}

theorem xu_fixes (hE : IdE X) (r : Fin D.R.rS) :
    mt (D.sp.Y 0) ((iotaX X h).symm (1, X.xu u)) *ᵥ ratV (fun k => X.ιE (X.eR r (Fin.cast (rank_eq X h) k))) =
      ratV fun k => X.ιE (X.eR r (Fin.cast (rank_eq X h) k)) := by
  have h1 := (GlobalTheory.Core.SBesLevi.transport_fix D X.B.I X.ιE hE h (rank_eq X h) {X.eR r}
    (Formalism.IndefR.RationalEmbedding.iota D ((iotaX X h).symm (1, X.xu u)))).1
  have e : castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D ((iotaX X h).symm (1, X.xu u))) = (1, X.xu u) :=
    (iotaX X h).apply_symm_apply _
  rw [e] at h1
  refine (GlobalTheory.Core.SBesLevi.bridge_fix D _ _).2 (h1 ⟨?_, ?_⟩ _ rfl)
  · exact one_mem _
  · rintro _ rfl
    exact (X.xu_fix u r).1

theorem first_vec (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (B : SBes X h u ψ (D.sp.X 0)) {μ : D.host.E} (hμ : μ ≠ 0)
    (hz : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) (r : Fin D.R.rS) (hr : r.1 = 0) :
    ∃ s : D.host.E, (s = 1 ∨ s = -1) ∧
      ∀ k, B.d.e k r = s * (μ * (X.B.g : D.host.E) ^ D.R.rS) * X.ιE (X.eR r (Fin.cast (rank_eq X h) k)) := by
  obtain ⟨lam, hl, H⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B', -, -, hz', he, -⟩ := H μ B.vA hμ
  have hne : ∀ B : SBes X h u ψ (D.sp.X 0), vecB B.o B.ζ ≠ 0 := fun B e => besVec_ne_zero B (by rw [e, mulVec_zero])
  have h1 := GlobalTheory.FirstVec.first_eq hψ B'.d B.d (funext fun k => (hz' k).trans (hz k).symm) (hne B') (hne B)
    (fun n => (B'.tieN n).trans (B.tieN n).symm)
    (fun n hn => star_injective ((B'.tieψ n hn).trans (B.tieψ n ((B.tieN n).2 ((B'.tieN n).1 hn))).symm)) r hr
  rcases hl with rfl | rfl
  · exact ⟨1, Or.inl rfl, fun k => by rw [h1, he, hr, Nat.sub_zero, one_mul]⟩
  · exact ⟨(-1) ^ D.R.rS, neg_one_pow_eq_or _ _, fun k => by rw [h1, he, hr, Nat.sub_zero, neg_pow]; ring⟩

end Word

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem single (W : RealPack ex) (hW : PkHyp W) (r : Fin D.R.rS) (hr : r.1 = 0) {u : D.what₂.Word} (f : FamCh W u)
    (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (hP : PlacedP f B) (a₀ a₁ : GA D (D.sp.X 0)) (x : GlobalTheory.FinPl.Pl D)
    (hg : ∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ x) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ x.asIdeal) {α cc : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), mt (D.sp.Y 0) (tOf f B a₀ a₁)⁻¹ *ᵥ (a •
      (((cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) : (AE D)ˣ) : AE D) *
        incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) •
      ratV fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) ∈ latV (D.sp.Y 0) ((pk W).ΛY 0) (· = x) ↔
      a ∈ intAt D (· = x) := by
  intro a ha
  obtain ⟨k, i1, i2, i3, i4, ι, v, o, n, G, pl, hc, -, ht, sh, -, -, hb, hp⟩ := hP
  obtain ⟨μ, lam, n1, n2, n3⟩ := hb.norm
  have hξ : -D.host.xi0 ^ (D.R.m / 2) ≠ 0 := neg_ne_zero.2 (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hμ : μ ≠ 0 := left_ne_zero_of_mul (n1 ▸ hξ)
  have hlam : lam ≠ 0 := right_ne_zero_of_mul (n1 ▸ hξ)
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.rS
    omega
  obtain ⟨s, hs, he⟩ := first_vec (F0 W u) (W.S.tr u) hW.bot.idE hc.std B hμ n2 r hr
  have hI := all_ideal hc sh (fun n h x hx => by subst h; exact hp x hx) (fun j hj => by
      change 0 < (D.sp.X (j + 1)).rank
      rw [Formalism.L2.Forms.rankN D _ hj]
      unfold Ranks.N
      have := D.R.m_add_three_le_k
      omega) hlam n3 (fun e => hx ((ht.tP x).1 e)) hα hψ 0 D.R.rS h₀ (D.R.rS - 1) r (by have := r.2; omega)
  have hd : B.d.e = (f.c.bes 0 D.R.rS h₀).d.e := eq_of_heq (Sigma.mk.inj (congrArg
    (fun Z : BesLev D D.R.rS => (⟨Z.V.rank, Z.d.e⟩ : Σ n, Matrix (Fin n) (Fin D.R.rS) D.host.E)) (hb.lev h₀))).2
  have hm := ht.moves 0 (by omega) (· = x) fun p hp e => by
    obtain ⟨PP, h1, h2⟩ := (ht.gP p).1 e
    exact hg PP h1 (h2.symm.trans hp)
  have hx1 := xu_fixes (h := W.Q.instEq) (u := u) hW.bot.idE r
  rw [← mul_assoc (α * α), ← mul_assoc (cc ^ _)] at hI
  generalize cc ^ (D.R.rS - 1) * (α * α * (α * (xiU D * cU α)⁻¹) ^ D.R.rS) = K at hI ⊢
  obtain ⟨ε, hε⟩ : ∃ ε : Fin (D.sp.Y 0).rank → D.host.E,
      (fun k => W.S.X.ιE (W.S.X.eR r (Fin.cast (rank_eq W.S.X W.Q.instEq) k))) = ε := ⟨_, rfl⟩
  have he' : ∀ k, B.d.e k r = s * (μ * (W.S.X.B.g : D.host.E) ^ D.R.rS) * ε k := fun k => by rw [he, ← hε]
  rw [hε] at hx1 ⊢
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> simp
  have hy : a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    funext k
    change a * (_ * incA D (ε k)) = _ * incA D (B.d.e k r)
    have : D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k = lam * -s * B.d.e k r := by
      rw [he']
      linear_combination ((W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * n1 + (lam * μ * (W.S.X.B.g : D.host.E) ^ D.R.rS * ε k) * hss
    have h2 := congrArg (incA D) this
    rw [map_mul, map_mul (incA D) (lam * -s), map_mul (incA D) lam] at h2
    linear_combination (a * K) * h2
  have hfix : mt (D.sp.Y 0) ((show GA D (D.sp.Y 0) from f.g.b 0) * (tOf f B a₀ a₁)⁻¹) *ᵥ
      (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) =
      colMul B.d.jX r ((K : AE D) * incA D lam * (incA D (-s) * a)) := by
    have e : (show GA D (D.sp.Y 0) from f.g.b 0) * (tOf f B a₀ a₁)⁻¹ =
        embA B.d B.o (a₀ * a₁)⁻¹ * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) := by
      unfold tOf
      rw [map_inv, _root_.mul_inv_rev, mul_inv_cancel_left, _root_.mul_inv_rev, inv_inv]
    rw [e, GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec, mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), mulVec_smul (mt _ ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))), hx1, hy]
    generalize (K : AE D) * incA D lam * (incA D (-s) * a) = t
    have e1 : colMul B.d.jX r t = B.d.jX *ᵥ Pi.single r t := by
      rw [mulVec_single]; funext k; exact mul_comm _ _
    rw [e1, mulVec_mulVec, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX]
  have hsup : ∀ i, (a • ((K : AE D) * incA D (D.host.xi0 ^ (D.R.m / 2) * (W.S.X.B.g : D.host.E) ^ D.R.rS)) • ratV ε) i ∈
      idAt D (· = x) := fun i => Ideal.mul_mem_right _ _ ha
  rw [GlobalTheory.MixModel.mt_mul, ← mulVec_mulVec] at hfix
  have hj : B.d.jX = (f.c.bes 0 D.R.rS h₀).d.jX := congrArg rat hd
  have h1 := hI ((K : AE D) * incA D lam * (incA D (-s) * a)) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha))
  rw [← inU_val lam hlam, ← Units.val_mul, Units.inv_mul_cancel_left, Units.val_mul, inU_val, ← hj] at h1
  refine (hm _ (GlobalTheory.FinPl.KOpen.supp_mulVec (D.sp.Y 0) _ _ hsup)).trans
    ((iff_of_eq (congrArg (· ∈ latV (D.sp.Y 0) (v.N 0) (· = x)) hfix)).trans (h1.trans ?_))
  rcases hs with rfl | rfl
  · rw [map_neg, map_one, neg_one_mul, int_neg]
  · rw [neg_neg, map_one, one_mul]

theorem common_line : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∃ w : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f B a₀ a))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) ∧ ((∃ x ∈ GlobalTheory.AdelicU.latLoc D.host.F ((pk W).ΛY 0) v, Matrix.mulVec (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (tOf f' B' a₀' a'))).1 x = c • w) ↔ c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v hg hu hu'
  have hstd : IsStdChar D W.Q.Rl.ψ (-1) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, -⟩ := hP
    exact hc.std
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D _ hstd
  have hψ : ∀ s ∈ idAt D (· = v), (∀ o ∈ intAt D (· = v), psiE W.Q.Rl.ψ (s * o) = 1) ↔
      (((xiU D * α * cU α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = v) := fun s hs => by
    rw [(hα v).2 s hs, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  have hfg : ((pk W).ΛY 0).FG := (sdY_frames W hW 0 (by have := D.R.two_le_m; omega)).1.1.fg
  exact ⟨_, fun c => ⟨line_loc (D.sp.Y 0) _ hfg v _ _ (single W hW ⟨0, hr⟩ rfl f B hP a₀ a v hg hu (hα v).1 hψ) c,
    line_loc (D.sp.Y 0) _ hfg v _ _ (single W hW ⟨0, hr⟩ rfl f' B' hP' a₀' a' v hg hu' (hα v).1 hψ) c⟩⟩

end GlobalTheory.LineIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw.ShapeExProof

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem places {v : VCom c} {o : TDat c k ι} (hpre : PreT v o) : Places o.p o.I (· ∈ v.tP) :=
  ⟨hpre.nodup, hpre.all, hpre.inj, hpre.tP, fun i => (hpre.char i).2⟩

theorem gluedCore_congr {ρ : ℕ} {B : BesLev D ρ} {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {L L' : Lat B.V₀}
    {q : Unif k} {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n}
    (hL : latV B.V₀ L' (· = p.v) = latV B.V₀ L (· = p.v)) (g : GluedCore B L q β β₀ P) : GluedCore B L' q β β₀ P :=
  ⟨g.unit, g.sum, g.norm, fun y => by rw [hL]; exact g.lat y⟩

end GlobalTheory.SeeSaw.ShapeExProof

namespace GlobalTheory.SeeSaw.ShapeExProof

theorem shapeEx : ∀ D : D7, GlobalTheory.SeeSaw.ShapeEx D := by
  intro D c v k _ _ _ _ ι o hc hdisj hNT hpre hNv hgP hLZ
  obtain ⟨N0, M0, β₀, hN0, hgood0, hsplit0, hglued0⟩ := GlobalTheory.T.exists_lattices_goodPosition_all_places D c v k ι o hc hNT hpre hLZ
  have key : ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀),
      (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j) ∧ ∀ x ∈ v.gP, latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
      (∀ j ρ h, ∀ x ∈ v.gP, latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
      (∀ x, GoodAt { v with N := N } { o with M := M } x) ∧
      (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M } x) ∧
      (∀ j ρ h, ∀ x, x ∉ v.gP → latV _ (M j ρ h) (· = x) = latV _ (M0 j ρ h) (· = x)) := by
    rcases v.gP.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
    · refine ⟨N0, M0, fun j hj => ⟨hN0 j hj, fun x hx => by simp [hE] at hx⟩, fun j ρ h x hx => by simp [hE] at hx,
        fun x => ⟨(hgood0 x).1, (hgood0 x).2⟩, fun x hx => ⟨(hsplit0 x hx).1, (hsplit0 x hx).2⟩, fun _ _ _ _ _ => rfl⟩
    · have hsdM : ∀ j ρ h, IsSelfDualC _ (o.M j ρ h) := fun j ρ h => ((hgP x0 hx0).1.bf j ρ h).sdV₀
      have hsdM0 : ∀ j ρ h, IsSelfDualC _ (M0 j ρ h) := fun j ρ h => ((hgood0 x0).bf j ρ h).sdV₀
      have hpN : ∀ j, ∃ L : Lat (c.V j), j < D.R.m → (IsSelfDualC (c.V j) L ∧
          (∀ x ∈ v.gP, latV (c.V j) L (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
          ∀ x, x ∉ v.gP → latV (c.V j) L (· = x) = latV (c.V j) (N0 j) (· = x)) := by
        intro j
        by_cases hj : j < D.R.m
        · obtain ⟨L, h1, h2, h3⟩ := GlobalTheory.T.exists_selfDual_lattice_patched_at_places D (c.V j) (N0 j) (v.N j) (hN0 j hj) (hNv j hj) v.gP
          exact ⟨L, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨N0 j, fun h => absurd h hj⟩
      choose N hN using hpN
      have hpM : ∀ j ρ h, ∃ L : Lat (c.bes j ρ h).V₀, IsSelfDualC _ L ∧
          (∀ x ∈ v.gP, latV _ L (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
          ∀ x, x ∉ v.gP → latV _ L (· = x) = latV _ (M0 j ρ h) (· = x) := fun j ρ h =>
        GlobalTheory.T.exists_selfDual_lattice_patched_at_places D _ (M0 j ρ h) (o.M j ρ h) (hsdM0 j ρ h) (hsdM j ρ h) v.gP
      choose M hM using hpM
      have hat : ∀ x, (x ∈ v.gP → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
            (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x)) ∧
          (x ∉ v.gP → (GoodAt { v with N := N0 } { o with M := M0, β₀ := β₀ } x → GoodAt { v with N := N } { o with M := M } x) ∧
            (SplitAt { v with N := N0 } { o with M := M0, β₀ := β₀ } x → SplitAt { v with N := N } { o with M := M } x)) := by
        intro x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · have := GlobalTheory.T.goodPosition_splitLines_read_completions_at_place D c v k ι o N M x (fun j hj => ⟨hNv j hj, (hN j hj).1, (hN j hj).2.1 x hx⟩)
            (fun j ρ h => ⟨hsdM j ρ h, (hM j ρ h).1, (hM j ρ h).2.1 x hx⟩)
          exact ⟨fun g => let g' := this.1 g; ⟨g'.1, g'.2⟩, fun s => let s' := this.2 s; ⟨s'.1, s'.2⟩⟩
        · have := GlobalTheory.T.goodPosition_splitLines_read_completions_at_place D c { v with N := N0 } k ι { o with M := M0, β₀ := β₀ } N M x
            (fun j hj => ⟨hN0 j hj, (hN j hj).1, (hN j hj).2.2 x hx⟩)
            (fun j ρ h => ⟨hsdM0 j ρ h, (hM j ρ h).1, (hM j ρ h).2.2 x hx⟩)
          exact ⟨fun g => let g' := this.1 g; ⟨g'.1, g'.2⟩, fun s => let s' := this.2 s; ⟨s'.1, s'.2⟩⟩
      refine ⟨N, M, fun j hj => ⟨(hN j hj).1, (hN j hj).2.1⟩, fun j ρ h => (hM j ρ h).2.1, fun x => ?_, fun x hxT => ?_,
        fun j ρ h => (hM j ρ h).2.2⟩
      · by_cases hx : x ∈ v.gP
        · exact ((hat x).1 hx).1 (hgP x hx).1
        · exact ((hat x).2 hx).1 (hgood0 x)
      · by_cases hx : x ∈ v.gP
        · exact ((hat x).1 hx).2 (hgP x hx).2
        · exact ((hat x).2 hx).2 (hsplit0 x hxT)
  obtain ⟨N, M, hN, hM, hgood, hsplit, hoff⟩ := key
  have hd : ∀ j, ∃ d : WO (c.X j) (c.X (j + 1)) →₀ ℂ, CombAt (· ∈ v.tP) d ∧ (j < D.R.m → ∀ f,
      Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L (· ∈ v.tP) f →
      OverAll c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
        (comb c.ψ _ _ d f)) := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨d, hdc, hdr⟩ := ((GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D) k ι o.p o.I (· ∈ v.tP) (places hpre) (Fin (c.X (j + 1)).rank)
        (Fin (c.X j).rank) c.ψ hc.std (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L
        (hc.x j hj.le).sd (hc.x (j + 1) hj).sd (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).1 (fun i => GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _)
      exact ⟨d, hdc, fun _ => hdr⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hj⟩
  choose dT hdC hdR using hd
  have hpT : ∀ i, (o.p i).v ∉ v.gP := fun i hg =>
    Finset.disjoint_left.mp hdisj hg ((hpre.tP _).mpr ⟨i, rfl⟩)
  refine ⟨N, dT, M, β₀, hN, hM, hdC, ⟨⟨hpre.1, hpre.2, hpre.3, hpre.4, hpre.5, hpre.6, hpre.7, hpre.8, hpre.9, hpre.10, hpre.11⟩,
    fun x => ⟨(hgood x).1, (hgood x).2⟩, fun x hx => ⟨(hsplit x hx).1, (hsplit x hx).2⟩,
    fun j ρ h i => gluedCore_congr (hoff j ρ h _ (hpT i)) (hglued0 j ρ h i), fun j hj => hdR j hj, fun j => rfl⟩⟩

end GlobalTheory.SeeSaw.ShapeExProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpecStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_realData_spec : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  first | exact @GlobalTheory.AdForm.realOf_is | exact GlobalTheory.AdForm.realOf_is | (intros; apply GlobalTheory.AdForm.realOf_is <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_chain_bound : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (J : QJ a t), J.Reads → ∀ κ, InK (I.rec7 l Z).sp.X' a.v.NT (fun p => ∃ i, (J.G i).q.v = p) κ → κ ∈ levSph W a.g.bT := by
  first | exact @GlobalTheory.TopVol.InKConj.inK_mem_levSph | exact GlobalTheory.TopVol.InKConj.inK_mem_levSph | (intros; apply GlobalTheory.TopVol.InKConj.inK_mem_levSph <;> assumption)
end

