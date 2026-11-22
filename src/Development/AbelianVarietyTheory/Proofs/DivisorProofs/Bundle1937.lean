import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchIntertw

open GlobalTheory.AdelicU

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

def infAd : mixedEmbedding.mixedSpace F →+ AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).toAddMonoidHom.comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv.toAddMonoidHom

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstA F).toRingHom

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_infAd (s : mixedEmbedding.mixedSpace F) : evI F (infAd s) = s :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply s

theorem sndA_infAd (s : mixedEmbedding.mixedSpace F) : sndA F (infAd s) = 0 := rfl

theorem evFin_infAd (v : Pl F) (s : mixedEmbedding.mixedSpace F) : evFin F v (infAd s) = 0 := by
  show evalV F v (sndA F (infAd s)) = 0
  rw [sndA_infAd, map_zero]

theorem infAd_evI (t : AF F) (h : sndA F t = 0) : infAd (evI F t) = t := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F t.1) = t.1
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
  · exact h.symm

theorem at_infAd (s : mixedEmbedding.mixedSpace F) : At (evI F) (infAd s) := by
  intro u hu
  have h1 : fstA F u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  rw [smul_eq_mul]
  refine Prod.ext ?_ ?_
  · change fstA F (u * infAd s) = 0
    rw [map_mul, h1, zero_mul]
  · change sndA F (u * infAd s) = 0
    rw [map_mul, sndA_infAd, mul_zero]

end SlopeTestRemainingChoices

section Aux2

variable {F : Type} [Field F] [NumberField F]

theorem evIHom_invOf [Invertible (2 : AF F)] [Invertible (2 : mixedEmbedding.mixedSpace F)] :
    evIHom (⅟(2 : AF F)) = ⅟(2 : mixedEmbedding.mixedSpace F) := by
  refine (invOf_eq_left_inv ?_).symm
  rw [show (2 : mixedEmbedding.mixedSpace F) = evIHom (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self,
    map_one]

theorem schr_pure [Invertible (2 : AF F)] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (Ψ : AddChar (AF F) ℂ) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) :
    schr Ψ (fun i => infAd (a i), fun i => infAd (b i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x =
      schr (Ψ.compAddMonoidHom infAd) (a, b) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (fun i => evI F (x i)) *
        ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  have e1 : (fun i => evI F ((x + fun i => infAd (a i)) i)) = (fun i => evI F (x i)) + a := by
    funext i
    change evIHom (x i + infAd (a i)) = evIHom (x i) + a i
    rw [map_add, evIHom_apply (infAd _), evI_infAd]
  have e2 : ∀ v, (fun i => evFin F v ((x + fun i => infAd (a i)) i)) = fun i => evFin F v (x i) := fun v => by
    funext i
    simp only [Pi.add_apply, map_add, evFin_infAd, add_zero]
  have hs : sndA F (x ⬝ᵥ (fun i => infAd (b i)) + ⅟(2 : AF F) * ((fun i => infAd (a i)) ⬝ᵥ fun i => infAd (b i))) = 0 := by
    simp only [dotProduct, map_add, map_sum, map_mul, sndA_infAd, mul_zero, Finset.sum_const_zero, add_zero]
  have hi : evI F (x ⬝ᵥ (fun i => infAd (b i)) + ⅟(2 : AF F) * ((fun i => infAd (a i)) ⬝ᵥ fun i => infAd (b i))) =
      (fun i => evI F (x i)) ⬝ᵥ b + ⅟(2 : mixedEmbedding.mixedSpace F) * (a ⬝ᵥ b) := by
    rw [← evIHom_apply]
    simp only [dotProduct, map_add, map_sum, map_mul, evIHom_invOf]
    simp only [evIHom_apply, evI_infAd]
  have e3 := infAd_evI _ hs
  rw [hi] at e3
  simp only [schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  have e2' : (∏ᶠ v, φ v fun i => evFin F v ((x + fun i => infAd (a i)) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) :=
    finprod_congr fun v => by rw [e2 v]
  rw [e1, e2', ← e3, AddChar.compAddMonoidHom_apply]
  ring

open Classical in

theorem exists_finprod_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (y : κ → mixedEmbedding.mixedSpace F) :
    ∃ x : κ → AF F, (fun i => evI F (x i)) = y ∧ ∏ᶠ v, φ v (fun i => evFin F v (x i)) ≠ 0 := by
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  have hS := Filter.eventually_cofinite.mp hstd
  let T := hS.toFinset
  let xf : κ → AF F := fun i => ∑ w ∈ T, GlobalTheory.LatVac.liftV w (p w i)
  have hxf1 : ∀ i, evI F (xf i) = 0 := fun i => by
    rw [← evIHom_apply, map_sum]
    exact Finset.sum_eq_zero fun w _ => (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have hxf2 : ∀ w i, w ∈ T → evFin F w (xf i) = p w i := fun w i hw => by
    simp only [xf, map_sum]
    rw [Finset.sum_eq_single_of_mem w hw]
    · exact GlobalTheory.LatVac.evFin_liftV w _
    · intro x _ hx
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hx) _
  have hxf3 : ∀ w i, w ∉ T → evFin F w (xf i) = 0 := fun w i hw => by
    simp only [xf, map_sum]
    exact Finset.sum_eq_zero fun x hx => GlobalTheory.AdelicU.evalV_singleFin_ne (fun h => hw (by rw [h]; exact hx)) _
  refine ⟨fun i => infAd (y i) + xf i, funext fun i => ?_, ?_⟩
  · rw [← evIHom_apply, map_add, evIHom_apply, evIHom_apply, evI_infAd, hxf1, add_zero]
  · have hfin := GlobalTheory.PureFactor.mulSupport_finite φ hstd (fun i => infAd (y i) + xf i)
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin (subset_refl _)]
    refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
    by_cases hw : w ∈ T
    · have : (fun i => evFin F w (infAd (y i) + xf i)) = p w := funext fun i => by
        rw [map_add, evFin_infAd, zero_add, hxf2 w i hw]
      rw [this]
      simpa using hp w
    · have : (fun i => evFin F w (infAd (y i) + xf i)) = 0 := funext fun i => by
        rw [map_add, evFin_infAd, zero_add, hxf3 w i hw, Pi.zero_apply]
      have hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hw (hS.mem_toFinset.mpr h)
      rw [this, hw', Set.indicator_of_mem (fun i => by simpa using (w.adicCompletionIntegers F).zero_mem)]
      exact one_ne_zero

end Aux2

theorem ei_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ [Invertible (2 : mixedEmbedding.mixedSpace F)], ∃ ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ,
        (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) ∧
        ∃ A : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
            (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
          ∀ w (f g : SInf F (Fin n × Fin d)), (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
            (ei g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (ei f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE ei ev hei hev hloc _
  classical
  refine ⟨B.ψ.compAddMonoidHom infAd, fun a => ?_, ?_⟩
  · show B.ψ (infAd a) = _
    rw [hP.base.std.2.2 _ (at_infAd a), evI_infAd]
  let u : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
      (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := fun w => (fun i => infAd (w.1 i), fun i => infAd (w.2 i))
  refine ⟨fun w => (fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).1 i),
    fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).2 i)), fun w f g hg => ?_⟩
  have hM := hP.good
  have hvacM : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hpure : ∀ h : SInf F (Fin n × Fin d), e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei h) M₁.vac :=
    fun h => by
      rw [hloc h M.vac hvacM (Filter.Eventually.of_forall fun _ => rfl)]
      congr 1
      funext v
      exact (hev v).1
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hM.std
  have key := hE.Heisenberg₂ (M.co.e.symm (u w)) _ hmem
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at key

  have hL : M.co.rho B.ψ (M.co.e.symm (u w)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac := by
    funext x
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, u]
    rw [schr_pure, Prod.mk.eta, ← hg]
    rfl

  let c : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hc : ∀ s, c * infAd s = 0 := fun s => by
    refine Prod.ext ?_ ?_
    · change fstA F (c * infAd s) = 0
      rw [map_mul]
      exact zero_mul _
    · change sndA F (c * infAd s) = 0
      rw [map_mul, sndA_infAd, mul_zero]
  have hcu : c • u w = 0 := Prod.ext (funext fun i => hc _) (funext fun i => hc _)
  have hcz : c • M₁.co.e (M.co.e.symm (u w)) = 0 := by
    rw [← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hcu, map_zero, map_zero]
  have hsnd : ∀ y : AF F, c * y = 0 → sndA F y = 0 := fun y hy => by
    have := congrArg (sndA F) hy
    have h1c : sndA F c = 1 := rfl
    rw [map_mul, map_zero, h1c, one_mul] at this
    exact this
  have hz : M₁.co.e (M.co.e.symm (u w)) =
      u ((fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).1 i)), fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).2 i)) := by
    refine Prod.ext (funext fun i => (infAd_evI _ (hsnd _ ?_)).symm) (funext fun i => (infAd_evI _ (hsnd _ ?_)).symm)
    · exact congrFun (congrArg Prod.fst hcz) i
    · exact congrFun (congrArg Prod.snd hcz) i
  rw [hL, hpure, hpure] at key
  funext y
  obtain ⟨x, hx, hne⟩ := exists_finprod_ne M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std y
  have k := congrFun key x
  rw [Darboux.rho, hz] at k
  simp only [u] at k
  rw [schr_pure] at k
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hx] at k
  exact mul_right_cancel₀ hne k

end GlobalTheory.ArchIntertw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenExtendsContinuous
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ThK.ModelLocInt

open scoped Classical
open Filter GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem incM_one (m : ℕ) : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem heis_loc {B : Base F E} {M M₁ : Model σ X W} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {e : Fn F n d →ₗ[ℂ] Fn F n d} (he : IsEv B M M₁ 1 1 ∅ e)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ) (hei : ei ≠ 0)
    (hvm : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (v : Pl F) (z : Matrix (Fin n) (Fin d) (AE F E)) (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB _)
    (φ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hφ₁ : φ₁ ∈ SB _) (hA : Acts (evFin F v) (M.co.rho B.ψ z) φ φ₁)
    (χ₁ : (Fin n × Fin d → Fv F v) → ℂ) (hA₁ : Acts (evFin F v) (M₁.co.rho B.ψ z) (ev v φ) χ₁) :
    ev v φ₁ = χ₁ := by
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl F, (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n × Fin d) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
  rw [incM_one, incM_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h1
  rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
  have hevφ : ev v φ ∈ SB _ := by
    rw [← (hvm v).2]
    exact Submodule.mem_map_of_mem hφ
  rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
  exact canc _ _ h1

def ptAt (M : Model σ X W) (v : Pl F) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  M.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k))

theorem at_ptAt (M : Model σ X W) (v : Pl F) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    At (evFin F v) (ptAt M v w) := by
  intro a ha
  unfold ptAt
  rw [← LinearEquiv.map_smul, ← M.co.e.symm.map_zero]
  congr 1
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · exact GlobalTheory.LatVac.at_liftV v _ a ha

theorem locCo_ptAt (M : Model σ X W) (v : Pl F) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :
    GlobalTheory.LatVac.locCo M.co v (ptAt M v w) = w := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
    simp [ptAt, GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

end GlobalTheory.ThK.ModelLocInt

open GlobalTheory.ThK.ModelLocInt in

theorem GlobalTheory.ThK.ModelLocInt.exists_loc_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl F) [Invertible (2 : Fv F v)], ∃ ψv : AddChar (Fv F v) ℂ, Continuous ψv ∧ ψv ≠ 1 ∧
        ∃ A : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          ∀ w, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr ψv w φ) = schr ψv (A w) (ev v φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e he ei ev hei hvm hloc v _
  obtain rfl : ‹Invertible (2 : Fv F v)› = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  have hψe : GlobalTheory.LatVac.psiAt B.ψ v = GlobalTheory.VacAny.psiV B.ψ v :=
    by
    ext t
    exact (GlobalTheory.LatVac.psiAt_apply B.ψ v t).trans (GlobalTheory.VacAny.psiV_eq_psiLoc B.ψ v t).symm
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := by
    rw [hψe]; exact GlobalTheory.VacAny.continuous_psiV hP.base.std.1 v
  refine ⟨GlobalTheory.LatVac.psiAt B.ψ v, hψc, by rw [hψe]; exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hP.base.std v,
    fun w => GlobalTheory.LatVac.locCo M₁.co v (ptAt M v w), fun w φ hφ => ?_⟩
  have hA := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v (ptAt M v w) (at_ptAt M v w) φ
  rw [locCo_ptAt] at hA
  have hA₁ := GlobalTheory.VacBridge.rho_acts_locCo M₁.co B.ψ v (ptAt M v w) (at_ptAt M v w) (ev v φ)
  exact heis_loc hP.good hM₁ he ei ev hei hvm hloc v (ptAt M v w) φ hφ _
    (GlobalTheory.SchrSBFin.schr_mem_SB v _ hψc w φ hφ) hA _ hA₁
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU

section Dbl

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ κ' : Type} [Fintype κ] [Fintype κ']

end Dbl

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem adm_of_eqOn_schA {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ φ ∈ schA F κ, l φ = l' φ) (hl : l ∈ (adeleClass F).adm κ) : l' ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩

variable {ψ : AddChar (AF F) ℂ} {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
  {κ κ' : Type} [Fintype κ] [Fintype κ'] {d : Darboux B κ} {d' : Darboux B κ'}
  {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
  {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem IsOp.rho_eq (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S') (w : W) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : S (d.rho ψ w φ) = d'.rho ψ w (S φ) := by
  simp only [Darboux.rho]
  rw [hS.Heisenberg₂ _ _ hφ, hs]

theorem isUSplitting_of_isOp (hψ : IsStd ψ) (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S')
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W}
    {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : G →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : IsUSplitting (adeleClass F) ψ d act om) : IsUSplitting (adeleClass F) ψ d' act om' := by
  have hmem : ∀ (κ₀ : Type) [Fintype κ₀] (p : (κ₀ → AF F) × (κ₀ → AF F)) (φ : (κ₀ → AF F) → ℂ),
      φ ∈ schA F κ₀ → schr ψ p φ ∈ schA F κ₀ := fun κ₀ _ p φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ₀ p φ hφ
  have hrho' : ∀ w, ∀ φ ∈ schA F κ', S' (d'.rho ψ w φ) = d.rho ψ w (S' φ) := fun w φ hφ => by
    have h1 := IsOp.rho_eq hs hS w (hS.pres' φ hφ)
    rw [hS.right φ hφ] at h1
    have hm : d.rho ψ w (S' φ) ∈ schA F κ := hmem _ _ _ (hS.pres' φ hφ)
    rw [← h1, hS.left _ hm]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ' hμ' g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [hom g φ hφ]
    exact hS.pres _ (h.pres g _ (hS.pres' φ hφ))
  · have hw : d'.rho ψ w φ ∈ schA F κ' := hmem _ _ _ hφ
    rw [hom g _ hw, hrho' w φ hφ, h.impl g w _ (hS.pres' φ hφ),
      IsOp.rho_eq hs hS _ (h.pres g _ (hS.pres' φ hφ)), hom g φ hφ]
  · have h2 := hS.adm' _ (h.adm g _ (hS.adm l hl))
    refine adm_of_eqOn_schA (fun φ hφ => ?_) h2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]
  · letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    obtain ⟨c, -, -, hc⟩ := hS.norm Measure.addHaar μ' inferInstance hμ'
    rw [hom g φ hφ, hc _ (h.pres g _ (hS.pres' φ hφ)), h.unit Measure.addHaar inferInstance g _ (hS.pres' φ hφ),
      ← hc _ (hS.pres' φ hφ), hS.right φ hφ]
  · refine (h.cont (l ∘ₗ S) (hS.adm l hl) (S' φ) (hS.pres' φ hφ)).congr fun g => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]

theorem siegelRule_of_isOp {E' : Type} [CommRing E'] [Algebra (AF F) E'] {c : E' →ₐ[AF F] E'} {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E'} {JA : Matrix α α E'} {JB : Matrix β β E'}
    {d : Darboux (symp c ξ JA JB) κ} {d' : Darboux (symp c ξ JA JB) κ'} (hs : ∀ w, s (d.e w) = d'.e w)
    (hS : IsOp ψ s S S') {χ : E'ˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E'}
    {om : UG c JB →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : UG c JB →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : SiegelRule c (adeleClass F) ψ ξ JA JB d χ Cy om) : SiegelRule c (adeleClass F) ψ ξ JA JB d' χ Cy om' := by
  intro l hl hinv p t hpt φ hφ
  have key := h (l ∘ₗ S) (hS.adm l hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [IsOp.rho_eq hs hS _ hφ']
    exact hinv z _ (hS.pres _ hφ')) p t hpt (S' φ) (hS.pres' φ hφ)
  simp only [LinearMap.coe_comp, Function.comp_apply, hS.right φ hφ] at key
  rw [hom p φ hφ]
  exact key

end Adelic

end GlobalTheory.TowU

end
end

