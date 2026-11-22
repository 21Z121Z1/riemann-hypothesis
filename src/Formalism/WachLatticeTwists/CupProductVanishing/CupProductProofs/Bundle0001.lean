import Formalism.WachLatticeTwists.CupProductVanishing.Bundle0001
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.Bundle0001

-- bundled from Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.CoboundaryTrivialActionZero
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

section Triv

variable {O : Type*} [CommRing O] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module O M]

theorem coboundary_trivial_action_zero (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) (c : Γ → M) (hc : c ∈ coB1 ρ) : c = 0 := by
  obtain ⟨v, rfl⟩ := hc
  funext g
  show ρ g v - v = 0
  rw [h, sub_self]

def cocOf (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) : H1z ρ →ₗ[O] (Γ → M) :=
  Submodule.liftQ _ (coZ1s ρ).subtype (fun x hx => by
    rw [LinearMap.mem_ker]
    exact coboundary_trivial_action_zero ρ h _ hx)

theorem unr_vanish (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) (I : Subgroup Γ) (z : coZ1s ρ)
    (hz : (Submodule.mkQ _ z : H1z ρ) ∈ unrH1 ρ I) (g : Γ) (hg : g ∈ I) : (z : Γ → M) g = 0 := by
  have h1 : resH1 ρ I (Submodule.mkQ _ z) = 0 := hz
  have h2 : (Submodule.mkQ _ (restrictCocycles1 ρ I z) : H1z (resRep ρ I)) = 0 := h1
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  have h3 := coboundary_trivial_action_zero (resRep ρ I) (fun g m => h g m) _ h2
  exact congrFun h3 ⟨g, hg⟩

end Triv

theorem vhE : StatVhE := hT2Core.out.vhE

theorem unramified_H1_antitone {O : Type*} [CommRing O] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module O M]
    (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) {I J : Subgroup Γ} (hIJ : I ≤ J) : unrH1 ρ J ≤ unrH1 ρ I := by
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  show resH1 ρ I (Submodule.mkQ _ z) = 0
  have : restrictCocycles1 ρ I z = 0 := Subtype.ext (funext fun g => unr_vanish ρ h J z hx g (hIJ g.2))
  show (Submodule.mkQ _ (restrictCocycles1 ρ I z) : H1z (resRep ρ I)) = 0
  rw [this, map_zero]

theorem vhEInChi : StatVhEInChi := by
  intro E Ω _ _ _ _ _ Av hA l _ O _ _ _ _ _ hl A T' _ _ _ _ M _ _ _ _ e r χ htr D places HcG F Vo VS Io IS hc hcov
  have hρ : ∀ g m, uRep O (M := M) r χ g m = m := fun g m => htr g m
  refine vhE E Ω Av hA l O hl M e (uRep O (M := M) r χ) hρ _ (fun x hx => hc x hx.1.1.1) (fun v x hx => ?_)
  rcases hcov v with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨w, hw, I, hF, hI⟩
  · exact unramified_H1_antitone _ hρ ha ((Submodule.mem_iInf _).1 hx.1.1.2 a)
  · exact unramified_H1_antitone _ hρ ha ((Submodule.mem_iInf _).1 hx.1.2 a)
  · have h1 : resH1 (uRep O (M := M) r χ) (D w) x ∈ F w :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hx.2 w) hw
    have h2 := hF h1
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    show Formalism.NG.resH1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) (Submodule.mkQ _ z) = 0
    have : Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) z = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨g', hg', hgg⟩ := hI g.2
      have h3 := unr_vanish (resRep (uRep O (M := M) r χ) (D w)) (fun g m => hρ g m) I
        (Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (D w) z) h2 g' hg'
      show (z : G E Ω → M) g = 0
      rw [← hgg]
      exact h3
    show (Submodule.mkQ _ (Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) z) :
      H1z (resRep (uRep O (M := M) r χ) (Ine (F := E) (Av v)))) = 0
    rw [this, map_zero]

end Formalism.RepresentationBoundsCohomology.T2
end
end

-- bundled from Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.H2MapInjectiveStatement
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem h2Map_injective_statement : H2MapInjective := by
  intro O _ _ _ _ Γ _ _ ε hNat Y R _ _ _ _ _ _ _ _ _ _ hY hR i hic hii z hz hzc hfz
  obtain ⟨f, hf, hfz⟩ := hfz
  obtain ⟨θ⟩ := hNat
  have htw : ∀ (M : Type) [AddCommGroup M] [Module O M] (g : Γ) (m : M),
      Formalism.RepresentationBoundsCohomology.LOC.twist ε M g m = ((ε g : Oˣ) : O) • m := fun M _ _ g m => rfl

  let zz : ReciprocityTheory.Gal.Z2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) := ⟨fun p => z p.1 p.2, hzc, fun g h k => hz g h k⟩
  have hzero : ReciprocityTheory.Gal.mapH2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) (Formalism.RepresentationBoundsCohomology.LOC.twist ε R) i hic
      (ReciprocityTheory.ChartRestriction.T2.twist_map ε i) (Submodule.Quotient.mk zz) = 0 := by
    rw [ReciprocityTheory.Gal.mapH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]
    refine ⟨f, hf, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    rw [ReciprocityTheory.Gal.d1_apply, htw]
    exact (hfz g h).symm
  have hθ := θ.nat Y R hY hR i hic (Submodule.Quotient.mk zz)
  rw [hzero, map_zero] at hθ
  have h0 : θ.θ Y hY (Submodule.Quotient.mk zz) = 0 := hii (hθ.symm.trans (map_zero i).symm)
  have hmk : (Submodule.Quotient.mk zz : ReciprocityTheory.Gal.H2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y)) = 0 :=
    (θ.θ Y hY).injective (by rw [h0, map_zero])
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem] at hmk
  obtain ⟨c, hc, hcz⟩ := hmk
  refine ⟨c, hc, fun g h => ?_⟩
  have e := congrFun hcz (g, h)
  rw [ReciprocityTheory.Gal.d1_apply, htw] at e
  exact e.symm

theorem clause4 : CupClause := by
  intro O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hA hNat z hz hzc hfz
  haveI : IsNoetherian O A := by
    haveI := hA.fg
    infer_instance
  haveI := hA.t2
  haveI := hA.csmul
  haveI : ContinuousConstSMul O (Ymod r χ E) :=
    ⟨fun a => continuous_induced_rng.2 ((continuous_const_smul a).comp continuous_subtype_val)⟩
  let i : Ymod r χ E →ₗ[O] A := (Ymod r χ E).subtype.restrictScalars O
  have hYfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop O (Ymod r χ E) :=
    ⟨Module.Finite.of_injective i Subtype.val_injective, inferInstance,
      ⟨continuous_induced_rng.2 (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))⟩⟩
  exact h2Map_injective_statement O Dw (ε.comp Dw.subtype) hNat (Ymod r χ E) A hYfg hA i continuous_subtype_val
    Subtype.val_injective z hz hzc hfz

end Formalism.RepresentationBoundsCohomology.T2
end
end

-- bundled from Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.PropLocGKOf
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem compat : StatCompat := by
  intro O G VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hc a t
  have h : D.pr (D.q a) t = D.inv (mapH2 (twist D.ε (FractionRing O)) (twist D.ε (KO O)) (toKO O) toKO_cont
      (toKO_equiv D.ε) (cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT' a (D.j' t))) := by
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      induction t using Submodule.Quotient.induction_on with
      | H t => rfl
  rw [h, hc]
  rfl

theorem realise_of (hI : StatInvGK) : StatRealise := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hK hO hF hD
  obtain ⟨inv, invF, h⟩ := hI p K O hK hO hF D.ε hD.cyc
  exact ⟨inv.toLinearMap, invF.toLinearMap,
    ⟨hD.cyc, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩, inv.bijective, invF.bijective, h⟩

theorem propLocGK_of (h1 : StatFinGK) (h2 : StatRatGK) (h3 : StatIntGK) : StatPropLocGK := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ D HfV HfV' ℓ e' ι₁ ι₂ P Q hK hO hF hD hi hiF hc hBK hsat hP hQ
  exact propLocContBK O (GK p K) VT VT' D HfV HfV' (pairF D) ℓ e' ι₁ ι₂ P Q hD.lat hD.perf
    (h1 p K O VT VT' D hK hO hD) hc hBK hsat (h2 p K O VT VT' D hK hO hF hD hiF)
    (compat O (GK p K) VT VT' D hc) (h3 p K O VT VT' D hK hO hF hD hi) hP hQ

end Formalism.RepresentationBoundsCohomology.T2
end
end

