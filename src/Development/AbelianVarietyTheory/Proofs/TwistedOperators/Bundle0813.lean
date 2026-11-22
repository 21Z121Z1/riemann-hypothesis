import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0812
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0720
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0772
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0732
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0757
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0703
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0744
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0708
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0709

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfUnramifiedOverPlaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_unramified_over_place : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}, IsPlaceIdem D v ε → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) → GlobalTheory.WeilParts.UnramAt ε χ := by
  first | exact @GlobalTheory.UnrOverPlaceConv.unramAt_of_unrAt_all | exact GlobalTheory.UnrOverPlaceConv.unramAt_of_unrAt_all | (intros; apply GlobalTheory.UnrOverPlaceConv.unramAt_of_unrAt_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotDvdDifferentIdealOfStandardAddCharUnramifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_dvd_differentIdeal_of_standardAddChar_unramified : ∀ {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {v : HeightOneSpectrum (𝓞 F)}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  first | exact @GlobalTheory.PsiDifferent.not_dvd_different_of_psiUnr | exact GlobalTheory.PsiDifferent.not_dvd_different_of_psiUnr | (intros; apply GlobalTheory.PsiDifferent.not_dvd_different_of_psiUnr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree.KerPMax

theorem kernel_maximal : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N N' : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) →
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → N ≤ N' → N' = N ∨ N' = algD Γ.M' Bs.ψ Bs.emb := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' Pi rf rl p p' hm N N' hN hN' hle
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by rw [← hO.psi]; exact hT'.base.std
  obtain ⟨hz, hlin⟩ := isDatum_linear Γ.M' ψ hstd cB
  have hfun : ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ → Φ₀ ∈ algF ψ θ false A₁ B := by
    intro ΦD hΦD Φ₀ hD
    obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' ΦD hΦD
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact hΦ₁
  let S : Submodule ℂ Pi :=
    { carrier := {x | ∃ ΦD ∈ N', ∃ Φ₀, IsDatum Γ.M' ψ cB ΦD Φ₀ ∧ p' Φ₀ = x}
      zero_mem' := ⟨0, N'.zero_mem, 0, hz, map_zero p'⟩
      add_mem' := by
        rintro _ _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩ ⟨ΨD, hΨD, Ψ₀, hE, rfl⟩
        refine ⟨ΦD + ΨD, N'.add_mem hΦD hΨD, Φ₀ + Ψ₀, ?_, map_add p' _ _⟩
        simpa using hlin ΦD ΨD Φ₀ Ψ₀ 1 hD hE
      smul_mem' := by
        rintro c _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
        refine ⟨c • ΦD, N'.smul_mem c hΦD, c • Φ₀, ?_, map_smul p' c Φ₀⟩
        simpa using hlin 0 ΦD 0 Φ₀ c hz hD }
  have hc1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1 = 1 :=
    Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])
  have hS1 : ∀ g ∈ GfC X, ∀ x ∈ S, rf g x ∈ S := by
    rintro g hg _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    have hΦ₀ := hfun ΦD (hN'.le hΦD) Φ₀ hD
    have hW := hO.weilB ΦD Φ₀ hD 1 g
    rw [hc1] at hW
    exact ⟨_, GlobalTheory.T.triple_geometry_hermitian_form hP D X W.rank W₁.rank e Bs Γ Xc om om' hT' hO.JX N' hN' g hg ΦD hΦD, _, hW,
      hm.mapB.eqf g hg Φ₀ hΦ₀⟩
  have hS2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, rl τ Y x ∈ S := by
    rintro τ Y hY _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    obtain ⟨ΨD, hΨD, Φ₁, hΦ₁, hE, hder⟩ := GlobalTheory.T.seesaw_unfolding_evaluation hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB
      hθ hT hO hT' Pi rf rl p p' hm N' hN' τ Y hY ΦD hΦD Φ₀ hD
    exact ⟨ΨD, hΨD, Φ₁, hE, hm.mapB.eql τ Y hY Φ₀ (hfun _ (hN'.le hΦD) _ hD) Φ₁ hΦ₁ hder⟩
  rcases hm.irred.2 S hS1 hS2 with h0 | h1
  · left
    refine le_antisymm (fun ΦD hΦD => ?_) hle
    obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algB' ΦD (hN'.le hΦD)
    have hx : p' Φ₁ ∈ S := ⟨ΦD, hΦD, Φ₁, hD₁, rfl⟩
    rw [h0, Submodule.mem_bot] at hx
    exact (hN ΦD).2 ⟨hN'.le hΦD, Φ₁, hΦ₁, hD₁, hx⟩
  · right
    refine le_antisymm hN'.le (fun ΨD hΨD => ?_)
    obtain ⟨Ψ₀, hΨ₀, hE⟩ := hO.algB' ΨD hΨD
    have hx : p' Ψ₀ ∈ S := h1 ▸ Submodule.mem_top
    obtain ⟨ΦD, hΦD, Φ₀, hD, hpe⟩ := hx
    have hdiff : ΨD - ΦD ∈ N := by
      refine (hN _).2 ⟨(algD _ _ _).sub_mem hΨD (hN'.le hΦD), Ψ₀ - Φ₀,
        (algF ψ θ false A₁ B).sub_mem hΨ₀ (hfun _ (hN'.le hΦD) _ hD), ?_, ?_⟩
      · simpa [sub_eq_add_neg] using hlin ΨD ΦD Ψ₀ Φ₀ (-1) hE hD
      · rw [map_sub, hpe, sub_self]
    simpa using N'.add_mem (hle hdiff) hΦD

end GlobalTheory.SquareAgree.KerPMax
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingMeasure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

theorem GlobalTheory.SquareAgree.kernel_maximal_thetaSubspace : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (algD Γ.M Bs.ψ Bs.emb) K ∧ K ≠ algD Γ.M Bs.ψ Bs.emb ∧
      (∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → K ≤ N → N = K ∨ N = algD Γ.M Bs.ψ Bs.emb) ∧
      ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (ΦD ∈ K ↔ p Φ = 0) := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm
  have hpsi := hO.psi
  subst hpsi
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hT.base.std

  let dF : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) → (WO W X → ℂ) :=
    fun ΦD x => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ (cA.symm x) ΦD)
  have hdat : ∀ ΦD f, IsDatum Γ.M Bs.ψ cA ΦD f → f = dF ΦD := by
    intro ΦD f h
    funext x
    have := h.2 (cA.symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  have hdat' : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), IsDatum Γ.M Bs.ψ cA ΦD (dF ΦD) := by
    intro ΦD h
    refine ⟨h, fun u => ?_⟩
    show _ = GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ (cA.symm (cA u)) ΦD)
    rw [AddEquiv.symm_apply_apply]
  have hS : ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)) := by
    intro ΦD h
    obtain ⟨_, _, hd⟩ := hO.algA' ΦD h
    exact hd.1
  have dF_sub : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∀ ΨD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), dF (ΦD - ΨD) = dF ΦD - dF ΨD := by
    intro ΦD h ΨD h'
    exact (hdat _ _ (GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hstd (hdat' ΦD h) (hdat' ΨD h'))).symm
  have dF_add : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∀ ΨD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), dF (ΦD + ΨD) = dF ΦD + dF ΨD := by
    intro ΦD h ΨD h'
    exact (hdat _ _ (GlobalTheory.SquareAgree.CoinvPass.isDatum_add hstd (hdat' ΦD h) (hdat' ΨD h'))).symm
  have dF_smul : ∀ (c : ℂ), ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      dF (c • ΦD) = c • dF ΦD := by
    intro c ΦD h
    exact (hdat _ _ (GlobalTheory.SquareAgree.CoinvPass.isDatum_smul c (hdat' ΦD h))).symm
  have dF_zero : dF 0 = 0 := (hdat _ _ GlobalTheory.SquareAgree.CoinvPass.isDatum_zero).symm
  have hAlgF : ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, dF ΦD ∈ algF Bs.ψ θ true A B := by
    intro ΦD h
    obtain ⟨Φ, hΦ, hd⟩ := hO.algA' ΦD h
    rw [← hdat _ _ hd]; exact hΦ
  have inj : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∀ ΨD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), dF ΦD = dF ΨD → ΦD = ΨD := by
    intro ΦD h ΨD h' he
    have h0 := GlobalTheory.T.eq_zero_of_thetaDistribution_heisenbergTranslates Γ.M Bs.ψ hstd (ΦD - ΨD) (sub_mem h h') (fun u => by
      have := congrFun (dF_sub ΦD h ΨD h') (cA u)
      rw [he, sub_self] at this
      have e2 : dF (ΦD - ΨD) (cA u) = GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (ΦD - ΨD)) := by
        show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ (cA.symm (cA u)) (ΦD - ΨD)) = _
        rw [AddEquiv.symm_apply_apply]
      rw [← e2, this]; rfl)
    exact sub_eq_zero.1 h0
  have toS : ∀ ΦD ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)), dF ΦD ∈ algF Bs.ψ θ true A B →
      ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
    intro ΦD h hF
    obtain ⟨ΨD, hΨ, hd⟩ := hO.algA _ hF
    rw [inj ΦD h ΨD (hS _ hΨ) (hdat _ _ hd)]
    exact hΨ

  have hWf : ∀ h' ∈ GfC X, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (1, kapX X e hO.JX h') ΦD ∈ algD Γ.M Bs.ψ Bs.emb ∧
      dF (om (1, kapX X e hO.JX h') ΦD) = ωA (1, h') (dF ΦD) := by
    intro h' hh' ΦD hΦD
    have hd := hO.weilA ΦD (dF ΦD) (hdat' ΦD (hS _ hΦD)) 1 h'
    rw [GlobalTheory.LocWeilAct.conjU_one'] at hd
    have e1 := hdat _ _ hd
    refine ⟨toS _ hd.1 ?_, e1.symm⟩
    rw [← e1]
    exact hm.mapA.stabX.1 h' hh' _ (hAlgF _ hΦD)
  have hVf : ∀ g' ∈ GfC W, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb,
      om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW g', 1) ΦD ∈ algD Γ.M Bs.ψ Bs.emb ∧
      dF (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW g', 1) ΦD) = ωA (g', 1) (dF ΦD) := by
    intro g' hg' ΦD hΦD
    have hd := hO.weilA ΦD (dF ΦD) (hdat' ΦD (hS _ hΦD)) g' 1
    rw [GlobalTheory.KapXLine.kapX_one] at hd
    have e1 := hdat _ _ hd
    refine ⟨toS _ hd.1 ?_, e1.symm⟩
    rw [← e1]
    exact hm.mapA.stabM.1 g' hg' _ (hAlgF _ hΦD)

  let K : Submodule ℂ ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :=
    { carrier := {ΦD | ΦD ∈ algD Γ.M Bs.ψ Bs.emb ∧ p (dF ΦD) = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, ?_⟩
        rw [dF_add a (hS _ ha) b (hS _ hb), map_add, ha', hb', add_zero]
      zero_mem' := ⟨zero_mem _, by rw [dF_zero, map_zero]⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨Submodule.smul_mem _ c ha, ?_⟩
        rw [dF_smul c a (hS _ ha), map_smul, ha', smul_zero] }
  have memK : ∀ ΦD, ΦD ∈ K ↔ ΦD ∈ algD Γ.M Bs.ψ Bs.emb ∧ p (dF ΦD) = 0 := fun _ => Iff.rfl
  refine ⟨K, ⟨⟨fun x hx => hx.1, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    rintro v h hh ΦD ⟨hΦD, hp0⟩
    obtain ⟨h', hh', rfl⟩ := GlobalTheory.T.transposeGramUnitary_surjective_finitePlaceSupported D X e Γ.W hO.JX v h hh
    obtain ⟨h1, h2⟩ := hWf h' hh' ΦD hΦD
    refine ⟨h1, ?_⟩
    rw [h2, hm.mapA.eqf h' hh' _ (hAlgF _ hΦD), hp0, map_zero]
  · rintro k hk ΦD ⟨hΦD, hp0⟩
    have h1 := GlobalTheory.T.seesaw_unfolding_square_integral hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm k hk ΦD hΦD
    exact ⟨h1, GlobalTheory.T.p_eq_zero_of_kInf_right_translate hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm k hk ΦD hΦD _ _ (hdat' _ (hS _ hΦD)) (hdat' _ (hS _ h1)) hp0⟩
  · rintro γ hγ ΦD ⟨hΦD, hp0⟩ Φ₁ hΦ₁ hder
    exact ⟨hΦ₁, GlobalTheory.T.seesaw_unfolding_global_integral hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm γ hγ ΦD hΦD Φ₁ hΦ₁ hder _ _ (hdat' _ (hS _ hΦD)) (hdat' _ (hS _ hΦ₁)) hp0⟩
  ·
    intro v g hg ΦD hΦD
    have hg' := GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W Γ.V 1 one_ne_zero hO.JW v g hg
    have eg : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (GlobalTheory.ConjUTransport.conjUInv W 1 one_ne_zero hO.JW g) = g :=
      (GlobalTheory.ConjUTransport.conjEquiv W 1 one_ne_zero hO.JW).apply_symm_apply g
    obtain ⟨h1, h2⟩ := hVf _ hg' ΦD hΦD
    rw [eg] at h1 h2
    refine ⟨sub_mem h1 hΦD, ?_⟩
    rw [dF_sub _ (hS _ h1) _ (hS _ hΦD), map_sub, h2, hm.mapA.invf _ hg' _ (hAlgF _ hΦD), sub_self]
  · intro k hk ΦD hΦD
    have h1 := GlobalTheory.T.seesaw_unfolding_compatible hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm k hk ΦD hΦD
    refine ⟨sub_mem h1 hΦD, ?_⟩
    rw [dF_sub _ (hS _ h1) _ (hS _ hΦD), map_sub,
      GlobalTheory.T.seesaw_unfolding_inner_product hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
        Pi rf rl p p' hm k hk ΦD hΦD _ _ (hdat' _ (hS _ hΦD)) (hdat' _ (hS _ h1)), sub_self]
  · intro γ hγ ΦD hΦD Φ₁ hΦ₁ hder
    exact ⟨hΦ₁, GlobalTheory.T.seesaw_unfolding_swap hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
      Pi rf rl p p' hm γ hγ ΦD hΦD Φ₁ hΦ₁ hder _ (hdat' _ (hS _ hΦ₁))⟩
  ·
    intro hK
    have hnt := hm.irred.1
    have : ∃ Φ ∈ algF Bs.ψ θ true A B, p Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      have hb : (algF Bs.ψ θ true A B).map p = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨Φ, hΦ, rfl⟩
        exact (Submodule.mem_bot ℂ).2 (hc Φ hΦ)
      rw [hm.mapA.onto] at hb
      exact top_ne_bot hb
    obtain ⟨Φ, hΦ, hp⟩ := this
    obtain ⟨ΦD, hΦD, hd⟩ := hO.algA Φ hΦ
    have hK' : ΦD ∈ K := hK ▸ hΦD
    exact hp (by rw [hdat _ _ hd]; exact hK'.2)
  ·
    intro N hN hKN
    have hNS : ∀ ΦD ∈ N, ΦD ∈ algD Γ.M Bs.ψ Bs.emb := fun ΦD h => hN.1.1 h
    let NI : Submodule ℂ Pi :=
      { carrier := {y | ∃ ΦD ∈ N, p (dF ΦD) = y}
        add_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a + b, add_mem ha hb, by rw [dF_add a (hS _ (hNS _ ha)) b (hS _ (hNS _ hb)), map_add]⟩
        zero_mem' := ⟨0, zero_mem _, by rw [dF_zero, map_zero]⟩
        smul_mem' := by
          rintro c _ ⟨a, ha, rfl⟩
          exact ⟨c • a, Submodule.smul_mem _ c ha, by rw [dF_smul c a (hS _ (hNS _ ha)), map_smul]⟩ }
    have hirr := hm.irred.2 NI ?_ ?_
    · rcases hirr with hb | ht
      · left
        refine le_antisymm (fun ΦD hΦD => ⟨hNS _ hΦD, ?_⟩) hKN
        have : p (dF ΦD) ∈ NI := ⟨ΦD, hΦD, rfl⟩
        rw [hb] at this
        exact (Submodule.mem_bot ℂ).1 this
      · right
        refine le_antisymm (fun ΦD h => hNS _ h) (fun ΦD hΦD => ?_)
        have : p (dF ΦD) ∈ NI := by rw [ht]; trivial
        obtain ⟨ΨD, hΨ, he⟩ := this
        have hd : ΦD - ΨD ∈ K := ⟨sub_mem hΦD (hNS _ hΨ), by
          rw [dF_sub _ (hS _ hΦD) _ (hS _ (hNS _ hΨ)), map_sub, he, sub_self]⟩
        have := add_mem (hKN hd) hΨ
        rwa [sub_add_cancel] at this
    · rintro g hg _ ⟨ΦD, hΦD, rfl⟩
      refine ⟨_, GlobalTheory.T.kapX_finite_action_mem_of_isStabW hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT
        Pi rf rl p p' hm N hN.1 g hg ΦD hΦD, ?_⟩
      rw [(hWf g hg ΦD (hNS _ hΦD)).2, hm.mapA.eqf g hg _ (hAlgF _ (hNS _ hΦD))]
    · rintro τ Y hY _ ⟨ΦD, hΦD, rfl⟩
      obtain ⟨Φ₁D, hΦ₁D, Φ₁, hΦ₁, hd, hder⟩ := GlobalTheory.T.seesaw_unfolding_positive hP D Bs.ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ
        Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm N hN.1 τ Y hY ΦD hΦD (dF ΦD) (hdat' _ (hS _ (hNS _ hΦD)))
      refine ⟨Φ₁D, hΦ₁D, ?_⟩
      rw [← hdat _ _ hd]
      exact hm.mapA.eql τ Y hY _ (hAlgF _ (hNS _ hΦD)) _ hΦ₁ hder
  ·
    intro Φ _ ΦD hΦD hd
    rw [hdat _ _ hd]
    exact ⟨fun h => h.2, fun h => ⟨hΦD, h⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleUnitaryActionUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LocActV

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.WeilM

theorem finite_point_acts_placewise : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
          om (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') ∧
    ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M'.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v) ∧
          om' (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.unramified_places_vacuum_fixed hPr F E σ B a a' G X om om' hT
  have key : ∀ {n : ℕ} (Y : Spc F E n) (M : Model σ Y G.W) (χX χW : Chr F E) (ω : Rep σ Y G.W) (r s r' s' : ℕ),
      GlobalTheory.ThK.IsPair B M χX χW ω r s r' s' →
      (∀ v ∉ S₀, ∀ k ∈ GlobalTheory.InertSph.KAt σ Y v, Acts (evFin F v) (ω (k, 1)) (M.vac v) (M.vac v)) →
      ∀ g : UA σ Y.J, (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) →
      ∀ (f : SInf F (Fin n × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ SB (Fin n × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ SB (Fin n × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = M.vac v) ∧
          (∀ v, φ' v - φ v ∈ augAt ω v) ∧ ω (g, 1) (pure f φ) = pure f φ' := by
    intro n Y M χX χW ω r s r' s' hP hsph g hg f φ hφ hvac
    classical
    obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all σ Y hP.herm.lat g
    have hfin := Filter.eventually_cofinite.1 hvac
    set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) := S₀ ∪ S₁ ∪ hfin.toFinset with hSdef
    obtain ⟨gS, k, hgk, hgS, hkS, hkI, hkL⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ Y g S
    obtain ⟨φ', hφ'SB, hφ'off, hφ'aug, hφ'eq⟩ := GlobalTheory.T.finiteSupport_unitaryPoint_replaces_pureTensorFactors σ B Y G.W M χX χW ω r s r' s' hP S gS hgS f φ hφ hvac
    have hk : ω (k, 1) (pure f φ) = pure f φ := by
      refine GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor_left σ B Y G.W M χX χW ω r s r' s' hP S (fun v hv => hsph v (fun h => hv (by simp [hSdef, h])))
        k (fun u hu => by rw [hkI u hu]; exact hg u hu) hkS (fun w hw z hz => ?_) f φ hφ (fun w hw => ?_)
      · have hw1 : w ∉ S₁ := fun h => hw (by simp [hSdef, h])
        rw [(hkL w hw z hz).1, (hkL w hw z hz).2]
        exact hS₁ w hw1 z hz
      · by_contra hne
        exact hw (by simp [hSdef, hne])
    refine ⟨φ', hφ'SB, ?_, hφ'aug, ?_⟩
    · filter_upwards [hvac, S.finite_toSet.compl_mem_cofinite] with v hv hvS
      rw [hφ'off v hvS, hv]
    · have e : ((g, 1) : UA σ Y.J × UA σ G.W.J) = (gS, 1) * (k, 1) := by
        rw [hgk, Prod.mk_mul_mk, one_mul]
      rw [e, map_mul, Module.End.mul_apply, hk, hφ'eq]
  exact ⟨fun g hg f φ hφ hvac => key G.V G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) (fun v hv => (hS₀ v hv).1) g hg f φ hφ hvac,
    fun g hg f φ hφ hvac => key G.V' G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) (fun v hv => (hS₀ v hv).2) g hg f φ hφ hvac⟩

end GlobalTheory.LocActV
end

