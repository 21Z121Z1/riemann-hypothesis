import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0810
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0726
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0814
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0793
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0806
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0779
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0731
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0777
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0580
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0807
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0686
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0723
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0690
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0803
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0804
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0703
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0691
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0797
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0696
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0754
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0792

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralFactorisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem matchKerP : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (p Φ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD 0) := by
  intro hU hR hM hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hRf Pi rf rl p p' hm
    Φ hΦ ΦD hΦD hD
  obtain ⟨K₁, g₁, ne₁, max₁, h₁⟩ := GlobalTheory.T.seesaw_unfolding_measure hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨K₂, g₂, ne₂, h₂⟩ := GlobalTheory.T.matched_maps_triple_factor hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf
  have hle : K₁ ≤ K₂ := fun x hx =>
    (h₂ x (g₁.1.1 hx)).2 (GlobalTheory.T.triple_geometry_unitary hU hR hM hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf K₁ g₁ ne₁ x hx)
  rcases max₁ K₂ g₂ hle with h | h
  · rw [← h₁ Φ hΦ ΦD hΦD hD, ← h, h₂ ΦD hΦD]
  · exact absurd h ne₂

theorem matchKerPPrime : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hU hR hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := GlobalTheory.T.seesaw_unfolding_fundamental_domain hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := GlobalTheory.T.matched_maps_finite_identity hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, GlobalTheory.T.matched_maps_real_finite hU hR hMi hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (GlobalTheory.T.seesaw_unfolding_integrable hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0

theorem matchUpToScalar : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ s : ℂ, s ≠ 0 ∧ ∀ Φ ∈ algF ψ θ true A B, ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ ΦD Φ₀D,
      IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Φ₀D ∈ Γ.M'.So Bs.ψ Bs.τ₁ → p Φ = p' Φ₀ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match Bs Γ Xc R Rf ΦD (s • Φ₀D) := by
  intro hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hTD.base.std
  have dA := GlobalTheory.SquareAgree.isDatum_linear Γ.M ψ hstd cA
  have dB := GlobalTheory.SquareAgree.isDatum_linear Γ.M' ψ hstd cB
  have lin := GlobalTheory.PolMatchLin.polMatch_linear Bs Γ Xc om om' R Rf hR.fin
  let G : Set (Pi × Pi) := {x | ∃ Φ ∈ algF ψ θ true A B, ∃ Φ₀ ∈ algF ψ θ false A₁ B, ∃ ΦD ∈ algD Γ.M Bs.ψ Bs.emb,
      ∃ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ ∧ IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D ∧ x = (p Φ, p' Φ₀)}
  have G0 : (0 : Pi × Pi) ∈ G :=
    ⟨0, zero_mem _, 0, zero_mem _, 0, zero_mem _, 0, zero_mem _, dA.1, dB.1, lin.1, Prod.ext (map_zero p).symm (map_zero p').symm⟩
  have Glin : ∀ x ∈ G, ∀ y ∈ G, ∀ c : ℂ, x + c • y ∈ G := by
    rintro _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩ _ ⟨Ψ, hΨ, Ψ₀, hΨ₀, ΨD, hΨD, Ψ₀D, hΨ₀D, k1, k2, k3, rfl⟩ c
    exact ⟨Φ + c • Ψ, add_mem hΦ (Submodule.smul_mem _ c hΨ), Φ₀ + c • Ψ₀, add_mem hΦ₀ (Submodule.smul_mem _ c hΨ₀),
      ΦD + c • ΨD, add_mem hΦD (Submodule.smul_mem _ c hΨD), Φ₀D + c • Ψ₀D, add_mem hΦ₀D (Submodule.smul_mem _ c hΨ₀D),
      dA.2 _ _ _ _ c h1 k1, dB.2 _ _ _ _ c h2 k2, lin.2 _ _ _ _ c h3 k3, by ext <;> simp⟩
  let S : Submodule ℂ (Pi × Pi) :=
    { carrier := G
      add_mem' := fun {x y} hx hy => by simpa using Glin x hx y hy 1
      zero_mem' := G0
      smul_mem' := fun c x hx => by simpa using Glin 0 G0 x hx c }
  have stf : ∀ g ∈ GfC X, ∀ x ∈ S, (rf g x.1, rf g x.2) ∈ S := by
    rintro g hg _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
    have a1 := hM.mapA.stabX.1 g hg Φ hΦ
    have b1 := hM.mapB.stabX.1 g hg Φ₀ hΦ₀
    obtain ⟨ΨD, hΨD, hΨ⟩ := hO.algA _ a1
    obtain ⟨Ψ₀D, hΨ₀D, hΨ₀⟩ := hO.algB _ b1
    have e1 := GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstd cA _ _ _ hΨ (hO.weilA ΦD Φ h1 1 g)
    have e2 := GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hΨ₀ (hO.weilB Φ₀D Φ₀ h2 1 g)
    refine ⟨_, a1, _, b1, ΨD, hΨD, Ψ₀D, hΨ₀D, hΨ, hΨ₀, ?_, ?_⟩
    · rw [e1, e2]
      exact GlobalTheory.SquareAgree.polMatch_kapX hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM g hg ΦD hΦD Φ₀D hΦ₀D h3
    · rw [hM.mapA.eqf g hg Φ hΦ, hM.mapB.eqf g hg Φ₀ hΦ₀]
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, (rl τ Y x.1, rl τ Y x.2) ∈ S := by
    rintro τ Y hY _ ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
    obtain ⟨Φ', hΦ', hd⟩ := hM.mapA.stabX.2 τ Y hY Φ hΦ
    obtain ⟨Φ₀', hΦ₀', hd₀⟩ := hM.mapB.stabX.2 τ Y hY Φ₀ hΦ₀
    obtain ⟨ΨD, hΨD, hΨ⟩ := hO.algA _ hΦ'
    obtain ⟨Ψ₀D, hΨ₀D, hΨ₀⟩ := hO.algB _ hΦ₀'
    refine ⟨Φ', hΦ', Φ₀', hΦ₀', ΨD, hΨD, Ψ₀D, hΨ₀D, hΨ, hΨ₀,
      GlobalTheory.SquareAgree.LieEq.polMatch_der hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM τ Y hY Φ hΦ Φ' hΦ' Φ₀ hΦ₀ Φ₀' hΦ₀' hd hd₀ ΦD hΦD ΨD hΨD Φ₀D hΦ₀D Ψ₀D hΨ₀D h1 hΨ h2 hΨ₀ h3, ?_⟩
    rw [hM.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hd, hM.mapB.eql τ Y hY Φ₀ hΦ₀ Φ₀' hΦ₀' hd₀]
  have k1 : ∀ x : Pi, ((x, 0) : Pi × Pi) ∈ S → x = 0 := by
    rintro x ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, hx⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, h0⟩ := hx
    have m0 := (matchKerPPrime hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ₀ hΦ₀ Φ₀D hΦ₀D h2).1 h0.symm
    have m1 := lin.2 _ _ _ _ (-1) h3 m0
    rw [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at m1
    exact (matchKerP hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ hΦ ΦD hΦD h1).2 m1
  have k2 : ∀ y : Pi, ((0, y) : Pi × Pi) ∈ S → y = 0 := by
    rintro y ⟨Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, hy⟩
    simp only [Prod.mk.injEq] at hy
    obtain ⟨h0, rfl⟩ := hy
    have m0 := (matchKerP hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ hΦ ΦD hΦD h1).1 h0.symm
    have m1 := lin.2 _ _ _ _ (-1) h3 m0
    rw [smul_zero, add_zero, neg_one_smul, add_neg_cancel] at m1
    exact (matchKerPPrime hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM Φ₀ hΦ₀ Φ₀D hΦ₀D h2).2 m1
  have on : ∀ x : Pi, ∃ y : Pi, ((x, y) : Pi × Pi) ∈ S := by
    intro x
    have hx : x ∈ (algF ψ θ true A B).map p := hM.mapA.onto ▸ Submodule.mem_top
    obtain ⟨Φ, hΦ, rfl⟩ := hx
    obtain ⟨ΦD, hΦD, h1⟩ := hO.algA Φ hΦ
    obtain ⟨Φ₀D, hΦ₀D, h3⟩ := GlobalTheory.SquareAgree.polMatch_onto Bs Γ Xc om om' R Rf hR ΦD hΦD
    obtain ⟨Φ₀, hΦ₀, h2⟩ := hO.algB' Φ₀D hΦ₀D
    exact ⟨p' Φ₀, Φ, hΦ, Φ₀, hΦ₀, ΦD, hΦD, Φ₀D, hΦ₀D, h1, h2, h3, rfl⟩
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.SquareAgree.eq_smul_of_stable_graph D X Pi rf rl hM.irred (GlobalTheory.SquareAgree.rank_pi_le_aleph0 hU hRe hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM) S stf stl k1 k2 on
  refine ⟨c, hc0, ?_⟩
  intro Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
  obtain ⟨ΦD', hΦD', h1⟩ := hO.algA Φ hΦ
  have hΦD : ΦD ∈ algD Γ.M Bs.ψ Bs.emb := (GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstd cA _ _ _ hD h1) ▸ hΦD'
  obtain ⟨Φ₀D', hΦ₀D', h2⟩ := hO.algB Φ₀ hΦ₀
  have hΦ₀D : Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb := (GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hD₀ h2) ▸ hΦ₀D'
  obtain ⟨Φ₁D, hΦ₁D, m1⟩ := GlobalTheory.SquareAgree.polMatch_onto Bs Γ Xc om om' R Rf hR ΦD hΦD
  obtain ⟨Φ₁, hΦ₁, h4⟩ := hO.algB' Φ₁D hΦ₁D
  have hy := hc (p Φ) (p' Φ₁) ⟨Φ, hΦ, Φ₁, hΦ₁, ΦD, hΦD, Φ₁D, hΦ₁D, hD, h4, m1, rfl⟩
  have h5 := dB.2 _ _ _ _ (-c) h4 hD₀
  have hz : p' (Φ₁ + (-c) • Φ₀) = 0 := by rw [map_add, map_smul, hy, hp, neg_smul, add_neg_cancel]
  have m2 := (matchKerPPrime hU hRe hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR Pi rf rl p p' hM _ (add_mem hΦ₁ (Submodule.smul_mem _ _ hΦ₀)) _
    (add_mem hΦ₁D (Submodule.smul_mem _ _ hΦ₀D)) h5).1 hz
  have m3 := lin.2 _ _ _ _ (-1) m1 m2
  have e3 : Φ₁D + (-1 : ℂ) • (Φ₁D + (-c) • Φ₀D) = c • Φ₀D := by module
  rw [smul_zero, add_zero, e3] at m3
  exact GlobalTheory.SquareAgree.PolMatchConst.match_of_polMatch Bs Γ Xc om om' R Rf hTD _ _ m3 (Submodule.smul_mem _ c hSo)

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerPIffPolMatchZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem GlobalTheory.SquareAgree.ker_p_iff_polMatch_zero : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ ∈ algF ψ θ true A B, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ → (p Φ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD 0) := by
  intro hU hR hM hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hRf Pi rf rl p p' hm
    Φ hΦ ΦD hΦD hD
  obtain ⟨K₁, g₁, ne₁, max₁, h₁⟩ := GlobalTheory.T.seesaw_unfolding_measure hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨K₂, g₂, ne₂, h₂⟩ := GlobalTheory.T.matched_maps_triple_factor hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf
  have hle : K₁ ≤ K₂ := fun x hx =>
    (h₂ x (g₁.1.1 hx)).2 (GlobalTheory.T.triple_geometry_unitary hU hR hM hP _ _ _ Bs _ _ Γ Xc om om' hT' R Rf hRf K₁ g₁ ne₁ x hx)
  rcases max₁ K₂ g₂ hle with h | h
  · rw [← h₁ Φ hΦ ΦD hΦD hD, ← h, h₂ ΦD hΦD]
  · exact absurd h ne₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PPrimeEqZeroIffPolMatch
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem pPrime_eq_zero_iff_polMatch : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ Φ₀ ∈ algF ψ θ false A₁ B, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → (p' Φ₀ = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ₀D) := by
  intro hU hR hG hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT' R Rf hM Pi rf rl p p' hm
    Φ₀ hΦ₀ Φ₀D hΦ₀D hD
  obtain ⟨K, hK, hKs, hKne⟩ := GlobalTheory.T.seesaw_unfolding_fundamental_domain hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm
  obtain ⟨KD, hKD, hKDs, hKDne⟩ := GlobalTheory.T.matched_maps_finite_identity hP Bs Γ Xc om om' R Rf hM
  have h1 : K ≤ KD := fun Φ hΦ => (hKD Φ).2 ⟨hKs.le hΦ, GlobalTheory.T.matched_maps_real_finite hU hR hG hP Bs Γ Xc om om' R Rf hM K hKs hKne Φ hΦ⟩
  have h2 : KD = K := (GlobalTheory.T.seesaw_unfolding_integrable hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hT'
    Pi rf rl p p' hm K KD hK hKDs h1).resolve_right hKDne
  constructor
  · intro h0
    have hm : Φ₀D ∈ K := (hK Φ₀D).2 ⟨hΦ₀D, Φ₀, hΦ₀, hD, h0⟩
    rw [← h2] at hm
    exact ((hKD _).1 hm).2
  · intro hpm
    have hm : Φ₀D ∈ KD := (hKD _).2 ⟨hΦ₀D, hpm⟩
    rw [h2] at hm
    obtain ⟨_, Φ₁, _, hD₁, h0⟩ := (hK _).1 hm
    rw [IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD hD₁]
    exact h0

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareTripleFinitePlacesOfOrientedRoutesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareTriple_finitePlaces_of_orientedRoutes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ (M : Vol G), M.Is t → ∀ (en : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G ↑i ↑j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G ↑i ↑j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) om om',
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t ↑i ↑j en Bs Γ X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j) ∧ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j)) ∨
      (¬ GlobalTheory.WeilParts.NonSplitAt D v ε ∧ ¬ GlobalTheory.WeilParts.UnramAt ε (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t ↑i ↑j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G ↑i ↑j) ∧
        ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.TripleRam.ram_clause | exact GlobalTheory.TripleRam.ram_clause | (intros; apply GlobalTheory.TripleRam.ram_clause <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingOfCuspidalLifts
section
open GlobalTheory.RowClaim GlobalTheory.RowVal GlobalTheory.RowReal

namespace GlobalTheory.RowUnfLast

theorem stepUnfold : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := fun p c s =>
  have rel := GlobalTheory.T.lastRow_real_iterated_integral_eq_const_mul_finite
  have hcv := GlobalTheory.T.cellSumRelationsPassToIntegrals_proof
  have grp := GlobalTheory.T.rowPeriodGroups_split_real_finite_large_depth
  have it := GlobalTheory.T.iteration_and_linearity_cuspidal
  have inv := GlobalTheory.T.unfolded_integrand_biInvariant_large_depth
  have flat := GlobalTheory.RowFlatAsm.flatAt_big
  have supp := GlobalTheory.T.integrand_supported_on_cells_largeDepth
  have rep := GlobalTheory.T.representation_at_every_place
  have val := GlobalTheory.T.rowTest_cellValue_of_steps_large_depth
  have off := GlobalTheory.T.singleCosetOffTwistPlaces_largeDepth
  have tens := GlobalTheory.T.definitePeriod_depends_on_productFunction
  have vol := GlobalTheory.T.rowTest_definitePeriod_change_of_measures
  have wt := GlobalTheory.T.cell_masses_against_level_volumes_large_depth
  have fock := GlobalTheory.T.periodReductionToFockVectors_large_depth
  have bas := GlobalTheory.T.lastRow_unfolding_basicHypotheses
  have one := GlobalTheory.T.rowTest_support_families_staircase_cosets
  have rl := GlobalTheory.RowReal.realLine
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rel, grp⟩, it⟩, inv⟩, ⟨e, fl⟩⟩, supp⟩, rep⟩, val⟩, off⟩, tens⟩, vol⟩, wt⟩, fock⟩, bas⟩, one⟩, rl⟩, s⟩ =>
    rel grp it.1 it.2 inv ⟨e, supp e fl off inv tens bas, rep e, val e fl tens vol (wt e) fock bas one s⟩ rl s)
  (((((((((((((((((rel hcv).and grp).and (it p c)).and inv).and flat).and supp).and rep).and val).and off).and tens).and vol).and wt).and fock).and bas).and one).and rl).and s)

end GlobalTheory.RowUnfLast
end

