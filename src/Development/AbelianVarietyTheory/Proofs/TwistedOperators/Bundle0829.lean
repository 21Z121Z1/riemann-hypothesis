import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0827
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0814
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0625
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0680
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilDoublingValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly

set_option maxHeartbeats 1000000 in

theorem exists_pure_lieDer_left : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ τ, ∀ Y ∈ lieAt X τ, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W,
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e h.JX (oneP θ X τ Y t)) →
        ∀ Φ ∈ algF ψ θ true A B, ∀ Φ' ∈ algF ψ θ true A B, IsDer θ X (fun g => ωA (1, g)) τ Y Φ Φ' →
        ∃ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
          (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = Γ.M.vac v) ∧
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) ∧
          (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb ∧
          Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∧
          Φ' = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB R Rf hm τ Y hY γ hγ hγt
    Φ hΦ Φ' hΦ' hD
  classical
  have hg := hm.triple.geo
  have hψ' : Bs.ψ = ψ := h.ψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ' ▸ hm.triple.base.std
  have hG : Γ.M.IsGood ψ := hψ' ▸ hg.hM
  obtain ⟨Ψ, hΨ, rfl⟩ := (GlobalTheory.T.seesaw_weil_triple_norm hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB
    R Rf hm).1 Φ hΦ
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 hΨ
  choose f0 φ hf0 hφ hvac hpure using fun i => (g i).2
  let f : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)) := fun i => c i • f0 i
  have hΨeq : Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpure i]
    funext x
    simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, f, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  subst hΨeq
  have hfP : ∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb := fun i => Submodule.smul_mem _ _ (hf0 i)
  obtain ⟨δ, hδ⟩ := GlobalTheory.DerPol.pairDer hP Γ.M Bs.ψ Bs.emb Xc.β (Xc.β / Xc.α) om hm.triple.base.cm hm.triple.base.std
    hm.triple.weil γ hγ
  refine ⟨n, f, fun i => δ (f i), φ, fun i => ⟨hfP i, hφ i, hvac i, (hδ _ (hfP i)).2⟩,
    Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨δ (f i), φ i, (hδ _ (hfP i)).1, hφ i, hvac i, rfl⟩, rfl, ?_⟩
  have hstdi : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
    intro i
    filter_upwards [hg.hM.std, hvac i] with v hv hv'
    rw [hv', hv]
  have hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) :=
    fun i => ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hφ i) (hstdi i)⟩
  have hsum' : ∀ k : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (k i) (φ i) =
        ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(k i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun k =>
    Finset.sum_congr rfl fun i _ => GlobalTheory.EvZeroInf.pure_eq_tens _ _
  have hmem : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hφ i) (hstdi i)
  have hone : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW 1 = 1 := by
    apply Subtype.ext; simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]
  funext x
  have h1 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ (GlobalTheory.TripleRead.ptO (sgn true W).gram e x)
      (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))))) (Φ' x) 0 := by
    refine (hD x).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have h3 := tA _ hmem 1 (oneP θ X τ Y t)
    rw [hone, ← hγt t] at h3
    exact congrFun h3 x
  have h4 := GlobalTheory.T.restriction_line_operator_sum hP Bs Γ Xc om om' hm.triple γ hγ n f (fun i => δ (f i)) (fun i => GlobalTheory.EvZeroInf.finPart (φ i))
    hrest (fun i => (hδ _ (hfP i)).2) (GlobalTheory.TripleRead.ptO (sgn true W).gram e x)
  rw [← hsum', ← hsum', hψ'] at h4
  exact (h4.unique h1).symm

end GlobalTheory.TripleAssembly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly

variable {D : D7}

theorem toUX_one (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) : GlobalTheory.TripleRead.toUX X e hJ 1 = 1 := by
  apply Subtype.ext; apply Units.ext
  show (GlobalTheory.TripleRead.toUX X e hJ 1).1.1 = 1
  rw [GlobalTheory.TripleRead.toUX_val]
  simp [Formalism.L2.Theta.mt]

set_option maxHeartbeats 1000000 in

theorem mapA_mapB_invFin : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ g ∈ GfC W, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (g, 1) Φ) = GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) ∧
          ∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (g, 1) Φ) = GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hL1 := GlobalTheory.T.seesaw_weil_triple_norm hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hL2 := GlobalTheory.T.triple_unitary_action_unipotent hPr D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hM.triple
  refine ⟨fun g hg Φ hΦ => ?_, fun g hg Φ hΦ => ?_⟩
  · have key : ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
        om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W (1) h.JW g, 1) Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb ∧
        GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W (1) h.JW g, 1) Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      have hfin := GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero D W (1 : D.host.E) h.JW g hg
      intro Ψ hΨ
      induction hΨ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
        obtain ⟨φ', hφ', hv', hd, he⟩ := hL2.1 _ hfin f φ hφ hv
        rw [he]
        refine ⟨Submodule.subset_span ⟨f, φ', hf, hφ', hv', rfl⟩, ?_⟩
        unfold GlobalTheory.TripleAssembly.liftPure
        split_ifs with H
        · rw [H.choose_spec f φ' hφ' hv', H.choose_spec f φ hφ hv]
          congr 2
          funext v
          have := hM.fin.inv v (hd v)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this
        · rfl
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add, map_add, map_add, hx.2, hy.2]
        exact ⟨Submodule.add_mem _ hx.1 hy.1, rfl⟩
      | smul c x _ hx =>
        rw [map_smul, map_smul, map_smul, hx.2]
        exact ⟨Submodule.smul_mem _ c hx.1, rfl⟩
    obtain ⟨Ψ, hΨ, rfl⟩ := hL1.1 Φ hΦ
    have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hM.triple.geo.hM hΨ
    have e1 := hTA Ψ hS g 1
    rw [toUX_one] at e1
    refine (congrArg (⇑(GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf)) e1.symm).trans ?_
    obtain ⟨k1, k2⟩ := key Ψ hΨ
    unfold GlobalTheory.TripleAssembly.mapA
    unfold GlobalTheory.TripleAssembly.thetaLift
    split_ifs with H
    · rw [H.choose_spec _ k1, H.choose_spec _ hΨ, k2]
    · rfl
  · have key : ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
        om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ g, 1) Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb ∧
        GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ g, 1) Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      have hfin := GlobalTheory.T.archSupported_smul_conjugateUnitary_sub_one_eq_zero D W₁ (-1 : D.host.E) h.JW₁ g hg
      intro Ψ hΨ
      induction hΨ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
        obtain ⟨φ', hφ', hv', hd, he⟩ := hL2.2 _ hfin f φ hφ hv
        rw [he]
        refine ⟨Submodule.subset_span ⟨f, φ', hf, hφ', hv', rfl⟩, ?_⟩
        unfold GlobalTheory.TripleAssembly.liftPure
        split_ifs with H
        · rw [H.choose_spec f φ' hφ' hv', H.choose_spec f φ hφ hv]
          congr 2
          funext v
          have := hM.fin.inv' v (hd v)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this
        · rfl
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add, map_add, map_add, hx.2, hy.2]
        exact ⟨Submodule.add_mem _ hx.1 hy.1, rfl⟩
      | smul c x _ hx =>
        rw [map_smul, map_smul, map_smul, hx.2]
        exact ⟨Submodule.smul_mem _ c hx.1, rfl⟩
    obtain ⟨Ψ, hΨ, rfl⟩ := hL1.2 Φ hΦ
    have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM' hΨ
    have e1 := hTB Ψ hS g 1
    rw [toUX_one] at e1
    refine (congrArg (⇑(GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf)) e1.symm).trans ?_
    obtain ⟨k1, k2⟩ := key Ψ hΨ
    unfold GlobalTheory.TripleAssembly.mapB
    unfold GlobalTheory.TripleAssembly.thetaLift
    split_ifs with H
    · rw [H.choose_spec _ k1, H.choose_spec _ hΨ, k2]
    · rfl

end GlobalTheory.TripleAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly.ReadDerB

private theorem pure_smul_twisted_operators {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ)
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Ψ : (Fin n × Fin d → AF F) → ℂ} (hΨ : Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ) :
    ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ τ ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = M.vac v)) ∧
      Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i) := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
    exact ⟨1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, hv⟩, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, f₁, φ₁, h₁, rfl⟩ := hx
    obtain ⟨m₂, f₂, φ₂, h₂, rfl⟩ := hy
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h₁ j
      · simpa using h₂ j
    · simp [Fin.sum_univ_add]
  | smul c x _ hx =>
    obtain ⟨m, f, φ, h, rfl⟩ := hx
    refine ⟨m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ τ).smul_mem c (h i).1, (h i).2⟩, ?_⟩
    simp [Finset.smul_sum, pure_smul_twisted_operators]

theorem read_lieDer : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ τ, ∀ Y ∈ lieAt X τ, ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W,
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e h.JX (oneP θ X τ Y t)) →
        ∀ Φ ∈ algF ψ θ false A₁ B, ∀ Φ' ∈ algF ψ θ false A₁ B, IsDer θ X (fun g => ωB (1, g)) τ Y Φ Φ' →
        ∃ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
          (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          (∀ i, f i ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v) ∧
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) ∧
          (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb ∧
          Φ = GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∧
          Φ' = GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hwA hwB e Bs Γ Xc om om' h htA htB R Rf hM τ Y hY γ hγ hγt Φ hΦ Φ' hΦ' hD
  have hψe := h.ψ
  subst hψe
  obtain ⟨Ψ, hΨ, hΦeq⟩ := (GlobalTheory.T.seesaw_weil_triple_norm hH hP D Bs.ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hwA hwB e Bs Γ Xc om om' h
    htA htB R Rf hM).2 Φ hΦ
  obtain ⟨m, f, φ, hfφ, hΨeq⟩ := exists_sum_pure Γ.M' Bs.ψ Bs.emb hΨ
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_line_operator_polynomial hP Bs Γ Xc om om' hM.triple γ hγ
  have hΨs : Ψ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)) :=
    GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM' hΨ
  refine ⟨m, f, fun i => δ (f i), φ,
    fun i => ⟨(hfφ i).1, (hfφ i).2.1, (hfφ i).2.2, (hδ (f i) (hfφ i).1).2⟩, ?_, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨δ (f i), φ i, (hδ (f i) (hfφ i).1).1, (hfφ i).2.1, (hfφ i).2.2, rfl⟩
  · rw [← hΦeq, hΨeq]
  · funext x

    have key : ∀ t : ℝ, ωB (1, oneP θ X τ Y t) Φ x = GlobalTheory.WeilM.thetaSum D.host.F
        (Γ.M'.co.rho Bs.ψ (GlobalTheory.TripleRead.ptO (sgn false W₁).gram e x)
          (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))) := by
      intro t
      rw [← hΦeq, ← htB Ψ hΨs 1 (oneP θ X τ Y t), GlobalTheory.LocWeilAct.conjU_one', ← hγt t, hΨeq]
      rfl
    have hd := GlobalTheory.T.weil_model_standard_character hP Γ.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hM.triple.base.cm hM.triple.base.std
      hM.triple.geo.hM' hM.triple.weil' γ hγ m f (fun i => δ (f i)) φ (fun i => ⟨(hfφ i).2.1, (hfφ i).2.2⟩)
      (fun i => (hδ (f i) (hfφ i).1).2) (GlobalTheory.TripleRead.ptO (sgn false W₁).gram e x)
    have hDx : HasDerivAt (fun t : ℝ => ωB (1, oneP θ X τ Y t) Φ x) (Φ' x) 0 := hD x
    rw [show (fun t : ℝ => ωB (1, oneP θ X τ Y t) Φ x) = _ from funext key] at hDx
    exact hDx.unique hd

end GlobalTheory.TripleAssembly.ReadDerB

end
end

