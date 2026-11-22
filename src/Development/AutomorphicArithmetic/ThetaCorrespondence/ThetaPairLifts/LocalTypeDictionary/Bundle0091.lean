import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0828
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0089
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0830
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0829
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0088
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0042

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleMapsEquivariantOnFiniteVectors
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly.EqFin
end GlobalTheory.TripleAssembly.EqFin
namespace GlobalTheory.TripleAssembly.EqFin
set_option maxHeartbeats 2000000 in
theorem theta_triple_maps_equivariant_on_finite_vectors : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        (∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨oA, -⟩ := _root_.GlobalTheory.T.triple_algebra_map_surjective hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨⟨dA, rA⟩, ⟨dB, rB⟩⟩ :=
    _root_.GlobalTheory.T.triple_twist_transport hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have gM : Γ.M.IsGood Bs.ψ := hM.triple.geo.hM
  have gM' : Γ.M'.IsGood Bs.ψ := hM.triple.geo.hM'
  have c1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW 1 = 1 := Subtype.ext ((congrArg _ (map_one (matHom W))).trans (map_one _))
  have c1' : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ 1 = 1 := Subtype.ext ((congrArg _ (map_one (matHom W₁))).trans (map_one _))
  have hsA : ∀ᶠ v in Filter.cofinite, Rf.p v (Γ.M.vac v) = GlobalTheory.TripleAssembly.vacIm Γ Rf v :=
    Filter.Eventually.of_forall fun v => rfl
  have hsB : ∀ᶠ v in Filter.cofinite, Rf.p' v (Γ.M'.vac v) = GlobalTheory.TripleAssembly.vacIm Γ Rf v := by
    refine Filter.eventually_cofinite.2 ((Xc.T.finite_toSet).subset fun v hv => ?_)
    by_contra hn
    exact hv (hM.fin.sph v hn).1.symm
  have key : ∀ g ∈ GfC X, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
      ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
    intro g hg
    obtain ⟨hv, hvU, fA, fB⟩ := _root_.GlobalTheory.T.theta_pure_tensor_placewise_finite hP D W W₁ X e Bs Γ Xc om om' R Rf hM h.JX g hg
    choose a ha using fun v => GlobalTheory.T.exists_localOperator_thetaQuotient_finitePlace D.sp.cm.sig W.rank W₁.rank Bs Γ Xc om om' R Rf hM v (hv v) (hvU v)
    obtain ⟨T₀, hT₀⟩ := GlobalTheory.TripleAssembly.exists_rtensOp (GlobalTheory.TripleAssembly.vacIm Γ Rf) a
    refine ⟨LinearMap.lTensor R.Pi T₀, ?_, ?_⟩
    · have st := GlobalTheory.TripleAssembly.EqFin.darbAlg_stable Γ.M Bs.ψ Bs.emb gM R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) hsA
        (om (1, GlobalTheory.TripleRead.toUX X e h.JX g)) T₀ (fun f φ hφ hφv => by
          obtain ⟨φ₁, h1, h1v, hAct, hO⟩ := fA f φ hφ hφv
          refine ⟨φ₁, h1, h1v, hO, ?_⟩
          rw [hT₀ _ (Filter.eventually_cofinite.1 ((hφv.and hsA).mono fun v hv' => by rw [hv'.1, hv'.2]))]
          congr 1
          funext v
          exact (ha v).1 (φ v) (hφ v) (φ₁ v) (h1 v) (hAct v))
      intro Φ hΦ
      obtain ⟨Ψ, hΨ, rfl⟩ := rA Φ hΦ
      have hs := GlobalTheory.TripleAssembly.darbAlg_le_schA D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb gM hΨ
      have e1 := hTA Ψ hs 1 g
      rw [c1] at e1
      have s1 := (st Ψ hΨ).1
      have s2 := (st Ψ hΨ).2
      have d1 := dA _ s1
      have d2 := dA Ψ hΨ
      have x1 := congrArg (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) e1.symm
      have x2 := congrArg (LinearMap.lTensor R.Pi T₀) d2.symm
      exact x1.trans (d1.trans (s2.trans x2))
    · have st := GlobalTheory.TripleAssembly.EqFin.darbAlg_stable Γ.M' Bs.ψ Bs.emb gM' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) hsB
        (om' (1, GlobalTheory.TripleRead.toUX X e h.JX g)) T₀ (fun f φ hφ hφv => by
          obtain ⟨φ₁, h1, h1v, hAct, hO⟩ := fB f φ hφ hφv
          refine ⟨φ₁, h1, h1v, hO, ?_⟩
          rw [hT₀ _ (Filter.eventually_cofinite.1 ((hφv.and hsB).mono fun v hv' => by rw [hv'.1, hv'.2]))]
          congr 1
          funext v
          exact (ha v).2 (φ v) (hφ v) (φ₁ v) (h1 v) (hAct v))
      intro Φ hΦ
      obtain ⟨Ψ, hΨ, rfl⟩ := rB Φ hΦ
      have hs := GlobalTheory.TripleAssembly.darbAlg_le_schA D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb gM' hΨ
      have e1 := hTB Ψ hs 1 g
      rw [c1'] at e1
      exact (congrArg (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf) e1.symm).trans ((dB _ (st Ψ hΨ).1).trans
        (((st Ψ hΨ).2).trans (congrArg (LinearMap.lTensor R.Pi T₀) (dB Ψ hΨ).symm)))
  have opEq : ∀ g, ∀ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) →
      GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g = T := by
    intro g T hTg
    have H : ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), ∀ Φ ∈ algF ψ θ true A B,
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) := ⟨T, hTg⟩
    unfold GlobalTheory.TripleAssembly.opFin
    rw [dif_pos H]
    apply LinearMap.ext
    intro y
    have hy : y ∈ (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) := by rw [oA]; trivial
    obtain ⟨Φ, hΦ, rfl⟩ := hy
    rw [← H.choose_spec Φ hΦ, hTg Φ hΦ]
  refine ⟨fun g hg Φ hΦ => ?_, fun g hg Φ hΦ => ?_⟩
  · obtain ⟨T, h1, -⟩ := key g hg
    rw [opEq g T h1]
    exact h1 Φ hΦ
  · obtain ⟨T, h1, h2⟩ := key g hg
    rw [opEq g T h1]
    exact h2 Φ hΦ
end GlobalTheory.TripleAssembly.EqFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_triple_maps_equivariant : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
        (∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.EqFin.theta_triple_maps_equivariant_on_finite_vectors | exact _root_.GlobalTheory.TripleAssembly.EqFin.theta_triple_maps_equivariant_on_finite_vectors | (intros; apply _root_.GlobalTheory.TripleAssembly.EqFin.theta_triple_maps_equivariant_on_finite_vectors <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleMapCompInverseFinite
section
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
set_option maxHeartbeats 1000000 in
theorem triple_map_comp_inverse_finite : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
  have hL1 := _root_.GlobalTheory.T.triple_invariant_theta_surjective hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hL2 := _root_.GlobalTheory.T.local_action_finite_places hPr D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hM.triple
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

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_assembly_inverse_finite : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
  first | exact @_root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite | exact _root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite | (intros; apply _root_.GlobalTheory.TripleAssembly.triple_map_comp_inverse_finite <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleProductLieDerivLeftPureTensor
section
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
theorem exists_pure_tensor_lieDeriv_left_factor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
  obtain ⟨Ψ, hΨ, rfl⟩ := (_root_.GlobalTheory.T.triple_invariant_theta_surjective hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hA hB e Bs Γ Xc om om' h tA tB
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
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.DerPol.polarization_pair_derivation hP Γ.M Bs.ψ Bs.emb Xc.β (Xc.β / Xc.α) om hm.triple.base.cm hm.triple.base.std
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
  have h4 := _root_.GlobalTheory.T.twisted_theta_line_derivative hP Bs Γ Xc om om' hm.triple γ hγ n f (fun i => δ (f i)) (fun i => GlobalTheory.EvZeroInf.finPart (φ i))
    hrest (fun i => (hδ _ (hfP i)).2) (GlobalTheory.TripleRead.ptO (sgn true W).gram e x)
  rw [← hsum', ← hsum', hψ'] at h4
  exact (h4.unique h1).symm
end GlobalTheory.TripleAssembly
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tripleProduct_lieDeriv_left_pure_tensor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
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
  first | exact @_root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor | exact _root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor | (intros; apply _root_.GlobalTheory.TripleAssembly.exists_pure_tensor_lieDeriv_left_factor <;> assumption)
end
end

