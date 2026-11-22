import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoConst
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0097
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0020
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3651
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0096
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IntertwineOfCompatibleMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3653
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0022
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0038
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0009
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0016
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0071

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvStageGeoConst
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.StageGeo
variable {D : D7} {T : Type} {A A' WW : HSp D} {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E} {S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))}
  {FA : Fr A} {FA' : Fr A'} {FW : Fr WW} {Bs : Base D.host.F D.host.E} {Γ : Geo D.sp.cm.sig A.rank A'.rank}
theorem geometric_stage_constant_ratio (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hX : X.Is ψ θ α β νH S) (hG : IsStageGeo ψ X FA FA' FW hX.rank Bs Γ) {a b : D.what₂.Tau → ℚ}
    (hd : ∀ t : T, IsTriple A A' WW (α t) (β t) ∧ (∀ τ, HasInfExp D (α t) τ (a τ) ∧ HasInfExp D (β t) τ (b τ)) ∧
      IsFinF ψ θ true FA FW (X.f t) ∧ IsFinF ψ θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (fockF ψ θ true FA FW (X.f t) P) = X.ker ψ θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (fockF ψ θ false FA' FW (X.f' t) P) = X.ker' ψ θ t P h g)
    {lam : T → ℂ} (hF : GlobalTheory.ConstRatio.Factor X ψ θ lam) {t₁ t₂ : T} {X₁ X₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E}
    (r₁ : Reads α β S Bs t₁ X₁) (r₂ : Reads α β S Bs t₂ X₂) {R om₁ om₁' Rf₁ om₂ om₂' Rf₂} {c₁ c₂ : ℂ}
    (m₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X₁ om₁ om₁' R Rf₁) (m₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X₂ om₂ om₂' R Rf₂)
    (k₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ X₁ om₁ om₁' R Rf₁ c₁) (k₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ X₂ om₂ om₂' R Rf₂ c₂) :
    c₁ * lam t₂ = c₂ * lam t₁ := by
  have hψ := hX.isVac.1
  have hθ := hX.isVac.2.inf
  obtain ⟨g, g0, hg⟩ := exists_vac (ε := true) hG.pairA hG.latA hX.isVac
  obtain ⟨g', g0', hg'⟩ := exists_vac (ε := false) hG.pairB hG.latB hX.isVac'
  have hco : ∀ {κ : Type} (T₀ : Finset (HeightOneSpectrum (𝓞 D.host.F)))
      {φ vac : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (κ → Fv D.host.F v) → ℂ}, (∀ v ∉ T₀, φ v = vac v) →
      ∀ᶠ v in Filter.cofinite, φ v = vac v := fun T₀ _ _ h =>
    Filter.Eventually.mono T₀.finite_toSet.compl_mem_cofinite fun v hv => h v hv
  obtain ⟨Φ, Φ', hΦ, hΦ', eΦ, eΦ'⟩ : ∃ (Φ : PolF D WW.rank A.rank →ₗ[ℂ] SInf D.host.F (Fin A.rank × Fin (A.rank + A'.rank)))
      (Φ' : PolF D WW.rank A'.rank →ₗ[ℂ] SInf D.host.F (Fin A'.rank × Fin (A.rank + A'.rank))),
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧ LinearMap.range Φ' = Γ.M'.Pol Bs.ψ Bs.emb ∧
      (∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) → ∀ P,
        thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
          fockF ψ θ true FA FW (thO Γ.M ψ (sgn true A).gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P) ∧
      ∀ φ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) → ∀ P,
        thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ' P) φ) =
          fockF ψ θ false FA' FW (thO Γ.M' ψ (sgn false A').gram (finCongr hX.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ)) P := by
    obtain ⟨φ, φ', s, s', v, v', n, n', -, e, e'⟩ := exists_fin hX hG r₁ m₁ hg hg'
    obtain ⟨Φ, h1, h2⟩ := UpperTheory.thetaLift_pure_tensor_of_isFinF D ψ true A WW _ hX.rank Bs Γ.V Γ.W Γ.M hG.pairA θ hθ FA FW hG.cartA g g0 φ s (hco _ v) n
      (e ▸ (hd t₁).2.2.1)
    obtain ⟨Φ', h1', h2'⟩ := UpperTheory.thetaLift_pure_tensor_of_isFinF D ψ false A' WW _ hX.rank Bs Γ.V' Γ.W Γ.M' hG.pairB θ hθ FA' FW hG.cartB g' g0' φ' s'
      (hco _ v') n' (e' ▸ (hd t₁).2.2.2.1)
    exact ⟨Φ, Φ', h1, h1', h2, h2'⟩
  obtain ⟨-, Pi, p, p', J, -, hJ, -, hI, hI', P', hP', hint⟩ := hF
  have mP' : Φ' P' ∈ Γ.M'.Pol Bs.ψ Bs.emb := hΦ' ▸ LinearMap.mem_range_self _ _
  obtain ⟨f, mf, ef⟩ : R.p' (Φ' P') ∈ (Γ.M.Pol Bs.ψ Bs.emb).map R.p := by rw [m₁.real.quot.onto]; trivial
  obtain ⟨P, rfl⟩ : f ∈ LinearMap.range Φ := hΦ ▸ mf
  obtain ⟨Pr, qm, qm', -, -, hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ A A' WW FA FA' FW a b
  have key : ∀ t Xc om om' Rf c, Reads α β S Bs t Xc → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ Xc om om' R Rf c → lam t • p P = c • p' P' := by
    intro t Xc om om' Rf c r m k
    obtain ⟨hT, hE, -, -, hk, hk'⟩ := hd t
    obtain ⟨Pim, rf, rl, pm, pm', hmm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hP.howeDualityReal hP hK hM D ψ θ hψ hθ A A' WW FA FA' FW _ _ hT
      (hLM _ _ hT hE).1 (X.ω t) (X.ω' t) (hX.weil t) (hX.weil' t)
    obtain ⟨φ, φ', s, s', v, v', -, -, l, e, e'⟩ := exists_fin hX hG r m hg hg'
    obtain ⟨cA, cB, hO, dA, dB⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D ψ θ hθ T A A' WW X FA FA' FW hX.rank Bs Γ hG Xc om om' m.triple (X.ω t) (X.ω' t)
      (by rw [r.eα, r.eβ]; exact hX.weil t) (by rw [r.eα, r.eβ]; exact hX.weil' t)
    rw [r.eα, r.eβ] at hO
    have d1 := dA _ (GlobalTheory.TensUniq.pure_mem_schA (Φ P) φ s (((hco _ v).and m.triple.geo.hM.std).mono fun v h => h.1.trans h.2))
    have d2 := dB _ (GlobalTheory.TensUniq.pure_mem_schA (Φ' P') φ' s'
      (((hco _ v').and m.triple.geo.hM'.std).mono fun v h => h.1.trans h.2))
    rw [eΦ φ s (hco _ v), ← e] at d1
    rw [eΦ' φ' s' (hco _ v'), ← e'] at d2
    have h1 := _root_.GlobalTheory.StageGeo.geometric_stage_constant_on_pure_tensors hP hK D ψ θ A A' WW FA FA' FW _ _ _ _ _ _ _ _ _ Bs Γ Xc om om' cA cB hθ hT hO hX.meas' (hX.weil' t)
      hmm.mapB.stabM.1 R Rf c m k _ mf _ mP' φ φ' s s' v v' ef l _ _ d1 d2 (fun h => by
        simp only [hk']
        exact hint t h)
    have h2 : X.I ψ θ t P = c • X.I' ψ θ t P' := by
      funext h
      have h3 := congrFun h1 h
      simp only [thetaInt, _root_.Pi.smul_apply, hk, hk'] at h3
      exact h3
    refine hJ t ?_
    rw [map_smul, map_smul, ← hI, ← hI' t P' (hint t), h2]
  have q₁ := key _ _ _ _ _ _ r₁ m₁ k₁
  have q₂ := key _ _ _ _ _ _ r₂ m₂ k₂
  refine smul_left_injective ℂ hP' ?_
  show (c₁ * lam t₂) • p' P' = (c₂ * lam t₁) • p' P'
  rw [mul_comm c₁, mul_comm c₂, mul_smul, mul_smul, ← q₁, ← q₂, smul_comm]
end GlobalTheory.StageGeo
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaBottomFinitePlaceMatching
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotFinMatch
theorem theta_bottom_finite_match : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  intro hH hP hK hL
  refine gBig_two (_root_.GlobalTheory.T.theta_bottomLevel_matches_finiteData hH hP hK hL) (_root_.GlobalTheory.T.theta_bottomLevel_uniqueness hH hP hK hL) fun {D T Lc sc} G μ₀ C x b hA hB => ?_
  intro W i j A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, hA'⟩ := hA W i j A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have k1 : ∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p₀ (fockF W.ψ W.θ true FA FW f P) = (e.trans E.symm) (q P ⊗ₜ (c⁻¹ • r) f) := by
    intro f hf P
    have hmem : fockF W.ψ W.θ true FA FW f P ∈ algF W.ψ W.θ true FA FW := Submodule.subset_span ⟨f, P, hf, rfl⟩
    have h1 := hE _ hmem
    rw [hp f hf P] at h1
    rw [LinearEquiv.trans_apply, LinearMap.smul_apply, TensorProduct.tmul_smul, LinearEquiv.map_smul, h1,
      LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have k2 : ∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p₀' (fockF W.ψ W.θ false FA' FW f P) = (e.trans E.symm) (q' P ⊗ₜ r' f) := by
    intro f hf P
    have hmem : fockF W.ψ W.θ false FA' FW f P ∈ algF W.ψ W.θ false FA' FW := Submodule.subset_span ⟨f, P, hf, rfl⟩
    have h1 := hE' _ hmem
    rw [hp' f hf P] at h1
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
  obtain ⟨κ, hκ⟩ := hA' Pr Pf q q' (c⁻¹ • r) r' (e.trans E.symm) hq hq' k1 k2
  refine ⟨c * κ, ?_⟩
  rw [LinearMap.smul_apply] at hκ
  rw [mul_smul, ← hκ, smul_smul, mul_inv_cancel₀ hc, one_smul]
end GlobalTheory.BotFinMatch
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bottom_finite_place_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  first | exact @_root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match | exact _root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match | (intros; apply _root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftExtensionFieldExists
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
namespace GlobalTheory.RowEx
theorem exists_extension_field_of_join : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ExField :=
  fun hw hm P hJ ht K WC LM TA FS =>
    exField_of_keyFin_exKey keyFin_holds
      (exKey_of (_root_.GlobalTheory.RowEx.twisted_grid_existence_of_identity P)
        (isEx_of_separates FS (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)) (_root_.GlobalTheory.RowEx.twisted_base_existence P (_root_.GlobalTheory.RowEx.twisted_constant_existence hw hm P K WC LM TA)))
        (nfAll_of GlobalTheory.RowEx.nfChars nfRoot (GlobalTheory.RowEx.nfPhase_of_sumOKK (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P))
          (GlobalTheory.NFJetProof.nfJet_holds (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P) GlobalTheory.NormSum.inp_all (_root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large P GlobalTheory.NormSum.inp_all))
          (_root_.GlobalTheory.RowEx.RatioField.twistRatio_mem_numberField P
            (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport
              hJ.2.2.1)
            GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          (_root_.GlobalTheory.RowEx.bottomField_isNumberField P GlobalTheory.NormSum.inp_all))
        CarryGrid.carryG (GlobalTheory.RowEx.carryW_of_weil P.weilRepresentationUnitaryPair) GlobalTheory.RowEx.carryS trEasy
        (PhaseCarry.trPhase_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) (Jet.trJet_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) GlobalTheory.RowEx.trBot_holds)
end GlobalTheory.RowEx
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_extension_field_exists : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ExField := by
  first | exact @_root_.GlobalTheory.RowEx.exists_extension_field_of_join | exact _root_.GlobalTheory.RowEx.exists_extension_field_of_join | (intros; apply _root_.GlobalTheory.RowEx.exists_extension_field_of_join <;> assumption)
end
end

