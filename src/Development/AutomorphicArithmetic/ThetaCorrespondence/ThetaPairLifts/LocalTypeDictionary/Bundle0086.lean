import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingIntegralIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0034
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStatementOfSmall
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsCombinationMemRegularSubspace
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RegSo
theorem regular_subspace_vacuum_at : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (P : GL (Fin a') (Fv F v)) (Λ : Submodule 𝒪[Fv F v] (Fin (a + a') → Fv F v)) (c : ℂ),
      G.M'.IsLinBar B.ψ t 1 1 ι ∧
      ∀ Y, ι (G.M'.vac v) Y = c * (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t
  haveI := hT.geo.hV'.lat
  haveI := hT.geo.hW.lat
  obtain ⟨b', hb'⟩ := exists_isSplitBasis t G.V'.L hT.base.cm
  obtain ⟨c, hc⟩ := exists_isSplitBasis t G.W.L hT.base.cm
  obtain ⟨b₁, -, ι', hι', hvac'⟩ :=
    _root_.GlobalTheory.T.splitPlace_sphericalVector_indicator_value hP F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.ThKConst.isPair_small hT) v t b' c hb' hc
  let Q : GL (Fin a') (Fv F v) := Matrix.GeneralLinearGroup.mkOfDetNeZero b₁.valᵀ (by
    rw [Matrix.det_transpose]; exact b₁.isUnit.map Matrix.detMonoidHom |>.ne_zero)
  let Λ : Submodule 𝒪[Fv F v] (Fin (a + a') → Fv F v) :=
    { carrier := {x | ∀ j, (x ᵥ* c.val) j ∈ 𝒪[Fv F v]}
      add_mem' := fun {x y} hx hy j => by rw [Matrix.add_vecMul]; exact add_mem (hx j) (hy j)
      zero_mem' := fun j => by rw [Matrix.zero_vecMul]; exact zero_mem _
      smul_mem' := fun s x hx j => by
        rw [show s • x = (s : Fv F v) • x from rfl, Matrix.smul_vecMul]
        exact mul_mem s.2 (hx j) }
  refine ⟨_, Q, Λ, 1, isLinBar_one G.M' B.ψ t b₁ Q rfl c ι' hι', fun Y => ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
  rw [hvac', one_mul]
  have key : mulHomeo Q c Y ∈ {Y : Matrix (Fin a') (Fin (a + a')) (Fv F v) | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} ↔
      Q.val * Y ∈ (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F v))) := by
    rw [mulHomeo_apply]
    show (∀ i j, (Q.val * Y * c.val) i j ∈ v.adicCompletionIntegers F) ↔ ∀ i j, ((Q.val * Y).row i ᵥ* c.val) j ∈ 𝒪[Fv F v]
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    rfl
  by_cases h : Q.val * Y ∈ (GlobalTheory.SplitFlip.matLat (Fin a') Λ : Set (Matrix (Fin a') (Fin (a + a')) (Fv F v)))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key.2 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (key.1 h'))]
theorem exists_combination_mem_regular_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
      (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, Xc.Good v → ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁ ∧ k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) ∧
        GlobalTheory.FunObj.zdeg z ≠ 0 ∧ ∀ i, ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
          Φ₀D ∈ Γ.M'.So Bs.ψ t := by
  intro hP D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD n Ψ hΨ
  classical
  choose ΦD hΦD hD using fun i => hO.algB (Ψ i) (hΨ i)
  choose m f φ hsum hSB hvac using fun i => decAlg Γ.M' Bs.ψ Bs.emb (ΦD i) (hΦD i)
  have hfin : Set.Finite (⋃ i, ⋃ k, {v | ¬ φ i k v = Γ.M'.vac v}) :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (hvac i k)
  refine ⟨hfin.toFinset, fun v hv hg t => ?_⟩
  have h0 : ∀ i k, φ i k v = Γ.M'.vac v := fun i k => by
    by_contra h
    exact hv (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, h⟩⟩))
  have hTD' := isTriple_goodPlace hTD v t hg
  obtain ⟨K, hK⟩ := homAt W₁ Γ hO.JW₁ hTD.base.cm hTD.geo.hV'.herm v t
  let K' : GL (Fin W₁.rank) (Fv D.host.F v) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (K g)
      map_one' := by simp only [map_one]; exact GlobalTheory.LocWeilAct.conjU_one' _ _ _
      map_mul' := fun g g' => by simp only [map_mul]; exact GlobalTheory.LocWeilAct.conjU_mul' _ _ _ _ _ }
  obtain ⟨ν', α', hν', hact⟩ := actAt { Bs with v₁ := v, τ₁ := t } Γ Xc om om' hTD' K' (fun g => (hK g).2.2)
  obtain ⟨ι, Pm, Λ, c, hι, hvι⟩ := _root_.GlobalTheory.RegSo.regular_subspace_vacuum_at hP _ _ D.sp.cm.sig { Bs with v₁ := v, τ₁ := t } _ _ Γ Xc om om' hTD' v t
  obtain ⟨z, hzs, hzd, hz⟩ := combAt { Bs with v₁ := v, τ₁ := t } Γ hTD.geo.hM' hTD.geo.lt om'
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁) K ν' α' hν' ι hι (hact ι hι) (Γ.M'.vac v) Pm Λ c hvι
  refine ⟨z, fun k hk => ?_, hzd, fun i => ⟨(z.sum fun k c => c • om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ k, 1) (ΦD i)),
    datumComb D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hTD (ΦD i) (Ψ i) (hD i) z, ?_⟩⟩
  · obtain ⟨g, rfl⟩ := hzs k hk
    exact ⟨(hK g).1, (hK g).2.1⟩
  · rw [hsum i]
    exact hz (f i) (φ i) (hSB i) (hvac i) (h0 i)
end GlobalTheory.RegSo
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_form_mem_regular_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
      (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, Xc.Good v → ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁ ∧ k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) ∧
        GlobalTheory.FunObj.zdeg z ≠ 0 ∧ ∀ i, ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
          Φ₀D ∈ Γ.M'.So Bs.ψ t := by
  first | exact @_root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace | exact _root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace | (intros; apply _root_.GlobalTheory.RegSo.exists_combination_mem_regular_subspace <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsGoodGeometryOverCarriedFrames
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.exists_good_geometry_over_carried_frames : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s := by
  intro _
  refine GlobalTheory.SqStepBig.gbig_two GlobalTheory.T.towerStage_seesawDictionary_framesSignatures GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b q1 _ W _ i j p q A A' WW X lam t Bs hX _ hB
  obtain ⟨FA, FA', FW, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨⟨hψ, -⟩, hBs, hemb, -, -, hκ⟩ := hB
  have hsz := GlobalTheory.StageDict.stage_sizes i j hp hq hrA hrA'
  obtain ⟨Γ, hp', hq', hg, hS⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X FA FA' FW hXi.rank Bs p q hBs hψ hemb hXi.rigA hXi.rigA' hXi.rigW
    hXi.meas hXi.meas' hnA hnA' hnW hsz.1 hsz.2.1 hsz.2.2.1 hκ
  refine ⟨FA, FA', FW, Γ, ⟨⟨rfl, hS.JA, hS.latA.1⟩, ⟨rfl, hS.JB, hS.latB.1⟩, ⟨hXi.rank.symm, hS.pairA.JW, hS.latA.2⟩⟩,
    hp', hq', hg, fun s _ => ?_⟩
  obtain ⟨-, -, f1, f2, k1, k2⟩ := hd s
  refine ⟨f1, f2, k1, k2, fun om om' hT => ?_⟩
  obtain ⟨cA, cB, hO, -⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D W.ψ W.θ hXi.isVac.2.inf T A A' WW X FA FA' FW hXi.rank Bs Γ hS
    (GlobalTheory.SqStep.chs G i j s) om om' hT (X.ω s) (X.ω' s) (hXi.weil s) (hXi.weil' s)
  exact ⟨_, cA, cB, hO⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GaloisAtPlaceOfAutomorphicAtPlace
section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameGal
section Poly
open Polynomial Formalism.L2.Col
variable {K : Type} [Field K]
end Poly
section Runs
open Formalism.BasicNotions Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.GalDef
end Runs
section Galois
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.ExpFrame GlobalTheory.TripleGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
variable [IsCMField E]
end Galois
section Side
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.ExpFrame GlobalTheory.TripleGal GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.GalDef
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.L2.Col Polynomial
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] [IsCMField E]
variable (Ω) in
theorem galois_side_of_compatible_systems (p1 : GlobalTheory.Published.ClozelCohomological) (p2 : GlobalTheory.Published.CohomologicalCsdTempered)
    (p3 : GlobalTheory.Published.HeckeLAdicCharacter) (p4 : GlobalTheory.Published.ChebotarevDegreeOne)
    (p6 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (p7 : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup)
    (p8 : GlobalTheory.Published.BhattScholzeCrystallineLattices) (p9 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (p10 : GlobalTheory.Published.LocalLanglandsGL)
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    (ι : Qbar l ≃+* ℂ) {T : Type} [DecidableEq T] {inc : T → (E →+* Qbar l)} (half : IsHalf inc) (s : T → ℤ)
    {P : Par} {W : Wts T} (hP : P.Hyp) (hL : P.Large) (hW : W.Ok P) (F : Frame l T P.Nr) (Bk : (F.I → Qbar l) → Prop)
    {Pl : Type} (pt : Pl → Fin P.Nr → F.I) (lab : Pl → HeightOneSpectrum (𝓞 E))
    (cofin : {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range lab}.Finite)
    (hlab : ∀ Q, IsSplitAt (lab Q) ∧ ((l : ℕ) : 𝓞 E) ∉ (lab Q).asIdeal)
    (haut : ∀ mu θ, (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → ∃ π, SystemOf ι inc s lab P.Nr mu (sysOf P.Nr pt θ) π)
    (hblk : ∀ θ, Bk θ → ∀ Q, ∃ ν : Qbar l, ‖ι ν‖ ^ 2 = (Ideal.absNorm (lab Q).asIdeal : ℝ) ^ (P.Nr - P.t) ∧
      blockPoly ν (Ideal.absNorm (lab Q).asIdeal) P.t ∣ heckePolyOf P.Nr (Ideal.absNorm (lab Q).asIdeal) (sysOf P.Nr pt θ Q)) :
    GalSide Ω inc P W F Bk := by
  have hN := hP.Nr_eq
  have ht := hP.t_ge
  have hm := hP.m_pos
  have hk := hP.m_le
  obtain ⟨c, hc, hc'⟩ := exists_of_half half (fun τ => (h0 P : ℤ) - P.Nr + 1 + s τ) fun τ => -s τ
  obtain ⟨tw, htw, hcr⟩ := exists_crys_char Ω p3 p9 ι c ((h0 P : ℤ) - P.Nr + 1) fun i => by
    obtain ⟨τ, rfl | rfl⟩ := half.2.2 i
    · rw [hc, hc']; ring
    · rw [cj_cj, hc, hc']; ring
  let Fn : FrobNorm E Ω l Pl := ⟨lab, -1, tw, htw, cofin⟩
  have main := _root_.GlobalTheory.GalAut.exists_galoisRep_of_definiteUnitary p7 p6 p1 p2 p3 p9 p4 p8 p10 E Ω hE P.Nr (by omega)
  refine ⟨Pl, pt, Fn, cj, Or.inr rfl, fun mu θ ha hθ => ?_, fun θ hθ hB => ?_⟩
  · obtain ⟨π, hπ⟩ := haut mu θ ha hθ
    obtain ⟨lam, hl, hl1, hl2, -⟩ := hπ.weights half
    obtain ⟨⟨r, hr, hf⟩, -⟩ := main π hπ.1 lam hl l ι hπ.2.2.1
    refine ⟨GlobalTheory.TwistAbove.twGL tw r,
      fun τ a => ((Fin.rev a : ℕ) : ℤ) - (lam (ι.toRingHom.comp τ)).w (Fin.rev a) + c τ, fun τ a => ⟨?_, ?_⟩, ?_,
      SystemOf.reads Fn hlab hπ hf fun g => charpoly_smul _ (Units.ne_zero _)⟩
    · have := a.2
      simp only [hl2, hc', DomWeight.dual, Fin.rev_rev, hl1, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      rw [Fin.val_rev]
      omega
    · have := a.2
      simp only [cj_cj, hc, hl1, Formalism.CohomologicalDescent.UnitNormBounds.UN, Fin.val_rev]
      omega
    · convert crysWith_twist (r' := GlobalTheory.TwistAbove.twGL tw r) (fun _ => rfl) hr htw hcr using 2 with τ
      rw [jumpsOf, Multiset.map_map]
      conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
      rfl
  · have ha : ∀ τ, Antitone (res P.Nr (W.lam τ)) := fun τ a b h => hW.anti τ a b h b.2
    obtain ⟨π, hπ⟩ := haut W.lam θ ha hθ
    obtain ⟨lam, hl, hl1, hl2, hl3⟩ := hπ.weights half
    have r1 := fun τ => isRunAt_block hP hL hW τ _ _ (hl1 τ)
    have r2 := fun τ => isRunAt_dual (by omega) (r1 τ).1
    obtain ⟨-, v, hv, hd, -⟩ := (p4.dense (Ω := Ω) cofin).nonempty
    obtain ⟨Q, -⟩ : v ∈ Set.range lab := by
      by_contra h
      exact hv ⟨((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd, h⟩
    have hstr : HasString l π P.t := by
      obtain ⟨hu, σ, S, h1, h2, h3⟩ := hπ.2.2.2 Q
      obtain ⟨ν, hν, hdv⟩ := hblk θ hB Q
      obtain ⟨u, hu1, hu2⟩ := string_of_dvd ι (absNorm_ne_zero _) (by omega) S (card_of_hasSat h2) _ h3 ν hν hdv
      exact ⟨lab Q, (hlab Q).1, (hlab Q).2, hu, σ, S, u, h1, h2, hu1, hu2⟩
    obtain ⟨a, ρ, χ, bot, h1, h2, h3, h4, h5⟩ := (main π hπ.1 lam hl l ι hπ.2.2.1).2 P.t (by omega) (fun φ => by
      obtain ⟨τ, rfl | rfl⟩ := hl3 φ
      · exact ⟨_, (r1 τ).1⟩
      · exact ⟨_, hl2 τ ▸ (r2 τ).1⟩) hstr
    refine ⟨a, GlobalTheory.TwistAbove.twGL tw ρ, fun j => χ j * tw, fun τ => bot τ + c τ, h1,
      continuous_twist (fun _ => rfl) h2 htw, fun j => ?_, fun τ => ⟨?_, ?_⟩, SystemOf.reads Fn hlab hπ h5 fun g => ?_⟩
    · convert crysWith_twist (r' := rk1 (χ j * tw)) (fun g => ?_) (h3 j) htw hcr using 2 with τ
      · rw [Multiset.map_singleton, add_right_comm]
      · ext x y
        simp [rk1, Matrix.diagonal_apply, mul_comm]
    · have := hW.what₂ τ
      beta_reduce
      rw [h4 _ _ (hl2 τ ▸ (r2 τ).1), hl2, (r2 τ).2, (r1 τ).2, hc']
      omega
    · beta_reduce
      rw [cj_cj, h4 _ _ (r1 τ).1, (r1 τ).2, hc]
      omega
    · have e := scaleRoots_prod (Finset.univ.val.map fun j => ((χ j g : (Qbar l)ˣ) : Qbar l)) ((tw g : (Qbar l)ˣ) : Qbar l)
      rw [Multiset.map_map, Multiset.map_map] at e
      rw [mul_scaleRoots_of_noZeroDivisors, ← charpoly_smul _ (Units.ne_zero _)]
      exact congrArg₂ (· * ·) rfl e.symm
end Side
section Point
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame GlobalTheory.FrameAut
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.L2.Col
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
set_option maxHeartbeats 1600000 in
theorem galois_at_place_of_automorphic_at_place (p1 : GlobalTheory.Published.ClozelCohomological) (p2 : GlobalTheory.Published.CohomologicalCsdTempered)
    (p3 : GlobalTheory.Published.HeckeLAdicCharacter) (p4 : GlobalTheory.Published.ChebotarevDegreeOne)
    (p6 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (p7 : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup)
    (p8 : GlobalTheory.Published.BhattScholzeCrystallineLattices) (p9 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (p10 : GlobalTheory.Published.LocalLanglandsGL)
    {j : Fin D.R.m} {P : Par} {W : Wts D.what₂.Tau} (hD : Dict L j P W) (hN : NumOk P W) {w : HeightOneSpectrum (𝓞 D.what₂.LL)}
    (h : AutAt p j P W w) : GalAt p j P W w := by
  classical
  intro _ F R inc _ T
  obtain ⟨⟨hpl, hcof, hbl⟩, haut⟩ := h
  obtain ⟨hn, ht, ν, hν⟩ := blk_numbers p hD hN.1 (p.R.mu w)
  let Pl := {Q : (blk p j (p.R.mu w)).Pl // ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal}
  have hpt : ∀ (Q : Pl) (k : Fin P.Nr), ∃ i, R.ix i = (Q.1, (k : ℕ) + 1) := fun Q k =>
    (T.ix_range (Q.1, (k : ℕ) + 1)).2 ⟨Nat.le_add_left _ _, k.2, Q.2⟩
  choose pt hpt using hpt
  refine _root_.GlobalTheory.FrameGal.galois_side_of_compatible_systems _ p1 p2 p3 p4 p6 p7 p8 p9 p10 (GlobalTheory.DefiniteBC.host_unramified D.host) T.io T.half T.sh hN.1 hN.2.1
    hN.2.2.1 F _ pt (fun Q => labOf p j (p.R.mu w) Q.1) (hcof.subset fun v hv => ⟨hv.1, fun ⟨Q, h1, h2⟩ => hv.2 ⟨⟨Q, h1⟩, h2⟩⟩)
    (fun Q => ⟨(hpl Q.1).1, fun h => Q.2 ((hpl Q.1).2.2.2.1 h)⟩) (fun mu θ ha hθ => ?_) fun θ hθ Q => ?_
  · obtain ⟨π, h1, h2, h3, h4⟩ := haut F R inc T mu θ ha hθ
    refine ⟨π, h1, h2, h3, fun Q => ?_⟩
    obtain ⟨hu, σ, S, a, b, c⟩ := h4 Q.1
    refine ⟨hu, σ, S, a, b, fun k hk => ?_⟩
    rcases k with _ | k
    · rw [sysOf_zero, map_one, GlobalTheory.LFun.satEig]
      simp [Multiset.esymm]
    · have e := c (pt Q ⟨k, hk⟩) (by rw [hpt])
      rw [hpt] at e
      exact (congrArg T.io (sysOf_succ P.Nr pt θ Q ⟨k, hk⟩)).trans e
  · refine ⟨R.e0 (ν Q.1), ?_, ?_⟩
    · rw [T.liftFrame_embedding_base, hbl ν hν, (hpl Q.1).2.2.1, hn, ht]
    · rw [(hpl Q.1).2.2.1, ← ht]
      exact block_dvd hθ hn pt Q Q.1 (hpt Q) hν
end Point
end GlobalTheory.FrameGal
open Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie in
theorem GlobalTheory.FrameGal.galois_steinberg_local : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter →
    GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal →
    _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove →
    GlobalTheory.Published.LocalLanglandsGL → SmallSt → GlobalTheory.ExpTie.GalSt := by
  intro p1 p2 p3 p4 p6 p7 p8 p9 p10 hS
  refine Closed.imp (GlobalTheory.T.small_estimate_implies_frame_automorphy hS) fun Fm _ _ H => ?_
  obtain ⟨a, ha⟩ := H
  exact ⟨a, fun x hx hle i p hp hm j P W hD hN w hw hR =>
    _root_.GlobalTheory.FrameGal.galois_at_place_of_automorphic_at_place p p1 p2 p3 p4 p6 p7 p8 p9 p10 hD hN (ha x hx hle i p hp hm j P W hD hN w hw hR)⟩
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_frame_compatibility : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.LocalLanglandsGL → SmallSt → GlobalTheory.ExpTie.GalSt := by
  first | exact @_root_.GlobalTheory.FrameGal.galois_steinberg_local | exact _root_.GlobalTheory.FrameGal.galois_steinberg_local | (intros; apply _root_.GlobalTheory.FrameGal.galois_steinberg_local <;> assumption)
end
end

