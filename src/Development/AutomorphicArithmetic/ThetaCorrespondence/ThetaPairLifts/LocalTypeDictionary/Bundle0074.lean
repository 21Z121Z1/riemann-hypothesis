import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseMain
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvReBaseReal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0038
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0073
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.ReBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0813
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0071
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0814
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0072
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0068
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0006

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvReBaseMain
section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ReBase
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')}
variable {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem rebase_finite_scalar (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {R R₂ : RealMaps F a a'} {Rf S : FinMaps F a a'}
    (hM : IsMatched B G X om om' R Rf) (hM₂ : IsMatched B (reG G V V' Z) X om om' R₂ S) :
    ∃ (ψ : ∀ v, Rf.Pi v ≃ₗ[ℂ] S.Pi v) (l : Pl F → ℂ), (∀ v ∉ X.T, l v = 1) ∧
      (∀ v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), S.p v φ = ψ v (Rf.p v φ)) ∧
      (∀ v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S.p' v φ = l v • ψ v (Rf.p' v φ)) ∧
      ∏ v ∈ X.T, l v = X.ν (kapId B G V V' Z) := by
  choose ψ l hl h3 h4 h5 using _root_.UpperTheory.Lit.HoweDuality.exists_local_iso_scalar_of_reG hP F E σ B a a' G X om om' R Rf hM V V' Z S hM₂.fin
  refine ⟨ψ, l, h5, h3, h4, ?_⟩
  have hc := hM.triple.chars
  have key : ∀ v : B.P, l v.1 = (chrW X.ν (B.τ v) (kap G V V' Z v.1) : ℂ) := by
    intro v
    by_cases hv : v.1 ∈ X.T
    · haveI := hM.fin.nontriv v.1
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v.1)
      obtain ⟨φ, hφ, e⟩ : y ∈ (SB _).map (Rf.p v.1) := by rw [hM.fin.onto]; trivial
      obtain ⟨φ', hφ', e'⟩ : y ∈ (SB _).map (Rf.p' v.1) := by rw [hM.fin.onto']; trivial
      have h := zeta_rel hM.triple.base hM.triple.geo hM₂.triple.geo (hM.fin.zeta v hv) (hM₂.fin.zeta v hv) hφ hφ'
        (e.trans e'.symm)
      rw [map_smul, h3 _ _ hφ, h4 _ _ hφ', e, e'] at h
      exact (smul_left_injective ℂ ((LinearEquiv.map_ne_zero_iff (ψ v.1)).2 hy) h).symm
    · have hw : splitPrime (B.τ v) ∉ above E (X.T : Set (Pl F)) := fun h => hv (by
        have h' : (splitPrime (B.τ v)).under (𝓞 F) ∈ (X.T : Set (Pl F)) := h
        rwa [splitPrime_under] at h')
      have hk := valuation_kap hM.triple.geo hM₂.triple.geo v
      have h1 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hc.heckeα v.1 (B.τ v)).2.2.2 (hc.unrα _ hw) _ hk
      have h2 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hc.heckeβ v.1 (B.τ v)).2.2.2 (hc.unrβ _ hw) _ hk
      have h0 : chrW X.ν (B.τ v) (kap G V V' Z v.1) =
          chrW X.α (B.τ v) (kap G V V' Z v.1) / chrW X.β (B.τ v) (kap G V V' Z v.1) := by
        simp only [Chars.ν, chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div]
      rw [h5 _ hv, h0, h1, h2, div_one, Units.val_one]
  rw [chr_kapId, Finset.prod_subset hc.sub (fun v _ hv => h5 v hv), ← Finset.prod_coe_sort B.P l]
  exact Finset.prod_congr rfl fun v _ => key v
theorem rebase_constants_agree (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) {R R₂ : RealMaps F a a'} {Rf S : FinMaps F a a'}
    (hM : IsMatched B G X om om' R Rf) (hM₂ : IsMatched B (reG G V V' Z) X om om' R₂ S)
    {g : UA σ G.V.J} (hg : g ∈ UAt σ G.V (evI F)) {g' : UA σ G.V'.J} (hg' : g' ∈ UAt σ G.V' (evI F))
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F))
    (hθ : ∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w)))
    (hθ' : ∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = Z.θ w * (mat h).map (piInf (B.emb w)))
    {T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}
    {T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))} (hTc : Continuous T) (hTc' : Continuous T')
    (hT1 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hT1' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g', h)) f (T' f))
    (hT2' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g'⁻¹, h⁻¹)) f (T'.symm f))
    {ψ₀ : R.Pi ≃ₗ[ℂ] (reR R₂ T T').Pi} {l₀ : ℂ} (hl₀ : l₀ ≠ 0)
    (hR : ∀ f ∈ G.M.Pol B.ψ B.emb, (reR R₂ T T').p f = ψ₀ (R.p f))
    (hR' : ∀ f ∈ G.M'.Pol B.ψ B.emb, (reR R₂ T T').p' f = l₀ • ψ₀ (R.p' f))
    {c d : ℂ} (hc : IsConst B G X om om' R Rf c) (hd : IsConst B (reG G V V' Z) X om om' R₂ S d) :
    d = l₀ * X.ν (kapId B G V V' Z) * c := by
  obtain ⟨ψ, l, hl1, h3, h4, hl⟩ := _root_.GlobalTheory.ReBase.rebase_finite_scalar hP hM hM₂
  obtain ⟨⟨-, hu, -⟩, -, hso⟩ := (hK.1 F E σ B a a' G X om om' hM.triple).2 R Rf hM
  have hT := hM.triple
  set Λ : ℂ := l₀ * X.ν (kapId B G V V' Z) with hΛ
  have hΛ0 : Λ ≠ 0 := mul_ne_zero hl₀ (Circle.coe_ne_zero _)
  have pm : ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' →
      PolMatch B (reG G V V' Z) X R₂ S (om (g, h) (Λ • Φ)) (om' (g', h) Φ') := fun Φ Φ' hm => by
    have := polMatch_iso hl1 hR hR' h3 h4 hm
    rw [hl] at this
    exact polMatch_transport hT R₂ hg hg' hh hθ hθ' hθW hT1 hT2 hT1' hT2' S this
  have so : ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' (g', h) Φ' ∈ (reG G V V' Z).M'.So B.ψ B.τ₁ := fun Φ' hΦ' =>
    (GlobalTheory.ThKRealConj.so_reG' G V V' Z B.ψ B.τ₁).symm ▸ hso (g', h) Φ' hΦ'
  have hc' : IsConst B G X om om' R Rf (d / Λ) := by
    rintro Φ Φ' ⟨hSo, m, m', r, f, s, r', f', s', hr, hr', hΦ, hΦ', hk⟩ y
    have e1 : ∀ u : Fin m → SInf F (Fin a × Fin (a + a')),
        om (g, h) (Λ • ∑ i, pureA F (u i) (r i)) = ∑ i, pureA F (⇑(Λ • T (u i))) (r i) := fun u => by
      rw [map_smul, map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [acts_pureA (hT1 (u i)) (hr i).1, pureA_smul]
    have e2 : ∀ u : Fin m' → SInf F (Fin a' × Fin (a + a')),
        om' (g', h) (∑ i, pureA F (u i) (r' i)) = ∑ i, pureA F (T' (u i)) (r' i) := fun u => by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => acts_pureA (hT1' (u i)) (hr' i).1
    have hm : Match B (reG G V V' Z) X R₂ S (om (g, h) (Λ • Φ)) (om' (g', h) Φ') := by
      refine ⟨so _ hSo, m, m', r, fun i => Λ • T (f i), fun k i => Λ • T (s k i), r', fun i => T' (f' i),
        fun k i => T' (s' k i), fun i => ⟨(hr i).1, ((hTc.tendsto _).comp (hr i).2).const_smul Λ⟩,
        fun i => ⟨(hr' i).1, (hTc'.tendsto _).comp (hr' i).2⟩, by rw [hΦ, e1], by rw [hΦ', e2], fun k => ?_⟩
      have h1 := so _ (hk k).1
      have h2 := pm _ _ (hk k).2
      rw [e2] at h1
      rw [e1, e2] at h2
      exact ⟨h1, h2⟩
    have sΦ : Λ • Φ ∈ schA F (Fin a × Fin (a + a')) := by
      rw [hΦ]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, r i, (hr i).1, rfl⟩)
    have sΦ' : Φ' ∈ schA F (Fin a' × Fin (a + a')) := by
      rw [hΦ']
      exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, r' i, (hr' i).1, rfl⟩
    have key := hd _ _ hm (y * h⁻¹)
    have i1 := _root_.GlobalTheory.T.thetaIntegral_comp_rightTranslate hP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V hT) g hg h _ sΦ
      (y * h⁻¹)
    have i2 := _root_.GlobalTheory.T.thetaIntegral_comp_rightTranslate hP F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V' hT) g' hg' h _
      sΦ' (y * h⁻¹)
    rw [inv_mul_cancel_right] at i1 i2
    change G.M.I om (om (g, h) (Λ • Φ)) (y * h⁻¹) = d * G.M'.I om' (om' (g', h) Φ') (y * h⁻¹) at key
    rw [i1, i2, GlobalTheory.PolIso.modelI_smul] at key
    rw [div_mul_eq_mul_div, eq_div_iff hΛ0, ← key, mul_comm]
  rw [hu.unique hc hc']
  field_simp
theorem rebase_ratio_real_part (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) {Xa Xb : Chars F E} {R R₂ : RealMaps F a a'}
    {oa ob : Rep σ G.V G.W} {oa' ob' : Rep σ G.V' G.W} {Ra Rb Sa Sb : FinMaps F a a'} {ca cb da db : ℂ}
    (m1 : IsMatched B G Xa oa oa' R Ra) (m2 : IsMatched B G Xb ob ob' R Rb)
    (n1 : IsMatched B (reG G V V' Z) Xa oa oa' R₂ Sa) (n2 : IsMatched B (reG G V V' Z) Xb ob ob' R₂ Sb)
    (k1 : IsConst B G Xa oa oa' R Ra ca) (k2 : IsConst B G Xb ob ob' R Rb cb)
    (l1 : IsConst B (reG G V V' Z) Xa oa oa' R₂ Sa da) (l2 : IsConst B (reG G V V' Z) Xb ob ob' R₂ Sb db) :
    ∃ k : (AE F E)ˣ, da * cb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * ca) := by
  have ta := m1.triple
  have tb := m2.triple
  have hB := ta.base
  obtain ⟨g, hg, eg⟩ := GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary F E σ B a _ _ G.V V hB ta.geo.hV n1.triple.geo.hV
  obtain ⟨g', hg', eg'⟩ := GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary F E σ B a' _ _ G.V' V' hB ta.geo.hV' n1.triple.geo.hV'
  obtain ⟨h, hh, eh⟩ := GlobalTheory.T.skewHermitian_cartanInvolutionSystems_conjugate_archimedean F E σ B (a + a') _ _ G.W Z hB ta.geo.hW n1.triple.geo.hW
  obtain ⟨T, hTc, hT1, hT2⟩ := exists_op hB.std ta.weil hg hh
  obtain ⟨T', hTc', hT1', hT2'⟩ := exists_op hB.std ta.weil' hg' hh
  have hR₃ := _root_.GlobalTheory.ReBase.real_maps_transport hP ta R₂ hg hg' hh eg eg' eh hT1 hT2 hT1' hT2' n1.triple n1.real
  obtain ⟨ψ₀, l₀, hl₀, hR, hR'⟩ := _root_.GlobalTheory.ReBase.real_maps_unique hP F E σ B a a' G Xa oa oa' R Ra m1 _ hR₃
  have eα : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → Xa.α z = Xb.α z := fun z hz =>
    Circle.ext ((ta.chars.expα z hz).trans (tb.chars.expα z hz).symm)
  have eβ : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → Xa.β z = Xb.β z := fun z hz =>
    Circle.ext ((ta.chars.expβ z hz).trans (tb.chars.expβ z hz).symm)
  have eV := fun g hg h hh => weil_arch_eq (g := g) (k := h) hB.cm hB.std ta.geo.hV.herm
    (GlobalTheory.FinUniq.det_ne_zero_herm ta.geo.hV) ta.geo.hW.skew (GlobalTheory.FinUniq.det_ne_zero_skew ta.geo.hW) eβ
    (fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, eα z hz, eβ z hz]) ta.weil tb.weil hg hh
  have eV' := fun g hg h hh => weil_arch_eq (g := g) (k := h) hB.cm hB.std ta.geo.hV'.herm
    (GlobalTheory.FinUniq.det_ne_zero_herm ta.geo.hV') ta.geo.hW.skew (GlobalTheory.FinUniq.det_ne_zero_skew ta.geo.hW) eα
    (fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, eα z hz, eβ z hz]) ta.weil' tb.weil' hg hh
  have hhi := GlobalTheory.MajTransport.uat_inv hh
  have ha := _root_.GlobalTheory.ReBase.rebase_constants_agree hP hK m1 n1 hg hg' hh eg eg' eh hTc hTc' hT1 hT2 hT1' hT2' hl₀ hR hR' k1 l1
  have hb := _root_.GlobalTheory.ReBase.rebase_constants_agree hP hK m2 n2 hg hg' hh eg eg' eh hTc hTc' (fun f => acts_congr (eV g hg h hh) (hT1 f))
    (fun f => acts_congr (eV _ (GlobalTheory.MajTransport.uat_inv hg) _ hhi) (hT2 f))
    (fun f => acts_congr (eV' g' hg' h hh) (hT1' f))
    (fun f => acts_congr (eV' _ (GlobalTheory.MajTransport.uat_inv hg') _ hhi) (hT2' f)) hl₀ hR hR' k2 l2
  refine ⟨kapId B G V V' Z, ?_⟩
  have h0 : (Xb.ν (kapId B G V V' Z) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [ha, hb, Circle.coe_div]
  field_simp
end GlobalTheory.ReBase
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteAdeleActsPlacewise
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
namespace GlobalTheory.LocActV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.WeilM
theorem finite_adele_acts_placewise : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
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
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.lattice_stabilizer_fixes_vacuum_vector hPr F E σ B a a' G X om om' hT
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
theorem _root_.GlobalTheory.T.local_action_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
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
  first | exact @_root_.GlobalTheory.LocActV.finite_adele_acts_placewise | exact _root_.GlobalTheory.LocActV.finite_adele_acts_placewise | (intros; apply _root_.GlobalTheory.LocActV.finite_adele_acts_placewise <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerProjectionMaximalThetaSubspace
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree.KerPMax
theorem ker_projection_maximal_thetaSubspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
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
    exact ⟨_, _root_.GlobalTheory.T.adelic_stabilizer_finite_of_theta_subgroup hP D X W.rank W₁.rank e Bs Γ Xc om om' hT' hO.JX N' hN' g hg ΦD hΦD, _, hW,
      hm.mapB.eqf g hg Φ₀ hΦ₀⟩
  have hS2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ S, rl τ Y x ∈ S := by
    rintro τ Y hY _ ⟨ΦD, hΦD, Φ₀, hD, rfl⟩
    obtain ⟨ΨD, hΨD, Φ₁, hΦ₁, hE, hder⟩ := _root_.GlobalTheory.T.adelic_stabilizer_lie_ker_polarization hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB
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

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_projection_isMax : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
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
  first | exact @_root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace | exact _root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace | (intros; apply _root_.GlobalTheory.SquareAgree.KerPMax.ker_projection_maximal_thetaSubspace <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedIterateEventuallyLarge
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
variable {D : D7}
section Lin
variable {ψ : AddChar (AF D.host.F) ℂ} {T₀ : HSp D}
end Lin
variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
variable (W : G.Weil) (M : Vol G) (t : T)
variable {W M t}
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun
end GlobalTheory.RowChain
namespace GlobalTheory.RowChain
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun GlobalTheory.RowUnf GlobalTheory.RowVal
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)
theorem twisted_iterate_eventually_large : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch := by
  intro hP hL
  obtain ⟨c0, h0⟩ := (_root_.GlobalTheory.T.flipRun_cusp_transition hL hP).and ((_root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList hP).and GlobalTheory.RowClaim.colFn_cont_left)
  refine ⟨c0, fun ε CF hC => ?_⟩
  obtain ⟨x0, hx⟩ := h0 ε CF hC
  refine ⟨x0, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R Fc hS ch hch hsc => ?_⟩
  obtain ⟨hstep, htop, hcol⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R Fc hS ch hch hsc
  choose ρ hρ hρ' using exists_rowMeas ch.G
  choose v hv using exists_vol_row ch.G
  refine ⟨ρ, fun j => (v j).μ, fun j hj => ⟨hρ j (mem_idx hj).2, (v j).haar⟩, ?_⟩
  intro t a τ hτ M hM P y
  obtain ⟨e, he, φm, hw, -⟩ := hτ
  have hu : GlobalTheory.Unf.IsContAut _ (colFn ch a) := ⟨(hcol a).2, (hcol a).1⟩
  have core : ∀ d ∈ τ.support,
      BplusConv ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) ∧
      NIter ρ (fun j => (v j).μ) (fun h => per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h) d.1 P.1 (colFn ch a) (formTop ch t y))
        (idx D) 1 (Bplus ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y))) := by
    intro d hd
    have h2 := hw d hd
    obtain ⟨-, h1, h3⟩ := pure_core hP.cuspRapidDecay hch.vol hM (hstep t M hM) he (φm d) d h2.1 h2.2 P (htop t y) hu
    refine ⟨GlobalTheory.RowBplus.bplusConv_col ch.W ch.M hch.vol ch.ξ (ch.col a) (col_mem ch a) _ h1.1.toIsAutFun, ?_⟩
    exact nIter_meas_congr ρ _ _ _ (fun j hj => hv j (mem_idx hj).1 (mem_idx hj).2.le t M hM)
      (nIter_conAt_of_colPer ch.G ch.W t hM (fockD ch.W t d.2 P.2) _ _ _ h3 ρ (fun j => (hρ' j t M hM).1)
        fun j => (hρ' j t M hM).2)
  have e1 : liftT ch.W M (oppPath t D.R.m) (oppTens ch.W t (Finsupp.single P 1) τ) (formTop ch t y) =
      ∑ d ∈ τ.support, τ d • liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y) := by
    rw [GlobalTheory.RowVal.liftT_oppTens, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
      one_smul]
  have e2 : lhs ch t M (Finsupp.single P 1) τ a y = ∑ d ∈ τ.support,
      τ d * Bplus ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) := by
    rw [lhs, e1, (bplus_sum_right ch.W ch.M (colFn ch a) τ.support _
      fun d hd => (bplus_smul_right ch.W ch.M (τ d) (core d hd).1).1).2]
    exact Finset.sum_congr rfl fun d hd => (bplus_smul_right ch.W ch.M _ (core d hd).1).2
  rw [e2]
  exact (niter_lin_congr _ _ _ ρ _ (idx D) 1).1 _ τ.support τ _ _ fun d hd => (core d hd).2
theorem twisted_iterate_eq_linear : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch ∧ LinAt ch :=
  fun hP hL => (_root_.GlobalTheory.RowChain.twisted_iterate_eventually_large hP hL).and (_root_.GlobalTheory.RowVal.placeValuation_linAt_large hP hL)
end GlobalTheory.RowChain
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_iterate_chain : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch ∧ LinAt ch := by
  first | exact @_root_.GlobalTheory.RowChain.twisted_iterate_eq_linear | exact _root_.GlobalTheory.RowChain.twisted_iterate_eq_linear | (intros; apply _root_.GlobalTheory.RowChain.twisted_iterate_eq_linear <;> assumption)
end
end

