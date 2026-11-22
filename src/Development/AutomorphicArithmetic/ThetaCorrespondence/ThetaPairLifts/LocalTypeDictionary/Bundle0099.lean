import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangleStageFrameFactorisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0098
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaPairingExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3660
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0085
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0087
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0094
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0020
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0088

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BaseSplitPrimeInLocalPlaces
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
section Helpers
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StageGeo
private theorem common_factor_of_pair_relation {T K : Type} [Group K] {t u : T} (ν : T → K →* Circle) (lam : T → ℂ) (h0 : ∀ s, lam s ≠ 0)
    (good : T → ℂ → Prop)
    (H : ∀ s₁ s₂ c₁ c₂, (s₁ = t ∨ s₁ = u) → (s₂ = t ∨ s₂ = u) → good s₁ c₁ → good s₂ c₂ →
      ∃ k, (ν s₂ k : ℂ) * c₁ * lam s₂ = (ν s₁ k : ℂ) * c₂ * lam s₁) :
    ∃ (κ : ℂ) (k : K), ∀ s c, (s = t ∨ s = u) → good s c → c = κ * ((ν s k : ℂ) * lam s) := by
  have same : ∀ s c₁ c₂, (s = t ∨ s = u) → good s c₁ → good s c₂ → c₁ = c₂ := fun s c₁ c₂ hs g₁ g₂ => by
    obtain ⟨k, hk⟩ := H s s c₁ c₂ hs hs g₁ g₂
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (mul_right_cancel₀ (h0 s) hk)
  have nz : ∀ s k, (ν s k : ℂ) * lam s ≠ 0 := fun s k => mul_ne_zero (Circle.coe_ne_zero _) (h0 s)
  by_cases ht : ∃ c, good t c
  · obtain ⟨c₁, g₁⟩ := ht
    by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      obtain ⟨k, hk⟩ := H t u c₁ c₂ (.inl rfl) (.inr rfl) g₁ g₂
      refine ⟨c₁ / ((ν t k : ℂ) * lam t), k, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · rw [same _ _ _ (.inr rfl) g g₂, div_mul_eq_mul_div, eq_div_iff (nz _ _)]
        linear_combination -hk
    · refine ⟨c₁ / ((ν t 1 : ℂ) * lam t), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inl rfl) g g₁
      · exact absurd ⟨c, g⟩ hu
  · by_cases hu : ∃ c, good u c
    · obtain ⟨c₂, g₂⟩ := hu
      refine ⟨c₂ / ((ν u 1 : ℂ) * lam u), 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · rw [div_mul_cancel₀ _ (nz _ _)]
        exact same _ _ _ (.inr rfl) g g₂
    · refine ⟨0, 1, ?_⟩
      rintro s c (rfl | rfl) g
      · exact absurd ⟨c, g⟩ ht
      · exact absurd ⟨c, g⟩ hu
private theorem reSpace_eq_of_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {X Y : Spc F E n}
    (hJ : X.J = Y.J) (hL : X.L = Y.L) : reS X Y = Y := by
  cases X; cases Y; cases hJ; cases hL; rfl
theorem exists_pivot_pair {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) (hM : LocalMatching) {B : Base F E} {a a' : ℕ}
    {Γ : Geo σ a a'} {Xa Xb : Chars F E} {oa oa' ob ob'} (ha : IsTriple B Γ Xa oa oa') (hb : IsTriple B Γ Xb ob ob') :
    ∃ R Ra Rb ca cb, IsMatched B Γ Xa oa oa' R Ra ∧ IsMatched B Γ Xb ob ob' R Rb ∧ IsConst B Γ Xa oa oa' R Ra ca ∧
      IsConst B Γ Xb ob ob' R Rb cb ∧ cb ≠ 0 := by
  obtain ⟨R, Ra, h1⟩ := hM F E σ B a a' Γ Xa oa oa' ha
  obtain ⟨R', Rb, h2⟩ := hM F E σ B a a' Γ Xb ob ob' hb
  have h3 : IsMatched B Γ Xb ob ob' R Rb := ⟨hb, _root_.GlobalTheory.T.characters_real_valued_of_equal_exponent hP F E σ B a a' Γ Xa Xb oa oa' ob ob' R ha hb h1.real, h2.fin⟩
  obtain ⟨⟨-, ⟨ca, hca, -⟩, -⟩, -⟩ := (hK.1 F E σ B a a' Γ Xa oa oa' ha).2 R Ra h1
  obtain ⟨⟨-, ⟨cb, hcb, -⟩, h0⟩, -⟩ := (hK.1 F E σ B a a' Γ Xb ob ob' hb).2 R Rb h3
  exact ⟨R, Ra, Rb, ca, cb, h1, h3, hca, hcb, h0 cb hcb⟩
variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
private theorem readings_of_split_units {G : GridData Lc sc} {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (s : T) {Bs : Base D.host.F D.host.E}
    (hsub : (GlobalTheory.SqStep.chs G i j s).T ⊆ Bs.P)
    (hin : ∀ v : Bs.P, v.1 ∈ (GlobalTheory.SqStep.chs G i j s).T → GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G s)
    (hU : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      GlobalTheory.AdelicU.splitPrime τ ∈ locPl G s → AUnit τ) :
    Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))
      (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s) := by
  classical
  refine ⟨rfl, rfl, fun w => ⟨fun hw => ?_, ?_⟩, fun v hv => hU _ _ (hin v hv)⟩
  · have hv : w.under (𝓞 D.host.F) ∈ (GlobalTheory.SqStep.chs G i j s).T := by
      by_cases h0 : w ∈ G.pl.W0
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h0
        rw [G.pl.under_w hv]
        exact Finset.mem_union_left _ hv
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, h0⟩, rfl⟩)
    exact ⟨⟨_, hsub hv⟩, hv, GlobalTheory.FunObj.Good.under_injOn hL G s (hin ⟨_, hsub hv⟩ hv) hw (GlobalTheory.AdelicU.splitPrime_under _)⟩
  · rintro ⟨v, hv, rfl⟩
    exact hin v hv
private theorem base_split_prime_in_local_places {G : GridData Lc sc} {μ₀ : T} (hL : Lc.Is μ₀) {W : G.Weil} {i j : Fin D.R.m} {t : T}
    {Bs : Base D.host.F D.host.E} (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (v : Bs.P) (hv : v.1 ∈ (GlobalTheory.SqStep.chs G i j μ₀).T) :
    GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G μ₀ := by
  classical
  rw [GlobalTheory.SqStepArith.chs_T_base G hL i j] at hv
  have hw : G.pl.w v.1 ∈ G.pl.W0 := Finset.mem_image_of_mem _ hv
  have h1 := hB.2.2.2 v (Finset.mem_union_left _ hv)
  have e := GlobalTheory.FunObj.Good.under_injOn hL G t h1 (Finset.mem_union_left _ hw)
    ((GlobalTheory.AdelicU.splitPrime_under _).trans (G.pl.under_w hv).symm)
  rw [e]
  exact Finset.mem_union_left _ hw
private theorem stage_regular_geometry {ψ : AddChar (AF D.host.F) ℂ} {A A' WW : HSp D} {X : Tri T A A' WW} {FA : GlobalTheory.ChainFr.Fr A}
    {FA' : GlobalTheory.ChainFr.Fr A'} {FW : GlobalTheory.ChainFr.Fr WW} {hr : A.rank + A'.rank = WW.rank} {Bs : Base D.host.F D.host.E}
    {Γ Γ₀ : Geo D.sp.cm.sig A.rank A'.rank} (hO : GlobalTheory.SqStepBig.Over X Γ) (g : Γ.IsGood Bs) (g₀ : Γ₀.IsGood Bs)
    (ep : Γ₀.p = Γ.p) (eq : Γ₀.q = Γ.q) (h : IsStageGeo ψ X FA FA' FW hr Bs Γ₀)
    (JA : Γ.V.J = (1 : D.host.E) • A.gram) (JB : Γ.V'.J = (-1 : D.host.E) • A'.gram)
    (m1 : Γ.M.μ = X.m.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA)) (d1 : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A 1 JA '' X.fd)
    (m2 : Γ.M'.μ = X.m'.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB)) (d2 : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU A' (-1) JB '' X.fd') :
    (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs ∧ IsStageGeo ψ X FA FA' FW hr Bs (reG Γ Γ₀.V Γ₀.V' Γ₀.W) := by
  obtain ⟨⟨r1, -, l1⟩, ⟨r2, -, l2⟩, r3, j3, l3⟩ := hO
  have L1 : Γ.V.L = Γ₀.V.L := Submodule.ext fun y => (l1 y).trans (h.latA.1 y).symm
  have L2 : Γ.V'.L = Γ₀.V'.L := Submodule.ext fun y => (l2 y).trans (h.latB.1 y).symm
  have L3 : Γ.W.L = Γ₀.W.L := Submodule.ext fun y => (l3 y).trans (h.latA.2 y).symm
  have J3 : Γ.W.J = Γ₀.W.J := j3.trans h.pairA.JW.symm
  have e1 : reS Γ.V Γ₀.V = Γ₀.V := reSpace_eq_of_same (JA.trans h.JA.symm) L1
  have e2 : reS Γ.V' Γ₀.V' = Γ₀.V' := reSpace_eq_of_same (JB.trans h.JB.symm) L2
  have e3 : reS Γ.W Γ₀.W = Γ₀.W := reSpace_eq_of_same J3 L3
  have hV : (reS Γ.V Γ₀.V).IsHerm D.sp.cm.sig Bs (A.rank - Γ.p) Γ.p := by rw [e1, ← ep]; exact g₀.hV
  have hV' : (reS Γ.V' Γ₀.V').IsHerm D.sp.cm.sig Bs Γ.q (A'.rank - Γ.q) := by rw [e2, ← eq]; exact g₀.hV'
  have hW : (reS Γ.W Γ₀.W).IsSkew D.sp.cm.sig Bs (A.rank + A'.rank - (Γ.p + Γ.q)) (Γ.p + Γ.q) := by
    rw [e3, ← ep, ← eq]; exact g₀.hW
  have G : (reG Γ Γ₀.V Γ₀.V' Γ₀.W).IsGood Bs :=
    ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, hV, hV', hW, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩
  refine ⟨G, ⟨h.pairA.base, h.pairA.psi, JA, J3.trans h.pairA.JW, ⟨_, _, hV⟩, ⟨_, _, hW⟩, G.hM⟩,
    ⟨h.pairB.base, h.pairB.psi, JB, J3.trans h.pairB.JW, ⟨_, _, hV'⟩, ⟨_, _, hW⟩, G.hM'⟩, ⟨l1, l3⟩, ⟨l2, l3⟩, h.cartA, h.cartB,
    JA, JB, m1, d1, m2, d2, h.basA, h.basB, h.basW⟩
end Helpers
theorem _root_.GlobalTheory.T.pivot_reduction_divisibility : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ → Γ.p = p → Γ.q = q → Γ.IsGood Bs →
        (∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s) →
        ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F A.rank A'.rank) (P' : PolF D WW.rank A'.rank),
          (∀ s, (s = t ∨ s = μ₀) → ∀ h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ s P' h) X.fd' X.m') →
          ∃ (P : PolF D WW.rank A.rank) (k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)ˣ), ∀ s, (s = t ∨ s = μ₀) →
            ∀ om om' Rf (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf →
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c →
              ∀ h, ((GlobalTheory.SqStep.chs G i j s).ν k : ℂ) * X.I W.ψ W.θ s P h = c * X.I' W.ψ W.θ s P' h := by
  intro hP hK hM
  obtain ⟨a1, h1⟩ := GlobalTheory.T.towerStage_seesawDictionary_framesSignatures
  obtain ⟨a2, h2⟩ := GlobalTheory.StageGeo.aUnit_locPl
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have q1 := g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G
  have q2 := g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G
  intro W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P' hint
  obtain ⟨F₀, F₀', FW₀, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨-, -, -, -, nA, nA', nW, hXi⟩ := hX
  have b1 := hg.eBig
  have b2 := hg.aBig
  have b3 := hg.lt
  have b4 := hg.even
  rw [hp, hq] at b1 b2
  obtain ⟨Γ₀, p₀, q₀, g₀, s₀⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X F₀ F₀' FW₀ hXi.rank Bs p q hB.2.1 hB.1.1 hB.2.2.1
    hXi.rigA hXi.rigA' hXi.rigW hXi.meas hXi.meas' nA nA' nW b4 (by omega) b2 hg.kappa
  have rd : ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.StageGeo.Reads (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (locPl G) Bs s (GlobalTheory.SqStep.chs G i j s) := by
    rintro s (rfl | rfl)
    · exact readings_of_split_units hL i j _ hB.1.2.1 hB.1.2.2.2 (q2 _)
    · exact readings_of_split_units hL i j _ hB.2.2.2.2.1.sub (base_split_prime_in_local_places hL hB.1) (q2 _)
  obtain ⟨κ, k, hκ⟩ := common_factor_of_pair_relation (t := t) (u := μ₀) (fun s => (GlobalTheory.SqStep.chs G i j s).ν) lam hF.1
    (fun s c => ∃ om om' Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c) (by
    rintro s₁ s₂ c₁ c₂ h₁ h₂ ⟨o₁, o₁', R₁, m₁, k₁⟩ ⟨o₂, o₂', R₂, m₂, k₂⟩
    obtain ⟨e, cA, cB, hv⟩ := (hs s₁ h₁).2.2.2.2 o₁ o₁' m₁.triple
    obtain ⟨G₂, S₂⟩ := stage_regular_geometry hO hg g₀ (p₀.trans hp.symm) (q₀.trans hq.symm) s₀ hv.JW hv.JW₁ hv.measW hv.domW hv.measW₁ hv.domW₁
    have t₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₁) o₁ o₁' :=
      ⟨m₁.triple.base, G₂, m₁.triple.chars, m₁.triple.weil, m₁.triple.weil'⟩
    have t₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs (GlobalTheory.ThK.reG Γ Γ₀.V Γ₀.V' Γ₀.W) (GlobalTheory.SqStep.chs G i j s₂) o₂ o₂' :=
      ⟨m₂.triple.base, G₂, m₂.triple.chars, m₂.triple.weil, m₂.triple.weil'⟩
    obtain ⟨R', Sa, Sb, da, db, n₁, n₂, l₁, l₂, hdb⟩ := _root_.exists_pivot_pair hP hK hM t₁ t₂
    have E1 := _root_.GlobalTheory.StageGeo.geometric_stage_constant_ratio hP hK hM hXi S₂ hd hF (rd s₁ h₁) (rd s₂ h₂) n₁ n₂ l₁ l₂
    obtain ⟨k, E2⟩ := _root_.GlobalTheory.ReBase.rebase_ratio_real_part hP hK m₁ m₂ n₁ n₂ k₁ k₂ l₁ l₂
    refine ⟨k⁻¹, ?_⟩
    have z₁ : (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have z₂ : (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    rw [Circle.coe_div] at E2
    rw [map_inv, map_inv, Circle.coe_inv, Circle.coe_inv]
    generalize (((GlobalTheory.SqStep.chs G i j s₁).ν k : Circle) : ℂ) = n₁ at z₁ E2 ⊢
    generalize (((GlobalTheory.SqStep.chs G i j s₂).ν k : Circle) : ℂ) = n₂ at z₂ E2 ⊢
    have E3 : da * c₂ * n₂ = n₁ * (db * c₁) := by rw [E2]; field_simp
    have E4 : n₁ * c₁ * lam s₂ = n₂ * c₂ * lam s₁ :=
      mul_left_cancel₀ hdb (by linear_combination (-lam s₂) * E3 + c₂ * n₂ * E1)
    calc n₂⁻¹ * c₁ * lam s₂ = n₁⁻¹ * n₂⁻¹ * (n₁ * c₁ * lam s₂) := by field_simp
      _ = n₁⁻¹ * c₂ * lam s₁ := by rw [E4]; field_simp)
  obtain ⟨-, Pm, pp, pp', J, hsurj, -, -, hI, hI', -⟩ := hF
  obtain ⟨P, eP⟩ := hsurj (κ • pp' P')
  refine ⟨P, k, fun s hs' om om' Rf c m kc h => ?_⟩
  rw [hI, hI' s P' (hint s hs'), eP, map_smul, hκ s c hs' ⟨om, om', Rf, m, kc⟩]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockModelAdmissiblePolynomialExists
section
section
noncomputable section
namespace GlobalTheory.GoodFock
section Ring
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli Finset
variable {U : Type} [Ring U] [Algebra ℂ U] {n b : ℕ}
end Ring
section Poly
open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)
end Poly
section Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.ChainFr GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.MixModel Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
end Theta
section Quot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Matrix GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.RealQuot Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {M X : HSp D}
end Quot
section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem exists_admissible_fock_polynomial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  intro hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, q, q', -, hq', hLM⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, q' P₀ = 0 → ∀ P, q' P = 0 := by
    by_cases h : ∃ P₀, q' P₀ ≠ 0
    · exact h.imp fun _ h h' => absurd h' h
    · push_neg at h
      exact ⟨0, fun _ => h⟩
  refine ⟨capelliC (quad (raiO τ (sgA A₁ τ) (B.ε τ)) (lowO τ (sgA A₁ τ) (B.ε τ)))
    ((W₁.rank : ℂ) - 1) P₀, fun α β htr hexp ωA ωB Pi rf rl p p' hm f hf => ⟨fun ν₁ 𝓕₁ hν => ?_, fun h0 P'' => ?_⟩⟩
  · obtain ⟨p₀, q₀, hsig, -, hlt⟩ := htr.sig
    have hW : IsWeilDatumO ψ (GlobalTheory.Grid.sgn false W₁) X α (α / β) (ωB.toSgn false) := hm.weilB
    have hk := killed_capelli hψ hθ (frSgn false A₁) B hf τ P₀
    refine GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain hP.siegelSetUnitary D ψ θ hθ false W₁ X _ _ ωB hm.weilB q₀ ⟨τ, (hsig τ).2.1⟩ (by omega) ν₁ 𝓕₁ hν _
      (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn false A₁) B hf.1 _) τ fun g h S₀ r d μ' 𝓕' hμ x i hx => ?_
    have := (hk.om hW hθ ((GlobalTheory.Grid.ofSgn false W₁).symm g) h).mixS_eq_zero hψ hθ d hμ x i hx
    exact this
  · have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨-, hco, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ)
      hm.weilB hexpB Pi rf rl p' hm.mapB
    have hc := LinearMap.congr_fun (comp_capelli (p' ∘ₗ fockF ψ θ false A₁ B f) _ _ ((W₁.rank : ℂ) - 1)
      (comp_quad A₁ B (fun τ => a τ - b τ) τ _ (hco f hf))) P₀
    obtain ⟨a', b', ha', hb', hgap⟩ := htr.gap τ
    rw [Formalism.L2.Fam.ThC.expU D α τ _ _ ha' (hexp τ).1, Formalism.L2.Fam.ThC.expU D β τ _ _ hb' (hexp τ).2] at hgap
    have hne : (∏ j : Fin W₁.rank, (-((X.rank : ℂ) / 2 + ((a τ - b τ : ℚ) : ℂ)) + ((W₁.rank : ℂ) - 1 - (j : ℕ)))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j _ h => ?_
      have hj : ((j : ℕ) : ℚ) + 1 ≤ W₁.rank := by exact_mod_cast j.2
      have h' : (-((X.rank : ℚ) / 2 + (a τ - b τ)) + ((W₁.rank : ℚ) - 1 - (j : ℕ))) = 0 := by
        refine Rat.cast_injective (α := ℂ) ?_
        push_cast at h ⊢
        exact h
      linarith
    have h1 : p' (fockF ψ θ false A₁ B f P₀) = 0 := (smul_eq_zero.1 (hc.symm.trans h0)).resolve_left hne
    obtain ⟨Pf, r, r', e, -, -, -, he⟩ := (hLM α β htr hexp).2 ωA ωB Pi rf rl p p' hm
    rw [he f hf] at h1 ⊢
    by_cases hz : q' P₀ = 0
    · rw [hP₀ hz, TensorProduct.zero_tmul, map_zero]
    · have h2 : q' P₀ ⊗ₜ[ℂ] r' f = 0 := e.injective (h1.trans (map_zero e).symm)
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hz
      have h3 := congrArg (fun x => TensorProduct.lid ℂ Pf (LinearMap.rTensor Pf l x)) h2
      have h4 : r' f = 0 := by simpa [hl] using h3
      rw [h4, TensorProduct.tmul_zero, map_zero]
end Main
end GlobalTheory.GoodFock
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_model_admissible_polynomial_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  first | exact @_root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | exact _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial | (intros; apply _root_.GlobalTheory.GoodFock.exists_admissible_fock_polynomial <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JoinedLocalSumEstimates
section
section
namespace GlobalTheory.RowClaim.JoinF
theorem joined_local_sum_estimates :
    _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK :=
  fun hP hK hM =>
    _root_.GlobalTheory.T.thetaLift_row_properties hP hK hM (_root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP)
      (_root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hM) (_root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM)
end GlobalTheory.RowClaim.JoinF
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_sum_estimates_joined : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  first | exact @_root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates | exact _root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates | (intros; apply _root_.GlobalTheory.RowClaim.JoinF.joined_local_sum_estimates <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmallStageThetaIntegralNonzeroCase
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
open MeasureTheory
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.StageSmallNz
theorem smallStage_thetaIntegral_of_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
      (∀ t P' h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      ∃ P' : PolF D WW.rank A'.rank, ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  have hH := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_seesawDictionary_framesSignatures (_root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p A A' WW X hX hint => ?_⟩
  obtain ⟨hd, h3⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, -, hsA', -, hD⟩ := hd W i j p 0 A A' WW X hX
  have hdef : ∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0 := fun τ => by simpa using hsA' τ
  have hIs := hX.2.2.2.2.2.2.2
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  have key : ∀ t, ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi)
      (pm : (WO A WW → ℂ) →ₗ[ℂ] Pi) (pm' : (WO A' WW → ℂ) →ₗ[ℂ] Pi),
      GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
        (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl pm pm' ∧ Nontrivial Pr ∧
      ∀ P', q' P' ≠ 0 → pm' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, pm, pm', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex
      (X.ω t) (X.ω' t) (hIs.weil t) (hIs.weil' t)
    obtain ⟨Pf, rr, rr', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    have hy := h3 W i j p 0 A A' WW X hX FA FA' FW t hf hf' Pm rf rl pm pm' hm Pr Pf q q' rr rr' e hq hq' hr hr'
    haveI : Nontrivial Pm := hm.irred.1
    refine ⟨Pm, rf, rl, pm, pm', hm, nontrivial_left e, fun P' hP' => ?_⟩
    rw [hr' _ hf']
    exact e.map_ne_zero_iff.2 (tmul_ne_zero hP' hy)
  by_cases hT : Nonempty T
  · obtain ⟨t0⟩ := hT
    haveI : Nontrivial Pr := (key t0).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
    obtain ⟨P0, rfl⟩ := hq' x
    refine ⟨P0, fun t h0 => ?_⟩
    obtain ⟨hTr, -, -, hf', -, hk'⟩ := hD t
    obtain ⟨Pm, rf, rl, pm, pm', hm, -, hne⟩ := key t
    have memF : ∀ P', GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
      fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩
    have eI' : GlobalTheory.SquareComm.thetaInt (X.ω' t) X.m' X.fd' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P0) =
        X.I' W.ψ W.θ t P0 := by
      funext h; simp only [GlobalTheory.SquareComm.thetaInt, Tri.I', hk']
    obtain ⟨Φ, hΦ, hΦ0⟩ := _root_.GlobalTheory.T.definite_theta_lift_ne_zero hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdef X.m' X.fd' hIs.meas'
      _ _ _ _ _ _ _ hm
    exact hΦ0 (_root_.GlobalTheory.T.vanishing_of_definite_small_irreducible hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdef X.m X.fd X.m' X.fd' hIs.meas hIs.meas'
      _ _ _ _ _ _ _ hm _ (memF P0) (hne P0 hx) (by rw [eI']; exact h0) Φ hΦ)
  · exact ⟨0, fun t => (hT ⟨t⟩).elim⟩
end GlobalTheory.StageSmallNz
end
end

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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallStage_thetaIntegral_nonzero_case : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
      (∀ t P' h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') →
      ∃ P' : PolF D WW.rank A'.rank, ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageSmallNz.smallStage_thetaIntegral_of_ne_zero | exact _root_.GlobalTheory.StageSmallNz.smallStage_thetaIntegral_of_ne_zero | (intros; apply _root_.GlobalTheory.StageSmallNz.smallStage_thetaIntegral_of_ne_zero <;> assumption)
end
end

