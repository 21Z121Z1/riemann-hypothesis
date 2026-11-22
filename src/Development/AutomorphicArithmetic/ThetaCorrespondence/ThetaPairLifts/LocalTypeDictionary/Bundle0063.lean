import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0802
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0002
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3152
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0034
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0800

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsDarbouxBasisOfSymplecticPair
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
noncomputable section
namespace GlobalTheory.PairDarboux
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexOrder
theorem exists_darboux_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ ∧ GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ := by
  intro _ D ψ θ hψ _ ε M X A B χS χT ω eS eT hω _
  have hω' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε) := hω
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := GlobalTheory.AdelicU.isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  let τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w := fun w => ⟨_, hτf w⟩
  have hτ : ∀ w x, (τ w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  let Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank :=
    ⟨GlobalTheory.RealDict.sgE (D := D) ε • M.gram, ⊥, fun w => (if ε then 1 else -1 : ℂ) • A.cart (τf w), fun _ => 1⟩
  let Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank :=
    ⟨D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)), ⊥,
      fun w => (B.cart (τf w)).map conj, fun _ => 1⟩
  have hXJ : Xs.J = -(sgn ε M).gram := gram_neg_sgn ε M rfl
  have hWJ : Ws.J = D.host.xi0 • X.gramᵀ := rfl
  have hc : GlobalTheory.RealDict.sgE (D := D) ε ≠ 0 := by cases ε <;> simp [GlobalTheory.RealDict.sgE]
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hXh : ∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j := fun i j => by
    rw [hXJ]
    show star (-(sgn ε M).gram j i) = -(sgn ε M).gram i j
    rw [star_neg, GlobalTheory.TripleSpace.star_gram]
  have hXd : Xs.J.det ≠ 0 := by
    rw [hXJ]
    exact gram_det_ne (neg (sgn ε M))
  have hWs : ∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j := fun i j => by
    show star (D.host.xi0 * X.gram i j) = -(D.host.xi0 * X.gram j i)
    rw [star_mul', Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, GlobalTheory.TripleSpace.star_gram, neg_mul]
  have hWd : Ws.J.det ≠ 0 := by
    rw [hWJ, Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hξ) (gram_det_ne X)
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star (R := D.host.E) x
  obtain ⟨co, hrat⟩ := GlobalTheory.RatDarboux.exists_darboux (AF D.host.F) h2 D.sp.cm.sig hσ hXh hWs hXd hWd
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas M
  obtain ⟨hμ', h𝓕'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain M (J := Xs.J) _ hc rfl μ 𝓕 hμ h𝓕
  obtain ⟨o, ho⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E D.sp.cm.sig hcm
    (by haveI := GlobalTheory.InertOfConj.unram D; infer_instance)
  let Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws :=
    ⟨co, fun v => Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1,
      μ.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (J := Xs.J) _ rfl), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (J := Xs.J) _ rfl '' 𝓕⟩
  have hgood : Mo.IsGood ψ :=
    { rat := hrat
      vac := fun v => isVac_of_bot Mo rfl ψ o ho v
      std := Filter.Eventually.of_forall fun _ => rfl
      haar := hμ'
      dom := h𝓕' }
  obtain ⟨om, hom, htr⟩ := exists_weil_transp ψ ε M X Xs Ws rfl rfl Mo hrat χS χT ω hω
  refine ⟨Xs, Ws, Mo, ψ, χS, χT, om, τ, ⟨hcm, GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ, hXh, hXd, hWs, hWd,
    GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ hω'.resS, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ hω'.resT,
    hω'.hecS, hω'.hecT, hom, fun w => ?_, fun w => ?_⟩,
    ⟨rfl, rfl, rfl, fun w => ⟨τf w, hτ w, rfl, rfl⟩, hgood, htr⟩⟩
  · have h := GlobalTheory.TripleSpace.isCartan_neg_conj
      (isCartanInv_sgn ε M (τf w) (GlobalTheory.CompactFockAction.cart_isCartanInv A (τf w)))
    have e1 : Xs.J.map (τ w).1 = -((gramAt D (sgn ε M) (τf w)).map star) := by
      rw [hXJ]
      ext a b
      simp [gramAt, hτ]
    have e2 : Xs.θ w = -sgnM ε (A.cart (τf w)) := by
      cases ε <;> simp [Xs, sgnM]
    rw [e1, e2]
    exact h
  · have h := isCartan_conj (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (GlobalTheory.CompactFockAction.cart_isCartanInv B (τf w))
    have e0 : Complex.I * conj (tauE D (τf w) D.host.xi0) = ((tauE D (τf w) D.host.xi0).im : ℂ) := by
      apply Complex.ext <;> simp [Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero]
    have e1 : Complex.I • Ws.J.map (τ w).1 = ((tauE D (τf w) D.host.xi0).im : ℂ) • gramAt D X (τf w) := by
      ext a b
      have e3 : conj (tauE D (τf w) (X.gram b a)) = tauE D (τf w) (X.gram a b) := by
        rw [← GlobalTheory.TripleSpace.star_gram X b a]
        exact (hcm.2.2.2 (tauE D (τf w)) (X.gram b a)).symm
      show Complex.I * conj (tauE D (τf w) (D.host.xi0 * X.gram b a)) = _ * tauE D (τf w) (X.gram a b)
      rw [map_mul, map_mul, ← mul_assoc, e0, e3]
    rw [e1]
    exact h
end GlobalTheory.PairDarboux
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_darboux_basis_of_symplectic_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ ∧ GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ := by
  first | exact @_root_.GlobalTheory.PairDarboux.exists_darboux_pair | exact _root_.GlobalTheory.PairDarboux.exists_darboux_pair | (intros; apply _root_.GlobalTheory.PairDarboux.exists_darboux_pair <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsDarbouxCoordinatesTriple
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
namespace GlobalTheory.TripleDarboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model)
open GlobalTheory.WeilSchrodinger
end GlobalTheory.TripleDarboux
namespace GlobalTheory.TripleDarboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)
end GlobalTheory.TripleDarboux
namespace GlobalTheory.TripleDarboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)
theorem exists_darboux_basis_of_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
      ∃ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
        (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
        (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
        GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) ∧
        GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) := by
  intro _ D ψ hψ W W₁ X A A₁ B α β h ωA ωB hA hB
  classical
  let e : Fin (W.rank + W₁.rank) ≃ Fin X.rank := finCongr h.rank.symm
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  choose a b ha hb hab using h.gap
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_ram_set h
  obtain ⟨v₁, hv₁, hv₁s, ⟨τ₁⟩⟩ := exists_good_place D T
  let Bs : Base D.host.F D.host.E :=
    ⟨ψ, fun w => ⟨_, hτf w⟩, mα, mβ, T, fun v => (hT1 v v.2).1.some, v₁, τ₁⟩
  have hBs : Bs.IsGood D.sp.cm.sig := base_isGood Bs hψ fun v hv => (hT1 v hv).2
  have hemb : ∀ w x, (Bs.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨p, q, hsig, hn1, hn2⟩ := h.sig
  have hneg : ∀ τ, gramAt D (sgn true W) τ = -gramAt D W τ := fun τ => by ext i j; simp [gramAt, neg_gram]
  obtain ⟨ΛV, basV, hV⟩ := exists_isHerm Bs τf hemb (sgn true W) (fun τ => sgnM true (A.cart τ))
    (fun τ => isCartanInv_sgn true W τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ))
    (fun τ => by rw [hneg]; exact hasSignature_neg (hsig τ).1)
  have eJ : (-1 : D.host.E) • (sgn true W).gram = (1 : D.host.E) • W.gram := by
    rw [neg_gram, neg_smul, one_smul, one_smul, neg_neg]
  have eθ : (fun w => -sgnM true (A.cart (τf w))) = fun w => A.cart (τf w) := funext fun w => neg_neg _
  rw [eJ, eθ] at hV
  obtain ⟨ΛV', basV', hV'⟩ := exists_isHerm Bs τf hemb W₁ A₁.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A₁)
    fun τ => (hsig τ).2.1
  obtain ⟨ΛX, basX, hX⟩ := exists_isSkew Bs τf hemb X e B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
    fun τ => (hsig τ).2.2
  have e3 : X.rank - (p + q) = W.rank + W₁.rank - (p + q) := by rw [h.rank]
  rw [e3] at hX
  obtain ⟨Mo, hMo⟩ := exists_model Bs hBs W _ _ hV hX 1 one_ne_zero rfl
  obtain ⟨Mo', hMo'⟩ := exists_model Bs hBs W₁ _ _ hV' hX (-1) (neg_ne_zero.2 one_ne_zero) rfl
  obtain ⟨om, hom, htr⟩ := exists_weil Bs hBs true W X e _ _ hV hX 1 rfl (by rw [neg_gram, one_smul, neg_neg]) rfl Mo hMo hA
  obtain ⟨om', hom', htr'⟩ := exists_weil Bs hBs false W₁ X e _ _ hV' hX (-1) rfl (neg_one_smul _ _) rfl Mo' hMo' hB
  have hr := h.rank
  have hev := h.even
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have hTe : (⟨α, β, T, ∅⟩ : Chars D.host.F D.host.E).T = T := by simp [Chars.T]
  refine ⟨e, Bs, ⟨p, q, _, _, _, Mo, Mo'⟩, ⟨α, β, T, ∅⟩, om, om',
    ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, ⟨hBs, ?_, ?_, hom, hom'⟩, htr, htr'⟩
  · refine ⟨by omega, hr ▸ hev, fun w => ?_, ?_, hn2, hV, hV', hX, hMo, hMo'⟩
    · have h1 := eα w
      have h3 := eβ w
      have h4 := hab (τf w)
      rw [hr] at h4
      have : (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
        push_cast at h4 ⊢
        rw [h1, h3]
        linarith
      exact_mod_cast this
    · obtain ⟨m, hm⟩ := hev
      show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2
      omega
  · refine ⟨h.hecA, h.hecB, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resA),
      GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resB), hα, hβ, Finset.disjoint_empty_right _,
      hTe.le, fun w hw => hT2 w (hTe ▸ hw), fun w hw => (hT3 w fun h0 => hw ?_).1, fun w hw => (hT3 w fun h0 => hw ?_).2,
      ⟨hTe.symm ▸ hv₁, hv₁s⟩⟩
    · rw [hTe]; exact h0
    · rw [hTe]; exact h0
end GlobalTheory.TripleDarboux
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
theorem _root_.GlobalTheory.T.exists_darboux_coordinates_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
      ∃ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
        (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
        (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
        GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) ∧
        GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) := by
  first | exact @_root_.GlobalTheory.TripleDarboux.exists_darboux_basis_of_triple | exact _root_.GlobalTheory.TripleDarboux.exists_darboux_basis_of_triple | (intros; apply _root_.GlobalTheory.TripleDarboux.exists_darboux_basis_of_triple <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HeckeFormAnisotropicOfRallisBottom
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
open GlobalTheory.Core.Rk.IP in
theorem GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.RallisBottom.HeckeFormAniso D := by
  intro hP D
  have hU19 := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic hP.unramifiedDoublingGL D)
    (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU19 D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D))
  have hE : EulerRight D :=
    GlobalTheory.T.doubling_eulerProduct_farRight hP.cuspRapidDecay D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair hP.weilRepresentationUnitaryPair D) hLZ hPB
  have hG : GlobalTheory.BottomRallis.GlobalFormAniso D :=
    _root_.GlobalTheory.T.theta_tower_compatibility hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
      (_root_.UpperTheory.Lit.Sw47.siegelWeil_fock_anisotropic_unconditional D)
  exact GlobalTheory.BottomRallis.heckeFormAniso_of_global_euler D hG hE
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_bottom_hecke_form_anisotropic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.RallisBottom.HeckeFormAniso D := by
  first | exact @_root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom | exact _root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom | (intros; apply _root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaLargeRank
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotFormula
end GlobalTheory.BotFormula
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.BotFormula.rallis_bottom_formula_large_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T, starRingEnd ℂ (P.coord h T) = Ω * u * X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := _root_.GlobalTheory.T.bottomTheta_kernel_finiteDimensional hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := _root_.GlobalTheory.T.bottom_thetaIntegral_classSum_formula hPr hK hM hI hB
  refine ⟨max cA cB, fun ε CF hCF => ?_⟩
  obtain ⟨CA, xA, hA⟩ := hA ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max CA CB, max xA xB, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have hA := hA C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have hB' := hB' C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω₀, hΩ₀, HK⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨v, hv, HC⟩ := hB' W hψ i j A A' WW X δ t0 hX
  refine ⟨(v * Ω₀)⁻¹, inv_ne_zero (mul_ne_zero hv hΩ₀), fun s Q P P' hP => ?_⟩
  obtain ⟨u, hu, huQ, huU, HK⟩ := HK s Q P P' hP
  have huQ' : u⁻¹ ∈ Qbar := inv_mem huQ
  refine ⟨u⁻¹, inv_ne_zero hu, huQ', fun p _ hp lam => ?_, fun ea ed h g hg T => ?_⟩
  · have h1 := GlobalTheory.BotFormula.lamC_mul lam huQ huQ'
    rw [mul_inv_cancel₀ hu] at h1
    have h2 : lamC lam (1 : ℂ) = 1 := by
      unfold lamC
      rw [dif_pos (one_mem Qbar)]
      exact (congrArg lam (Subtype.ext rfl : (⟨1, one_mem Qbar⟩ : Qbar) = 1)).trans (map_one lam)
    rw [h2] at h1
    have h3 := congrArg norm h1
    rw [norm_mul, huU p hp lam, one_mul, norm_one] at h3
    exact h3.symm
  have pts : ∀ x : GA D P.a, ∃ y : GA D A, GlobalTheory.BotFormula.IsFinPt A y x := fun x =>
    GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne A hX.std.1 x ea.symm
  choose pt hpt using pts
  rw [HC s Q P P' hP ea ed g pt hpt T]
  simp_rw [HK ea ed h g _ (pt _) hg (hpt _) T]
  rw [GlobalTheory.NormSum.Pair.coord, GlobalTheory.BotFormula.conj_finsum]
  have e1 : ∀ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * (Ω₀ * u * starRingEnd ℂ (P.term x.out h T)) =
      (Ω₀ * u) * starRingEnd ℂ (((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * P.term x.out h T) := by
    intro x
    rw [map_mul, map_inv₀, map_natCast]; ring
  simp_rw [e1, ← mul_finsum]
  field_simp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_bottom_formula_large : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T, starRingEnd ℂ (P.coord h T) = Ω * u * X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g := by
  first | exact @_root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank | exact _root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank | (intros; apply _root_.GlobalTheory.BotFormula.rallis_bottom_formula_large_rank <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisInnerProductBottomNormEq
section
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
noncomputable section
namespace GlobalTheory.BottomRallis
variable {D : D7}
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
variable {D : D7}
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
variable {D : D7}
theorem rallis_inner_product_bottom_norm_eq (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A B : HSp D}
    {χA χB : (AE D)ˣ →* Circle} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A} {a : GL (Fin A.rank) (AE D)}
    {om : WRep A B} {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hPair : Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕)
    (hA : wittIndex A = 0) (hB : wittIndex B = 0) {LA : Lat A} {LB : Lat B} {Sf : Finset (FinPl D)}
    {Φ : WO A B → ℂ} (hF : IsFockVec ψ θ A B sA sB Φ) (hU : Unram ψ A B χB LA LB Sf Φ Φ)
    (m : Measure (GA D A)) (mH : Measure (GA D B)) [m.IsHaarMeasure] [mH.IsHaarMeasure]
    (hint : ∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧
      IntegrableOn (integrand om m ν 𝓕 LA a Φ Φ (fun _ => 1) (fun _ => 1) s₁) (openOff A LA Sf) m)
    (l : ℕ → ℂ) (hl : ∀ i < A.rank,
      HolValueAt (LFun.charL χB⁻¹ (Sf : Set (FinPl D))) ((t : ℂ) / 2 + (A.rank : ℂ) / 2 - i) (l i)) :
    petersson B mH (up om m Φ (fun _ => 1)) (up om m Φ (fun _ => 1)) =
      volQ B mH * volQ A m * ((∏ i ∈ Finset.range A.rank, l i) /
        LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
        ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ Φ g ∂m := by
  have hU19 := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic hP.unramifiedDoublingGL D)
    (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU19 D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D))
  have hE : EulerRight D :=
    GlobalTheory.T.doubling_eulerProduct_farRight hP.cuspRapidDecay D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair hP.weilRepresentationUnitaryPair D) hLZ hPB
  have hG : GlobalFormAniso D := _root_.GlobalTheory.T.theta_tower_compatibility hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
    (_root_.UpperTheory.Lit.Sw47.siegelWeil_fock_anisotropic_unconditional D)
  have hH := heckeFormAniso_of_global_euler D hG hE
  have h1 : (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := GlobalTheory.T.one_mem_A0_of_wittIndex_eq_zero hPair.setting hA
  have hpar := GlobalTheory.T.constantFunction_has_trivialRep_satakeParameters A LA Sf hU.sdA hU.two
  have hsph : SphFun A LA Sf (fun _ : GA D A => (1 : ℂ)) := fun _ _ _ _ _ => rfl
  obtain ⟨-, -, -, hfin⟩ := hH ψ θ A B χA χB sA sB t cA a om ν 𝓕 hPair hB LA LB Sf Φ Φ hF hF hU m mH
    inferInstance inferInstance _ h1 _ h1 (trivPar A.rank) hpar hsph hint
  have hL : HolValueAt (fun s => LFun.LSD D Sf (trivPar A.rank) χB (s + 1 / 2)) ((t : ℂ) / 2)
      (∏ i ∈ Finset.range A.rank, l i) := by
    refine HolValueAt.congr (holValueAt_prod (Finset.range A.rank) fun i hi => ?_) (GlobalTheory.T.partial_L_trivial_rep_twist_eq_prod_hecke_L χB Sf A.rank hU.unr)
    have h2 := hl i (Finset.mem_range.1 hi)
    rw [show (t : ℂ) / 2 + (A.rank : ℂ) / 2 - i = (t : ℂ) / 2 + ((A.rank : ℂ) / 2 - i) by ring] at h2
    have h3 := h2.comp_add
    simpa only [add_sub_assoc] using h3
  rw [hfin _ hL]
  simp only [rcoef_one]
  rw [integral_mul_const]
  ring
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
end GlobalTheory.BottomRallis
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TranslatedJetsDictionary
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedDict
theorem jets_moved_by_translation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧ ∀ (k : ℕ), 0 < k → ∀ w : WO (ch.G.pS p) (ch.G.pT p), k • w ∈ latO (ch.G.pS p) (ch.G.pT p) (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True) → ∃ (ζ : Qbar) (s : VC D (ch.G.pS p).rank (ch.G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ k • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt ∧ ∀ mon, jetTab ch.W ch.S.N.frC p (heisO ch.W.ψ (ch.G.pS p) (ch.G.pT p) w (ch.S.Z.vac p)) (x * ch.S.N.u _) (y * ch.S.N.u _) mon = ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) s (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)) := by
  intro hPr hInp
  obtain ⟨CF0, h2⟩ := _root_.GlobalTheory.T.twist_moved_vacuum_correspondence hPr hInp
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h2 ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx₀ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt => ?_⟩
  intro p hp x y
  obtain ⟨Ls, Lt, κ, hSs, hSt, hκ, hd, hq, hvac, hmov, hjet⟩ := hx D large₂ hε hx₀ Γ Pl0 T A Ks R F hS ch hIs hAt p hp x y
  refine ⟨Ls, Lt, κ, hSs, hSt, hκ, hd, hq, fun n hn w hw => ?_⟩
  obtain ⟨ζ, s, hζ, hs, hj⟩ := GlobalTheory.T.finiteHeisenbergTranslate_selfDualVacuum_fockJets ch.S.toGridChoice p hp Ls Lt κ _ hSs hSt hd hvac hjet n hn _
    (by rw [← actO_nsmul]; exact hmov _ hw)
  refine ⟨ζ, s, hζ, hs, fun mon => ?_⟩
  rw [jetTab_heisO ch.W ch.S.N.frC p hp _ (ch.S.Z.vac_is p hp).2.theta w _ _ mon]
  exact hj _
end GlobalTheory.MovedDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_jets_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧ ∀ (k : ℕ), 0 < k → ∀ w : WO (ch.G.pS p) (ch.G.pT p), k • w ∈ latO (ch.G.pS p) (ch.G.pT p) (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True) → ∃ (ζ : Qbar) (s : VC D (ch.G.pS p).rank (ch.G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ k • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt ∧ ∀ mon, jetTab ch.W ch.S.N.frC p (heisO ch.W.ψ (ch.G.pS p) (ch.G.pT p) w (ch.S.Z.vac p)) (x * ch.S.N.u _) (y * ch.S.N.u _) mon = ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) s (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)) := by
  first | exact @_root_.GlobalTheory.MovedDict.jets_moved_by_translation | exact _root_.GlobalTheory.MovedDict.jets_moved_by_translation | (intros; apply _root_.GlobalTheory.MovedDict.jets_moved_by_translation <;> assumption)
end
end

