import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
section
noncomputable section

namespace GlobalTheory.ModuLR

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped NNReal ENNReal TensorProduct

theorem chi_Af (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (Af F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) = ∏ᶠ v, ‖evalV F v M.det‖ := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_matrixPair_integral_outside F κ M M⁻¹
  obtain ⟨hOc, hOs, hOt⟩ := GlobalTheory.T.finiteIntegers_topology F S
  let _ : MeasurableSpace (OPart F S) := borel _
  have _ : BorelSpace (OPart F S) := ⟨rfl⟩

  let φS : Af F →+* SPart F S := RingHom.pi fun v => (evalV F v.1).toRingHom
  let φO : Af F →+* (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Fv F v.1) :=
    RingHom.pi fun v => (evalV F v.1).toRingHom
  let ι : OPart F S →+* (∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, Fv F v.1) :=
    RingHom.pi fun v => (v.1.adicCompletionIntegers F).toSubring.subtype.comp (Pi.evalRingHom _ v)
  have hι : Function.Injective ι := fun x y h => funext fun v => Subtype.ext (congrFun h v)
  let MS : Matrix κ κ (SPart F S) := φS.mapMatrix M
  let MO : Matrix κ κ (OPart F S) := fun i j v => ⟨evalV F v.1 (M i j), (hS v.1 v.2 i j).1⟩
  let NO : Matrix κ κ (OPart F S) := fun i j v => ⟨evalV F v.1 (M⁻¹ i j), (hS v.1 v.2 i j).2⟩
  have hdS : MS.det = φS M.det := (RingHom.map_det φS M).symm
  have huS : IsUnit MS.det := hdS ▸ hM.map φS
  have hMO : ι MO.det = φO M.det := by
    rw [RingHom.map_det, RingHom.map_det]; rfl
  have hNO : ι NO.det = φO M⁻¹.det := by
    rw [RingHom.map_det, RingHom.map_det]; rfl
  have hON : MO.det * NO.det = 1 := hι (by
    rw [map_mul, hMO, hNO, ← map_mul, ← Matrix.det_mul, Matrix.mul_nonsing_inv M hM, Matrix.det_one,
      map_one, map_one])
  have huO : IsUnit MO.det := ⟨⟨_, _, hON, by rw [mul_comm]; exact hON⟩, rfl⟩
  let j : ((κ → SPart F S) × (κ → OPart F S)) →+ (κ → Af F) :=
    ((jS F S).toAddMonoidHom.compLeft κ).comp (zipHom κ (SPart F S) (OPart F S))
  have hj : IsOpenEmbedding j :=
    (IsOpenEmbedding.piMap fun _ => GlobalTheory.T.isOpenEmbedding_finiteAdeleOfSPartAndIntegralPart F S).comp (GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (SPart F S) (OPart F S))
  have key := GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict (κ → Af F) ((κ → SPart F S) × (κ → OPart F S)) j hj (mulVecCE M hM)
    (prodCE (mulVecCE MS huS) (mulVecCE MO huO)) (by
      intro x
      funext i
      rw [mulVecCE_apply, prodCE_apply, mulVecCE_apply, mulVecCE_apply]
      apply RestrictedProduct.ext
      intro v
      change evalV F v ((M *ᵥ j x) i) = evalV F v (jS F S ((MS *ᵥ x.1) i, (MO *ᵥ x.2) i))
      rw [evalV_jS]
      by_cases hv : v ∈ S
      · rw [dif_pos hv]
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        change evalV F v (M i k) * evalV F v (jS F S (x.1 k, x.2 k)) = _
        rw [evalV_jS, dif_pos hv]
        rfl
      · rw [dif_neg hv]
        change _ = ι ((MO *ᵥ x.2) i) ⟨v, hv⟩
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        change evalV F v (M i k) * evalV F v (jS F S (x.1 k, x.2 k)) = _
        rw [evalV_jS, dif_neg hv]
        rfl)
  rw [key, GlobalTheory.T.addEquivAddHaarChar_prodCongr, addEquivAddHaarChar_eq_one_of_compactSpace (mulVecCE MO huO), mul_one,
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (SPart F S)
      (by show IsArtinianRing (∀ v : S, Fv F v.1); infer_instance)
      ⟨fun x ⟨n, hn⟩ => funext fun v => IsReduced.eq_zero (x v) ⟨n, congrFun hn v⟩⟩ κ _ huS,
    GlobalTheory.T.haarModulusOfUnit_completionsAtPlaces_eq_prod_norm F S _ huS, hdS,
    finprod_eq_prod_of_mulSupport_subset (s := S), ← Finset.prod_coe_sort S]
  · rfl
  · intro v hv
    by_contra hvS
    apply hv
    have h1 := GlobalTheory.T.norm_eq_one_of_mul_eq_one_adicCompletionIntegers F v (MO.det ⟨v, hvS⟩) (NO.det ⟨v, hvS⟩) (congrFun hON ⟨v, hvS⟩)
    have h2 : (MO.det ⟨v, hvS⟩ : Fv F v) = evalV F v M.det := congrFun hMO ⟨v, hvS⟩
    show ‖evalV F v M.det‖ = 1
    rw [← h2]
    exact h1

theorem chi_AF (F : Type) [Field F] [NumberField F] [IsTotallyReal F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (∏ w, ‖(fstA F M.det) w‖) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  have hd₁ : (M.map (fstA F)).det = fstA F M.det := (RingHom.map_det (fstA F).toRingHom M).symm
  have hd₂ : (M.map (sndA F)).det = sndA F M.det := (RingHom.map_det (sndA F).toRingHom M).symm
  have hu₁ : IsUnit (M.map (fstA F)).det := hd₁ ▸ hM.map (fstA F)
  have hu₂ : IsUnit (M.map (sndA F)).det := hd₂ ▸ hM.map (sndA F)
  let j : ((κ → Ainf F) × (κ → Af F)) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (Ainf F) (Af F)
  have key := GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict (κ → AF F) ((κ → Ainf F) × (κ → Af F)) j hj (mulVecCE M hM)
    (prodCE (mulVecCE (M.map (fstA F)) hu₁) (mulVecCE (M.map (sndA F)) hu₂)) (by
      intro x
      funext i
      rw [mulVecCE_apply, prodCE_apply, mulVecCE_apply, mulVecCE_apply]
      refine Prod.ext ?_ ?_
      · change fstA F _ = _
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        exact Finset.sum_congr rfl fun k _ => rfl
      · change sndA F _ = _
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        exact Finset.sum_congr rfl fun k _ => rfl)
  rw [key, GlobalTheory.T.addEquivAddHaarChar_prodCongr, NNReal.coe_mul, chi_Af F _ hu₂, hd₂,
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (Ainf F)
      (by show IsArtinianRing (∀ v : InfinitePlace F, v.Completion); infer_instance)
      ⟨fun x ⟨n, hn⟩ => funext fun v => IsReduced.eq_zero (x v) ⟨n, congrFun hn v⟩⟩ κ _ hu₁, hd₁,
    GlobalTheory.GaugeProdFormula.modu_infinite F _ (hM.map (fstA F))]

theorem chi_lr (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)) :
    addEquivAddHaarChar (lrCE g a) = GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det g) ^ n *
      GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det a) ^ m := by
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := GlobalTheory.T.exists_restrictScalars_matrix_leftRightMul_adeleTensor F E m n g a
  apply NNReal.coe_injective
  rw [hchar, chi_AF F Λ hΛ, hdet, GlobalTheory.T.tensorIdeleNormalizedAbs_eq_adelic_abs_norm F E]
  simp [map_mul, map_pow]

theorem smul_map_lr (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)
    [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))]
    (μ : Measure (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))) [μ.IsAddHaarMeasure]
    (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)) :
    μ = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) ^ n *
      (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det a) : ℝ≥0∞) ^ m) • μ.map (lrCE g a) := by
  have h := addEquivAddHaarChar_smul_map μ (lrCE g a)
  rw [chi_lr F E m n g a] at h
  calc μ = _ := h.symm
    _ = _ := by rw [ENNReal.smul_def]; push_cast; rfl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem modu_lrMul : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)), μ.IsAddHaarMeasure → ∀ (g : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) : ENNReal) ^ n * (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ m) • Measure.map (fun u : Mx D m n => (HMul.hMul (HMul.hMul g.val (u : Matrix (Fin m) (Fin n) (AE D))) a.val : Mx D m n)) μ := by
  intro D m n μ hμ g a
  have _ : LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AF D.host.F ⊗[D.host.F] D.host.E))
  have _ : SecondCountableTopology (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AF D.host.F ⊗[D.host.F] D.host.E))
  have hb : BorelSpace (Fin m → Fin n → AE D) := inferInstance
  have _ : BorelSpace (Matrix (Fin m) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    ⟨by first | rfl | exact hb.measurable_eq⟩
  exact smul_map_lr D.host.F D.host.E m n μ g a

end GlobalTheory.ModuLR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentMulIntegralOfUnitFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.UnitAtPl

open GlobalTheory.FinPlLoc (idem ePl evalV_ePl ePl_int idem_mem_idAt idem_mul_self finPart_pair)

variable {D : D7}

theorem evalV_inv_mem (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    evalV D.host.F x (algebraMap D.host.F (Af D.host.F) ((c : D.host.F))⁻¹) ∈ x.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : x.intValuation c = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 hc
  have h2 := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) x c
  rw [h1] at h2
  show Valued.v ((((c : D.host.F))⁻¹ : D.host.F) : x.adicCompletion D.host.F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : HeightOneSpectrum.valuation D.host.F x (c : D.host.F) = 1 := h2
  rw [this, inv_one]

theorem inv_ePl_int (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    ((c : D.host.F))⁻¹ • ePl D (· = x) ∈ intAf D.host.F := by
  intro w
  rw [Algebra.smul_def, map_mul, evalV_ePl]
  split_ifs with h
  · subst h; rw [mul_one]; exact evalV_inv_mem w c hc
  · rw [mul_zero]; exact zero_mem _

theorem tmul_one_mul_mem {γ : Af D.host.F} (hγ : γ ∈ intAf D.host.F) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) : (γ ⊗ₜ[D.host.F] (1 : D.host.E)) * w ∈ intAE D := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, o, rfl⟩
    rw [map_mul]
    exact mul_mem (hγ v) (hα v)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem finPart_idem_inv (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) :
    finPart D (idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹) =
      (((c : D.host.F))⁻¹ • ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have h0 : idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹ =
      pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹ := by
    change (pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h1 : ((c : D.host.F) : D.host.E)⁻¹ = ((c : D.host.F))⁻¹ • (1 : D.host.E) := by
    rw [Algebra.smul_def, map_inv₀, mul_one]; rfl
  rw [h0, finPart_pair, h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem idem_mul_mem_of_unit : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (u : 𝓞 D.host.F), u ∉ v.asIdeal → ∀ z : AE D, GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z ∈ intAt D (· = v) → GlobalTheory.FinPlLoc.idem D (· = v) * z ∈ intAt D (· = v) := by
  intro D v u hu z hz
  have hu0 : ((u : D.host.F) : D.host.E) ≠ 0 := by
    intro h
    apply hu
    have h' : (u : D.host.F) = 0 := by exact_mod_cast h
    have h'' : u = 0 := by exact_mod_cast h'
    rw [h'']; exact zero_mem _
  have hinc : incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hu0, map_one]
  have key : idem D (· = v) * z = (idem D (· = v) * incA D ((u : D.host.F) : D.host.E)⁻¹) *
      (idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z) := by
    calc idem D (· = v) * z = (idem D (· = v) * idem D (· = v)) *
        (incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E)) * z := by
          rw [idem_mul_self, hinc, mul_one]
      _ = _ := by ring
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [key, (finPart D).map_mul, finPart_idem_inv]
  exact tmul_one_mul_mem (inv_ePl_int v u hu) hz.2

end GlobalTheory.UnitAtPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentSmulMemLatticeCompletionAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPlLoc

theorem idem_smul_mem_latMul_at : ∀ (D : D7) (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D) (z : Fin S.rank → AE D), z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (fun _ => True) → GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (· = v) := by
  intro D S 𝔞 L v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]
      exact mul_mem (ePl_int _ w) (hαi w)
    · rw [map_mul, evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.FinPlLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicSphericalEigenfunctionLocalHeckeAlgebraEigStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSphericalEigenfunction_local_heckeAlgebra_eigen : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ v ∉ Sb, ∀ f : GA D V → ℂ, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) ∧ ∀ h ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f := by
  first | exact @GlobalTheory.FinZeta.eigen_heckeAlg | exact GlobalTheory.FinZeta.eigen_heckeAlg | (intros; apply GlobalTheory.FinZeta.eigen_heckeAlg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AestronglyMeasurableExtChar
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

variable {n : ℕ} (ε : Fin n → Bool)

theorem measurable_detRoot : Measurable (detRoot (n := n) ε) := by
  have hdet : Continuous fun x : UJ ε => (umat x).det :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_det
  have h1 : Measurable fun x : UJ ε => Complex.arg (umat x).det / (n : ℝ) :=
    (Complex.measurable_arg.comp hdet.measurable).div_const _
  exact Circle.exp.continuous.measurable.comp h1

variable [NeZero n]

theorem measurable_root (j : ZMod n) : Measurable fun x : UJ ε => root ε x j :=
  (measurable_detRoot ε).mul_const _

theorem measurable_part (j : ZMod n) : Measurable fun x : UJ ε => part ε x j := by
  have hc : Continuous fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2 :=
    ((GlobalTheory.SqIntSU.continuous_unitScalar ε).comp ((continuous_fst.mul continuous_const).inv)).mul continuous_snd
  have hp : Measurable fun x : UJ ε => (detRoot ε x, x) := (measurable_detRoot ε).prodMk measurable_id
  have hcomp : Measurable ((fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2) ∘ fun x : UJ ε => (detRoot ε x, x)) :=
    hc.measurable.comp hp
  have he : (fun x : UJ ε => GlobalTheory.SqIntSU.unitScalar ε (root ε x j)⁻¹ * x) = ((fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2) ∘ fun x : UJ ε => (detRoot ε x, x)) := by
    funext x; simp only [Function.comp_apply, root]
  have hm : Measurable fun x : UJ ε => GlobalTheory.SqIntSU.unitScalar ε (root ε x j)⁻¹ * x := he ▸ hcomp
  exact hm.subtype_mk

theorem measurable_extChar (m : ℤ) (Θ : SUJ ε → ℂ) (hΘ : Measurable Θ) : Measurable (extChar ε m Θ) := by
  have hz : Continuous fun z : Circle => (z : ℂ) ^ m :=
    Continuous.zpow₀ (by fun_prop) m (fun z => Or.inl (Circle.coe_ne_zero z))
  unfold extChar
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (hz.measurable.comp (measurable_root ε j)).mul (hΘ.comp (measurable_part ε j))

end GlobalTheory.ExtChar

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem aestronglyMeasurable_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), AEStronglyMeasurable Θ' μ' → AEStronglyMeasurable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
  intro n _ ε μ' _ m Θ' hΘ
  have hm'' : Measurable (hΘ.mk Θ') := hΘ.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ g ∂μ', Θ' g = hΘ.mk Θ' g := hΘ.ae_eq_mk
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hE : MeasurableSet (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) :=
    MeasurableSet.iUnion fun j => measurable_part ε j hNm
  have hpre : scalarMul ε ⁻¹' (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) ⊆
      ⋃ k : ZMod n, Set.univ ×ˢ ((fun g => cen ε k * g) ⁻¹' N) := by
    rintro ⟨z, g⟩ hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨i, hi⟩ := root_scalarMul ε z g
    refine Set.mem_iUnion.2 ⟨i + j, Set.mem_univ _, ?_⟩
    have h := part_scalarMul ε z g i hi j
    simp only [Set.mem_preimage] at hj ⊢
    rw [h] at hj
    exact hj
  have hE0 : Measure.map (scalarMul ε) (circleHaar.prod μ') (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) = 0 := by
    rw [Measure.map_apply (GlobalTheory.SqIntSU.continuous_scalarMul ε).measurable hE]
    refine measure_mono_null hpre (measure_iUnion_null fun k => ?_)
    rw [Measure.prod_prod, measure_preimage_mul, hN0, mul_zero]
  have heq : extChar ε m (hΘ.mk Θ') =ᵐ[Measure.map (scalarMul ε) (circleHaar.prod μ')] extChar ε m Θ' := by
    refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hE0)
    by_contra hxE
    apply hx
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hxE
    simp only [extChar]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : Θ' (part ε x j) = hΘ.mk Θ' (part ε x j) := by
      by_contra h
      exact hxE j (hsub h)
    rw [h]
  exact (measurable_extChar ε m _ hm'').aestronglyMeasurable.congr heq

end GlobalTheory.ExtChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
section
noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def algAt (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = M.vac v) ∧ Φ = pure f φ}

variable (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)

theorem algAt_mono {T T' : Finset (Pl F)} (h : T ⊆ T') : algAt M ψ emb T ≤ algAt M ψ emb T' := by
  refine Submodule.span_mono ?_
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨f, φ, hf, hφ, fun v hv' => hv v fun h' => hv' (h h'), rfl⟩

theorem exists_algAt {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb)
    (T₀ : Finset (Pl F)) : ∃ T, T₀ ⊆ T ∧ Φ ∈ algAt M ψ emb T := by
  classical
  induction hΦ using Submodule.span_induction generalizing T₀ with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hco, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hco
    refine ⟨T₀ ∪ hfin.toFinset, Finset.subset_union_left, Submodule.subset_span ⟨f, φ, hf, hφ, fun v hv => ?_, rfl⟩⟩
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hne))
  | zero => exact ⟨T₀, subset_rfl, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    obtain ⟨T₂, h₂, hy₂⟩ := hy T₁
    exact ⟨T₂, h₁.trans h₂, add_mem (algAt_mono M ψ emb h₂ hx₁) hy₂⟩
  | smul c x _ hx =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    exact ⟨T₁, h₁, Submodule.smul_mem _ c hx₁⟩

end GlobalTheory.HoweGlobal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacTransfer

variable {D : D7} {S X : HSp D} {n d : ℕ}

def archLine (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) : ℝ →+ WO S X where
  toFun t := cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
  map_zero' := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 = 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd; simp only [map_zero]; rfl
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 • u) = 0
    rw [h, zero_smul]
    exact map_zero cS
  map_add' s t := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd; simp only [map_add]; rfl
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) • u) =
      cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u) + cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
    rw [h, add_smul]
    exact map_add cS _ _

theorem archLine_apply (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) (t : ℝ) :
    archLine cS u t = cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) := rfl

end GlobalTheory.VacTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactTorusProductRealPlacesSpecStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactTorusProductRealPlaces_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (s : D.what₂.Tau → Fin T.rank → ℝ), GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s ∈ GinfC T ∧ ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T (GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s)) = B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ := by
  first | exact @GlobalTheory.AdSpan.ConjHol.torProd_spec | exact GlobalTheory.AdSpan.ConjHol.torProd_spec | (intros; apply GlobalTheory.AdSpan.ConjHol.torProd_spec <;> assumption)
end

