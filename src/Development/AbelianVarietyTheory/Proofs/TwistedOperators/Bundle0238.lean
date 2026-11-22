import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviConjHaarModulus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0358
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairTensor

open GlobalTheory.InvPairingTensor (exists_real_parts inner_act_skew exists_frame)

variable {p q : ℕ} {T : GrpData p q} (R : DSRep T)

theorem eq_zero_of_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (y : R.HK.V ⊗[ℂ] U)
    (hy : ∀ v, ctr R U v y = 0) : y = 0 := by
  let m : R.HK.V → R.HK.V →ₗ[ℂ] ℂ := fun v => innerₛₗ ℂ (R.ι v) ∘ₗ R.ι
  have sepm : ∀ b, (∀ v, m v b = 0) → b = 0 := fun b h => by
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h b)
  have key : ∀ v (z : R.HK.V ⊗[ℂ] U),
      GlobalTheory.PairingTensor.contrR (m v) (TensorProduct.comm ℂ _ _ z) = ctr R U v z := by
    intro v z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [TensorProduct.comm_tmul, GlobalTheory.PairingTensor.contrR_tmul, ctr_tmul]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  apply (TensorProduct.comm ℂ _ _).injective
  rw [map_zero]
  exact GlobalTheory.PairingTensor.eq_zero_of_contrR m sepm _ fun v => by rw [key, hy]

theorem ext_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (z w : R.HK.V ⊗[ℂ] U)
    (h : ∀ v, ctr R U v z = ctr R U v w) : z = w := by
  rw [← sub_eq_zero]
  exact eq_zero_of_ctr R U _ fun v => by rw [map_sub, h, sub_self]

theorem ctr_add (U : Type) [AddCommGroup U] [Module ℂ U] (v w : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U (v + w) z = ctr R U v z + ctr R U w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_add, inner_add_left, add_smul]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

theorem ctr_smul (U : Type) [AddCommGroup U] [Module ℂ U] (c : ℂ) (v : R.HK.V)
    (z : R.HK.V ⊗[ℂ] U) : ctr R U (c • v) z = (starRingEnd ℂ) c • ctr R U v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_smul, inner_smul_left, mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem ctr_act (U : Type) [AddCommGroup U] [Module ℂ U] {X : Mat p q} (hX : X ∈ upq p q)
    (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U v (TensorProduct.map (R.HK.act X) LinearMap.id z) = -ctr R U (R.HK.act X v) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.map_tmul, ctr_tmul, ctr_tmul,
      eq_neg_of_add_eq_zero_left (inner_act_skew R hX v a), neg_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

variable {W U : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  (a : Mat p q →ₗ[ℂ] Module.End ℂ W)

theorem exists_finiteDimensional_kill (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) (P : W) :
    ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧
      ∀ y, (∀ x ∈ E, inner ℂ (R.ι y) (R.ι x) = 0) → B P y = 0 := by
  obtain ⟨W₀, hW, hP, hst⟩ := ha.2.1 P
  obtain ⟨E, hE, hE'⟩ := GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q R.HK hA _ a
    (fun Y Z _ _ => ha.1 Y Z) W₀ hW hst (fun v _ => ha.2.2 v)
  refine ⟨E, hE, fun y hy => ?_⟩
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  obtain ⟨F, hF, hyF, hFst⟩ := R.HK.kfin y
  obtain ⟨n, e, heF, he⟩ := exists_frame R.ι R.ι_inj F
  let φ : W →ₗ[ℂ] R.HK.V := ∑ j, (l ∘ₗ B.flip (e j)).smulRight (e j)
  have hφ : ∀ w, φ w = ∑ j, l (B w (e j)) • e j := fun w => by
    simp [φ, LinearMap.sum_apply]
  have hφF : ∀ w, φ w ∈ F := fun w => by
    rw [hφ]; exact F.sum_mem fun j _ => F.smul_mem _ (heF j)
  have hR : ∀ w, ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ w)) = l (B w x) := fun w x hx => by
    conv_rhs => rw [← he x hx]
    rw [hφ]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, LinearMap.map_smulₛₗ,
      inner_conj_symm, smul_eq_mul, mul_comm]
  have hreal : ∀ X ∈ upq p q, IsKC X → ∀ w, φ (a X w) = R.HK.act X (φ w) := by
    intro X hX hK w
    have hd : φ (a X w) - R.HK.act X (φ w) ∈ F :=
      F.sub_mem (hφF _) (hFst X hK _ (hφF w))
    have h0 : ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ (a X w) - R.HK.act X (φ w))) = 0 := by
      intro x hx
      have h1 := inner_act_skew R hX x (φ w)
      have h2 := congrArg l (hB X hX w x)
      rw [map_add, map_zero] at h2
      rw [hR w _ (hFst X hK x hx)] at h1
      rw [map_sub, inner_sub_right, hR _ x hx]
      linear_combination h2 - h1
    rw [← sub_eq_zero]
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h0 _ hd)
  have heq : ∀ Z, IsKC Z → ∀ w, φ (a Z w) = R.HK.act Z (φ w) := by
    intro Z hZ w
    obtain ⟨X, Y, hX, hY, hK, rfl⟩ := exists_real_parts Z
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hreal X hX (hK hZ).1, hreal Y hY (hK hZ).2]
  rw [← hR P y hyF]
  exact hy _ (hE' φ heq P hP)

theorem exists_pairing (f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U)
    (hf : ∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) :
    ∃ B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B ∧ ∀ P v, B P v = ctr R U v (f P) := by
  let B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P =>
        { toFun := fun v => ctr R U v (f P)
          map_add' := fun v w => ctr_add R U v w _
          map_smul' := fun c v => ctr_smul R U c v _ }
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  refine ⟨B, fun Z hZ P v => ?_, fun _ _ => rfl⟩
  change ctr R U v (f (a Z P)) + ctr R U (R.HK.act Z v) (f P) = 0
  have := LinearMap.congr_fun (hf Z) P
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
  rw [this, ctr_act R U hZ, neg_add_cancel]

theorem exists_map (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) :
    ∃ f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U,
      (∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) ∧
        ∀ P v, B P v = ctr R U v (f P) := by
  have ex : ∀ P, ∃ z : R.HK.V ⊗[ℂ] U, ∀ y, ctr R U y z = B P y := by
    intro P
    obtain ⟨E, hE, hkill⟩ := exists_finiteDimensional_kill R a ha hA B hB P
    obtain ⟨n, e, heE, he⟩ := exists_frame R.ι R.ι_inj E
    refine ⟨∑ j, e j ⊗ₜ[ℂ] B P (e j), fun y => ?_⟩
    have h1 := hkill (y - ∑ j, inner ℂ (R.ι (e j)) (R.ι y) • e j) (fun x hx => by
      rw [map_sub, inner_sub_left, sub_eq_zero]
      conv_lhs => rw [← he x hx]
      simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
        inner_conj_symm, mul_comm])
    rw [map_sub, sub_eq_zero] at h1
    rw [h1]
    simp only [map_sum, ctr_tmul, LinearMap.map_smulₛₗ, inner_conj_symm]
  choose g hg using ex
  let f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U :=
    { toFun := g
      map_add' := fun P Q => ext_ctr R U _ _ fun y => by
        rw [map_add, hg, hg, hg, map_add, LinearMap.add_apply]
      map_smul' := fun t P => ext_ctr R U _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply, LinearMap.smul_apply] }
  have hf : ∀ P y, ctr R U y (f P) = B P y := hg
  have hreal : ∀ X ∈ upq p q, ∀ P,
      f (a X P) = TensorProduct.map (R.HK.act X) LinearMap.id (f P) := by
    intro X hX P
    refine ext_ctr R U _ _ fun y => ?_
    rw [ctr_act R U hX, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB X hX P y)
  refine ⟨f, fun Z => ?_, fun P y => (hf P y).symm⟩
  obtain ⟨X, Y, hX, hY, -, rfl⟩ := exists_real_parts Z
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.comp_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.map_add_left, TensorProduct.map_smul_left, hreal X hX, hreal Y hY]

end GlobalTheory.ArchRec.PairTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMeasureModulus
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.ParabModulus

section General

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

noncomputable def prodMul (μM μN : Measure G) : Measure G := (μM.prod μN).map (fun z => z.1 * z.2)

theorem lintegral_prodMul (μM μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂prodMul μM μN = ∫⁻ m, ∫⁻ u, f (m * u) ∂μN ∂μM := by
  rw [prodMul, lintegral_map hf measurable_mul]
  exact lintegral_prod (fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul).aemeasurable

theorem measurable_inner (μN : Measure G) [SFinite μN] (f : G → ENNReal) (hf : Measurable f) :
    Measurable fun m => ∫⁻ u, f (m * u) ∂μN :=
  Measurable.lintegral_prod_right' (f := fun z : G × G => f (z.1 * z.2)) (hf.comp measurable_mul)

theorem prodMul_left_fst (M : Subgroup G) (μM μN : Measure G) [SFinite μN]
    (iM : ∀ s ∈ M, μM.map (fun g => s * g) = μM) (s : G) (hs : s ∈ M) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iM s hs) _ (measurable_inner μN f hf)
  simpa only [mul_assoc] using this

theorem prodMul_left_snd (M N : Subgroup G) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m⁻¹ * u * m ∈ N)
    (μM μN : Measure G) [SFinite μN] (h1 : μM (M : Set G)ᶜ = 0)
    (iN : ∀ s ∈ N, μN.map (fun g => s * g) = μN) (s : G) (hs : s ∈ N) :
    (prodMul μM μN).map (fun g => s * g) = prodMul μM μN := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_const_mul s), lintegral_prodMul _ _ (fun x => f (s * x)) (hf.comp (measurable_const_mul s)),
    lintegral_prodMul _ _ _ hf]
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  refine lintegral_congr_ae (aM.mono fun m hm => ?_)
  have := GlobalTheory.IwasawaShape.lintegral_mul_left_of_map (iN _ (hnorm m hm s hs)) (fun u => f (m * u))
    (hf.comp (measurable_const_mul m))
  show ∫⁻ u, f (s * (m * u)) ∂μN = ∫⁻ u, f (m * u) ∂μN
  rw [← this]
  refine lintegral_congr fun u => ?_
  rw [show m * (m⁻¹ * s * m * u) = s * (m * u) by group]

theorem prodMul_facts (M N P : Subgroup G) (hM : IsClosed (M : Set G)) (hN : IsClosed (N : Set G))
    (hPm : MeasurableSet (P : Set G)) (hMN : ∀ m ∈ M, m ∈ N → m = 1)
    (hMP : ∀ m ∈ M, ∀ u ∈ N, m * u ∈ P) (hdec : ∀ p ∈ P, ∃ m ∈ M, ∃ u ∈ N, p = m * u)
    (μM μN : Measure G) [SigmaFinite μN] [IsFiniteMeasureOnCompacts μM] [IsFiniteMeasureOnCompacts μN]
    (hM0 : μM ≠ 0) (hN0 : μN ≠ 0) (h1 : μM (M : Set G)ᶜ = 0) (h2 : μN (N : Set G)ᶜ = 0) :
    prodMul μM μN (P : Set G)ᶜ = 0 ∧ SigmaFinite (prodMul μM μN) ∧
      ∃ T : Set G, MeasurableSet T ∧ prodMul μM μN T ≠ 0 ∧ prodMul μM μN T ≠ ⊤ := by
  set ρ₀ := prodMul μM μN with hρ₀
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 h1
  have aN : ∀ᵐ u ∂μN, u ∈ N := mem_ae_iff.2 h2
  have hP0 : ρ₀ (P : Set G)ᶜ = 0 := by
    rw [← lintegral_indicator_one hPm.compl, hρ₀, lintegral_prodMul _ _ _ (measurable_one.indicator hPm.compl)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aM] with m hm
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [aN] with u hu
    rw [Set.indicator_of_notMem (show m * u ∉ (P : Set G)ᶜ from fun h => h (hMP m hm u hu))]
    simp
  set Q : ℕ → Set G := fun i => (compactCovering G i ∩ M) * (compactCovering G i ∩ N) with hQ
  have hQc : ∀ i, IsCompact (Q i) := fun i =>
    ((isCompact_compactCovering G i).inter_right hM).mul ((isCompact_compactCovering G i).inter_right hN)
  have uniq : ∀ i, ∀ m ∈ M, ∀ u ∈ N, m * u ∈ Q i → m ∈ compactCovering G i ∧ u ∈ compactCovering G i := by
    rintro i m hm u hu ⟨m', ⟨hm'C, hm'M⟩, u', ⟨hu'C, hu'N⟩, e⟩
    have e : m' * u' = m * u := e
    have e' : m'⁻¹ * m = u' * u⁻¹ := by
      calc m'⁻¹ * m = m'⁻¹ * (m * u) * u⁻¹ := by group
        _ = m'⁻¹ * (m' * u') * u⁻¹ := by rw [e]
        _ = u' * u⁻¹ := by group
    have h := hMN _ (M.mul_mem (M.inv_mem hm'M) hm) (by rw [e']; exact N.mul_mem hu'N (N.inv_mem hu))
    have hm' : m = m' := (inv_mul_eq_one.1 h).symm
    rw [h] at e'
    have hu' : u = u' := (mul_inv_eq_one.1 e'.symm).symm
    exact ⟨hm' ▸ hm'C, hu' ▸ hu'C⟩
  have hQ1 : ∀ i, ρ₀ (Q i) < ⊤ := by
    intro i
    have hC := isCompact_compactCovering G i
    rw [← lintegral_indicator_one (hQc i).measurableSet, hρ₀,
      lintegral_prodMul _ _ _ (measurable_one.indicator (hQc i).measurableSet)]
    calc _ ≤ ∫⁻ m, (compactCovering G i).indicator (fun _ => μN (compactCovering G i)) m ∂μM := by
          refine lintegral_mono_ae ?_
          filter_upwards [aM] with m hm
          by_cases hmC : m ∈ compactCovering G i
          · rw [Set.indicator_of_mem hmC, ← lintegral_indicator_one hC.measurableSet]
            refine lintegral_mono_ae ?_
            filter_upwards [aN] with u hu
            by_cases hq : m * u ∈ Q i
            · simp [Set.indicator_of_mem hq, Set.indicator_of_mem (uniq i m hm u hu hq).2]
            · simp [Set.indicator_of_notMem hq]
          · rw [Set.indicator_of_notMem hmC]
            refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
            filter_upwards [aN] with u hu
            rw [Set.indicator_of_notMem (fun h => hmC (uniq i m hm u hu h).1)]
            simp
      _ < ⊤ := by
          rw [lintegral_indicator_const hC.measurableSet]
          exact ENNReal.mul_lt_top hC.measure_lt_top hC.measure_lt_top
  have hS : ⋃ i, (Q i ∪ (P : Set G)ᶜ) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ?_
    by_cases hg : g ∈ P
    · obtain ⟨m, hm, u, hu, rfl⟩ := hdec g hg
      obtain ⟨i, hi⟩ := exists_mem_compactCovering m
      obtain ⟨k, hk⟩ := exists_mem_compactCovering u
      exact ⟨max i k, Or.inl (Set.mul_mem_mul ⟨compactCovering_subset G (le_max_left _ _) hi, hm⟩
        ⟨compactCovering_subset G (le_max_right _ _) hk, hu⟩)⟩
    · exact ⟨0, Or.inr hg⟩
  have hS1 : ∀ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) < ⊤ := fun i =>
    lt_of_le_of_lt (measure_union_le _ _) (by rw [hP0, add_zero]; exact hQ1 i)
  have sf : SigmaFinite ρ₀ := ⟨⟨⟨fun i => Q i ∪ (P : Set G)ᶜ, fun _ => trivial, hS1, hS⟩⟩⟩
  have huniv : ρ₀ Set.univ ≠ 0 := by
    rw [hρ₀, prodMul, Measure.map_apply measurable_mul MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero (fun h => hM0 (Measure.measure_univ_eq_zero.1 h))
      (fun h => hN0 (Measure.measure_univ_eq_zero.1 h))
  obtain ⟨i, hi⟩ : ∃ i, ρ₀ (Q i ∪ (P : Set G)ᶜ) ≠ 0 := by
    by_contra h
    push_neg at h
    exact huniv (by rw [← hS]; exact measure_iUnion_null h)
  refine ⟨hP0, sf, Q i, (hQc i).measurableSet, fun h => hi ?_, (hQ1 i).ne⟩
  exact measure_union_null h hP0

theorem eq_smul_of_left_inv (P : Subgroup G) (hPm : MeasurableSet (P : Set G)) (ρ ρ₀ : Measure G)
    [SigmaFinite ρ] [SigmaFinite ρ₀] (h0 : ρ (P : Set G)ᶜ = 0) (h0' : ρ₀ (P : Set G)ᶜ = 0)
    (hi : ∀ s ∈ P, ρ.map (fun g => s * g) = ρ) (hi' : ∀ s ∈ P, ρ₀.map (fun g => s * g) = ρ₀)
    (T : Set G) (hT : MeasurableSet T) (hT0 : ρ₀ T ≠ 0) (hT1 : ρ₀ T ≠ ⊤) :
    ∃ c : ENNReal, ρ = c • ρ₀ := by
  have hemb : MeasurableEmbedding (Subtype.val : P → G) := MeasurableEmbedding.subtype_coe hPm
  haveI : MeasurableMul₂ P := ⟨Measurable.subtype_mk
    ((hemb.measurable.comp measurable_fst).mul (hemb.measurable.comp measurable_snd))⟩
  haveI : MeasurableInv P := ⟨Measurable.subtype_mk hemb.measurable.inv⟩
  have hmap : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (τ.comap Subtype.val).map (Subtype.val : P → G) = τ := by
    intro τ h
    rw [hemb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem h
  have hinv : ∀ τ : Measure G, τ (P : Set G)ᶜ = 0 → (∀ s ∈ P, τ.map (fun g => s * g) = τ) →
      (τ.comap (Subtype.val : P → G)).IsMulLeftInvariant := by
    intro τ h hτ
    refine ⟨fun s => ?_⟩
    rw [← hemb.comap_map ((τ.comap Subtype.val).map (fun g => s * g)),
      Measure.map_map hemb.measurable (measurable_const_mul s)]
    have : (Subtype.val : P → G) ∘ (fun g => s * g) = (fun g => (s : G) * g) ∘ Subtype.val := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hemb.measurable, hmap τ h, hτ s s.2]
  haveI := hinv ρ h0 hi
  haveI := hinv ρ₀ h0' hi'
  haveI : SigmaFinite (ρ.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ h0]; infer_instance)
  haveI : SigmaFinite (ρ₀.comap (Subtype.val : P → G)) :=
    SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap ρ₀ h0']; infer_instance)
  have hT' : ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) = ρ₀ T := by
    rw [← hmap ρ₀ h0', Measure.map_apply hemb.measurable hT, hmap ρ₀ h0']
  set c : ENNReal := ρ.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) /
    ρ₀.comap (Subtype.val : P → G) (Subtype.val ⁻¹' T) with hc
  have key : ρ.comap (Subtype.val : P → G) = c • ρ₀.comap (Subtype.val : P → G) :=
    measure_eq_div_smul (ρ.comap (Subtype.val : P → G)) (ρ₀.comap (Subtype.val : P → G))
      (s := Subtype.val ⁻¹' T) (by rw [hT']; exact hT0) (by rw [hT']; exact hT1)
  refine ⟨c, ?_⟩
  conv_lhs => rw [← hmap ρ h0, key]
  rw [Measure.map_smul, hmap ρ₀ h0']

end General

end GlobalTheory.ParabModulus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceCoverProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeProductCover

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem lev_of_isConjPl (D : D7) {P P' : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.BasicNotions.IsConjPl D.host P P') :
    Formalism.IndefR.Lev.IsConjPl P P' := fun c hc =>
  ⟨RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) c,
    (h c _ rfl).1 hc, by
      show D.host.conj (c : D.host.E) = star (c : D.host.E)
      rw [star_eq_conj]⟩

theorem place_cover_prod : ∀ (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg),
    (∀ kv, ((plg kv : ↥Pg) : Formalism.L2.DIV.Pl D.host.E) = D.naut.plGw kv.1 kv.2) →
    ∀ PP : Formalism.L2.DIV.Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∈ Pg ∨ ∃ PP' ∈ Pg, IsConjPl PP' PP := by
  intro D Pg plg hplg PP hPP
  have hmul : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← Nat.cast_mul]; exact hPP
  have hk : ∃ k : Fin 2, PP ∈ placesOver D.host.E (D.host.g k) := by
    rcases PP.isPrime.mem_or_mem hmul with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k PP hk
  · left
    rw [hv, ← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  · right
    refine ⟨(plg ⟨k, v⟩ : Formalism.L2.DIV.Pl D.host.E), (plg ⟨k, v⟩).2, ?_⟩
    rw [hplg ⟨k, v⟩]
    exact lev_of_isConjPl D hv

end GlobalTheory.TypeProductCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowerBasisCoordsIsTorusHermitianIsometry
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

theorem trace_mul_star_eq_sum (z z' : Fld P) :
    ∑ i, ∑ j, σ ((powB P).repr z' i) * gramOne P i j * (powB P).repr z j =
      Algebra.trace E (Fld P) (z * star' P z') := by
  have hs : star' P z' = ∑ i, σ ((powB P).repr z' i) • star' P (powB P i) := by
    conv_lhs => rw [← (powB P).sum_repr z']
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.smul_def, map_mul, star'_algebraMap, ← Algebra.smul_def]
  rw [hs, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (powB P).sum_repr z]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, smul_eq_mul, gramOne, Matrix.of_apply]
  ring

theorem isIsom_coordEquiv : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k],
    IsIsom P k (GlobalTheory.TrUnitLat.gramOne P) 1 (GlobalTheory.TrUnitLat.coordEquiv P k) := by
  intro F E _ _ _ σ r P k _ _ y y'
  simp only [Formalism.UG.hform, hx, one_mul, coordEquiv_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
    simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
    | tmul a' z' =>
      have e1 : ∀ e : E, sigR k σ (a' ⊗ₜ[F] e) = a' ⊗ₜ[F] σ e := fun e => rfl
      have e2 : sigR k (star' P) (a' ⊗ₜ[F] z') = a' ⊗ₜ[F] star' P z' := rfl
      have e3 : ∀ i j, JR k (gramOne P) i j = (1 : k) ⊗ₜ[F] gramOne P i j := fun i j => rfl
      have e4 : ∀ (b : k) (w : Fld P), trBase P k (b ⊗ₜ[F] w) = b ⊗ₜ[F] Algebra.trace E (Fld P) w := fun b w => rfl
      simp only [coordF_tmul, e1, e2, e3, Algebra.TensorProduct.tmul_mul_tmul, e4, mul_one, ← TensorProduct.tmul_sum,
        trace_mul_star_eq_sum]
      rw [mul_comm a' a]

end GlobalTheory.TrUnitLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarHypotheses_of_topRows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → Given R.toRealDat F.lv2 := by
  first | exact @GlobalTheory.GivenOfTop.given_of_top | exact GlobalTheory.GivenOfTop.given_of_top | (intros; apply GlobalTheory.GivenOfTop.given_of_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitHalfResidueReductionFunctionEqFrameLocalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHalf_residueReduction_function_eq_frameLocal : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsIdemOf φ e → IsProjAt φ PP → IsRedMap φ PP r →
    ∀ (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (ω : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ),
      onHalf φ S T (frCo φ βS) (frCo φ βT) e (viaRed r ω) = locFn S T βS βT e PP ω := by
  first | exact @GlobalTheory.StepVec.onHalf_viaRed_eq_locFn | exact GlobalTheory.StepVec.onHalf_viaRed_eq_locFn | (intros; apply GlobalTheory.StepVec.onHalf_viaRed_eq_locFn <;> assumption)
end

