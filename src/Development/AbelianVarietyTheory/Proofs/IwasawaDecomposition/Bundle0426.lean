import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0424
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0050
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAdelicFormLevelTypeEqColumnLevel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicFormFunctionValuesMemCoefficientLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFormFunction_values_mem_coefficientLattice : ∀ (D : D7) (V : HSp D), Seed.FrmC.StdLat V → ∀ (c : CoefA V) (S : CSD D.what₂.LL) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ) (pres : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL c.coef.ρ J χ) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair del, Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefTie V c.coef pres lam c0 pair (nabAtr (labLL D) lam) del → (∀ k ∈ J, ∀ h, Bridge.hLat V (h * k) = Bridge.hLat V h) → (∀ k : J, ∃ z : 𝓞 D.what₂.LL, D.what₂.embLL (z : D.what₂.LL) = (χ k : ℂ)) → ∀ f : S.Forms, (∀ h, pres.ext f.1 h ∈ Set.range c0) ∧ ((∀ a, f.1 a ∈ S.Nab a) → ∀ h, ∃ v ∈ nabAtr (labLL D) lam (Bridge.hLat V h), pres.ext f.1 h = c0 v) := by
  first | exact @GlobalTheory.MtIn.ext_vals | exact GlobalTheory.MtIn.ext_vals | (intros; apply GlobalTheory.MtIn.ext_vals <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiser
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnifMap

theorem unif_to_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  intro F E _ _ _ _ v w i hi ϖ hϖ
  have hle := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv F E v w i hi
  have key : ∀ x : WithZero (Multiplicative ℤ), x ≠ 0 → x < 1 → x ≤ WithZero.exp (-1 : ℤ) := by
    intro x hx h1
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]; omega
  have hlt : ∀ y, Valued.v (i y) < 1 ↔ Valued.v y < 1 := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have hiy : i y ≠ 0 := by simpa using hy
      have e1 := (Valued.v (R := w.adicCompletion E)).one_lt_val_iff (inv_ne_zero hiy)
      have e2 := (Valued.v (R := v.adicCompletion F)).one_lt_val_iff (inv_ne_zero hy)
      rw [inv_inv] at e1 e2
      rw [← e1, ← e2, ← not_le, ← not_le, ← map_inv₀ i, hle]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hiϖ0 : i ϖ ≠ 0 := by simpa using hϖ0
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hup : Valued.v (i ϖ) < 1 := (hlt ϖ).2 hϖ1
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  set z : w.adicCompletion E := (π : w.adicCompletion E)
  have hz : Valued.v z = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  set y := i.symm z
  have hy1 : Valued.v y < 1 := by
    rw [← hlt, RingEquiv.apply_symm_apply, hz, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy1
    have : z = 0 := by simpa [y] using h
    rw [this, map_zero] at hz; exact WithZero.exp_ne_zero hz.symm
  have hdiv : Valued.v (y / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ, div_le_one₀ (by simp)]
    exact key _ (by simpa using hy0) hy1
  have h2 := (hle _).2 hdiv
  rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply, hz] at h2
  have hlow : WithZero.exp (-1 : ℤ) ≤ Valued.v (i ϖ) := by
    rwa [div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hiϖ0))] at h2
  exact le_antisymm (key _ (by simpa using hiϖ0) hup) hlow

end GlobalTheory.UnifMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspParam_of_greenParametrisation : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam (ZMod g) (convC t ht ζ hζ) := by
  first | exact @GlobalTheory.GreenParam.cuspParam_of_green | exact GlobalTheory.GreenParam.cuspParam_of_green | (intros; apply GlobalTheory.GreenParam.cuspParam_of_green <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLargeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_definiteSpaces_standard_and_large : Top.Ev fun K => ∀ X : Stages, K.Over X.B.toPre → (∀ i, Formalism.IndefR.FWT.VStd X.toD7 i) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  first | exact @GlobalTheory.Mem.StdSize.vstd_size_ev | exact GlobalTheory.Mem.StdSize.vstd_size_ev | (intros; apply GlobalTheory.Mem.StdSize.vstd_size_ev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldContainsHeckeEigenvaluesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientField_contains_heckeEigenvalues : ∃ So : ∀ P : Pre, Top.Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ,
  (∀ P f F F₀ Ξ, ∀ z ∈ So P f F F₀ Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok →
    (∀ z ∈ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC) → ∀ a : I.ι,
      Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
        ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  first | exact @GlobalTheory.Mem.HFld.heckeFields | exact GlobalTheory.Mem.HFld.heckeFields | (intros; apply GlobalTheory.Mem.HFld.heckeFields <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodCharacterSetIdempotentCoeffCoefficientStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodCharacterSet_idempotent_coeff_coefficientField : ∀ (X : Stages) (px : PreX X.B.toPre) (eR : Gc X.B px ≃* G0g X.toD7.nd), ∃ Xg : Finset (Gc X.B px → X.B.LL), GoodSet X (px := px) eR Xg ∧ ∀ g, (idemOf Xg).coeff g ∈ X.B.Ks := by
  first | exact @GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks | exact GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks | (intros; apply GlobalTheory.Mem.R3.GoodSetExists.exists_goodSet_Ks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
section
noncomputable section

namespace GlobalTheory.DefLift.Gen

section Abstract

open Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Real

theorem quad_comm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} (h0 : ∀ x, om x x = 0)
    (hH : IsHeis (fun x y => om x y) ρ) {X : V → V} {κ : Type} [Fintype κ] {c : κ → ℂ} {p q : κ → V}
    (hQ : IsQuadOf (fun x y => om x y) X c p q) {f : B} (hf : Sm ρ f) (v : V) :
    quad ρ c p q (dH ρ v f) - dH ρ v (quad ρ c p q f) = dH ρ (X v) f := by
  have C := DCalc.dH_calculus V B om ρ h0 hH
  let d : V → Module.End ℂ (smS ρ) := fun u =>
    { toFun := fun g => ⟨dH ρ u g.1, (C g.1 g.2).1 u⟩
      map_add' := fun g g' => Subtype.ext (dH_add u g.2 g'.2)
      map_smul' := fun a g => Subtype.ext (dH_smul u a g.2) }
  have hd : ∀ u w, d u * d w = d w * d u + (2 * π * I * (om u w : ℂ)) • (1 : Module.End ℂ (smS ρ)) := by
    intro u w
    refine LinearMap.ext fun g => Subtype.ext ?_
    have := (C g.1 g.2).2.2.2.2 u w
    rw [sub_eq_iff_eq_add'] at this
    exact this
  have key : ∀ a b, d a * d b * d v - d v * (d a * d b) =
      (2 * π * I : ℂ) • ((om b v : ℂ) • d a + (om a v : ℂ) • d b) := by
    intro a b
    rw [mul_assoc, hd b v, mul_add, ← mul_assoc, hd a v, add_mul, mul_assoc]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  have hq : ∀ g : smS ρ, ((∑ i, c i • (d (p i) * d (q i))) g).1 = quad ρ c p q g.1 := by
    intro g
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    rfl
  have e : (∑ i, c i • (d (p i) * d (q i))) * d v - d v * (∑ i, c i • (d (p i) * d (q i))) =
      (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) v : ℂ) • d (p i) + (om (p i) v : ℂ) • d (q i)) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, key, smul_comm]
  have e1 := congrArg Subtype.val (LinearMap.congr_fun e ⟨f, hf⟩)
  rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply, Module.End.mul_apply, hq,
    LinearMap.smul_apply, Submodule.coe_smul, LinearMap.sum_apply _ (fun i => c i • (_ + _)), Submodule.coe_sum] at e1
  have e2 := hQ.apply_vec (fderiv ℝ (fun u => ρ u f) 0).toLinearMap v
  refine Eq.trans ?_ (e1.trans e2)
  rw [← hq ⟨f, hf⟩]
  rfl

theorem nOp_comm {ι : Type} [Fintype ι] [DecidableEq ι] {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (hX : Xᴴ * H + H * X = 0) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {ρ : (ι → ℂ) → B →L[ℂ] B}
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) {f : B} (hf : Sm ρ f) (v : ι → ℂ) :
    nOp ρ H X (dH ρ v f) - dH ρ v (nOp ρ H X f) = dH ρ (X *ᵥ v) f := by
  obtain ⟨κ, _, c, p, q, hQ, hn⟩ := Normal.normal_quad ι H X hH hd hX
  obtain ⟨om, hom⟩ := Ccr.exists_om H
  have hρ' : IsHeis (fun x y => om x y) ρ := by simpa only [hom] using hρ
  have hQ' : IsQuadOf (fun x y => om x y) (fun v => X *ᵥ v) c p q := by simpa only [hom] using hQ
  rw [← hn B ρ hρ f hf, ← hn B ρ hρ _ (DCalc.sm_dH hρ' hf v)]
  exact quad_comm (fun x => by rw [hom, Ccr.im_self hH]) hρ' hQ' hf v

theorem nOp_add_comm {ι : Type} [Fintype ι] [DecidableEq ι] {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (hX : Xᴴ * H + H * X = 0) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {ρ : (ι → ℂ) → B →L[ℂ] B}
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) (a : ℂ) {f : B} (hf : Sm ρ f) (hn : Sm ρ (nOp ρ H X f))
    (v : ι → ℂ) :
    nOp ρ H X (dH ρ v f) + a • dH ρ v f = dH ρ v (nOp ρ H X f + a • f) + dH ρ (X *ᵥ v) f := by
  have s2 : Sm ρ (a • f) := (smS _).smul_mem _ hf
  rw [← nOp_comm hH hd hX hρ hf, dH_add _ hn s2, dH_smul _ _ hf]
  abel

theorem blk_vecL {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (τ τ' : O)
    (u : Matrix (Fin m) (Fin n) ℂ) :
    blk (Pi.single τ X) (fun _ => 1) *ᵥ vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) =
      vecL (Pi.single τ' ((Pi.single τ X : O → Matrix (Fin m) (Fin m) ℂ) τ' * u) : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext ⟨⟨i, j⟩, t⟩
  have e := congrFun (congrFun (cpt_blk (Pi.single τ X) (fun _ => 1)
    (vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ)) t) i) j
  have e' : ∀ y : O → Matrix (Fin m) (Fin n) ℂ, cpt (vecL y) t = y t := fun y => rfl
  rw [e', Matrix.mul_one] at e
  refine e.trans ?_
  change _ = (Pi.single τ' ((Pi.single τ X : O → Matrix (Fin m) (Fin m) ℂ) τ' * u) : O → Matrix (Fin m) (Fin n) ℂ) t i j
  by_cases h : t = τ'
  · subst h
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, Matrix.mul_zero]

end Abstract

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Classical

variable {D : D7} {θ : InfFam D}

theorem hasDerivAt_comp (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (τ' : D.what₂.Tau) (i j : Fin V.rank) :
    HasDerivAt (fun t : ℝ => Datum.compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) i j)
      ((Pi.single τ X : D.what₂.Tau → _) τ' i j) 0 := by
  by_cases h : τ' = τ
  · subst h
    have e : ∀ t : ℝ, Datum.compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ' X t)) = NormedSpace.exp (t • X) :=
      fun t => (isAtTau_oneP hθ hX t).2.1
    have := hasDerivAt_exp_entry X 0 i j
    rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
    simpa only [e, Pi.single_eq_same] using this
  · have e : ∀ t : ℝ, Datum.compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) = 1 :=
      fun t => (isAtTau_oneP hθ hX t).2.2 τ' h
    simp only [e, Pi.single_eq_of_ne h]
    exact hasDerivAt_const _ _

theorem blk_lie {S T : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) :
    (blk (Pi.single τ X) fun _ => 1 : Matrix (Ix S T) (Ix S T) ℂ)ᴴ * HM S T +
      HM S T * blk (Pi.single τ X) (fun _ => 1) = 0 := by
  have h : Xᴴ * gramAt D T τ + gramAt D T τ * X = 0 := hX
  unfold HM
  rw [blk_conjTranspose, blk_mul, blk_mul]
  simp only [conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
  unfold RealWeil.blk
  rw [← blockDiagonal_add, ← blockDiagonal_zero]
  congr 1
  funext t
  rw [Pi.add_apply, ← add_kronecker]
  beta_reduce
  by_cases ht : t = τ
  · subst ht
    rw [Pi.single_eq_same, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, h, smul_zero, zero_kronecker]
    rfl
  · rw [Pi.single_eq_of_ne ht]
    simp

variable {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem coe_dH (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (τ : D.what₂.Tau) (y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ((dH (rhoV hψ σ S T) (vecL (Pi.single τ y : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)) F).1 : WO S T → ℂ) =
      Datum.dRho (heisO ψ S T) θ τ y F.1 := by
  funext w
  refine (ev_fderiv hψ F (sm_of_theta h hψ F hF) _ w).trans ?_
  have e : ∀ t : ℝ, iotaV σ S T (t • vecL (Pi.single τ y : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)) =
      lineAt θ τ y t := fun t => by
    rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ y t]
    rfl
  simp only [e]
  rfl

theorem dRho_zero (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (τ : D.what₂.Tau) : Datum.dRho (heisO ψ S T) θ τ 0 F.1 = 0 := by
  have e : vecL (Pi.single τ 0 : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) = 0 := by
    rw [Pi.single_zero]
    rfl
  have e' : dH (rhoV hψ σ S T) 0 F = 0 := map_zero _
  rw [← coe_dH h hψ F hF, e, e']
  rfl

theorem coe_add_smul (A F : BB ψ S T) (a : ℂ) :
    (A.1 : WO S T → ℂ) + a • (F.1 : WO S T → ℂ) = ((A + a • F).1 : WO S T → ℂ) := rfl

theorem coe_add_sub (A F : BB ψ S T) :
    ((A + F).1 : WO S T → ℂ) - (A.1 : WO S T → ℂ) = (F.1 : WO S T → ℂ) := add_sub_cancel_left (A.1 : WO S T → ℂ) F.1

theorem theta_dH (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (v : Ix S T → ℂ) : IsThetaFunO ψ S T (dH (rhoV hψ σ S T) v F).1 := by
  obtain ⟨F', hF', hd⟩ := exists_deriv h hψ F hF v
  have e : F' = dH (rhoV hψ σ S T) v F := QB_ext fun w => (hd w).unique
    (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (sm_of_theta h hψ F hF)))
  exact e ▸ hF'

theorem exists_extension (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1))
    (Y : Matrix (Ix S T) (Ix S T) ℂ) (lam : ℂ) : ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ F : BB ψ S T,
      IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) Y F).1 ∧
        Gn F.1 = (nOp (rhoV hψ σ S T) (HM S T) Y F + lam • F).1 := by
  obtain ⟨x, d, -, hn⟩ := exists_isCCR_theta D θ σ h ψ hψ S T
  have hA := hn Y
  generalize (∑ k, ∑ l, Y k l • (x k * d l)) = A at hA
  obtain ⟨G, hG⟩ := LinearMap.exists_extend ((thetaSub ψ S T).subtype ∘ₗ A)
  refine ⟨G + lam • 1, fun F hF => ?_⟩
  have e := hA ⟨F.1, hF⟩ F rfl
  have e' : G F.1 = (A ⟨F.1, hF⟩).1 := LinearMap.congr_fun hG ⟨F.1, hF⟩
  refine ⟨e ▸ (A ⟨F.1, hF⟩).2, ?_⟩
  rw [← coe_add_smul, ← e, ← e']
  rfl

theorem comm_dRho (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) {τ : D.what₂.Tau}
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) (lam : ℂ) {Gn : Module.End ℂ (WO S T → ℂ)}
    (hG : ∀ F : BB ψ S T, IsThetaFunO ψ S T F.1 →
      IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) (blk (Pi.single τ X) fun _ => 1) F).1 ∧
        Gn F.1 = (nOp (rhoV hψ σ S T) (HM S T) (blk (Pi.single τ X) fun _ => 1) F + lam • F).1)
    (F : BB ψ S T) (hf : IsThetaFunO ψ S T F.1) : IsThetaFunO ψ S T (Gn F.1) ∧
      ∀ τ' (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Gn (Datum.dRho (heisO ψ S T) θ τ' u F.1) - Datum.dRho (heisO ψ S T) θ τ' u (Gn F.1) =
      ((dH (rhoV hψ σ S T) (vecL (Pi.single τ' ((Pi.single τ X : D.what₂.Tau → _) τ' * u) :
        D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)) F).1 : WO S T → ℂ) := by
  obtain ⟨h2, e⟩ := hG F hf
  have h1 := GlobalTheory.OrientedHeis.theta_add h2 (GlobalTheory.OrientedHeis.theta_smul lam hf)
  rw [coe_add_smul] at h1
  refine ⟨e ▸ h1, fun τ' u => ?_⟩
  rw [← coe_dH h hψ F hf, (hG _ (theta_dH h hψ F hf _)).2, e, ← coe_dH h hψ _ h1, ← blk_vecL,
    nOp_add_comm HM_herm HM_det (blk_lie (S := S) hX) (isHeis_rhoB h hψ) lam (sm_of_theta h hψ F hf)
      (sm_of_theta h hψ _ h2)]
  exact coe_add_sub _ _

theorem exists_generator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ τ, ∀ X ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Datum.dRho (heisO ψ S T) θ τ u f) - Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Datum.dRho (heisO ψ S T) θ τ (X * u) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Datum.dRho (heisO ψ S T) θ τ' u f) = Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ ∀ (p : GA D S × GA D T) (w : WO S T), HasDerivAt (fun t : ℝ => om (p * (1, oneP θ T τ X t)) f w) (om p (Gn f) w) 0 := by
  intro D ψ S T χS χT om hom θ hθ τ X hX
  have hψ := hom.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl⟩ := GlobalTheory.T.hasDerivAt_weilRep_realOneParam_adelicPoint D θ σ h ψ hψ S T om (GlobalTheory.Ker.isWeak_of_datum hom) hom.om_cont
    (fun t => (1, oneP θ T τ X t)) (continuous_const.prodMk (continuous_oneP hθ hX))
    (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨one_mem _, (isAtTau_oneP hθ hX t).1⟩) (blk (Pi.single τ X) fun _ => 1) (fun k l => by
      simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, RealWeil.blk, blockDiagonal_apply,
        kroneckerMap_apply]
      split_ifs
      · exact (hasDerivAt_comp hθ hX _ _ _).mul_const _
      · exact hasDerivAt_const _ _)
  obtain ⟨Gn, hG⟩ := exists_extension (S := S) (T := T) h hψ (blk (Pi.single τ X) fun _ => 1) lam
  refine ⟨Gn, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f := ⟨toB hψ f hf, coe_toB hψ f hf⟩
  obtain ⟨hth, hcomm⟩ := comm_dRho h hψ hX lam hG F hf
  refine ⟨hth, fun u => ?_, fun τ' hτ u => ?_, fun p w => ?_⟩
  · rw [hcomm, Pi.single_eq_same, coe_dH h hψ F hf]
  · rw [← sub_eq_zero, hcomm, Pi.single_eq_of_ne hτ, Matrix.zero_mul, coe_dH h hψ F hf]
    exact dRho_zero h hψ F hf τ'
  · rw [(hG F hf).2]
    exact hl F hf p w

end GlobalTheory.DefLift.Gen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankBaseRowsIsotypicEqGoodFormsIsotypicStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_baseRows_isotypic_eq_goodForms_isotypic : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → ∀ (i : Fin D.R.m) (π : D.what₂.FT), Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) = Module.finrank ℂ (principalLevelFrame.isotL R.toRealDat.θ (Y.PW i) (R.toRealDat.MW i (sg0 D A3.A)) (levS _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.toRealDat.βW i) (R.toRealDat.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  first | exact @GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL | exact GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL | (intros; apply GlobalTheory.Mem.R3.IsotMult.finrank_isotE_eq_isotL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaSupportedAtPlaceIdempotentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameTransport_eta_supported_at_placeIdempotent : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ → SuppAt e V α := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.eta_suppAt | exact GlobalTheory.Mem.R3.LiftBrg.eta_suppAt | (intros; apply GlobalTheory.Mem.R3.LiftBrg.eta_suppAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotent
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem GlobalTheory.SerCmp.eSerC_eq_eSerO : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : IsGenSys L.gen), t = L.teich → ∀ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht L.gen hζ), (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht L.gen hζ) τ (O.lab d τ)) → ∀ (r : ℕ) (f : (ZMod g)[X]), 1 ≤ r → GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  intro hG g _ L t ht hζ htL O hO r f hr
  have hcusp : ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x) :=
    fun d V hd hs hc => GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel g L t ht hζ htL d V _ hd ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc)
      (hO d V hd hs hc)
  have hB : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), CategoryTheory.Simple τ →
      (GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f ↔ Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f) := by
    intro τ hτ
    constructor
    · refine GlobalTheory.T.labelMap_label_of_classFunctionLabel g L O (fun d V P hd hs hc hP => ?_) (fun d χ hχ => ?_)
        (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g) (GlobalTheory.T.exists_blocks_of_cuspidal_character_list g) r τ f hτ
      · exact GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes hG g L d P (O.lab d V) _ hP (hcusp d V hd hs hc)
      · obtain ⟨V, hV, hVχ⟩ := hχ.2.1
        have hχV : (fun x => V.character x) = χ := funext hVχ
        have hd : 1 ≤ d := hχ.1
        exact ⟨V, hV, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hV).1 (hχV ▸ hχ), hVχ⟩
    · exact GlobalTheory.T.classFunctionLabel_of_labelMap_label g L O hcusp (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g) (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g) r τ f hτ
  unfold GlobalTheory.GLq.eSerC Formalism.L2.NT.eSerO
  rw [GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple]
  refine finsum_congr fun z => finsum_congr_Prop (propext ?_) fun _ => rfl
  constructor
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).1 hl⟩
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).2 hl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A, σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  first | exact @GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | exact GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | (intros; apply GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAdelicFormLevelTypeEqColumnLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAdelicForm_level_type_eq_columnLevel : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∃ hJ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J =
        (Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).map eG.toMonoidHom,
      ∀ (k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
        (hk : eG (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J),
        (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩)⁻¹ : ℂˣ) =
          Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
            (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
              ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) ∧
        ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) →
          (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩ = 1) := by
  first | exact @GlobalTheory.Mem.LevPres.lev_type_eq | exact GlobalTheory.Mem.LevPres.lev_type_eq | (intros; apply GlobalTheory.Mem.LevPres.lev_type_eq <;> assumption)
end

