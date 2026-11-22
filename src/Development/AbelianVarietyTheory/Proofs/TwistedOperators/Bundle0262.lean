import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransferOfFundamentalDomains
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvalNormTransfer

theorem castGA_mem_GFset {I I' : AutInst} (h : I = I') (x : I.GA) :
    castGA h x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst h; exact Iff.rfl

theorem iotaX_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ (iotaX X h).toMulEquiv g ∈ X.B.I.GFset := by
  rw [Formalism.IndefR.RationalEmbedding.iota_rat D g]
  exact (castGA_mem_GFset h.symm _).symm

theorem borel_inst {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : BorelSpace X.B.I.GA := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  infer_instance

theorem exists_map_eq_smul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (ν : Measure (GA D (D.sp.Y 0))) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      Measure.map (iotaX X h).toMulEquiv.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • ν := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ga_facts D (D.sp.Y 0)
  haveI := X.B.haar
  haveI := X.B.sf
  haveI : BorelSpace X.B.I.GA := inferInstance
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  set μ' := Measure.map (iotaX X h).toMulEquiv.symm (X.B.I.muA X.B.μf) with hμ'
  haveI hH : μ'.IsHaarMeasure :=
    (iotaX X h).toMulEquiv.symm.isHaarMeasure_map _ (iotaX X h).symm.continuous (iotaX X h).continuous
  refine ⟨(Measure.haarScalarFactor μ' ν : ℝ), ?_, ?_⟩
  · exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ' ν
  · rw [ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def]
    exact Measure.isMulLeftInvariant_eq_smul μ' ν

theorem evalTranslate_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ t ∈ GfC (Yc D 0), ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ EP R F, MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X) ∧ ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM t ht
  haveI hνH : R.ν0.IsHaarMeasure := hM.ν0.1.1
  obtain ⟨c, hc, hmap⟩ := @exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hM.ν0.2 (iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hI := GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel R hM
  have hS' : S ∈ R.EEat (R.levR F true) := hS
  have hMult : S ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) := hS'.1
  have hcl := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := _) (χ := _) hMult v₀
  have hip := hI.2.2 _ S hS' S hS'
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : MemLp (S v₀) 2 (R.ν0.restrict R.fd0) := by
    refine (memLp_two_iff_integrable_sq_norm hcl.1.measurable.aestronglyMeasurable).2
      (((hip v₀ v₀).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) hcl.1 hcl.2 hL2
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq ⟨_, hip⟩ hv).symm), ?_⟩
  intro h0
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 (hI.2.1 _ hS')
  have hx : inner ℂ x x = ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (R.HE.e x) := hM.HE.2.2 x x
  have hre : ‖x‖ ^ 2 = (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (R.HE.e x)).re := by
    rw [← hx]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  have h00 : ‖x‖ ^ 2 = 0 := hre.trans h0
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h00
  rw [h00]
  exact map_zero R.HE.e

end GlobalTheory.EvalNormTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UjMatScalarMul
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ScalarTwist

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem ujMat_scalarMul {n : ℕ} (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    ujMat ε (scalarMul ε (z, g)) = (z : ℂ) • suMat ε g := by
  show umat (GlobalTheory.SqIntSU.unitScalar ε z) * umat (g : UJ ε) = _
  rw [GlobalTheory.SqIntSU.umat_unitScalar, Matrix.smul_mul, Matrix.one_mul]
  rfl

theorem scalar_twist : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure], ∃ c : NNReal, c ≠ 0 ∧ (letI := GlobalTheory.SqIntSU.circleBorelMS; μ = c • Measure.map (scalarMul ε) (circleHaar.prod μ')) ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π') (h : IsURepOn (UJset ε) π), Ext ε m π' π → ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f → repOp (ujRep h) μ f = ((c : ℝ) : ℂ) • repOp (suRep h') μ' fun g : SUJ ε => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar := by
  intro n hn ε μ _ μ' _
  have hn0 : 0 < n := hn
  haveI : SFinite μ' := inferInstance
  haveI : (circleHaar.prod μ').IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  haveI hν : (Measure.map (scalarMul ε) (circleHaar.prod μ')).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ (scalarMul ε) hsc (GlobalTheory.SqIntSU.scalarMul_surjective ε hn0)
      (GlobalTheory.SqIntSU.scalarMul_proper ε)
  set ν := Measure.map (scalarMul ε) (circleHaar.prod μ') with hνdef
  have hmu : μ = μ.haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  have hc0 : μ.haarScalarFactor ν ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  refine ⟨μ.haarScalarFactor ν, hc0, hmu, ?_⟩
  intro V _ _ _ m π' π h' h hE f hf hfc
  set c := μ.haarScalarFactor ν
  have hUc : Continuous (ujMat ε) := Units.continuous_val.comp continuous_subtype_val
  have hU : IsUnitaryRep (ujRep h) := GlobalTheory.Orb.isUnitaryRep_repVia h (fun g => g.2) hUc
  have hpt : ∀ (z : Circle) (g : SUJ ε), ujRep h (scalarMul ε (z, g)) = (z : ℂ) ^ m • suRep h' g := by
    intro z g
    show π (ujMat ε (scalarMul ε (z, g))) = (z : ℂ) ^ m • π' (suMat ε g)
    rw [ujMat_scalarMul]
    exact hE z (Circle.norm_coe z) _ (suMat_mem ε g)
  set fm : SUJ ε → ℂ := fun g => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar with hfm
  have hR := hU.isRepOp (μ := μ) hf hfc
  have key : ∀ v, Integrable (fun g => fm g • suRep h' g v) μ' ∧
      ((c : ℂ)⁻¹ • repOp (ujRep h) μ f) v = ∫ g, fm g • suRep h' g v ∂μ' := by
    intro v
    set F : UJ ε → V := fun g => f g • ujRep h g v with hF
    have hFc : Continuous F := hf.smul (hU.continuous_apply v)
    have hFi : Integrable F ν := hFc.integrable_of_hasCompactSupport hfc.smul_right
    have hGi : Integrable (F ∘ scalarMul ε) (circleHaar.prod μ') :=
      (integrable_map_measure hFi.aestronglyMeasurable hsc.aemeasurable).1 hFi
    have hin : ∀ g : SUJ ε, ∫ z, (F ∘ scalarMul ε) (z, g) ∂circleHaar = fm g • suRep h' g v := by
      intro g
      have : ∀ z : Circle, (F ∘ scalarMul ε) (z, g) = (f (scalarMul ε (z, g)) * (z : ℂ) ^ m) • suRep h' g v := by
        intro z
        simp only [Function.comp, hF, hpt, ContinuousLinearMap.smul_apply, smul_smul]
      simp only [this]
      exact integral_smul_const _ _
    refine ⟨?_, ?_⟩
    · have := hGi.integral_prod_right
      simpa only [hin] using this
    · rw [ContinuousLinearMap.smul_apply, (hR v).2]
      conv_lhs => rw [hmu]
      rw [integral_smul_nnreal_measure, hνdef, integral_map hsc.aemeasurable
        (hFc.aestronglyMeasurable),
        show ∫ x, F (scalarMul ε x) ∂(circleHaar.prod μ') = ∫ g, ∫ z, (F ∘ scalarMul ε) (z, g) ∂circleHaar ∂μ' from
          integral_prod_symm _ hGi]
      simp only [hin]
      have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      rw [NNReal.smul_def, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ this, one_smul]
  have hT : IsRepOp (suRep h') μ' fm ((c : ℂ)⁻¹ • repOp (ujRep h) μ f) := fun v => ⟨(key v).1, (key v).2⟩
  rw [hT.repOp_eq, smul_smul]
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  simp [this]

end GlobalTheory.ScalarTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentIntegralsPureTensorVanishOfLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TestConstTerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

open Classical in

theorem tensor_eq_mul_update {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ} (hf : IsFinFamily σ J L ff)
    (v : HeightOneSpectrum (𝓞 F)) (g : GAd σ J) :
    tensor σ J fa ff g = ff v (proj σ J v g) * tensor σ J fa (Function.update ff v fun _ => 1) g := by
  have h1 : (Function.mulSupport fun u => ff u (proj σ J u g)).Finite := by
    simpa only [projFinLoc_projFin] using hf.finite_mulSupport (projFin σ J g)
  have h2 : (Function.mulSupport fun u => (Function.update ff v fun _ => 1) u (proj σ J u g)).Finite :=
    h1.subset fun u hu => by
      by_cases e : u = v
      · subst e; simp at hu
      · simpa [Function.update_of_ne e] using hu
  simp only [tensor]
  rw [← mul_finprod_cond_ne v h1, ← mul_finprod_cond_ne v h2]
  simp only [Function.update_self, one_mul]
  have : (∏ᶠ (i) (_ : i ≠ v), (Function.update ff v fun _ => 1) i (proj σ J i g)) =
      ∏ᶠ (i) (_ : i ≠ v), ff i (proj σ J i g) :=
    finprod_congr fun i => finprod_congr fun hi => by rw [Function.update_of_ne hi]
  rw [this]; ring

open Classical in

theorem tensor_update_mul_emb (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a b : GAd σ J) (h : GLoc σ J v) :
    tensor σ J fa (Function.update ff v fun _ => 1) (a * emb σ J v h * b) =
      tensor σ J fa (Function.update ff v fun _ => 1) (a * b) := by
  simp only [tensor]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    simp only [map_mul, projArch_emb, mul_one]
  · refine finprod_congr fun u => ?_
    by_cases e : u = v
    · subst e; simp only [Function.update_self]
    · simp only [map_mul, proj_emb_ne σ J e, mul_one]

end GlobalTheory.TestConstTerm

namespace GlobalTheory.TestConstTerm

variable {D : D7} {V : HSp D} (𝔉 : IsoFlag V) (v : HeightOneSpectrum (𝓞 D.host.F))

def locIn : Subgroup (NA 𝔉) := (emb D.sp.cm.sig V.gram v).range.subgroupOf (NA 𝔉)

theorem isClosed_locIn : IsClosed (locIn 𝔉 v : Set (NA 𝔉)) := by
  have : (locIn 𝔉 v : Set (NA 𝔉)) = Subtype.val ⁻¹' Set.range (emb D.sp.cm.sig V.gram v) := by
    ext u; simp [locIn, Subgroup.mem_subgroupOf]
  rw [this]
  exact (isClosedEmbedding_emb D.sp.cm.sig V.gram v).isClosed_range.preimage continuous_subtype_val

theorem emb_proj_of_mem_locIn {u : NA 𝔉} (hu : u ∈ locIn 𝔉 v) :
    emb D.sp.cm.sig V.gram v (proj D.sp.cm.sig V.gram v u) = u := by
  obtain ⟨h, hh⟩ := Subgroup.mem_subgroupOf.1 hu
  rw [← hh, proj_emb_self]

def locInEquiv : locIn 𝔉 v ≃ₜ* NLoc 𝔉 v where
  toFun u := ⟨proj D.sp.cm.sig V.gram v u.1.1, IsoFlag.mapH_mem_unip _ u.1.2⟩
  invFun h := ⟨⟨emb D.sp.cm.sig V.gram v h, IsoFlag.emb_mem_unip.2 h.2⟩, Subgroup.mem_subgroupOf.2 ⟨h, rfl⟩⟩
  left_inv u := Subtype.ext (Subtype.ext (emb_proj_of_mem_locIn 𝔉 v u.2))
  right_inv h := Subtype.ext (proj_emb_self D.sp.cm.sig V.gram v (h : GLoc D.sp.cm.sig V.gram v))
  map_mul' a b := Subtype.ext (map_mul (proj D.sp.cm.sig V.gram v) _ _)
  continuous_toFun := ((continuous_proj D.sp.cm.sig V.gram v).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (((continuous_emb D.sp.cm.sig V.gram v).comp continuous_subtype_val).subtype_mk _).subtype_mk _

end GlobalTheory.TestConstTerm

namespace GlobalTheory.TestConstTerm

open Classical in

theorem unipIntegralsVanish_tensor : ∀ (D : D7) (V : HSp D) (𝔉 : IsoFlag V) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ)
    (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) →
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    (∀ (ν : Measure (NLoc 𝔉 v)) [ν.IsHaarMeasure] (x y : GLoc D.sp.cm.sig V.gram v),
      ∫ n : NLoc 𝔉 v, ff v (x * n * y) ∂ν = 0) →
    UnipIntegralsVanish 𝔉 (tensor D.sp.cm.sig V.gram fa ff) := by
  intro D V 𝔉 fa ff ha hf v hv ν _ x y
  set f := tensor D.sp.cm.sig V.gram fa ff with hfdef
  have hcc := continuous_of_mem_ccAd (tensor_mem_ccAd ha hf)
  let φ : GAd D.sp.cm.sig V.gram ≃ₜ GAd D.sp.cm.sig V.gram := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight y)
  have hcont : Continuous fun n : NA 𝔉 => f (x * n * y) :=
    hcc.1.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  have hsupp : HasCompactSupport fun n : NA 𝔉 => f (x * n * y) :=
    (hcc.2.comp_homeomorph φ).comp_isClosedEmbedding
      (IsoFlag.isClosed_unip 𝔉 D.sp.cm _).isClosedEmbedding_subtypeVal
  refine ⟨hcont.integrable_of_hasCompactSupport hsupp, ?_⟩
  haveI : LocallyCompactSpace (locIn 𝔉 v) := (isClosed_locIn 𝔉 v).locallyCompactSpace
  have key : ∀ g : NA 𝔉, ∫ u : locIn 𝔉 v, f (x * ((u : NA 𝔉) * g : NA 𝔉) * y) ∂(Measure.haar) = 0 := by
    intro g
    have e1 : ∀ u : locIn 𝔉 v, f (x * ((u : NA 𝔉) * g : NA 𝔉) * y) =
        ff v (proj D.sp.cm.sig V.gram v x * (locInEquiv 𝔉 v u : GLoc D.sp.cm.sig V.gram v) *
          proj D.sp.cm.sig V.gram v ((g : GAd D.sp.cm.sig V.gram) * y)) *
        tensor D.sp.cm.sig V.gram fa (Function.update ff v fun _ => 1) (x * ((g : GAd D.sp.cm.sig V.gram) * y)) := by
      intro u
      rw [hfdef, tensor_eq_mul_update hf v]
      have hu := emb_proj_of_mem_locIn 𝔉 v u.2
      congr 1
      · simp only [Subgroup.coe_mul, map_mul, mul_assoc]; rfl
      · rw [Subgroup.coe_mul, ← hu, show ∀ a b c d : GAd D.sp.cm.sig V.gram, a * (b * c) * d = a * b * (c * d)
          from fun a b c d => by group, tensor_update_mul_emb]
    simp_rw [e1]
    rw [integral_mul_const]
    have hH : (Measure.map (locInEquiv 𝔉 v) (Measure.haar : Measure (locIn 𝔉 v))).IsHaarMeasure :=
      ContinuousMulEquiv.isHaarMeasure_map _ _
    have := @hv (Measure.map (locInEquiv 𝔉 v) (Measure.haar : Measure (locIn 𝔉 v))) hH (proj D.sp.cm.sig V.gram v x) (proj D.sp.cm.sig V.gram v ((g : GAd D.sp.cm.sig V.gram) * y))
    rw [show Measure.map (locInEquiv 𝔉 v) (Measure.haar : Measure (locIn 𝔉 v)) =
      Measure.map ((locInEquiv 𝔉 v).toHomeomorph.toMeasurableEquiv) Measure.haar from rfl,
      integral_map_equiv] at this
    refine (congrArg (· * _) ?_).trans (zero_mul _)
    exact this
  have := GlobalTheory.T.integral_mul_eq_zero_of_coset_integral_eq_zero_alt (NA 𝔉) (locIn 𝔉 v) (isClosed_locIn 𝔉 v) Measure.haar ν (fun n => f (x * n * y)) (fun _ => 1)
    hcont hsupp (locallyIntegrable_const 1) (fun _ _ => Filter.EventuallyEq.rfl) key
  simpa using this

end GlobalTheory.TestConstTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightRealFrameElementLeHsPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameHeight

def EntryBd {n : ℕ} (f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : ℝ, ∀ g i j, ‖f g i j‖ ≤ c * (1 + Formalism.REAL.hs g)

variable {n : ℕ} {f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}

theorem hs_nonneg (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs; positivity

theorem entryBd_id : EntryBd (fun g : Matrix (Fin n) (Fin n) ℂ => g) := by
  refine ⟨1, fun g i j => ?_⟩
  have h1 : ‖g i j‖ ^ 2 ≤ Formalism.REAL.hs g := by
    unfold Formalism.REAL.hs
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  nlinarith [sq_nonneg (‖g i j‖ - 1), hs_nonneg g]

theorem EntryBd.conjTranspose (h : EntryBd f) : EntryBd fun g => (f g)ᴴ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g i j => by simpa [conjTranspose_apply] using hc g j i⟩

theorem EntryBd.const_mul (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => P * f g := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(∑ i, ∑ k, ‖P i k‖) * |c|, fun g i j => ?_⟩
  have h0 := hs_nonneg g
  show ‖(P * f g) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ k, ‖P i k‖ * (|c| * (1 + Formalism.REAL.hs g)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((hc g k j).trans
          (mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith))) (norm_nonneg _)
    _ = (∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖)
          (fun _ _ => by positivity) (Finset.mem_univ i)) (by positivity)
    _ = _ := by ring

theorem EntryBd.mul_const (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => f g * P := by
  simpa using (h.conjTranspose.const_mul Pᴴ).conjTranspose

theorem frame_mem {D : D7} {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.MainNotions.S.UJset (A.ε τ)) :
    (A.fr τ)⁻¹ * k * A.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (A.ε τ) * k = Formalism.REAL.Jm (A.ε τ) := hk
  have h3 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← A.fr_gram τ]
  calc _ = (A.fr τ)ᴴ * (kᴴ * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * k) *
        A.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

theorem height_elt_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau), ∃ (C : ℝ) (m : ℕ), ∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), GlobalTheory.Grow.height V (A.elt θ τ g) ≤ C * (1 + Formalism.REAL.hs g) ^ m := by
  intro D θ hθ V A τ
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow V hθ
  have b1 := (entryBd_id.const_mul (A.fr τ)⁻¹).mul_const (A.fr τ)
  obtain ⟨c2, h2⟩ := (b1.conjTranspose.const_mul (gramAt D V τ)⁻¹).mul_const (gramAt D V τ)
  obtain ⟨c1, h1⟩ := b1
  refine ⟨(∑ _ρ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (|c1| + |c2| + 2)) ^ d, d, fun g hg => ?_⟩
  have hu := frame_mem A τ hg
  have s1 := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
  have s2 := GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hu s1
  have h0 := hs_nonneg g
  refine (hd _ s1.1).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by unfold normInf; positivity) ?_ d
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have a1 := mul_nonneg (abs_nonneg c1) h0
  have a2 := mul_nonneg (abs_nonneg c2) h0
  by_cases e : ρ = τ
  · subst e
    rw [s1.2.1, s2.2.1]
    have e1 := (h1 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c1) (by linarith))
    have e2 := (h2 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c2) (by linarith))
    nlinarith
  · rw [s1.2.2 ρ e, s2.2.2 ρ e]
    have : ‖(1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    nlinarith [abs_nonneg c1, abs_nonneg c2]

end GlobalTheory.FrameHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedTraceConjFrameToRealLieLoweringOperator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

theorem star_trace_mat_of_unitLie {D : D7} {S T : HSp D} (C : Ctx S T) {Z : Frame C.X.Ψ T.rank}
    (hZ : Z ∈ GlobalTheory.HolRead.unitLie C.X) (σ : C.X.Ψ) : star (trace (mat Z σ)) = -trace (mat Z σ) := by
  set Sg : Matrix (Fin T.rank) (Fin T.rank) ℂ := diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ) with hSg
  have hSS : Sg * Sg = 1 := by
    rw [hSg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> norm_num
  have h := hZ σ
  have h2 : Sg * ((mat Z σ)ᴴ * Sg + Sg * mat Z σ) = 0 := by rw [h, Matrix.mul_zero]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hSS, Matrix.one_mul] at h2
  have h3 := congrArg trace h2
  rw [trace_add, trace_zero, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hSS, Matrix.mul_one,
    trace_conjTranspose] at h3
  exact eq_neg_of_add_eq_zero_left h3

theorem trace_mat_eq_zero_of_add_I {D : D7} {S T : HSp D} (C : Ctx S T) (ρ : D.what₂.Tau) (c d : Fin T.rank) (hcd : c < d)
    {Z Z' : Frame C.X.Ψ T.rank} (hZ : Z ∈ GlobalTheory.HolRead.unitLie C.X) (hZ' : Z' ∈ GlobalTheory.HolRead.unitLie C.X)
    (h : Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) (σ : C.X.Ψ) :
    trace (mat Z σ) = 0 ∧ trace (mat Z' σ) = 0 := by
  have e : mat Z σ + I • mat Z' σ = mat (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) σ := by rw [← h]; rfl
  have e0 : trace (mat Z σ) + I * trace (mat Z' σ) = 0 := by
    have := congrArg trace e
    rw [trace_add, trace_smul, smul_eq_mul, GlobalTheory.HolRead.AdExt.mat_unitFr] at this
    rw [this]
    split_ifs
    · simp [Matrix.trace, Matrix.single, hcd.ne']
    · simp
  have a := star_trace_mat_of_unitLie C hZ σ
  have b := star_trace_mat_of_unitLie C hZ' σ
  have e1 := congrArg star e0
  rw [star_add, star_mul', a, b, star_zero, Complex.star_def, Complex.conj_I] at e1
  have hy : trace (mat Z' σ) = 0 := by
    have : (2 * I) * trace (mat Z' σ) = 0 := by linear_combination e0 + e1
    rcases mul_eq_zero.1 this with h2 | h2
    · exfalso; simp at h2
    · exact h2
  refine ⟨?_, hy⟩
  rw [hy, mul_zero, add_zero] at e0
  exact e0

theorem trLin_toLieC_of_trace {D : D7} {S T : HSp D} (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas)
    (hB : C.IsB B) (m : D.what₂.Tau → ℤ) (W : Frame C.X.Ψ T.rank) (hW : ∀ σ, trace (mat W σ) = 0) :
    trLin T m (toLieC C R B W) = 0 := by
  change ∑ ρ, (m ρ : ℂ) * trace ((toLieC C R B W) ρ).1 = 0
  refine Finset.sum_eq_zero fun ρ _ => ?_
  change (m ρ : ℂ) * trace ((GlobalTheory.HolRead.AdExt.toLie R B (fun ρ => C.m.e ρ) (conjL W)) ρ).1 = 0
  rw [GlobalTheory.HolRead.AdExt.toLie_val, mat_conjL]
  have hN : trace ((mat W (C.m.e ρ)).map (starRingEnd ℂ)) = 0 := by
    have : trace ((mat W (C.m.e ρ)).map (starRingEnd ℂ)) = starRingEnd ℂ (trace (mat W (C.m.e ρ))) := by
      simp [Matrix.trace, map_sum]
    rw [this, hW, map_zero]
  set N := (mat W (C.m.e ρ)).map (starRingEnd ℂ)
  have hM : trace (B ρ * N * (B ρ)⁻¹) = 0 := by
    rw [trace_mul_cycle, nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.one_mul, hN]
  have hC : trace (conjAt T ρ (B ρ * N * (B ρ)⁻¹)) = 0 := by
    unfold conjAt
    rw [trace_neg, trace_mul_cycle, mul_nonsing_inv _ (R.1 ρ).2, Matrix.one_mul, trace_conjTranspose, hM, star_zero,
      neg_zero]
  rw [trace_smul, trace_add, hM, hC]
  simp

theorem trLin_toLieC_unitFr : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (m : D.what₂.Tau → ℤ) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  intro D S T C R B hB m ρ c d hcd Z Z' hZ hZ' h
  rw [trLin_toLieC_of_trace C R B hB m Z (fun σ => (trace_mat_eq_zero_of_add_I C ρ c d hcd hZ hZ' h σ).1),
    trLin_toLieC_of_trace C R B hB m Z' (fun σ => (trace_mat_eq_zero_of_add_I C ρ c d hcd hZ hZ' h σ).2), mul_zero, add_zero]

end GlobalTheory.AdSpan.ConjHol
end
end

