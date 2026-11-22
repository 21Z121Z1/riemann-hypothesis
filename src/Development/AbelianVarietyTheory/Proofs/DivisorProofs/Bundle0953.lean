import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfRowTestOfScalar
section
noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.OneFormTest

theorem tw_span_top (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {I : Type} (v : I → E)
    (h : Submodule.span ℂ (Set.range v) = ⊤) : Submodule.span ℂ (Set.range fun i => Tw.mk s (v i)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : Tw.out x ∈ Submodule.span ℂ (Set.range v) := h ▸ Submodule.mem_top
  have key : ∀ y ∈ Submodule.span ℂ (Set.range v),
      Tw.mkL s E y ∈ Submodule.span ℂ (Set.range fun i => Tw.mk s (v i)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  exact key _ hx

theorem tw_map_surjective (s : Bool) {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E']
    [InnerProductSpace ℂ E'] {f : E →ₗ[ℂ] E'} (h : Function.Surjective f) : Function.Surjective (Tw.map s f) := h

theorem model_of_pres {H Γ : Type} [Group H] [Group Γ] {ι : Γ →* H} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (H → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) :
    (∀ x y, ⟪j x, j y⟫_ℂ = σ (S.csum x.1 y.1)) ∧ Function.Injective j ∧ Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [hM.2.2, hj, hj]
    exact h3 x y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h4 : P.extL x = 0 := by rw [← hj, hx, map_zero]
    rw [← S.basis.sum_repr x, map_sum] at h4
    simp only [map_smulₛₗ] at h4
    have h5 := Fintype.linearIndependent_iff.1 h1 _ h4
    refine S.basis.repr.injective (Finsupp.ext fun i => ?_)
    rw [(map_eq_zero _).1 (h5 i), map_zero, Finsupp.zero_apply]
  · apply Submodule.map_injective_of_injective hM.1
    rw [Submodule.map_top, hM.2.1, Submodule.map_span, ← Set.range_comp, show M.e ∘ j = P.extL from funext hj, h2]

theorem apply_gaOp {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) {H E : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (j : S.Forms →ₛₗ[σ] H) (Θ : H →ₗ[ℂ] E) (h : ∀ g x, Θ (j (r g x)) = ρ g (Θ (j x)))
    (Y : Finset (G → K)) (hY : ∀ y, ∑ g, σ ((idemOf Y).coeff g) • ρ g y = y) (x : S.Forms) :
    Θ (j (S.gaOp r (goodAt Y ⊥ 1) x)) = Θ (j x) := by
  rw [goodAt, level_idempotent_bot, mul_one, CSD.gaOp, LinearMap.sum_apply, map_sum, map_sum, ← hY (Θ (j x))]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, map_smulₛₗ, map_smul, h]

theorem surjective_of_scalar {H E : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup E] [Module ℂ E] (f : H →ₗ[ℂ] E)
    (g : E →ₗ[ℂ] H) {I : Type} (p : I → Submodule ℂ E) (hp : ⨆ c, p c = ⊤)
    (h : ∀ c, ∃ l : ℝ, 0 < l ∧ ∀ x ∈ p c, (f ∘ₗ g) x = (l : ℂ) • x) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hp, iSup_le_iff]
  intro c x hx
  obtain ⟨l, hl, h⟩ := h c
  refine ⟨(l : ℂ)⁻¹ • g x, ?_⟩
  have h1 : f (g x) = (l : ℂ) • x := h x hx
  rw [map_smul, h1, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hl.ne'), one_smul]

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem model_jX (hH : R.models_HX) (hj : R.models_jX) (t : T) :
    (∀ x y : (A.MtildeCSD t).Forms, ⟪R.jX t x, R.jX t y⟫_ℂ = D.what₂.embLL ((A.MtildeCSD t).csum x.1 y.1)) ∧
      Function.Injective (R.jX t) ∧ Submodule.span ℂ (Set.range (R.jX t)) = ⊤ :=
  model_of_pres (S := A.MtildeCSD t) (R.B.R t).pres (R.HX t) (hH t) (R.jX t) (hj t)

theorem formsTie (hH : R.models_HX) (hj : R.models_jX) : FormsTie (F := A.fam) (R.toCx F) where
  inner_eq t x y := ((congrArg (cj (twAt D.what₂.embLL A.v0)) ((model_jX R hH hj t).1 x y)).trans (R.emb0 _).symm :)
  inj t := (model_jX R hH hj t).2.1
  span t := tw_span_top (twAt D.what₂.embLL A.v0) (R.jX t) (model_jX R hH hj t).2.2

theorem sum_gE_eq (hE : R.models_HE) (hg : R.models_gE) (y : R.HE.H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  apply hE.1
  have h1 : R.HE.e y ∈ R.EEat R.triv := hE.2.1 ▸ ⟨y, rfl⟩
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) = R.HE.e y := sub_eq_zero.1 h1.2
  rw [map_sum]
  refine Eq.trans ?_ h2
  simp only [map_smul, hg]
  ext v h
  simp [RealDat.e0, gaL, postOn, RealDat.eC]
  rfl

theorem isTranslate_jX (hred : R.grp_red_R) (hj : R.models_jX) (t : T) (g : G) (x : (A.MtildeCSD t).Forms) :
    GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate D.sp.X' R.βX (R.datXt t) (R.eG g) ((R.HX t).e (R.jX t x))
      ((R.HX t).e (R.jX t (A.leftGroupActionRight t g x))) := by
  have e1 := hj t x
  have e2 := hj t (A.leftGroupActionRight t g x)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate
  refine ⟨?_, fun κ hκ h => ?_⟩
  · obtain ⟨q, hq⟩ := (R.B.R t).act_tie.red_surj g
    exact ⟨q, (hred t q).symm.trans (congrArg R.eG hq)⟩
  · have h1 : (R.B.R t).act_tie.red κ = g := R.eG.injective ((hred t κ).trans hκ)
    have h2 := ((e2.trans ((R.B.R t).act_tie.act_eq g κ h1 x)).trans
      (congrArg (Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch κ) e1.symm))
    exact congrFun h2 h

theorem th_gaOp (hC : R.Char F) (hG : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.GEquiv R) (t : T) (x : (A.MtildeCSD t).Forms) :
    R.Th t (R.jX t ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (goodAt A.X ⊥ 1) x)) = R.Th t (R.jX t x) :=
  apply_gaOp (S := A.MtildeCSD t) (A.leftGroupActionRight t) R.gE (R.jX t) (R.Th t)
    (fun g y => hG.th_of_translate R t (hC.models.HX t).1 g _ _ (isTranslate_jX R hC.grp.red_R hC.models.jX t g y))
    A.X (sum_gE_eq R hC.models.HE hC.models.gE) x

theorem throughGood (hC : R.Char F) (hG : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.GEquiv R) (F' : Face D A) : ThroughGood (F := A.fam) (R.toCx F') :=
  fun t x => th_gaOp R F hC hG t x

def PartsSpan : Prop := ⨆ c, GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R c = ⊤

theorem th_surjective (hB : GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.Concl R) (hS : PartsSpan R) (t : T) : Function.Surjective (R.Th t) :=
  surjective_of_scalar (R.Th t) (LinearMap.adjoint (R.Th t)) (GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.partE R) hS (hB.scalar_pos t)

theorem theta_surjective (hon : ∀ t, Function.Surjective (R.Th t)) (t : T) : Function.Surjective ((R.toCx F).Θ t) :=
  tw_map_surjective (twAt D.what₂.embLL A.v0) (hon t)

theorem principal_of_rowTest {s : ℕ} (hOk : A.fam.Ok s) (hC : R.Char F) (hG : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.GEquiv R)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestAt R F) (hon : ∀ t, Function.Surjective (R.Th t)) :
    (∀ t, Function.Bijective ((R.toCx (GlobalTheory.OneForm.principalFace F)).iC (GlobalTheory.OneForm.principalFace F).cr false t)) ∧
      (R.toCx (GlobalTheory.OneForm.principalFace F)).RATmu (GlobalTheory.OneForm.principalFace F).cr false :=
  bijective_and_ratMu (F := A.fam) (X := R.toCx (GlobalTheory.OneForm.principalFace F)) hOk
    (formsTie R _ hC.models.HX hC.models.jX) (throughGood R F hC hG _)
    ((GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.rowTest_toCx_iff R _).2 ((GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.rowTest_toCx_iff R F).1 (hT hC))) (theta_surjective R _ hon) _ false
    (GlobalTheory.EquivariantEuclideanComplex.isCoord_base A ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc _)

theorem principal_of_rowTest_of_scalar {s : ℕ} (hOk : A.fam.Ok s) (hC : R.Char F) (hG : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.GEquiv R)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestAt R F) (hB : GlobalTheory.IndefiniteRowSideFullHecke.DownUpLambdaOperators.Concl R) (hS : PartsSpan R) :
    (∀ t, Function.Bijective ((R.toCx (GlobalTheory.OneForm.principalFace F)).iC (GlobalTheory.OneForm.principalFace F).cr false t)) ∧
      (R.toCx (GlobalTheory.OneForm.principalFace F)).RATmu (GlobalTheory.OneForm.principalFace F).cr false :=
  principal_of_rowTest R F hOk hC hG hT (th_surjective R hB hS)

end Concrete

end GlobalTheory.OneFormTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSubstitutionThetaHeisenbergUnitary
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatSubst

theorem setLIntegral_comp_addEquiv {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (e : G ≃+ G) (he : Continuous e) (hes : Continuous e.symm)
    (hΓ : ∀ x, e x ∈ Γ ↔ x ∈ Γ) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) (hfin : μ F ≠ ⊤) (φ : G → ENNReal)
    (hφ : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) : ∫⁻ w in F, φ (e w) ∂μ = ∫⁻ w in F, φ w ∂μ := by
  let m : G ≃ᵐ G :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  have hν : (μ.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he)
  have hF' : IsAddFundamentalDomain Γ (e ⁻¹' F) (μ.map e.symm) := by
    let f : Γ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simp)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map e.symm = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  have hac : μ.map e.symm ≪ μ := hc ▸ Measure.smul_absolutelyContinuous
  have hF'' : IsAddFundamentalDomain Γ F (μ.map e.symm) := hF.mono hac
  have h1 : (μ.map e.symm) (e ⁻¹' F) = μ F := hmp.measure_preimage_equiv F
  have h2 : (μ.map e.symm) F = μ F := (hF''.measure_eq hF').trans h1
  have h0 : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  have hc1 : (c : ENNReal) = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [h2, one_mul])
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hc2, one_smul] at hc
  have h3 : ∫⁻ w in e ⁻¹' F, φ (e w) ∂(μ.map e.symm) = ∫⁻ w in F, φ w ∂μ :=
    hmp.setLIntegral_comp_preimage_emb m.measurableEmbedding φ F
  rw [hc] at h3 hF'
  rw [← h3]
  refine hF.setLIntegral_eq hF' (fun w => φ (e w)) fun g x => ?_
  show φ (e ((g : G) + x)) = φ (e x)
  rw [map_add, hφ _ ((hΓ _).2 g.2)]

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem mt_mul (V : HSp D) (g g' : GA D V) : Formalism.L2.Theta.mt V (g * g') = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g' := rfl

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul, Matrix.mul_assoc,
    ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem symplOH_actO (g : GA D S) (h : GA D T) (x y : WO S T) :
    symplOH S T (actO S T g h x) (actO S T g h y) = symplOH S T x y := by
  unfold symplOH
  rw [GlobalTheory.SymplOInv.symplO_actO]

theorem exists_mt_eq (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) :
    ∃ m : Matrix (Fin V.rank) (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ = m.map (incA D) := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ'.1, (congrArg Units.val e).symm⟩

theorem exists_actO_ratW {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ∃ y, actO S T γ γ' (ratW T S x) = ratW T S y := by
  obtain ⟨m, hm⟩ := exists_mt_eq S ((GQ S).inv_mem hγ)
  obtain ⟨m', hm'⟩ := exists_mt_eq T hγ'
  refine ⟨m' * x * m, ?_⟩
  unfold actO ratW
  rw [hm, hm', Matrix.map_mul, Matrix.map_mul]

theorem actO_mem_ratL {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) {x : WO S T}
    (hx : x ∈ ratL T S) : actO S T γ γ' x ∈ ratL T S := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := exists_actO_ratW hγ hγ' y
  exact ⟨z, hz.symm⟩

theorem isThetaFunO_comp {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) :
    IsThetaFunO ψ S T fun w => f (actO S T γ γ' w) := by
  let A : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T γ γ') (actO_add γ γ')
  have hA : Continuous (actO S T γ γ') := GlobalTheory.LatLevel.continuous_actO S T γ γ'
  refine ⟨fun x w => ?_, ?_, hf.cont.comp hA, fun k L h1 h2 w => ?_⟩
  · obtain ⟨y, e⟩ := exists_actO_ratW hγ hγ' x
    rw [actO_add, ← symplOH_actO γ γ', e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hA, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu (GlobalTheory.LatLevel.actO_map_inf S T γ γ' h0)) (actO S T γ γ' w)
    unfold heisO at e ⊢
    rw [← e, ← symplOH_actO γ γ' w u]
    exact congrArg (fun x => _ * f x) (actO_add γ γ' w u)
  · have h3 : ∀ t, (actO S T γ γ' (L t)).map (finPart D) = 0 := fun t => by
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    have := hf.smooth k (A.comp L) (hA.comp h1) h3 (actO S T γ γ' w)
    simp only [actO_add]
    exact this

theorem rational_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (fun w => f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ (∀ w₀, (fun w => heisO ψ S T w₀ f (actO S T γ⁻¹ γ'⁻¹ w)) = heisO ψ S T (actO S T γ γ' w₀) (fun w => f (actO S T γ⁻¹ γ'⁻¹ w))) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∫⁻ w in 𝓕, ‖f (actO S T γ⁻¹ γ'⁻¹ w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
  intro D ψ hψ S T γ hγ γ' hγ' f hf
  have hi := (GQ S).inv_mem hγ
  have hi' := (GQ T).inv_mem hγ'
  refine ⟨isThetaFunO_comp hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext w
    unfold heisO
    beta_reduce
    rw [actO_add, actO_inv_actO, ← symplOH_actO γ⁻¹ γ'⁻¹ w, actO_inv_actO]
  · obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have : Countable (ratL T S) := countable_of_discrete_addSubgroup _
    have hinv : ∀ x, actO S T γ γ' (actO S T γ⁻¹ γ'⁻¹ x) = x := fun x => by
      have := actO_inv_actO γ⁻¹ γ'⁻¹ x
      rwa [inv_inv, inv_inv] at this
    let e : WO S T ≃+ WO S T :=
      { toFun := actO S T γ⁻¹ γ'⁻¹
        invFun := actO S T γ γ'
        left_inv := hinv
        right_inv := actO_inv_actO γ γ'
        map_add' := actO_add _ _ }
    refine setLIntegral_comp_addEquiv (G := WO S T) (ratL T S) e (GlobalTheory.LatLevel.continuous_actO S T _ _)
      (GlobalTheory.LatLevel.continuous_actO S T _ _) (fun x => ⟨fun hx => ?_, actO_mem_ratL hi hi'⟩) μ h𝓕
      (measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hcov μ h𝓕).ne
      (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact actO_mem_ratL hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h6 : f (ratW T S y + x) = _ := hf.quasi y x
      have h7 : ‖f (ratW T S y + x)‖ = ‖f x‖ := by
        rw [h6, norm_mul, hψ.1.2.1, one_mul]
      show ‖f (ratW T S y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h7]

end GlobalTheory.RatSubst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryConjSplitSupportedFiniteAdelicPoi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjSplit

theorem sigR_incA (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := by
  simp [cA, sigR, incA, inclR]

def ratPt (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram) : GA D V :=
  ⟨Formalism.UG.bc (incA D) γ, by
    show Formalism.UG.cT _ _ * _ * _ = _
    have hc : Formalism.UG.cT (cA D) ((γ : Matrix _ _ D.host.E).map (incA D)) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1).map (incA D) := by
      ext i j; simp [Formalism.UG.cT, sigR_incA]
    have := congrArg (fun M => M.map (incA D)) hγ
    simp only [Matrix.map_mul] at this
    simpa [Formalism.UG.bc, JR, hc] using this⟩

theorem finE_ratPt (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E) hγ :
    (Formalism.IndefR.Lev.finE V (ratPt D V γ hγ)).1 = γ.1.map (eToEAf D) := by
  ext i j
  change Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E
    (Algebra.TensorProduct.map (AlgHom.snd (↥D.host.F) (Ainf ↥D.host.F) (Af ↥D.host.F)) (AlgHom.id (↥D.host.F) D.host.E)
      (Algebra.TensorProduct.includeRight (γ.1 i j))) = _
  simp [eToEAf]

theorem mt_mul (D : D7) (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_mul_inv (D : D7) (V : HSp D) (a : GA D V) : mt V a * mt V a⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel]; simp [Formalism.L2.Theta.mt]

theorem suppAt_conj {D : D7} {V : HSp D} {e : AE D} {h : GA D V} (hs : SuppAt e V h) (g : GA D V) :
    SuppAt e V (g * h * g⁻¹) := by
  have hm : (e + cA D e) • (mt V h - 1) = mt V h - 1 := Matrix.ext fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hs i j
  have key : mt V (g * h * g⁻¹) - 1 = mt V g * (mt V h - 1) * mt V g⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have hm' : (e + cA D e) • (mt V (g * h * g⁻¹) - 1) = mt V (g * h * g⁻¹) - 1 := by
    rw [key, ← Matrix.smul_mul, ← Matrix.mul_smul, hm]
  intro i j
  have := congrFun (congrFun hm' i) j
  rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem finE_ratPt_units (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E) hγ :
    Formalism.IndefR.Lev.finE V (ratPt D V γ hγ) = Formalism.UG.bc (eToEAf D) γ :=
  Units.ext (finE_ratPt D V γ hγ)

theorem conj_supp : ∀ (D : D7) (V : HSp D) (S : Finset ℕ) (γ : GL (Fin V.rank) D.host.E) (h : GA D V),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram → h ∈ GfC V →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) →
    ∃ u : GA D V, u ∈ GfC V ∧ (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u ∧ ∀ w ∈ P, Off S w) ∧
      (Formalism.IndefR.Lev.finE V u).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (γ⁻¹).1.map (eToEAf D) := by
  intro D V S γ h hγ hh ⟨P, e, he, hs, hoff⟩
  refine ⟨ratPt D V γ hγ * h * (ratPt D V γ hγ)⁻¹, ?_, ⟨P, e, he, suppAt_conj hs _, hoff⟩, ?_⟩
  · exact (MonoidHom.normal_ker (infHom V)).conj_mem h hh _
  · rw [map_mul, map_mul, map_inv, finE_ratPt_units, Units.val_mul, Units.val_mul, ← map_inv]
    rfl

end GlobalTheory.ConjSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealUnitaryCovolumeSumStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_unitary_covolume_sum : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → IsSReps X.Gm (Λ : Set (Fin r → E)) 1 s → ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) ≤ ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  first | exact @GlobalTheory.SUVolBound.sum_covolume_le | exact GlobalTheory.SUVolBound.sum_covolume_le | (intros; apply GlobalTheory.SUVolBound.sum_covolume_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResInjLToLiftReal
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftResInj

theorem resInjL_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.models_inf → RecTie.ResInjL (RecTie.toLiftReal R F tupT hm hTop hinj) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hθ i w hw h0
  let U : MMap (R.MW i (sg0 D A)) := PiTensorProduct.lift.symm w
  have hU : U ∈ Mult.Mult R.θ (R.MW i (sg0 D A)) _ _ := (Mult.mem_multT _ _ _ _ w).1 hw
  have hT : U = 0 := GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hθ
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
      have e := LinearMap.congr_fun h0 (PiTensorProduct.tprod ℂ v)
      have e2 : w (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
      rw [PiTensorProduct.map_tprod] at e2
      show (PiTensorProduct.lift.symm w : MMap (R.MW i (sg0 D A))) (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) = 0
      exact e2)
  have e3 : PiTensorProduct.lift U = w := LinearEquiv.apply_symm_apply _ w
  rw [← e3, hT]
  exact map_zero _

end GlobalTheory.LiftResInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaarStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_specialUnitary_eq_smul_haar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (ν : Measure (realSU X.Ψ X.Gm)), 1 ≤ r → IsOrth X x → ν.IsHaarMeasure → (∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x) → riemHaar X.Ψ X.Gm x = ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  first | exact @GlobalTheory.RiemConst.riemHaar_eq_smul | exact GlobalTheory.RiemConst.riemHaar_eq_smul | (intros; apply GlobalTheory.RiemConst.riemHaar_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionAdjointOfAdjointOnSpanningFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AdjSpan

open GlobalTheory.CechPic

theorem adj_of_span : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ∀ (act : O → (A ⟶ A)), IsRAct A act → (∀ i, LBIso (Q.pull (lift (fst A A ≫ act (e i)) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar (e i)))).left)) → Adj A Q bar act := by
  intro S A _ _ Q hQ O _ bar r e hbar hspan act hact he
  obtain ⟨hA, hL, h₁, h₂, -, hamp⟩ := hQ
  have hbi := GlobalTheory.Biadditive.biadditive_of_triv_axes GlobalTheory.globalFns_holds S A _ hA (pull_isLB hL _) hamp Q hL h₁ h₂

  let B : ((A ⊗ A) ⟶ A) → ((A ⊗ A) ⟶ A) → Pic (A ⊗ A).left := fun u v => pull (lift u v).left (cls Q hL)
  have addL : ∀ u u' v, B (u * u') v = B u v + B u' v := fun u u' v => by
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (hbi (A ⊗ A) u u' v).1
    rw [cls_linComb hL, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    show pull _ _ = pull _ _ + pull _ _
    rw [← sub_eq_zero, ← z]
    abel
  have addR : ∀ u v v', B u (v * v') = B u v + B u v' := fun u v v' => by
    have z := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 (hbi (A ⊗ A) v v' u).2
    rw [cls_linComb hL, Fin.sum_univ_three] at z
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
    show pull _ _ = pull _ _ + pull _ _
    rw [← sub_eq_zero, ← z]
    abel
  let f : O → Pic (A ⊗ A).left := fun a => B (fst A A ≫ act a) (snd A A) - B (fst A A) (snd A A ≫ act (bar a))
  have fadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    simp only [f]
    rw [hbar, hact.2.2.2, hact.2.2.2, MonObj.comp_mul, MonObj.comp_mul, addL, addR]
    abel
  let F : O →+ Pic (A ⊗ A).left := AddMonoidHom.mk' f fadd
  have Fe : ∀ i, F (e i) = 0 := fun i => by
    show f (e i) = 0
    exact sub_eq_zero.2 ((cls_eq_iff (pull_isLB hL _) (pull_isLB hL _)).2 (he i))
  have hker : Submodule.span ℤ (Set.range e) ≤ LinearMap.ker F.toIntLinearMap :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Fe i)
  intro a
  have ha : F a = 0 := hker (hspan ▸ Submodule.mem_top : a ∈ Submodule.span ℤ (Set.range e))
  exact (cls_eq_iff (pull_isLB hL _) (pull_isLB hL _)).1 (sub_eq_zero.1 ha)

end GlobalTheory.AdjSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersJointEigenspaceDisjointBiSupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegersJointEigenspace_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  first | exact @GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup | exact GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup | (intros; apply GlobalTheory.UPel.HT.LieType.eigSp_disjoint_biSup <;> assumption)
end

