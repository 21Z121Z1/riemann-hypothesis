import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0366
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPoint
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

theorem GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ)
    (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) : ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧
      CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  obtain ⟨A, hA, h, hh, hb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ Y₁.Fn (ratOf Y₁).pt
  obtain ⟨q, ⟨hq, hqb⟩, -⟩ := h₂.2.2 Y₁.Fn ((ratOf Y₁).pt ≫ f₁) A hA h hh
  have hcq : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt q := ⟨A, hA, h, hh, hb, hqb⟩
  obtain ⟨B, hB, g, hg, hgb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₂ Eb S₂ φ₂ f₂ h₂ Y₂.Fn (ratOf Y₂).pt
  obtain ⟨r, ⟨hr, hrb⟩, -⟩ := h₁.2.2 Y₂.Fn ((ratOf Y₂).pt ≫ f₂) B hB g hg
  have hcr : CoBear Eb S₁ φ₁ S₂ φ₂ (r ≫ f₁) r (ratOf Y₂).pt := ⟨B, hr ▸ hB, g, hg, hrb, hgb⟩
  have hsp := GlobalTheory.T.fullFlagLift_genericPoint_specializes_residue F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ q hq hcq (r (IsLocalRing.closedPoint _))
    (fun K _ p p' hp hpp hc => GlobalTheory.T.fullFlagBundle_point_at_genericLift_image F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ r hr hcr K p p' hp hpp hc)
  have hs : q ≫ Y₂.str = spMap (algebraMap F Y₁.Fn) := by
    have e1 : f₂ ≫ X.str = Y₂.str := h₂.1.inducedModelMorphism_comp_structureMap
    have e2 : f₁ ≫ X.str = Y₁.str := h₁.1.inducedModelMorphism_comp_structureMap
    have e3 : ((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ Y₁.str = spMap (algebraMap F Y₁.Fn) := (ratOf Y₁).pt_s
    calc q ≫ Y₂.str = q ≫ (f₂ ≫ X.str) := congrArg (q ≫ ·) e1.symm
    _ = (q ≫ f₂) ≫ X.str := (Category.assoc _ _ _).symm
    _ = ((ratOf Y₁).pt ≫ f₁) ≫ X.str := congrArg (· ≫ X.str) hq
    _ = (ratOf Y₁).pt ≫ (f₁ ≫ X.str) := Category.assoc _ _ _
    _ = (ratOf Y₁).pt ≫ Y₁.str := congrArg (((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ ·) e2
    _ = _ := e3
  obtain ⟨ψ, rfl⟩ := GlobalTheory.T.exists_algHom_functionField_of_specializes_genericPoint F Y₂ Y₁.Fn q hsp hs
  refine ⟨ψ, ?_, hcq⟩
  have key : ∀ (σ : X.Fn →+* Y₁.Fn) (a : X.Fn), (ratOf X).val (spMap σ ≫ (ratOf X).pt) a = σ a := by
    intro σ a
    have hm : a ∈ (ratOf X).O (genericPoint (ratOf X).Z) :=
      (RatModel.O_genericPoint (ratOf X)).symm ▸ Algebra.mem_top
    have h1 := RatModel.val_spMap_comp σ (ratOf X).pt ((ratOf X).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, hm⟩
    have h2 := RatModel.valLoc_eq_val (M := ratOf X) (ratOf X).pt ((ratOf X).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, hm⟩
    exact h1.trans (congrArg σ (h2.trans (RatModel.val_pt (M := ratOf X) a)))
  have H1 : ((ratOf Y₁).pt : Sp Y₁.Fn ⟶ Y₁.X) ≫ f₁ = spMap φ₁.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := h₁.1
  have H2 : ((ratOf Y₂).pt : Sp Y₂.Fn ⟶ Y₂.X) ≫ f₂ = spMap φ₂.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := h₂.1
  have e : spMap (ψ.comp φ₂).toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) =
      spMap φ₁.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X) := by
    have s1 : spMap (ψ.comp φ₂).toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X)
        = spMap ψ.toRingHom ≫ (spMap φ₂.toRingHom ≫ ((ratOf X).pt : Sp X.Fn ⟶ X.X)) := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    exact s1.trans ((congrArg (spMap ψ.toRingHom ≫ ·) H2.symm).trans
      ((Category.assoc _ _ _).symm.trans (hq.trans H1)))
  ext a
  have := congrArg (fun y => (ratOf X).val y a) e
  simp only [key] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepOfCuspidalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_rep_of_cuspidal : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  first | exact @GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw | exact GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw | (intros; apply GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitEmb
open GlobalTheory.SplitLift

section General
variable {n : ℕ} {K : Type*} (A : Type*) [CommRing K] [CommRing A]

def triMat (M : GL (Fin n) K) : Matrix (Fin n) (Fin n) (K × K × A) :=
  fun i j => ((M : Matrix (Fin n) (Fin n) K) i j, ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j i,
    (1 : Matrix (Fin n) (Fin n) A) i j)

theorem triMat_one : triMat A (1 : GL (Fin n) K) = 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [triMat, inv_one, Units.val_one, Matrix.one_apply, eq_comm (a := j)]
  split_ifs <;> rfl

theorem triMat_mul (M N : GL (Fin n) K) : triMat A (M * N) = triMat A M * triMat A N := by
  symm
  apply matrix_prod_ext
  · exact Matrix.map_mul (L := triMat A M) (M := triMat A N) (f := RingHom.fst K (K × A))
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.fst K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    change ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose *
      ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose =
      (((M * N)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
  · have e := Matrix.map_mul (L := triMat A M) (M := triMat A N)
      (f := (RingHom.snd K A).comp (RingHom.snd K (K × A)))
    refine e.trans ?_
    exact Matrix.mul_one (1 : Matrix (Fin n) (Fin n) A)

end General

theorem exists_hom_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    ∃ e : GL (Fin n) (s.v.adicCompletion (NumberField.maximalRealSubfield L)) →* GAf L n,
      (∀ g, TrivOutside {s.v} (e g)) ∧ ∀ g, s.loc n (e g) = g := by
  intro L _ _ _ n s
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : maximalRealSubfield L := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap (maximalRealSubfield L) L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  let X : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) → Matrix (Fin n) (Fin n) (AL L) :=
    fun M => (triMat (AL L) M).map (θ s δ d hd hr)
  have hX1 : X 1 = 1 := by
    show (triMat (AL L) 1).map (θ s δ d hd hr) = 1
    rw [triMat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXm : ∀ M N, X (M * N) = X M * X N := fun M N => by
    show (triMat (AL L) (M * N)).map (θ s δ d hd hr) = _
    rw [triMat_mul, Matrix.map_mul]
  have hconj : ∀ M, conjT (conjAL L) (X M) = X M⁻¹ := fun M => by
    refine Matrix.ext fun i j => ?_
    simp only [conjT, X, Matrix.transpose_apply, Matrix.map_apply]
    rw [conj_θ s δ d hd hr hδ]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [triMat, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have hX : ∀ M, X M * conjT (conjAL L) (X M) = 1 := fun M => by
    rw [hconj, ← hXm, mul_inv_cancel, hX1]
  let e : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := fun M => ⟨⟨X M, conjT (conjAL L) (X M), hX M, mul_eq_one_comm.mp (hX M)⟩, hX M⟩
      map_one' := Subtype.ext (Units.ext hX1)
      map_mul' := fun M N => Subtype.ext (Units.ext (hXm M N)) }
  refine ⟨e, fun M w hw => ?_, fun M => ?_⟩
  · have hw' : w ≠ s.v := hw
    refine Matrix.ext fun i j => ?_
    change compAt L w (θ s δ d hd hr (triMat (AL L) M i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [compAt_θ s δ d hd hr _ hw']
    simp only [triMat, Matrix.one_apply]
    split_ifs <;> simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change s.proj (θ s δ d hd hr (triMat (AL L) M i j)) = _
    rw [proj_θ]
    rfl

end GlobalTheory.SplitEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsGaugeOfIsCMExt
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCompatible_smul {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin M → E}
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (Hstab (AF F) σ J x)}
    {ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)} (h : IsCompatible F E σ M J x μ μ' ν) (c k : ℝ≥0) :
    IsCompatible F E σ M J x ((k * c) • μ) (c • μ') (k • ν) := by
  intro f hf sec hsec
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [h f hf sec hsec]
  simp only [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  push_cast
  ring

theorem StepRel.smul {d : ℕ} {b : Module.Basis (Fin d) F E} {s : StdMeas b} {M : ℕ}
    {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E} {β : F}
    {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (h : StepRel s σ J x β B J' μ μ') (c : ℝ≥0) : StepRel s σ J x β B J' (c • μ) (c • μ') := by
  intro ν hν e he
  have hc := isCompatible_smul (h ν hν e he) c 1
  simpa only [one_mul, one_smul, Measure.map_smul] using hc

end Scale

theorem smul_haar_inj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] (μ : Measure G) [μ.IsHaarMeasure] {c c' : ℝ≥0}
    (h : c • μ = c' • μ) : c = c' := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : μ K ≠ 0 :=
    (μ.measure_pos_of_nonempty_interior ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have htop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure G => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj hpos htop).1 h2)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem stepData_unique {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    {a a' : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' J'' : Matrix (Fin M) (Fin M) E}
    (h : StepData σ J x a B J') (h' : StepData σ J x a' B J'') : a = a' ∧ J' = J'' := by
  obtain ⟨-, -, h1, -, h2, -⟩ := h
  obtain ⟨-, -, h1', -, h2', -⟩ := h'
  exact ⟨(algebraMap F E).injective (h1.symm.trans h1'), h2.trans h2'.symm⟩

theorem exists_const (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} (s : StdMeas b)
    (G : GaugeFam F E σ) (hG : G.IsHaar) :
    ∃ c : ∀ M : ℕ, Matrix (Fin (M + 1)) (Fin (M + 1)) E → (Fin 1 → Fin (M + 1) → E) →
      Matrix (Fin (M + 1)) (Fin M) E → ℝ≥0ˣ,
      ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
        StepRel s σ J x a B J' ((c M J x B : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have key : ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E)
      (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
      2 ≤ M → StepData σ J x a B J' →
      ∃ u : ℝ≥0ˣ, StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
    intro M J x a B J' hM hS
    haveI : (G.μ M J').IsHaarMeasure := hG M J' hS.2.2.2.2.2
    haveI : (G.μ (M + 1) J).IsHaarMeasure := hG (M + 1) J hS.1
    obtain ⟨⟨μ, hμ, hrel⟩, -⟩ :=
      GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure F E σ hσ d b s M J x a B J' (G.μ M J') hM hS inferInstance
    haveI := hμ
    refine ⟨Units.mk0 (Measure.haarScalarFactor μ (G.μ (M + 1) J))
      (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', ?_⟩
    rw [Units.val_mk0, ← Measure.isMulLeftInvariant_eq_smul]
    exact hrel
  refine ⟨fun M J x B => if h : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧
      StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J')
    then h.choose else 1, ?_⟩
  intro M J x a B J' hM hS
  have hex : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧
      StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
    obtain ⟨u, hu⟩ := key M J x a B J' hM hS
    exact ⟨u, a, J', hM, hS, hu⟩
  simp only [dif_pos hex]
  obtain ⟨a₀, J₀, -, hS₀, hR₀⟩ := hex.choose_spec
  obtain ⟨rfl, rfl⟩ := stepData_unique hS₀ hS
  exact hR₀

theorem exists_std_family (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} (s : StdMeas b) :
    ∃ (G : GaugeFam F E σ) (α : ∀ M : ℕ, Matrix (Fin M) (Fin M) E → ℝ≥0ˣ), G.IsHaar ∧ G.BasisInv ∧
      (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
        α M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E)) =
          α M J) ∧
      ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
        StepRel s σ J x a B J' ((α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) ((α M J' : ℝ≥0) • G.μ M J') := by
  classical
  obtain ⟨G, hH, hB⟩ := GlobalTheory.T.exists_basisInvariant_haar_family_adelicUnitary F E σ hσ
  obtain ⟨c, hc⟩ := exists_const hσ s G hH
  refine (GlobalTheory.T.exists_coboundary_of_invariant_unitary_step_constants F E σ hσ ℝ≥0ˣ c ?inv ?coc).elim fun α hα => ?main
  case main =>
    obtain ⟨hαinv, hαstep⟩ := hα
    refine ⟨G, α, hH, hB, hαinv, ?_⟩
    intro M J x a B J' hM hS
    have r := (hc M J x a B J' hM hS).smul (α M J' : ℝ≥0)
    rw [smul_smul] at r
    rw [hαstep M J x a B J' hM hS, Units.val_mul, mul_comm]
    exact r
  case inv =>
    intro M J x a B J' x₂ B₂ P Q hM hS hx hPB
    obtain ⟨J₂, hJ₂⟩ : ∃ J₂, J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *
        J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) := ⟨_, rfl⟩
    obtain ⟨J₂', hJ₂'⟩ : ∃ J₂', J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) *
        J' * (Q : Matrix (Fin M) (Fin M) E) := ⟨_, rfl⟩
    rw [← hJ₂]
    obtain ⟨⟨eP, heP⟩, hmapP⟩ := hB (M + 1) J J₂ P hS.1 hJ₂
    obtain ⟨⟨eQ, heQ⟩, hmapQ⟩ := hB M J' J₂' Q hS.2.2.2.2.2 hJ₂'
    obtain ⟨hS₂, hR₂⟩ := GlobalTheory.T.unitaryOneVectorStep_compatible_changeOfBasis F E σ hσ _ b s M J J₂ x a B J' x₂ B₂ J₂' P Q eP eQ _ _ hS hJ₂
      hJ₂' hx hPB heP heQ (hc M J x a B J' hM hS)
    rw [Measure.map_smul, hmapP eP heP, hmapQ eQ heQ] at hR₂
    have hR₃ := hc M J₂ x₂ a B₂ J₂' hM hS₂
    have hHaar₂ : (G.μ M J₂').IsHaarMeasure := hH M J₂' hS₂.2.2.2.2.2
    have huniq := (GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure F E σ hσ _ b s M J₂ x₂ a B₂ J₂' (G.μ M J₂') hM hS₂ hHaar₂).2 _ _
      hR₃ hR₂
    haveI : (G.μ (M + 1) J₂).IsHaarMeasure := hH (M + 1) J₂ hS₂.1
    exact Units.ext (smul_haar_inj _ huniq)
  case coc =>
    intro M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀ hM h1 h1' h2 h2' hBC
    haveI : (G.μ M J₀).IsHaarMeasure := hH M J₀ h1'.2.2.2.2.2
    haveI : (G.μ (M + 1 + 1) J).IsHaarMeasure := hH _ J h1.1
    have r1 := (hc (M + 1) J x₁ a₁ B₁ J₁ (by omega) h1).smul (c M J₁ y₁ C₁ : ℝ≥0)
    have r2 := (hc (M + 1) J x₂ a₂ B₂ J₂ (by omega) h2).smul (c M J₂ y₂ C₂ : ℝ≥0)
    have heq := GlobalTheory.T.unitaryStabilizer_measure_independent_of_path F E σ hσ _ b s M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀
      (G.μ M J₀) _ _ _ _ hM h1 h1' h2 h2' hBC inferInstance (hc M J₁ y₁ b₁ C₁ J₀ hM h1') r1
      (hc M J₂ y₂ b₂ C₂ J₀ hM h2') r2
    rw [smul_smul, smul_smul] at heq
    have he := smul_haar_inj _ heq
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, mul_comm, he, mul_comm]

theorem exists_isGauge_of_isCMExt (hσ : IsCMExt F E σ) : ∃ G : GaugeFam F E σ, G.IsGauge := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  haveI : IsTotallyReal F := hσ.1
  obtain ⟨s⟩ := GlobalTheory.T.nonempty_standardLocalHaarMeasures F E _ (Module.finBasis F E)
  obtain ⟨G, α, hH, hB, hαinv, hstep⟩ := exists_std_family hσ s
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.quadricFibreMeasure_eq_smul_normalisedProduct F E σ hσ _ _ s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal F
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℝ≥0, K = fun M => ∏ i ∈ Finset.range (M + 1), κ i := ⟨_, rfl⟩
  have hK0 : ∀ M, K M ≠ 0 := fun M => by
    rw [hK]; exact Finset.prod_ne_zero_iff.2 fun i _ => hκ0 i
  have hKs : ∀ M, K (M + 1) = κ (M + 1) * K M := fun M => by
    rw [hK]; simp only [Finset.prod_range_succ (n := M + 1)]; ring
  refine ⟨⟨fun M J => (K M * α M J : ℝ≥0) • G.μ M J⟩, ?_, ?_, ?_⟩
  · intro M J hJ
    haveI : (G.μ M J).IsHaarMeasure := hH M J hJ
    exact Measure.IsHaarMeasure.nnreal_smul _ (mul_ne_zero (hK0 M) (α M J).ne_zero)
  · intro M J J' P hJ hJ'
    obtain ⟨⟨e, he⟩, hmap⟩ := hB M J J' P hJ hJ'
    refine ⟨⟨e, he⟩, fun e' he' => ?_⟩
    show ((K M * α M J : ℝ≥0) • G.μ M J).map e' = (K M * α M J' : ℝ≥0) • G.μ M J'
    rw [Measure.map_smul, hmap e' he', hJ', hαinv M J P hJ]
  · intro M J J' x β B hM hJ hβ hx hB' hJ'' hJ'
    have hS : StepData σ J x β B J' := ⟨hJ, hβ, hx, hB', hJ'', hJ'⟩
    obtain ⟨ν, hν, -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ _ _ s (M + 1) J β hM hJ hβ
    obtain ⟨e, he, -⟩ := (GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x β B J' hS).2.1
    refine ⟨⟨ψ, hψ⟩, fun ψ' hψ' => ?_⟩
    have hX := hκ (M + 1) J β ψ' ν (by omega) hJ hβ hψ' hν
    refine ⟨⟨_, (hX _).2 rfl⟩, fun νX hνX => ?_⟩
    rw [(hX νX).1 hνX]
    refine ⟨⟨e, he⟩, fun e' he' => ?_⟩
    have hc := isCompatible_smul (hstep M J x β B J' (by omega) hS ν hν e' he') (K M) (κ (M + 1))
    convert hc using 1
    · show ((K (M + 1) * α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) = _
      rw [smul_smul, hKs, mul_assoc]
    · show ((K M * α M J' : ℝ≥0) • G.μ M J').map e'.symm = _
      simp only [Measure.map_smul, smul_smul]

end GlobalTheory.GaugeEx

open Formalism.BasicNotions Formalism.MainNotions.G in

theorem GlobalTheory.GaugeEx.exists_isGauge : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ G : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.GaugeFam F E cm.sig, G.IsGauge := by
  intro F E _ _ _ _ _ _ cm
  have hσ : IsCMExt F E cm.sig :=
    ⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩
  exact exists_isGauge_of_isCMExt hσ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_fockVacuum_of_nonzero_thetaFunction : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → f ≠ 0 → ∃ f₀, GlobalTheory.ChainFr.IsVacF ψ θ A B f₀ ∧ f₀ ≠ 0 := by
  first | exact @GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero | exact GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero | (intros; apply GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.ThetaLevel

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  have h1 : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, z ^ i‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have : ∀ i ∈ Finset.range N, (1 / 2 : ℝ) ≤ (z ^ i).re := by
      intro i _
      have h2 := (Complex.abs_re_le_norm (z ^ i - 1)).trans_lt (h i)
      rw [Complex.sub_re, Complex.one_re, abs_lt] at h2
      linarith [h2.1]
    have h3 := Finset.sum_le_sum this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
    linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h4 := h N
  rw [← geom_sum_mul, norm_mul] at h4
  rw [div_lt_iff₀ hpos] at hN
  nlinarith [h1 N]

theorem eventually_smul (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hw : GlobalTheory.Ker.IsWeak ψ S T om)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∃ c : ℂ, om p f = c • f := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  filter_upwards [GlobalTheory.T.eventually_weilMatrixCoeff_finitePoint_invariant D ψ hψ S T μ 𝓕 hμ h𝓕 f hf] with p hp h1 h2
  obtain ⟨g, h⟩ := p
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.thetaFunction_eq_unitSmul_of_diagonalCoefficient_eq D ψ hψ S T μ 𝓕 hμ h𝓕 f (om (g, h) f) hf (hw.om_pres _ f hf) (fun w => by
    have e : actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := GlobalTheory.AdelicLatMove.actO_actO_inv S T g h w
    have e1 := hp h1 h2 (actO S T g⁻¹ h⁻¹ w)
    have e2 := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om (g, h)) (hw.om_pres _) (hw.om_unit μ 𝓕 hμ h𝓕 _)
      (heisO ψ S T (actO S T g⁻¹ h⁻¹ w) f) f (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf
    rw [hw.om_heis g h _ f hf, e] at e2
    simp only [e] at e1
    exact e2.trans e1.symm)
  exact ⟨c, hc⟩

theorem exists_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ f, IsThetaFunO ψ S T f → ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧ IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → om (k, k') f = f := by
  intro D ψ hψ S T om hw hc f hf
  by_cases h0 : f = 0
  · exact ⟨⊤, ⊤, by simp, by simp, fun k _ _ k' _ _ => by rw [h0, map_zero]⟩
  obtain ⟨w, hw0⟩ := Function.ne_iff.1 h0
  have hw0 : f w ≠ 0 := hw0
  have hcont : Continuous fun p : GA D S × GA D T => ‖om p f w / f w - 1‖ :=
    (((hc f hf w).div_const _).sub continuous_const).norm
  have hnear : ∀ᶠ p : GA D S × GA D T in 𝓝 1, ‖om p f w / f w - 1‖ < 1 / 2 := by
    refine hcont.continuousAt.eventually_lt continuousAt_const ?_
    simp [div_self hw0]
  have hN := (eventually_smul D ψ hψ S T om hw f hf).and hnear
  obtain ⟨N, hN1, N', hN2, hsub⟩ := mem_nhds_prod_iff.1 (show _ ∈ 𝓝 ((1 : GA D S), (1 : GA D T)) from hN)
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D S N hN1
  obtain ⟨U', hU', hUN'⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D T N' hN2
  refine ⟨U, U', hU, hU', fun k hk hkf k' hk' hkf' => ?_⟩
  obtain ⟨c, hcf⟩ := (hsub (Set.mk_mem_prod (hUN k hk hkf) (hUN' k' hk' hkf'))).1 hkf hkf'
  have hpow : ∀ n : ℕ, om ((k, k') ^ n) f = c ^ n • f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hcf, map_smul, ih, smul_smul, pow_succ']
  have hc1 : c = 1 := eq_one_of_pow_near fun n => by
    have h := (hsub (Set.mk_mem_prod (hUN _ (pow_mem hk n) (pow_mem hkf n))
      (hUN' _ (pow_mem hk' n) (pow_mem hkf' n)))).2
    have e : om (k ^ n, k' ^ n) f = c ^ n • f := hpow n
    rw [e, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hw0] at h
    exact h
  rw [hcf, hc1, one_smul]

end GlobalTheory.Mem.ThetaLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepCombinationPurePowerTraceStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polyRep_combination_pure_power_trace : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι) (i : ℕ), 1 ≤ i → ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ), ∀ (A : Mat m S) (b : ℕ), b ≤ n → ∑ j, c j • (ρ j).ptr b A = if b = i then ((A τ) ^ i).trace else 0 := by
  first | exact @GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace | exact GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace | (intros; apply GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecialisationCoefficientSpaceToDualWeylStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialisation_coefficientSpace_to_dualWeyl : ∀ (K : Type) [Field K] [Infinite K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → DomWeight n) (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n), w ∈ Formalism.L2.DIV.VV K lam → w ≠ 0 →
    ∃ φ : Formalism.L2.DIV.Pol K ι n →ₗ[K] MvPolynomial (Fin n × Fin n) K, φ w ≠ 0 ∧
      (∀ P ∈ Formalism.L2.DIV.VV K lam, φ P ∈ nablaSq K n (lam τ₀)) ∧
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Formalism.L2.DIV.Pol K ι n),
        φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) = Formalism.GradedWeylDivisibility.rowAct K M (φ P) := by
  first | exact @GlobalTheory.specialise_factor | exact GlobalTheory.specialise_factor | (intros; apply GlobalTheory.specialise_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericCharacterProjectorOnTwistFormsFixStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericCharacterProjectorOnTwistForms_fix : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool),
    ∀ y ∈ Fm0T D T S In.rho In.chi In.θ i j b, piKop D T S In i j b y = y := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.piKop_fix | exact GlobalTheory.HeightCounting.FormsStep.piKop_fix | (intros; apply GlobalTheory.HeightCounting.FormsStep.piKop_fix <;> assumption)
end

