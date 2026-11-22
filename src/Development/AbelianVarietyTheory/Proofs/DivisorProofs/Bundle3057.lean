import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.HessKer

open ReciprocityTheory.L2DbarEstimates (V cHess bas)

theorem exists_vecMul_eq_zero {D D' : ℕ} (h : D' < D) (P : Matrix (Fin D) (Fin D') ℂ) :
    ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ Matrix.vecMul ξ P = 0 := by
  have hk : LinearMap.ker P.vecMulLinear ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨ξ, hξ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨ξ, h0, by simpa using hξ⟩

theorem exists_common_kernel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D D' : ℕ), D' < D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (c : AlgChart p σ D') (c' : AlgChart q σ D) (w : CxPts q σ), w ∈ c'.e.source → ptMap π hπ σ w ∈ c.e.source → ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ ∀ (A : MLine p σ) (i : (A.pull π hπ).B.ι), w ∈ ptsIn q σ ((A.pull π hπ).B.U i) → Matrix.vecMul ξ (c'.hess (A.pull π hπ).φ i w) = 0 := by
  intro k _ X Y p q σ D D' hD π hπ c c' y hy hy0
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  set F : V D → V D' := c.e ∘ m ∘ c'.e.symm with hFdef
  set U := c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)
  have hU : IsOpen U := isOpen_over c'.e (c.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c'.e y ∈ U := mem_over c'.e hy hy0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c' c
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c'.e y) = c.e (m y) := by
    simp only [hFdef, Function.comp_apply, c'.e.left_inv hy]
  obtain ⟨ξ, hξ, hP⟩ := exists_vecMul_eq_zero hD (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b)
  refine ⟨ξ, hξ, fun A i hi => ?_⟩
  have him : m y ∈ ptsIn p σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V D' → ℂ := fun v => (A.φ.φ (i PUnit.unit) (c.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c'.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (A.cInf.contDiffAt c hy0 him)
  have e : (fun v => ((A.pull π hπ).φ.φ i (c'.e.symm v) : ℂ)) =ᶠ[𝓝 (c'.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ A.φ π hπ i (c'.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c.e.left_inv hv.2]
    exact congrArg _ this
  have key : c'.hess (A.pull π hπ).φ i y =
      (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b) * (cHess D' g (F (c'.e y)) *
        Matrix.of fun a l => (starRingEnd ℂ) (fderiv ℂ F (c'.e y) (bas D l) a)) := by
    show cHess D _ (c'.e y) = _
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, ← Matrix.mul_assoc]
    ext j l
    rw [GlobalTheory.HessPull.cHess_comp_apply D D' g F U hU _ hyU hF hg j l, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [key, ← Matrix.vecMul_vecMul, hP, Matrix.zero_vecMul]

end GlobalTheory.HessKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompOfIsFilLift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.AbDual GlobalTheory.AbLaw
  GlobalTheory.CechPic GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSBijection

open TrivSqZeroExt KSSymm

section Crystal

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {g : ℕ}

theorem fst_surj : Function.Surjective (fstHom R R R).toRingHom := fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩

def Comp (d : Crys (epsDP R) (DeRham.epsRed R) A) (f k : HdR A) : Prop :=
  ∀ c : primDR A, d ((constMor A).pull c) = TrivSqZeroExt.inl (f c) + TrivSqZeroExt.inr (k c)

variable {d d' : Crys (epsDP R) (DeRham.epsRed R) A} {f f' k k' : HdR A}

theorem Comp.unique (h : Comp d f k) (h' : Comp d f' k') : f = f' ∧ k = k' :=
  ⟨LinearMap.ext fun c ↦ by simpa using congrArg TrivSqZeroExt.fst ((h c).symm.trans (h' c)),
    LinearMap.ext fun c ↦ by simpa using congrArg TrivSqZeroExt.snd ((h c).symm.trans (h' c))⟩

theorem comp_zero : Comp (0 : Crys (epsDP R) (DeRham.epsRed R) A) 0 0 := fun _ ↦ by
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  simp

theorem Comp.add (h : Comp d f k) (h' : Comp d' f' k') : Comp (d + d') (f + f') (k + k') := fun c ↦ by
  rw [LinearMap.add_apply, h, h']
  ext <;> simp

theorem Comp.smul (h : Comp d f k) (r : DualNumber R) : Comp (r • d) (r.fst • f) (r.fst • k + r.snd • f) :=
  fun c ↦ by
  rw [LinearMap.smul_apply, h]
  ext <;> simp [mul_comm]

theorem Comp.ext (hm : (constMor A).IsBC) (h : Comp d f k) (h' : Comp d' f k) : d = d' :=
  JetIsotropic.ext_of_isBC hm fun c ↦ (h c).trans (h' c).symm

theorem Comp.corr (hm : (constMor A).IsBC) (h : Comp d f k) : (redMor A).Corr d f := fun c ↦ by
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smul, h, LinearMap.map_smulₛₗ, redMor_constMor, LinearMap.map_smul]
    simp

theorem Comp.push (h : Comp d f k) (u : A ⟶ A) [IsMonHom u] :
    Comp (push (epsDP R) (DeRham.epsRed R) u d) (push (dp0 R) (𝟙 _) u f) (push (dp0 R) (𝟙 _) u k) := fun c ↦ by
  have kk := (homMor (dp0 R) (𝟙 _) u).comp (constMor A)
  have hM := homMor (epsDP R) (DeRham.epsRed R) u
  have e1 := GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) u) (constMor A) kk (fun _ ↦ rfl) rfl c
  rw [push_apply]
  change d (hM.pull ((constMor A).pull c)) = _
  rw [e1, ← e2, h]
  rfl

variable [IsCommMonObj A] {O : Type} [CommRing O] {a : OAct O A} (hL : LieExact A)

def graph (κ : Fil A →ₗ[R] Serre.Lie a) : Submodule (DualNumber R) (Crys (epsDP R) (DeRham.epsRed R) A) where
  carrier := {d | ∃ (f : Fil A) (k : HdR A), Comp d f k ∧ hL.toLie a k = κ f}
  zero_mem' := ⟨0, 0, comp_zero, by simp⟩
  add_mem' := by
    rintro _ _ ⟨f, k, h, e⟩ ⟨f', k', h', e'⟩
    exact ⟨f + f', k + k', h.add h', by rw [map_add, map_add, e, e']⟩
  smul_mem' := by
    rintro r _ ⟨f, k, h, e⟩
    have z : hL.toLie a f = 0 := (hL.ker_toLie a).ge f.2
    exact ⟨r.fst • f, _, h.smul r, by rw [map_add, map_smul, map_smul, map_smul, e, z, smul_zero, add_zero]⟩

variable (κ : Fil A →ₗ[R] Serre.Lie a)

end Crystal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R : Type} [CommRing R]
  {X : Obj F 𝔠 (Sp R)}

end GlobalTheory.KSBijection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_npow_of_tensFacts {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hf : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hf 0
    have he0 : ∀ j, e 0 j = 0 := fun j => by
      have := hf.2.2.1 0 0 j
      rw [add_zero] at this
      simpa using this
    have e1 : (1 : Fin r → N.Gt) = fun j => N.io (e 0 j) := funext fun j => by rw [he0, N.io_zero]; rfl
    rw [pow_zero, pow_zero, e1, ← N'.io_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hf _ _ _ _ ih h

theorem exists_components_of_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' : QkPt D'.toPre F k), ∃ ps : Fin r → QkPt D.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hf := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  obtain ⟨q', hq', -⟩ := ((hGt R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).1 p'
  obtain ⟨vs, hvs⟩ := GlobalTheory.T.exists_torus_components_of_unimodular_tensor F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW q'.1.2
  have hk := gtRelV_npow_of_tensFacts hf hvs k
  rw [N'.mem_QT.1 q'.2] at hk
  have hio := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf q'.1.1.toAdd
  have hv := GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW _ _ _ hk hio
  let qs : Fin r → N.QT k := fun j =>
    ⟨(Multiplicative.ofAdd (chi T ν ν' q'.1.1.toAdd j), vs j), N.mem_QT.2 (congrFun hv j)⟩
  choose ps hps using fun j => ((hGt R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.1 (qs j)
  exact ⟨ps, q', qs, hq', hps, fun _ => rfl, hvs⟩

end GlobalTheory.Mum.TensTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpEvenOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PrimCube

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem evenOn_of_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (P : GlobalTheory.UU.CP G) (a : G ⟶ G), IsMonHom a → LBIso P.L.L (cubeLB G ![𝟙 G, a] P.L.L) → EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U P a ha hw
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = U.gen.hom.left ≫ A.A.hom := (Over.w U.gen.hom).symm
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U.gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U.gt 0) hB
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal R) 0 P
  have hm : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.field _
  have hS0 := IsSemiAbelian.pullback (thick R (maximalIdeal R) 0) G hS
  have := hS0.smooth
  have := hS0.geomConnected
  have := Q₀.i_hom
  letI := D.toPre.addX
  haveI := D.toPre.freeX
  haveI := D.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (R ⧸ maximalIdeal R ^ (0 + 1)) D.toPre.X (thickObj R (maximalIdeal R) 0 G) P₀.L P₀.c Q₀.i
    Q₀.i_hom
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective (GlobalTheory.EvenTriv.surjective_cube_of_generic G hS hp) P a hw P₀
    (IsPullback.of_hasPullback G.hom (thick R (maximalIdeal R) 0)) hv Q₀.i s
  exact ⟨D.toPre.X, D.toPre.addX, D.toPre.freeX, D.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

theorem exists_cp_evenOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → TraceFormTwistIso D.toPre o w → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) ∧ EvenOn P := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw _
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have ha := oG.hom w
  have hb := oG.hom (star w)
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hgh := U.gen_hom
  have hp : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = U.gen.hom.left ≫ A.A.hom := (Over.w U.gen.hom).symm
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U.gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := GlobalTheory.T.uniformisation_ringAction_adjoint_cubeBundle R hR.1 D A G hS U O o oA oG hlin w
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => normCls U.LG.L (oG.act w) x.left) =
      fun x => diff₂ (ptCls U.LG.L T) x (postHom (oG.act w) T x) := fun T => funext fun x => normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G), postHom (oG.act w) T y * postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G), diff₂ (ptCls U.LG.L T) (postHom (oG.act w) T x) y =
      diff₂ (ptCls U.LG.L T) x (postHom (oG.act (star w)) T y) := fun T x y => diff₂_ptCls_adj hM hadj x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine lbIso_nested hM _ _ _ _ _ _ ((prod_square_id x y (normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (prod_square_id x y (cls U.LG.L)).symm))
    rw [hq]
    exact diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have symN : HasGen (cubeLB G ![𝟙 G, oG.act w] U.LG.L) (K := Fin 2) ![(GrpObj.inv (X := G)).left, 𝟙 _] ![1, -1] := by
    refine hasGen_nested hM _ _ _ _ ?_
    rw [Fin.prod_univ_two]
    show normCls U.LG.L (oG.act w) (GrpObj.inv (X := G)).left ^ (1 : ℤ) *
      normCls U.LG.L (oG.act w) (𝟙 G : G ⟶ G).left ^ (-1 : ℤ) = 1
    have e : GrpObj.inv (X := G) = (𝟙 G)⁻¹ := by simp [Hom.inv_def]
    have e' : (𝟙 G)⁻¹ ≫ oG.act w = (𝟙 G ≫ oG.act w)⁻¹ := map_inv (postHom (oG.act w) G) _
    rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc G), zpow_neg, mul_inv_cancel]
  have hN := GlobalTheory.LamCalc.cubeLB_isLB hM ![𝟙 G, oG.act w]
  obtain ⟨L', c', hL'⟩ := GlobalTheory.RigCube.exists_rigLB_cubicalStr R G hS hp _ hN
  have hsym : L'.IsSymmetric := isSymmetric_of_hasGen L' (hL' ▸ symN)
  obtain ⟨P, hP, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric hL R A G hS U.gen hgh L' c' hsym
  have hPN : P.L.L = cubeLB G ![𝟙 G, oG.act w] U.LG.L := by rw [hP, hL']
  refine ⟨P, hPN ▸ GlobalTheory.PolBaseChange.lbIso_refl P.L.isLB, evenOn_of_prim R hR D A G hS U P (oG.act w) ha ?_⟩
  rw [hPN]
  exact (iso G (𝟙 G) (oG.act w)).symm

end GlobalTheory.Mum.PrimCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPeakAtInjectiveChartFrameStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cusp_form_peak_at_injective_chart_frame : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → ∃ P ∈ X.SS la, P x ≠ 0 ∧ ENNReal.ofReal (Real.exp (-(C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8)))) * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (X.pnorm la P x ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0 FF := by
  first | exact @GlobalTheory.PeakThick.peak | exact GlobalTheory.PeakThick.peak | (intros; apply GlobalTheory.PeakThick.peak <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorValuationBoundStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_valuation_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ)
    (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → ∀ la : GlobalTheory.AllWt.Weight Dw, GapGe 1 la →
    ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0),
      (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  first | exact @GlobalTheory.LatFull.CMInt.exists_frame_denom_intWt | exact GlobalTheory.LatFull.CMInt.exists_frame_denom_intWt | (intros; apply GlobalTheory.LatFull.CMInt.exists_frame_denom_intWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedGeneratorThickenedAbelianPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_generator_thickened_abelian_part : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  first | exact @GlobalTheory.HomMum.exists_gen_thick_two | exact GlobalTheory.HomMum.exists_gen_thick_two | (intros; apply GlobalTheory.HomMum.exists_gen_thick_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantRestrictionPointClosures
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem clo_restrict_dominant : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) (y : Y), ∃ g : clo y ⟶ clo (π y), g ≫ cloι (π y) = cloι y ≫ π ∧ g (genericPoint _) = genericPoint _ ∧ ∀ w : clo y, g.residueDegree w = π.residueDegree (cloι y w) := by
  intro X Y π y
  set i := cloι (π y)
  set j := cloι y
  have hi : i (genericPoint (clo (π y))) = π y := cloι_genericPoint _
  have hj : j (genericPoint (clo y)) = y := cloι_genericPoint _
  have hr : Set.range i = closure {π y} := by
    have h₁ := (genericPoint_spec (clo (π y))).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i (j ≫ π)) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    refine Set.eq_univ_of_forall fun w => ?_
    have := ((genericPoint_specializes w).map (j ≫ π).continuous)
    rw [Set.mem_preimage]
    have e : (j ≫ π) (genericPoint (clo y)) = π y := by
      rw [Scheme.Hom.comp_apply, hj]
    rw [e] at this
    exact this.mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i (j ≫ π))
  refine ⟨inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π), ?_, ?_, ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      Scheme.Hom.comp_apply, hj, hi]
  · intro w
    have e₁ := GlobalTheory.CurveDegreesCompare.residueDegree_comp (inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π)) i w
    have e₂ := GlobalTheory.CurveDegreesCompare.residueDegree_comp j π w
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      GlobalTheory.Published.residueDegree_of_isClosedImmersion i, one_mul] at e₁
    rw [GlobalTheory.Published.residueDegree_of_isClosedImmersion j, mul_one] at e₂
    rw [← e₁, e₂]

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalSymmetricBundleTranslateOrderTw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwistCP

theorem exists_cp_transl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P := by
  intro R _ _ _ hR D A G _ _ hG U a ha
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  let M := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_generator_lineBundle_pullback_spec_localRing R G.left M.L.L M.L.isLB a.left
  obtain ⟨P, hPL, h2, h3⟩ := GlobalTheory.T.exists_translate_cubicalSymmetricLineBundle_twoTorsion (Sp R) G M a ha ρ hρ
  refine ⟨P, ?_, GlobalTheory.T.translatedUniformisationBundle_even_closedFibreTorus R hR D A G hG U a ha P hPL h2 h3⟩
  rw [hPL]
  exact GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _)

end GlobalTheory.MumTwistCP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatAlgHomEtaleHeightOneStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_algHom_etale_height_one : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R] [CommRing C] [Algebra R C]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    Algebra.IsIntegral R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    (∃ s : C →+* FractionRing A, s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O), Module.FaithfullyFlat R O ∧ Nonempty (C →ₐ[R] O) := by
  first | (exact @GlobalTheory.GoodEtaleSection.exists_faithfullyFlat_algHom) | (exact GlobalTheory.GoodEtaleSection.exists_faithfullyFlat_algHom) | (intros; apply GlobalTheory.GoodEtaleSection.exists_faithfullyFlat_algHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSubgroupSchemeOfGaloisStablePoiStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_subgroupScheme_of_galoisStable_points : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (H : Over (Sp K)) (_ : GrpObj H) (i : H ⟶ A.X), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ x : A.Pt, x ∈ G ↔ ∃ y, y ≫ i = x := by
  first | (exact @GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points) | (exact GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points) | (intros; apply GlobalTheory.FinEtSubgroup.exists_finiteEtale_subgroup_of_points  <;> assumption)
end

