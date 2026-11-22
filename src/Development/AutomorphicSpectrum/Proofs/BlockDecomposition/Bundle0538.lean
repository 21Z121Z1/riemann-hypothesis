import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0507
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesTracePairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLevelFacts
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinLevelTw

open PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def atHom (a b : ℕ) (w : Pl E) : Gf E a b →* GLw a w × GLw b w :=
  (GeneralLinearGroup.map (pLoc E w)).prodMap (GeneralLinearGroup.map (pLoc E w))

omit [IsCMField E] in
theorem atHom_apply (w : Pl E) (y : Gf E a b) : atHom a b w y = atW w y := rfl

theorem continuous_atHom (w : Pl E) : Continuous (atHom (E := E) a b w) :=
  ((GlobalTheory.EulerTwU.continuous_pc w).comp continuous_fst).prodMk ((GlobalTheory.EulerTwU.continuous_pc w).comp continuous_snd)

theorem isOpen_Kf (n : ℕ) : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := by
  refine Subgroup.isOpen_mono (H₁ := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) ?_
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hg
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_comap.2 ?_
  refine GlobalTheory.EulerTwU.mem_GLint _ _ (fun i j => ?_) (fun i j => ?_)
  · exact GroundTheory.Global.mem_integralFiniteAdeles.1 (h1 i j) w
  · rw [← map_inv]
    exact GroundTheory.Global.mem_integralFiniteAdeles.1 (h2 i j) w

theorem continuous_thP : Continuous (thP E a b) := by
  have h : ∀ n, Continuous (thF E n) := fun n => GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)
  exact ((h a).comp continuous_fst).prodMk ((h b).comp continuous_snd)

theorem thP_thP (y : Gf E a b) : thP E a b (thP E a b y) = y :=
  Prod.ext (GlobalTheory.EulerTwU.thF_thF y.1) (GlobalTheory.EulerTwU.thF_thF y.2)

theorem isOpen_family (M : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (hM : ∀ w, IsOpen (M w : Set (GLw a w × GLw b w)))
    (hK : ∀ᶠ w in cofinite, K2 a b w ≤ M w) :
    IsOpen ((⨅ w, (M w).comap (atHom a b w) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hT : {w | ¬ K2 a b w ≤ M w}.Finite := hK
  have h1 : ∀ᶠ u in nhds (1 : Gf E a b), ∀ w ∈ {w | ¬ K2 a b w ≤ M w}, atHom a b w u ∈ M w :=
    (Filter.eventually_all_finite hT).2 fun w _ =>
      (continuous_atHom w).continuousAt.eventually_mem
        ((hM w).mem_nhds (by rw [map_one]; exact one_mem _))
  have h2 : ∀ᶠ u in nhds (1 : Gf E a b), u ∈ ((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) :=
    ((isOpen_Kf a).prod (isOpen_Kf b)).mem_nhds ⟨one_mem _, one_mem _⟩
  filter_upwards [h1, h2] with u hu1 hu2
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_comap.2 ?_
  by_cases hw : K2 a b w ≤ M w
  · refine hw ⟨?_, ?_⟩
    · exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu2.1 w)
    · exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu2.2 w)
  · exact hu1 w hw

theorem exists_level_of_test {φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) :
    ∃ L : ∀ w : Pl E, Subgroup (GLw a w × GLw b w), (∀ w, IsOpen (L w : Set (GLw a w × GLw b w))) ∧
      (∀ᶠ w in cofinite, L w = K2 a b w) ∧ ∀ w, ∀ k ∈ L w, ∀ x, φ w (k * x) = φ w x ∧ φ w (x * k) = φ w x := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  refine ⟨fun w => (K₁ w).prod (K₂ w), fun w => ?_, ?_, fun w => (h₃.1 w).2⟩
  · rw [Subgroup.coe_prod]
    exact (h₁.1 w).1.prod (h₂.1 w).1
  · filter_upwards [h₁.2, h₂.2] with w e₁ e₂
    rw [e₁, e₂]

theorem finLevel : FinLevel := by
  intro E _ _ _ _ a b S φ₁ φ₂ h₁ h₂
  obtain ⟨L₁, o₁, e₁, i₁⟩ := exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := exists_level_of_test h₂
  let A : Subgroup (Gf E a b) := ⨅ w, (L₁ w ⊓ L₂ w).comap (atHom a b w)
  have hA : IsOpen (A : Set (Gf E a b)) := by
    refine isOpen_family _ (fun w => ?_) ?_
    · rw [Subgroup.coe_inf]
      exact (o₁ w).inter (o₂ w)
    · filter_upwards [e₁, e₂] with w f₁ f₂
      rw [f₁, f₂, inf_idem]
  have mA : ∀ {u}, u ∈ A → ∀ w, atW w u ∈ L₁ w ⊓ L₂ w := fun hu w =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hu w)
  refine ⟨A ⊓ A.comap (thP E a b), ?_, fun u hu y => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hA.inter (hA.preimage continuous_thP)
  · have hu₁ := mA hu.1
    have hu₂ := mA (Subgroup.mem_comap.1 hu.2)
    have key : ∀ (w : Pl E) (f : GLw a w × GLw b w → ℂ) (k k' x : GLw a w × GLw b w),
        (∀ c ∈ ({k⁻¹, k'} : Set _), ∀ x, f (c * x) = f x ∧ f (x * c) = f x) → f (k⁻¹ * x * k') = f x := by
      intro w f k k' x h
      rw [(h k' (by simp) _).2, (h k⁻¹ (by simp) _).1]
    unfold finFn
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    have m₁ : atW w (u⁻¹ * y * thP E a b u) = (atW w u)⁻¹ * atW w y * atW w (thP E a b u) := by
      simp only [← atHom_apply, map_mul, map_inv]
    have m₂ : atW w (thP E a b (u⁻¹ * y * thP E a b u)) =
        (atW w (thP E a b u))⁻¹ * atW w (thP E a b y) * atW w u := by
      simp only [← atHom_apply, map_mul, map_inv, thP_thP]
    rw [m₁, m₂, key w (φ₁ w), key w (φ₂ w)]
    · intro c hc x
      rcases hc with rfl | rfl
      · exact i₂ w _ (inv_mem (hu₂ w).2) x
      · exact i₂ w _ (hu₁ w).2 x
    · intro c hc x
      rcases hc with rfl | rfl
      · exact i₁ w _ (inv_mem (hu₁ w).1) x
      · exact i₁ w _ (hu₂ w).1 x

end GlobalTheory.CompanionTheory.FinLevelTw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionFieldOfPointCoordsTop
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.GenTop

theorem appLE_fromSpecResidueField {X : Scheme.{0}} {U : X.Opens} (x : X) (hx : x ∈ U)
    (h : ⊤ ≤ X.fromSpecResidueField x ⁻¹ᵁ U) :
    (X.fromSpecResidueField x).appLE U ⊤ h = X.evaluation U x hx ≫ (Scheme.ΓSpecIso _).inv := by
  have h' : ⊤ ≤ Spec.map (X.residue x) ⁻¹ᵁ (X.fromSpecStalk x ⁻¹ᵁ U) := h
  have e : X.fromSpecResidueField x = Spec.map (X.residue x) ≫ X.fromSpecStalk x := rfl
  have := Scheme.Hom.appLE_comp_appLE (Spec.map (X.residue x)) (X.fromSpecStalk x) U (X.fromSpecStalk x ⁻¹ᵁ U) ⊤ le_rfl h'
  rw [appLE_of_eq e U ⊤ h (h'.trans le_rfl), ← this, ← Scheme.Hom.app_eq_appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, Scheme.Hom.map_appLE]
  rw [← Scheme.germ_residue, Category.assoc, Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem pullRatio_SpecMap_fromSpec {N : ℕ} (i : Fin (N + 1)) {R : CommRingCat.{0}}
    (ψ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ R)
    (h : ⊤ ≤ (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    pullRatio (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⊤ i h j =
      (Scheme.ΓSpecIso R).inv (ψ (ratio ℤ N i j)) := by
  have h1 : (isAffineOpen_chart ℤ N i).fromSpec.appLE (chart ℤ N i) ⊤
      (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h3 := Scheme.Hom.appLE_comp_appLE (Spec.map ψ) (isAffineOpen_chart ℤ N i).fromSpec
    (chart ℤ N i) ⊤ ⊤ (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge le_rfl
  unfold pullRatio
  rw [← h3, h1]
  have := congrArg (fun q => q.hom (ratio ℤ N i j)) (Scheme.ΓSpecIso_inv_naturality ψ)
  exact this.symm

theorem surjective_of_factor {X : Scheme.{0}} (x : X) {F : Type} [Field F]
    (ι : CommRingCat.of F ⟶ X.residueField x) (G : Spec (.of F) ⟶ X)
    (h : Spec.map ι ≫ G = X.fromSpecResidueField x) : Function.Surjective ι.hom := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective G
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  have hz : z = x := by
    have e := congrArg (fun f : Spec (X.residueField x) ⟶ X => f default) h
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hz
  rw [← Category.assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (φ ≫ ι) = Spec.map (𝟙 _) := by
    rw [← cancel_mono (X.fromSpecResidueField _), Spec.map_id, Category.id_comp]
    exact h
  have h3 : φ ≫ ι = 𝟙 _ := Spec.map_injective h2
  intro a
  refine ⟨φ.hom a, ?_⟩
  have := congrArg (fun q => q.hom a) h3
  simpa using this

theorem blockFnField_ptCoord_eq_top (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n)
    [CharZero ((MP ℤ m n).residueField x)] : blockFnField (ptCoord x) = ⊤ := by
  have hone : ∀ k, ptCoord x ⟨k, ptChart x k⟩ = 1 := fun k => by
    simp only [ptCoord, pullRatio_self, map_one]
  have hmem : ∀ p, ptCoord x p ∈ blockFnField (ptCoord x) := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, by rw [hone, div_one]⟩
  let F := blockFnField (ptCoord x)
  let r : ∀ k, Fin (n k + 1) → F := fun k j => ⟨ptCoord x ⟨k, j⟩, hmem _⟩
  have hr : ∀ k, r k (ptChart x k) = 1 := fun k => Subtype.ext (hone k)
  let ρ : ∀ k, Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k)) ⟶ CommRingCat.of F := fun k =>
    CommRingCat.ofHom (R := Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k))) (S := F)
      (chartLift (ptChart x k) (Int.castRingHom F) (r k))
  let g : ∀ k, Spec (CommRingCat.of F) ⟶ projectiveSpace ℤ (n k) := fun k =>
    Spec.map (ρ k) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec
  let G : Spec (CommRingCat.of F) ⟶ MP ℤ m n :=
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (Spec.map (CommRingCat.ofHom (Int.castRingHom F))) g
      (fun _ => specZIsTerminal.hom_ext _ _)
  let ι : CommRingCat.of F ⟶ (MP ℤ m n).residueField x := CommRingCat.ofHom F.val.toRingHom
  have key : Spec.map ι ≫ G = (MP ℤ m n).fromSpecResidueField x := by
    refine GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_
    rw [Category.assoc, GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr]
    have hx := mem_ptChart x k
    have h₂' : ⊤ ≤ (MP ℤ m n).fromSpecResidueField x ⁻¹ᵁ blockChart n k (ptChart x k) := fun s _ => by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hx
    have e1 : Spec.map ι ≫ g k = Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec := by
      rw [Spec.map_comp, Category.assoc]
    have h₁ : ⊤ ≤ (Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec) ⁻¹ᵁ
        chart ℤ (n k) (ptChart x k) := by
      rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
      exact le_top
    rw [e1]
    refine GlobalTheory.ProjSpace.hom_ext (specZIsTerminal.hom_ext _ _) fun _ =>
      ⟨⊤, trivial, ptChart x k, h₁, by rw [Scheme.Hom.comp_preimage]; exact h₂', fun j => ?_⟩
    rw [pullRatio_SpecMap_fromSpec]
    have e2 := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k) (hi := le_rfl)
      (j := j) ((MP ℤ m n).fromSpecResidueField x) h₂'
    refine Eq.trans ?_ e2
    rw [appLE_fromSpecResidueField x hx]
    show _ = (Scheme.ΓSpecIso _).inv (ptCoord x ⟨k, j⟩)
    congr 1
    show F.val (chartLift (ptChart x k) (Int.castRingHom F) (r k) (ratio ℤ (n k) (ptChart x k) j)) = _
    rw [chartLift_ratio _ _ (hr k)]
    rfl
  have hs := surjective_of_factor x ι G key
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨b, rfl⟩ := hs a
  exact b.2

end GlobalTheory.CompanionTheory.MPDict.GenTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlaces
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittPf

private theorem tensorBasis_repr_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (c : R) (e : E) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m = c * algebraMap F R (b.repr e m) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Algebra.smul_def]

private theorem eq_sum_repr_tmul_basis {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (z : R ⊗[F] E) :
    z = ∑ k, ((Algebra.TensorProduct.basis R b).repr z k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem tensorBasis_repr_sum_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) {ι : Type} (s : Finset ι)
    (f : ι → R ⊗[F] E) (h : ∀ x ∈ s, ∀ m, (Algebra.TensorProduct.basis R b).repr (f x) m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (∑ x ∈ s, f x) m ∈ O := by
  rw [map_sum, Finsupp.finsetSum_apply]
  exact O.sum_mem fun x hx => h x hx m

private theorem tensorBasis_repr_tmul_mem_of_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (c : R) (e : E) (hc : c ∈ O)
    (he : ∀ m, algebraMap F R (b.repr e m) ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m ∈ O := by
  rw [tensorBasis_repr_tmul]
  exact O.mul_mem hc (he m)

private theorem tensorBasis_repr_mul_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R)
    (hb : ∀ k l m, algebraMap F R (b.repr (b k * b l) m) ∈ O) (z w : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O)
    (hw : ∀ m, (Algebra.TensorProduct.basis R b).repr w m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m ∈ O := by
  rw [eq_sum_repr_tmul_basis b z, eq_sum_repr_tmul_basis b w, Finset.sum_mul_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun l _ m'' => ?_) m') m
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (O.mul_mem (hz k) (hw l)) (hb k l) m''

private theorem tensorBasis_repr_sigR_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (σ : E →ₐ[F] E)
    (hs : ∀ k m, algebraMap F R (b.repr (σ (b k)) m) ∈ O) (z : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ z) m ∈ O := by
  rw [eq_sum_repr_tmul_basis b z, map_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => ?_) m
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (hz k) (hs k) m'

theorem hermOf_sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ),
    2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
        hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn d b T hT
  have intF : ∀ t : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) t ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    intro t
    filter_upwards [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b t] with v hv
    have h0 := hv 0 (fun a i k => by simp)
    simpa [qR, hR, Formalism.UG.hform] using h0
  have hdiag := Filter.eventually_all.2 fun i : Fin n =>
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b ((1 / 2) * Algebra.trace F E (T i i))
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k l m,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => Filter.eventually_all.2 fun m => intF _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k m,
      algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun m => intF _
  have h3 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ p q m,
      algebraMap F (Fv F v) (b.repr (J p q) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q => Filter.eventually_all.2 fun m => intF _
  have h4 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j m,
      algebraMap F (Fv F v) (b.repr (T i j) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun m => intF _
  filter_upwards [hdiag, h1, h2, h3, h4] with v hd hb hs hJv hTv
  intro X hX
  clear intF hdiag h1 h2 h3 h4
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  unfold latH gramH
  refine ⟨fun i => ?_, fun i j _ k => ?_⟩
  · have hX' := hd i (fun _ => X i) (fun _ a k => hX i a k)
    convert hX' using 1
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, qR, Matrix.map_apply, map_sub, mul_sub]
    congr 1
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, map_mul]
  · let O : Subring (Fv F v) := (HeightOneSpectrum.adicCompletionIntegers F v).toSubring
    have gX : ∀ a p m, (Algebra.TensorProduct.basis (Fv F v) b).repr (X a p) m ∈ O := fun a p m => hX a p m
    have gI : ∀ e : E, (∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ O) →
        ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) e) m ∈ O := by
      intro e he m
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [tensorBasis_repr_tmul, one_mul]
      exact he m
    have gH : ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (hR (Fv F v) σ J (X i) (X j)) m ∈ O := by
      intro m
      simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply]
      exact tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun p _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun q _ m'' =>
        tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (fun m3 => tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (tensorBasis_repr_sigR_mem_of_repr_mem b O σ hs _ (gX i p))
          (gI _ (hJv p q)) m3) (gX j q) m'') m') m
    have gT := gI (T i j) (hTv i j)
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, Matrix.map_apply, map_sub,
      Finsupp.coe_sub, Pi.sub_apply]
    exact O.sub_mem (gT k) (gH k)

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal Matrix

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramNear (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (U : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ u ∈ U, (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X = (u : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def gramTest (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (ρ : HermR R σ n → ℝ)
    (X : Fin n → Fin M → R ⊗[F] E) : ℝ := by
  classical
  exact if h : (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X ∈ HermR R σ n then ρ ⟨_, h⟩ else 0

end Loc

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxF {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxF A).indicator (fun _ => (1 : ℂ)) (projFin X)

def intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (AF F) σ n) :=
  {B | ∀ v, v ∉ S → projV v (projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) ∈ latV (M := n) (n := n) b v}

def coefS (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ B, (intH σ b S).indicator (fun _ => (1 : ℂ)) B *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ B * ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))) ∂db

end Adelic

end GlobalTheory.CompanionTheory.WhitFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProduct
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.HaarSplit

open GroundTheory.Automorphic.Reduction in

theorem map_prod_eq_smul (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ha : 0 < a)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL E a)) [ν.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ := by
  obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph E a ha
  have hfun : (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e := by
    funext p
    exact (he p.1 p.2).symm
  rw [hfun]
  set m : Measure (GA E a) := Measure.map e (ν.prod volume) with hm
  have hemeas : Measurable e := e.continuous.measurable
  have hinv : m.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := e.surjective g
    have hcomp : (fun x => e (y, s) * x) ∘ e = e ∘ Prod.map (fun x => y * x) (fun t => s + t) := by
      funext p
      obtain ⟨x, t⟩ := p
      simp only [Function.comp, Prod.map, he]
      rw [splitCentre_add, Subgroup.coe_mul]
      rw [mul_assoc, mul_assoc, ← mul_assoc (y : GA E a), ← splitCentre_comm, mul_assoc]
    have hpres : MeasurePreserving (Prod.map (fun x : normOneGL E a => y * x) (fun t : ℝ => s + t))
        (ν.prod volume) (ν.prod volume) :=
      (measurePreserving_mul_left ν y).prod (measurePreserving_add_left volume s)
    rw [hm, Measure.map_map (by fun_prop) hemeas, hcomp, ← Measure.map_map hemeas hpres.measurable, hpres.map_eq]
  have hfin : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    change Measure.map e.toMeasurableEquiv (ν.prod volume) K < ⊤
    rw [e.toMeasurableEquiv.map_apply]
    exact (e.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  have hopen : m.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hhaar : m.IsHaarMeasure := { }
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure m μ
  refine ⟨(Measure.haarScalarFactor m μ : NNReal), ENNReal.coe_ne_zero.2 hc.ne', ENNReal.coe_ne_top, ?_⟩
  exact Measure.isMulLeftInvariant_eq_smul m μ

end GlobalTheory.CompanionTheory.HaarSplit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExistsStatement
section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_solution_exists : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C → ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧ C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesTracePairingStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_coordinates_trace_pairing : ∀ (D : D7) (r : ℕ) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∃ (n : ℕ) (c : (Fin n → AF D.host.F) ≃ₜ+ hermA D r) (u : Mx D r r → Fin n → AF D.host.F) (R : (Fin n → AF D.host.F) → Mx D r r), Continuous u ∧ Continuous R ∧ (∀ x : Mx D r r, x ∈ hermA D r → R (u x) = x) ∧ (∀ (v : Fin n → AF D.host.F) (x : Mx D r r), halfTr (Matrix.trace (HMul.hMul (c v).1 x : Mx D r r)) = v ⬝ᵥ u x) ∧ GlobalTheory.SWLit.IsTamagawa D.host.F (Fin n) (lam.map c.symm) := by
  first | exact @GlobalTheory.CompanionTheory.HermCoord.coords | exact GlobalTheory.CompanionTheory.HermCoord.coords | (intros; apply GlobalTheory.CompanionTheory.HermCoord.coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslateStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_right_translate_toL2 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (φ ψ : G → ℂ) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ) (c : ℝ → G), Continuous φ → Continuous ψ → Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → (∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) → ∀ t, HasDerivAt (fun s => R Γ μ (c s) hφ.toL2) (R Γ μ (c t) hψ.toL2) t := by
  first | exact @GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R | exact GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R | (intros; apply GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R <;> assumption)
end

