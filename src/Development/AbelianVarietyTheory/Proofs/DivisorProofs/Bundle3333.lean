import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3322
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentGradedFamilyNonzeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeDescent_gradedFamily_nonzero : ∀ σ : Setup, GradedFam σ.c₀ σ.N ∧ ∃ k, 1 ≤ k ∧ ∃ b ∈ σ.N k, b ≠ 0 := by
  first | exact @GlobalTheory.DescGraded.gradedFam_and_ne_zero | exact GlobalTheory.DescGraded.gradedFam_and_ne_zero | (intros; apply GlobalTheory.DescGraded.gradedFam_and_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeNoPrimitiveO2
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.NoPrimNoeth

theorem injective_of_algClosure (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] N)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Function.Injective (f.baseChange K)) :
    Function.Injective f := by
  obtain ⟨g, hg⟩ : ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by
    refine GlobalTheory.split_injective_of_forall_lTensor_residueField_injective f fun m hm => ?_
    let k := AlgebraicClosure m.ResidueField
    have hinj := h k
    have e : (AlgebraTensorModule.cancelBaseChange R m.ResidueField m.ResidueField k N) ∘
          ((f.baseChange m.ResidueField).lTensor k) =
        (f.lTensor k) ∘ (AlgebraTensorModule.cancelBaseChange R
          m.ResidueField m.ResidueField k M) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        m.ResidueField m.ResidueField (M := k) f) x).symm
    have h1 : Function.Injective ((f.baseChange m.ResidueField).lTensor k) :=
      Function.Injective.of_comp (e ▸ (hinj.comp (LinearEquiv.injective _)))
    haveI : Module.FaithfullyFlat m.ResidueField k :=
      (fun (F L : Type) [Field F] [Field L] [Algebra F L] ↦ (inferInstance : Module.FaithfullyFlat F L)) _ _
    exact (Module.FaithfullyFlat.lTensor_injective_iff_injective m.ResidueField k _).1 h1
  exact Function.LeftInverse.injective (g := g) fun x ↦ LinearMap.congr_fun hg x

theorem abelian_scheme_second_cohomology_finite_projective (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO2 A.hom) ∧ Module.Projective R (HO2 A.hom)) ∧ StructureSheafH2BaseChange A.hom := by
  have hsm : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have H := GlobalTheory.T.structure_cohomology_residue_field_fibre R A.left A.hom hA.proper inferInstance (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA) (by
    intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hp w
    obtain ⟨_, -, h1, h2⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R' (algebraMap R R') A X' s' φ hp
    exact GlobalTheory.T.abelianSchemeSpecialFibre_cohomology_lift_artinian R' (Over.mk s' : Over (Sp R')) g (h1 hA) (h2 g hg) k (α : R' →+* k) hα X₀ s₀ ψ w)
  exact ⟨H.2.1, H.2.2.2⟩

theorem pull_comm {R K : Type} [CommRing R] [CommRing K] {σ : R →+* K} {A A' : Over (Sp R)} {B B' : Over (Sp K)}
    {pr : B.left ⟶ A.left} {pr' : B'.left ⟶ A'.left} (h : pr ≫ A.hom = B.hom ≫ spMap σ)
    (h' : pr' ≫ A'.hom = B'.hom ≫ spMap σ) (f : A' ⟶ A) (f' : B' ⟶ B) (e : f'.left ≫ pr = pr' ≫ f.left)
    (c : HO2 A.hom) : pullHO2 h' (structureSheafH2Pullback f c) = structureSheafH2Pullback f' (pullHO2 h c) := by
  have h'' : (pr' ≫ f.left) ≫ A.hom = B'.hom ≫ spMap σ := by rw [Category.assoc, Over.w f, h']
  have a1 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R _ _ A.hom A'.hom (RingHom.id R) f.left (ovw f) K _ B'.hom σ pr' h' σ _ h''
    rfl (fun _ ↦ rfl)).2.1 c
  have a2 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R K _ _ A.hom B.hom σ pr h K _ B'.hom (RingHom.id K) f'.left (ovw f') σ _ h''
    e.symm (fun _ ↦ rfl)).2.1 c
  exact a1.trans a2.symm

theorem noPrimO2_of_isNoetherianRing : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → NoPrimitiveStructureSheafH2 A := by
  intro R _ _ A _ g hA hg
  obtain ⟨⟨_, _⟩, bc⟩ := abelian_scheme_second_cohomology_finite_projective R A g hA hg
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨⟨_, _⟩, bc2⟩ := abelian_scheme_second_cohomology_finite_projective R (A ⊗ A) (g + g) hA2 hg2
  let D : HO2 A.hom →ₗ[R] HO2 (A ⊗ A).hom := structureSheafH2Pullback μ[A] - structureSheafH2Pullback (fst A A) - structureSheafH2Pullback (snd A A)
  have hD : Function.Injective D := by
    refine injective_of_algClosure R _ _ D fun K _ _ _ ↦ ?_
    obtain ⟨B, _, pr, pr', hB, hgB, p1, p2, eμ, e1, e2, -, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R K A g hA hg
    obtain ⟨e, he⟩ := bc K _ _ _ p1
    obtain ⟨e', he'⟩ := bc2 K _ _ _ p2
    have hN := (GlobalTheory.T.abelian_variety_wedge_no_primitive_h2 K B g hB hgB).2
    let DB : HO2 B.hom →ₗ[K] HO2 (B ⊗ B).hom := structureSheafH2Pullback μ[B] - structureSheafH2Pullback (fst B B) - structureSheafH2Pullback (snd B B)
    have key : ∀ x, e' (D.baseChange K x) = DB (e x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a c =>
        have : a ⊗ₜ[R] c = a • ((1 : K) ⊗ₜ[R] c) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, map_smul, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, he, he']
        congr 1
        simp only [D, DB, LinearMap.sub_apply, map_sub]
        rw [pull_comm p1.w p2.w _ _ eμ, pull_comm p1.w p2.w _ _ e1, pull_comm p1.w p2.w _ _ e2]
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : DB (e x) = 0 := by rw [← key, hx, map_zero]
    have h1 : e x = 0 := hN _ (by
      simp only [DB, LinearMap.sub_apply] at h0
      rw [sub_sub, sub_eq_zero] at h0
      exact h0)
    exact e.map_eq_zero_iff.1 h1
  intro z hz
  refine (injective_iff_map_eq_zero D).1 hD z ?_
  simp only [D, LinearMap.sub_apply]
  rw [hz]; abel

end GlobalTheory.AbCoh.NoPrimNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfHodgeDeRhamStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeSquareZeroLifts_of_hodgeDeRham : CrystallineSmoothLift → AbelianHodgeDeRham → AbelianSchemeLifts := by
  first | exact @GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham | exact GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham | (intros; apply GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnectedStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), G.IsConn → Function.Surjective (omegaMap G H q) → ∀ n, Function.Surjective (q.app n) := by
  first | exact @GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective | exact GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective | (intros; apply GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionIntegralFrame
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore.Bdry

theorem nval_evI_eq_zero : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ s.sig) = 0 := by
  intro hP hQ2 hQ3 E _ _ _ H Dw l Xo c r U x hL Z τ s T io y₀ hv hZ
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.T.exists_archimedean_section_flat hP hQ2 hQ3 E H Dw l Xo c r U x hL Z τ ⟨s⟩
  obtain ⟨a, ha, hsa⟩ := GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight E H Dw l Xo c r U x hL.unf hL.geo Z (flatWt Dw τ) s₀ s
  have h0 : io a ≠ 0 := (map_ne_zero io).2 ha
  rw [hsa, evI_smul, nval_mul, hs₀ T io y₀ hv hZ, nval_of_ne h0, hv a ha]
  simp

end GlobalTheory.FlatCore.Bdry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem hasDim_iff_clo {Y : Scheme.{0}} (y : Y) (e : ℕ) : HasDim y e ↔ topologicalKrullDim (clo y) = (e : ℕ) := by
  have hemb := (cloι y).isClosedEmbedding
  have hr : Set.range (cloι y) = closure ({y} : Set Y) := by
    rw [← Set.image_univ, ← (genericPoint_spec (clo y)).def, ← hemb.isClosedMap.closure_image_eq_of_continuous
      hemb.continuous, Set.image_singleton, cloι_genericPoint]
  have h := (hemb.toIsEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq
  unfold HasDim
  rw [h, hr]

theorem heightProj : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H'
  have key : ∀ (n : ℕ) (w : Y), HasDim w (n + 1) → h' w = (π.residueDegree w : ℝ) * h (π w) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact GlobalTheory.T.arithHeight_projectionFormula_pointCurve k X Y p q D E hX hY π hπ L h h' H H' w hc hw
    | succ m ih =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact GlobalTheory.T.arithHeight_projectionFormula_inductiveStep k X Y p q D E hX hY π hπ L h h' H H' w m hc hw ih
  intro y
  rcases hY.vertical_or_horizontal (cloι y) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
  · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' y l hl
  · exact key e y ((hasDim_iff_clo y (e + 1)).2 he)

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelUpperBoundCountRankAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.HSUpper

noncomputable def polyComb {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ) :
    (Fin δ → MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) →ₗ[ℤ] K :=
  ∑ i : Fin δ, LinearMap.mulRight ℤ (w i) ∘ₗ (MvPolynomial.aeval x).toLinearMap ∘ₗ
    (MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n).subtype ∘ₗ LinearMap.proj i

theorem polyComb_apply {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ) (T) :
    polyComb x w n T = ∑ i, MvPolynomial.aeval x (T i : MvPolynomial (Fin (D + 1)) ℤ) * w i := by
  simp [polyComb]

theorem fg_finrank_le {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ)
    (H : AddSubgroup K) (hH : ∀ f ∈ H, ∃ T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ,
      (∀ i, (T i).IsHomogeneous n) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i) :
    H.FG ∧ Module.finrank ℤ H ≤ δ * (n + D).choose D := by
  obtain ⟨-, -, -, hrk, hfin⟩ := GlobalTheory.T.card_bounded_homogeneous_int_form_families D n δ 0 le_rfl
  haveI := hfin
  haveI : Module.Free ℤ (MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) :=
    Module.free_of_finite_type_torsion_free'
  set Φ := polyComb x w n
  have hle : ∀ f ∈ H, f ∈ LinearMap.range Φ := by
    intro f hf
    obtain ⟨T, hT, rfl⟩ := hH f hf
    refine ⟨fun i => ⟨T i, (MvPolynomial.mem_homogeneousSubmodule n (T i)).2 (hT i)⟩, ?_⟩
    simp [Φ, polyComb_apply]
  let g : H →ₗ[ℤ] LinearMap.range Φ :=
    { toFun := fun f => ⟨f.1, hle f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun m f => by ext; simp }
  have hg : Function.Injective g := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI : Module.Finite ℤ H := Module.Finite.of_injective g hg
  refine ⟨(AddGroup.fg_iff_addSubgroup_fg H).1 (Module.Finite.iff_addGroup_fg.1 inferInstance), ?_⟩
  calc Module.finrank ℤ H ≤ Module.finrank ℤ (LinearMap.range Φ) := LinearMap.finrank_le_finrank_of_injective hg
    _ ≤ Module.finrank ℤ (Fin δ → MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) := LinearMap.finrank_range_le Φ
    _ = δ * (n + D).choose D := by
      rw [Module.finrank_pi_fintype, hrk]; simp

end GlobalTheory.HSAmp.HSUpper

theorem GlobalTheory.HSAmp.HSUpper.upper_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (P.H (e * q + a) b).FG ∧ Module.finrank ℤ (P.H (e * q + a) b) ≤ Module.finrank (ratF x) X.functionField * (q + c + D).choose D ∧ ∀ R κ : ℝ, 0 ≤ R → 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (P.Bl (e * q + a) b R).Finite ∧ (P.Bl (e * q + a) b R).ncard ≤ (2 * ⌊C * R / κ ^ (q + c)⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + c + D).choose D) := by
  intro k _ X _ p D hD P hA e x hx a b
  obtain ⟨c, w, C, hC, hrep⟩ := GlobalTheory.T.sections_eq_sum_aeval_boundedIntCoeff_ample k X p D hD P hA e x hx a b
  refine ⟨c, C, hC, fun q => ?_⟩
  obtain ⟨hfg, hrk⟩ := GlobalTheory.HSAmp.HSUpper.fg_finrank_le x w (q + c) (P.H (e * q + a) b) (fun f hf => by
    obtain ⟨T, hT, hf', -⟩ := hrep q f hf
    exact ⟨T, hT, hf'⟩)
  refine ⟨hfg, hrk, fun R κ hR hκ hcov => ?_⟩
  set R' : ℝ := C * R / κ ^ (q + c)
  have hR' : 0 ≤ R' := div_nonneg (mul_nonneg hC.le hR) (pow_pos hκ _).le
  obtain ⟨hSfin, hScard, -⟩ := GlobalTheory.T.card_bounded_homogeneous_int_form_families D (q + c) (Module.finrank (ratF x) X.functionField) R' hR'
  set S := {T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ |
    (∀ i, (T i).IsHomogeneous (q + c)) ∧ ∀ i α, |((MvPolynomial.coeff α (T i) : ℤ) : ℝ)| ≤ R'}
  have hsub : P.Bl (e * q + a) b R ⊆
      (fun T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ =>
        ∑ i, MvPolynomial.aeval x (T i) * w i) '' S := by
    intro f hf
    rw [← ballIn_H] at hf
    obtain ⟨hfH, hfR⟩ := hf
    obtain ⟨T, hT, hfT, hbd⟩ := hrep q f hfH
    exact ⟨T, ⟨hT, hbd R κ hκ hcov hfR⟩, hfT.symm⟩
  have himfin := hSfin.image (fun T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ =>
        ∑ i, MvPolynomial.aeval x (T i) * w i)
  refine ⟨himfin.subset hsub, ?_⟩
  calc (P.Bl (e * q + a) b R).ncard ≤ _ := Set.ncard_le_ncard hsub himfin
    _ ≤ S.ncard := Set.ncard_image_le hSfin
    _ = _ := hScard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingNoetherianAbelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.AxesSq

theorem surj_of_comp {R R' : Type} [CommRing R] [CommRing R'] {X X' X₀ : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R}
    {s₀ : X₀ ⟶ Sp R'} {σ : R →+* R'} (e : X ⟶ X') (ψ : X₀ ⟶ X)
    (he : e ≫ s' = s ≫ spMap (RingHom.id R)) (hψ : ψ ≫ s = s₀ ≫ spMap σ) (hc : (ψ ≫ e) ≫ s' = s₀ ≫ spMap σ) :
    (Function.Surjective (pullHO1 hc) → Function.Surjective (pullHO1 hψ)) ∧
    (Function.Surjective (pullHO2 hc) → Function.Surjective (pullHO2 hψ)) := by
  have H := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R X' X s' s (RingHom.id R) e he R' X₀ s₀ σ ψ hψ σ (ψ ≫ e) hc rfl (fun _ ↦ rfl))
  refine ⟨fun h y ↦ ?_, fun h y ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := h y
    exact ⟨pullHO1 he a, H.1 a⟩
  · obtain ⟨a, rfl⟩ := h y
    exact ⟨pullHO2 he a, H.2.1 a⟩

theorem fp_bc1 (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom)) ∧ StructureSheafH1BaseChange A.hom := by
  haveI : Smooth A.hom := hA.smooth
  haveI : IsProper A.hom := hA.proper
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.structure_cohomology_residue_field_fibre R A.left A.hom inferInstance inferInstance (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA)
    (by
      intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hφ w
      obtain ⟨B, _, pr, -, hB, hBg, hpb, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R R' A g hA hg
      let e : B.left ≅ X' := IsPullback.isoIsPullback _ _ hpb hφ
      have he2 : e.hom ≫ s' = B.hom := IsPullback.isoIsPullback_hom_snd A.left (Sp R') hpb hφ
      have he : e.inv ≫ B.hom = s' ≫ spMap (RingHom.id R') := by
        rw [← he2, Iso.inv_hom_id_assoc]
        first | (rw [spMap_id, Category.comp_id]) | (simp [spMap, CommRingCat.ofHom_id]) | (rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
      have w' : IsPullback (ψ ≫ e.inv) s₀ B.hom (spMap (α : R' →+* k)) := by
        refine IsPullback.of_iso w (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [← he2]
      obtain ⟨s1, s2⟩ := GlobalTheory.T.abelianSchemeSpecialFibre_cohomology_lift_artinian R' B g hB hBg k α hα X₀ s₀ (ψ ≫ e.inv) w'
      have hc := surj_of_comp (s := s') (s' := B.hom) e.inv ψ he w.w w'.w
      exact ⟨hc.1 s1, hc.2 s2⟩)
  exact ⟨h1, h3⟩

theorem pull1_congr {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {σ : R →+* R'} {φ₁ φ₂ : X' ⟶ X} (hφ : φ₁ = φ₂) (h₁ : φ₁ ≫ s = s' ≫ spMap σ) (h₂ : φ₂ ≫ s = s' ≫ spMap σ)
    (c : HO1 s) : pullHO1 h₁ c = pullHO1 h₂ c := by
  subst hφ; rfl

def axesMap {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] :
    HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
  LinearMap.prod (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)))

theorem pO1_bc {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {A Y : Over (Sp R)} {B Z : Over (Sp K)}
    (f : Y ⟶ A) (f' : Z ⟶ B) (pr : Z.left ⟶ Y.left) (pr' : B.left ⟶ A.left)
    (hpb : pr ≫ Y.hom = Z.hom ≫ spMap (algebraMap R K)) (hpb' : pr' ≫ A.hom = B.hom ≫ spMap (algebraMap R K))
    (hc : f'.left ≫ pr' = pr ≫ f.left) (c : HO1 A.hom) :
    pO1 f' (pullHO1 hpb' c) = pullHO1 hpb (pO1 f c) := by
  have h1 : (f'.left ≫ pr') ≫ A.hom = Z.hom ≫ spMap (algebraMap R K) := by
    rw [Category.assoc, hpb', ← Category.assoc, Over.w]
  have h2 : (pr ≫ f.left) ≫ A.hom = Z.hom ≫ spMap (algebraMap R K) := by rw [← hc]; exact h1
  have E1 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R K A.left B.left A.hom B.hom (algebraMap R K) pr' hpb' K Z.left Z.hom (RingHom.id K)
    f'.left (ovw f') (algebraMap R K) (f'.left ≫ pr') h1 rfl (fun _ ↦ rfl)).1 c
  have E2 := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id.1 R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) K Z.left Z.hom (algebraMap R K)
    pr hpb (algebraMap R K) (pr ≫ f.left) h2 rfl (fun _ ↦ rfl)).1 c
  unfold pO1
  rw [E1, E2]
  exact pull1_congr hc h1 h2 c

theorem axesMap_baseChange_injective (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (K : Type) [Field K] [IsAlgClosed K] [Algebra R K] :
    Function.Injective ((axesMap A).baseChange K) := by
  obtain ⟨hsq, hsqg⟩ := (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨B, _, pr, pr', hB, hBg, hpb, hpb', -, -, -, h1, h2⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R K A g hA hg
  obtain ⟨eS, heS⟩ := (fp_bc1 R (A ⊗ A) (g + g) hsq hsqg).2 K _ _ pr' hpb'
  obtain ⟨eA, heA⟩ := (fp_bc1 R A g hA hg).2 K _ _ pr hpb
  have key : ∀ (f : A ⟶ A ⊗ A) (f' : B ⟶ B ⊗ B), f'.left ≫ pr' = pr ≫ f.left →
      ∀ z, pO1 f' (eS z) = eA ((pO1 f).baseChange K z) := by
    intro f f' hc z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      have : a ⊗ₜ[R] c = a • ((1 : K) ⊗ₜ[R] c) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, map_smul, heS, heA]
      congr 1
      exact pO1_bc f f' pr pr' hpb.w hpb'.w hc c
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨-, -, -, -, hax⟩ := GlobalTheory.T.structureSheafCohomology_abelianVariety_algClosed K B g hB hBg
  intro z z' hzz
  rw [← sub_eq_zero] at hzz ⊢
  rw [← map_sub] at hzz
  generalize z - z' = w at hzz ⊢
  have hfst : (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))).baseChange K w = 0 := by
    have := congrArg ((LinearMap.fst R (HO1 A.hom) (HO1 A.hom)).baseChange K) hzz
    rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp] at this
  have hsnd : (pO1 (lift (toUnit A ≫ η[A]) (𝟙 A))).baseChange K w = 0 := by
    have := congrArg ((LinearMap.snd R (HO1 A.hom) (HO1 A.hom)).baseChange K) hzz
    rwa [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp] at this
  have e0 : eS w = 0 := by
    apply hax
    · have k1 := key (lift (𝟙 A) (toUnit A ≫ η[A])) (lift (𝟙 B) (toUnit B ≫ η[B])) h1 w
      rw [k1, hfst, map_zero]
    · have k2 := key (lift (toUnit A ≫ η[A]) (𝟙 A)) (lift (toUnit B ≫ η[B]) (𝟙 B)) h2 w
      rw [k2, hsnd, map_zero]
  simpa using congrArg eS.symm e0

theorem axesO1_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → AxesVanishingStructureSheafDegOne A := by
  intro R _ _ A _ g hA hg
  obtain ⟨hsq, hsqg⟩ := (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨⟨hS1, hS2⟩, -⟩ := fp_bc1 R (A ⊗ A) (g + g) hsq hsqg
  obtain ⟨⟨hA1, hA2⟩, -⟩ := fp_bc1 R A g hA hg
  let e1 : ULift.{1} (HO1 (A ⊗ A).hom) ≃ₗ[R] HO1 (A ⊗ A).hom := ULift.moduleEquiv
  let e2 : ULift.{1} (HO1 A.hom × HO1 A.hom) ≃ₗ[R] HO1 A.hom × HO1 A.hom := ULift.moduleEquiv
  let f : ULift.{1} (HO1 (A ⊗ A).hom) →ₗ[R] ULift.{1} (HO1 A.hom × HO1 A.hom) :=
    e2.symm.toLinearMap ∘ₗ axesMap A ∘ₗ e1.toLinearMap
  haveI : Module.Finite R (ULift.{1} (HO1 (A ⊗ A).hom)) := Module.Finite.equiv e1.symm
  haveI : Module.Projective R (ULift.{1} (HO1 (A ⊗ A).hom)) := Module.Projective.of_equiv e1.symm
  haveI : Module.Finite R (ULift.{1} (HO1 A.hom × HO1 A.hom)) := Module.Finite.equiv e2.symm
  haveI : Module.Projective R (ULift.{1} (HO1 A.hom × HO1 A.hom)) := Module.Projective.of_equiv e2.symm
  obtain ⟨r, hr⟩ := GlobalTheory.split_injective_of_forall_prime_baseChange_field_injective R _ _ f (by
    intro P
    refine ⟨AlgebraicClosure P.asIdeal.ResidueField, inferInstance, inferInstance, ?_, ?_⟩
    · have hk : RingHom.ker (algebraMap P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField)) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap P.asIdeal.ResidueField _).injective
      rw [IsScalarTower.algebraMap_eq R P.asIdeal.ResidueField (AlgebraicClosure P.asIdeal.ResidueField),
        ← RingHom.comap_ker, hk]
      exact Ideal.ker_algebraMap_residueField _
    · have hi := axesMap_baseChange_injective R A g hA hg (AlgebraicClosure P.asIdeal.ResidueField)
      simp only [f, LinearMap.baseChange_comp]
      exact (e2.symm.baseChange R _ _ _).injective.comp (hi.comp (e1.baseChange R _ _ _).injective))
  have hf : Function.Injective f := fun x y hxy ↦ by
    have := congrArg r hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hr, LinearMap.id_apply, LinearMap.id_apply] at this
  intro y hy1 hy2
  have h0 : f (e1.symm y) = f 0 := by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_zero]
    simp [axesMap, hy1, hy2]
  simpa using congrArg e1 (hf h0)

end GlobalTheory.AbCoh.AxesSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLPowerTorsionKernelEqLPartIsogenyDegreeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} = l ^ padicValNat l (deg f) := by
  first | (exact @GlobalTheory.AV.AbVar.card_kerLPart_eq) | (exact GlobalTheory.AV.AbVar.card_kerLPart_eq) | (intros; apply GlobalTheory.AV.AbVar.card_kerLPart_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsChartEqSpanStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierMultipleGlobalSections_chart_eq_span : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ), Sec (σ.D₁ x) k = spanBy (GlobalTheory.Desc.cst (σ.C x).G.hom) (σ.θ x '' σ.N k) := by
  first | exact @GlobalTheory.Desc.ChartSpan.sec_eq_spanBy | exact GlobalTheory.Desc.ChartSpan.sec_eq_spanBy | (intros; apply GlobalTheory.Desc.ChartSpan.sec_eq_spanBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsEqSpanRegularLatticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierMultipleGlobalSections_eq_span_regularLattice : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  first | exact @GlobalTheory.Desc.sec_eq_spanBy_N | exact GlobalTheory.Desc.sec_eq_spanBy_N | (intros; apply GlobalTheory.Desc.sec_eq_spanBy_N <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentSumEqZeroOfOrbitalIntegralEqZeroStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ (B : GlobalTheory.LKDef.DForm G) (y : GlobalTheory.LKCx.grp G B.β),
      orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.emb y) (fun h => f h.1 * f' h.2) = 0 →
      centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' y = 0 := by
  first | (exact @GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK) | (exact GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK) | (intros; apply GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK <;> assumption)
end

