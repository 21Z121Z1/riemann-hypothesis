import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0097

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosureStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projBundle_closure_alt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (J : Type) [Fintype J] (EE : M.Lat J) (s : J → Ω'), IsProjOver M.s → (∃ j, s j ≠ 0) → Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤ → ∃ (M' : RatModel o Ω') (f : M'.Z ⟶ M.Z), M.IsHom M' φ f ∧ IsProjOver M'.s ∧ ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty → (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) → (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 → ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧ M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_projBundle_closure | exact GlobalTheory.ZH.RatModel.exists_projBundle_closure | (intros; apply GlobalTheory.ZH.RatModel.exists_projBundle_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projSpace_map_of_local_sections_no_common_zero : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  first | exact @GlobalTheory.ZH.CoordMap.exists_coordMap | exact GlobalTheory.ZH.CoordMap.exists_coordMap | (intros; apply GlobalTheory.ZH.CoordMap.exists_coordMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAtStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pureWeight_section_ne_zero_at : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) := by
  first | exact @GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at | exact GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at | (intros; apply GlobalTheory.ZH.FibPre.exists_pure_ne_zero_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalBStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidified_cubical_symmetric_extension_normalBase : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], IsNormalScheme S → ∀ (U : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (a : A.left ⟶ G.left), IsGrpPullback A G j a → ∀ (L : RigLB A) (c : CubicalStr A L) (M : LB G.left), M.IsLB → LBIso (M.pull a) L.L → ∃ (L' : RigLB G) (c' : CubicalStr G L') (m : CubeMap A G), m.F = a ∧ m.e = j ∧ m.IsPullCubical c c' ∧ (L.IsSymmetric → L'.IsSymmetric) := by
  first | exact @GlobalTheory.NormalCubeExt.exists_cubical_extension | exact GlobalTheory.NormalCubeExt.exists_cubical_extension | (intros; apply GlobalTheory.NormalCubeExt.exists_cubical_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupportStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extending_torsionPoints_support : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧ h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι → x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀ := by
  first | exact @GlobalTheory.ZH.TorsionSection.exists_section | exact GlobalTheory.ZH.TorsionSection.exists_section | (intros; apply GlobalTheory.ZH.TorsionSection.exists_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsToStkAUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT

theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) (k : Fin 4) : DegPre.gtφ D F b χ k = b.left ≫ D.Oφ (𝟙 D.P.A) χ k := by
  rw [comp_Oφ_id]
  have h : padd D.P.A (DegPre.cF D F χ) b = padd D.P.A b (DegPre.cF D F χ) := _root_.mul_comm (DegPre.cF D F χ) b
  have h' : DegPre.gtφ D F b χ = D.Oφ b χ := by
    unfold DegPre.gtφ DegPre.Oφ
    rw [h]
  rw [h']

theorem Oφ_over {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (k : Fin 4) :
    D.Oφ (𝟙 D.P.A) χ k ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases k <;> exact Over.w _

theorem gs_scal {F : Type} [CommRing F] {Y : Scheme.{0}} (q : Y ⟶ Sp F) (r : Sp F ⟶ Y) (h : r ≫ q = 𝟙 _) (z : Sp F)
    (a : F) : gs r z ⊤ (scal q a) = toStkA z a :=
  (gs_pull r q z ⊤ trivial _).trans ((congrArg (fun t => gs t z ⊤ _) h).trans (gs_eq (𝟙 _) z ⊤ trivial _))

theorem toStkA_surj {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStkA z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s
  exact ⟨x, congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom hx⟩

theorem exists_toStkA_unit {F : Type} [Field F] (z : Sp F) (v : ((Sp F).presheaf.stalk z)ˣ) :
    ∃ t : F, t ≠ 0 ∧ toStkA z t = v.val := by
  obtain ⟨t, e⟩ := toStkA_surj z v.val
  exact ⟨t, fun e0 => v.ne_zero (by rw [← e, e0, map_zero]), e⟩

theorem top_le_of_mem {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U) :
    ⊤ ≤ x ⁻¹ᵁ U := fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ h

theorem exists_valF_secLin {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (h : Y ⟶ X)
    (q : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hq : r ≫ q = 𝟙 _) (x : Sp F ⟶ X) (hr : r ≫ h = x) (k : ℕ) {l l' : L.ι}
    (hl : ⊤ ≤ x ⁻¹ᵁ L.U l) (hl' : ⊤ ≤ x ⁻¹ᵁ L.U l') : ∃ τ : F, τ ≠ 0 ∧
      ∀ (σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ)))) (n : ℕ) (cc : Fin n → F)
        (σ : Fin n → H0 L k), GeneratorPullback.SecLin L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) σ'
          (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) σ h (fun i => scal q (cc i)) →
        valF r _ (σ'.f (fun _ => l)) = τ * ∑ i, cc i *
          valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => l')) ((σ i).f (fun _ => l')) := by
  subst hr
  let z : Sp F := cpt F
  obtain ⟨J, hJ, eJ⟩ := exists_good L hL z (fun _ : PUnit.{1} => r ≫ h) (fun _ => l')
    (fun _ _ _ => rfl) (fun _ => hl' trivial)
  replace eJ : J (r ≫ h) = l' := eJ PUnit.unit
  have hl₁ : ⊤ ≤ r ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => h) (fun _ => l) :=
    fun y hy => Set.mem_iInter.2 fun _ => hl hy
  have hl₂ : r z ∈ LB.wchart L (fun _ : Fin 1 => h) (fun _ => l') := Set.mem_iInter.2 fun _ => hl' trivial
  obtain ⟨τ, τ0, hτ⟩ := exists_toStkA_unit z (trF (L := L) (fun _ : Fin 1 => h)
    (fun _ => (k : ℤ)) r z (fun _ => l) (fun _ => l'))
  refine ⟨τ, τ0, fun σ' n cc σ hσ => (toStkA z).injective ?_⟩
  refine (toStkA_valR_eq_gs r _ z hl₁ _).trans ((sec_trans σ' r z (hl₁ trivial) hl₂).trans ?_)
  rw [map_mul, hτ, map_sum, ← sval_of σ' r z J (fun _ => l') (fun _ => eJ), ExpGTrans.secLin_val hσ r z hJ]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, sval_of (σ i) _ z J (fun _ => l') (fun _ => by rw [Category.comp_id, eJ])]
  exact congrArg₂ (· * ·) (gs_scal _ r hq z _)
    (toStkA_valR_eq_gs (r ≫ h) (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => l')) z
      (fun y hy => Set.mem_iInter.2 fun _ => hl' hy) _).symm

theorem exists_coef_secLin {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : Frm D F k g.b) (hw : w.IsGen) (z : Sp F)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) : ∃ κ : F, κ ≠ 0 ∧
      ∀ (s : Fam D F k) (χ : D.X) (n : ℕ) (cc : Fin n → F) (f : Fin n → D.SecB k χ),
        GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) (s.s χ) (D.famφB χ) (DegPre.famε k) f
          (DegPre.prB D F).left (fun i => scal (fst (TF (R := R) F) D.P.A).left (cc i)) →
        ∀ (b : Sp F ⟶ D.P.A.left) (jf jt : Fin 4 → D.P.L.ι), b = g.b.left → (∀ i, J (b ≫ D.famφB χ i) = jf i) →
          (∀ i, J (b ≫ D.Oφ (𝟙 _) χ i) = jt i) →
          coef s g w χ = κ * ∑ i, cc i * (valR b _ ((f i).f jf) * valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) := by
  obtain ⟨Rg, R0, hR⟩ := exists_toStkA_unit z (rigV D (TF (R := R) F).hom z J)
  obtain ⟨W, W0, hW⟩ := exists_toStkA_unit z (val w (𝟙 _) z J)
  refine ⟨W * (Rg ^ k)⁻¹, by simp [R0, W0], fun s χ n cc f hs b jf jt hb hjf hjt => ?_⟩
  let rb : Sp F ⟶ (DegPre.BF D F).left := (lift (𝟙 (TF (R := R) F)) g.b).left
  have hrb : rb ≫ (DegPre.prB D F).left = b :=
    (congrArg (fun t => t.left) (lift_snd (𝟙 (TF (R := R) F)) g.b)).trans hb.symm
  have hrb' : rb ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun t => t.left) (lift_fst (𝟙 (TF (R := R) F)) g.b)
  have hcf : IsCoef k g w χ (s.s χ) (coef s g w χ) := Classical.epsilon_spec
    (((CoefBasic.coef_basic R D F k g).2.2 w hw).1 χ (s.s χ)).exists
  have e := hcf z J hJ
  have a₁ : sval (s.s χ) rb z J = toStkA z (∑ i, cc i * valR b _ ((f i).f jf)) := by
    rw [ExpGTrans.secLin_val hs rb z hJ, hrb, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, sval_of (f i) _ z J jf hjf]
    refine congrArg₂ (· * ·) (gs_scal _ rb hrb' z _) (toStkA_valR_eq_gs b _ z (top_le_of_mem _ _ z ?_) _).symm
    have := hJ.mem (D.famφB χ) b
    rwa [funext hjf] at this
  have a₂ : (val (g.s χ) (𝟙 _) z J).val = toStkA z (valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) := by
    have c : ∀ i, J (𝟙 (Sp F) ≫ DegPre.gtφ D F g.b χ i) = jt i := fun i =>
      (congrArg J ((Category.id_comp _).trans ((gtφ_eq D F g.b χ i).trans
        (congrArg (· ≫ D.Oφ (𝟙 _) χ i) hb.symm)))).trans (hjt i)
    refine (congrArg Units.val (val_of (g.s χ) (𝟙 _) z J jt c)).trans ?_
    refine (toStkA_valR (𝟙 (Sp F)) _ z (top_le_of_mem _ _ z ?_) _).symm
    have := hJ.mem (DegPre.gtφ D F g.b χ) (𝟙 (Sp F))
    rwa [funext c] at this
  have e' : toStkA z (coef s g w χ) * toStkA z Rg ^ k = toStkA z (∑ i, cc i * valR b _ ((f i).f jf)) *
      toStkA z (valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) * toStkA z W := by
    have a₃ : toStkA z (coef s g w χ) = GlobalTheory.UT.cst (R := R) F z (coef s g w χ) := (CoefBasic.cst_eq (R := R) z _).symm
    rw [hR, hW, ← a₁, ← a₂, a₃]
    exact e
  rw [← map_pow, ← map_mul, ← map_mul, ← map_mul] at e'
  rw [(eq_mul_inv_iff_mul_eq₀ (pow_ne_zero k R0)).2 ((toStkA z).injective e'), Finset.sum_mul]
  simp only [_root_.mul_assoc]
  ring

end GlobalTheory.ZH.IntegralSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.SquareLevel

open GlobalTheory.ThetaCoord

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (i : Fin g) : (halves g (.inl i) : ℕ) = i := rfl

theorem halves_inr (g : ℕ) (i : Fin g) : (halves g (.inr i) : ℕ) = g + i := rfl

theorem labelSymp_eq (g M : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) :
    labelSymp (a ∘ (halves g).symm) (b ∘ (halves g).symm) = eStd g M a b := by
  have h₁ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inl, if_neg (by omega), if_neg (by omega)]
  have h₂ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₃ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_neg (by omega), if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₄ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inr, halves_inr, if_neg (by omega), if_neg (by omega)]
  rw [labelSymp, ← (halves g).sum_comp]
  simp_rw [← (halves g).sum_comp]
  simp [Fintype.sum_sum_type, h₁, h₂, h₃, h₄, eStd, sub_eq_add_neg, Finset.sum_add_distrib, add_comm]

variable {S : Scheme.{0}}

theorem linComb_pow_left {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb (fun i => y i ^ M) c = linComb y (fun i => M * c i) := by
  simp only [linComb, pow_mul]

theorem linComb_pow_right {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb y c ^ M = linComb y (fun i => M * c i) := by
  simp only [linComb, List.prod_ofFn, ← Finset.prod_pow, ← pow_mul, Nat.mul_comm]

theorem comp_linComb {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : h ≫ linComb y c = linComb (fun i => h ≫ y i) c := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (h ≫ ·) (fun a b => MonObj.comp_mul _ _ _)
  simp only [linComb, List.prod_ofFn]
  exact (map_prod F _ _).trans (Finset.prod_congr rfl fun i _ => map_pow F _ _)

theorem existsUnique_lab {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n M : ℕ} [NeZero M]
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ (M ^ 2) = 1)
    (ind : ∀ c c' : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = linComb y (fun i => (c' i : ℕ)) → c = c')
    (z : T ⟶ A) (hz : z ^ M = 1) (sp : ∃ c : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = z) :
    ∃! a : Fin n → ZMod M, lab (fun i => y i ^ M) a = z := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have lt : ∀ a : ZMod M, M * a.val < M ^ 2 := fun a => by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hM
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb => ?_
  · obtain ⟨c, hc⟩ := sp
    have h₀ := ind (fun i => ⟨(M * c i) % M ^ 2, Nat.mod_lt _ (pow_pos hM 2)⟩) (fun _ => ⟨0, pow_pos hM 2⟩) (by
      have e : linComb y (fun i => (M * c i) % M ^ 2) = linComb y (fun i => M * c i) := by
        simp only [linComb]
        exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => (pow_eq_pow_mod _ (hy i)).symm)
      refine e.trans ?_
      rw [← linComb_pow_right, hc, hz]
      simp [linComb])
    have h₁ : ∀ i, M ∣ (c i : ℕ) := fun i => by
      have q : (M * c i) % M ^ 2 = 0 := congrArg Fin.val (congrFun h₀ i)
      exact Nat.dvd_of_mul_dvd_mul_left hM (sq M ▸ Nat.dvd_of_mod_eq_zero q)
    refine ⟨fun i => ((c i : ℕ) / M : ℕ), (linComb_pow_left _ _ _).trans
      ((congrArg (linComb y) (funext fun i => ?_)).trans hc)⟩
    rw [ZMod.val_cast_of_lt (Nat.div_lt_of_lt_mul (sq M ▸ (c i).2)), Nat.mul_div_cancel' (h₁ i)]
  · have h := ind (fun i => ⟨_, lt (a i)⟩) (fun i => ⟨_, lt (b i)⟩)
      ((linComb_pow_left _ _ _).symm.trans ((ha.trans hb.symm).trans (linComb_pow_left _ _ _)))
    funext i
    exact ZMod.val_injective M (Nat.eq_of_mul_eq_mul_left hM (congrArg Fin.val (congrFun h i)))

theorem weilIs_pow_pow (hW : WeilSt) [IsLocallyNoetherian S] (P : PolAV S) {M : ℕ} {T : Over S}
    (hu : IsUnit (M : Γ(T.left, ⊤))) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hM : 1 ≤ M) (hx : x ^ (M ^ 2) = 1)
    (hy : y ^ (M ^ 2) = 1) (H : WeilIs P.A P.L (M ^ 2 : ℕ) x y c) :
    WeilIs P.A P.L M (x ^ M) (y ^ M) (c ^ M) := by
  have H' := CommPairing.weilIs_symm P.isLB H
  have k : ∀ n, WeilIs P.A P.L (M ^ 2 : ℕ) (y ^ (n + 1)) x (c⁻¹ ^ (n + 1)) := fun n => by
    induction n with
    | zero => simpa using H'
    | succ n ih => rw [pow_succ y, pow_succ c⁻¹]; exact (hW S P _ T).2.1 _ _ _ _ _ ih H'
  have k' := CommPairing.weilIs_symm P.isLB (k (M - 1))
  rw [Nat.sub_add_cancel hM, inv_pow, inv_inv] at k'
  refine ((hW S P M T).2.2.2 M x _ _ (by rw [Nat.cast_mul]; exact hu.mul hu) (by rw [← sq, hx])
    (by rw [← pow_mul, ← sq, hy])).1 ?_
  rwa [← Nat.cast_mul, ← sq]

end GlobalTheory.SquareLevel

namespace GlobalTheory

open SquareLevel ThetaCoord in

theorem exists_torsionPoints_of_squareLevel : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  intro hL S _ P M ze hM hu lev
  have : NeZero M := ⟨by omega⟩
  have hq : ∀ i, (lev.pt i ^ M) ^ M = 1 := fun i => by rw [← pow_mul, ← sq, lev.torsion]
  refine ⟨fun a => lab (fun i => lev.pt i ^ M) (a ∘ (halves P.g).symm), fun a b => lab_add hq _ _,
    fun K _ _ x z hz => ?_, fun a b => ?_, fun a => ?_, fun i i₁ i₂ h₁ h₂ => ?_⟩
  · have H := existsUnique_lab (M := M)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ lev.pt i)
      (fun i => by rw [← MonObj.comp_pow, lev.torsion, MonObj.comp_one]) (lev.indep K x) z hz
      (lev.span K x z (by rw [sq, pow_mul, hz, one_pow]))
    refine ((Equiv.arrowCongr (halves P.g) (Equiv.refl (ZMod M))).existsUnique_congr fun a => ?_).2 H
    rw [lab, comp_linComb]
    simp only [MonObj.comp_pow]
    rfl
  · have hze : (ze ^ M) ^ M = 1 := by rw [← pow_mul, ← sq, lev.prim.pow_eq_one]
    have := weilIs_lab hL.globalFns P (T := baseOver S) hq (ze := ze ^ M) hze (fun i j => by
      have := weilIs_pow_pow hL.weil P (T := baseOver S) hu hM (lev.torsion i) (lev.torsion j) (lev.pairing i j)
      convert this using 1
      show (ze ^ M) ^ stdSymp P.g i j = (ze ^ stdSymp P.g i j) ^ M
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm])
      (fun a b => ((hL.weil S P M _).1 _ _ (lab_pow hq a) (lab_pow hq b)).exists)
      (a ∘ (halves P.g).symm) (b ∘ (halves P.g).symm)
    rw [labelSymp_eq] at this
    rw [pow_mul]
    exact this
  · refine ⟨linComb lev.pt fun i => (a ((halves P.g).symm i)).val, ?_, ?_⟩
    · simp only [linComb, List.prod_ofFn, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, lev.torsion, one_pow]
    exact (linComb_pow_right _ _ _).trans (linComb_pow_left _ _ _).symm
  · have k : ∀ s, lab (fun i => lev.pt i ^ M) ((Pi.single s (1 : ZMod M) : _ → ZMod M) ∘ (halves P.g).symm) =
        lev.pt (halves P.g s) ^ M := fun s => by
      rw [← lab_single (M := M) hq (halves P.g s)]
      congr 1
      funext j
      simp [Pi.single_apply, Equiv.symm_apply_eq]
    have e₁ : i₁ = halves P.g (.inl i) := Fin.ext h₁
    have e₂ : i₂ = halves P.g (.inr i) := Fin.ext (h₂.trans (Nat.add_comm _ _))
    rw [e₁, e₂]
    exact ⟨k _, k _⟩

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionPointOfIntegralModelPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusExtensionPoint_of_integralModelPoint : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left), c ≫ u.G.hom = spMap u.j → ∃ g, u.Lev c g := by
  first | exact @GlobalTheory.IntegralGt.exists_lev | exact GlobalTheory.IntegralGt.exists_lev | (intros; apply GlobalTheory.IntegralGt.exists_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpSchemeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorFieldFrame_smooth_commGrpScheme : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  first | exact @GlobalTheory.SS.exists_isFrame | exact GlobalTheory.SS.exists_isFrame | (intros; apply GlobalTheory.SS.exists_isFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.fib_of_indep : ∀ C : Core, C.Indep → C.Fib := by
  intro C hI p _ y τ x hx
  obtain ⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, htest⟩ := GlobalTheory.T.abelianSchemeProperClosureData_basic_properties C
  have := C.lft
  have hne : ((C.GG.hom ⁻¹ᵁ C.U : C.G.toScheme.Opens) : Set C.G.toScheme).Nonempty := by
    obtain ⟨w, hw⟩ := hdom.denseRange.exists_mem_open C.U.isOpen C.ne
    exact ⟨w, hw⟩
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  obtain ⟨b', hb'x, hb'U⟩ :=
    (@GlobalTheory.T.exists_classical_point_lifting_residue_point C.G.toScheme hint (C.GG.hom ≫ C.π) hflat hlft' (C.GG.hom ⁻¹ᵁ C.U) hne p _).1 x
  have hcl : C.Cl (b' ≫ C.GG.hom) := by
    rintro _ ⟨s, rfl⟩
    have := hb'U ⟨s, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact this
  obtain ⟨b, hby, hbx⟩ := hI p (b' ≫ C.GG.hom) y hcl (htest p y τ).1
    (by rw [← Category.assoc, hb'x, hx]) b' rfl
  obtain ⟨c, hc, hcb⟩ := τ.lift b hby
  refine ⟨rPt p ≫ c, by rw [Category.assoc, hc], ?_⟩
  rw [Category.assoc, hcb, hbx, hb'x]

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmersedByOfLocalCoords
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.SecImm
open GlobalTheory.Points GlobalTheory.ProjSpace

section
variable {o : Type} [CommRing o] {m m' : ℕ} {K : Type} [Field K] {Y : Scheme.{0}}

theorem crd_toProj {L : LB Y} (f : Y ⟶ Sp o) (s : Fin (m + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (x : Sp K ⟶ Y) (k : L.ι) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    Crd (O1 o m) (coord o m) (x ≫ toProj f s hs) (fun i => valF x _ ((s i).f k)) := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top (x ≫ toProj f s hs) (iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k) := fun z hz => ⟨hi hz, hk hz⟩
  have hu := (isUnit_resG_sec (s i) k (W := toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k)
    (inf_le_left.trans (toProj_preimage_chart f s hs i).le) inf_le_right).map (valMap x _ hT).hom
  rw [← valR_eq] at hu
  refine (LinFrame.crd_iff _ _).2 ⟨i, hu.unit, hi, fun j => ?_⟩
  have := congrArg (valR x _) (sec_eq_pullRatio_toProj_mul f s hs i j k
    (W := toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k) inf_le_left inf_le_right)
  rw [valR_mul x _ hT, valR_res x _ hT, LinFrame.valR_pullRatio x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end

end GlobalTheory.ZH.SecImm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChangeStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isImmersion_projSpace_of_local_linearChange : ∀ (o : Type) [CommRing o] (Y Z : Scheme.{0}) [IsReduced Y] (s : Z ⟶ Sp o) (f : Y ⟶ Z) (m : ℕ) (π : Y ⟶ PSpace o m) (h : π ≫ PSpace.str o m = f ≫ s), (∀ y : Y, ∃ (W : Z.Opens) (A : Type) (_ : CommRing A) (c : W.toScheme ⟶ Sp A) (ψ : (f ⁻¹ᵁ W).toScheme ⟶ PSpace A m) (a : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(Z, W)) (K : Type) (_ : Field K) (η : Sp K ⟶ (f ⁻¹ᵁ W).toScheme) (v : Fin (m + 1) → K), f y ∈ W ∧ IsImmersion ψ ∧ ψ ≫ PSpace.str A m = (f ∣_ W) ≫ c ∧ IsUnit a.det ∧ IsDominant η ∧ Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (η ≫ (f ⁻¹ᵁ W).ι ≫ π) v ∧ Crd (ProjSpace.O1 A m) (ProjSpace.coord A m) (η ≫ ψ) ((a.map (valF (η ≫ (f ⁻¹ᵁ W).ι ≫ f) W)).mulVec v)) → IsImmersion (pullback.lift π f h) := by
  first | exact @GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change | exact GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change | (intros; apply GlobalTheory.ZH.LinFrame.isImmersion_lift_of_linear_change <;> assumption)
end

