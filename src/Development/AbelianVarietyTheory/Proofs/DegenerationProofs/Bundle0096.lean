import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0090

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpScheme
section
noncomputable section

namespace GlobalTheory.SS.InvFrame

theorem exists_det_ne_zero {F S : Type} [Field F] {n : ℕ} (D : Fin n → S → F) (h : LinearIndependent F D) :
    ∃ t : Fin n → S, (Matrix.of fun i j => D i (t j)).det ≠ 0 := by
  have hs := span_flip_eq_top_iff_linearIndependent.2 h
  obtain ⟨f, hf, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq F (Set.range (flip D))
  have e : Module.finrank F (Submodule.span F (Set.range (flip D))) = n := by
    rw [hs, finrank_top, Module.finrank_fin_fun]
  choose t ht using hf
  refine ⟨fun j => t (j.cast e.symm), ?_⟩
  have h2 := hli.comp (Fin.cast e.symm) (Fin.cast_injective _)
  refine ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)).ne_zero
  have e2 : (Matrix.of fun i j : Fin n => D i (t (j.cast e.symm))).col = f ∘ Fin.cast e.symm :=
    funext fun j => ht _
  rw [e2]
  exact h2

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis constFn)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.KS GlobalTheory.KS.InvField

theorem value_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {T : CommRingCat.{0}}
    (φ : Γ(X, U) ⟶ T) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso T).hom.hom (pbT (Spec.map φ ≫ hU.fromSpec) f ⊤) = φ.hom f := by
  have ht : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have ht' : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := fun q _ => ht (x := Spec.map φ q) trivial
  rw [pbT_of_le _ ht']
  have h1 : hU.fromSpec.appLE U ⊤ ht = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h2 : (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso T).hom = φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, h1, Category.assoc, Iso.inv_comp_eq,
      ← Scheme.ΓSpecIso_naturality]
    congr 1
  exact congrArg (fun q => q.hom f) h2

theorem value_constFn_id {T : Type} [CommRing T] (a : T) :
    (Scheme.ΓSpecIso (.of T)).hom.hom (constFn (𝟙 (Sp T)) ⊤ a) = a := by
  have h : (𝟙 (Sp T) : Sp T ⟶ Sp T).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 (Sp T)) (U := ⊤)).trans rfl
  rw [constFn, h]
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso (.of T)).inv_hom_id

variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))} [GrpObj G] [IsCommMonObj G]

theorem exists_independent [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {S F : Type} [CommRing S] [Algebra K S] [Field F] [Algebra K F] (j : sp (R₀ := K) S ⟶ G)
    [IsOpenImmersion j.left] (u : S →ₐ[K] F) :
    ∃ D : Fin n → S → F, LinearIndependent F D ∧ ∀ k, ∃ φ : S →ₐ[K] DualNumber F,
      spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v k) *
        (spMap ((inlS K F).comp u) ≫ j) ∧ ∀ a, (φ a).snd = D k a := by
  obtain ⟨χ, hχ, hfst⟩ := exists_chart_pt_of_nil j (TrivSqZeroExt.fstHom K F (Fin n → F))
    (fun a => ⟨inl a, rfl⟩) (fun a ha => ⟨2, by
      rw [pow_two]; exact mul_eq_zero_of_sq (ker_fst_sq (R := K) (S := F) (Fin n → F)) ha ha⟩)
    (lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) *
      (spMap ((TrivSqZeroExt.inlAlgHom K F (Fin n → F)).comp u) ≫ j)) u (by
      rw [MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), one_mul, ← Category.assoc,
        spMap_comp]
      rfl)
  have hfst : ∀ a, (χ a).fst = u a := AlgHom.congr_fun hfst
  let φ : (Fin n → F) → (S →ₐ[K] DualNumber F) := fun c => (vecTo (inlS K F) (fun i => inr (c i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = tanExp v c * (spMap ((inlS K F).comp u) ≫ j) := fun c => by
    rw [← spMap_comp, Category.assoc, ← hχ, MonObj.comp_mul, comp_lieExp, ← Category.assoc, spMap_comp]
    congr 1
    · exact lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _
    · congr 2
      exact AlgHom.ext fun a => by simp [vecTo_apply]
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, c k * (χ a).snd k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  refine ⟨fun k a => (χ a).snd k, Fintype.linearIndependent_iff.2 fun c hc k => ?_,
    fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · have : φ c = φ 0 := AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by
      rw [hφ2, hφ2]
      simpa using congrFun hc a)
    have h3 := mul_right_cancel ((hφ c).symm.trans (this ▸ hφ 0))
    have h4 := (expBij (DualNumber F) hv _ (ker_fst_sq (R := K) (S := F) F)).1 _ _ (fun _ => rfl) (fun _ => rfl) _ _ h3
    exact TrivSqZeroExt.inr_injective (congrFun h4 k)
  · rw [hφ]
    congr 1
    refine (Finset.prod_eq_single k (fun i _ hi => epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _
      (by simp [Pi.single_eq_of_ne hi]) _) (by simp)).trans ?_
    congr 3
    simp
  · rw [hφ2]
    simp [Pi.single_apply]

omit [IsCommMonObj G] in

theorem value_invDer {v : epsR K ⟶ G} {dd : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(G.left, W)} (hd : IsInvDer v dd)
    {U : G.left.Opens} (hU : IsAffineOpen U) [Algebra K Γ(G.left, U)] (j : sp (R₀ := K) Γ(G.left, U) ⟶ G)
    (hj : j.left = hU.fromSpec) {F : Type} [Field F] [Algebra K F] (u : Γ(G.left, U) →ₐ[K] F)
    (φ : Γ(G.left, U) →ₐ[K] DualNumber F)
    (hφ : spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v) *
        (spMap ((inlS K F).comp u) ≫ j)) (f : Γ(G.left, U)) : (φ f).snd = u (dd U f) := by
  let w : sp (R₀ := K) (DualNumber F) ⟶ epsR K ⊗ G :=
    lift (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))) (spMap ((inlS K F).comp u) ≫ j)
  have e1 : w.left ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, ← hφ, Over.comp_left, hj]
    rfl
  have e2 : w.left ≫ (snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom ((inlS K F).comp u).toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, lift_snd, Over.comp_left, hj]
    rfl
  have e3 : w.left ≫ (fst (epsR K) G).left = 𝟙 _ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
      (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)).toRingHom := by
    rw [← Over.comp_left, lift_fst, Category.id_comp]
    rfl
  have hw : ⊤ ≤ w.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, e2]
    exact fun q _ => hU.fromSpec_preimage_self.ge (x := Spec.map _ q) trivial
  have key : ∀ f : Γ(G.left, U), ((Scheme.ΓSpecIso (.of (DualNumber F))).hom.hom (pbT w.left
      (pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ U)) ⊤) : DualNumber F) =
      inl (u f) + inr 1 * inl (u (dd U f)) := fun f => by
    rw [hd U f, pbT_add, pbT_mul, pbT_pbT _ _ le_rfl hw, pbT_pbT _ _ le_rfl hw, pbT_constFn _ _ hw, e2, e3,
      constFn_spMap, map_add, map_mul]
    refine congrArg₂ _ (value_fromSpec hU _ _) (congrArg₂ _ ?_ (value_fromSpec hU _ _))
    refine Eq.trans ?_ (epsTo_eps (R := K) (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))
    exact value_constFn_id _
  by_cases h : (snd (epsR K) G).left ⁻¹ᵁ U ≤ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ U
  · have := key f
    rw [pbT_pbT _ _ h hw, e1] at this
    have h5 := congrArg TrivSqZeroExt.snd ((value_fromSpec hU _ f).symm.trans this)
    simpa using h5
  · have := key 1
    rw [show pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left (1 : Γ(G.left, U))
      ((snd (epsR K) G).left ⁻¹ᵁ U) = 0 from dif_neg h, pbT_zero, map_zero] at this
    simpa using congrArg TrivSqZeroExt.fst this

theorem exists_mem_basicOpen [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    (D : Fin n → VF G) (hd : ∀ i, IsInvDer (v i) fun W f => (D i).D W f) (x : G.left) :
    ∃ (U : G.left.Opens) (t : Fin n → Γ(G.left, U)), x ∈ G.left.basicOpen (jac D U t) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  letI : Algebra K Γ(G.left, U) := (Spec.preimage (hU.fromSpec ≫ G.hom)).hom.toAlgebra
  let j : sp (R₀ := K) Γ(G.left, U) ⟶ G := Over.homMk hU.fromSpec (Spec.map_preimage _).symm
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hx
  have := PrimeSpectrum.isPrime p
  let u : Γ(G.left, U) →ₐ[K] (PrimeSpectrum.asIdeal p).ResidueField := IsScalarTower.toAlgHom _ _ _
  obtain ⟨δ, hδ, hφ⟩ := exists_independent hv j u
  obtain ⟨t, ht⟩ := exists_det_ne_zero δ hδ
  refine ⟨U, t, ?_⟩
  have h1 : u (jac D U t) ≠ 0 := by
    rw [jac, AlgHom.map_det]
    refine (congrArg Matrix.det (Matrix.ext fun i k => ?_)).trans_ne ht
    obtain ⟨φ, h2, h3⟩ := hφ i
    exact (value_invDer (hd i) hU j rfl u φ h2 (t k)).symm.trans (h3 _)
  have h2 : p ∈ hU.fromSpec ⁻¹ᵁ G.left.basicOpen (jac D U t) := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact fun h => h1 (Ideal.algebraMap_residueField_eq_zero.2 h)
  exact h2

end GlobalTheory.SS.InvFrame

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.SS.exists_isFrame : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  intro K _ A _ _ g hg
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  choose dd hdd using fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).1
  have hp := fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).2 _ (hdd i)
  let D : Fin g → VF A := fun i =>
    { D := fun U => AddMonoidHom.mk' (dd i U) ((hp i).1 U)
      leibniz := (hp i).2.1
      const := (hp i).2.2.2.1
      res := fun U V h a => by
        have := (hp i).2.2.1 U V a h
        rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h] at this
        exact this }
  refine ⟨D, by rwa [Fintype.card_fin], fun x => ?_⟩
  obtain ⟨U, t, hx⟩ := InvFrame.exists_mem_basicOpen hv D hdd x
  have hle := A.left.basicOpen_le (jac D U t)
  refine ⟨_, fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i), hx, ?_⟩
  have e : jac D _ (fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i)) =
      (A.left.presheaf.map (homOfLE hle).op).hom (jac D U t) := by
    exact (congrArg Matrix.det (Matrix.ext fun i k => (D i).res U _ hle (t k))).trans
      (RingHom.map_det (A.left.presheaf.map (homOfLE hle).op).hom (Matrix.of fun i k => (D i).D U (t k))).symm
  rw [e]
  exact A.left.toRingedSpace.isUnit_res_basicOpen (jac D U t)

end

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesMulVecOfGenericValueStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoordinates_mulVec_of_genericValue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N N' : RatModel o Ω') (a : N'.Z ⟶ N.Z) (q : N'.Z ⟶ M.Z) (W : M.Z.Opens) (H : LB N.Z) (d : H.ι → Ω') (J : Type) [Fintype J] (st : J → H.Sec) (σ : J → (H.pull a).Sec) (t u : J → Ω') (c : Matrix J J Γ(M.Z, W)), N.IsHom N' (AlgHom.id o Ω') a → M.IsHom N' φ q → (∀ z, q z ∈ W) → (∀ j, N.HasVal d (st j) (t j)) → (∀ j, N'.HasVal (H := H.pull a) (fun k => d (k PUnit.unit)) (σ j) (u j)) → t = (c.map fun g => φ (valF M.pt W g)).mulVec u → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ N'.Z) (w : J → R), Crd (H.pull a) σ x w → Crd H st (x ≫ a) ((c.map (valR (x ≫ q) W)).mulVec w) := by
  first | exact @GlobalTheory.ZH.RatModel.crd_mulVec_of_hasVal | exact GlobalTheory.ZH.RatModel.crd_mulVec_of_hasVal | (intros; apply GlobalTheory.ZH.RatModel.crd_mulVec_of_hasVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomogeneousCoordinatesOfGeometricFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoordinates_of_geometricFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : u.PtC) (v : S.J → PadicAlgCl p), Crd (LPow u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v → ρ.Crd (u.toA a) v := by
  first | exact @GlobalTheory.ZH.CrdMove.crd_of_moved | exact GlobalTheory.ZH.CrdMove.crd_of_moved | (intros; apply GlobalTheory.ZH.CrdMove.crd_of_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem immBy_of_spans (hA : AmpleSt) {R : Type} [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {N : ℕ}
    (hN : 4 ≤ N) {J : Type} [Fintype J] (s : J → LB.Sec (LPow P.A P.L N (baseOver (Sp R))))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), ∃ c : J → Γ((baseOver (Sp R)).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j) :
    ImmBy (baseOver (Sp R) ⊗ P.A).hom (LPow P.A P.L N (baseOver (Sp R))) s Set.univ := by
  have := P.isAb.proper
  have hT : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have hL : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  have key := (AmpleSpan.embedsBy_of_isPullback P.A P.isLB (hA _ P N hN).2 (isAffineOpen_top (Sp R))
    (g := (baseOver (Sp R)).hom ≫ (Sp R).topIso.inv) (φ := (snd (baseOver (Sp R)) P.A).left)
    (f' := (fst (baseOver (Sp R)) P.A).left) (K := Fin 1) (ε := fun _ => (N : ℤ))
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact (IsPullback.of_hasPullback _ P.A.hom).flip) (by simp) s
    (fun σ => hs σ)).1
  have e : (baseOver (Sp R) ⊗ P.A).hom = (fst (baseOver (Sp R)) P.A).left :=
    (Over.w (fst (baseOver (Sp R)) P.A)).symm.trans (Category.comp_id _)
  rw [SpanImm.immBy_iff, e]
  exact key

theorem ThetaSys.Real.immBy_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ImmBy (baseOver (Sp S.R) ⊗ ρ.P.A).hom (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s Set.univ := by
  intro hL o Ω _ _ _ _ S ρ
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have hN : 4 ≤ S.N := by
    have h : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h 2
  exact immBy_of_spans hL.1.ample ρ.P hN ρ.s fun σ => (ρ.s_basis σ).exists

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralTorsionPointDescendsToModelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_torsion_point_descends_to_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p), (∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) → ∀ b : Over.mk (spMap jV) ⟶ u.G, b ^ (S.r * S.N) = 1 → ∃ (a : S.Gam) (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) ∧ spMap jV ≫ hV = b.left := by
  first | exact @GlobalTheory.ZH.torsion_integral_descends | exact GlobalTheory.ZH.torsion_integral_descends | (intros; apply GlobalTheory.ZH.torsion_integral_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpanStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersionBySections_of_span : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsProper p] (H : LB X), H.IsLB → ∀ (I J : Type) [Fintype I] [Fintype J] (t : I → H.Sec) (s : J → H.Sec), ImmBy p H t Set.univ → (∀ i, ∃ a : J → k, IsLin p s a (t i)) → ImmBy p H s Set.univ) := by
  first | exact @GlobalTheory.ZH.SpanImm.immBy_of_span | exact GlobalTheory.ZH.SpanImm.immBy_of_span | (intros; apply GlobalTheory.ZH.SpanImm.immBy_of_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibilityStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_of_coordinate_divisibility : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  first | exact @GlobalTheory.ZH.RatModel.immBy_of_div | exact GlobalTheory.ZH.RatModel.immBy_of_div | (intros; apply GlobalTheory.ZH.RatModel.immBy_of_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegralOfWeightZeroCoordinateDominates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem Mod.integral_of_weight_zero_dominates : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (a : Sp (PadicAlgCl p) ⟶ G.left) (w : J → PadicAlgCl p), a ≫ G.hom = gPt p ≫ spMap j → Crd H σ a w → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a := by
  intro p _ V _ j G _ g N N' X _ q H J _ σ cls m hB a w ha hw hi
  obtain ⟨ν, hν, hc⟩ := m.ser a ha w hw
  apply hc
  let e : m.Φ.E.X ≃ₗ[ℤ] X := m.xe.toIntLinearEquiv
  have : Module.Free ℤ X := Module.Free.of_equiv e
  have : Module.Finite ℤ X := Module.Finite.equiv e
  have hq : ∀ x : X, (q.comp m.xe.toIntLinearEquiv.toLinearMap) (m.xe.symm x) = q x := by
    intro x
    rw [QuadraticMap.comp_apply]
    exact congrArg q (m.xe.apply_symm_apply x)
  refine GlobalTheory.T.valuation_eq_polarForm_of_weightZero_max X q g N J cls p w ν ?_ ?_ hB.lll ?_ hν hi
  · have h := m.good.pos.comp (m.xe.symm.injective.tendsto_cofinite)
    exact h.congr hq
  · exact e.finrank_eq.symm.le.trans ((Nat.le_add_left _ _).trans m.dim.le)
  · intro i n
    have h := m.good.short i (m.xe.symm n)
    rw [← map_nsmul, ← map_add, hq, hq] at h
    exact h

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperHomOfRelAmple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem isProper_hom_of_relAmple {T : Scheme.{0}} {A : Over T} [GrpObj A] {B : LB A.left} (h : RelAmple A B) :
    IsProper A.hom := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (fun U : T.affineOpens => U.1)
    (iSup_affineOpens_eq_top T) fun U => ?_
  have h₁ := projProper _ _ _ (GlobalTheory.ProjSpace.isProjOver_morphismRestrict_of_relAmple h U.2)
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _ U.2.isoSpec.hom).1 h₁

theorem abOpen_of_isOpen_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → IsOpen (abLocus Z.G) → GlobalTheory.Models.AbOpen Z.G := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Z _ hO
  letI := Z.grp
  let W : M.Z.Opens := ⟨abLocus Z.G, hO⟩
  refine ⟨W, rfl, ?_⟩
  have h : IsProper (pullback.snd Z.G.hom W.ι) := isProper_hom_of_relAmple (Z.pol W le_rfl).1
  unfold morphismRestrict
  infer_instance

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPurePullbackSectionMulWeightGenerator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem pure_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ (b : LB.Sec (LB.LinComb L ψ ε)) (φ : (Φ.H 1).Sec), UFib.Red Φ c t b φ → Φ.Pure α φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ α hw b φ hr
  rintro χ ⟨l, hl⟩
  by_contra hne
  refine hl ((GlobalTheory.T.hasTorusWeight_iff_torusEquivariant k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).1 ?_ χ hne)
  intro Z τ g z hz
  have := Φ.D.q_hom
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
    (fun _ _ _ => rfl) (fun _ => c.le l hz)
  have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
    congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
  have h₁ := hr _ g.left z J hJ l hz (e ())
  have h₂ := hr _ ((τ ≫ Φ.D.i) * g).left z J hJ l
    (GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz)
    (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
  rw [hq, hw Z τ g z J hJ, Units.val_mul, mul_left_comm, ← h₁] at h₂
  exact h₂

end GlobalTheory.ZH.UFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoPullbackUniformisedThetaModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.TestBundle

open GlobalTheory.CechPic

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (P : Over (Spec (CommRingCat.of V))) [Smooth P.hom] [GeometricallyConnected P.hom]
    (e : Spec (CommRingCat.of V) ⟶ P.left) (he : e ≫ P.hom = 𝟙 _) {L M : LB P.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : CechPic.pull (pullback.fst P.hom (jK V)) (cls L hL) =
      CechPic.pull (pullback.fst P.hom (jK V)) (cls M hM)) : LBIso L M := by
  have hN := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
  have h₂ : Flat (jK V) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors V))
  refine GenericExtend.exists_isGen_of_densePart _ _ (jK V) ((isNormalScheme_iff_pred _).1 inferInstance) h₁ h₂
    DVR.isDominant_jK inferInstance P e (LB.div M L) he ‹_› (geometricallyIntegral_of_smooth P.hom) hN
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hN _)) ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  rw [cls_pull hN, cls_div hM hL, map_sub, h, sub_self]

theorem lbIso_pull_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK _ F ψ ⟨_, h₁, _, h₂⟩
  have := u.semi.smooth
  have := u.semi.geomConnected
  have hL := Q.L.isLB
  have hP := ρ.P.isLB
  have hA := u.A.isLB
  have hG := u.U.LG.isLB
  refine lbIso_of_generic u.G (eSec u.G) (Over.w η[u.G]) (pull_isLB hL F) hG ?_
  have a : CechPic.pull Q.φ (cls _ hL) = CechPic.pull (pullback.fst ρ.P.A.hom Q.u₀) (cls _ hP) :=
    (cls_eq_iff (pull_isLB hL _) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
  have b : cls _ hA = CechPic.pull u.φ (cls _ hP) := (cls_eq_iff hA (pull_isLB hP _)).2 u.lb
  have c : CechPic.pull u.U.gen.hom.left (cls _ hA) = CechPic.pull (pullback.fst u.G.hom (jK u.V)) (cls _ hG) :=
    (cls_eq_iff (pull_isLB hA _) (pull_isLB hG _)).2 u.U.ext
  refine Eq.trans ?_ c
  rw [cls_pull hL, ← pull_comp, ← h₂, pull_comp, a, ← pull_comp, h₁, b]
  exact pull_comp _ _ _

end GlobalTheory.ZH.TestBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RestrictEqOfSameThetaMultipleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_eq_of_same_theta_multiple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  first | exact @GlobalTheory.ZH.ZHPre.resG_eq_of_thMul | exact GlobalTheory.ZH.ZHPre.resG_eq_of_thMul | (intros; apply GlobalTheory.ZH.ZHPre.resG_eq_of_thMul <;> assumption)
end

