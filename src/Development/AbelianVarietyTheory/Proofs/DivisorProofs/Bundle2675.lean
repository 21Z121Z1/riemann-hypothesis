import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentGeneratorsHolomorphicFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_tangent_generators_holomorphicFrame : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (d : CD N g r bX) (G : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g → ℂ), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b → ∃ T : Fin r → ℂ, ∀ (χ : N.X) (ct : Fin g → ℂ), ct = d.t12 *ᵥ co bX χ → vE (gm.s (ν.eX χ)) (𝟙 _) ν.J * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) = (1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ T))) * TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) + TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) := by
  first | exact @GlobalTheory.MBLow.Cl.JetGen.tangent_generators | exact GlobalTheory.MBLow.Cl.JetGen.tangent_generators | (intros; apply GlobalTheory.MBLow.Cl.JetGen.tangent_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraRetractionExists
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusLieRetraction

open IsLocalRing GlobalTheory.HodgeTateCompare GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem lieEquiv_add' {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (v w : Lie G) :
    lieEquiv G (v + w) = lieAdd G (lieEquiv G v) (lieEquiv G w) :=
  Subtype.ext (lieEquiv_add v w)

theorem lieEquiv_smul' {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (a : R) (v : Lie G) :
    lieEquiv G (a • v) = lieScale G a (lieEquiv G v) :=
  Subtype.ext (lieEquiv_smul a v)

def lieLin {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u] :
    Lie T →ₗ[R] Lie G where
  toFun v := (lieEquiv G).symm (lieMap u (lieEquiv T v))
  map_add' v w := by
    apply (lieEquiv G).injective
    rw [Equiv.apply_symm_apply, lieEquiv_add', lieEquiv_add', Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap u).1 _ _
  map_smul' a v := by
    apply (lieEquiv G).injective
    rw [Equiv.apply_symm_apply, lieEquiv_smul', RingHom.id_apply, lieEquiv_smul',
      Equiv.apply_symm_apply]
    exact (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap u).2 _ _

theorem lieEquiv_lieLin {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G)
    [IsMonHom u] (v : Lie T) : lieEquiv G (lieLin u v) = lieMap u (lieEquiv T v) :=
  Equiv.apply_symm_apply _ _

theorem res_comp_of_mem {M : Type} [AddCommGroup M] [Module R M] {v : Module.Dual R M}
    (hv : v ∈ (maximalIdeal R) • (⊤ : Submodule R (Module.Dual R M))) :
    (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0 := by
  refine Submodule.smul_induction_on (p := fun v : Module.Dual R M =>
    (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0) hv ?_ ?_
  · intro a ha w _
    ext c
    simp [IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha]
  · intro x y hx hy
    rw [LinearMap.comp_add, hx, hy, add_zero]

theorem mem_of_res_comp {M : Type} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {v : Module.Dual R M}
    (hv : (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0) :
    v ∈ (maximalIdeal R) • (⊤ : Submodule R (Module.Dual R M)) := by
  let b := Module.Free.chooseBasis R M
  rw [← b.sum_dual_apply_smul_coord v]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
  have := LinearMap.congr_fun hv (b i)
  rw [← IsLocalRing.residue_eq_zero_iff]
  simpa [IsLocalRing.ResidueField.algebraMap_eq] using this

theorem tangentPt_inj {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {A : Type} [CommRing A]
    [Algebra R A] {v w : Cotangent G →ₗ[R] A}
    (h : (tangentPt v : specO R (DualNumber A) ⟶ G) = tangentPt w) : v = w := by
  have h1 : tangentAlg v = tangentAlg w := ptMap_locIncl_injective h
  refine GlobalTheory.AugCot.hom_ext (ε := aug G) fun a => ?_
  exact (tangentAlg_snd v a).symm.trans
    ((congrArg (fun φ => (φ a).snd) h1).trans (tangentAlg_snd w a))

theorem comp_cancel {T G : Over (Spec (CommRingCat.of R))} (u : T ⟶ G)
    (hu : IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (ResidueField R)).map u).left)
    {p q : specO R (DualNumber (ResidueField R)) ⟶ T} (h : p ≫ u = q ≫ u) : p = q := by
  let k := ResidueField R
  let f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let Y : Over (Spec (CommRingCat.of k)) := specO k (DualNumber k)
  let e : specO R (DualNumber k) ≅ (Over.map f).obj Y := Over.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Over.map_obj_hom, Y, f, specO, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
  let adj := Over.mapPullbackAdj f
  haveI : Mono ((Over.pullback f).map u) := by
    haveI : Mono ((Over.pullback f).map u).left := inferInstanceAs (Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map u).left)
    exact Over.mono_of_mono_left _
  have h1 : adj.homEquiv _ _ (e.inv ≫ p) = adj.homEquiv _ _ (e.inv ≫ q) := by
    apply (cancel_mono ((Over.pullback f).map u)).1
    rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_right, Category.assoc,
      Category.assoc, h]
  have h2 := (adj.homEquiv _ _).injective h1
  exact (cancel_epi e.inv).1 h2

theorem lTensor_injective_of {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (l : M →ₗ[R] N)
    (h : ∀ x, l x ∈ (maximalIdeal R) • (⊤ : Submodule R N) →
      x ∈ (maximalIdeal R) • (⊤ : Submodule R M)) :
    Function.Injective (l.lTensor (R ⧸ maximalIdeal R)) := by
  let eM := TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal R)
  let eN := TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal R)
  have hle : (maximalIdeal R) • (⊤ : Submodule R M) ≤
      ((maximalIdeal R) • (⊤ : Submodule R N)).comap l :=
    Submodule.smul_le.2 fun r hr n _ => by
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_smul hr trivial
  let q := Submodule.mapQ _ _ l hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero q).2 fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 (h x hx)
  have hcomm : ∀ t, eN (l.lTensor (R ⧸ maximalIdeal R) t) = q (eM t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul a x =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [LinearMap.lTensor_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.mapQ_apply, map_smul]
    | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  intro s t hst
  apply eM.injective
  apply hq
  rw [← hcomm, ← hcomm, hst]

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G], Smooth G.hom → ∀ (r : ℕ) (u : torus R r ⟶ G) [IsMonHom u],
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left →
    ∃ ρ : LieG G → LieG (torus R r), IsLieLinear ρ ∧ ∀ x, ρ (lieMap u x) = x := by
  intro R _ _ G _ hG r u _ hu
  haveI := hG
  obtain ⟨_, _⟩ := finite_projective_of_smooth (G := G)
  obtain ⟨_, _⟩ := finite_projective_of_smooth (G := torus R r)
  haveI : Module.FinitePresentation R (Cotangent G) := Module.finitePresentation_of_projective _ _
  haveI : Module.Free R (Cotangent G) := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation R (Cotangent (torus R r)) :=
    Module.finitePresentation_of_projective _ _
  haveI : Module.Free R (Cotangent (torus R r)) := Module.free_of_flat_of_isLocalRing
  let l := lieLin u
  let φ := Algebra.ofId R (ResidueField R)
  have key : ∀ x, l x ∈ (maximalIdeal R) • (⊤ : Submodule R (Lie G)) →
      x ∈ (maximalIdeal R) • (⊤ : Submodule R (Lie (torus R r))) := by
    intro x hx
    have h1 := res_comp_of_mem hx
    have a1 : ∀ y, (lieEquiv (torus R r) y).1 ≫ u = (lieEquiv G (l y)).1 := fun y => by
      rw [lieEquiv_lieLin]; rfl
    have h2 : (ptMap (dualBC φ) ≫ (lieEquiv (torus R r) x).1) ≫ u =
        (ptMap (dualBC φ) ≫ (lieEquiv (torus R r) 0).1) ≫ u := by
      rw [Category.assoc, Category.assoc, a1, a1, map_zero, lieEquiv_val, lieEquiv_val,
        dualBC_tangentPt, dualBC_tangentPt]
      exact congrArg tangentPt (h1.trans (LinearMap.comp_zero _).symm)
    have h3 := comp_cancel u hu h2
    rw [lieEquiv_val, lieEquiv_val, dualBC_tangentPt, dualBC_tangentPt, LinearMap.comp_zero] at h3
    exact mem_of_res_comp (tangentPt_inj h3)
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).2
    (lTensor_injective_of l key)
  refine ⟨fun y => lieEquiv (torus R r) (l' ((lieEquiv G).symm y)), ⟨fun x y => ?_, fun a x => ?_⟩,
    fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := (lieEquiv G).surjective x
    obtain ⟨y, rfl⟩ := (lieEquiv G).surjective y
    dsimp only
    rw [← lieEquiv_add', Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      map_add, lieEquiv_add']
  · obtain ⟨x, rfl⟩ := (lieEquiv G).surjective x
    dsimp only
    rw [← lieEquiv_smul', Equiv.symm_apply_apply, Equiv.symm_apply_apply, map_smul, lieEquiv_smul']
  · obtain ⟨x, rfl⟩ := (lieEquiv (torus R r)).surjective x
    dsimp only
    rw [← lieEquiv_lieLin, Equiv.symm_apply_apply]
    exact congrArg _ (LinearMap.congr_fun hl' x)

end GlobalTheory.TorusLieRetraction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointPermutationSignStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_point_permutation_sign : ∀ (F : Type) [Field F] [NumberField F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (π : Equiv.Perm (Fin (Module.finrank ℚ F))) (𝔞 𝔟 : FracId F) (z : (F →+* ℝ) → ℂ)
    (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetOmega),
    IsTorusPoint e 𝔞 𝔟 z X δ → IsTorusPoint (π.trans e) 𝔞 𝔟 z X ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) • δ) := by
  first | exact @GlobalTheory.TorusRenumber.isTorusPoint_perm | exact GlobalTheory.TorusRenumber.isTorusPoint_perm | (intros; apply GlobalTheory.TorusRenumber.isTorusPoint_perm <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private def piSL {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {J : Type} {M M' : J → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[σ] M' i) : (∀ i, M i) →ₛₗ[σ] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := by funext i; simp
  map_smul' r x := by funext i; simp [map_smulₛₗ]

private theorem piSL_bij {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} [Finite J]
    {M M' : J → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i)
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f _ (fun _ _ ↦ rfl) hf

theorem liftSemi_pullTot1_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs h
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add (α T), map_smul' := hs T }
  have ha : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ h T (a T) fun _ ↦ rfl
  have hsh : ∀ T, SemiHom (algebraMap R R') (α T) := fun T ↦
    semiHom_coef (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F') T
  refine GlobalTheory.T.liftBaseChange_prod_bijective_semilinear R R' _ _ _ _
    (piSL fun T : C ↦ piSL fun T' : C ↦ piSL fun _ : T ⟶ T' ↦ a T')
    (piSL fun T : C ↦ (hsh T).m1) _ (fun _ ↦ rfl) ?_ ?_
  · exact piSL_bij _ fun T ↦ piSL_bij _ fun T' ↦ piSL_bij _ fun _ ↦ ha T'
  · exact piSL_bij _ fun T ↦
      GlobalTheory.T.bijective_liftSemi_of_semilinear_hom R R' _ _ (α T) (hsh T) (a T) (fun _ ↦ rfl) (ha T)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalTwoCochainsFiniteCategoryBaseChangeBijectivStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalTwoCochains_finiteCategory_baseChange_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot2 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.TotTwoBaseChange.main | exact GlobalTheory.TotTwoBaseChange.main | (intros; apply GlobalTheory.TotTwoBaseChange.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalZeroCochainsFiniteCategoryBaseChangeBijectiStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_liftSemi_tot0_of_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → ∀ g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F', (∀ x T, g x T = α T (x T)) → Function.Bijective (liftSemi g) := by
  first | exact @GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective | exact GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective | (intros; apply GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageExtensionExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepK.PiLocalization₂

theorem stage_first : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  intro hP _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W S hψ hN i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXI⟩ := hX
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hrk := hXI.rank
  have hb1 : 2 * qq D j + 3 ≤ rankV D i j := by
    simp only [rankV, qq, Formalism.BasicNotions.Ranks.r]; omega
  have hb2 : 2 * pp D j ≤ rankV D (i + 1) (j + 1) := by
    simp only [rankV, pp, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨B', Λ₁, ι, x, y, hs, hsig, hsd, hneg⟩ := GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D A' X.rA'.Λ q hXI.rigA'.1 hnA' (by omega) (by omega)
  obtain ⟨WW₁, ΛW, ι', x', y', hs', hsig', hsd', hneg'⟩ :=
    GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D WW X.rW.Λ (p + q) hXI.rigW.1 (by simpa only [add_assoc] using hnW) (by omega) (by omega)
  obtain ⟨rB, eB, hB⟩ := GlobalTheory.RigExists.exists_rig D B' Λ₁ hsig hsd
  obtain ⟨rW, eW, hW⟩ := GlobalTheory.RigExists.exists_rig D WW₁ ΛW hsig' hsd'
  obtain ⟨Y, e1, e2, e3, hY⟩ := GlobalTheory.T.rigidified_family_triple_exists hP D T A A' WW B' WW₁ X W.ψ W.θ _ _ _ _ rB rW W.θ_is hXI hB hW
    (by have := hs.1; omega) (by have := hs'.1; omega)
  refine ⟨B', WW₁, Y, ⟨hp, by omega, hrA, by have := hs.1; omega, hnA, hneg, hneg', hY⟩, e1, ⟨ι, x, y, ?_⟩, ⟨ι', x', y', ?_⟩⟩
  · rw [e2, eB]; exact hs
  · rw [e3, eW]; exact hs'

end GlobalTheory.SqStepK.PiLocalization₂
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisUniformiserConsResidualLiftsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transcendenceBasis_uniformiser_cons_residual_lifts : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) ∧ S.formOrd (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 ∧ S.ord (f : L) = 1 ∧ ∀ g : S.ring, ψ g ≠ 0 → S.ord (g : L) = 0 := by
  first | exact @GlobalTheory.FieldPair.trBasis_uniformiser_cons | exact GlobalTheory.FieldPair.trBasis_uniformiser_cons | (intros; apply GlobalTheory.FieldPair.trBasis_uniformiser_cons <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateBaseChangeAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem translate_baseChange_affineOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (G : Over (Sp R)) [GrpObj G] (V : G.left.Opens), IsAffineOpen V → ∀ (a : Over.mk (spMap ρ) ⟶ G), ∃ W : (pullback G.hom (spMap ρ)).Opens, IsAffineOpen W ∧ ∀ (Ω : Type) [Field Ω] (z : Sp Ω ⟶ pullback G.hom (spMap ρ)) (t : Sp Ω ⟶ Sp R) (x a' : Over.mk t ⟶ G), x.left = z ≫ pullback.fst _ _ → a'.left = z ≫ pullback.snd _ _ ≫ a.left → (∀ w, (x * a').left w ∈ V) → ∀ w, z w ∈ W := by
  intro R R₁ _ _ ρ G _ V hV a
  let f := spMap ρ
  let G₁ := (Over.pullback f).obj G
  let a₁ : Over.mk (𝟙 (Sp R₁)) ⟶ G₁ :=
    Over.homMk (pullback.lift (f := G.hom) (g := f) a.left (𝟙 (Sp R₁))
      ((Over.w a).trans (Category.id_comp _).symm))
      (by show pullback.lift _ _ _ ≫ pullback.snd G.hom f = 𝟙 _; exact pullback.lift_snd _ _ _)
  let e : G₁ ⟶ Over.mk (𝟙 (Sp R₁)) := Over.homMk G₁.hom (by simp)
  let c : G₁ ⟶ G₁ := e ≫ a₁
  have hc : ∀ g : G₁ ⟶ G₁, g ≫ c = c := fun g =>
    by rw [← Category.assoc]; congr 1; ext; simp [e]
  let T : G₁ ⟶ G₁ := 𝟙 G₁ * c
  let T' : G₁ ⟶ G₁ := 𝟙 G₁ * c⁻¹
  have h₁ : T ≫ T' = 𝟙 G₁ := by
    simp only [T', MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, hc, T, mul_inv_cancel_right]
  have h₂ : T' ≫ T = 𝟙 G₁ := by
    simp only [T, MonObj.comp_mul, Category.comp_id, T', hc, inv_mul_cancel_right]
  haveI : IsIso T := ⟨⟨T', h₁, h₂⟩⟩
  haveI : IsIso T.left := Functor.map_isIso (Over.forget _) T
  haveI : IsAffineHom (pullback.fst G.hom f) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback G.hom f).flip
      (inferInstanceAs (IsAffineHom (spMap ρ)))
  refine ⟨(T.left ≫ pullback.fst G.hom f) ⁻¹ᵁ V, hV.preimage _, ?_⟩
  intro Ω _ z t x a' hx ha hxa w
  have ht : t = (z ≫ pullback.snd G.hom f) ≫ f := by
    have h0 : x.left ≫ G.hom = t := Over.w x
    rw [← h0, hx, Category.assoc, pullback.condition, Category.assoc]
  subst ht
  let Z : Over (Sp R₁) := Over.mk (z ≫ pullback.snd G.hom f)
  let z' : Z ⟶ G₁ := Over.homMk z (by simp [G₁, Z])
  have key := (isGrpPullback_pullback G f).2 Z z' (z' ≫ c) x a' (by simpa [z'] using hx)
    (by rw [ha]; simp [z', c, e, a₁, G₁, pullback.lift_fst]; rfl)
  have hT : z' * (z' ≫ c) = z' ≫ T := by simp only [T, MonObj.comp_mul, Category.comp_id]
  rw [hT] at key
  have : (z ≫ T.left ≫ pullback.fst G.hom f) w ∈ V := by
    have e2 : z ≫ T.left ≫ pullback.fst G.hom f = (x * a').left := by
      rw [key]; simp [z']
    rw [e2]; exact hxa w
  simpa using this

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateMulInvIsNonvanishingLocusSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SquareLocus

set_option maxHeartbeats 1000000 in

theorem translate_mul_inv_isLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (V : A.left.Opens), IsLocus c V → ∀ (T : Over S) (a : T ⟶ A), GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull ((a)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 → IsLocus (2 • GlobalTheory.CechPic.pull (fst A T).left c) ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  intro S _ A _ hA c V hV T a h
  have hsq := GlobalTheory.T.theorem_of_square_cechPicard_translates S A hA c (A ⊗ T) (fst A T) (snd A T ≫ a)
  have e1 : (snd A T ≫ a)⁻¹ = snd A T ≫ a⁻¹ := (GrpObj.comp_inv _ _).symm
  have e2 : (1 : A ⊗ T ⟶ A) = snd A T ≫ (1 : T ⟶ A) := (MonObj.comp_one _).symm
  have h0 : pull (snd A T ≫ a).left c + pull (snd A T ≫ a)⁻¹.left c
      - 2 • pull (1 : A ⊗ T ⟶ A).left c = 0 := by
    rw [e1, e2, Over.comp_left, Over.comp_left, Over.comp_left, pull_comp, pull_comp, pull_comp,
      ← map_nsmul, ← map_add, ← map_sub, h, map_zero]
  have h2 : pull (fst A T * (snd A T ≫ a)).left c + pull (fst A T * (snd A T ≫ a)⁻¹).left c
      = 2 • pull (fst A T).left c := by
    rw [hsq, ← sub_eq_zero, ← h0]
    abel
  have hl := (GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)).left c V hV).add
    (GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)⁻¹).left c V hV)
  rw [h2] at hl
  exact hl

end GlobalTheory.SquareLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverAStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), N.IsLB → ∀ (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ) (U : Y.left.Opens), Triv ((LB.div (translDiff (GlobalTheory.TwistFlat.bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x) ((GlobalTheory.TwistFlat.twist A φ N).pull (snd Y (GlobalTheory.TwistFlat.bc A φ)).left)).pull ((fst Y (GlobalTheory.TwistFlat.bc A φ)).left ⁻¹ᵁ U).ι) ↔ Triv ((LB.div (translDiff A L (GlobalTheory.TwistFlat.upa φ x)) (ev N (snd (GlobalTheory.TwistFlat.up φ Y) A) (fst (GlobalTheory.TwistFlat.up φ Y) A ≫ GlobalTheory.TwistFlat.upt φ Y))).pull ((fst (GlobalTheory.TwistFlat.up φ Y) A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.triv_twist_iff | exact GlobalTheory.TwistFlat.triv_twist_iff | (intros; apply GlobalTheory.TwistFlat.triv_twist_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHilbertLatticeContainsAndCoordinateSizeStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHilbertLattice_contains_and_coordinate_size : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N n : ℕ) (L : Lat F) (α : GL (Fin 2) (ZMod N)) (ρ₀ : ℝ), L ≤ stdLat F → (∀ x ∈ stdLat F, (n : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → ![0, (n : F)] ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)) ∧ ∀ v ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)), ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.TwistSize.main | exact GlobalTheory.HilbFam.TwistSize.main | (intros; apply GlobalTheory.HilbFam.TwistSize.main <;> assumption)
end

