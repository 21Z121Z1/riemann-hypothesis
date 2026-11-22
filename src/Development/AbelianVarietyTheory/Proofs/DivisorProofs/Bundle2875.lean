import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem convMul_includeLeft_includeRight {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D] :
    (toConv (Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] D) *
      toConv (Algebra.TensorProduct.includeRight : D →ₐ[R] D ⊗[R] D)).ofConv = Bialgebra.comulAlgHom R D := by
  ext a
  rw [AlgHom.convMul_apply]
  simp only [Bialgebra.comulAlgHom_apply]
  induction (Coalgebra.comul (R := R) a) with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul u v => simp

theorem cobOne_algebraMap {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D] (r : R) :
    cobOne R D (algebraMap R D r) = -algebraMap R (D ⊗[R] D) r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, cobOne_apply, Algebra.algebraMap_eq_smul_one]
  simp [Algebra.TensorProduct.one_def]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem isCan_unique (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (hA : IsAbelianScheme A) (x x' : G.RigExt)
    (hx : IsCan t c x) (hx' : IsCan t c x') : x = x' := by
  obtain ⟨d, z, w, hz, hw, rfl⟩ := hx
  obtain ⟨d', z', w', hz', hw', rfl⟩ := hx'
  obtain ⟨k, hk⟩ := H1.mk_eq_mk.1 (d.cl.trans d'.cl.symm)
  let κ : Fn0 A := fun D _ _ y ↦ k (trivAt y)
  have hκ : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (y : Pt A D), fv d.f D D' φ y - fv d'.f D D' φ y = κ D' (spOver φ ≫ y) - φ (κ D y) := by
    intro D _ _ D' _ _ φ y
    have := congrFun (congrFun (congrFun hk (trivAt y)) (trivAt (spOver φ ≫ y))) (trivMap φ y)
    exact this.symm
  let e : Fn0 (A ⊗ A) := fun D _ _ u ↦
    d.g D (u ≫ fst A A) (u ≫ snd A A) - d'.g D (u ≫ fst A A) (u ≫ snd A A) -
      (κ D ((u ≫ fst A A) * (u ≫ snd A A)) - κ D (u ≫ fst A A) - κ D (u ≫ snd A A))
  have hcob : IsCob (whole (A ⊗ A)) (Fn1.zero _) e := by
    intro D _ _ D' _ _ φ u _
    have h1 := d.add D D' φ (u ≫ fst A A) (u ≫ snd A A)
    have h2 := d'.add D D' φ (u ≫ fst A A) (u ≫ snd A A)
    have h3 := hκ D D' φ ((u ≫ fst A A) * (u ≫ snd A A))
    have h4 := hκ D D' φ (u ≫ fst A A)
    have h5 := hκ D D' φ (u ≫ snd A A)
    rw [comp_mul] at h3
    simp only [e, Fn1.zero, Category.assoc, map_sub]
    linear_combination -h1 + h2 - h3 + h4 + h5
  obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ A) Unit (whole _) (by simp [whole]) (globalFns_holds _ (A ⊗ A)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 e hcob
  have he : ∀ (D : Type) [CommRing D] [Algebra R D] (y y' : Pt A D),
      d.g D y y' - d'.g D y y' - (κ D (y * y') - κ D y - κ D y') = algebraMap R D r := by
    intro D _ _ y y'
    have := hr D (lift y y') (sm_whole _)
    simpa [e] using this
  let b : ∀ n, G.A n := fun n ↦ d.h n - d'.h n - κ _ (t.y n) + algebraMap R (G.A n) r
  have hb : b ∈ G.funs := by
    intro n
    have h1 := d.res n
    have h2 := d'.res n
    have h3 := hκ _ _ (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1))
    rw [t.res] at h3
    have h4 : (G.res n : G.A (n + 1) →ₐ[R] G.A n) (algebraMap R _ r) = algebraMap R _ r := AlgHom.commutes _ _
    change (G.res n : G.A (n + 1) →ₐ[R] G.A n) (b (n + 1)) = b n
    have e1 : ∀ a, (G.res n : G.A (n + 1) →ₐ[R] G.A n) a = G.res n a := fun _ ↦ rfl
    simp only [b, map_sub, map_add, e1] at h3 h4 ⊢
    linear_combination h1 - h2 - h3 + h4
  refine (Submodule.Quotient.eq _).2 ⟨-⟨b, hb⟩, Prod.ext (Subtype.ext (funext fun n ↦ ?_))
    (Subtype.ext (funext fun n ↦ ?_))⟩
  · change cobOne R _ (-b n) = z.1 n - z'.1 n
    rw [hz, hz']
    have hXY := t.mul n (G.A n ⊗[R] G.A n) (toConv Algebra.TensorProduct.includeLeft)
      (toConv Algebra.TensorProduct.includeRight)
    rw [convMul_includeLeft_includeRight] at hXY
    have h0 := he _ (spOver (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) ≫ t.y n)
      (spOver (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] G.A n ⊗[R] G.A n) ≫ t.y n)
    rw [← hXY] at h0
    have hc := hκ _ _ (Bialgebra.comulAlgHom R (G.A n)) (t.y n)
    have hL := hκ _ _ (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) (t.y n)
    have hR := hκ _ _ (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] G.A n ⊗[R] G.A n) (t.y n)
    have hk1 := cobOne_apply (O := R) (κ _ (t.y n))
    have hk2 := cobOne_algebraMap (R := R) (D := G.A n) r
    simp only [Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply] at hc hL hR
    simp only [Dat.coc, b, map_neg, map_add, map_sub]
    linear_combination hk1 - hk2 - h0 + hc - hL - hR
  · change dUnit R (-b n) = w.1 n - w'.1 n
    rw [hw, hw']
    have h0 := GlobalTheory.T.cotVal_sub_eq_dUnit_of_d0_eq_sub R A (G.A n) (t.y n) d.f d'.f k hk
    have h1 : dUnit R (algebraMap R (G.A n) r) = 0 := AugCot.d_algebraMap _ r
    simp only [Dat.om, b]
    change AugCot.d _ _ = _
    simp only [map_neg, map_add, map_sub]
    change -(dUnit R _ - dUnit R _ - dUnit R _ + dUnit R _) = _
    rw [h1]
    change _ = cotVal d.f (t.y n) - dUnit R _ - (cotVal d'.f (t.y n) - dUnit R _)
    rw [show cotVal d.f (t.y n) - dUnit R (d.h n) - (cotVal d'.f (t.y n) - dUnit R (d'.h n)) =
      (cotVal d.f (t.y n) - cotVal d'.f (t.y n)) - dUnit R (d.h n) + dUnit R (d'.h n) by abel, h0]
    abel

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesUnitSectionRigidificationUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_unitSection_rigidification_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W) (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k), T.Carries u σ' σ → ∃ ε : Wˣ, ∀ J J', Good C.P.L.L (cpt W) J → Good T.U.LG.L (cpt W) J' → sval σ (unitW T.G) (cpt W) J * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k = stalkOf (cpt W) (u * ε) * sval σ' (unitW T.G) (cpt W) J' * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  first | exact @GlobalTheory.Mum.Trait.carries_unit | exact GlobalTheory.Mum.Trait.carries_unit | (intros; apply GlobalTheory.Mum.Trait.carries_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyStructureSheafIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lid_baseChange_self {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) (x : K ⊗[K] M) :
    TensorProduct.lid K N (f.baseChange K x) = f (TensorProduct.lid K M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem nonempty_equiv_homology_of_baseChange_self {K : Type} [Field K]
    (S : ShortComplex (ModuleCat.{0} K)) {H : Type} [AddCommGroup H] [Module K H]
    (θ : LinearMap.ker (S.g.hom.baseChange K) →ₗ[K] H) (hs : Function.Surjective θ)
    (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (S.f.hom.baseChange K)) :
    Nonempty (H ≃ₗ[K] S.homology) := by
  have hmem : ∀ x : LinearMap.ker S.g.hom,
      (TensorProduct.lid K S.X₂).symm x.1 ∈ LinearMap.ker (S.g.hom.baseChange K) := by
    intro x
    rw [LinearMap.mem_ker]
    apply (TensorProduct.lid K S.X₃).injective
    rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, map_zero]
    exact x.2
  let q : LinearMap.ker S.g.hom →ₗ[K] H :=
    θ ∘ₗ ((((TensorProduct.lid K S.X₂).symm : S.X₂ →ₗ[K] K ⊗[K] S.X₂) ∘ₗ
      (LinearMap.ker S.g.hom).subtype).codRestrict _ hmem)
  have hq : ∀ x, q x = θ ⟨(TensorProduct.lid K S.X₂).symm x.1, hmem x⟩ := fun x => rfl
  have hsurj : Function.Surjective q := by
    intro h
    obtain ⟨z, rfl⟩ := hs h
    have hz : TensorProduct.lid K S.X₂ z.1 ∈ LinearMap.ker S.g.hom := by
      rw [LinearMap.mem_ker, ← lid_baseChange_self, z.2, map_zero]
    refine ⟨⟨_, hz⟩, ?_⟩
    rw [hq]
    congr 1
    exact Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  have hker : LinearMap.range S.moduleCatToCycles = LinearMap.ker q := by
    ext x
    rw [LinearMap.mem_ker, hq, hk]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(TensorProduct.lid K S.X₁).symm y, ?_⟩
      apply (TensorProduct.lid K S.X₂).injective
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨TensorProduct.lid K S.X₁ y, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid K S.X₂) hy
      rw [lid_baseChange_self, LinearEquiv.apply_symm_apply] at this
      exact this
  exact ⟨((q.quotKerEquivOfSurjective hsurj).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ
    S.moduleCatHomologyIso.toLinearEquiv.symm)⟩

theorem hO_equiv_cech : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (κ : Type) [LinearOrder κ]
    [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    Nonempty (HO1 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 1) ∧
      Nonempty (HO2 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 2) := by
  intro K _ X s κ _ _ D hsep haff hcov
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology K X s κ D hsep haff hcov
  have hsp : spMap (algebraMap K K) = 𝟙 (Sp K) := by
    rw [Algebra.algebraMap_self]; exact Spec.map_id _
  have hP : IsPullback (𝟙 X) s s (spMap (algebraMap K K)) := by
    rw [hsp]; exact IsPullback.id_horiz s
  obtain ⟨h1s, h1k, h2s, h2k⟩ := M.exact hP
  obtain ⟨e1⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 0 1 2) (M.θ1 hP) h1s h1k
  obtain ⟨e2⟩ := nonempty_equiv_homology_of_baseChange_self ((cechLB s (LB.triv X) D).sc' 1 2 3) (M.θ2 hP) h2s h2k
  exact ⟨⟨e1 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv.symm⟩,
    ⟨e2 ≪≫ₗ ((cechLB s (LB.triv X) D).homologyIsoSc' 1 2 3 (by simp) (by simp)).toLinearEquiv.symm⟩⟩

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

namespace GlobalTheory.CechKS

theorem chartPt_sub : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (V : X.Opens) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) (J₀ : Type) (W₀ : J₀ → t.G.left.Opens) (j : J₀ → t.PP.L.ι) (d : J₀ → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hcov : ⨆ i, W₀ i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V)) (hWj : ∀ i, W₀ i ≤ t.PP.L.U (j i)) (hfield : ∀ i, LogKS.IsField (W₀ i) (d i)) (hlift : ∀ i (h : W₀ i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W₀ i) ((t.G.hom.appLE U.1 (W₀ i) h).hom r) = (t.G.hom.appLE U.1 (W₀ i) h).hom (D r)) (hdiff : ∀ (i i' : J₀) (O : t.G.left.Opens), O ≤ W₀ i ⊓ W₀ i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ LogKS.chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, LogKS.IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (d i O f - d i' O f) = ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (hy1 : ∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (m : A.left ⟶ t.G.left) (m' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (u : Fin n → (epsR K ⟶ A)) (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (hm : IsGrpPullback A t.G x0 m) (hm' : IsGrpPullback A' t.G y1 m') (him : i ≫ m' = m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (M : LB A.left) (wg : LB.Iso (t.PP.L.pull m) M) (hwg : wg.IsGen) (i₁ i₂ : J₀) (Ω₁ Ω₂ : t.G.left.affineOpens) (hΩ₁ : Ω₁.1 ≤ W₀ i₁) (hΩ₂ : Ω₂.1 ≤ W₀ i₂) (p₁ p₂ : M.ι) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (O : A'.left.Opens) (f : Γ(A'.left, O)) (w : Fin n → (Sp (DualNumber B) ⟶ A.left)) (hx : x ≫ A.hom = spMap (baseMap K B)) (hxW : ⊤ ≤ x ⁻¹ᵁ ((m ⁻¹ᵁ Ω₁.1 ⊓ M.U p₁) ⊓ (m ⁻¹ᵁ Ω₂.1 ⊓ M.U p₂))) (hxO : ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O)) (hw : ∀ a, IsTransl (baseMap K B) x (u a) (w a)) (l₁ l₂ : Sp B ⟶ A'.left) (h₁ : IsChartPt A' m m' Ω₁.1 (d i₁ Ω₁.1) u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) x l₁) (h₂ : IsChartPt A' m m' Ω₂.1 (d i₂ Ω₂.1) u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂)) x l₂), valR l₁ O f - valR l₂ O f = algebraMap (DualNumber K) B DualNumber.eps * ∑ a, ∑ b, baseMap K B ((Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) a b) * ((valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val) * (valR (w a) (i ⁻¹ᵁ O) ((i.app O).hom f)).snd := by
  intro E _ _ _ H X t V U n v D Θ hv J₀ W₀ j d hcov hWj hfield hlift hdiff K _ x0 hU y1 hU' hy1 A _ A' _ m m' i u
    hi hm hm' him hu M wg hwg i₁ i₂ Ω₁ Ω₂ hΩ₁ hΩ₂ p₁ p₂ B _ _ x O f w hx hxW hxO hw l₁ l₂ h₁ h₂
  have hW₀ : ∀ k, W₀ k ≤ t.G.hom ⁻¹ᵁ U.1 := fun k p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W₀ k) hp
    exact this.1
  have := t.semi.separated
  have hut : ∀ a, IsTangent (u a) := GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart t U v hv x0 hU A m u hm hu
  let Ω : t.G.left.affineOpens :=
    ⟨Ω₁.1 ⊓ Ω₂.1, GlobalTheory.T.isAffineOpen_inf_of_separated_over_affineOpen t.G.hom U Ω₁ Ω₂ (hΩ₁.trans (hW₀ _)) (hΩ₂.trans (hW₀ _))⟩
  have e₁ : Ω.1 ≤ Ω₁.1 := inf_le_left
  have e₂ : Ω.1 ≤ Ω₂.1 := inf_le_right
  have hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1) := fun p hp => ⟨(hxW hp).1.1, (hxW hp).2.1⟩
  obtain ⟨l₁', k₁⟩ := GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ i₁) (hW₀ i₁) (d i₁) (hfield i₁) (hlift i₁ (hW₀ i₁)) x0 hU y1 hU' hy1
    A A' m m' u hm hm' hu Ω (e₁.trans hΩ₁) (Matrix.of fun a b => ev x0 U.1 hU (Θ a b))
    (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) B x hx hxΩ
  obtain ⟨l₂', k₂⟩ := GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ i₂) (hW₀ i₂) (d i₂) (hfield i₂) (hlift i₂ (hW₀ i₂)) x0 hU y1 hU' hy1
    A A' m m' u hm hm' hu Ω (e₂.trans hΩ₂) (Matrix.of fun a b => ev x0 U.1 hU (Θ a b))
    (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂)) B x hx hxΩ
  obtain rfl : l₁' = l₁ := (k₁.of_le (hfield i₁) e₁ hΩ₁ hx hxΩ hut).unique hm'.1 h₁
  obtain rfl : l₂' = l₂ := (k₂.of_le (hfield i₂) e₂ hΩ₂ hx hxΩ hut).unique hm'.1 h₂
  have hwt : ∀ a, transl (baseMap K B) x (u a) = w a := fun a => (isTransl_transl _ x hx (u a)).unique (hw a)
  have hwx := fun a => (hw a).red (hut a)
  have := isAffineHom_of_field x0
  have : IsAffineHom m := MorphismProperty.of_isPullback (P := @IsAffineHom) hm.1.flip inferInstance
  obtain ⟨S, hS, hSx, hSv⟩ := GlobalTheory.T.exists_linearCombination_tangentVectors_affineOpen A.hom ⟨m ⁻¹ᵁ Ω.1, Ω.2.preimage m⟩ (baseMap K B) x hx hxΩ w
    (fun a => (hw a).w) hwx (fun a => ∑ b, baseMap K B ((Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) a b) *
      ((valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val))
  have hx₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) :=
    fun p hp => ⟨(hxW hp).1.2, Set.mem_iInter.2 fun _ => hWj i₁ (hΩ₁ (hxW hp).1.1)⟩
  have hx₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) :=
    fun p hp => ⟨(hxW hp).2.2, Set.mem_iInter.2 fun _ => hWj i₂ (hΩ₂ (hxW hp).2.1)⟩
  have hlog : ∀ b, (valR (w b) _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val =
      (valR (w b ≫ m) _ (t.PP.L.g (j i₁) (j i₂)).val).snd * valR (x ≫ m) _ (t.PP.L.g (j i₁) (j i₂))⁻¹.val +
      (dlogAt (baseMap K B) x (u b) (M.U p₁ ⊓ (t.PP.L.pull m).U (fun _ => j i₁)) (wg.s (p₁, fun _ => j i₁)) -
        dlogAt (baseMap K B) x (u b) (M.U p₂ ⊓ (t.PP.L.pull m).U (fun _ => j i₂)) (wg.s (p₂, fun _ => j i₂))) := by
    intro b
    unfold dlogAt
    rw [hwt]
    exact GlobalTheory.T.logDerivative_transitionUnits_isoLineBundles m t.PP.L M wg hwg (j i₁) (j i₂) p₁ p₂ x (w b) (hwx b) hx₁ hx₂
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := hxΩ
  have hbase : (x ≫ m) ≫ t.G.hom = spMap ((baseMap K B).comp (ev x0 U.1 hU)) ≫ LogKS.chart U := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hx, GlobalTheory.Cris.spMap_comp (ev x0 U.1 hU), Category.assoc]
    exact congrArg _ (GlobalTheory.FlagMod.spMap_ev x0 U.2 hU).symm
  rw [GlobalTheory.T.firstOrderDeformation_points_differ_eps_allOpens hi.1.w hm'.1 him U hU' Ω ((e₁.trans hΩ₁).trans (hW₀ _)) x hxΩ S hS hSx l₁' l₂' k₁.1 k₂.1 k₁.2.1 k₂.2.1
    (fun f => ⟨_, k₂.2.2 f⟩) ?_ O hxO f, hSv _ hxO]
  · simp only [Finset.sum_mul]
  · intro f
    have hd := hdiff i₁ i₂ Ω.1 (le_inf (e₁.trans hΩ₁) (e₂.trans hΩ₂)) f B _ (x ≫ m) (fun a => w a ≫ m) hbase hxm
      (fun a => GlobalTheory.T.isTranslateOfTangentVector_fibre_to_groupScheme t x0 A m hm _ (v a) (u a) (hu a) _ x hx (w a) (hw a))
    rw [valR_eq_ev _ _ hxm, map_sub, ← valR_eq_ev, ← valR_eq_ev] at hd
    rw [k₁.2.2, k₂.2.2, valR_comp_app S, hSv _ hxΩ]
    unfold chartVal
    simp only [← valR_comp_app, hwt, hlog]
    rw [add_sub_add_left_eq_sub, ← mul_sub, add_sub_add_comm, hd, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
    rw [← Finset.sum_mul, ← sub_mul, ← add_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine congrArg (· * _) (Finset.sum_congr rfl fun b _ => ?_)
    simp only [Matrix.of_apply, RingHom.comp_apply]
    ring

theorem isCechKS_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ a, IsTanAtG t (LogKS.chart U) (v a)) → LogKS.IsKS t V U v D Θ → ∀ (K : Type) [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1), ⊤ ≤ x0 ⁻¹ᵁ V → ∀ (y1 : Sp (DualNumber K) ⟶ X) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1), (∀ r, ev y1 U.1 hU' r = TrivSqZeroExt.inl (ev x0 U.1 hU r) + TrivSqZeroExt.inr (ev x0 U.1 hU (D r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ι : A.left ⟶ t.G.left) (ι' : A'.left ⟶ t.G.left) (i : A.left ⟶ A'.left) (u : Fin n → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A t.G x0 ι → IsGrpPullback A' t.G y1 ι' → i ≫ ι' = ι → (∀ a, (u a).left ≫ ι = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) → ∀ (M : LB A.left), ⨆ k, M.U k = ⊤ → LBIso (t.PP.L.pull ι) M → GlobalTheory.CechKS.IsCechKS A A' i M u (Matrix.of fun a b => ev x0 U.1 hU (Θ a b)) := by
  intro E _ _ _ H X t V U n v D Θ hv hKS K _ x0 hU hV y1 hU' hy1 A _ A' _ ι ι' i u hi hι hι' hιι' hu M hM hiso
  obtain ⟨J₀, W₀, j, d, hcov, hWj, hfield, hlift, hdiff⟩ := hKS
  obtain ⟨wg, hwg⟩ := hiso
  have hW₀ : ∀ k, W₀ k ≤ t.G.hom ⁻¹ᵁ U.1 := fun k p hp => by
    have : p ∈ t.G.hom ⁻¹ᵁ (U.1 ⊓ V) := hcov ▸ (le_iSup W₀ k) hp
    exact this.1
  let θ : Matrix (Fin n) (Fin n) K := Matrix.of fun a b => ev x0 U.1 hU (Θ a b)
  let lam : ∀ (_ : Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι) (B : Type) [CommRing B]
      [Algebra (DualNumber K) B], (Sp B ⟶ A.left) → (Sp B ⟶ A'.left) :=
    fun k B _ _ x => chartPt A' i ι ι' k.2.1.1.1 (d k.1 k.2.1.1.1) u θ
      (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1)) (wg.s (k.2.2, fun _ => j k.1)) x
  have hex : ∀ (k : Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι) (B : Type) [CommRing B]
      [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left), x ≫ A.hom = spMap (baseMap K B) →
      ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) →
      IsChartPt A' ι ι' k.2.1.1.1 (d k.1 k.2.1.1.1) u θ (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1))
        (wg.s (k.2.2, fun _ => j k.1)) x (lam k B x) := by
    intro k B _ _ x hx hxΩ
    exact isChartPt_chartPt _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.CechKS.exists_isChartPt t U v D hv (W₀ k.1) (hW₀ k.1) (d k.1)
      (hfield k.1) (hlift k.1 (hW₀ k.1)) x0 hU y1 hU' hy1 A A' ι ι' u hι hι' hu k.2.1.1 k.2.1.2 θ _ _ B x hx hxΩ)
  refine ⟨Σ k : J₀, {Ω : t.G.left.affineOpens // Ω.1 ≤ W₀ k} × M.ι, fun k => ι ⁻¹ᵁ k.2.1.1.1 ⊓ M.U k.2.2,
    fun k => k.2.2, lam, ?_, fun k => inf_le_right, ?_, ?_⟩
  · refine eq_top_iff.2 fun a _ => ?_
    have h1 : (ι ≫ t.G.hom).base a ∈ U.1 ⊓ V := by
      rw [hι.1.w]
      exact ⟨hU (Set.mem_univ (A.hom.base a)), hV (Set.mem_univ (A.hom.base a))⟩
    have h2 : ι.base a ∈ ⨆ k, W₀ k := by
      rw [hcov]
      exact h1
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    obtain ⟨Ω, hΩB, haΩ, hΩk⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 t.G.left.isBasis_affineOpens hk
    have h3 : a ∈ ⨆ p, M.U p := by
      rw [hM]
      trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 h3
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, ⟨⟨Ω, hΩB⟩, hΩk⟩, p⟩, haΩ, hp⟩
  · intro k B _ _ x hx hxW
    have hxΩ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) := fun p hp => (hxW hp).1
    have hP := hex k B x hx hxΩ
    refine ⟨hP.1, GlobalTheory.T.deformationChartPoint_reduction_eq_specialFibre hi hι'.1 hιι' hx hxΩ hP, fun B' _ _ ρ => ?_⟩
    have hx' : (spMap (ρ : B →+* B') ≫ x) ≫ A.hom = spMap (baseMap K B') := by
      rw [Category.assoc, hx]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, AlgHom.comp_algebraMap]
    have hxΩ' : ⊤ ≤ (spMap (ρ : B →+* B') ≫ x) ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) :=
      fun p _ => hxΩ (Set.mem_univ ((spMap (ρ : B →+* B')).base p))
    have hxWo : ⊤ ≤ x ⁻¹ᵁ (M.U k.2.2 ⊓ (t.PP.L.pull ι).U (fun _ => j k.1)) :=
      fun p hp => ⟨(hxW hp).2, Set.mem_iInter.2 fun _ => hWj k.1 (k.2.1.2 (hxW hp).1)⟩
    exact (GlobalTheory.T.isDeformationChartPoint_spec_map hx hxΩ hxWo (GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart t U v hv x0 hU A ι u hι hu) hP B' ρ).unique hι'.1 (hex k B' _ hx' hxΩ')
  · intro k k' B _ _ x O f w hx hxW hxO hw
    have h₁ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k.2.1.1.1) := fun p hp => (hxW hp).1.1
    have h₂ : ⊤ ≤ x ⁻¹ᵁ (ι ⁻¹ᵁ k'.2.1.1.1) := fun p hp => (hxW hp).2.1
    exact chartPt_sub t V U v D Θ hv J₀ W₀ j d hcov hWj hfield hlift hdiff x0 hU y1 hU' hy1 A A' ι ι' i u hi hι
      hι' hιι' hu M wg hwg k.1 k'.1 k.2.1.1 k'.2.1.1 k.2.1.2 k'.2.1.2 k.2.2 k'.2.2 B x O f w hx hxW hxO hw _ _
      (hex k B x hx h₁) (hex k' B x hx h₂)

end GlobalTheory.CechKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundlePullTrivialOfPointwiseGeneratorStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB → ∀ (q : Y ⟶ X) (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E), IsPtGen L q t → GlobalTheory.AbLaw.Triv (L.pull q.left) := by
  first | exact @GlobalTheory.PtExt.triv_pull_of_isPtGen | exact GlobalTheory.PtExt.triv_pull_of_isPtGen | (intros; apply GlobalTheory.PtExt.triv_pull_of_isPtGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrameStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_columns_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι), VB.IsFrame (cellCol ι N w τ) := by
  first | exact @GlobalTheory.FlagZ.Univ.isFrame_cellCol | exact GlobalTheory.FlagZ.Univ.isFrame_cellCol | (intros; apply GlobalTheory.FlagZ.Univ.isFrame_cellCol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagPointStalkStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_flag_point_stalk : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (fun τ => Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)) = (Fl ι N).fromSpecStalk y := by
  first | exact @GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk | exact GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk | (intros; apply GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagStalkSpanStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_flag_stalk_span : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), colSpan (Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)).1 l = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellOpen ι N w) y hy (cellCol ι N w τ j)} := by
  first | exact @GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL | exact GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL | (intros; apply GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMapOfIntegralMatrixAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.MatChar

theorem charMap_matrix : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom f → EndChar U f m → (∀ u, f ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ u χ, m (c u χ) = ∑ v, a u v • c v χ := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq c hc a f m hf hm hfq u χ
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  obtain ⟨-, hone, hmul⟩ := GlobalTheory.Poinc.Eq8.torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U
  have huniq : ∀ (β : G.left ⟶ G₀.left) (ρ ρ' : D₀.toPre.X →+ D.toPre.X), TorMatch U₀ U (RingHom.id V₁) β ρ →
      TorMatch U₀ U (RingHom.id V₁) β ρ' → ρ = ρ' := fun β ρ ρ' =>
    GlobalTheory.Poinc.Eq8.torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) β Function.injective_id ρ ρ'
  have hinv : ∀ (p : G ⟶ G₀) [IsMonHom p] (ρ : D₀.toPre.X →+ D.toPre.X), TorMatch U₀ U (RingHom.id V₁) p.left ρ →
      TorMatch U₀ U (RingHom.id V₁) (p⁻¹).left (-ρ) := by
    intro p _ ρ hp
    obtain ⟨ρ', hρ'⟩ := GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U p⁻¹ inferInstance
    have h1 := hmul p p⁻¹ ρ ρ' hp hρ'
    rw [mul_inv_cancel] at h1
    have h2 : ρ + ρ' = 0 := huniq _ _ _ h1 hone
    have h3 : ρ' = -ρ := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
    rwa [← h3]
  have hnpow : ∀ (p : G ⟶ G₀) (ρ : D₀.toPre.X →+ D.toPre.X) (n : ℕ), TorMatch U₀ U (RingHom.id V₁) p.left ρ →
      TorMatch U₀ U (RingHom.id V₁) (p ^ n).left (n • ρ) := by
    intro p ρ n hp
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact hone
    | succ n ih => rw [pow_succ, succ_nsmul]; exact hmul _ _ _ _ ih hp
  have hzpow : ∀ (p : G ⟶ G₀) [IsMonHom p] (ρ : D₀.toPre.X →+ D.toPre.X) (k : ℤ),
      TorMatch U₀ U (RingHom.id V₁) p.left ρ → TorMatch U₀ U (RingHom.id V₁) (p ^ k).left (k • ρ) := by
    intro p _ ρ k hp
    cases k with
    | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast, natCast_zsmul]; exact hnpow p ρ n hp
    | negSucc n =>
      rw [zpow_negSucc, ← inv_pow, negSucc_zsmul, ← smul_neg]
      exact hnpow _ _ (n + 1) (hinv p ρ hp)
  have hprod : ∀ (n : ℕ) (g : Fin n → (G ⟶ G₀)) (r : Fin n → (D₀.toPre.X →+ D.toPre.X)),
      (∀ i, TorMatch U₀ U (RingHom.id V₁) (g i).left (r i)) →
      TorMatch U₀ U (RingHom.id V₁) (List.ofFn g).prod.left (∑ i, r i) := by
    intro n
    induction n with
    | zero => intro g r _; rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]; exact hone
    | succ n ih =>
      intro g r h
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact hmul _ _ _ _ (h 0) (ih _ _ fun i => h i.succ)
  have hright : TorMatch U₀ U (RingHom.id V₁) (f ≫ q u).left (∑ v, a u v • c v) := by
    rw [hfq u]
    exact hprod 8 _ _ fun v => haveI := hq v; hzpow (q v) (c v) (a u v) (hc v)
  have hleft := GlobalTheory.Poinc.Eq8.torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q u).left
    V₁ hB G hG D P U (RingHom.id V₁) f.left Function.injective_id (fun _ hk => hk) (c u) m (hc u)
    (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V₁ hB G hG D P U f hf m hm)
  rw [RingHom.id_comp, ← Over.comp_left] at hleft
  have e := huniq _ _ _ hleft hright
  have e' := DFunLike.congr_fun e χ
  rw [AddMonoidHom.comp_apply, AddMonoidHom.finset_sum_apply] at e'
  exact e'

end GlobalTheory.Poinc.MatChar
end

