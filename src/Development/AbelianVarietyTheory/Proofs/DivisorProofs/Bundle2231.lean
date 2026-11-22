import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFunEqMinIntLinearFormsOnCones
section
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.PolFan

theorem evalZ_eq_of_nsmul_eq_sum {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {φ : InvFun O} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) {b : LinearMap.BilinForm ℤ X} {k : ℕ}
    (hk : 0 < k) {cf : Fin m → ℕ} (he : k • b = ∑ j, cf j • γ j) :
    φ.evalZ b = ∑ j, ((cf j : ℝ) / k) * φ.evalZ (γ j) := by
  rw [← (linearOn_iff φ γ).1 h _ (fun j => by positivity), ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := LinearMap.congr_fun₂ he x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h1
  have h2 : (k : ℝ) * b x y = ∑ j, (cf j : ℝ) * γ j x y := by exact_mod_cast h1
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show ∑ j, (cf j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (cf j : ℝ) * γ j x y) / k by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring, ← h2]
  field_simp

theorem cones_eq_min_linear : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) →
    ∃ (Nℓ : ℕ) (ℓ : Fin p → LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ), 0 < Nℓ ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) →
      (∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j) →
      (∀ i, (Nℓ : ℝ) * φ.evalZ b' ≤ ℓ i b') ∧ ∃ i, (Nℓ : ℝ) * φ.evalZ b' = ℓ i b' := by
  intro O _ bar φ Y _ _ _ p m γ hγ
  choose N ℓ hN h1 h2 h3 using fun i => (hγ i).strict
  refine ⟨∏ i, N i, fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℤ) • ℓ i,
    Finset.prod_pos fun i _ => hN i, ?_⟩
  rintro b' hb hp ⟨i, k, cf, hk, he⟩
  have key : ∀ i, ((∏ j, N j : ℕ) : ℝ) = ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℝ) * N i := fun i => by
    rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have eq : ∀ i, (N i : ℝ) * φ.evalZ b' ≤ ℓ i b' := fun i => h2 i b' hb hp
  refine ⟨fun i' => ?_, i, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i', mul_assoc]
    exact mul_le_mul_of_nonneg_left (eq i') (by positivity)
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i, mul_assoc]
    congr 1
    have hev := evalZ_eq_of_nsmul_eq_sum (hγ i).linear hk he
    have hl : (k : ℤ) * ℓ i b' = ∑ j, (cf j : ℤ) * ℓ i (γ i j) := by
      have := congrArg (ℓ i) he
      simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    have hl' : (k : ℝ) * ℓ i b' = ∑ j, (cf j : ℝ) * ℓ i (γ i j) := by exact_mod_cast hl
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [hev, Finset.mul_sum, show (ℓ i b' : ℝ) = (∑ j, (cf j : ℝ) * ℓ i (γ i j)) / k by
      rw [← hl']; field_simp, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 i j]
    field_simp

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsArithVarEffCartier
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.BlowArith

theorem exists_isArithVar_effCartier (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsArithVar (ρ ≫ p) D ∧
      ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0 ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) := by
  have := hX.isNoetherianRing
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup p hX.isProjOver J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : b.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have := hX.charZero
    have : IsDominant b := ⟨by
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant b
    have hinj' : Function.Injective b.appTop := Scheme.Hom.app_injective b ⊤
    exact charZero_of_injective_ringHom (f := b.appTop.hom) hinj'
  exact ⟨Y, b, ‹_›, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩,
    hgen, hdeg, hb.1⟩

end GlobalTheory.BlowArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.KeyLieChg

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem lieComb_of_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left)
    (hu'v' : ∀ i, (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left) (i : Fin m) :
    IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i) := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).1 (hu'v' i)

theorem constFn_one {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    Geo.Tor.constFn p U (1 : R) = 1 := by
  simp [Geo.Tor.constFn]

theorem exists_keyPB_det : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R : Type) [CommRing R] (y : KeyIn R) (x : KeyIn ℂ) (f : R →+* ℂ), KeyPB x y f → ∀ (v' : Fin y.P.g → (epsR R ⟶ y.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin y.P.g) (Fin y.P.g) R), (∀ i, IsLieComb (M i) y.v (v' i)) → ∃ x' : KeyIn ℂ, KeyPB x' ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'⟩ f ∧ (κ ℂ x' : ℂ) = (M.map f).det ^ 4 * κ ℂ x := by
  intro κ hκ R _ y x f hxy v' hv' M hM
  obtain ⟨φ, he, w, hg, F, hp, hw, hrig, hsec, hF, hε, hlie⟩ := hxy
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  subst hF'
  haveI := y.P.isAb.comm
  haveI := x.P.isAb.comm
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange R ℂ f y.P.A x.P.A φ hp y.P.isAb.smooth y.P.g v' hv'
  have hb : IsLieBasis (fun i : Fin x.P.g => u (i.cast hg)) := isLieBasis_cast hg hu
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, fun i => u (i.cast hg), hb⟩,
    ⟨φ, he, w, hg, Chart.dualMapR f, hp, hw, hrig, hsec, hF, hε, fun i => huv (i.cast hg)⟩, ?_⟩
  have hc := lieComb_of_over f hp hg M y.v v' x.v (fun i => u (i.cast hg)) hM hlie (fun i => huv (i.cast hg))
  have k := hκ ℂ x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne (fun i => u (i.cast hg)) hb 1
    (fun i j => f (M (i.cast hg) (j.cast hg))) (fun i => by rw [constFn_one, _root_.one_mul]) hc
  have hd : (Matrix.of fun i j : Fin x.P.g => f (M (i.cast hg) (j.cast hg))).det = (M.map f).det :=
    Matrix.det_submatrix_equiv_self (finCongr hg) (M.map f)
  simp only [Nat.mul_one, one_pow, _root_.one_mul] at k
  rw [k]
  exact congrArg (· ^ 4 * (κ ℂ x : ℂ)) hd

end GlobalTheory.KeyLieChg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumFibreOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem exists_keyAtMap_of_isGrpPullback : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (y : KeyIn R)
    (P : PolAV (Sp K)) (φ : P.A.left ⟶ y.P.A.left) (hp : 1 ≤ P.g) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (hr : rig.IsGen), P.g = y.P.g → IsGrpPullback P.A y.P.A (spMap f) φ → LBIso P.L (y.P.L.pull φ) →
    ∃ th hth v hv, KeyAtMap ⟨P, hp, rig, hr, th, hth, v, hv⟩ y f φ := by
  intro R K _ _ f y P φ hp rig hr hg h hI
  obtain ⟨w, hw0⟩ := hI
  have hw := (isGen_iff w).1 hw0
  have he : eSec P.A ≫ φ = spMap f ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  have := P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  obtain ⟨w', g', m'⟩ := KeyPow.exists_rescale y.P.isLB P.isLB hw (p := P.A.hom) (Over.w η[P.A]) he hr y.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down g' y.P.isLB P.isLB y.th
  have := P.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R K f y.P.A P.A φ h y.P.isAb.smooth y.P.g y.v y.basis
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact hb'
  refine ⟨th', SectionBaseChange.fibre_nonzero_of_pull P.isLB hth' h.1 y.th_ne, _, hb hg, he, w', hg,
    Chart.dualMapR f, h, (isGen_iff _).2 g',
    (maps_iff w' _ (fun _ => eSec y.P.A) _ rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2 m',
    KeyPow.appLE_eq_of_stalk _ y.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumPolarisedAbelianLocalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem exists_keyIn_local : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W]
    (P : PolAV (Sp W)), 1 ≤ P.g → ∃ y : KeyIn W, y.P = P := by
  intro W _ _ _ _ P hg
  have hL := GlobalTheory.abelianSchemeLaws_all
  let m : PrimeSpectrum W := IsLocalRing.closedPoint W
  obtain ⟨th, a, ha, -, hth⟩ := GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes hL.1 hL.2 W P m m
  have c : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨b, hb, -, v, hv⟩ := GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes W P.A P.g P.smoothDim m m
  have hbu : IsUnit b := (IsLocalRing.mem_maximalIdeal b).not.mp hb |> not_not.mp
  let g : Localization.Away b →+* W := IsLocalization.Away.lift (g := RingHom.id W) b hbu
  have hgf : g.comp (algebraMap W (Localization.Away b)) = RingHom.id W := by
    ext x; simp [g]
  have h₁ := isGrpPullback_pullback P.A (spMap (algebraMap W (Localization.Away b)))
  have hA₁ := Out.TLinPf.isAb_pullback (spMap (algebraMap W (Localization.Away b))) P.A P.isAb
  have c₁ := hA₁.comm
  have e : spMap g ≫ spMap (algebraMap W (Localization.Away b)) = 𝟙 (Sp W) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgf, CommRingCat.ofHom_id, Spec.map_id]
  have w₁ : 𝟙 P.A.left ≫ P.A.hom = (P.A.hom ≫ spMap g) ≫ spMap (algebraMap W (Localization.Away b)) := by
    rw [Category.assoc, e]; simp
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 P.A))
  have hid : IsGrpPullback P.A P.A (𝟙 _) (𝟙 P.A.left) := isGrpPullback_of_iso (Iso.refl P.A)
  have h₂ : IsGrpPullback P.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (hid.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange _ W g _ P.A _ h₂ hA₁.smooth P.g v hv
  obtain ⟨rig, hr⟩ := P.rigid
  refine ⟨⟨P, hg, rig, hr, th, fun s => hth s fun h => ?_, v', hb'⟩, rfl⟩
  have hs : s.asIdeal ≤ IsLocalRing.maximalIdeal W := IsLocalRing.le_maximalIdeal s.isPrime.ne_top
  exact ha (hs h)

end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyInNf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_keyIn_nf :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), 1 ≤ g → τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → c ≠ 0 → Mx.det ≠ 0 → ∃ (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) := by
  intro g τ a b c Mx hg hs hp ha hb hc hM
  obtain ⟨x, h, u, τ', a', b', e₁, e₂, e₃, -, -, -, -, h₃, h₄, h₅, h₆⟩ :=
    GlobalTheory.KeyOfPeriod.exists_keyIn_classicalFrame g τ a b hg hs hp ha hb
  subst h
  obtain rfl : τ' = τ := e₁
  obtain rfl : a' = a := e₂
  obtain rfl : b' = b := e₃
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hbas⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (Mx i)).exists
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyNormalExists.constMul x.P.A.hom c x.th, fun s => ?_, v,
    (hbas Mx v x.basis hv).2 hM.isUnit⟩, rfl, u, hs, hp, ha, hb, hc, h₃, h₄,
    KeyNormalExists.isFn_constMul u c h₅, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, KeyNormalExists.mem_nonzeroLocus_constMul _ hc.isUnit _ hz'⟩
  · have h1 := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (Mx i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, Mx i j • (Pi.single j (2 * Real.pi * Complex.I : ℂ)⁻¹ : Fin x.P.g → ℂ) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx i := by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, MulZeroClass.mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [e] at h1
    exact h1

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

namespace GlobalTheory.LevelMapBase

theorem levelMap_coeff_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    1 ≤ Dw.p + Dw.q → l.Dvd l' →
    ∃ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (r₀ : Xo'.X ⟶ Xo.X) (_ : SABMap Xo'.univ.t Xo.univ.t r₀),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r₀ ∧ IsFinite (pullback.lift r _ h) ∧ Etale (pullback.lift r _ h) ∧
        Surjective (pullback.lift r _ h) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' hle hpq hd
  obtain ⟨r₀, jK, m, hk, -, -, -, -, hc⟩ := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hpq).1 l l' Xo Xo' hd
  have hle₁ : KA l ≤ c'.F := fun x hx => by
    have := c'.le (jK ⟨x, hx⟩).2
    rwa [hk] at this
  let c₁ : Coeff l :=
    { F := c'.F
      fin := c'.fin
      conj := c'.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := GlobalTheory.LevelExist.zeta_eq_pow_of_dvd (a := l.M') (GlobalTheory.LevelExist.M'_pos l')
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l.M' ∣ l'.M')
        rw [he]
        exact pow_mem c'.zeta_mem e
      le := hle₁ }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₁ c' rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c'.F)).toRingHom = 𝟙 (Sp c'.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion hle).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom =
      spMap (IntermediateField.inclusion c₁.le).toRingHom := by
    rw [← Spec.map_comp]
    rfl
  let b : Xo.XF c₁ ⟶ Xo.XF c :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (by rw [Category.assoc, hi, pullback.condition])
  have hb1 : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hb2 : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom :=
    pullback.lift_snd _ _ _
  have hp : IsPullback b (pullback.snd _ _) (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
      (spMap (IntermediateField.inclusion hle).toRingHom) := by
    refine IsPullback.of_right ?_ hb2 (IsPullback.of_hasPullback _ _)
    rw [hb1, hi]
    exact IsPullback.of_hasPullback _ _
  have h : (rF ≫ b) ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
      pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, hb2, reassoc_of% e2']
  have hlift : pullback.lift (rF ≫ b) _ h = rF ≫ hp.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, e2']
  refine ⟨rF ≫ b, h, r₀, m, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hb1, e1]
  · rw [hlift]; infer_instance
  · rw [hlift]; infer_instance
  · rw [hlift]; infer_instance

end GlobalTheory.LevelMapBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFiberIsAlgebraicResidueFieldOfLft
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

namespace GlobalTheory

theorem isAlgebraic_residueField_transport {X : Scheme.{0}} {w x : X} (h : w = x) {C : CommRingCat.{0}}
    (ψ : X.residueField w ⟶ C) (φ : X.residueField x ⟶ C)
    (e : Spec.map ψ ≫ X.fromSpecResidueField w = Spec.map φ ≫ X.fromSpecResidueField x)
    (hφ : letI := φ.hom.toAlgebra; Algebra.IsAlgebraic (X.residueField x) C) :
    letI := ψ.hom.toAlgebra; Algebra.IsAlgebraic (X.residueField w) C := by
  subst h
  have : ψ = φ := Spec.map_injective ((cancel_mono _).mp e)
  subst this
  exact hφ

theorem exists_mem_fiber_isAlgebraic_residueField :
    ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧
      (letI := (π.residueFieldMap y).hom.toAlgebra;
        Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) := by
  intro Y X π _ y₀
  let x := π y₀
  let s : π.fiber x ⟶ Spec (X.residueField x) := π.fiberToSpecResidueField x
  haveI : LocallyOfFiniteType s := by
    show LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  haveI : JacobsonSpace (π.fiber x) := LocallyOfFiniteType.jacobsonSpace s
  have hx : y₀ ∈ Set.range (π.fiberι x) := by
    rw [π.range_fiberι]; rfl
  obtain ⟨y₀', -⟩ := hx
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set (π.fiber x)))
    ⟨y₀', trivial⟩ isClosed_univ.isLocallyClosed
  have h1 : LocallyOfFiniteType ((π.fiber x).fromSpecResidueField z) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((π.fiber x).fromSpecResidueField z ≫ s)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  have halg : letI := φ.hom.toAlgebra;
      Algebra.IsAlgebraic (X.residueField x) ((π.fiber x).residueField z) := by
    letI : Algebra (X.residueField x) ((π.fiber x).residueField z) := φ.hom.toAlgebra
    haveI : Algebra.FiniteType (X.residueField x) ((π.fiber x).residueField z) := hft
    haveI : Module.Finite (X.residueField x) ((π.fiber x).residueField z) :=
      finite_of_finite_type_of_isJacobsonRing _ _
    exact Algebra.IsAlgebraic.of_finite _ _
  let y : Y := π.fiberι x z
  have hy : π y = x := by
    have : y ∈ Set.range (π.fiberι x) := ⟨z, rfl⟩
    rw [π.range_fiberι] at this
    exact this
  refine ⟨y, hy, ?_⟩
  let g := (π.fiberι x).residueFieldMap z
  let ψ := π.residueFieldMap y ≫ g
  have e : Spec.map ψ ≫ X.fromSpecResidueField (π y) = Spec.map φ ≫ X.fromSpecResidueField x := by
    have e2 : π.fiberι x ≫ π = s ≫ X.fromSpecResidueField x := pullback.condition
    rw [hφ, Category.assoc, ← e2, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
  have hψ := isAlgebraic_residueField_transport hy ψ φ e halg
  letI : Algebra (X.residueField (π y)) (Y.residueField y) := (π.residueFieldMap y).hom.toAlgebra
  letI : Algebra (Y.residueField y) ((π.fiber x).residueField z) := g.hom.toAlgebra
  letI : Algebra (X.residueField (π y)) ((π.fiber x).residueField z) := ψ.hom.toAlgebra
  haveI : IsScalarTower (X.residueField (π y)) (Y.residueField y) ((π.fiber x).residueField z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.IsAlgebraic.tower_bot_of_injective (R := X.residueField (π y)) (A := (π.fiber x).residueField z) g.hom.injective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomOverAlgebraicClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mon_hom_over_algebraic_closure : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A', IsMonHom f → ∃ g : (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (algebraicClosure K Ω)))).obj A', IsMonHom g ∧ GlobalTheory.Spread.bcMap A.hom (algebraicClosure K Ω).val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.ChowRigid.chow_rigidity | exact GlobalTheory.ChowRigid.chow_rigidity | (intros; apply GlobalTheory.ChowRigid.chow_rigidity <;> assumption)
end

