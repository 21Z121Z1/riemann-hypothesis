import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsProjectiveRankStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_global_oneForms_projective_rank : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FP R (GlobForm A.hom) g := by
  first | exact @GlobalTheory.AbCoh.globForm_FP | exact GlobalTheory.AbCoh.globForm_FP | (intros; apply GlobalTheory.AbCoh.globForm_FP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsoLineBundleSectionsTransfer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.BasisMatch
open GlobalTheory.AbLaw GlobalTheory.Cartier TensorProduct

theorem topEquiv_pull {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Sp R}
    {f' : X' ⟶ Sp R'} {π : X' ⟶ X} {g : R →+* R'} (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
    (M : LB X) (x : SecOnR f M ⊤) :
    SecOnR.topEquiv f' (M.pull π) (SecOnR.pull M w ⊤ ⊤ le_top x) = secPull (SecOnR.topEquiv f M x) π := by
  refine DVR.SecOps.sec_ext fun i => ?_
  refine (congrArg (rs X' _) (SecOn.coord_pullLE π le_top x i)).trans ?_
  change (π.appLE _ _ _ ≫ X'.presheaf.map _).hom _ = (X.presheaf.map _ ≫ π.appLE _ _ _).hom _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

theorem secMaps_congr {Y : Scheme.{0}} {L N : LB Y} (hL : L.IsLB) (hN : N.IsLB) (w : LB.Iso L N)
    (hw : w.IsGen) (a : L.Sec) :
    SecMaps w a (SecOn.topEquiv N (SecOn.congr hL hN w hw ⊤ ((SecOn.topEquiv L).symm a))) := by
  intro p
  have e := SecOn.coord_congr hL hN w hw ((SecOn.topEquiv L).symm a) p.1 p.2 (O := N.U p.1 ⊓ L.U p.2)
    (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl
  rw [SecOn.topEquiv_symm_apply, GlobalTheory.LB.coord_ofSec, rs_self, rs_rs] at e
  rw [SecOn.topEquiv_f]
  exact (rs_rs _ _ _).trans e

theorem topEquiv_sum {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Sp R) (M : LB X) {n : ℕ}
    (c : Fin n → R) (x : Fin n → SecOnR f M ⊤) :
    SecOnR.topEquiv f M (∑ j, c j • x j) = ∑ j, cst f ⊤ (c j) • SecOnR.topEquiv f M (x j) := by
  simp only [map_sum, SecOnR.smul_def, map_smul]

theorem sum_f {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin m → H.Sec) (k : H.ι) :
    (∑ j, s j).f k = ∑ j, (s j).f k :=
  map_sum ({ toFun := fun s : H.Sec => s.f k, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    H.Sec →+ Γ(X, H.U k)) s Finset.univ

theorem veryAmpleBy_of_span {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) [UniversallyClosed f]
    (H : LB X) {m n : ℕ} (s₁ : Fin (m + 1) → H.Sec) (s : Fin (n + 1) → H.Sec) (hs₁ : VeryAmpleBy f H s₁)
    (hsp : ∀ i, ∃ c : Fin (n + 1) → R, s₁ i = ∑ k, cst f ⊤ (c k) • s k) : VeryAmpleBy f H s := by
  have E : ∀ {p : ℕ} (u : Fin (p + 1) → H.Sec), VeryAmpleBy f H u ↔ AmpleSpan.EmbedsBy f u :=
    fun u => (AmpleSpan.embedsBy_spec_iff f u).symm
  refine (E s).2 (((E s₁).1 hs₁).of_inSpan fun i => ?_)
  obtain ⟨c, hc⟩ := hsp i
  refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c k), fun k' => ?_⟩
  rw [hc, sum_f]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GlobalTheory.LB.smul_f]
  congr 1
  change rs X le_top (cst f ⊤ (c k)) = _
  rw [rs_cst]
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp, Scheme.Hom.appTop]
  rfl

end GlobalTheory.BasisMatch

namespace GlobalTheory.BasisMatch
open GlobalTheory.AbLaw GlobalTheory.Cartier TensorProduct

def basisOfExistsUnique {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ} (v : Fin n → V)
    (h : ∀ x, ∃! c : Fin n → R, x = ∑ j, c j • v j) : Module.Basis (Fin n) R V :=
  Module.Basis.mk (v := v)
    (Fintype.linearIndependent_iff.2 fun g hg i => by
      obtain ⟨c, -, hc⟩ := h 0
      exact congrFun ((hc g hg.symm).trans (hc 0 (by simp)).symm) i)
    (fun x _ => (Submodule.mem_span_range_iff_exists_fun R).2 (by
      obtain ⟨c, hc, -⟩ := h x
      exact ⟨c, hc.symm⟩))

theorem basisOfExistsUnique_apply {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
    (v : Fin n → V) (h : ∀ x, ∃! c : Fin n → R, x = ∑ j, c j • v j) (j : Fin n) :
    basisOfExistsUnique v h j = v j := Module.Basis.mk_apply _ _ _

theorem core {K W K' : Type} [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K']
    [Module.Flat W K'] {XA XG Y : Scheme.{0}} (fA : XA ⟶ Sp K) (fG : XG ⟶ Sp W) (fY : Y ⟶ Sp K')
    (πA : Y ⟶ XA) (πG : Y ⟶ XG) [CompactSpace XA] [CompactSpace XG] [IsSeparated fA] [IsSeparated fG]
    [UniversallyClosed fA]
    (PA : IsPullback πA fY fA (spMap (algebraMap K K'))) (PG : IsPullback πG fY fG (spMap (algebraMap W K')))
    (H : LB XA) (M : LB XG) (w : LB.Iso (M.pull πG) (H.pull πA)) {m : ℕ} (s₁ : Fin (m + 1) → H.Sec)
    {N : ℕ} (t : Fin (N + 1) → M.Sec) (hH : H.IsLB) (hs₁ : VeryAmpleBy fA H s₁) (hM : M.IsLB)
    (hw : w.IsGen) (ht : ∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, cst fG ⊤ (c j) • t j) :
    ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'),
      VeryAmpleBy fA H s ∧ IsUnit g.det ∧
      (∀ j, SecMaps w (secPull (t j) πG) (∑ k, cst fY ⊤ (g j k) • secPull (s k) πA)) ∧
      ∀ c c' : Fin (N + 1) → K', ∑ k, cst fY ⊤ (c k) • secPull (s k) πA =
        ∑ k, cst fY ⊤ (c' k) • secPull (s k) πA → c = c' := by
  have hLy : (M.pull πG).IsLB := LB.isLB_pull hM _
  have hHy : (H.pull πA).IsLB := LB.isLB_pull hH _
  let bcA := LinearEquiv.ofBijective _ (GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective hH PA)
  let bcG := LinearEquiv.ofBijective _ (GlobalTheory.PlaceInt.Ext.baseChangeHom_top_bijective hM PG)
  let ψ := SecOnR.linEquiv fY (R := K') (SecOn.congr hLy hHy w hw ⊤)
  have htt : ∀ x : SecOnR fG M ⊤, ∃! c : Fin (N + 1) → W,
      x = ∑ j, c j • (SecOnR.topEquiv fG M).symm (t j) := by
    intro x
    refine (existsUnique_congr fun c => ?_).1 (ht (SecOnR.topEquiv fG M x))
    refine Iff.trans ?_ (SecOnR.topEquiv fG M).injective.eq_iff
    rw [topEquiv_sum]
    simp only [LinearEquiv.apply_symm_apply]
  let bt := basisOfExistsUnique _ htt
  let tY := ((bt.baseChange K').map bcG).map ψ
  have hfr : Module.finrank K (SecOnR fA H ⊤) = N + 1 := by
    rw [← Module.finrank_baseChange (R := K') (S := K), Module.finrank_eq_card_basis (tY.map bcA.symm),
      Fintype.card_fin]
  haveI : Module.Finite K (SecOnR fA H ⊤) := Module.finite_of_finrank_eq_succ hfr
  let bs := Module.finBasisOfFinrankEq K _ hfr
  let s : Fin (N + 1) → H.Sec := fun k => SecOnR.topEquiv fA H (bs k)
  let bV := (bs.baseChange K').map bcA
  have hbV : ∀ k, SecOnR.topEquiv fY (H.pull πA) (bV k) = secPull (s k) πA := fun k => by
    simp only [bV, bcA, Module.Basis.map_apply, Module.Basis.baseChange_apply, LinearEquiv.ofBijective_apply]
    exact (congrArg (SecOnR.topEquiv fY (H.pull πA)) (one_smul K' (SecOnR.pull H PA.w ⊤ ⊤ le_top (bs k)))).trans
      (topEquiv_pull PA.w H _)
  have htY : ∀ j, SecOnR.topEquiv fY (H.pull πA) (tY j) =
      SecOn.topEquiv (H.pull πA) (SecOn.congr hLy hHy w hw ⊤ ((SecOn.topEquiv (M.pull πG)).symm
        (secPull (t j) πG))) := fun j => by
    have e1 : SecOnR.topEquiv fY (M.pull πG) (bcG (1 ⊗ₜ bt j)) = secPull (t j) πG := by
      simp only [bcG, LinearEquiv.ofBijective_apply]
      refine (congrArg (SecOnR.topEquiv fY (M.pull πG))
        (one_smul K' (SecOnR.pull M PG.w ⊤ ⊤ le_top (bt j)))).trans ?_
      rw [topEquiv_pull]
      show secPull (SecOnR.topEquiv fG M (basisOfExistsUnique _ htt j)) πG = _
      rw [basisOfExistsUnique_apply, LinearEquiv.apply_symm_apply]
    rw [← e1]
    simp only [tY, Module.Basis.map_apply, Module.Basis.baseChange_apply]
    show SecOn.topEquiv _ (SecOn.congr hLy hHy w hw ⊤ (bcG (1 ⊗ₜ bt j))) =
      SecOn.topEquiv _ (SecOn.congr hLy hHy w hw ⊤ ((SecOn.topEquiv _).symm (SecOn.topEquiv _ (bcG (1 ⊗ₜ bt j)))))
    exact congrArg (fun z => SecOn.topEquiv (H.pull πA) (SecOn.congr hLy hHy w hw ⊤ z))
      ((SecOn.topEquiv (M.pull πG)).symm_apply_apply _).symm
  let g : Matrix (Fin (N + 1)) (Fin (N + 1)) K' := fun j k => bV.repr (tY j) k
  have hsum : ∀ c : Fin (N + 1) → K', ∑ k, cst fY ⊤ (c k) • secPull (s k) πA =
      SecOnR.topEquiv fY (H.pull πA) (∑ k, c k • bV k) := fun c => by
    rw [topEquiv_sum]
    simp only [hbV]
  refine ⟨s, g, ?_, ?_, fun j => ?_, fun c c' h => ?_⟩
  · refine veryAmpleBy_of_span fA H s₁ s hs₁ fun i => ⟨bs.repr ((SecOnR.topEquiv fA H).symm (s₁ i)), ?_⟩
    conv_lhs => rw [← (SecOnR.topEquiv fA H).apply_symm_apply (s₁ i),
      ← bs.sum_repr ((SecOnR.topEquiv fA H).symm (s₁ i))]
    rw [topEquiv_sum]
  · have : g = Matrix.transpose (bV.toMatrix tY) := by
      ext j k
      rfl
    rw [this, Matrix.det_transpose]
    letI := bV.invertibleToMatrix tY
    exact Matrix.isUnit_det_of_invertible _
  · rw [hsum, bV.sum_repr (tY j), htY]
    exact secMaps_congr hLy hHy w hw _
  · rw [hsum, hsum] at h
    have h3 : bV.equivFun.symm c = bV.equivFun.symm c' := by
      simpa only [Module.Basis.equivFun_symm_apply] using (SecOnR.topEquiv fY (H.pull πA)).injective h
    exact bV.equivFun.symm.injective h3

end GlobalTheory.BasisMatch

open GlobalTheory.AbLaw GlobalTheory.Cartier in

theorem GlobalTheory.BasisMatch.exists_basis_match : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s₁ : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (N : ℕ) (t : Fin (N + 1) → M.Sec), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s₁ → M.IsLB → w.IsGen → (∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j) → ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ c c' : Fin (N + 1) → K', ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c' k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) → c = c' := by
  intro K W K' _ _ _ _ _ _ _ _ A _ hA G _ hG e H m s₁ M w N t hH hs₁ hM hw ht
  haveI := hA.proper
  haveI := hG.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : Module.Flat W K' := IsLocalization.flat K' (nonZeroDivisors W)
  have PG : IsPullback (pullback.fst G.hom (spMap (algebraMap W K'))) (pullback.snd G.hom (spMap (algebraMap W K')))
      G.hom (spMap (algebraMap W K')) := IsPullback.of_hasPullback _ _
  have PA : IsPullback (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd G.hom (spMap (algebraMap W K'))) A.hom (spMap (algebraMap K K')) := by
    refine (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))).of_iso
      ((Over.forget _).mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, Iso.refl_hom,
        Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left]
      exact (Category.id_comp _).symm
    · have := Over.w e.inv
      simp only [Functor.mapIso_symm, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, Iso.refl_hom,
        Category.comp_id]
      exact this.symm
    · simp
    · simp
  exact GlobalTheory.BasisMatch.core A.hom G.hom _ _ _ PA PG H M w s₁ t hH hs₁ hM hw ht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointsRestrictBijectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (n : ℕ), 0 < n → IsUnit (n : Γ(S, ⊤)) →
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (t : Sp R ⟶ S)
    (K : Type) [Field K] (φ : R →+* K),
    (∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g =
        (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ h → g = h) ∧
    ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 → ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g = x := by
  first | exact @GlobalTheory.TorsLift.torsion_points_restrict_bijective | exact GlobalTheory.TorsLift.torsion_points_restrict_bijective | (intros; apply GlobalTheory.TorsLift.torsion_points_restrict_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramified
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnramifiedClosure

theorem injective_of_map_maximalIdeal {R W : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra R W]
    (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Function.Injective (algebraMap R W) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hp : (RingHom.ker (algebraMap R W)).IsPrime := RingHom.ker_isPrime _
  have hm : RingHom.ker (algebraMap R W) = maximalIdeal R := IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)
  apply IsDiscreteValuationRing.not_a_field W
  rw [← h, ← hm]
  exact (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl

variable (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K']
  [IsScalarTower R W K'] [IsScalarTower R K K']

theorem isLocalization (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    IsLocalization (Algebra.algebraMapSubmonoid W (nonZeroDivisors R)) K' := by
  have hinj := injective_of_map_maximalIdeal h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖW : Irreducible (algebraMap R W ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← h,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact fun h0 => nonZeroDivisors.ne_zero hr (hinj (by rw [map_zero]; exact h0))
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖW
    refine ⟨⟨x * ↑u⁻¹, ⟨algebraMap R W (ϖ ^ n), ϖ ^ n,
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero), rfl⟩⟩, ?_⟩
    have hu : algebraMap W K' ↑u * algebraMap W K' ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hp : algebraMap W K' (algebraMap R W ϖ) ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hϖW.ne_zero
    have hu0 : algebraMap W K' ↑u ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact u.ne_zero
    simp only [map_pow, map_mul]
    field_simp
    linear_combination (-(algebraMap W K' x)) * hu
  · intro x y hxy
    exact ⟨1, by simpa using IsFractionRing.injective W K' hxy⟩

theorem isPushout (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Algebra.IsPushout R K W K' := by
  haveI := isLocalization R W K' h
  constructor
  exact (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K _).1
    (isLocalizedModule_iff_isLocalization.2 this)

theorem isPullback_spec (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    IsPullback (spMap (algebraMap K K')) (spMap (algebraMap W K')) (spMap (algebraMap R K))
      (spMap (algebraMap R W)) := by
  haveI := isPushout R K W K' h
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R K W K')

theorem flat_spec (h : (maximalIdeal R).map (algebraMap R W) = maximalIdeal W) :
    Flat (spMap (algebraMap R W)) := by
  have hinj := injective_of_map_maximalIdeal h
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  refine GlobalTheory.ringHom_flat_of_injective_of_isUnit (algebraMap R W) (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W)) fun t ht => IsUnit.mk0 _ ?_
  rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact fun h0 => ht (hinj (by rw [h0, map_zero]))

end GlobalTheory.UnramifiedClosure

namespace GlobalTheory.UnramifiedClosure

theorem schDom_spMap {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (spMap φ) := by
  haveI : IsDominant (spMap φ) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

end GlobalTheory.UnramifiedClosure

open GlobalTheory.UnramifiedClosure in
theorem GlobalTheory.UnramifiedClosure.closure_baseChange : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (P : Over (Sp R)), QuasiSeparated P.hom → ∀ (A : Over (Sp K)), QuasiCompact A.hom → ∀ (G : Over (Sp W)), QuasiCompact G.hom → Flat G.hom → ∀ (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)), IsClosedImmersion (pullback.lift iA A.hom hA) → ∀ (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)), IsClosedImmersion (pullback.lift iG G.hom hG) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG → ∃ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) ∧ IsPullback g G.hom X.hom (spMap (algebraMap R W)) ∧ e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm P hP A hAq G hGq hGf e iA hA hcA iG hG hcG hcomp

  have hjp : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hjf : Flat (spMap (algebraMap R K)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hjW : Flat (spMap (algebraMap R W)) := flat_spec R W hm
  have hsq := isPullback_spec R K W K' hm
  have hqc : QuasiCompact iA := by
    have : QuasiCompact (iA ≫ P.hom) := by rw [hA]; infer_instance
    exact QuasiCompact.of_comp iA P.hom
  have hdom : IsSchemeTheoreticallyDominant iA.toImage := GlobalTheory.isSchemeTheoreticallyDominant_toImage iA
  let X : Over (Sp R) := Over.mk (iA.imageι ≫ P.hom)
  have hXh : X.hom = iA.imageι ≫ P.hom := rfl
  have hXa : iA.toImage ≫ X.hom = A.hom ≫ spMap (algebraMap R K) := by
    rw [hXh, Scheme.Hom.toImage_imageι_assoc, hA]
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{0} :=
    ⟨fun f g hf hg ↦ @IsClosedImmersion.comp _ _ _ f g hf hg⟩

  let t : A.left ⟶ pullback X.hom (spMap (algebraMap R K)) := pullback.lift iA.toImage A.hom hXa
  let mK : pullback X.hom (spMap (algebraMap R K)) ⟶ pullback P.hom (spMap (algebraMap R K)) :=
    pullback.map _ _ _ _ iA.imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hmK : IsClosedImmersion mK :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  have htm : t ≫ mK = pullback.lift iA A.hom hA := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst,
        Scheme.Hom.toImage_imageι]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.comp_id]
  have : IsClosedImmersion (t ≫ mK) := htm ▸ hcA
  have ht : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t mK
  have hpb : IsPullback (𝟙 A.left) t iA.toImage (pullback.fst X.hom (spMap (algebraMap R K))) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have htd : IsSchemeTheoreticallyDominant t := .of_isPullback hpb
  have : IsIso t := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t.ker_eq_bot
  have hIa : IsPullback iA.toImage A.hom X.hom (spMap (algebraMap R K)) :=
    IsPullback.of_iso_pullback ⟨hXa⟩ (asIso t) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  have hAK : IsPullback (pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd A.hom (spMap (algebraMap K K')) ≫ spMap (algebraMap W K'))
      (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) :=
    (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))).paste_vert hsq
  let mW : pullback X.hom (spMap (algebraMap R W)) ⟶ pullback P.hom (spMap (algebraMap R W)) :=
    pullback.map _ _ _ _ iA.imageι (𝟙 _) (𝟙 _) (Category.comp_id _) (by simp)
  have hmW : IsClosedImmersion mW :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0}) inferInstance inferInstance rfl (by simp)
  let n : pullback (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) ⟶
      pullback X.hom (spMap (algebraMap R W)) :=
    pullback.map _ _ _ _ iA.toImage (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hXa]) (by simp)
  have hL : IsPullback (pullback.fst (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W))) n
      iA.toImage (pullback.fst X.hom (spMap (algebraMap R W))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback X.hom (spMap (algebraMap R W)))
    have h1 : n ≫ pullback.snd X.hom (spMap (algebraMap R W)) =
        pullback.snd (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W)) := by
      rw [pullback.lift_snd, Category.comp_id]
    rw [h1, hXa]
    exact IsPullback.of_hasPullback _ _
  have hn : IsSchemeTheoreticallyDominant n := .of_isPullback hL
  have hsd : IsSchemeTheoreticallyDominant (spMap (algebraMap W K')) :=
    schDom_spMap _ (IsFractionRing.injective W K')
  have hu : IsSchemeTheoreticallyDominant (pullback.fst G.hom (spMap (algebraMap W K'))) :=
    inferInstance
  have he : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let v : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback X.hom (spMap (algebraMap R W)) :=
    e.hom.left ≫ hAK.isoPullback.hom ≫ n
  have hv : IsSchemeTheoreticallyDominant v := inferInstance
  let cG : G.left ⟶ pullback P.hom (spMap (algebraMap R W)) := pullback.lift iG G.hom hG
  have hes : e.hom.left ≫ pullback.snd A.hom (spMap (algebraMap K K')) =
      pullback.snd G.hom (spMap (algebraMap W K')) := Over.w e.hom
  have hcomm : pullback.fst G.hom (spMap (algebraMap W K')) ≫ cG = v ≫ mW := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← hcomp]
      simp only [v, mW, n, Category.assoc]
      rw [pullback.lift_fst]
      try simp only [Category.assoc]
      rw [pullback.lift_fst_assoc]
      try simp only [Category.assoc]
      rw [IsPullback.isoPullback_hom_fst_assoc, Scheme.Hom.toImage_imageι]
    · rw [Category.assoc, pullback.lift_snd]
      simp only [v, mW, n, Category.assoc]
      rw [pullback.lift_snd, Category.comp_id (pullback.snd X.hom (spMap (algebraMap R W))),
        pullback.lift_snd,
        Category.comp_id (pullback.snd (A.hom ≫ spMap (algebraMap R K)) (spMap (algebraMap R W))),
        IsPullback.isoPullback_hom_snd, reassoc_of% hes]
      exact pullback.condition
  have hker : mW.ker = cG.ker := by
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K')) ≫ cG).ker = cG.ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    have h2 : (v ≫ mW).ker = mW.ker := by
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← h1, ← h2, hcomm]
  let ψ : G.left ⟶ pullback X.hom (spMap (algebraMap R W)) := IsClosedImmersion.lift mW cG hker.le
  have hψ : ψ ≫ mW = cG := IsClosedImmersion.lift_fac _ _ _
  have : IsIso ψ := IsClosedImmersion.isIso_lift mW cG hker
  have hψs : ψ ≫ pullback.snd X.hom (spMap (algebraMap R W)) = G.hom := by
    have h := congrArg (· ≫ pullback.snd P.hom (spMap (algebraMap R W))) hψ
    simp only [Category.assoc] at h
    rwa [pullback.lift_snd, Category.comp_id, pullback.lift_snd] at h
  have hIg : IsPullback (ψ ≫ pullback.fst X.hom (spMap (algebraMap R W))) G.hom X.hom
      (spMap (algebraMap R W)) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, reassoc_of% hψs]⟩
      (asIso ψ) rfl hψs
  refine ⟨X, iA.toImage, ψ ≫ pullback.fst X.hom (spMap (algebraMap R W)), hIa, hIg, ?_⟩
  rw [← cancel_mono iA.imageι]
  have h3 : pullback.fst X.hom (spMap (algebraMap R W)) ≫ iA.imageι =
      mW ≫ pullback.fst P.hom (spMap (algebraMap R W)) := (pullback.lift_fst _ _ _).symm
  simp only [Category.assoc]
  rw [Scheme.Hom.toImage_imageι, h3, reassoc_of% hψ, pullback.lift_fst, hcomp]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRationalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCoordinates_rationalMatrices_onto_rational : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), (∀ x : Matrix (Fin m) (Fin n) D.host.E, ∃ y z : Fin N → D.host.F, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) → ∀ y z : Fin N → D.host.F, ∃ x : Matrix (Fin m) (Fin n) D.host.E, e (incM D.host.F x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  first | exact @GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps | exact GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps | (intros; apply GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepPartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), Continuous e ∧ Continuous e.symm ∧ (∀ x, x.map (finPart D) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧ (∀ x, x.map (infPart D) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  first | exact @GlobalTheory.AdelicCoord.coord | exact GlobalTheory.AdelicCoord.coord | (intros; apply GlobalTheory.AdelicCoord.coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValuesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_determined_by_schrodingerThetaValues : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w : (κ → AF D.host.F) × (κ → AF D.host.F), GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ) =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ')) → φ = φ' := by
  first | exact @GlobalTheory.SchrodingerUniq.main | exact GlobalTheory.SchrodingerUniq.main | (intros; apply GlobalTheory.SchrodingerUniq.main <;> assumption)
end

