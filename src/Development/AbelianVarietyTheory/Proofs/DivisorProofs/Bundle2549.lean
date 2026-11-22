import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0369
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRationalInjectivity
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelTwistBySimilitude
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem reduceMod_eq_zero_iff {h : ℕ} (M : ℕ) (u : Fin h ⊕ Fin h → ℤ) :
    reduceMod M u = 0 ↔ ∃ c, u = M • c := by
  constructor
  · intro hu
    refine ⟨fun i => u i / M, ?_⟩
    funext i
    have hi : ((u i : ℤ) : ZMod M) = 0 := congrFun hu i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' hi).symm
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (u v : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd u v : ℤ) : ZMod M) = omegaMod M (reduceMod M u) (reduceMod M v) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem sympCond_twist : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  intro p _ D R _ b N h M hM S t o T t₁ lv hlv a n σ hn hσ
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlv

  let φ : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (T ⟶ o.A) :=
    MonoidHom.mk' (fun u => lv (Multiplicative.toAdd u)) (fun u v => hadd _ _)
  have hsm : ∀ (k : ℕ) (w : Fin h ⊕ Fin h → ℤ), lv (k • w) = lv w ^ k := by
    intro k w
    have := map_pow φ (Multiplicative.ofAdd w) k
    simpa [φ, ← ofAdd_nsmul] using this
  have per : ∀ {u v : Fin h ⊕ Fin h → ℤ}, reduceMod M u = reduceMod M v → lv u = lv v := by
    intro u v huv
    have h0 : reduceMod M (u - v) = 0 := by
      funext i
      have := congrFun huv i
      simp only [reduceMod, Pi.sub_apply, Pi.zero_apply, Int.cast_sub] at this ⊢
      rw [this, sub_self]
    obtain ⟨w, hw⟩ := (reduceMod_eq_zero_iff M _).1 h0
    have : u = v + M • w := by rw [← hw]; abel
    rw [this, hadd, hsm, htor, _root_.mul_one]
  let g := (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
  have tw : ∀ u, sympTwist a lv u = lv (liftMod (g (reduceMod M u))) := fun u => rfl
  have redAdd : ∀ u v : Fin h ⊕ Fin h → ℤ, reduceMod M (u + v) = reduceMod M u + reduceMod M v := by
    intro u v; funext i; simp [reduceMod]
  refine ⟨fun u c => ?_, fun u => ?_, fun k _ _ x β' z' hx' hz' => ?_⟩
  · rw [tw, tw, tw, ← hadd]
    apply per
    rw [reduceMod_liftMod, redAdd, redAdd, reduceMod_liftMod, reduceMod_liftMod, map_add]
  · rw [tw]; exact htor _
  ·
    set β : cycAway M →+* k := (Spec.preimage (x ≫ t₁)).hom with hβdef
    have hβ : x ≫ t₁ = spMap β := by
      simp only [spMap, hβdef, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hβ' : β' = β.comp σ := by
      have e : spMap β' = spMap (β.comp σ) := by
        rw [spMap_comp, ← hx', ← hβ, Category.assoc]
      have := Spec.map_injective e
      exact congrArg CommRingCat.Hom.hom this
    have hζM : β (zetaAway M) ^ M = 1 := by
      rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
    have hne : β (zetaAway M) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM.ne'] at hζM
      exact zero_ne_one hζM
    set z : kˣ := Units.mk0 (β (zetaAway M)) hne with hzdef
    have hz : (z : k) = β (zetaAway M) := rfl
    have hzz : z' = z ^ n := by
      ext
      rw [hz', hβ', RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val, hz]
    have hzM : z ^ (M : ℤ) = 1 := by
      rw [zpow_natCast]; ext; rw [Units.val_pow_eq_pow_val, hz, hζM]; rfl
    obtain ⟨hK, hS, hW⟩ := hgeo k x β z hβ hz
    refine ⟨fun u => ?_, fun g' hg' => ?_, fun u c => ?_⟩
    · rw [tw, hK]
      constructor
      · rintro ⟨c, hc⟩
        apply (reduceMod_eq_zero_iff M u).1
        have : g (reduceMod M u) = 0 := by
          rw [← reduceMod_liftMod (g (reduceMod M u)), hc]
          exact (reduceMod_eq_zero_iff M _).2 ⟨c, rfl⟩
        exact (LinearEquiv.map_eq_zero_iff _).1 this
      · intro hu
        apply (reduceMod_eq_zero_iff M _).1
        rw [reduceMod_liftMod, (reduceMod_eq_zero_iff M u).2 hu, map_zero]
    · obtain ⟨u₀, hu₀⟩ := hS g' hg'
      refine ⟨liftMod (g.symm (reduceMod M u₀)), ?_⟩
      rw [tw, reduceMod_liftMod, LinearEquiv.apply_symm_apply, per (reduceMod_liftMod _)]
      exact hu₀
    · rw [tw, tw]
      set u' := liftMod (g (reduceMod M u))
      set c' := liftMod (g (reduceMod M c))
      have hcast : ((2 * omegaStd u' c' : ℤ) : ZMod M) = (((n : ℤ) * (2 * omegaStd u c) : ℤ) : ZMod M) := by
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod]
        rw [show omegaMod M (g (reduceMod M u)) (g (reduceMod M c)) = n * omegaMod M (reduceMod M u) (reduceMod M c)
          from hn _ _]
        ring
      have e : z' ^ (2 * omegaStd u c) = z ^ (2 * omegaStd u' c') := by
        rw [hzz, ← zpow_natCast z, ← zpow_mul, zpow_eq_zpow_emod _ hzM, zpow_eq_zpow_emod (2 * omegaStd u' c') hzM]
        congr 1
        exact ((ZMod.intCast_eq_intCast_iff' _ _ _).1 hcast).symm
      rw [e]
      exact hW u' c'

end GlobalTheory.HTSympCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMapCompatibleStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_map_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (σ : E →+* ℂ) (U h : Fin (Dw.mult σ) → Fin g → A), IsUnit (pairDet h U) →
    ∀ (L : Type) [CommRing L] [Algebra c.F L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ z₀ : FrPt Xo c L, z₀.x = yL ≫ r ≫ pullback.fst _ _ →
    ∀ w : Fin (Dw.mult σ) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left),
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U i b)) (w i ≫ Y.m.φ)) →
      (∀ i, IsTanAtG Y.oF.t yL (w i)) → (∀ i, IsEigAt c σ (w i ≫ ν.φ)) →
      ∃ g₁ : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L, IsUnit g₁.det ∧
        ∀ i, IsCombAt z₀.x (z₀.u σ) (g₁ i) (w i ≫ ν.φ) := by
  first | exact @GlobalTheory.FrameCoordUnit.coord_unit | exact GlobalTheory.FrameCoordUnit.coord_unit | (intros; apply GlobalTheory.FrameCoordUnit.coord_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameLocalizationIndependentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_localization_independent : ∀ {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G],
    Smooth G.hom → ∀ (a : OAct O G) (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → GlobalTheory.Serre.Lie a),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i).hom (v i)) → IsLieBasis v) →
    ∀ l : GlobalTheory.Serre.Lie a, ∃ s ∉ p, s • l ∈ Submodule.span R (Set.range w) := by
  first | exact @GlobalTheory.LieSpanLoc.exists_smul_mem_span | exact GlobalTheory.LieSpanLoc.exists_smul_mem_span | (intros; apply GlobalTheory.LieSpanLoc.exists_smul_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameLocalizationSpansStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_localization_spans : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G], Smooth G.hom →
    ∀ (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → (epsR R ⟶ G)),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) →
    ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T), (IsLocalRing.maximalIdeal T).comap g = p →
    ∀ (G' : Over (Sp T)) [GrpObj G'] (ψ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) ψ →
    ∀ v : Fin n → (epsR T ⟶ G'), (∀ i, GlobalTheory.IsVecOver g ψ (w i) (v i)) → IsLieBasis v := by
  first | exact @GlobalTheory.isLieBasis_of_local_restrict | exact GlobalTheory.isLieBasis_of_local_restrict | (intros; apply GlobalTheory.isLieBasis_of_local_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsLocalizationLiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vectors_localization_lift : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → ∀ (p : Ideal R) [p.IsPrime],
    ∃ (n : ℕ) (w : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (w i)) ∧
      (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) := by
  first | exact @GlobalTheory.exists_tangent_isLieBasis_atPrime | exact GlobalTheory.exists_tangent_isLieBasis_atPrime | (intros; apply GlobalTheory.exists_tangent_isLieBasis_atPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem tateSt : TateSt := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hA yb yy P π ψ hP β σ J _ N a T S hL
  obtain ⟨ev, ζ, hζp, hζpow, hadd, hlin, honto, htow, hweil, hlev⟩ :=
    GlobalTheory.T.p_adic_point_level_power E H Dw l' Xo' c' W Y p n hA yb yy P π ψ hP
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hev1 : ∀ b, ev 1 b = 1 := fun b => by
    have := (honto 1 one_pos (ev 1 b)).2 ⟨b, rfl⟩
    simpa using this
  obtain ⟨f, hflev, hflin⟩ := GlobalTheory.T.exists_tate_module_of_evaluations E H Dw p P ev hadd hlin htow hev1
  have hspan := GlobalTheory.T.tate_lattice_spans E H Dw p P f (fun x hx => by
    obtain ⟨b, hb⟩ := (honto p hp x).1 hx
    exact ⟨b, by rw [hflev, pow_one, hb]⟩)
  obtain ⟨u, hu, hpair⟩ := GlobalTheory.T.weil_pairing_unit_scalar E H Dw p P f ζ hζp hζpow (fun k b b' => by
    rw [hflev, hflev]; exact hweil _ (pow_pos hp k) b b')
  have hmem : ∀ (c : 𝓞_ℂ_[p]) (t : P.T), ((c : ℂ_[p]) ⊗ₜ[ℤ_[p]] t : P.V) ∈ P.latT := fun c t =>
    ⟨c ⊗ₜ t, by rw [Point.inclT_tmul]; rfl⟩
  have hsum : ∀ (X : Fin N → 𝓞_ℂ_[p]), (∑ m, ((X m : ℂ_[p]) ⊗ₜ[ℤ_[p]] f (a m)) : P.V) ∈ P.latT := fun X =>
    Submodule.sum_mem _ fun m _ => hmem _ _
  let Φ : (c'.V W) ⊗[ℤ] Dw.La →ₗ[ℤ] P.V := TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun (v : c'.V W) (b : Dw.La) => ((β v : ℂ_[p]) ⊗ₜ[ℤ_[p]] f b : P.V))
    (fun v v' b => by simp [TensorProduct.add_tmul])
    (fun z v b => by simp [TensorProduct.smul_tmul'])
    (fun v b b' => by simp [TensorProduct.tmul_add])
    (fun z v b => by simp [TensorProduct.tmul_smul]))
  have hΦ : ∀ v b, Φ (v ⊗ₜ b) = (β v : ℂ_[p]) ⊗ₜ[ℤ_[p]] f b := fun v b => rfl
  refine ⟨fun m => f (a m), algebraMap ℤ_[p] ℂ_[p] u, fun m => by rw [hflev]; exact hlev _, ?_⟩
  refine ⟨fun i => ⟨hsum _, ?_⟩, fun i => hsum _, ?_, fun i j => ?_, ?_⟩
  · refine EigenSplit.mem_eigenSub.2 fun o => ?_
    have e1 := congrArg Φ (hL.1 i o)
    simp only [map_sum, hΦ] at e1
    have e2 : ∀ (c : ℂ_[p]) (t : P.T), P.actV o (c ⊗ₜ[ℤ_[p]] t) = c ⊗ₜ[ℤ_[p]] P.actT o t := fun c t => rfl
    simp only [map_sum, e2, ← hflin]
    rw [e1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TensorProduct.smul_tmul', map_mul]
    rfl
  · change ‖algebraMap ℚ_[p] ℂ_[p] (u : ℚ_[p])‖ = 1
    rw [norm_algebraMap']
    exact PadicInt.isUnit_iff.1 hu
  · have hc : ∀ x : 𝓞_ℂ_[p], algebraMap 𝓞_ℂ_[p] ℂ_[p] x = (x : ℂ_[p]) := fun x => rfl
    have e := congrArg (fun x : c'.V W => algebraMap 𝓞_ℂ_[p] ℂ_[p] (β x)) (hL.2.1 i j)
    simp only [map_sum, map_mul, map_intCast] at e
    simp only [hc] at e
    simp only [map_sum, LinearMap.sum_apply, Point.pairV_tmul, hpair]
    simp only [Algebra.smul_def, map_mul, map_intCast]
    have e4 : ∀ m m', algebraMap ℤ_[p] ℂ_[p] u * ((Dw.EF (a m) (a m') : ℤ) : ℂ_[p]) * (((β (S i m) : 𝓞_ℂ_[p]) : ℂ_[p]) * ((β (T j m') : 𝓞_ℂ_[p]) : ℂ_[p])) =
        algebraMap ℤ_[p] ℂ_[p] u * (((β (S i m) : 𝓞_ℂ_[p]) : ℂ_[p]) * ((β (T j m') : 𝓞_ℂ_[p]) : ℂ_[p]) * ((Dw.EF (a m) (a m') : ℤ) : ℂ_[p])) :=
      fun m m' => by ring
    rw [Finset.sum_comm]
    simp only [e4, ← Finset.mul_sum, e]
    by_cases h : i = j <;> simp [h]
  · exact GlobalTheory.T.lattice_data_tate_span E H Dw p P (c'.V W) β (embV c' W σ) J N a T S f hL hflin hspan

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorEqZeroOfForallDualPairing
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_dual_pairing {R : Type} [CommRing R] {M N : Type 1}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R M] [Module.Projective R N] (u : M ⊗[R] N)
    (h : ∀ (x : Module.Dual R M) (y : Module.Dual R N),
      TensorProduct.lift ((LinearMap.mul R R).compl₁₂ x y) u = 0) : u = 0 := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := R) (P := M)
  obtain ⟨s', hs'⟩ := Module.Projective.out (R := R) (P := N)
  have key : ∀ (w : M ⊗[R] N) (c : M) (c' : N),
      finsuppTensorFinsupp' R M N (TensorProduct.map s s' w) (c, c') =
        TensorProduct.lift ((LinearMap.mul R R).compl₁₂ ((Finsupp.lapply c).comp s)
          ((Finsupp.lapply c').comp s')) w := by
    intro w c c'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply]
    | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw]
  have h0 : TensorProduct.map s s' u = 0 := by
    apply (finsuppTensorFinsupp' R M N).injective
    rw [map_zero]
    ext ⟨c, c'⟩
    rw [key]
    exact h _ _
  have hl : (Finsupp.linearCombination R id).comp s = LinearMap.id := LinearMap.ext hs
  have hl' : (Finsupp.linearCombination R id).comp s' = LinearMap.id := LinearMap.ext hs'
  have : u = TensorProduct.map (Finsupp.linearCombination R id) (Finsupp.linearCombination R id)
      (TensorProduct.map s s' u) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hl, hl', TensorProduct.map_id,
      LinearMap.id_apply]
  rw [this, h0, map_zero]

theorem tensor_mem_of_dualAnnihilator : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Projective R M] [Module.Projective R N] (F : Submodule R M) (F' : Submodule R N), (∃ C, IsCompl F C) → (∃ C, IsCompl F' C) → (∀ c : M, (∀ h ∈ F.dualAnnihilator, h c = 0) → c ∈ F) ∧ ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N), (∀ x ∈ F.dualAnnihilator, ∀ y ∈ F'.dualAnnihilator, ∑ k, x (a k) * y (b k) = 0) → ∃ (a₁ : Fin n → M) (b₁ : Fin n → N), (∀ k, a₁ k ∈ F) ∧ (∀ k, b₁ k ∈ F') ∧ ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0 := by
  intro R _ M N _ _ _ _ _ _ F F' ⟨C, hC⟩ ⟨C', hC'⟩
  set e : M →ₗ[R] M := C.subtype.comp (C.linearProjOfIsCompl F hC.symm) with he
  set e' : N →ₗ[R] N := C'.subtype.comp (C'.linearProjOfIsCompl F' hC'.symm) with he'
  have eF : ∀ f ∈ F, e f = 0 := fun f hf => by
    rw [he, LinearMap.comp_apply, show C.linearProjOfIsCompl F hC.symm f = 0 from
      Submodule.linearProjOfIsCompl_apply_right hC.symm ⟨f, hf⟩, map_zero]
  have eF' : ∀ f ∈ F', e' f = 0 := fun f hf => by
    rw [he', LinearMap.comp_apply, show C'.linearProjOfIsCompl F' hC'.symm f = 0 from
      Submodule.linearProjOfIsCompl_apply_right hC'.symm ⟨f, hf⟩, map_zero]
  have sub : ∀ m, m - e m ∈ F := fun m => by
    rw [← Submodule.linearProjOfIsCompl_ker hC.symm, LinearMap.mem_ker, map_sub, he,
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.linearProjOfIsCompl_apply_left]
    exact sub_self _
  have sub' : ∀ m, m - e' m ∈ F' := fun m => by
    rw [← Submodule.linearProjOfIsCompl_ker hC'.symm, LinearMap.mem_ker, map_sub, he',
      LinearMap.comp_apply, Submodule.subtype_apply, Submodule.linearProjOfIsCompl_apply_left]
    exact sub_self _
  have ann : ∀ x : Module.Dual R M, x.comp e ∈ F.dualAnnihilator := fun x => by
    rw [Submodule.mem_dualAnnihilator]; intro f hf; simp [eF f hf]
  have ann' : ∀ y : Module.Dual R N, y.comp e' ∈ F'.dualAnnihilator := fun y => by
    rw [Submodule.mem_dualAnnihilator]; intro f hf; simp [eF' f hf]
  refine ⟨fun c hc => ?_, fun n a b hab => ?_⟩
  · have : e c = 0 := (Module.forall_dual_apply_eq_zero_iff R (e c)).mp fun x => hc _ (ann x)
    simpa [this] using sub c
  · refine ⟨fun k => a k - e (a k), fun k => b k - e' (b k), fun k => sub _, fun k => sub' _, ?_⟩
    simp only [sub_sub_cancel]
    apply tensor_eq_zero_of_forall_dual_pairing
    intro x y
    simp only [map_sum, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    exact hab _ (ann x) _ (ann' y)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_fraction_injective_of_tensor_injective : ∀ (R R₁ B K L : Type) [CommRing R] [CommRing R₁] [CommRing B] [Field K] [Field L] [Algebra R R₁] [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K] [IsFractionRing B K] (θ : K →+* L) (c : R₁ →+* L) (β : B ⊗[R] R₁ →+ L), Function.Injective β → (∀ b r, β (b ⊗ₜ[R] r) = θ (algebraMap B K b) * c r) → ∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0 := by
  first | exact @GlobalTheory.tensor_fraction_injective_of_injective | exact GlobalTheory.tensor_fraction_injective_of_injective | (intros; apply GlobalTheory.tensor_fraction_injective_of_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanish
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tensor_kaehler_eq_zero_of_derivations_vanish :
  ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C], Module.Projective C Ω[C⁄R] → ∀ z : B ⊗[R] Ω[C⁄R], (∀ θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C, (∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → LinearMap.liftBaseChange B θ z = 0) → z = 0 := by
  intro R B C _ _ _ _ _ hP z hz
  classical
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := C) (P := Ω[C⁄R])).1 hP
  let π : (Ω[C⁄R] →₀ C) →ₗ[C] Ω[C⁄R] := Finsupp.linearCombination C id
  have hcomp : (LinearMap.lTensor B (π.restrictScalars R)) ∘ₗ (LinearMap.lTensor B (s.restrictScalars R))
      = LinearMap.id := by
    rw [← LinearMap.lTensor_comp]
    have : (π.restrictScalars R) ∘ₗ (s.restrictScalars R) = LinearMap.id := by
      exact LinearMap.ext fun x => LinearMap.congr_fun hs x
    rw [this, LinearMap.lTensor_id]
  have key : LinearMap.lTensor B (s.restrictScalars R) z = 0 := by
    apply (TensorProduct.finsuppRight R R B C Ω[C⁄R]).injective
    rw [map_zero]
    ext i
    let θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C :=
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toLinearMap ∘ₗ
        ((Finsupp.lapply (R := C) (M := C) i).restrictScalars R ∘ₗ s.restrictScalars R)
    have hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x := by
      intro c x
      simp [θ, Algebra.TensorProduct.tmul_mul_tmul]
    have h1 := hz θ hθ
    have heq : ∀ w : B ⊗[R] Ω[C⁄R], (TensorProduct.finsuppRight R R B C Ω[C⁄R]
        (LinearMap.lTensor B (s.restrictScalars R) w)) i = LinearMap.liftBaseChange B θ w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [θ, TensorProduct.finsuppRight_apply_tmul_apply, LinearMap.liftBaseChange_tmul,
          TensorProduct.smul_tmul']
      | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
    rw [heq, h1]; rfl
  have := congrArg (fun f => f z) hcomp
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [← this, key, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRationalInjectivityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_rational_injectivity : ∀ (N : ℕ) (I A : Type) [CommRing A] (B : I → Type) [∀ i, CommRing (B i)] (φ : ∀ i, A →+* B i),
    Module.Flat ℤ A → (∀ i, Module.Flat ℤ (B i)) → IsUnit ((N : ℤ) : A) →
    (N ≠ 0 → ∀ h : A ⊗[ℤ] ℚ, (∀ i, LinearMap.rTensor ℚ (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ h : A ⊗[ℤ] ZMod p,
      (∀ i, LinearMap.rTensor (ZMod p) (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    ∀ (L : Type) [AddCommGroup L] (h : A ⊗[ℤ] L),
      (∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0 := by
  first | exact @GlobalTheory.jointInj_tensor_of_rat_and_zmod | exact GlobalTheory.jointInj_tensor_of_rat_and_zmod | (intros; apply GlobalTheory.jointInj_tensor_of_rat_and_zmod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslatesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_square_cechPicard_translates : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (Y : Over S) (x a : Y ⟶ A), GlobalTheory.CechPic.pull (x * a).left c + GlobalTheory.CechPic.pull (x * a⁻¹).left c = 2 • GlobalTheory.CechPic.pull (x).left c + GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull (a⁻¹).left c - 2 • GlobalTheory.CechPic.pull ((1 : Y ⟶ A)).left c := by
  first | exact @GlobalTheory.SquareSym.pull_mul_add_pull_mul_inv | exact GlobalTheory.SquareSym.pull_mul_add_pull_mul_inv | (intros; apply GlobalTheory.SquareSym.pull_mul_add_pull_mul_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  first | exact @GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | exact GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | (intros; apply GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing <;> assumption)
end

