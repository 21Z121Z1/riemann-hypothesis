import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFrameOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDvr.Scale

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.ZH.TestVal

theorem odd_level' {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    Odd (S.r * S.N) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow

theorem powFrame_one' {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) :
    powFrame A L x τ 1 = τ :=
  congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))

attribute [local instance] gtGroup in

theorem exists_scale : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (yK : S.R →+* FractionRing V) (A : PolAV (Sp (FractionRing V))) (φ : A.A.left ⟶ ρ.P.A.left), IsGrpPullback A.A ρ.P.A (spMap yK) φ → LBIso A.L (ρ.P.L.pull φ) → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), IsSemiAbelian G → (∀ a : o, yK (algebraMap o S.R a) ∈ (algebraMap V (FractionRing V)).range) → ∀ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A), QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x → x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → ∀ (ϖ : V), Irreducible ϖ → ∀ (v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ (AlgebraicClosure (FractionRing V)) v → ∃ s : WithTop ℚ, (∀ b : S.Gam, s ≤ v (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (yK ⟨S.th b, S.th_mem b⟩)) ∧ (yy b ≠ 0 → yK ⟨S.th b, S.th_mem b⟩ ≠ 0 → s < v (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (yK ⟨S.th b, S.th_mem b⟩)))) ∧ ∀ n : ℕ, 2 ≤ n → n ∣ S.r * S.N → ∀ a : S.Gam, yy a = 0 → ∃ a' : S.Gam, yy a' = 0 ∧ n • (a' - a) = 0 ∧ v (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (yK ⟨S.th a', S.th_mem a'⟩)) = s := by
  intro hL hL₂ o Ω _ _ _ _ S ρ V _ _ _ _ hc yK A φ cart lb G _ _ D U semi hy yy _hyy_onto hyy ϖ hϖ v hv
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have hm := odd_level' ρ
  have hA : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  choose Q hQ using QForm.exists_QVal hϖ D
  have hu : IsUnit ((S.r * S.N : ℕ) : V) := by
    obtain ⟨b, hb⟩ := S.unit.exists_right_inv
    obtain ⟨c, hc'⟩ := hy b
    refine IsUnit.of_mul_eq_one c (IsFractionRing.injective V (FractionRing V) ?_)
    have := congrArg (fun a => yK (algebraMap o S.R a)) hb
    simp only [map_mul, map_natCast, map_one] at this ⊢
    rw [hc']; simpa using this
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points yK cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames yK cart lb x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G
    semi U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G semi U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA D A G semi U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set F := AlgebraicClosure (FractionRing V) with hF
  set y₀ : S.R →+* F := (algebraMap (FractionRing V) F).comp yK with hy₀
  have tv : ∀ a z J, Good A.L z J → cst (R := V) F z sc *
      @id ((TF (R := V) F).left.presheaf.stalk z) (sA th (ptSecT A.A (x a)).left z J) =
      cst (R := V) F z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := V) F).left.presheaf.stalk z)
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one' (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU U.toUnifPre F (S.r * S.N) q (x a) ∧ yy a = QuotientAddGroup.mk q.y :=
    fun a => by
      obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
      exact ⟨q, (f₁ _ _).2 hq.symm, hyy a q _ ((f₁ _ _).2 hq.symm) (hx a)⟩
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨S.th a, S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := F)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    have z1 : ∀ a, algebraMap (FractionRing V) F (yK ⟨S.th a, S.th_mem a⟩) = 0 := fun a => z0 a
    refine ⟨⊤, fun b => ⟨by rw [z1 b, AddValuation.map_zero], fun _ hb => absurd ?_ hb⟩,
      fun n _ _ a ha => ⟨a, ha, by simp, by rw [z1 a, AddValuation.map_zero]⟩⟩
    exact (map_eq_zero_iff _ (algebraMap (FractionRing V) F).injective).1 (z1 b)
  have tv' : ∀ a z J, Good A.L z J → sA th (ptSecT A.A (x a)).left z J =
      @id ((TFK (R := V) F).left.presheaf.stalk z)
        (cst (R := V) F z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc := fun a => by
    rw [split a]
    constructor
    · intro h; rw [h, add_zero]
    · intro h
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
      rw [← hs] at h
      have e1 := congrArg (((-s : ℚ) : WithTop ℚ) + ·) h
      simp only [← add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, zero_add] at e1
      exact e1
  refine ⟨v sc, fun b => ?_, fun n hn hnm a ha => ?_⟩
  · obtain ⟨q, hq₁, hq₂⟩ := ex b
    have hk := (key q _ hq₁).1 _ _ (he b) (tv' b)
    have lo : (0 : WithTop ℚ) ≤ v (sc⁻¹ * y₀ ⟨S.th b, S.th_mem b⟩) := by
      have := hk.1 0 fun χ => by
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ D hQ]; simp
        · exact div_nonneg (Int.cast_nonneg (zero_le_one.trans (QForm.Q_pos hϖ D hQ c))) (Nat.cast_nonneg _)
      simpa using this
    have le : v sc ≤ v (y₀ ⟨S.th b, S.th_mem b⟩) := by rw [split b]; exact le_add_of_nonneg_right lo
    refine ⟨le, fun hb _ => lt_of_le_of_ne le fun h => hb ?_⟩
    obtain ⟨z, hz⟩ := hk.2 ((nz b).2 h.symm)
    exact hq₂.trans ((QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz.symm⟩)
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).1 (hq₂.symm.trans ha)
    have hz' : (S.r * S.N) • z = q.y := hz
    let q₀ : QkPt D.toPre F (S.r * S.N) := qkMk hB 0 (q.g + iota hB _ (-z)) (by
      rw [smul_add, qk_nsmul hB, ← map_nsmul, ← map_add, smul_neg, hz', add_neg_cancel])
    have e₀ : f q = f q₀ := (f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨-z, by
      rw [smul_neg, hz', add_neg_cancel]; rfl, rfl⟩)
    obtain ⟨q', x', hy', hx', hpow, hval⟩ :=
      (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 n hn hnm rfl
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := V) F ⟶ A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', (hyy a' q' _ hx' (hx a')).trans (by rw [hy']; rfl), xinj ?_,
      (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

end GlobalTheory.ThetaDvr.Scale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticInjectivePlaneCoordinatesStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_injective_plane_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁),
    Module.finrank F E = 2 → d = d₁ + 2 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.y = 0) →
    (Function.Injective fun z : Matrix (Fin n) (Fin d₁) E => z * H'.ιᵀ) →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
    ∀ K : Submodule F (Matrix (Fin n) (Fin d₁) E), Module.finrank F K = n * d₁ → (∀ z ∈ K, (M₁.co.e (incM F z)).1 = 0) →
      n * d ≤ Module.finrank F (lagr M M₁ H') := by
  first | exact @GlobalTheory.MixedLagr.le_finrank_lagr | exact GlobalTheory.MixedLagr.le_finrank_lagr | (intros; apply GlobalTheory.MixedLagr.le_finrank_lagr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointCompositeLiftLeSpanBlockEigenspacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_adjoint_compositeLift_le_span_blockEigenspaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A.fam.Ok s → Core R F → SchurAll R → ∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A.fam.R t).ZH : Set (A.fam.R t).S.Forms)) := by
  first | exact @GlobalTheory.AdjSpan.range_adjoint_le_span | exact GlobalTheory.AdjSpan.range_adjoint_le_span | (intros; apply GlobalTheory.AdjSpan.range_adjoint_le_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientSchwartzAverage
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.TorusSupportAvg

section Generic

variable {K V Ω : Type} [AddCommGroup K] [AddCommGroup V]

def IsCharAvg (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) (h : Ω → ℂ) : Prop :=
  ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → V), ∑ m, a m = 1 ∧ ∀ Y, ∑ m, a m * ψ (G (w m) Y) = h Y

theorem isCharAvg_one (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) : IsCharAvg ψ G 1 :=
  ⟨1, fun _ => 1, fun _ => 0, by simp, fun Y => by simp⟩

theorem isCharAvg_mul {ψ : AddChar K ℂ} {G : V →+ (Ω → K)} {h₁ h₂ : Ω → ℂ}
    (h1 : IsCharAvg ψ G h₁) (h2 : IsCharAvg ψ G h₂) : IsCharAvg ψ G (h₁ * h₂) := by
  obtain ⟨N₁, a₁, w₁, hs₁, hv₁⟩ := h1
  obtain ⟨N₂, a₂, w₂, hs₂, hv₂⟩ := h2
  refine ⟨N₁ * N₂, fun m => a₁ (finProdFinEquiv.symm m).1 * a₂ (finProdFinEquiv.symm m).2,
    fun m => w₁ (finProdFinEquiv.symm m).1 + w₂ (finProdFinEquiv.symm m).2, ?_, ?_⟩
  · rw [finProdFinEquiv.symm.sum_comp (fun p => a₁ p.1 * a₂ p.2), Fintype.sum_prod_type,
      ← Finset.sum_mul_sum, hs₁, hs₂, one_mul]
  · intro Y
    rw [finProdFinEquiv.symm.sum_comp (fun p => a₁ p.1 * a₂ p.2 * ψ (G (w₁ p.1 + w₂ p.2) Y)),
      Fintype.sum_prod_type, Pi.mul_apply, ← hv₁, ← hv₂, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, Pi.add_apply, AddChar.map_add_eq_mul]
    ring

theorem isCharAvg_prod {ψ : AddChar K ℂ} {G : V →+ (Ω → K)} {ι : Type} (s : Finset ι) (h : ι → Ω → ℂ)
    (hs : ∀ j ∈ s, IsCharAvg ψ G (h j)) : IsCharAvg ψ G (∏ j ∈ s, h j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCharAvg_one ψ G
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact isCharAvg_mul (hs j (Finset.mem_insert_self j s))
      (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

theorem isCharAvg_poly (ψ : AddChar K ℂ) (G : V →+ (Ω → K)) (P : Polynomial ℂ) (hP : P.eval 1 = 1) (w₀ : V) :
    IsCharAvg ψ G (fun Y => P.eval (ψ (G w₀ Y))) := by
  refine ⟨P.natDegree + 1, fun m => P.coeff m, fun m => (m : ℕ) • w₀, ?_, ?_⟩
  · rw [Fin.sum_univ_eq_sum_range (fun i => P.coeff i), ← hP, Polynomial.eval_eq_sum_range]
    simp
  · intro Y
    dsimp only
    rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun i => P.coeff i * ψ (G w₀ Y) ^ i)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_nsmul, Pi.smul_apply, AddChar.map_nsmul_eq_pow]

end Generic

def killPoly (Z : Finset ℂ) : Polynomial ℂ :=
  ∏ ζ ∈ Z.filter (· ≠ 1), (Polynomial.C (1 - ζ)⁻¹ * (Polynomial.X - Polynomial.C ζ))

theorem killPoly_eval_one (Z : Finset ℂ) : (killPoly Z).eval 1 = 1 := by
  unfold killPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_one fun ζ hζ => ?_
  have : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm (Finset.mem_filter.1 hζ).2)
  simp [this]

theorem killPoly_eval_eq_zero {Z : Finset ℂ} {z : ℂ} (hz : z ∈ Z) (h1 : z ≠ 1) : (killPoly Z).eval z = 0 := by
  unfold killPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨hz, h1⟩) (by simp)

theorem finite_image_of_isLocallyConstant {Ω : Type} [TopologicalSpace Ω] {g : Ω → ℂ} (hg : IsLocallyConstant g)
    {S : Set Ω} (hS : IsCompact S) : (g '' S).Finite := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [Set.image_eq_range]
  exact (hg.comp_continuous continuous_subtype_val).range_finite

theorem rank_ne_of_vecMul_eq_zero {K : Type} [Field K] {n d : ℕ} {c : Fin n → K} (hc : c ≠ 0)
    {Y : Matrix (Fin n) (Fin d) K} (h : Matrix.vecMul c Y = 0) : Y.rank ≠ n := by
  rw [← Matrix.rank_transpose, Matrix.rank]
  have hker : c ∈ LinearMap.ker Yᵀ.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, h]
  have hne : LinearMap.ker Yᵀ.mulVecLin ≠ ⊥ := by
    intro hb; rw [hb, Submodule.mem_bot] at hker; exact hc hker
  have hpos : 0 < Module.finrank K (LinearMap.ker Yᵀ.mulVecLin) := by
    rw [Nat.pos_iff_ne_zero]; exact fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
  have hrn := LinearMap.finrank_range_add_finrank_ker Yᵀ.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  omega

end GlobalTheory.TorusSupportAvg

namespace GlobalTheory.TorusSupportAvg

theorem exists_charAvg_mul_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ (n d : ℕ) (c : Fin n → Fv F v), c ≠ 0 → ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
    (∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → f Y = 0) →
    ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → Fin d → Fv F v), ∑ m, a m = 1 ∧
      ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (∑ m, a m * ψ₀ (∑ k, ∑ l, Y k l * c k * w m l)) * f Y = 0 := by
  intro F _ _ v ψ₀ hψ hne n d c hc f hf hrank
  classical
  have hlc : IsLocallyConstant ψ₀ :=
    @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.isLocallyConstant_addChar _ _ (GlobalTheory.LocalData.complRel v) _ (GlobalTheory.LocalData.isLocalField v) ψ₀ hψ
  obtain ⟨hloc, hcs⟩ : IsLocallyConstant f ∧ HasCompactSupport f := hf
  let G : (Fin d → Fv F v) →+ (Matrix (Fin n) (Fin d) (Fv F v) → Fv F v) :=
    AddMonoidHom.mk' (fun w Y => ∑ k, ∑ l, Y k l * c k * w l) (by
      intro w₁ w₂; funext Y; simp [mul_add, Finset.sum_add_distrib])
  have hG : ∀ w Y, G w Y = ∑ k, ∑ l, Y k l * c k * w l := fun _ _ => rfl
  have hGc : ∀ w, Continuous (G w) := by
    intro w
    show Continuous fun Y : Matrix (Fin n) (Fin d) (Fv F v) => ∑ k, ∑ l, Y k l * c k * w l
    exact continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ =>
      ((continuous_id.matrix_elem k l).mul continuous_const).mul continuous_const

  set S := Function.support f with hSdef
  have hSc : IsCompact S := by
    have hcl : IsClosed S := by
      have := (hloc.isClopen_fiber 0).isOpen.isClosed_compl
      convert this using 1
      ext x; simp [S, Function.mem_support]
    exact hcs.of_isClosed_subset hcl (subset_tsupport f)

  obtain ⟨t₀, ht₀⟩ : ∃ t, ψ₀ t ≠ 1 := by
    by_contra h; push_neg at h; exact hne (by ext x; simp [h x])
  have hex : ∀ Y ∈ S, ∃ w, ψ₀ (G w Y) ≠ 1 := by
    intro Y hY
    have hr : Y.rank = n := by by_contra h; exact hY (hrank Y h)
    have hv : Matrix.vecMul c Y ≠ 0 := fun h => rank_ne_of_vecMul_eq_zero hc h hr
    obtain ⟨l, hl⟩ : ∃ l, Matrix.vecMul c Y l ≠ 0 := by
      by_contra h; push_neg at h; exact hv (funext h)
    refine ⟨Pi.single l (t₀ / Matrix.vecMul c Y l), ?_⟩
    have : G (Pi.single l (t₀ / Matrix.vecMul c Y l)) Y = t₀ := by
      rw [hG]
      simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_mul]
      have e : ∑ k, Y k l * c k = Matrix.vecMul c Y l := by
        simp only [Matrix.vecMul, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [e]; field_simp
    rw [this]; exact ht₀
  choose! wch hwch using hex
  have hopen : ∀ Y, IsOpen {Y' | ψ₀ (G (wch Y) Y') ≠ 1} := fun Y =>
    isOpen_compl_singleton.preimage (hψ.comp (hGc _))
  obtain ⟨t, htS, hcov⟩ := hSc.elim_nhds_subcover (fun Y => {Y' | ψ₀ (G (wch Y) Y') ≠ 1})
    (fun Y hY => (hopen Y).mem_nhds (hwch Y hY))
  have hfin : ∀ j, ((fun Y => ψ₀ (G (wch j) Y)) '' S).Finite := fun j =>
    finite_image_of_isLocallyConstant (hlc.comp_continuous (hGc _)) hSc
  have hrep := isCharAvg_prod (ψ := ψ₀) (G := G) t
    (fun j Y => (killPoly (hfin j).toFinset).eval (ψ₀ (G (wch j) Y)))
    (fun j _ => isCharAvg_poly ψ₀ G _ (killPoly_eval_one _) (wch j))
  obtain ⟨N, a, w, hs, hval⟩ := hrep
  refine ⟨N, a, w, hs, fun Y => ?_⟩
  have hv := hval Y
  simp only [hG] at hv
  rw [hv]
  by_cases hY : f Y = 0
  · rw [hY, mul_zero]
  · have hYS : Y ∈ S := hY
    obtain ⟨j, hj, hjY⟩ : ∃ j ∈ t, ψ₀ (G (wch j) Y) ≠ 1 := by
      have := hcov hYS
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨j, hj, h⟩ := this
      exact ⟨j, hj, h⟩
    rw [Finset.prod_apply, Finset.prod_eq_zero hj, zero_mul]
    exact killPoly_eval_eq_zero ((hfin j).mem_toFinset.2 ⟨Y, hYS, rfl⟩) hjY

end GlobalTheory.TorusSupportAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalModelCoordinatesStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_model_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f ∧ ∀ x, hat (f x) = M.co.e (incM F x) := by
  first | exact @GlobalTheory.MixedLagr.ratCoord_linear_injective | exact GlobalTheory.MixedLagr.ratCoord_linear_injective | (intros; apply GlobalTheory.MixedLagr.ratCoord_linear_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeExistsBaseLevelVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.RowTypeVec

theorem vec_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i, ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) ((PW i).ψ κ)) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hgen n hF PY PW hPY hPW π hπ i
  obtain ⟨v, hvS, hv0, hvT, hvG⟩ := GlobalTheory.T.exists_good_fixed_vector_of_type_occurring_in_rows R F hOk hC PY π hπ
  obtain ⟨x, hxS, hx0, hxT⟩ := GlobalTheory.T.exists_baseLevel_vector_of_principalLevel_fixed R F hOk hC hgen PY (principalLevelFrame.FinTyp.conjT π) v hvS hv0 hvT hvG
  set y : Formalism.AUTREP.GAf D.host.E n → ℂ := fun g => star (x g) with hy
  have hyS : y ∈ π.S := hxS
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    funext g
    have := congrFun h g
    simpa [hy] using this
  have hyT : principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))))
      (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))) (PY.ψ κ)) y := by
    intro κ hκ
    have e := hxT κ hκ
    funext g
    have eg := congrFun e g
    simp only [principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul] at eg
    simp only [hy, principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul, eg, star_mul', GlobalTheory.T.star_rows_level_character_eq_lifts_level_character R F false]
  obtain ⟨h, hh⟩ := GlobalTheory.T.levels_standardFrames_conjugate_standardGroup R F hC i hF PY (PW i) hPY (hPW i) (R.levL F false (sg0 D A))
  refine ⟨Formalism.L2.NG.rt D.host.E n h y, π.stable h y hyS, ?_, ?_⟩
  · intro h0
    apply hy0
    have := congrArg (Formalism.L2.NG.rt D.host.E n h⁻¹) h0
    rwa [principalLevelFrame.rt_rt, inv_mul_cancel, principalLevelFrame.rt_one, map_zero] at this
  · intro κ hκ
    obtain ⟨h1, h2⟩ := hh κ hκ
    have e : κ * h = h * (h⁻¹ * κ * h) := by group
    show Formalism.L2.NG.rt D.host.E n κ (Formalism.L2.NG.rt D.host.E n h y) = _
    rw [principalLevelFrame.rt_rt, e, ← principalLevelFrame.rt_rt, hyT _ h1, map_smul]
    exact congrArg (· • Formalism.L2.NG.rt D.host.E n h y) h2.symm

end GlobalTheory.RowTypeVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartzStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_coset_indicator_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB | exact GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB | (intros; apply GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_indicator_coset_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 → ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | exact GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | (intros; apply GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSumSplitTensorStatement
section
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_sum_split_tensor : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → Af F) → ℂ), g ∈ SB (κ ⊕ κ' → Af F) → ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧ (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  first | exact @GlobalTheory.SBBlocks.sum_prod_blocks | exact GlobalTheory.SBBlocks.sum_prod_blocks | (intros; apply GlobalTheory.SBBlocks.sum_prod_blocks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslatesStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ 𝒱 : Set (VA F N → ℂ), (∀ f ∈ 𝒱, Continuous f ∧ QuasiV ψ f ∧ ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) → (∀ f ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0) → (∀ f ∈ 𝒱, ∀ (x : Fin N → AF F) (k : ℕ), ∃ C : ℝ, ∀ t : Fin N → mixedEmbedding.mixedSpace F, ‖t‖ ^ k * ‖invV ψ ν 𝓓 f (x + embR t)‖ ≤ C) → ∀ f ∈ 𝒱, ∀ x : Fin N → AF F, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = invV ψ ν 𝓓 f (x + embR t) := by
  first | exact @GlobalTheory.ThetaTransform.schwartz_invV_realTranslate | exact GlobalTheory.ThetaTransform.schwartz_invV_realTranslate | (intros; apply GlobalTheory.ThetaTransform.schwartz_invV_realTranslate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandardStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_square_root_weil_pairing_standard : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  first | exact @GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | exact GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | (intros; apply GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf <;> assumption)
end

