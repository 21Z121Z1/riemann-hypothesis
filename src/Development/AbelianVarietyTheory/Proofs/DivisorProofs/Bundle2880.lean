import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinatorialTangentPointConditionStatement
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combinatorial_tangent_point_condition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (S : Type) [Field S] [Algebra c.F S] (P : FrPt Xo c S) (σ : E →+* ℂ)
    (a a' : Fin (Dw.mult σ) → S) (w : Sp (DualNumber S) ⟶ Z.t.G.left),
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a w →
    IsCombAtG Z.t (GlobalTheory.AllWt.ptF P ≫ Z.j) ((frameOf Z P).v σ) a' w → a = a' := by
  first | exact @GlobalTheory.FramedPointCoeffs.coeffs_unique | exact GlobalTheory.FramedPointCoeffs.coeffs_unique | (intros; apply GlobalTheory.FramedPointCoeffs.coeffs_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomains
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem gm_spMap_unitOn_top {A B : Type} [CommRing A] [CommRing B] (m : A →+* B) (z : Sp B) (k : Aˣ) :
    gm (spMap m) z ⊤ (unitOn k) = gm (𝟙 (Sp B)) z ⊤ (unitOn (Units.map m.toMonoidHom k)) := by
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have nat := congrArg (fun q => q.hom k.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom m))
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom nat.symm

theorem from_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D), Function.Injective f → From T ω s ε n D₀.toPre e β ββ w → ∃ ββ' w', From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ Jd D₀ ω s e β ββ w f D hD hf hF
  obtain ⟨pb, sq, gen, hc, hτ⟩ := hF
  have hR : ∃ (β₂₁ : (G2 D.P.A).left ⟶ (G2 D₀.toPre.P.A).left)
      (w₁ : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₀.toPre.P.A D₀.toPre.P.L).pull β₂₁)),
      IsGrpPullback D.P.A D₀.toPre.P.A (spMap f) (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ∧
      IsSquare (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) β₂₁ ∧ w₁.IsGen ∧
      (∀ a, (D.c a).left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) =
        spMap f ≫ (D₀.toPre.c (hD.xe a)).left) ∧
      ∀ κ : (TK V).left ⟶ (TK R).left, κ ≫ jK R = jK V ≫ spMap f → ∀ a b z J J', Good D₀.toPre.P.L z J →
        Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
          lamVal w₁ (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J J' *
            val (D₀.toPre.tau (hD.xe a) (hD.xe b)) κ z J := by
    obtain ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, tau₁⟩ := GlobalTheory.MumFam.refAt_pull R V f hf Jd D₀ D hD
    exact ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, fun κ hκ a b z J J' hJ hJ' => (tau₁ κ hκ a b z J J' hJ hJ').trans
      (congrArg _ ((Wit.exists_tau D₀.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ κ z J hJ))⟩
  obtain ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, tau₁⟩ := hR
  have hΛT : (abelian₂ T.B T.M.L).IsLB := DVR.linComb_isLB _ T.M.isLB _ _
  have hΛ₀ : (abelian₂ D₀.toPre.P.A D₀.toPre.P.L).IsLB := DVR.linComb_isLB _ D₀.toPre.P.isLB _ _
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  obtain ⟨w', T3⟩ := exists_comp hΛ₀ w w₁ ((isGen_iff _).1 gen) ((isGen_iff _).1 gen₁) hΛT hΛ
  refine ⟨β₂₁ ≫ ββ, w', (IsGrpPullback.comp pb₁ pb).congr (GlobalTheory.HalfBC.spMap_comp_spMap' ω f) rfl, ⟨?_, ?_⟩,
    (isGen_iff _).2 (T3.pgen_comp hΛ₀ ((isGen_iff _).1 gen) ((isGen_iff _).1 gen₁)), fun a => ?_, fun a b => ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (β₂₁ ≫ ·) sq.1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) sq₁.1).trans (Category.assoc _ _ _))))
  · exact (Category.assoc _ _ _).trans ((congrArg (β₂₁ ≫ ·) sq.2).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) sq₁.2).trans (Category.assoc _ _ _))))
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ β) (c₁ a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (spMap f ≫ ·) (hc (hD.xe a))).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (GlobalTheory.HalfBC.spMap_comp_spMap' ω f))))))
  · obtain ⟨k₀, hk₀, hv₀⟩ := hτ (hD.xe a) (hD.xe b)
    let m : FractionRing R →+* FractionRing V := IsLocalization.map (FractionRing V) f (M := nonZeroDivisors R)
      (T := nonZeroDivisors V) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)
    have hm : ∀ r, m (algebraMap R (FractionRing R) r) = algebraMap V (FractionRing V) (f r) := fun r =>
      IsLocalization.map_eq _ _
    refine ⟨Units.map m.toMonoidHom k₀, ?_, fun z Jt J' hJt hJ' => ?_⟩
    · show m k₀ = _
      rw [hk₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, hm]
      rfl
    · let κ : (TK V).left ⟶ (TK R).left := spMap m
      have hκ : κ ≫ jK R = jK V ≫ spMap f := by
        show spMap m ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap V (FractionRing V)) ≫ spMap f
        rw [GlobalTheory.HalfBC.spMap_comp_spMap', GlobalTheory.HalfBC.spMap_comp_spMap']
        congr 1
        exact RingHom.ext hm
      choose J₁ hJ₀ using fun χ : (TK V).left ⟶ D₀.toPre.P.A.left => exists_chart D₀.toPre.P.isLB (χ z)
      have hJ₁ : Good D₀.toPre.P.L z J₁ := hJ₀
      have t₁ := tau₁ κ hκ a b z J₁ J' hJ₁ hJ'
      have n₁ : val (D₀.toPre.tau (hD.xe a) (hD.xe b)) (κ ≫ 𝟙 _) z J₁ = Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (D₀.toPre.tau (hD.xe a) (hD.xe b)) (𝟙 _) (κ z) (fun ψ => J₁ (κ ≫ ψ))) :=
        Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) κ z J₁ hJ₁).2.2.1 _)
      rw [Category.comp_id] at n₁
      have h₀ := hv₀ (κ z) (fun ψ => Jt (κ ≫ ψ)) (fun ψ => J₁ (κ ≫ ψ)) (fun ψ => hJt (κ ≫ ψ)) (fun ψ => hJ₁ (κ ≫ ψ))
      have h₁ := (congrArg (Units.map (κ.stalkMap z).hom.toMonoidHom) h₀).trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
      have g₁ : Units.map (κ.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK R).left) (κ z) ⊤ (unitOn k₀)) =
          gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map m.toMonoidHom k₀)) := by
        rw [← GlobalTheory.ConstFam.gm_comp_stalkMap κ (𝟙 _) z ⊤ trivial, Category.comp_id]
        exact gm_spMap_unitOn_top m z k₀
      have g₂ := (GlobalTheory.HalfBC.lamVal_comp w κ
        (lift (toUnit (TK R) ≫ D₀.toPre.c (hD.xe a)) (toUnit (TK R) ≫ D₀.toPre.c (hD.xe b))).left z Jt J₁ hJt hJ₁).symm
      have g₃ : Units.map (κ.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b)))
          ((TK R).hom ≫ spMap ω) (κ z) (fun ψ => Jt (κ ≫ ψ))) =
          val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b))) (κ ≫ (TK R).hom ≫ spMap ω) z Jt :=
        (Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ κ z Jt hJt).2.2.1 _)).symm
      have hb : κ ≫ (TK R).hom ≫ spMap ω = (TK V).hom ≫ spMap (f.comp ω) := by
        show κ ≫ jK R ≫ spMap ω = jK V ≫ spMap (f.comp ω)
        rw [← Category.assoc, hκ, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
      have hx : ∀ χ, (toUnit (TK V) ≫ D.c χ).left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) =
          κ ≫ (toUnit (TK R) ≫ D₀.toPre.c (hD.xe χ)).left := fun χ => by
        show (jK V ≫ (D.c χ).left) ≫ _ = κ ≫ jK R ≫ (D₀.toPre.c (hD.xe χ)).left
        rw [Category.assoc, c₁ χ, ← Category.assoc, ← Category.assoc, hκ]
      have hP : κ ≫ (lift (toUnit (TK R) ≫ D₀.toPre.c (hD.xe a)) (toUnit (TK R) ≫ D₀.toPre.c (hD.xe b))).left =
          (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β₂₁ := by
        refine Eq.symm ?_
        apply pullback.hom_ext
        · show _ ≫ (fst D₀.toPre.P.A D₀.toPre.P.A).left = _ ≫ (fst D₀.toPre.P.A D₀.toPre.P.A).left
          rw [Category.assoc, sq₁.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
            lift_fst]
          exact hx a
        · show _ ≫ (snd D₀.toPre.P.A D₀.toPre.P.A).left = _ ≫ (snd D₀.toPre.P.A D₀.toPre.P.A).left
          rw [Category.assoc, sq₁.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
            lift_snd]
          exact hx b
      have key : ∀ p : (TK V).left ⟶ (G2 D.P.A).left,
          lamVal w' p z Jt J' = lamVal w (p ≫ β₂₁) z Jt J₁ * lamVal w₁ p z J₁ J' := by
        intro p
        have t := T3 _ p z (fun I => Jt (p ≫ (β₂₁ ≫ ββ) ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
          (fun I => J₁ ((p ≫ β₂₁) ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
          (fun I => J' (p ≫ GlobalTheory.PrimCocycle.lamφ D.P.A I))
          (Set.mem_iInter.2 fun I => hJt _) (Set.mem_iInter.2 fun I => hJ₁ _) (Set.mem_iInter.2 fun I => hJ' _)
        refine t.trans (congrArg₂ (· * ·) ?_ ?_)
        · show _ = gw w (p ≫ β₂₁) z (fun I => Jt ((p ≫ β₂₁) ≫ ββ ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
            (fun I => J₁ ((p ≫ β₂₁) ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
          simp only [Category.assoc]
        · show _ = gw w₁ p z (fun I => J₁ (p ≫ β₂₁ ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
            (fun I => J' (p ≫ GlobalTheory.PrimCocycle.lamφ D.P.A I))
          simp only [Category.assoc]
      show _ = _ * (_ * val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b))) _ z Jt)
      rw [t₁, n₁, h₁, g₁, g₂, g₃, hP, hb, key]
      ac_rfl

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfRefinesPolarisedData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.PsiRing GlobalTheory.PrimCocycle

noncomputable section

namespace GlobalTheory.TInj.FromRefine

theorem from_of_refines : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (ρ : R →+* V) (ω : W →+* R) (s : I → R) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (D : DegPre V) (e' : D.X ≃+ Q.X), Function.Injective ρ → DataFrom T ω s ε n Q e → Refines Q ρ D e' → ∃ β ββ w, From T (ρ.comp ω) (fun i => ρ (s i)) ε n D (e'.trans e) β ββ w := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ ρ ω s Q e D e' hρ hDF hR
  obtain ⟨βQ, β₂Q, wQ, pbQ, sqQ, genQ, cQ, τQ⟩ := hDF
  obtain ⟨βR, β₂R, wR, pbR, sqR, genR, cR, τR⟩ := hR
  have hΛT : (abelian₂ T.B T.M.L).IsLB := DVR.linComb_isLB _ T.M.isLB _ _
  have hΛQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hΛD : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  obtain ⟨w'', hT⟩ := exists_comp hΛQ wQ wR ((isGen_iff _).1 genQ) ((isGen_iff _).1 genR) hΛT hΛD
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D.P.A).left) (z : Z) J JQ J', Good T.M.L z J → Good Q.M.L z JQ →
      Good D.P.L z J' → lamVal w'' p z J J' = lamVal wQ (p ≫ β₂R) z J JQ * lamVal wR p z JQ J' := by
    intro Z p z J JQ J' hJ hJQ hJ'
    have t := hT Z p z (fun I => J (p ≫ (β₂R ≫ β₂Q) ≫ lamφ T.B I))
      (fun I => JQ ((p ≫ β₂R) ≫ lamφ Q.B I)) (fun I => J' (p ≫ lamφ D.P.A I))
      (Set.mem_iInter.2 fun I => hJ (p ≫ (β₂R ≫ β₂Q) ≫ lamφ T.B I))
      (Set.mem_iInter.2 fun I => hJQ ((p ≫ β₂R) ≫ lamφ Q.B I))
      (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ D.P.A I))
    refine t.trans (congrArg₂ (· * ·) ?_ ?_)
    · show _ = gw wQ (p ≫ β₂R) z (fun I => J ((p ≫ β₂R) ≫ β₂Q ≫ lamφ T.B I))
        (fun I => JQ ((p ≫ β₂R) ≫ lamφ Q.B I))
      simp only [Category.assoc]
    · show _ = gw wR p z (fun I => JQ (p ≫ β₂R ≫ lamφ Q.B I)) (fun I => J' (p ≫ lamφ D.P.A I))
      simp only [Category.assoc]
  refine ⟨βR ≫ βQ, β₂R ≫ β₂Q, w'', ?_, isSquare_comp sqR sqQ,
    (isGen_iff _).2 (hT.pgen_comp hΛQ ((isGen_iff _).1 genQ) ((isGen_iff _).1 genR)), ?_, ?_⟩
  · exact (IsGrpPullback.comp pbR pbQ).congr (GlobalTheory.HalfBC.spMap_comp_spMap' ω ρ) rfl
  · intro a
    show (D.c a).left ≫ βR ≫ βQ = spMap (ρ.comp ω) ≫ (T.c₀ ((n : ℤ) • e (e' a))).left
    rw [← Category.assoc, cR, Category.assoc, cQ, ← Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
  · intro a b
    obtain ⟨k, hk, hv⟩ := τQ (e' a) (e' b)
    let m : FractionRing R →+* FractionRing V := IsLocalization.map (FractionRing V) ρ (M := nonZeroDivisors R)
      (T := nonZeroDivisors V) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ hρ)
    have hm : ∀ r, m (algebraMap R _ r) = algebraMap V _ (ρ r) := fun r => IsLocalization.map_eq _ _
    let κ : (TK V).left ⟶ (TK R).left := spMap m
    have hκ : κ ≫ jK R = jK V ≫ spMap ρ := GlobalTheory.HalfBC.gam_comm ρ m hm
    refine ⟨Units.map m.toMonoidHom k, ?_, fun z J J' hJ hJ' => ?_⟩
    · rw [Units.coe_map]
      show m (k : FractionRing R) = _
      rw [hk, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, hm]
      rfl
    · choose JQ hJQ0 using fun χ : (TK V).left ⟶ Q.B.left => exists_chart Q.M.isLB (χ z)
      have hJQ : Good Q.M.L z JQ := hJQ0
      have r1 := τR κ hκ a b z JQ J' hJQ hJ'
      have nQ : val (Q.tau (e' a) (e' b)) (κ ≫ 𝟙 _) z JQ = Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (Q.tau (e' a) (e' b)) (𝟙 _) (κ z) (fun ψ => JQ (κ ≫ ψ))) :=
        Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) κ z JQ hJQ).2.2.1 _)
      rw [Category.comp_id] at nQ
      have r2 := hv (κ z) (fun ψ => J (κ ≫ ψ)) (fun ψ => JQ (κ ≫ ψ)) (fun ψ => hJ (κ ≫ ψ)) (fun ψ => hJQ (κ ≫ ψ))
      rw [r2, map_mul, map_mul] at nQ
      have g1 : Units.map (κ.stalkMap z).hom.toMonoidHom (gm (𝟙 _) (κ z) ⊤ (unitOn k)) =
          gm (𝟙 _) z ⊤ (unitOn (Units.map m.toMonoidHom k)) := by
        rw [← GlobalTheory.ConstFam.gm_comp_stalkMap κ (𝟙 _) z ⊤ trivial, Category.comp_id]
        exact GlobalTheory.PolDeg.gm_spMap_unitOn m k z
      have g2 := (GlobalTheory.HalfBC.lamVal_comp wQ κ
        (lift (toUnit (TK R) ≫ Q.c (e' a)) (toUnit (TK R) ≫ Q.c (e' b))).left z J JQ hJ hJQ).symm
      have g3 : Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (T.τ₀ ((n : ℤ) • e (e' a)) ((n : ℤ) • e (e' b))) ((TK R).hom ≫ spMap ω) (κ z) (fun ψ => J (κ ≫ ψ))) =
          val (T.τ₀ ((n : ℤ) • e (e' a)) ((n : ℤ) • e (e' b))) (κ ≫ (TK R).hom ≫ spMap ω) z J :=
        (Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ ((TK R).hom ≫ spMap ω) κ z J hJ).2.2.1 _)).symm
      have hx : ∀ χ, (toUnit (TK V) ≫ D.c χ).left ≫ βR = κ ≫ (toUnit (TK R) ≫ Q.c (e' χ)).left := fun χ => by
        show (jK V ≫ (D.c χ).left) ≫ βR = κ ≫ jK R ≫ (Q.c (e' χ)).left
        rw [Category.assoc, cR, ← Category.assoc, ← hκ, Category.assoc]
      have hP : (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β₂R =
          κ ≫ (lift (toUnit (TK R) ≫ Q.c (e' a)) (toUnit (TK R) ≫ Q.c (e' b))).left := by
        apply pullback.hom_ext
        · show _ ≫ (fst Q.B Q.B).left = _ ≫ (fst Q.B Q.B).left
          rw [Category.assoc, sqR.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
            ← Over.comp_left, lift_fst]
          exact hx a
        · show _ ≫ (snd Q.B Q.B).left = _ ≫ (snd Q.B Q.B).left
          rw [Category.assoc, sqR.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
            ← Over.comp_left, lift_snd]
          exact hx b
      have hb : κ ≫ (TK R).hom ≫ spMap ω = (TK V).hom ≫ spMap (ρ.comp ω) := by
        rw [← GlobalTheory.HalfBC.spMap_comp_spMap', ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ spMap ω) hκ
      rw [g1, g2, g3, ← hP, hb] at nQ
      rw [r1, nQ, key _ _ z J JQ J' hJ hJQ hJ']
      ac_rfl

end GlobalTheory.TInj.FromRefine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCovers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverCommon

theorem exists_cover_dominating_two : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Cover Y), ∃ (V : Cover Y) (π₁ : V.X ⟶ V₁.X) (π₂ : V.X ⟶ V₂.X), π₁ ≫ V₁.p = V.p ∧ π₂ ≫ V₂.p = V.p ∧ Lies V V₁ π₁ ∧ Lies V V₂ π₂ := by
  intro F _ _ Y V₁ V₂
  obtain ⟨G, _, _, g, k, _, _, hk⟩ := GlobalTheory.T.normal_finite_dominant_refinement F Y V₁ V₂
  obtain ⟨W, a, k', ha, hW, hk'⟩ := GlobalTheory.T.cover_lift_through_normal F Y V₁ V₂ G g k hk
  obtain ⟨W', b, c, hb, hc, hW', hV⟩ := GlobalTheory.T.cover_dominating_pair F Y W V₂ k' hk'
  obtain ⟨e, he₁, he₂⟩ := hW
  obtain ⟨e', he₁', he₂'⟩ := hW'
  refine ⟨W', b ≫ a, c, by rw [Category.assoc, ha, hb], hc, ⟨e' ≫ e, ?_, ?_⟩, hV⟩
  · rw [Category.assoc, he₁, ← Category.assoc, he₁', Category.assoc]
  · rw [Category.assoc, he₂, he₂']

end GlobalTheory.CoverCommon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocycleFormEqConnectionForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.ConnCocycle

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem divPowerCompatDeRhamRelIdeal_zero_dividedPowers (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : rel R (dp0 B) = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨n, a, ha, rfl⟩
  rw [Ideal.mem_bot.1 ha]
  simp [dpow_eval_zero]

theorem cocyc {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (k : (KK (dp0 R) s).Z1)
    {T T' : Thick (dp0 R) s} (φ : T ⟶ T') :
    k.1.2 T' = km1 (SemiHom.of_algHom φ.φ) φ.dp (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ) := by
  have h := congrArg (fun c ↦ c.2.1 T T' φ) (AddMonoidHom.mem_ker.1 k.2)
  change k.1.2 T' - _ - _ = 0 at h
  rw [sub_sub, sub_eq_zero] at h
  exact h

section
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def sndK : (diagExt R B).C →+ K1 R (dp0 B) :=
  AddMonoidHom.mk' (fun c ↦ Submodule.Quotient.mk (TrivSqZeroExt.snd c)) fun a b ↦ by
    rw [TrivSqZeroExt.snd_add, Submodule.Quotient.mk_add]

theorem sndK_apply (c : (diagExt R B).C) : sndK R B c = Submodule.Quotient.mk (TrivSqZeroExt.snd c) := rfl

theorem sndK_mul (x y : (diagExt R B).C) :
    sndK R B (x * y) = (diagExt R B).π x • sndK R B y + (diagExt R B).π y • sndK R B x := by
  show Submodule.Quotient.mk (x * y).snd = x.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) y.snd +
    y.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) x.snd
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1

theorem sndK_alg (r : R) : sndK R B (algebraMap R (diagExt R B).C r) = 0 := by
  rw [sndK_apply, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, Submodule.Quotient.mk_zero]

theorem sndK_dpow (n : ℕ) (a : (diagExt R B).C) (ha : a ∈ RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) :
    sndK R B ((divided₂ (diagExt R B).sq).dpow (n + 1) a) =
      (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow n a) • sndK R B a := by
  rcases n with _ | m
  · rw [(divided₂ (diagExt R B).sq).dpow_one ha, (divided₂ (diagExt R B).sq).dpow_zero ha, map_one, one_smul]
  · have h0 : (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow (m + 1) a) = 0 :=
      (divided₂ (diagExt R B).sq).dpow_mem (Nat.succ_ne_zero m) ha
    rw [squareZeroDividedPowers_dpow _ (by omega), map_zero, h0, zero_smul]

end

section
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem deRhamAlgebraMap_sends_sectionOneForm (ρ : DR R (diagExt R B).C →+ DR R B) (hmul : ∀ x y, ρ (x * y) = ρ x * ρ y)
    (halg : ∀ c, ρ (algebraMap _ (DR R (diagExt R B).C) c) = algebraMap B (DR R B) ((diagExt R B).π c))
    (hD : ∀ c, ρ (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c))
    (α : B →ₐ[R] (diagExt R B).C) (hα : ∀ b, (diagExt R B).π (α b) = b)
    (g : Ω[B⁄R] →+ Ω[B⁄R]) (hg : ∀ b c : B, g (b • D R B c) = b • TrivSqZeroExt.snd (α c))
    (κ : Ω[B⁄R]) : ρ (ι1 ((SemiHom.of_algHom α).m1 κ)) = ι1 (g κ) := by
  induction κ using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, Algebra.smul_def, hmul, halg, hD, hg, map_smul,
      Algebra.smul_def]
    congr 2
    exact hα b
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]

end

theorem form_eq_connForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (k : (KK (dp0 R) s).Z1)
    (f : Z1 (O (dp0 R) s)), k.1.1 = f.1 → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)),
    k.1.2 (Thick.triv B x hx) = Submodule.Quotient.mk (connForm f x hx) := by
  intro R _ X s k f hk B _ _ x hx
  obtain ⟨ρ, hadd, hmul, halg, hD, hrel, -, -⟩ := GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R B ⊥ (dp0 B) (diagExt R B).C
    (RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) (divided₂ (diagExt R B).sq) (diagExt R B).π
    (sndK R B) (sndK_mul R B) (sndK_alg R B) (sndK_dpow R B)
  have h0 := divPowerCompatDeRhamRelIdeal_zero_dividedPowers R B
  simp only [h0, Ideal.mem_bot, sub_sub, sub_eq_zero] at hadd hmul halg hD hrel
  let ρh : DR R (diagExt R B).C →+ DR R B := AddMonoidHom.mk' ρ hadd
  have hD' : ∀ c, ρh (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c) := fun c ↦ hD c _ rfl
  let a := (diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl
  let a' := (diagExt R B).secHom hx (diagSec R B) (fst_derSec _)
  have c1 := cocyc k a
  have c2 := cocyc k a'
  rw [hk] at c1 c2
  obtain ⟨κ, hκ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 (Thick.triv B x hx))
  obtain ⟨θ, hθ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 ((diagExt R B).thick x hx))
  rw [← hκ, ← hθ, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at c1 c2
  have e1 : ρh (ι1 (θ - ((SemiHom.of_algHom a.φ).m1 κ + D R _ (f.1 _ _ a)))) = 0 := hrel _ c1
  have e2 : ρh (ι1 (θ - ((SemiHom.of_algHom a'.φ).m1 κ + D R _ (f.1 _ _ a')))) = 0 := hrel _ c2
  have r1 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a.φ (fun _ ↦ rfl) 0 (fun b c ↦ by
    show (0 : Ω[B⁄R]) = b • TrivSqZeroExt.snd (TrivSqZeroExt.inl c : TrivSqZeroExt B Ω[B⁄R])
    rw [TrivSqZeroExt.snd_inl, smul_zero])
  have r2 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a'.φ (fst_derSec _) (AddMonoidHom.id _) (fun b c ↦ by
    show b • D R B c = b • TrivSqZeroExt.snd (diagSec R B c)
    rw [snd_derSec])
  simp only [map_sub, map_add, r1, r2, hD', AddMonoidHom.zero_apply, AddMonoidHom.id_apply, map_zero,
    zero_add] at e1 e2
  rw [← hκ, Submodule.Quotient.eq]
  change ι1 _ ∈ rel R (dp0 B)
  rw [h0, Ideal.mem_bot, map_sub, sub_eq_zero]
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  change ι1 κ = ι1 (TrivSqZeroExt.snd (f.1 _ _ a)) - ι1 (TrivSqZeroExt.snd (f.1 _ _ a'))
  linear_combination (norm := abel1) e1 - e2

end GlobalTheory.ConnCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifference
section
set_option autoImplicit false

open MvPolynomial GlobalTheory.LineForm

namespace GlobalTheory.LineForm

theorem hs_term_rec (k j : ℕ) (hj : j ≤ k) :
    (C ((-1) ^ (j + 1) * ((k + 2 - (j + 1)).choose (j + 1) : ℝ)) * X 0 ^ (k + 2 - 2 * (j + 1)) * X 1 ^ (j + 1) :
        MvPolynomial (Fin 2) ℝ) =
      X 0 * (C ((-1) ^ (j + 1) * ((k + 1 - (j + 1)).choose (j + 1) : ℝ)) * X 0 ^ (k + 1 - 2 * (j + 1)) * X 1 ^ (j + 1)) -
        X 1 * (C ((-1) ^ j * ((k - j).choose j : ℝ)) * X 0 ^ (k - 2 * j) * X 1 ^ j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  have e1 : j + m + 2 - (j + 1) = m + 1 := by omega
  have e2 : j + m + 1 - (j + 1) = m := by omega
  have e3 : j + m - j = m := by omega
  have e4 : j + m + 2 - 2 * (j + 1) = m - j := by omega
  have e5 : j + m - 2 * j = m - j := by omega
  have e6 : j + m + 1 - 2 * (j + 1) = m - j - 1 := by omega
  rw [e1, e2, e3, e4, e5, e6, Nat.choose_succ_succ']
  rcases lt_or_ge j m with h | h
  · obtain ⟨n, hn⟩ : ∃ n, m - j = n + 1 := ⟨m - j - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]
    simp only [Nat.cast_add, map_mul, map_add, map_pow, map_neg, map_one]
    ring
  · rw [Nat.choose_eq_zero_of_lt (show m < j + 1 by omega)]
    simp only [Nat.cast_add, map_mul, map_add, map_pow, map_neg, map_one, Nat.cast_zero, map_zero]
    ring

theorem hs_add_two (k : ℕ) : hs (k + 2) = X 0 * hs (k + 1) - X 1 * hs k := by
  unfold hs
  rw [Finset.sum_range_succ' _ (k + 2), Finset.sum_range_succ _ (k + 1), Finset.sum_range_succ' _ (k + 1),
    Finset.sum_congr rfl (fun j hj => hs_term_rec k j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))),
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e : k + 2 - (k + 1 + 1) = 0 := by omega
  rw [e]
  simp only [Nat.choose_zero_succ, Nat.cast_zero, mul_zero, map_zero, zero_mul, add_zero, pow_zero, Nat.choose_zero_right,
    Nat.cast_one, mul_one, map_one, one_mul, Nat.sub_zero]
  ring

theorem aeval_hs_mul_sub :
    ∀ k : ℕ, aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) =
      (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp [hs]
  | one =>
    have : hs 1 = X 0 := by simp [hs, Finset.sum_range_succ]
    rw [this, aeval_X]
    simp only [Matrix.cons_val_zero]
    ring
  | more k h0 h1 =>
    rw [hs_add_two, map_sub, map_mul, map_mul, aeval_X, aeval_X]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (X 0 + X 1) * h1 - (X 0 * X 1) * h0

end GlobalTheory.LineForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedDominatingDvrClosedFibrePointIsTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_dominating_dvr_closedFibre_point_is_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  first | exact @GlobalTheory.Mum.trait_at_closed_point | exact GlobalTheory.Mum.trait_at_closed_point | (intros; apply GlobalTheory.Mum.trait_at_closed_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeBundleIso_uniformisedGroup_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (f' g' : G₁ ⟶ G₁) (fA gA : A₁.A ⟶ A₂.A) (fA' gA' : A₁.A ⟶ A₁.A), Gen₀ U₁ U₂ f fA → Gen₀ U₁ U₂ g gA → Gen₀ U₁ U₁ f' fA' → Gen₀ U₁ U₁ g' gA' → LBIso (cubeLB G₂ ![fst G₁ G₁ ≫ f, snd G₁ G₁ ≫ g] U₂.LG.L) (cubeLB G₁ ![fst G₁ G₁ ≫ f', snd G₁ G₁ ≫ g'] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ fA, snd A₁.A A₁.A ≫ gA] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ fA', snd A₁.A A₁.A ≫ gA'] A₁.L) := by
  first | exact @GlobalTheory.Mum.Two.lbIso_cubeLB_generic | exact GlobalTheory.Mum.Two.lbIso_cubeLB_generic | (intros; apply GlobalTheory.Mum.Two.lbIso_cubeLB_generic <;> assumption)
end

