import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValueTensorDataTransportLambdaBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRosMove

theorem rosati_alg {U : Type} [CommGroup U] (g : Fin 6 → U) (u : U) :
    (∏ k, g k ^ rosatiε k) * u * (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5) := by
  rw [Fin.prod_univ_six]
  show g 0 ^ (1 : ℤ) * g 1 ^ (-1 : ℤ) * g 2 ^ (-1 : ℤ) * g 3 ^ (-1 : ℤ) * g 4 ^ (1 : ℤ) * g 5 ^ (1 : ℤ) * u *
    (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

theorem rosVT_move : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (O : Type) [CommRing O] [StarRing O] (oa : D'.toPre.P.OAct O) (x : O) (ρ' : N'.A → N'.A → F), GlobalTheory.Relabel.RosV ν' oa x ρ' → ∃ ρ'' : N'.A → N'.A → F, GlobalTheory.Mum.TensRos.RosVT T ν ν' (oa.act (star x)) (oa.act x) ρ'' ∧ ∀ a b, ρ'' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a) * wv T ν ν' b * wv T ν ν' (a * GlobalTheory.Relabel.actV ν' oa x b)) = ρ' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a * b) * wv T ν ν' a * wv T ν ν' (GlobalTheory.Relabel.actV ν' oa x b)) := by
  intro R _ _ _ _ D D' n W T F _ _ _ N N' ν ν' O _ _ oa x ρ' hR
  obtain ⟨u, hu, u₀, hρ⟩ := hR
  have := oa.hom x
  have := oa.hom (star x)
  have hL₁ : (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).IsLB := LB.isLB_linComb D.toPre.P.isLB _ _
  obtain ⟨u'', hu'', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb D'.toPre.P.isLB _ rosatiε)
    (LB.isLB_linComb hL₁ (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε)
    (LB.linCombIso T.w _ rosatiε) (DVR.linCombIso_isGen T.w T.w_gen _ _) u hu
  refine ⟨fun a b => vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν), ⟨u'', hu'', ?_, fun _ _ => rfl⟩, ?_⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    rw [val_pull hJ, val_one]
    have h1 : (η[D'.toPre.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have hz : ∀ k, (𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A).left := fun k => by
      rw [Category.id_comp, zero2, h1, ← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [MonObj.one_comp]
    choose I hI using fun χ : _ ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ y)
    have hI' : Good D'.toPre.P.L y I := hI
    have e₀ : val u (𝟙 _ ≫ zero2 D'.toPre.P.A) y I = 1 := by
      have := val_corr hI' u₀ (𝟙 _)
      rwa [val_pull hI', val_one] at this
    have m₁ := hJ.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have m₂ := hI'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have H := hv _ (𝟙 _ ≫ zero2 D'.toPre.P.A) y _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (𝟙 _ ≫ zero2 D'.toPre.P.A) y ⟨m₁, m₂⟩
    refine H.trans (Eq.trans (congrArg₂ (· * ·) G e₀) ?_)
    rw [_root_.mul_one]
    have key : ∀ Fn : (_ ⟶ D'.toPre.P.A.left) → ((𝟙_ (Over (Spec (CommRingCat.of R)))).left.presheaf.stalk y)ˣ,
        ∏ a, Fn ((𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) a) ^ rosatiε a = 1 := by
      intro Fn
      simp only [hz]
      simp [Fin.prod_univ_succ, rosatiε]
    exact key (fun ψ => gm ψ y (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (J ψ, I ψ))
      (T.w.s (J ψ, I ψ)))
  · intro a b
    let z : Sp F := IsLocalRing.closedPoint F
    have hN : Good D.toPre.P.L z ν.J := fun q => ν.good q trivial
    have hJ' : Good D'.toPre.P.L z ν'.J := fun q => ν'.good q trivial
    have mT : ∀ y : Sp F ⟶ D'.toPre.P.A.left,
        y z ∈ (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).U (GlobalTheory.Mum.TensRos.tensJ T ν y) :=
      fun y => Set.mem_iInter.2 fun k => hN (y ≫ tensφ T.pr k)
    have m₁ : (lift (ν'.eA a) (ν'.eA b)).left z ∈ LB.wchart (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W))
        (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x))
        (fun k => GlobalTheory.Mum.TensRos.tensJ T ν ((lift (ν'.eA a) (ν'.eA b)).left ≫
          rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k)) := Set.mem_iInter.2 fun k => mT _
    have m₂ := hJ'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (lift (ν'.eA a) (ν'.eA b)).left
    have H := hv _ (lift (ν'.eA a) (ν'.eA b)).left z _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (lift (ν'.eA a) (ν'.eA b)).left z ⟨m₁, m₂⟩
    let Gp : N'.A → ((Sp F).presheaf.stalk z)ˣ := fun p => gm (ν'.eA p).left z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
        (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
    have hW : ∀ p, toStk z (wv T ν ν' p) = (Gp p).val := fun p => by
      have hm : (ν'.eA p).left z ∈ (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
          (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left)) := ⟨mT _, hJ' _⟩
      exact toStk_valF _ _ z hm _
    have ea : ∀ y c, ν'.eA (GlobalTheory.Relabel.actV ν' oa y c) = ν'.eA c ≫ oa.act y := fun y c => ν'.eA.apply_symm_apply _
    let pts : Fin 6 → N'.A := ![GlobalTheory.Relabel.actV ν' oa (star x) a * b, GlobalTheory.Relabel.actV ν' oa (star x) a, b,
      a * GlobalTheory.Relabel.actV ν' oa x b, a, GlobalTheory.Relabel.actV ν' oa x b]
    have hp : ∀ k, (lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (ν'.eA (pts k)).left := fun k => by
      rw [← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [pts, ea]
    have key : ∀ Fn : (Sp F ⟶ D'.toPre.P.A.left) → ((Sp F).presheaf.stalk z)ˣ,
        ∏ k, Fn ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k) ^ rosatiε k =
          ∏ k, Fn (ν'.eA (pts k)).left ^ rosatiε k := fun Fn => by simp only [hp]
    have G' := G.trans (key (fun ψ => gm ψ z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))))
    have v'' := toStk_valF _ _ z m₁ (u''.s _)
    have v' : toStk z (ρ' a b) = (gm (lift (ν'.eA a) (ν'.eA b)).left z _ (u.s fun k => ν'.J
        ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k))).val := by
      rw [hρ]; exact toStk_valF _ _ z m₂ _
    have HH := H.trans (congrArg₂ (· * ·) G' rfl)
    apply (toStk z).injective
    show toStk z (vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν) * _) = _
    simp only [map_mul, hW, v']
    erw [v'', HH]
    simp only [← Units.val_mul]
    congr 1
    exact rosati_alg (fun k => Gp (pts k)) _

end GlobalTheory.Mum.TensRosMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedOfTwoIdempotentFactors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.TwoFac
variable {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ D' : DegPre R}

theorem inc_pr_inc (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    F₂.inc ≫ F₁.pr ≫ F₁.inc = F₂.inc := by
  rw [F₁.pr_inc, he, ← F₂.pr_inc, ← Category.assoc, F₂.inc_pr, Category.id_comp]

theorem comp_inv (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    (F₂.inc ≫ F₁.pr) ≫ (F₁.inc ≫ F₂.pr) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← Category.assoc F₁.pr, ← Category.assoc F₂.inc, inc_pr_inc F₁ F₂ he, F₂.inc_pr]

theorem inv_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e) :
    (F₁.inc ≫ F₂.pr) ≫ (F₂.inc ≫ F₁.pr) = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← Category.assoc F₂.pr, F₂.pr_inc, ← he, ← F₁.pr_inc, Category.assoc F₁.pr, ← Category.assoc F₁.inc, F₁.inc_pr,
    Category.id_comp]

theorem xi_xp_xi (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) (a : D₂.X) :
    F₁.xi (F₁.xp (F₂.xi a)) = F₂.xi a := by
  rw [F₁.xi_xp, hXe, ← F₂.xi_xp, F₂.xp_xi]

theorem c_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) (a : D₂.X) :
    D₂.c a ≫ F₂.inc ≫ F₁.pr = D₁.c (F₁.xp (F₂.xi a)) := by
  have h := F₁.c_xi (F₁.xp (F₂.xi a))
  rw [xi_xp_xi F₁ F₂ hXe] at h
  rw [← Category.assoc, ← F₂.c_xi, h, Category.assoc, F₁.inc_pr, Category.comp_id]

def xEquiv (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (hXe : ∀ z : D'.X, F₁.e • z = F₂.e • z) : D₂.X ≃+ D₁.X where
  toFun a := F₁.xp (F₂.xi a)
  invFun a := F₂.xp (F₁.xi a)
  left_inv a := by
    show F₂.xp (F₁.xi (F₁.xp (F₂.xi a))) = a
    rw [xi_xp_xi F₁ F₂ hXe, F₂.xp_xi]
  right_inv a := by
    show F₁.xp (F₂.xi (F₂.xp (F₁.xi a))) = a
    rw [F₂.xi_xp, ← hXe, ← F₁.xi_xp, F₁.xp_xi, F₁.xp_xi]
  map_add' a b := by simp

theorem lift_comp (F₁ : Factor D₁ D') (F₂ : Factor D₂ D') (he : F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e)
    (hf : F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f) :
    (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) : G2 D₂.P.A ⟶ G2 D₁.P.A).left ≫
      (lift (fst D₁.P.A D₁.P.A ≫ F₁.inc) (snd D₁.P.A D₁.P.A ≫ F₁.inc ≫ F₁.o.onB.act F₁.f) : G2 D₁.P.A ⟶ G2 D'.P.A).left =
    (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₂.o.onB.act F₂.f) : G2 D₂.P.A ⟶ G2 D'.P.A).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% (inc_pr_inc F₁ F₂ he), inc_pr_inc F₁ F₂ he, hf]

theorem formEq_cancel {X Y Y' : Scheme.{0}} {K : Type} [Fintype K] (ε : K → ℤ) (A B : K → (Y ⟶ X)) (A₁ B₁ : K → (Y' ⟶ X))
    (h : Y ⟶ Y') (hA : ∀ k, h ≫ A₁ k = A k) :
    FormEq (Sum.elim (Sum.elim A B) (fun k => h ≫ Sum.elim A₁ B₁ k))
      (Sum.elim (Sum.elim ε (fun k => - ε k)) (fun k => - Sum.elim ε (fun k => - ε k) k))
      (Sum.elim (fun k => h ≫ B₁ k) B) (Sum.elim ε (fun k => - ε k)) := by
  intro U _ g
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hA, neg_neg, zpow_neg, Finset.prod_inv_distrib]
  generalize ∏ a₁, g (A a₁) ^ ε a₁ = a
  generalize ∏ x, g (B x) ^ ε x = b
  generalize ∏ x, g (h ≫ B₁ x) ^ ε x = c
  rw [mul_inv, inv_inv, _root_.mul_comm a, _root_.mul_assoc, mul_inv_cancel_left, _root_.mul_comm]

theorem samePol_of_two_factors : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ D' : DegPre R), D₁.TauBimult → ∀ (F₁ : Factor D₁ D') (F₂ : Factor D₂ D'), F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e → F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f → (∀ z : D'.X, F₁.e • z = F₂.e • z) → (∀ z : D'.X, F₁.f • z = F₂.f • z) → SamePol D₁ D₂ := by
  intro R _ _ D₁ D₂ D' hB F₁ F₂ he hf hXe hXf
  haveI := F₂.inc_hom
  haveI := F₁.pr_hom
  let eI : D₂.P.A ≅ D₁.P.A := ⟨F₂.inc ≫ F₁.pr, F₁.inc ≫ F₂.pr, comp_inv F₁ F₂ he, inv_comp F₁ F₂ he⟩
  haveI : IsMonHom eI.hom := inferInstanceAs (IsMonHom (F₂.inc ≫ F₁.pr))
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  refine ⟨GlobalTheory.PolDeg.Wit.ofDeg D₁ hB, AddEquiv.refl _, xEquiv F₁ F₂ hXe, GlobalTheory.PolDeg.Wit.refines_ofDeg D₁ hB, ?_⟩
  let β₂ := (lift (fst D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) (snd D₂.P.A D₂.P.A ≫ F₂.inc ≫ F₁.pr) : G2 D₂.P.A ⟶ G2 D₁.P.A).left
  have hsq : IsSquare (F₂.inc ≫ F₁.pr).left β₂ := by
    constructor
    · rw [← Over.comp_left, lift_fst, Over.comp_left]
    · rw [← Over.comp_left, lift_snd, Over.comp_left]

  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ _) (Classical.arbitrary _)⟩
  have hL₁ := D₁.P.isLB
  have hL₂ := D₂.P.isLB
  have hL' := D'.P.isLB
  have h₁₂ := join_isLB hL₁ hL₂
  have hN := join_isLB h₁₂ hL'
  have P₁ : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D₁.P.L (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) :=
    (isPart_inl _ _).trans (isPart_inl _ _)
  have P₂ : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D₂.P.L (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) :=
    (isPart_inl _ _).trans (isPart_inr _ _)
  have P' : IsPart (join (join D₁.P.L D₂.P.L) D'.P.L) D'.P.L coprod.inr Prod.snd := isPart_inr _ _
  have sπ₁ : Function.Surjective (Prod.fst ∘ Prod.fst : (join (join D₁.P.L D₂.P.L) D'.P.L).ι → D₁.P.L.ι) :=
    (fst_surjective hL₂).comp (fst_surjective hL')
  have sπ₂ : Function.Surjective (Prod.snd ∘ Prod.fst : (join (join D₁.P.L D₂.P.L) D'.P.L).ι → D₂.P.L.ι) :=
    (snd_surjective hL₁).comp (fst_surjective hL')
  obtain ⟨t₂, ht₂, vt₂⟩ := exists_gen_of_iso P' P₂ F₂.w F₂.w_gen
  obtain ⟨t₁, ht₁, vt₁⟩ := exists_gen_of_iso P' P₁ F₁.w F₁.w_gen
  have hℓ := lift_comp F₁ F₂ he hf
  let t := LB.mulGen _ _ _ _ _ t₂ (LB.invGen _ _ _ (LB.pullGen _ _ _ t₁ β₂))
  have ht : t.IsGen := LB.isGen_mulGen _ _ _ _ _ _ _ ht₂ (LB.isGen_invGen _ _ _ _ (LB.isGen_pullGen _ _ _ _ ht₁ _))
  obtain ⟨t', ht', vt'⟩ := exists_gen hN (formEq_cancel _ _ _ _ _ β₂ (fun k => by rw [← Category.assoc, hℓ])) t ht
  obtain ⟨w, hw, vw⟩ := exists_iso_of_gen P₁ P₂ hL₁ hL₂ sπ₁ sπ₂ t' ht'
  refine ⟨(F₂.inc ≫ F₁.pr).left, β₂, w, (isGrpPullback_of_iso eI).congr hs.symm rfl, hsq, hw, fun a => ?_, ?_⟩
  · show (D₂.c a).left ≫ (F₂.inc ≫ F₁.pr).left = spMap (RingHom.id R) ≫ (D₁.c (F₁.xp (F₂.xi a))).left
    rw [hs, Category.id_comp, ← Over.comp_left, c_comp F₁ F₂ hXe]
  intro κ hκ a b z J J' hJ hJ'
  obtain rfl : κ = 𝟙 _ := by
    rw [hs, Category.comp_id] at hκ
    have : Mono (jK R) := GlobalTheory.PolDeg.Wit.mono_jK
    exact (cancel_mono (jK R)).1 (hκ.trans (Category.id_comp _).symm)
  obtain ⟨J₁₂, hJ₁₂, e₁, e₂⟩ := exists_good_join hL₁ hL₂ hJ hJ'
  choose I hI using fun χ : (TK R).left ⟶ D'.P.A.left => exists_chart hL' (χ z)
  obtain ⟨JN, hJN, e₃, e₄⟩ := exists_good_join h₁₂ hL' hJ₁₂ (J₂ := I) hI
  have r₁ : GlobalTheory.Mum.Two.rs (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) JN = J := by
    rw [← e₁, ← e₃]; funext ψ; simp only [GlobalTheory.Mum.Two.rs, GlobalTheory.Mum.Two.rl, GlobalTheory.Mum.Two.rr, Function.comp, Category.assoc]
  have r₂ : GlobalTheory.Mum.Two.rs (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) JN = J' := by
    rw [← e₂, ← e₃]; funext ψ; simp only [GlobalTheory.Mum.Two.rs, GlobalTheory.Mum.Two.rl, GlobalTheory.Mum.Two.rr, Function.comp, Category.assoc]
  have r₃ : GlobalTheory.Mum.Two.rs coprod.inr Prod.snd JN = I := e₄
  have hp : (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left ≫ β₂ =
      (lift (toUnit (TK R) ≫ D₁.c (F₁.xp (F₂.xi a))) (toUnit (TK R) ≫ D₁.c (F₁.xp (F₂.xi b)))).left := by
    simp only [β₂]
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc,
      c_comp F₁ F₂ hXe, c_comp F₁ F₂ hXe]
  have v := vw _ (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN hJN
  rw [vt' _ _ z JN hJN] at v
  have hv : val t (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN =
      val t₂ (lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left z JN *
        (val t₁ ((lift (toUnit (TK R) ≫ D₂.c a) (toUnit (TK R) ≫ D₂.c b)).left ≫ β₂) z JN)⁻¹ := by
    rw [val_mul hJN, val_inv, val_pull hJN]
  rw [hv, vt₂ _ _ z JN hJN, vt₁ _ _ z JN hJN, r₁, r₂, r₃, hp] at v
  have hF₂ := F₂.tau a b z I J' hI hJ'
  have hF₁ := F₁.tau (F₁.xp (F₂.xi a)) (F₁.xp (F₂.xi b)) z I J hI hJ
  rw [xi_xp_xi F₁ F₂ hXe, xi_xp_xi F₁ F₂ hXe, hXf] at hF₁
  have hQ := (GlobalTheory.PolDeg.Wit.exists_tau D₁ (F₁.xp (F₂.xi a)) (F₁.xp (F₂.xi b))).choose_spec.2 _ (𝟙 _) z J hJ
  change GlobalTheory.PolDeg.lamVal w _ z J J' = GlobalTheory.PolDeg.lamVal F₂.w _ z I J' * (GlobalTheory.PolDeg.lamVal F₁.w _ z I J)⁻¹ at v
  rw [hF₂]
  refine Eq.trans ?_ (congrArg₂ (· * ·) v.symm hQ.symm)
  rw [hF₁, _root_.mul_assoc, inv_mul_cancel_left]

end GlobalTheory.Mum.TwoFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeMorphismsGlueOpenCover
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory

namespace GlobalTheory

open CategoryTheory.Limits

theorem glue_homs_of_opens_cover {X Y : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hU : ⨆ k, U k = ⊤)
    (f : ∀ k, (U k).toScheme ⟶ Y)
    (hf : ∀ k l, X.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ f k =
      X.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ f l) :
    ∃ g : X ⟶ Y, ∀ k, (U k).ι ≫ g = f k := by
  let 𝒰 := X.openCoverOfIsOpenCover U hU
  have hc : ∀ a b, pullback.fst (U a).ι (U b).ι ≫ f a = pullback.snd (U a).ι (U b).ι ≫ f b := by
    intro a b
    have P := isPullback_opens_inf (U a) (U b)
    rw [← cancel_epi P.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc]
    exact hf a b
  exact ⟨𝒰.glueMorphisms f hc, fun k => 𝒰.ι_glueMorphisms f hc k⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def SecTw {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))} {N : ℕ}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) : Prop :=
  ∀ (Z : Scheme.{0}) (p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left),
    p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left →
    p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom →
    ∀ z J, Good A.L z J → sval t' p z J = sval t p' z J
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Set Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ArchLim

section Dens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def densInt (ρ : AlgChart p σ D → CxPts p σ → ℝ) (f : CxPts p σ → ℝ) : ℝ :=
  ∫ y, f y ∂part ρ - ∫ y, f y ∂part fun c y => -ρ c y

def IntegrableDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) (f : CxPts p σ → ℝ) : Prop :=
  Integrable f (part ρ) ∧ Integrable f (part fun c y => -ρ c y)

def IsMDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ D, AEMeasurable (fun v => ρ c (c.e.symm v)) (volume.restrict c.e.target)

theorem isMDens_of_isDens {ρ : AlgChart p σ D → CxPts p σ → ℝ} (h : IsDens ρ) : IsMDens ρ :=
  ⟨h.1, fun c => (h.2 c).aemeasurable c.e.open_target.measurableSet⟩

theorem densInt_chernDens {B : LB X} (φ : Weight p σ B) (f : CxPts p σ → ℝ) :
    densInt (fun (c : AlgChart p σ D) y => c.chernDens φ y) f = φ.chernInt D univ f ∧
      (IntegrableDens (fun (c : AlgChart p σ D) y => c.chernDens φ y) f ↔ φ.ChernIntegrableOn D univ f) := by
  simp [densInt, IntegrableDens, Weight.chernInt, Weight.ChernIntegrableOn, (MixDens.chernPart_eq φ).1,
    (MixDens.chernPart_eq φ).2, integrableOn_univ]

def secondChernDensity (e : ℕ) (Θ : V (e + 2) → V (e + 2) → V (e + 2) → V (e + 2) → ℂ)
    (A : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ) : ℝ :=
  -(∑ s : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)),
    ((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) *
      (Θ (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1)) * ∏ i : Fin e, A (s i.succ.succ) (t i.succ.succ))).re /
    Real.pi ^ e

def secondChernDensityOfMetric {E : X.Modules} {r : ℕ} (h : Met p σ E r) {L : LB X} (φ : Weight p σ L) (e : ℕ)
    (c : AlgChart p σ (e + 2)) (y : CxPts p σ) : ℝ :=
  secondChernDensity e (chTwo (fun u => h.G (h.isVB.pick y) (c.e.symm u)) (c.e y)) (chernMat φ c y)

end Dens

section Cell

variable {n r D : ℕ} (ε : Fin D ≃ Fin n ⊕ Low r)

def base (v : V D) : V n := WithLp.toLp 2 fun a => v (ε.symm (.inl a))

def fib (v : V D) : Low r → ℂ := fun s => v (ε.symm (.inr s))

def pt (u : V n) (x : Low r → ℂ) : V D := WithLp.toLp 2 fun j => Sum.elim (fun a => u a) x (ε j)

theorem base_pt (u : V n) (x : Low r → ℂ) : base ε (pt ε u x) = u := by
  ext j
  simp [base, pt]

theorem fib_pt (u : V n) (x : Low r → ℂ) : fib ε (pt ε u x) = x := by
  ext s
  simp [fib, pt]

def rootWt (G : V n → Matrix (Fin r) (Fin r) ℂ) (i : Fin r) (v : V D) : ℝ :=
  -Real.log (quotGram ((chg (uni (fib ε v)) (G (base ε v))).submatrix (emb i) (emb i))).det.re

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {σ : k →+* ℂ} (π : Y ⟶ B) (w : π ≫ q = p)

def IsCell (c : AlgChart q σ n) (c' : AlgChart p σ D) : Prop :=
  c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ c'.U ∧
    c'.e.target = {v | base ε v ∈ c.e.target} ∧
    ∀ y ∈ c'.e.source, base ε (c'.e y) = c.e (PtsOver.map π w (spMap σ) y)

end Cell

section Pot

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {n : ℕ} {X : Type} [TopologicalSpace X]

def potMat (P : LocPot X) (u : CxPts q σ → X) (c : AlgChart q σ n) (y : CxPts q σ) : Matrix (Fin n) (Fin n) ℂ :=
  cHess n (fun v => (P.φ (u y) (u (c.e.symm v)) : ℂ)) (c.e y)

open Classical in

def potDens (P : LocPot X) (S : Set X) (u : CxPts q σ → X) (c : AlgChart q σ n) (y : CxPts q σ) : ℝ :=
  if u y ∈ S then n.factorial * (2 / Real.pi) ^ n * (potMat P u c y).det.re else 0

end Pot

open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

def up {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) (y : CxPts q (σ.comp β)) :
    CxPts (genStr Z) σ :=
  ⟨pullback.lift (y.1 ≫ j) (spMap σ) (by rw [Category.assoc, hj, y.2, ← Spec.map_comp]; rfl), pullback.lift_snd _ _ _⟩

theorem up_ι {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) (y : CxPts q (σ.comp β)) :
    (up j hj σ y).1 ≫ genι Z = y.1 ≫ j := pullback.lift_fst _ _ _

theorem continuous_up {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) :
    Continuous (up j hj σ) := by
  refine Continuous.subtype_mk ?_ _
  rw [(isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback Z.s (spMap β))).continuous_iff]
  refine (((continuous_comp j).comp continuous_subtype_val).prodMk (continuous_const (y := spMap σ))).congr fun y => ?_
  exact Prod.ext (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm

theorem inner_up {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ)
    (y : CxPts q (σ.comp β)) : Inner (up j hj σ y) ↔ j (y.1 (IsLocalRing.closedPoint ℂ)) ∈ abLocus Z.t.G := by
  have e : genι Z ((up j hj σ y).1 (IsLocalRing.closedPoint ℂ)) = j (y.1 (IsLocalRing.closedPoint ℂ)) :=
    congrArg (fun g : Sp ℂ ⟶ Z.X => g (IsLocalRing.closedPoint ℂ)) (up_ι j hj σ y)
  rw [← e]
  exact not_not.trans (Set.ext_iff.1 Z.ab_gen _).symm

def eigGram {σ : c.F →+* ℂ} (G : EigMet Z σ) {W : Type} (a : W → CxFr Z σ) (τ : E →+* ℂ) (u : W) :
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := (G.gram (a u).1 (a u).2 τ)ᵀ

end Model

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

def CurvBound (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (P : LocPot (CxPts (genStr s.T.Z) σ)) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (U : Set (V n)) (a : V n → CxFr s.T.Z σ), IsOpen U → HolFam U a → ContinuousOn (fun u => (a u).1) U →
    ∀ u ∈ U, Inner (a u).1 → (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u).PosSemidef ∧
      ∀ R : ℝ, 2 ≤ R → ∀ (τ : D.host.E →+* ℂ) (ξ η : V n),
        opNorm (eigGram (x.eigMetAt σ (some R)) a τ u) (eigGram (x.eigMetAt σ (some R)) a τ u)
          (curv (eigGram (x.eigMetAt σ (some R)) a τ) u ξ η) ≤
          C * gnorm (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u) ξ.ofLp *
            gnorm (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u) η.ofLp

end GlobalTheory.ArchLim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOfExpansionModMaximalIdealStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_nonzero_of_expansion_mod_maximalIdeal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (k : ℕ) (s : H0 U.LG.L k)
      (f : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt 0 k s f →
      (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) →
      ∀ y : (thickObj R (maximalIdeal R) 0 G).left,
      (∃ j : Fin 4 → D.toPre.P.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((U.gt 0).pG.left.app _).hom ((f 0).f j))) →
      ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  first | exact @GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero | exact GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero | (intros; apply GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero <;> assumption)
end

