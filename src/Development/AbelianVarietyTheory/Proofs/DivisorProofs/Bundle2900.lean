import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomMumfordGeneratorNormalisedOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem prod_alt_const {U : Type} [CommGroup U] (m : U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), m ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => m ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp

theorem lift_one_psum {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) (1 : T ⟶ G) ≫ psum G (x2 G) I = 1 := by
  rw [comp_psum]
  have e : (fun k => lift (1 : T ⟶ G) (1 : T ⟶ G) ≫ x2 G k) = fun _ => (1 : T ⟶ G) := by
    funext k
    fin_cases k <;> simp [x2]
  rw [e]
  unfold psum
  induction ((List.finRange 2).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

variable {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]

theorem kappa_comp_mφ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (k : MK) :
    (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun _ => (1 : H₁ ⊗ H₁ ⟶ H₂).left ≫ coprod.inr) (fun _ => (1 : H₁ ⊗ H₁ ⟶ H₁).left ≫ coprod.inl) k := by
  rcases k with I | I
  · simp only [mφ, Sum.elim_inl]
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, comp_lift, lift_fst_assoc,
      lift_snd_assoc, MonObj.one_comp, MonObj.one_comp, lift_one_psum]
  · simp only [mφ, Sum.elim_inr]
    rw [← Category.assoc, ← Over.comp_left, lift_one_psum]

theorem exists_isNrm : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    {L₁ : LB H₁.left} {L₂ : LB H₂.left}, (join L₁ L₂).IsLB → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b]
    (t : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)), t.IsGen →
    ∃ u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε), IsNrm u := by
  intro S H₁ H₂ _ _ _ _ L₁ L₂ hL a b _ _ t ht
  have p : ∀ (V : Type) [CommGroup V] (k : ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) → V),
      ∏ i : MK, k ((lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left ≫ mφ H₁ H₂ a b i) ^ mε i = 1 := by
    intro V _ k
    rw [Fintype.prod_sum_type]
    simp only [kappa_comp_mφ, Sum.elim_inl, Sum.elim_inr, mε, zpow_neg, Finset.prod_inv_distrib]
    rw [prod_alt_const, prod_alt_const, inv_one, _root_.mul_one]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := mφ H₁ H₂ a b) (ε' := mε)
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := MK) (K' := MK) (U := V) _
        (c := ∏ i, k (mφ H₁ H₂ a b i) ^ mε i) rfl (DVR.prod_neg _ _ (p V k))) ?_
      simp)
    (LB.mulGen _ _ _ _ _ t (LB.invGen _ _ _ (LB.pullGen _ _ _ t (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  have e : (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left ≫ (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left =
      (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end GlobalTheory.HomMum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectionsEighthPowerGrpObj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eighthPower_inj_exists : ∀ {S : Scheme.{0}} (P C : Over S) [GrpObj P] [IsCommMonObj P] [GrpObj C] (pr : Fin 8 → (P ⟶ C)) (hpr : ∀ a, IsMonHom (pr a)) (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ C)), ∃! x : T ⟶ P, ∀ a, x ≫ pr a = y a), ∃ inj : Fin 8 → (C ⟶ P), (∀ a, IsMonHom (inj a)) ∧ (∀ a b, inj a ≫ pr b = if a = b then 𝟙 C else 1) ∧ ∏ a, (pr a ≫ inj a) = 𝟙 P := by
  intro S P C _ _ _ pr hpr huniv
  have hext : ∀ {T : Over S} (f g : T ⟶ P), (∀ b, f ≫ pr b = g ≫ pr b) → f = g :=
    fun f g h => (huniv _ (fun b => g ≫ pr b)).unique h (fun _ => rfl)
  choose inj hinj using fun a => (huniv C (fun b => if a = b then 𝟙 C else 1)).exists
  have hmon : ∀ a, IsMonHom (inj a) := by
    intro a
    constructor
    · apply hext
      intro b
      haveI := hpr b
      rw [Category.assoc, hinj a b, IsMonHom.one_hom (pr b)]
      split_ifs
      · simp
      · rw [MonObj.comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    · apply hext
      intro b
      haveI := hpr b
      simp only [Category.assoc]
      rw [hinj a b, IsMonHom.mul_hom (pr b), tensorHom_comp_tensorHom_assoc, hinj a b]
      split_ifs
      · simp
      · rw [MonObj.comp_one, ← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_one, MonObj.comp_one, _root_.one_mul]
  refine ⟨inj, hmon, hinj, ?_⟩
  apply hext
  intro b
  haveI := hpr b
  rw [Fin.prod_univ_eight]
  simp only [MonObj.mul_comp, Category.assoc, hinj, MonObj.comp_one, Category.id_comp, Category.comp_id]
  fin_cases b <;> simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwBack

variable {R : Type} [CommRing R] [IsDomain R]

theorem prod_tw (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n : ℕ) (β : D.X) {U : Type} [CommGroup U]
    (g : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, g (tφ D a β k) ^ tε n 0 k = ∏ k, g (D.famφB β k) ^ DegPre.famε n k := by
  rw [Fin.prod_univ_castSucc (n := 4)]
  show (∏ k : Fin 4, _) * g a.left ^ (0 : ℤ) = _
  rw [zpow_zero, _root_.mul_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  fin_cases k <;> rfl

theorem vanMod_of_van (I : Ideal R) {D : DegPre R} {k : ℕ} {α : D.X} (b : D.SecB k α) (e : ℕ) (h : Van I b e) :
    VanMod I b e := by
  intro j
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (thickObj R I e D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero _ y _ hy).symm)
  refine (sec_trans b _ y hy (Good.mem hJ (D.famφB α) _)).trans ?_
  exact (congrArg _ (h _ (𝟙 _) y J hJ)).trans (mul_zero _)

theorem shift_zero {X : Type} [AddCommGroup X] (h h' : X →+ X) (n : ℕ) (mu : X) :
    shift h h' n 0 mu = n • mu := by
  rw [shift, zero_smul, add_zero, natCast_zsmul]

theorem famFE_of_tfe (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (n : ℕ) (F : ∀ β, SecT D a n 0 β)
    (hF : TFE h h' F)
    (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε n)))
    (hs : ∀ α (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) x z J = sval (F α) (x ≫ (DegPre.prB D (FractionRing R)).left) z J) :
    DegPre.FamFE D (FractionRing R) n s := by
  intro mu α u hu hc
  have hT : TRel h mu (F α) (F (α + n • mu)) := by
    have := hF mu α
    rwa [shift_zero] at this
  obtain ⟨u', hu', hv⟩ := exists_gen D.P.isLB (φ' := dφ D a mu α (α + n • mu)) (ε' := dε n 0) (fun U _ g => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, DegPre.deltaφ, DegPre.deltaε, dφ, dε, zpow_neg,
      Finset.prod_inv_distrib, DVR.GC.famφ_eq]
    rw [prod_tw D a n _ (fun ψ => g ((DegPre.prB D (FractionRing R)).left ≫ ψ)),
      prod_tw D a n _ (fun ψ => g ((DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left ≫ ψ))])
    u hu
  have hfac : IsFac D a h n 0 mu α (α + n • mu) u' := by
    refine ⟨hu', fun z J hJ => ?_⟩
    have e := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp, DegPre.famMult, val_pull hJ, val_mul hJ, val_mul hJ, Category.id_comp] at e
    rw [hv _ _ z J hJ, zpow_zero, _root_.mul_one, add_zero, zpow_natCast, zpow_natCast]
    exact e.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (map_pow _ _ _) rfl) (map_pow _ _ _))
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, ← hv _ _ y J hJ, Category.assoc]
  exact hT u' hfac _ (𝟙 _) y J hJ

theorem exists_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h h' : D.toPre.X →+ D.toPre.X) (n : ℕ) (F : ∀ β, SecT D.toPre a n 0 β), Small (maximalIdeal R) (w := id) F → TFE h h' F → ∃ Φ : IntFam (maximalIdeal R) D.toPre n, ∀ β, (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (Φ.f β) x z J = sval (F β) x z J) := by
  intro R _ _ _ _ D a h h' n F hS hF
  have hL := D.toPre.P.isLB
  choose f hf using fun β => exists_sec hL (φ' := D.toPre.famφB β) (ε' := DegPre.famε n)
    (fun U _ g => prod_tw D.toPre a n β g) (F β)
  choose s hs using fun β => exists_sec hL (φ' := DegPre.famφ D.toPre (FractionRing R) β) (ε' := DegPre.famε n)
    (fun U _ g => Finset.prod_congr rfl fun i _ => by rw [DVR.GC.famφ_eq])
    (DVR.pullSec D.toPre.P.L _ _ (f β) (DegPre.prB D.toPre (FractionRing R)).left)
  have hs' : ∀ β (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J),
      Good D.toPre.P.L z J → sval (s β) x z J = sval (f β) (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J :=
    fun β Z x z J hJ => (hs β Z x z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ x z hJ)
  have h1 : Out.scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    unfold Out.scal; rw [map_one, map_one]
  refine ⟨⟨⟨s, famFE_of_tfe D.toPre a h h' n F hF s fun β Z x z J hJ => (hs' β Z x z J hJ).trans (hf β Z _ z J hJ)⟩,
    f, fun β => ?_, fun e => (hS e).subset fun β hβ hv => hβ (vanMod_of_van _ _ e fun Z x z J hJ =>
      (hf β Z _ z J hJ).trans (hv Z x z J hJ))⟩, hf⟩
  rw [h1]
  exact DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' β _ _ y J hJ).symm

end GlobalTheory.TwBack
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorOfPsiCoordinate
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.PsiIntGen

theorem gs_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Spec (CommRingCat.of B)) (a : A) :
    gs (Spec.map (CommRingCat.ofHom f)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      gs (𝟙 (Spec (CommRingCat.of B))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f a)) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have e' : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f a) =
      ((Spec.map (CommRingCat.ofHom f)).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := e
  rw [e']
  have := gs_pull (𝟙 (Spec (CommRingCat.of B))) (Spec.map (CommRingCat.ofHom f)) z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [Category.id_comp] at this
  exact this.symm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)), gam.IsGen ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  intro V _ _ D mu r hr
  obtain ⟨j, hj, h, e⟩ := hr
  obtain ⟨t, ht, vt⟩ := PsiSpread.exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)
    j (fun y => Set.mem_iInter.2 fun _ => hj trivial) ⊤ (fun _ => trivial) 1
  refine ⟨t, ht, fun z J hJ => ?_⟩
  have q : jFK (R := V) (FractionRing V) ≫ ptK (D.c mu) =
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left := (Category.assoc _ _ _).symm
  have a := gen_trans (D.psi_gen mu) (jFK (R := V) (FractionRing V)) z (j' := j) (hJ.mem _ _) (h trivial)
  have b := vt _ (toUnit (TF (R := V) (FractionRing V))).left z _ (hJ.mem _ _)
  rw [map_one, _root_.mul_one] at b
  have c : (gm (jFK (R := V) (FractionRing V)) z (LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c mu)) j)
      ((D.psi mu).s j)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) := by
    refine (gs_unit _ _ _ (h trivial) _).symm.trans ?_
    refine (gs_res (jFK (R := V) (FractionRing V)) z h trivial ((D.psi mu).s j).val).symm.trans ?_
    refine (congrArg (gs (jFK (R := V) (FractionRing V)) z _) e.symm).trans ?_
    refine (gs_pull (jFK (R := V) (FractionRing V)) (jK V) z ⊤ trivial _).trans ?_
    refine (gs_res _ z (le_top : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ ⊤) trivial _).trans ?_
    have s : jFK (R := V) (FractionRing V) ≫ jK V = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
      rw [← Spec.map_comp]; rfl
    rw [s]
    exact gs_specMap _ z r
  have d : trF (L := D.P.L) (K := PUnit) (fun _ => ptK (D.c mu)) (fun _ => -1) (jFK (R := V) (FractionRing V)) z
      (fun _ => J (jFK (R := V) (FractionRing V) ≫ ptK (D.c mu))) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1) (toUnit (TF (R := V) (FractionRing V))).left z
      (fun _ => J ((toUnit (TF (R := V) (FractionRing V))).left ≫ (D.c mu).left)) j :=
    congrArg (fun ψ => ∏ k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U (j k)) (D.P.L.g (J ψ) (j k)) ^ (-1 : ℤ)) q
  refine (congrArg Units.val a).trans ((Units.val_mul _ _).trans ((_root_.mul_comm _ _).trans ?_))
  exact congrArg₂ (· * ·) c (congrArg Units.val (d.trans b.symm))

end GlobalTheory.Poinc.PsiIntGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsUniformisedGroupPowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_sections_uniformisedGroup_power : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k m : ℕ}, 1 ≤ k → ∀ (b : Fin (m + 1) → H0 A.L k), ∃ (σ : Fin (m + 1) → H0 U.LG.L k) (c : Fin (m + 1) → (FractionRing R)ˣ), ∀ (y : ↥(pullback G.hom (jK R))) (j : Fin 1 → U.LG.L.ι) (jA : Fin 1 → A.L.ι), pullback.fst G.hom (jK R) y ∈ U.LG.L.U (j 0) → U.gen.hom.left y ∈ A.L.U (jA 0) → ∃ u : ((pullback G.hom (jK R)).presheaf.stalk y)ˣ, ∀ i, secGerm (pullback.fst G.hom (jK R)) y (σ i) j = u.val * gs (pullback.snd G.hom (jK R)) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i : FractionRing R)) * secGerm (show pullback G.hom (jK R) ⟶ A.A.left from U.gen.hom.left) y (b i) jA := by
  first | exact @GlobalTheory.Mum.sections_move_integral | exact GlobalTheory.Mum.sections_move_integral | (intros; apply GlobalTheory.Mum.sections_move_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaExpansionOfSectionPowerGeThre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SecExp

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_restrict' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε t φ ε s h 1 := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  refine ⟨DVR.pullSec L φ ε s h, fun j₁ j₂ hco => ?_⟩
  obtain rfl : j₁ = j₂ := funext fun k => hco (Sum.inl k) (Sum.inr k) rfl
  rw [resTop, map_one, _root_.one_mul]
  exact (DVR.rs_rs _ _ _).symm

theorem exists_intFam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ s : H0 U.LG.L k, ∃ f : IntFam (maximalIdeal R) D.toPre k, ∀ e : ℕ, U.ExpandsAt e k s f.f := by
  intro R _ _ _ hB D A G _ _ hG U k hk s
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have : IsNoetherianRing R := hR.1
  obtain ⟨sK, hsK⟩ := exists_restrict' U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
    (pullback.fst G.hom (jK R)) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (Category.comp_id _).symm) s
  obtain ⟨E, hE, -⟩ := (U.expand k (by omega)).1 sK
  obtain ⟨g, hg, hext⟩ := GlobalTheory.IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D A G U.toUnifPre k s sK hsK E hE
  have h1 : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by
    unfold scal; rw [map_one, map_one]
  refine ⟨⟨E, g, fun α => h1 ▸ hext α, fun e => ?_⟩, hg⟩
  obtain ⟨S, hS, -⟩ := hg e
  refine S.finite_toSet.subset fun α hα => by_contra fun h => hα fun j => ?_
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  apply ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj (U.gt e).q.left
  rw [map_zero]
  have h' := hS α h j
  have e' : (U.gt e).pG.left = (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := rfl
  rw [e', Scheme.Hom.comp_app] at h'
  exact h'

end GlobalTheory.Mum.SecExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantMapsAffineOpenSmoothModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_maps_affineOpen_smoothModel : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [Algebra R R'] (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → (∀ σ, spMap (actC σ : C' →+* C') ≫ j = j ≫ act σ) → ∀ W : Y.left.Opens, IsAffineOpen W → φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ j.opensRange → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), Algebra.Smooth R O ∧ (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) := by
  first | exact @GlobalTheory.Mum.exists_invariant_maps_of_affine_open | exact GlobalTheory.Mum.exists_invariant_maps_of_affine_open | (intros; apply GlobalTheory.Mum.exists_invariant_maps_of_affine_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGrpPullbackOfCompatibleRetracts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RetractPullback

theorem exists_isGrpPullback_of_retracts : ∀ {S S' B : Scheme.{0}} (j : S' ⟶ S) (f : S' ⟶ B) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (P : Over B) [GrpObj P] (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback G' P f ψ) (e : G ⟶ G) (e₀ : P ⟶ P) (e' : G' ⟶ G') (he' : IsMonHom e') (h₁ : e'.left ≫ φ = φ ≫ e.left) (h₂ : e'.left ≫ ψ = ψ ≫ e₀.left) (H : Over S) [GrpObj H] (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = e) (C : Over B) [GrpObj C] (k : C ⟶ P) (p : P ⟶ C) (hk : IsMonHom k) (hp : IsMonHom p) (hkp : k ≫ p = 𝟙 C) (hpk : p ≫ k = e₀), ∃ (C' : Over S') (_ : GrpObj C') (a : C'.left ⟶ H.left) (b : C'.left ⟶ C.left), IsGrpPullback C' H j a ∧ IsGrpPullback C' C f b := by
  intro S S' B j f G _ G' _ P _ φ ψ hφ hψ e e₀ e' he' h₁ h₂ H _ i r hi hr hir hri C _ k p hk hp hkp hpk
  have hb := isGrpPullback_pullback C f
  have wk : k.left ≫ P.hom = C.hom := Over.w k
  have wp : p.left ≫ C.hom = P.hom := Over.w p
  have wi : i.left ≫ G.hom = H.hom := Over.w i
  have wr : r.left ≫ H.hom = G.hom := Over.w r
  have we' : e'.left ≫ G'.hom = G'.hom := Over.w e'
  have kp : k.left ≫ p.left = 𝟙 _ := by rw [← Over.comp_left, hkp]; rfl
  have pk : p.left ≫ k.left = e₀.left := by rw [← Over.comp_left, hpk]
  have ir : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir]; rfl
  have ri : r.left ≫ i.left = e.left := by rw [← Over.comp_left, hri]
  have hmw : (pullback.fst C.hom f ≫ k.left) ≫ P.hom = pullback.snd C.hom f ≫ f := by
    rw [Category.assoc, wk]; exact pullback.condition
  let m : pullback C.hom f ⟶ G'.left := hψ.1.lift (pullback.fst C.hom f ≫ k.left) (pullback.snd C.hom f) hmw
  have mψ : m ≫ ψ = pullback.fst C.hom f ≫ k.left := hψ.1.lift_fst _ _ _
  have mh : m ≫ G'.hom = pullback.snd C.hom f := hψ.1.lift_snd _ _ _
  have fix : ∀ {T : Scheme.{0}} (x : T ⟶ pullback C.hom f), x ≫ m ≫ e'.left = x ≫ m := by
    intro T x
    apply hψ.1.hom_ext
    · simp only [Category.assoc, h₂, reassoc_of% mψ, mψ, ← pk, reassoc_of% kp]
    · simp only [Category.assoc, we']
  refine ⟨(Over.pullback f).obj C, inferInstance, m ≫ φ ≫ r.left, pullback.fst C.hom f, ⟨?_, ?_⟩, hb⟩
  · have comm : (m ≫ φ ≫ r.left) ≫ H.hom = pullback.snd C.hom f ≫ j := by
      rw [Category.assoc, Category.assoc, wr, hφ.1.w, reassoc_of% mh]
    refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm (fun s => pullback.lift
        (hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ ψ ≫ p.left) s.snd
        (by simp only [Category.assoc, wp, hψ.1.w, hφ.1.lift_snd_assoc])) ?_ ?_ ?_⟩⟩
    · intro s
      have hm : pullback.lift (hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ ψ ≫ p.left)
          s.snd (by simp only [Category.assoc, wp, hψ.1.w, hφ.1.lift_snd_assoc]) ≫ m =
          hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ e'.left := by
        apply hψ.1.hom_ext
        · simp only [Category.assoc, mψ, h₂, pullback.lift_fst_assoc, pk]
        · simp only [Category.assoc, mh, we', pullback.lift_snd, hφ.1.lift_snd]
      rw [reassoc_of% hm, reassoc_of% h₁, hφ.1.lift_fst_assoc, ← ri]
      simp only [Category.assoc, reassoc_of% ir, ir, Category.comp_id]
    · intro s
      exact pullback.lift_snd _ _ _
    · intro s n hn1 hn2
      have hx : n ≫ m = hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) := by
        apply hφ.1.hom_ext
        · rw [hφ.1.lift_fst, ← hn1]
          calc (n ≫ m) ≫ φ = n ≫ m ≫ e'.left ≫ φ := by rw [reassoc_of% (fix n), Category.assoc]
            _ = _ := by rw [h₁, ← ri]; simp only [Category.assoc]
        · rw [hφ.1.lift_snd, Category.assoc, mh]; exact hn2
      apply pullback.hom_ext
      · rw [pullback.lift_fst, ← reassoc_of% hx, reassoc_of% mψ, kp, Category.comp_id]
      · rw [pullback.lift_snd]; exact hn2
  · intro T x y x₀ y₀ hx hy
    let M : (Over.pullback f).obj C ⟶ G' := Over.homMk m mh
    have pt : ∀ z : T ⟶ (Over.pullback f).obj C, pushPt hψ.1.w (z ≫ M) = pushPt hb.1.w z ≫ k :=
      fun z => Over.OverMorphism.ext (by
        show (z.left ≫ m) ≫ ψ = (z.left ≫ pullback.fst C.hom f) ≫ k.left
        rw [Category.assoc, mψ, Category.assoc])
    have Mmul : (x * y) ≫ M = (x ≫ M) * (y ≫ M) := by
      apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have e1 := hb.2 T x y (pushPt hb.1.w x) (pushPt hb.1.w y) rfl rfl
        have e2 := hψ.2 T (x ≫ M) (y ≫ M) (pushPt hψ.1.w (x ≫ M)) (pushPt hψ.1.w (y ≫ M)) rfl rfl
        rw [← e2, pt, pt, ← MonObj.mul_comp]
        show ((x * y).left ≫ m) ≫ ψ = (pushPt hb.1.w x * pushPt hb.1.w y).left ≫ k.left
        rw [e1, Category.assoc, mψ, Category.assoc]
      · rw [Over.w ((x * y) ≫ M), Over.w ((x ≫ M) * (y ≫ M))]
    have ex : x₀ = pushPt hφ.1.w (x ≫ M) ≫ r := Over.OverMorphism.ext (by
      rw [hx]; show _ = ((x.left ≫ m) ≫ φ) ≫ r.left; simp only [Category.assoc])
    have ey : y₀ = pushPt hφ.1.w (y ≫ M) ≫ r := Over.OverMorphism.ext (by
      rw [hy]; show _ = ((y.left ≫ m) ≫ φ) ≫ r.left; simp only [Category.assoc])
    have e3 := hφ.2 T (x ≫ M) (y ≫ M) (pushPt hφ.1.w (x ≫ M)) (pushPt hφ.1.w (y ≫ M)) rfl rfl
    rw [ex, ey, ← MonObj.mul_comp, Over.comp_left, e3, ← Mmul]
    show ((x * y).left ≫ m) ≫ φ ≫ r.left = _
    simp only [Category.assoc]

end GlobalTheory.RetractPullback
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisedGroupsSameSiegelFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem exists_iso_of_overPt : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing R) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (a : G₁ ≅ G₂) (cA : A₁.A ≅ A₂.A), IsMonHom a.hom ∧ IsMonHom cA.hom ∧ Gen₀ U₁ U₂ a.hom cA.hom ∧ cA.hom.left ≫ α₂ = α₁ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left) := by
  intro X g n B _ ζ sX c R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hG₁ hG₂ y α₁ α₂ hO₁ hO₂
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  obtain ⟨hp₁, β₁, hsq₁, hL₁⟩ := hO₁
  obtain ⟨hp₂, β₂, hsq₂, hL₂⟩ := hO₂
  obtain ⟨cA, hcA, hcα⟩ := grpPullback_iso hp₁ hp₂
  haveI := U₁.gen_hom
  haveI := U₂.gen_hom
  haveI := hcA
  let e : (Over.pullback (jK R)).obj G₁ ≅ (Over.pullback (jK R)).obj G₂ := U₁.gen ≪≫ cA ≪≫ U₂.gen.symm
  haveI : IsMonHom e.hom := by
    show IsMonHom (U₁.gen.hom ≫ cA.hom ≫ U₂.gen.inv)
    infer_instance
  obtain ⟨a, ⟨ha, hae⟩, -⟩ :=
    GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing R) G₁ G₂ hG₁ hG₂ e
  refine ⟨a, cA, ha, hcA, ?_, hcα, ?_⟩
  · show (Over.pullback (jK R)).map a.hom ≫ U₂.gen.hom = U₁.gen.hom ≫ cA.hom
    rw [show (Over.pullback (jK R)).map a.hom = e.hom from hae]
    simp [e]
  · set β := (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left with hβdef
    have hβ : β ≫ β₂ = β₁ := by
      have h1 : (β ≫ β₂) ≫ (fst c.A c.A).left = β₁ ≫ (fst c.A c.A).left := by
        rw [Category.assoc, hsq₂.1, hsq₁.1, ← Category.assoc, hβdef, ← Over.comp_left, lift_fst, Over.comp_left,
          Category.assoc, hcα]
      have h2 : (β ≫ β₂) ≫ (snd c.A c.A).left = β₁ ≫ (snd c.A c.A).left := by
        rw [Category.assoc, hsq₂.2, hsq₁.2, ← Category.assoc, hβdef, ← Over.comp_left, lift_snd, Over.comp_left,
          Category.assoc, hcα]
      simp only [Over.fst_left, Over.snd_left] at h1 h2
      exact pullback.hom_ext h1 h2
    have iL₁ : (abelian₂ A₁.A A₁.L).IsLB := LB.isLB_linComb A₁.isLB _ _
    have iL₂ : ((abelian₂ A₂.A A₂.L).pull β).IsLB := pull_isLB (LB.isLB_linComb A₂.isLB _ _) _
    have iP₁ : (c.P.pull β₁).IsLB := pull_isLB c.isLB _
    have iP₂ : ((c.P.pull β₂).pull β).IsLB := pull_isLB (pull_isLB c.isLB _) _
    have h₃ : LBIso ((abelian₂ A₂.A A₂.L).pull β) ((c.P.pull β₂).pull β) :=
      LBIso.chartPull (chartPullPull _ β) (chartPullPull _ β) hL₂
    exact hL₁.trans iL₁ iP₁ iL₂ ((GlobalTheory.ClosedPol.lbIso_pull_comp c.isLB β₂ β β₁ hβ).trans iP₁ iP₂ iL₂ h₃.symm)

end GlobalTheory.TInj
end

