import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0009
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CrossEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpFun

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.ExpInt

theorem cross_eq {V : Type} [CommRing V] [IsDomain V] (G : Over (Spec (CommRingCat.of V))) [Flat G.hom]
    {L : LB G.left} (hL : L.IsLB) (k : ℕ) (σ σ' ρ ρ' : H0 L k)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)))) (r r' : V)
    (h : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r))
    (h' : GeneratorPullback.SecScal L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK V)) (scal (pullback.snd G.hom (jK V) ≫ jK V) r'))
    (hρ : SecIsMul G.hom r' ρ σ) (hρ' : SecIsMul G.hom r ρ' σ') : ρ = ρ' := by
  refine SecOps.sec_ext fun j => generic_app_injective G _ (fn_ext fun y hy => ?_)
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left)
    (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
  have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left) = j a := fun a => by
    rw [Subsingleton.elim a 0]; exact e ()
  have e₁ := secScal_sval h (𝟙 _) y hJ
  have e₂ := secScal_sval h' (𝟙 _) y hJ
  rw [sval_of σ _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₁
  rw [sval_of σ' _ y J j ej, gs_scal, ← pullback.condition, ← Category.assoc] at e₂
  refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) _ y _ hy _).symm)
  refine (secIsMul_gs hρ _ y j hy).trans (Eq.trans ?_ (secIsMul_gs hρ' _ y j hy).symm)
  exact (congrArg _ e₁).trans ((mul_left_comm _ _ _).trans (congrArg _ e₂).symm)

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E E' : Fam D.toPre (FractionRing V) k), U.Expands k s E → U.Expands k s E' → E = E' := by
  intro hB V _ _ _ D A G _ _ U k s E E' hE hE'
  obtain ⟨r, hr, σ, f, h, hf, hx⟩ := hE
  obtain ⟨r', hr', σ', f', h', hf', hx'⟩ := hE'
  have := U.smooth
  have : Flat G.hom := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_secIsMul (p := G.hom) r' σ
  obtain ⟨ρ', hρ'⟩ := exists_secIsMul (p := G.hom) r σ'
  choose g hg using fun α => exists_secIsMul (p := D.toPre.P.A.hom) r' (f α)
  choose g' hg' using fun α => exists_secIsMul (p := D.toPre.P.A.hom) r (f' α)
  obtain rfl : ρ = ρ' := cross_eq G U.LG.isLB k σ σ' ρ ρ' s r r' h h' hρ hρ'
  obtain rfl : g = g' := GlobalTheory.ExpUniq.main hB V D A G U k ρ g g'
    (fun e => expandsAt_secIsMul V _ D A G U e k _ σ ρ f g hρ hg (hx e))
    (fun e => expandsAt_secIsMul V _ D A G U e k _ σ' ρ f' g' hρ' hg' (hx' e))
  refine fam_ext fun α j => sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j
  have e₁ := secScal_sval (hf α) (𝟙 _) y hJ
  have e₁' := secScal_sval (hf' α) (𝟙 _) y hJ
  have e₂ : sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (f α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (hg α) _ y _ (hJ.mem _ _)
  have e₂' : sval (g α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J = _ *
      sval (f' α) (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y J :=
    secIsMul_gs (hg' α) _ y _ (hJ.mem _ _)
  rw [Category.assoc, Over.w] at e₂ e₂'
  rw [gs_scal] at e₁ e₁'
  rw [e₁] at e₂
  rw [e₁', e₂, mul_left_comm] at e₂'
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing V)).hom =
      ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) ≫ jK V := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e₃] at e₂'
  exact (IsUnit.mul_right_inj (isUnit_cst _ y hr')).1 ((IsUnit.mul_right_inj (isUnit_cst _ y hr)).1 e₂')

end GlobalTheory.ExpFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntOfVgeZero
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralSection

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem exists_eq_of_nonneg (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) {c : FractionRing V} (h : 0 ≤ v c) :
    ∃ b : V, c = algebraMap V (FractionRing V) b := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨n, u, hu⟩ := hasVal_of_ne_zero hϖ hc

  have hvc : v c = ((n : ℚ) : WithTop ℚ) := hv c n ⟨u, hu⟩
  have hn : (0 : ℤ) ≤ n := by
    rw [hvc] at h
    have h' : (0 : ℚ) ≤ (n : ℚ) := WithTop.coe_le_coe.mp h
    exact_mod_cast h'

  lift n to ℕ using hn
  refine ⟨ϖ ^ n * (u : V), ?_⟩
  rw [hu, map_mul, map_pow, zpow_natCast]

theorem exists_int_of_vge_zero (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)}
    {v : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) v) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    (hs : VGe D (FractionRing V) v k α s 0) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs

  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i =>
    exists_eq_of_nonneg hϖ hv (by simpa using ha i)
  choose b hb using hint

  refine ⟨FamInt.secLin (fun i => constFn D.toPre.P.A.hom ⊤ (b i)) σ, ?_⟩
  refine SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_
  rw [SectionScalarValuation.sval_lin _ σ (fun j => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF
      (fun j => (hsum j).trans (by simp only [constBF_eq]; rfl)) _ y hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SectionScalarValuation.secScal_sval (hσ i) (𝟙 _) y hJ]
  congr 1
  clear hsum hσ ha hJ
  rw [gs_constFn]
  · rw [hb i]

    have e1 := gs_pull (𝟙 _) (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) (b i)))
    rw [Category.id_comp] at e1
    have e1' : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) (b i))) =
        cst (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y (algebraMap V (FractionRing V) (b i)) := e1
    rw [e1', ← cst_comp, Category.id_comp]
    congr 1

    have h1 := Over.w (DegPre.prB D.toPre (FractionRing V))
    have h2 := Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)
    rw [h1]
    rw [← h2]
    congr 1

    unfold TF spMap
    change jFK _ ≫ jK V = _
    unfold jFK jK
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · trivial

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E → (∀ α, VGe D (FractionRing V) vK k α (E.s α) 0) → ∃ σ : H0 U.LG.L k, GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 := by
  intro V _ _ _ ϖ hϖ D vK hvK A G _ _ U k s E hE hvE
  obtain ⟨r, hr, σ, f, hσ, hf, hexp⟩ := hE
  have hg : ∀ α, ∃ g : D.toPre.SecB k α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α)
      (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1 :=
    fun α => exists_int_of_vge_zero hϖ hvK (hvE α)
  choose g hg using hg
  have hfg : ∀ α, SecIsMul D.toPre.P.A.hom r (f α) (g α) := fun α =>
    secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom (prB_app_injective D.toPre) (hg α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing V))]; exact hf α)
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ

  have hmul : ∀ α, ∃ g' : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ m) (f α) g' := by
    intro α
    obtain ⟨g', hg'⟩ := exists_secIsMul D.toPre.P.A.hom (u : V) (g α)
    obtain ⟨F', hF'⟩ := exists_secIsMul D.toPre.P.A.hom (ϖ ^ m) g'
    have hc := SecIsMul.comp hF' hg'
    have hF'f : F' = f α := SecOps.sec_ext fun j => by
      rw [hc j, hfg α j, hu, mul_comm (u : V)]
    exact ⟨g', hF'f ▸ hF'⟩
  choose g' hg' using hmul

  have hdiv : ∃ τ : H0 U.LG.L k, SecIsMul G.hom (ϖ ^ m) σ τ := by
    rcases m with _ | e
    · refine ⟨σ, fun j => ?_⟩
      simp [scal]
    · exact exists_div_of_expandsAt hϖ U e k σ g' f hg' (hexp e)
  obtain ⟨τ, hτ⟩ := hdiv

  obtain ⟨σ', hσ'⟩ := exists_secIsMul G.hom ((u⁻¹ : Vˣ) : V) τ
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have hlin : ∀ {a : V} {t t' : H0 U.LG.L k}, SecIsMul G.hom a t' t →
      sval t' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
        gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y ⊤ (scal G.hom a) * sval t (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J := by
    intro a t t' ht
    have hl := SectionScalarValuation.sval_lin (fun _ : Fin 1 => scal G.hom a) (fun _ => t)
      (fun j => by rw [Fin.sum_univ_one]; exact ht j) (𝟙 _ ≫ pullback.fst G.hom (jK V)) y hJ
    rwa [Fin.sum_univ_one] at hl
  have hgs : ∀ {X : Scheme.{0}} (r' : _ ⟶ X) (p : X ⟶ Spec (CommRingCat.of V)) (a : V),
      gs r' y ⊤ (scal p a) = cst (r' ≫ p) y a := fun r' p a => gs_pull r' p y ⊤ trivial _
  have hq : (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom = 𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V := by
    rw [Category.assoc, pullback.condition]
  have key := GlobalTheory.IntegralExpansion.sval_of_secScal hσ (𝟙 _) y hJ
  rw [hlin hτ, hgs, hgs, hq, hu, cst_mul] at key
  rw [hlin hσ', hgs, hq]

  have hunit : IsUnit (cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (ϖ ^ m)) := by
    have hK : algebraMap V (FractionRing V) (ϖ ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr (pow_ne_zero _ hϖ.ne_zero)
    rw [← Category.assoc]
    change IsUnit (cst (_ ≫ spMap (algebraMap V (FractionRing V))) y _)
    rw [cst_comp]
    have h1 := (cst_mul (𝟙 _ ≫ pullback.snd G.hom (jK V)) y (algebraMap V (FractionRing V) (ϖ ^ m))
      (algebraMap V (FractionRing V) (ϖ ^ m))⁻¹).symm.trans (by rw [mul_inv_cancel₀ hK, cst_one])
    exact ⟨⟨_, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩
  have hT : sval τ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (u : V) * sval s (𝟙 _) y J :=
    hunit.mul_left_cancel (by rw [key]; ring)
  rw [hT, ← _root_.mul_assoc, ← cst_mul, Units.inv_mul, cst_one, _root_.one_mul]

end GlobalTheory.IntegralSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralExpansionLocal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

theorem dvd_gs_of_dvd_sval {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {c : Z.presheaf.stalk z}
    (h : ∀ J, Good L z J → c ∣ sval s r z J) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) :
    c ∣ gs r z (LB.wchart L φ j) (s.f j) := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  rw [sec_trans s r z hj (hJ.mem φ r)]
  exact dvd_mul_of_dvd_right (h J hJ) _

theorem isUnit_cst_of_ne_zero {R : Type} [CommRing R] [IsDomain R] {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) {r : R} (hr : r ≠ 0) :
    IsUnit (cst (p ≫ jK R) z r) := by
  have hne : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have key : cst (p ≫ jK R) z r = cst p z (algebraMap R (FractionRing R) r) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp p (algebraMap R (FractionRing R)) z r
  rw [key]
  refine isUnit_iff_exists_inv.2 ⟨cst p z (algebraMap R (FractionRing R) r)⁻¹, ?_⟩
  rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, mul_inv_cancel₀ hne, ReciprocityTheory.ChartRestriction.G.H1.cst_one]

private theorem injective_app_pullback_fst_of_flat {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [Flat G.hom]
    (W : G.left.Opens) : Function.Injective ((pullback.fst G.hom (jK R)).app W).hom := by
  haveI : QuasiCompact (pullback.fst G.hom (jK R)) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (jK R) := by
    unfold jK
    exact SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap _ (IsFractionRing.injective R (FractionRing R))
  haveI : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) := inferInstance
  exact Scheme.Hom.app_injective _ W

private theorem isUnit_gs_scal_of_ne_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : (D.BF (FractionRing R)).left)
    {r : R} (hr : r ≠ 0) : IsUnit (gs (𝟙 _) y ⊤ (scal (D.BF (FractionRing R)).hom r)) := by
  unfold scal
  erw [gs_pull (𝟙 _) (D.BF (FractionRing R)).hom y ⊤ trivial, Category.id_comp]
  unfold DegPre.BF
  change IsUnit (cst (TF (FractionRing R) ⊗ D.P.A).hom y r)
  rw [← Over.w (fst (TF (FractionRing R)) D.P.A)]
  unfold TF
  simp only [Over.mk_hom]
  rw [← Category.assoc]
  exact isUnit_cst_of_ne_zero _ y hr

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R)) 1 → ∀ E : Fam D.toPre (FractionRing R) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  intro R _ _ _ _ I hI D A G _ _ U k σ s hs E hE
  obtain ⟨r, hr, σ', f, hσ', hf, hexp⟩ := hE
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hP : D.toPre.P.L.IsLB := D.toPre.P.isLB
  haveI : Smooth G.hom := U.smooth
  have hinj : ∀ W : G.left.Opens, Function.Injective ((pullback.fst G.hom (jK R)).app W).hom :=
    fun W => injective_app_pullback_fst_of_flat G W
  have hσ'' : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK R))
      (scal (pullback.fst G.hom (jK R) ≫ G.hom) r) := by
    rw [pullback.condition]
    exact hσ'
  have h2 : SecIsMul G.hom r σ' σ := GlobalTheory.IntegralExpansion.secIsMul_of_secScal hLG G.hom hinj hs hσ''
  have h3 := fun e => GlobalTheory.expandsAt_dvd_of_secIsMul R I D A G U e k r σ' σ f h2 (hexp e)
  haveI : Smooth D.toPre.P.A.hom := D.toPre.P.isAb.smooth
  haveI : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  have h4 : ∀ α, ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom r (f α) g := by
    intro α
    refine GlobalTheory.GermDiv.main R I (hI.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)
      D.toPre.P.A _ (linComb_isLB _ hP _ _) (f α) r hr ?_
    intro n x j hx
    exact dvd_gs_of_dvd_sval hP (f α) (fstG I n D.toPre.P.A).left x (fun J hJ => h3 n α x J hJ) j hx
  choose g hg using h4
  refine ⟨g, fun e => expandsAt_cancel_of_ne_zero R I D A G U k r hr σ σ' g f h2 hg hexp e, ?_⟩
  intro α
  have hga := hg α
  unfold SecIsMul at hga
  refine ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_of_sval hP (fun y J hJ => ?_)
  have e1 := GlobalTheory.IntegralExpansion.sval_of_secScal (hf α) (𝟙 _) y hJ
  have hm := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left)
  have e2 : sval (f α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y J =
      gs (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y ⊤ (scal D.toPre.P.A.hom r) *
        sval (g α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y J := by
    unfold sval
    erw [hga, gs_mul _ _ _ hm, gs_res _ _ le_top hm]
  rw [e2] at e1
  have e3 : gs (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y ⊤ (scal D.toPre.P.A.hom r) =
      gs (𝟙 _) y ⊤ (scal (D.toPre.BF (FractionRing R)).hom r) := by
    unfold scal
    rw [Category.id_comp]
    erw [gs_pull (D.toPre.prB (FractionRing R)).left D.toPre.P.A.hom y ⊤ trivial,
      gs_pull (𝟙 _) (D.toPre.BF (FractionRing R)).hom y ⊤ trivial, Category.id_comp, Over.w]
  rw [e3] at e1
  have hu : IsUnit (gs (𝟙 _) y ⊤ (scal (D.toPre.BF (FractionRing R)).hom r)) := isUnit_gs_scal_of_ne_zero D.toPre y hr
  exact hu.mul_left_cancel e1

end GlobalTheory.IntegralExpansionLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegralStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expansion_of_integral_section_is_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 → ∀ E : Fam D.toPre (FractionRing V) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  first | exact @GlobalTheory.ExpInt.main | exact GlobalTheory.ExpInt.main | (intros; apply GlobalTheory.ExpInt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedCrossIdentityGenericFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericCross

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gs_scal {V : Type} [CommRing V] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of V)) (z : Z)
    (c : V) : gs r z ⊤ (scal p c) = cst (r ≫ p) z c := by
  unfold scal cst
  exact gs_pull r p z ⊤ (by simp) _

theorem isUnit_cst {V : Type} [CommRing V] [IsDomain V] {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) {c : V} (hc : c ≠ 0) :
    IsUnit (cst (q ≫ jK V) z c) := by
  have hne : algebraMap V (FractionRing V) c ≠ 0 := fun h =>
    hc (IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero]))
  obtain ⟨u, hu⟩ := (IsUnit.mk0 _ hne).map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom
  have nat : ((jK V).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) c) :=
    (congrArg (fun g => g.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))).symm
  have h1 : cst (q ≫ jK V) z c = gs q z ⊤ (((jK V).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c)) :=
    (gs_pull q (jK V) z ⊤ (by simp) _).symm
  rw [h1, nat, ← hu, gs_unit q z ⊤ (by simp) u]
  exact Units.isUnit _

theorem endK_fst {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {G : Over (Spec (CommRingCat.of V))} (f : G ⟶ G) :
    endK f ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ f.left := by
  unfold endK
  exact pullback.lift_fst _ _ _

theorem endK_snd {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {G : Over (Spec (CommRingCat.of V))} (f : G ⟶ G) :
    endK f ≫ pullback.snd G.hom (jK V) = pullback.snd G.hom (jK V) := by
  unfold endK
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem main : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k₁ : ℕ) (s₁ : P.U.SecK k₁) (F₁ : Fam P.D.toPre (FractionRing V) k₁) (u₁ : P.U.SecK (k₁ * N)) (F₁' : Fam P.D.toPre (FractionRing V) (k₁ * N)), P.U.Expands k₁ s₁ F₁ → P.U.Expands (k₁ * N) u₁ F₁' → PullAl P.D (FractionRing V) P.oD a k₁ N F₁ F₁' → ∀ (k₂ : ℕ) (s₂ : P.U.SecK k₂) (F₂ : Fam P.D.toPre (FractionRing V) k₂) (u₂ : P.U.SecK (k₂ * N)) (F₂' : Fam P.D.toPre (FractionRing V) (k₂ * N)), P.U.Expands k₂ s₂ F₂ → P.U.Expands (k₂ * N) u₂ F₂' → PullAl P.D (FractionRing V) P.oD a k₂ N F₂ F₂' → ∀ m₁ m₂ : ℕ, m₁ * k₁ = m₂ * k₂ → ∀ (y : (pullback t.G.hom (jK V) : Scheme.{0})) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u₁ (𝟙 _) y J ^ m₁ * Geo.Tor.sval s₂ (endK (t.act.act a)) y J ^ m₂ = Geo.Tor.sval u₂ (𝟙 _) y J ^ m₂ * Geo.Tor.sval s₁ (endK (t.act.act a)) y J ^ m₁ := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0 k₁ s₁ F₁ u₁ F₁' he₁ he₁' hp₁ k₂ s₂ F₂ u₂ F₂' he₂ he₂' hp₂
    m₁ m₂ hm y J hJ
  let _ : StarRing (NumberField.RingOfIntegers E) := H.starRing
  obtain ⟨uΨ, huΨ, -⟩ := P.w0
  obtain ⟨X, hX, hXc⟩ := exists_XB (D := P.D) (hL := P.D.toPre.P.isLB) (oa := P.oD) (w0 := H.w0) (uΨ := uΨ)
    (huΨ := huΨ) (a := a) (N := N) (hN := hN) (hN1 := by omega) (k := 1)
  obtain ⟨c₁, σ₁, τ₁, hc₁, hτ₁, hσ₁, ht₁⟩ := GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc
    k₁ s₁ F₁ u₁ F₁' he₁ he₁' hp₁
  obtain ⟨c₂, σ₂, τ₂, hc₂, hτ₂, hσ₂, ht₂⟩ := GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc
    k₂ s₂ F₂ u₂ F₂' he₂ he₂' hp₂
  have hx := GlobalTheory.MixedCross.main hL.lemmaB V E H t P a N hN hN0 X k₁ k₂ m₁ m₂ hm σ₁ τ₁ σ₂ τ₂ ht₁ ht₂ _
    (pullback.fst t.G.hom (jK V)) y J hJ
  have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hσ₁ (𝟙 _) y hJ
  have e₂ := GlobalTheory.PullIntegral.sval_of_secScal hσ₂ (𝟙 _) y hJ
  have f₁ := GlobalTheory.PullIntegral.sval_of_secScal hτ₁ (endK (t.act.act a)) y hJ
  have f₂ := GlobalTheory.PullIntegral.sval_of_secScal hτ₂ (endK (t.act.act a)) y hJ
  rw [gs_scal, Category.id_comp, Category.id_comp] at e₁ e₂
  rw [gs_scal, endK_fst, ← Category.assoc, endK_snd] at f₁ f₂
  rw [e₁, e₂, f₁, f₂] at hx
  have hu : IsUnit (cst (pullback.snd t.G.hom (jK V) ≫ jK V) y c₁ ^ m₁ *
      cst (pullback.snd t.G.hom (jK V) ≫ jK V) y c₂ ^ m₂) :=
    ((isUnit_cst _ y hc₁).pow m₁).mul ((isUnit_cst _ y hc₂).pow m₂)
  apply hu.mul_left_cancel
  linear_combination hx

end GlobalTheory.GenericCross
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.uniformisation_power_without_expansion : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G), ∃ (U' : UnifPre I D' A' G') (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) := by
  first | exact @GlobalTheory.PowUnif.main | exact GlobalTheory.PowUnif.main | (intros; apply GlobalTheory.PowUnif.main <;> assumption)
end

