import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HrelPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionMultiplicationPullbackTraitDegreeOne
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.MulExpand

open ReciprocityTheory.ChartRestriction.G.DVR (mulGen_isGen pullGen_isGen powGen_isGen val_pow cP comp_cP)
open GlobalTheory.UT

section
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}

abbrev prj (hD : IsPullDeg φ D D') : D'.P.A.left ⟶ D.P.A.left := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)

def om (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι) (q : Z ⟶ D'.P.A.left) : (Z.presheaf.stalk z)ˣ :=
  gw hD.w q z (J (q ≫ prj hD)) (J' q)

theorem pullB_val {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x}
    (H : PullB hD x b b') {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    sval b (r ≫ prj hD) z J = (∏ κ, om hD z J J' (r ≫ D'.famφB x κ) ^ DegPre.famε k κ).val * sval b' r z J' := by
  rw [sval_of b (r ≫ prj hD) z J (fun κ => J ((r ≫ D'.famφB x κ) ≫ prj hD)) (fun κ => by
    rw [Category.assoc r (prj hD), Category.assoc r _ (prj hD), ExpGTrans.famφB_pull hD x κ])]
  exact H Z r z _ _ (fun κ => hJ ((r ≫ D'.famφB x κ) ≫ prj hD)) (fun κ => hJ' (r ≫ D'.famφB x κ))

theorem prod_fam_unit (D : DegPre R) (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : (Sp R ⟶ D.P.A.left) → U) :
    ∏ κ, h (eSec D.P.A ≫ D.famφB α κ) ^ DegPre.famε k κ = h (eSec D.P.A) ^ (k : ℤ) := by
  have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by rw [Hom.one_def]; simp
  have a₀ : eSec D.P.A ≫ D.famφB α 0 = eSec D.P.A := Category.comp_id _
  have a₁ : eSec D.P.A ≫ D.famφB α 1 = eSec D.P.A ≫ D.famφB α 2 := congrArg (fun z => z.left)
    ((MonObj.comp_mul η[D.P.A] (𝟙 _) (cP D _ α)).trans
      ((congrArg (· * _) ((Category.comp_id _).trans e₁.symm)).trans (_root_.one_mul _)))
  have a₃ : eSec D.P.A ≫ D.famφB α 3 = eSec D.P.A := PullExp.eSec_comp_one
  rw [Fin.prod_univ_four, a₀, a₁, a₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, DegPre.famε, Matrix.cons_val]
  module

theorem mul_val_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') (m k k' : ℕ) (hk : k ≤ k') (x x' : D'.X) (hx : x' = m • x)
    (a : D'.P.A ⟶ D'.P.A) (ha : a = 𝟙 D'.P.A ^ m) (b : D.SecB k (hD.xe x)) (g : ∀ χ, D.SecB k' χ)
    (hM : MulSecB D m (hD.xe x) b (g (m • hD.xe x))) (b' : D'.SecB k x) (hb : PullB hD x b b')
    (c' : D'.SecB k' x') (hc : PullB hD x' (g (hD.xe x')) c')
    (eB : LB.Gen (LB.LinComb D'.P.L (Sum.elim (D'.famφB x') (fun i => a.left ≫ D'.famφB x i))
        (Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)))) (heB : eB.IsGen)
    (hn : ∀ y J, Good D'.P.L y J → val eB (eSec D'.P.A) y J = rigV D' (𝟙 _) y J ^ ((k' : ℤ) - k))
    (y : D'.P.A.left) (J') (hJ' : Good D'.P.L y J') :
    sval c' (𝟙 _) y J' = sval b' (𝟙 _ ≫ a.left) y J' * (val eB (𝟙 _) y J').val := by
  subst hx ha
  obtain ⟨u, hu, hun, hrel⟩ := hM
  have gp := pull_grp hD
  have hm : (mulA D'.P.A m).left ≫ prj hD = prj hD ≫ (mulA D.P.A m).left := GlobalTheory.ZH.TorsFrame.mulA_comm gp m
  have hφ : ∀ i, mulφB D' m x i ≫ prj hD = prj hD ≫ mulφB D m (hD.xe x) i := by
    rintro (i | i)
    · have := ExpGTrans.famφB_pull hD (m • x) i
      rw [map_nsmul] at this
      exact this
    · show ((mulA D'.P.A m).left ≫ D'.famφB x i) ≫ prj hD = prj hD ≫ (mulA D.P.A m).left ≫ D.famφB (hD.xe x) i
      rw [Category.assoc, ExpGTrans.famφB_pull hD x i, ← Category.assoc, hm, Category.assoc]
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (φ' := mulφB D' m x)
    (ε := mulεB k k') eB heB
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ i, om hD z J J' (r ≫ mulφB D' m x i) ^ mulεB k k' i) * val eB r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [om, Category.assoc]
  have hr : PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
    (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (prj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
  have he : eSec D'.P.A ≫ prj hD = spMap φ ≫ eSec D.P.A := hD.he
  have hem : eSec D'.P.A ≫ (mulA D'.P.A m).left = eSec D'.P.A := by
    have e₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = η[D'.P.A] := by rw [Hom.one_def]; simp
    refine (GlobalTheory.ZH.TorsFrame.comp_mulA η[D'.P.A] m).trans ?_
    rw [← e₁, one_pow, e₁]; rfl
  have key := gen_unique' D.P.isLB (φ := fun i => prj hD ≫ mulφB D m (hD.xe x) i) (ε := mulεB k k')
    (fun V _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ mulεB k k' i) (hφ i))
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 (pullGen_isGen _ _ _ _ hu (prj hD)) ht (fun y I hI => by
      choose I' hI' using fun χ : Sp R' ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have hI' : Good D'.P.L y I' := hI'
      have p : (∏ i, om hD y I I' (eSec D'.P.A ≫ mulφB D' m x i) ^ mulεB k k' i) =
          om hD y I I' (eSec D'.P.A) ^ ((k' : ℤ) - k) := by
        rw [Fintype.prod_sum_type]
        simp only [mulφB, mulεB, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, hem, zpow_neg, Finset.prod_inv_distrib]
        rw [prod_fam_unit D' _ _ (om hD y I I'), prod_fam_unit D' _ _ (om hD y I I'), zpow_sub]
      have q : rigV D (spMap φ) y I = om hD y I I' (eSec D'.P.A) * rigV D' (𝟙 _) y I' := by
        have := hr _ (𝟙 _) y (fun _ => I (eSec D'.P.A ≫ prj hD)) (fun _ => I' (eSec D'.P.A))
          (fun _ => hI (eSec D'.P.A ≫ prj hD)) (fun _ => hI' (eSec D'.P.A))
        rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at this
        rw [rigV, rigV, val_of (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig _ y I (fun _ => I (eSec D'.P.A ≫ prj hD)) (fun _ => by rw [he]),
          val_of (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig _ y I' (fun _ => I' (eSec D'.P.A)) (fun _ => by rw [Category.id_comp])]
        exact this
      have s := val_corr hI hun (spMap φ)
      rw [val_pull hI, val_pow] at s
      rw [val_pull hI, hv' _ _ y I I' hI hI', p, hn y I' hI', ← mul_zpow, ← q, he, s,
        show ((k' : ℤ) - k) = ((k' - k : ℕ) : ℤ) by omega, zpow_natCast]
      rfl)
  choose J hJ using fun χ : D'.P.A.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ
  have k₁ := (val_pull hJ u (prj hD) (𝟙 _)).symm.trans ((key _ (𝟙 _) y J hJ).trans (hv' _ _ y J J' hJ hJ'))
  have k₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 hrel _ (𝟙 _ ≫ prj hD) y J hJ
  have k₃ := pullB_val hc (𝟙 _) y hJ hJ'
  have k₄ := pullB_val hb (𝟙 _ ≫ (mulA D'.P.A m).left) y hJ hJ'
  have k₅ : sval (g (hD.xe (m • x))) (𝟙 _ ≫ prj hD) y J = sval (g (m • hD.xe x)) (𝟙 _ ≫ prj hD) y J :=
    congrArg (fun χ => sval (g χ) (𝟙 _ ≫ prj hD) y J) (map_nsmul hD.xe m x)
  rw [Category.assoc (𝟙 _) (prj hD), ← hm, ← Category.assoc (𝟙 _) _ (prj hD), k₄, k₁, ← k₅, k₃, Fintype.prod_sum_type] at k₂
  simp only [mulφB, mulεB, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, zpow_neg, Finset.prod_inv_distrib] at k₂
  refine (Units.mul_right_inj _).1 (k₂.trans ?_)
  generalize (∏ κ, om hD y J J' (𝟙 _ ≫ D'.famφB (m • x) κ) ^ DegPre.famε k' κ) = P
  generalize (∏ κ, om hD y J J' ((𝟙 _ ≫ (mulA D'.P.A m).left) ≫ D'.famφB x κ) ^ DegPre.famε k κ) = Q
  rw [Units.val_mul, Units.val_mul]
  linear_combination (P.val * sval b' (𝟙 _ ≫ (mulA D'.P.A m).left) y J' * (val eB (𝟙 _) y J').val) * Q.mul_inv

end

theorem expand : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ), Odd m →
    ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G →
    ∀ (σ' : H0 T.U.LG.L 1) (f' : ∀ x, T.D'.toPre.SecB 1 x), (∀ x, PullB T.hD x (F₁.f (T.hD.xe x)) (f' x)) →
    (∀ e, T.U.ExpandsAt e 1 σ' f') →
    ∀ (f'' : ∀ x, T.D'.toPre.SecB (m ^ 2) x), (∀ x, PullB T.hD x (G.f (T.hD.xe x)) (f'' x)) →
    ∃ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (σ'' : H0 T.U.LG.L (m ^ 2)), uG.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
        sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) ∧
      ∀ e, T.U.ExpandsAt e (m ^ 2) σ'' f'' := by
  intro R _ _ _ _ D C W _ _ _ T m hm F₁ G hFG σ' f' hf' hσ' f'' hf''
  obtain ⟨hd, hV, hz⟩ := T.cdvr
  have hL := GlobalTheory.firstFiveLaws
  have hI : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have hGF := hL.1.globalFns
  have hG : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨E, hEG, -, hEB, hEh, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL W (maximalIdeal W) hI T.D' T.A T.G hG T.U).1 m
  have := E.homG
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hsm : Function.Injective fun χ : T.D'.toPre.X => m • χ := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
    exact smul_right_injective T.D'.toPre.X (Int.natCast_ne_zero.2 hm0) h'
  have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
  obtain ⟨β₀, hβ₀⟩ := ThetaSum.exists_gen_pow T.U.LG T.U.cubG T.U.symG T.U.symG_gen m E.aG hEG
  obtain ⟨β, hβ, hβ'⟩ := PullExp.exists_normalised T.U.LG.isLB E.aG _ _ β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL W (maximalIdeal W) hI T.D' T.A T.G hG T.U E (m ^ 2) 1 β hβ hβ'
  obtain ⟨σ₃, f₃, p₁, p₂, p₃, p₄⟩ := GlobalTheory.T.pullback_section_endomorphism_expansion W (maximalIdeal W) T.D' T.A T.G T.U.toUnifPre E hinj (m ^ 2) 1 β hβ κ₀
    hκ₀.1 hrel σ' f' hσ'
  have hf : f₃ = f'' := funext fun b => ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext (sec_ext_val T.D'.toPre.P.isLB fun y J hJ => by
    by_cases hb : b ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      obtain ⟨eB, heB, hvB⟩ := NsmulPull.gen_shape T.D'.toPre E.aB (m ^ 2) 1 hm2 (E.h χ) χ κ₀ hκ₀.1 (E.u χ) (E.u_norm χ).1
      have h := mul_val_pull hGF T.hD m 1 (m ^ 2) hm2 χ (E.h χ) (hEh χ) E.aB hEB _ G.f (hFG.1 _) _ (hf' χ) _ (hf'' _) eB heB
        (fun y J hJ => by
          have a := val_corr hJ hκ₀.2 (𝟙 _)
          have a' := val_corr hJ (E.u_norm χ).2 (𝟙 _)
          rw [val_pull hJ, Category.id_comp, val_one] at a a'
          rw [hvB _ _ y J hJ, a, a', _root_.one_mul, _root_.mul_one]
          exact congrArg (fun q => rigV T.D'.toPre q y J ^ _) (Over.w η[T.D'.toPre.P.A])) y J hJ
      rw [h, hvB _ _ y J hJ]
      exact p₃ χ _ _ y J hJ
    · choose J₀ hJ₀ using fun χ : T.D'.toPre.P.A.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
      have h := pullB_val (hf'' b) (𝟙 _) y hJ₀ hJ
      rw [GlobalTheory.PullComp.sval_eq_zero _ (hFG.2 _ fun χ e => hb ⟨T.hD.xe.symm χ, by
        rw [hEh, ← map_nsmul, ← e, AddEquiv.symm_apply_apply]⟩)] at h
      rw [GlobalTheory.PullComp.sval_eq_zero _ (p₄ b hb), (Units.mul_right_eq_zero _).1 h.symm])
  subst hf
  let ρ := LB.pullGen T.U.LG.L (K := PUnit) (fun _ => eSec T.G) (fun _ => 1) T.U.LG.rig T.G.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ T.U.LG.rigGen _
  obtain ⟨uG, huG, hv⟩ := exists_gen T.U.LG.isLB (K' := Fin 2) (φ' := ![𝟙 T.G.left, (mulA T.G m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]) (fun U _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_three, Fintype.prod_unique]
      show h (𝟙 _) ^ ((m ^ 2 : ℕ) : ℤ) * h E.aG.left ^ (-((1 : ℕ) : ℤ)) * h (1 : T.G ⟶ T.G).left ^ (((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)) *
        h (T.G.hom ≫ eSec T.G) ^ (((m ^ 2 - 1 : ℕ) : ℤ) * 1) = h (𝟙 _) ^ ((m ^ 2 : ℕ) : ℤ) * h (mulA T.G m).left ^ (-((1 : ℕ) : ℤ))
      rw [hEG, GlobalTheory.ZH.TorsFrame.one_left, _root_.mul_assoc, ← zpow_add, Nat.cast_sub hm2]
      simp)
    (LB.mulGen _ _ _ _ _ β (GeneratorPullback.powGen _ _ _ ρ (m ^ 2 - 1))) (mulGen_isGen _ _ _ _ _ _ _ hβ (powGen_isGen _ _ _ _ hρ _))
  refine ⟨uG, σ₃, huG, fun Z r z J hJ => ?_, p₁⟩
  rw [p₂ Z r z J hJ, hv _ _ z J hJ, val_mul hJ, val_pow, val_pull hJ, Category.comp_id, mul_comm,
    show r ≫ E.aG.left = r ≫ (mulA T.G m).left by rw [hEG],
    show (((m ^ 2 : ℕ) : ℤ) - (1 : ℕ)) = ((m ^ 2 - 1 : ℕ) : ℤ) by omega, zpow_natCast]

end GlobalTheory.Mum.MulExpand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.eq_comp_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) {F : Type} [Field F]
    (ψ : FractionRing R →+* F) (x : Sp F ⟶ M.S) (hx : x ≫ M.π = spMap ψ ≫ jK R) : x = spMap ψ ≫ M.gp := by
  have := M.integral
  have hd := M.dominant
  let pt : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  obtain ⟨B, e₀, hoi, P, hP⟩ : ∃ (B : CommRingCat) (e₀ : Spec B ⟶ M.S), IsOpenImmersion e₀ ∧ ∃ P, e₀ P = x pt :=
    ⟨_, M.S.affineCover.f (M.S.affineCover.idx (x pt)), M.S.affineCover.map_prop _, M.S.affineCover.covers (x pt)⟩
  have hsub : Set.range M.gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  have hsub' : Set.range x ⊆ Set.range e₀ := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y pt]
    exact ⟨P, hP⟩
  obtain ⟨g', hfac⟩ : ∃ g', g' ≫ e₀ = M.gp := ⟨_, IsOpenImmersion.lift_fac e₀ M.gp hsub⟩
  obtain ⟨x', hfx⟩ : ∃ x', x' ≫ e₀ = x := ⟨_, IsOpenImmersion.lift_fac e₀ x hsub'⟩
  obtain ⟨g, rfl⟩ := Spec.map_surjective g'
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective x'
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (e₀ ≫ M.π)
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfac, M.gp_π]
  have hcomp₁ : ρ ≫ g₁ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfx, hx, Spec.map_comp]
  have hc : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => congrArg (fun f => f.hom r) hcomp
  have hc₁ : ∀ r, g₁.hom (ρ.hom r) = ψ (algebraMap R (FractionRing R) r) := fun r => congrArg (fun f => f.hom r) hcomp₁
  have hden : DenseRange (Spec.map g) := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ Spec.map g) = M.gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hinj : Function.Injective g.hom := by
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 hden
    have hr := (affine_isReduced_iff _).1 (isReduced_of_isOpenImmersion e₀)
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have key : g₁ = g ≫ CommRingCat.ofHom ψ := by
    ext b
    show g₁.hom b = ψ (g.hom b)
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom b)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * b = ρ.hom a := hinj (by rw [map_mul, hc, hc, ← hxs, mul_div_cancel₀ _ hs0])
    have h1 := congrArg g₁.hom h0
    rw [map_mul, hc₁, hc₁] at h1
    rw [← hxs, map_div₀, ← h1, mul_div_cancel_left₀ _ ((map_ne_zero ψ).2 hs0)]
  rw [← hfx, ← hfac, key, Spec.map_comp, Category.assoc]

theorem PullB.unique {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b₁ b₂ : D'.SecB k x} (H₁ : PullB hD x b b₁) (H₂ : PullB hD x b b₂) : b₁ = b₂ := by
  refine DVR.SecOps.sec_ext fun q => fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.famφB x κ y))
  have e₁ := H₁ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  have e₂ := H₂ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem PullB.eq_zero {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X}
    {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x} (H : PullB hD x b b') (h : ∀ q, b'.f q = 0) (p) : b.f p = 0 := by
  have : IsDominant (specOf φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hφ]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (specOf φ)
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsSchemeTheoreticallyDominant (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (pull_grp hD).1.flip
  have : QuasiCompact (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (pull_grp hD).1.flip inferInstance
  apply (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)).app_injective
  rw [map_zero]
  refine fn_ext fun y hy => ?_
  choose q hq using fun κ => exists_chart D'.P.isLB (D'.famφB x κ y)
  have e := H _ (𝟙 _) y p q (fun κ => by
    have a := Set.mem_iInter.1 hy κ
    exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) (ExpGTrans.famφB_pull hD x κ)).mpr a) hq
  have e' := e.trans ((congrArg _ ((congrArg (gs _ y _) (h q)).trans (DVR.hr_gs_zero _ _ _))).trans (mul_zero _))
  exact (gs_pull _ _ y _ hy _).trans (e'.trans (DVR.hr_gs_zero _ _ _).symm)

theorem expands_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) :
    U.Expands k DVR.SecOps.secZero 0 := by
  refine ⟨1, one_ne_zero, DVR.SecOps.secZero, fun _ => DVR.SecOps.secZero, fun j₁ j₂ _ => ?_, fun α j₁ j₂ _ => ?_,
    fun e => ⟨∅, fun α _ j => map_zero _, fun p j₁ jf jt _ _ => ?_⟩⟩
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (mul_zero _)).trans (Finset.sum_empty).symm

theorem IntFam.f_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {k : ℕ} (F : IntFam I D k)
    (h : F.F = 0) (x : D.X) (q) : (F.f x).f q = 0 := by
  have h₀ : GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) x) (DegPre.famε k) (F.F.s x)
      (D.famφB x) (DegPre.famε k) DVR.SecOps.secZero (DegPre.prB D (FractionRing R)).left 1 := by
    rw [h]
    intro j₁ j₂ _
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  exact (IntegralExpansion.secIsMul_of_secScal D.P.isLB D.P.A.hom (a := 1) (IntegralExpansion.prB_app_injective D) h₀
    (by rw [Over.w (DegPre.prB D (FractionRing R))]; exact F.ext x) q).trans (mul_zero _)

theorem IntFam.eq_zero_of_two_scalars {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k)
    (F : IntFam I D.toPre k) {σ₁ σ₂ : H0 U.LG.L k} (e₁ : ∀ e, U.ExpandsAt e k σ₁ F.f) (e₂ : ∀ e, U.ExpandsAt e k σ₂ F.f)
    {b b' : W} (hb : b ≠ b') (H : ∀ y J, Good U.LG.L y J → ∃ u : ((pullback G.hom (jK W)).presheaf.stalk y)ˣ,
      gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) * u.val * sval σ₁ (pullback.fst G.hom (jK W)) y J =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') * u.val * sval σ₂ (pullback.fst G.hom (jK W)) y J) :
    F.F = 0 := by
  have res : ∀ σ : H0 U.LG.L k, (∀ e, U.ExpandsAt e k σ F.f) → ∃ s : U.SecK k, U.Expands k s F.F ∧
      ∀ y J, Good U.LG.L y J → sval σ (pullback.fst G.hom (jK W)) y J = sval s (𝟙 _) y J := fun σ e => by
    obtain ⟨s, hs⟩ := UnifBaseChange.exists_secScal_one U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (pullback.fst G.hom (jK W)) (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm) σ
    refine ⟨s, ⟨1, one_ne_zero, σ, F.f, ?_, F.ext, e⟩, fun y J hJ => ?_⟩
    · rw [UnifBaseChange.scal_one]; exact hs
    · have v := DVR.hr_secScal_sval hs (𝟙 _) y hJ
      rwa [Category.id_comp, gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at v
  obtain ⟨s₁, x₁, v₁⟩ := res σ₁ e₁
  obtain ⟨s₂, x₂, v₂⟩ := res σ₂ e₂
  obtain rfl : s₁ = s₂ := ((U.expand k hk).2 F.F).unique x₁ x₂
  have hz : s₁ = DVR.SecOps.secZero := by
    refine DVR.SecOps.sec_ext (sec_ext_val U.LG.isLB fun y J hJ => ?_)
    obtain ⟨u, e⟩ := H y J hJ
    rw [v₁ y J hJ, v₂ y J hJ, ← sub_eq_zero, ← sub_mul, ← sub_mul] at e
    have hu : IsUnit (gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b'))) := by
      rw [GenericCross.gs_scal, pullback.condition]
      exact GenericCross.isUnit_cst _ y (sub_ne_zero.2 hb)
    have hs : gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b')) =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) - gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') := by
      simp only [gs_eq _ y ⊤ trivial, scal, map_sub]
    rw [hs] at hu
    exact ((hu.mul u.isUnit).mul_right_eq_zero.1 e).trans (DVR.hr_gs_zero _ _ _).symm
  rw [hz] at x₁
  exact ((U.expand k hk).1 _).unique x₁ (expands_zero U.toUnifPre k)

theorem exists_fractionRing_square {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W) (h : Function.Injective φ) :
    ∃ ψ : FractionRing R →+* FractionRing W, jK W ≫ spMap φ = spMap ψ ≫ jK R := by
  have hi : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp h
  have h₀ : (algebraMap W (FractionRing W)).comp φ = (IsFractionRing.lift hi).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => by rw [RingHom.comp_apply (IsFractionRing.lift hi), IsFractionRing.lift_algebraMap]
  refine ⟨IsFractionRing.lift hi, ?_⟩
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← h₀]

theorem Trait.exists_generic_map {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    ∃ p' : pullback T.G.hom (jK W) ⟶ C.A.A.left, pullback.fst T.G.hom (jK W) ≫ T.β = p' ≫ C.α := by
  obtain ⟨ψ, h₀⟩ := exists_fractionRing_square T.φ T.inj
  have hψ : jK W ≫ T.ξ = spMap ψ ≫ C.gp := C.toModif.eq_comp_gp ψ _ (by rw [Category.assoc, T.ξ_π, h₀])
  have w₁ : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
  have w₂ : pullback.fst T.G.hom (jK W) ≫ T.G.hom = pullback.snd T.G.hom (jK W) ≫ jK W := pullback.condition
  have w₃ : (pullback.fst T.G.hom (jK W) ≫ T.β) ≫ C.G.hom = (pullback.snd T.G.hom (jK W) ≫ spMap ψ) ≫ C.gp := by
    rw [Category.assoc, w₁, reassoc_of% w₂, hψ, Category.assoc]
  have hp : IsPullback C.α C.A.A.hom C.G.hom C.gp := C.α_cart.1
  exact ⟨hp.lift _ _ w₃, (hp.lift_fst _ _ w₃).symm⟩

theorem Trait.exp_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∃ α j, (F.f α).f j ≠ 0) → ∀ a b b' : W, a ≠ 0 → T.Exp a b s F → T.Exp a b' s F → b = b' := by
  intro R _ _ _ hR D C W _ _ _ T k hk s F hF a b b' _ h₁ h₂
  obtain ⟨α, j, hne⟩ := hF
  obtain ⟨σ₁, ⟨σ₁', f₁, c₁, p₁, e₁⟩, g₁⟩ := h₁
  obtain ⟨σ₂, ⟨σ₂', f₂, c₂, p₂, e₂⟩, g₂⟩ := h₂
  by_contra hb
  apply hne
  obtain ⟨F', hF'⟩ := exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F
  rw [show f₁ = F'.f from funext fun x => (p₁ x).unique (hF' x)] at e₁
  rw [show f₂ = F'.f from funext fun x => (p₂ x).unique (hF' x)] at e₂
  obtain ⟨p', hp'⟩ := T.exists_generic_map
  have h₀ : F'.F = 0 := F'.eq_zero_of_two_scalars T.U hk e₁ e₂ hb fun y J' hJ' => by
    choose J hJ using fun χ : pullback T.G.hom (jK W) ⟶ C.G.left => exists_chart C.P.L.isLB (χ y)
    exact ⟨_, (c₁ _ _ y J J' hJ hJ').symm.trans ((g₁ _ _ p' hp' y J hJ).trans
      ((g₂ _ _ p' hp' y J hJ).symm.trans (c₂ _ _ y J J' hJ hJ')))⟩
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  exact (hF' x).eq_zero T.inj (F'.f_eq_zero h₀ x) j

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorizationThroughFiniteModification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finite_modif_eq_gp : ∀ (R : Type) [CommRing R] [IsDomain R] (M M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h →
    M'.gp ≫ h = M.gp → ∀ (Z : Scheme.{0}) (a : Z ⟶ M'.S) (c : Z ⟶ Sp (FractionRing R)), a ≫ h = c ≫ M.gp →
    a = c ≫ M'.gp := by
  intro R _ _ M M' h hh e Z a c hac
  haveI := M'.integral
  have cA : ∀ {X Y W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ W) (x : Γ(W, ⊤)),
      (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  have hsub : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  let pt : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.S) (U := ⊤) (x := M.gp pt) trivial
  have hgU : ∀ y : Sp (FractionRing R), M.gp y ∈ U := fun y => by rwa [Subsingleton.elim y pt]
  have hV : IsAffineOpen (h ⁻¹ᵁ U) := hU.preimage h
  have ha : Set.range a ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (a z) ∈ U
    rw [← Scheme.Hom.comp_apply, hac, Scheme.Hom.comp_apply]; exact hgU _
  have hg : Set.range M'.gp ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (M'.gp z) ∈ U
    rw [← Scheme.Hom.comp_apply, e]; exact hgU _
  obtain ⟨a₀, fa⟩ : ∃ a₀, a₀ ≫ (h ⁻¹ᵁ U).ι = a := ⟨_, IsOpenImmersion.lift_fac _ _ ha⟩
  obtain ⟨g₀, fg⟩ : ∃ g₀, g₀ ≫ (h ⁻¹ᵁ U).ι = M'.gp := ⟨_, IsOpenImmersion.lift_fac _ _ hg⟩
  suffices key : a₀ = c ≫ g₀ by rw [← fa, key, Category.assoc, fg]
  haveI : IsAffine (h ⁻¹ᵁ U) := hV
  have hq1 : a₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = c ≫ jK R := by
    rw [reassoc_of% fa, reassoc_of% hac, M.gp_π]
  have hq2 : g₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = jK R := by
    rw [reassoc_of% fg, reassoc_of% e, M.gp_π]
  have hinj : Function.Injective g₀.appTop.hom := by
    haveI : IsDominant (g₀ ≫ (h ⁻¹ᵁ U).ι) := by rw [fg]; exact M'.dominant
    haveI : IsDominant g₀ := IsDominant.of_comp_of_isOpenImmersion g₀ (h ⁻¹ᵁ U).ι
    rw [injective_iff_map_eq_zero]
    intro x hx0
    apply eq_zero_of_basicOpen_eq_bot
    by_contra hne
    obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    obtain ⟨z, hz⟩ := g₀.denseRange.exists_mem_open (Scheme.basicOpen _ x).isOpen ⟨y, hy⟩
    have hz' : z ∈ g₀ ⁻¹ᵁ Scheme.basicOpen _ x := hz
    have hx0' : (ConcreteCategory.hom (g₀.app ⊤)) x = 0 := hx0
    rw [Scheme.preimage_basicOpen, hx0', Scheme.basicOpen_zero] at hz'
    exact hz'
  have hfrac : ∀ x : Γ(Sp (FractionRing R), ⊤), ∃ r t : Γ(Sp R, ⊤),
      IsUnit ((jK R).appTop.hom t) ∧ x * (jK R).appTop.hom t = (jK R).appTop.hom r := by
    intro x
    have nat : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom s) =
        algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := fun s =>
      congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
    obtain ⟨r', t', ht', hx'⟩ := IsFractionRing.div_surjective (A := R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom x)
    have ht0 : algebraMap R (FractionRing R) t' ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t', ?_, ?_⟩
    · have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
          ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t'))) := by
        rw [nat]; simpa using ht0
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      simpa using this
    · apply inj
      rw [map_mul, nat, nat]
      have hi : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s) = s :=
        fun s => congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
      rw [hi, hi, ← hx']
      exact div_mul_cancel₀ _ ht0
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop]
  ext b
  obtain ⟨r, t, ht, hx⟩ := hfrac (g₀.appTop.hom b)
  have e1 : b * ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom t = ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom r := by
    apply hinj
    rw [map_mul, ← cA, ← cA, hq2, hx]
  have e2 := congrArg a₀.appTop.hom e1
  rw [map_mul, ← cA, ← cA, hq1, cA, cA, ← hx, map_mul] at e2
  exact (IsUnit.mul_left_inj (ht.map c.appTop.hom)).1 e2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFractionFieldOfFinitelyManyProportionalImaStatement
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fractionField_of_finitely_many_proportional_images : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (X : Scheme.{0}) (x : Sp R ⟶ X) (I : Type) [Finite I] (v : I → R), R.FG → (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite → (∀ (K : Type) [Field K] [IsAlgClosed K] (c : I → K), Set.Finite {y : Sp K ⟶ X | ∃ σ : R →+* K, spMap σ ≫ x = y ∧ ∃ u : K, u ≠ 0 ∧ ∀ i, σ (v i) = u * c i}) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {z | ∃ i i', z = (v i : Ω) / (v i' : Ω)})) Ω := by
  first | exact @GlobalTheory.LevelFinite.finite_ratio_field | exact GlobalTheory.LevelFinite.finite_ratio_field | (intros; apply GlobalTheory.LevelFinite.finite_ratio_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAutStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiser_systems_definite_forms_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSubStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)), Nonempty (SABMap t₀ Xo.univ.t y.x) → Nonempty (SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) → ∀ (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ t : 𝓞 E →+* 𝓞 K, (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act t) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  first | exact @GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub | exact GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub | (intros; apply GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub <;> assumption)
end

