import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PullAlExtensionFieldOfFraction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section

variable (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]

theorem jFK_self : jFK (R := V) (FractionRing V) = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _
  exact Spec.map_id _

def specFrac : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing V)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F))

theorem specFrac_jFK : specFrac V F ≫ jFK (R := V) (FractionRing V) = jFK (R := V) F :=
  (congrArg (fun q => specFrac V F ≫ q) (jFK_self V)).trans (Category.comp_id _)

def toFrac : TF (R := V) F ⟶ TF (R := V) (FractionRing V) :=
  Over.homMk (specFrac V F) ((Category.assoc (specFrac V F) (jFK (R := V) (FractionRing V)) (jK V)).symm.trans
    (congrArg (fun q => q ≫ jK V) (specFrac_jFK V F)))

theorem toFrac_jFK : (toFrac V F).left ≫ jFK (R := V) (FractionRing V) = jFK (R := V) F :=
  specFrac_jFK V F

variable {V} (D : DegPre V)

def bc : DegPre.BF D F ⟶ DegPre.BF D (FractionRing V) := toFrac V F ▷ D.P.A

theorem bc_prB : bc F D ≫ DegPre.prB D (FractionRing V) = DegPre.prB D F := whiskerRight_snd _ _

theorem bc_prB_left : (bc F D).left ≫ (DegPre.prB D (FractionRing V)).left = (DegPre.prB D F).left :=
  congrArg (fun q => q.left) (bc_prB F D)

theorem zF_bc : DegPre.zF D F ≫ bc F D = toFrac V F ≫ DegPre.zF D (FractionRing V) := by
  unfold DegPre.zF bc
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [Category.assoc, whiskerRight_snd, lift_snd]
    rw [← Category.assoc, comp_toUnit]

theorem bc_famφ (α : D.X) (i : Fin 4) :
    (bc F D).left ≫ DegPre.famφ D (FractionRing V) α i = DegPre.famφ D F α i := by
  rw [GC.famφ_eq, GC.famφ_eq, ← Category.assoc, bc_prB_left]

end

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
  (F : Type) [Field F] [Algebra (FractionRing V) F] {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]

theorem aF_bc (oa : D.toPre.OAct O) (a : O) :
    aF D F oa a ≫ bc F D.toPre = bc F D.toPre ≫ aF D (FractionRing V) oa a := by
  unfold aF
  apply CartesianMonoidalCategory.hom_ext
  · simp [bc]
  · simp only [Category.assoc, lift_snd]
    rw [← Category.assoc (bc F D.toPre), bc_prB]
    exact lift_snd _ _

theorem aF_bc_left (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (bc F D.toPre).left = (bc F D.toPre).left ≫ (aF D (FractionRing V) oa a).left :=
  congrArg (fun q => q.left) (aF_bc D F oa a)

theorem bc_pullφ (oa : D.toPre.OAct O) (a : O) (χ : D.toPre.X) (i : Fin 4 ⊕ Fin 4) :
    (bc F D.toPre).left ≫ pullφ D (FractionRing V) oa a χ i = pullφ D F oa a χ i := by
  rcases i with i | i
  · exact bc_famφ F D.toPre _ i
  · show (bc F D.toPre).left ≫ (aF D (FractionRing V) oa a).left ≫ _ = (aF D F oa a).left ≫ _
    rw [← Category.assoc, ← aF_bc_left, Category.assoc, bc_famφ]

theorem sval_bc {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {g : D.toPre.SecB k α}
    (hs : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s (D.toPre.famφB α)
      (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1)
    (ht : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) t (D.toPre.famφB α)
      (DegPre.famε k) g (DegPre.prB D.toPre F).left 1)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    sval t r z J = sval s (r ≫ (bc F D.toPre).left) z J := by
  rw [← SectionScalarValuation.secScal_sval ht r z hJ, ← SectionScalarValuation.secScal_sval hs _ z hJ, Category.assoc, bc_prB_left]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (E : Fam D.toPre (FractionRing V) k) (E' : Fam D.toPre (FractionRing V) (k * N)) (g : ∀ α, D.toPre.SecB k α) (g' : ∀ α, D.toPre.SecB (k * N) α) (θ : Fam D.toPre F k) (θ' : Fam D.toPre F (k * N)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε (k * N)) (E'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε (k * N)) (θ'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre F).left 1) → PullAl D (FractionRing V) oa a k N E E' → PullAl D F oa a k N θ θ' := by
  intro V _ _ _ D F _ _ O _ _ _ oa a k N E E' g g' θ θ' hE hE' hθ hθ' hP
  have hL := D.toPre.P.isLB
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hrel⟩ := hP.1 χ
    obtain ⟨u', hu', vu⟩ := exists_gen hL (φ' := pullφ D F oa a χ) (ε' := pullε k N)
      (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [bc_pullφ])
      (LB.pullGen D.toPre.P.L _ _ u (bc F D.toPre).left) (pullGen_isGen _ _ _ _ hu _)
    refine ⟨u', hu', corr_of_val hL fun y J hJ => ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_⟩
    · have e := val_corr hJ hc (toFrac V F).left
      rw [val_pull hJ, val_pull hJ, toFrac_jFK] at e
      have z₁ : (DegPre.zF D.toPre F).left ≫ (bc F D.toPre).left =
          (toFrac V F).left ≫ (DegPre.zF D.toPre (FractionRing V)).left :=
        congrArg (fun q => q.left) (zF_bc F D.toPre)
      rw [val_pull hJ, val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, Category.id_comp, z₁]
      exact e
    · have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (bc F D.toPre).left y J hJ
      rw [sval_bc D F (hE' _) (hθ' _) _ y hJ, sval_bc D F (hE _) (hθ _) _ y hJ, vu _ _ y J hJ, val_pull hJ,
        Category.id_comp, Category.id_comp, aF_bc_left]
      exact e
  · refine fn_ext (V := LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F β) j) fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left => exists_chart hL (ψ y)
    have hI' : Good D.toPre.P.L y I := hI
    have e : sval (θ'.s β) (𝟙 _) y I = 0 := by
      rw [sval_bc D F (hE' β) (hθ' β) _ y hI']
      exact (congrArg (gs _ y _) (hP.2 β hβ _)).trans (gs_zero _ y _ (hI'.mem _ _))
    refine (sec_trans (θ'.s β) (𝟙 _) y hy (hI'.mem _ _)).trans ?_
    exact (congrArg _ e).trans ((mul_zero _).trans (gs_zero _ y _ hy).symm)

end GlobalTheory.PullBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PullAlLinearCombination
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullComb

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]

theorem aF_fst (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left := by
  rw [← Over.comp_left]
  unfold aF
  rw [lift_fst]

theorem gen_val (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    {u u' : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))} (hu : u.IsGen) (hu' : u'.IsGen)
    {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)}
    (c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left) t)
    (c' : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u' (DegPre.zF D.toPre F).left) t)
    (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u r z J = val u' r z J := by
  have hβ : Function.Surjective (β_ (TF (R := V) F) D.toPre.P.A).hom.left.appTop.hom := by
    intro x
    refine ⟨(β_ (TF (R := V) F) D.toPre.P.A).inv.left.appTop.hom x, ?_⟩
    have hid : (β_ (TF (R := V) F) D.toPre.P.A).hom.left ≫ (β_ (TF (R := V) F) D.toPre.P.A).inv.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    have hx := congrArg (fun g => g.appTop.hom x) hid
    first
      | simpa [Scheme.Hom.appTop] using hx
      | (simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at hx; exact hx)
  have hp : Function.Surjective (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom := by
    have h1 := surj_comp hβ (surj_snd hG D.toPre.P.isAb (TF (R := V) F))
    rwa [← Over.comp_left, braiding_hom_snd] at h1
  have he : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left]
    unfold DegPre.zF
    rw [lift_fst, Over.id_left]
  refine gen_unique D.toPre.P.isLB _ _ he hp hu hu' ?_ Z r z J hJ
  intro y J' hJ'
  have e1 := val_pull hJ' u (DegPre.zF D.toPre F).left (𝟙 _)
  have e2 := val_pull hJ' u' (DegPre.zF D.toPre F).left (𝟙 _)
  rw [Category.id_comp] at e1 e2
  rw [← e1, ← e2, val_corr hJ' c, val_corr hJ' c']

private lemma sval_add_of_good {k : ℕ} (s s' : Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) :
    sval ((s + s').s α) r z J = sval (s.s α) r z J + sval (s'.s α) r z J := by
  unfold sval
  exact (congrArg (gs r z _) (ReciprocityTheory.ChartRestriction.G.DVR.add_f s s' α _)).trans (gs_add _ _ _ (hJ.mem _ r) _ _)

theorem pull_add (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s s' : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s' t') :
    PullAl D F oa a k N (s + s') (t + t') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hr⟩ := h1 χ
    obtain ⟨u', hu', hc', hr'⟩ := h1' χ
    refine ⟨u, hu, hc, ?_⟩
    refine (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 ?_
    intro y J hJ
    have e1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hr _ (𝟙 _) y J hJ
    have e2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 hr' _ (𝟙 _) y J hJ
    have e3 := gen_val hG oa a k N χ hu' hu hc' hc _ (𝟙 _) y J hJ
    rw [sval_add_of_good _ _ _ _ _ hJ, sval_add_of_good _ _ _ _ _ hJ, e1, e2, e3, add_mul]
  · rw [ReciprocityTheory.ChartRestriction.G.DVR.add_f, h2 β hβ j, h2' β hβ j, add_zero]

private lemma sval_smul_eq_gs_gF_mul_of_good {k : ℕ} (ζ : F) (s : Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) :
    sval ((ζ • s).s α) r z J = gs r z ⊤ (gF D.toPre F ζ) * sval (s.s α) r z J := by
  unfold sval
  refine (congrArg (gs r z _) (ReciprocityTheory.ChartRestriction.G.DVR.smul_f ζ s α _)).trans ?_
  refine (gs_mul _ _ _ (hJ.mem _ r) _ _).trans ?_
  congr 1
  exact gs_res r z le_top (hJ.mem _ r) _

private lemma gs_aF_gF_eq_gs_gF (oa : D.toPre.OAct O) (a : O) (ζ : F) (y : (DegPre.BF D.toPre F).left) :
    gs (𝟙 _ ≫ (aF D F oa a).left) y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) := by
  have k1 : ∀ f : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left,
      gs f y ⊤ (gF D.toPre F ζ) = gs (f ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
    fun f => gs_pull f _ y ⊤ (by simp) _
  rw [k1, k1, Category.assoc, aF_fst]

theorem pull_smul (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (ζ : F) {s : Fam D.toPre F k}
    {t : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) : PullAl D F oa a k N (ζ • s) (ζ • t) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hr⟩ := h1 χ
    refine ⟨u, hu, hc, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 ?_⟩
    intro y J hJ
    have e1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hr _ (𝟙 _) y J hJ
    rw [sval_smul_eq_gs_gF_mul_of_good _ _ _ _ _ hJ, sval_smul_eq_gs_gF_mul_of_good _ _ _ _ _ hJ, e1, gs_aF_gF_eq_gs_gF, _root_.mul_assoc]
  · rw [ReciprocityTheory.ChartRestriction.G.DVR.smul_f, h2 β hβ j, mul_zero]

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N n : ℕ), 0 < n → ∀ (c : Fin n → F) (s : Fin n → Fam D.toPre F k) (s' : Fin n → Fam D.toPre F (k * N)), (∀ l, PullAl D F oa a k N (s l) (s' l)) → PullAl D F oa a k N (∑ l, c l • s l) (∑ l, c l • s' l) := by
  intro hG V _ _ _ D F _ _ O _ _ _ oa a k N n hn c s s' hs
  have key : ∀ S : Finset (Fin n), S.Nonempty →
      PullAl D F oa a k N (∑ l ∈ S, c l • s l) (∑ l ∈ S, c l • s' l) := by
    intro S hS
    induction hS using Finset.Nonempty.cons_induction with
    | singleton l =>
      rw [Finset.sum_singleton, Finset.sum_singleton]
      exact pull_smul oa a k N (c l) (hs l)
    | cons l S hl hS ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact pull_add hG oa a k N (pull_smul oa a k N (c l) (hs l)) ih
  exact key Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩

end GlobalTheory.PullComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
section
namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

private theorem relDim_eq_of_smoothOfRelativeDimension_grp {X Y : Scheme.{0}} (f : X ⟶ Y) (n m : ℕ) (x : X)
    (hn : SmoothOfRelativeDimension n f) (hm : SmoothOfRelativeDimension m f) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hn.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hQ⟩ :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) f hm ⟨U, hU⟩ ⟨V, hV⟩ e
  have hp := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    by_contra! H
    exact hp.ne_top (eq_top_iff.2 (hs ▸ Ideal.span_le.2 H))
  have : Nontrivial (Localization.Away t) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h0 : algebraMap Γ(X, V) (Localization.Away t) 1 = 0 := Subsingleton.elim _ _
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers t)] at h0
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := h0
    have hc' : t ^ k = 0 := by simpa using hc
    exact htp (hp.mem_of_pow_mem k (by rw [hc']; exact Ideal.zero_mem _))
  have hn' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    (Localization.Away t) t _ h
  have hm' := hQ t ht
  let := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) (Localization.Away t) := hn'
  have a1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) n
  have : Algebra.IsStandardSmoothOfRelativeDimension m Γ(Y, U) (Localization.Away t) := hm'
  have a2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) m
  exact_mod_cast a1.symm.trans a2

private theorem exists_limit_fan_smooth_relDim_mul {S : Scheme.{0}} (A : Over S) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom) :
    ∀ k : ℕ, ∃ c : Fan (fun _ : Fin k => A), Nonempty (IsLimit c) ∧
      SmoothOfRelativeDimension (k * g) c.pt.hom := by
  intro k
  induction k with
  | zero =>
    refine ⟨Fan.mk (𝟙_ (Over S)) (fun i => Fin.elim0 i), ⟨Fan.IsLimit.mk _
      (fun s => CartesianMonoidalCategory.toUnit s.pt) (fun _ i => Fin.elim0 i)
      (fun _ _ _ => CartesianMonoidalCategory.toUnit_unique _ _)⟩, ?_⟩
    rw [zero_mul]
    show SmoothOfRelativeDimension 0 (𝟙 S)
    infer_instance
  | succ k ih =>
    obtain ⟨c, ⟨hc⟩, hsm⟩ := ih
    refine ⟨extendFan (f := fun _ : Fin (k + 1) => A) c
      (BinaryFan.mk (CartesianMonoidalCategory.fst A c.pt) (CartesianMonoidalCategory.snd A c.pt)),
      ⟨extendFanIsLimit (fun _ : Fin (k + 1) => A) hc
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct A c.pt)⟩, ?_⟩
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (k * g)) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (k * g)
    have h1 : SmoothOfRelativeDimension (k * g) (pullback.fst A.hom c.pt.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback A.hom c.pt.hom).flip hsm
    have h2 := smoothOfRelativeDimension_comp (n := k * g) (m := g) (pullback.fst A.hom c.pt.hom) A.hom
    rw [Nat.succ_mul]
    exact h2

theorem rank_and_g_of_isPowDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j), D'.rank = j * D.rank ∧ D'.P.g = j * D.P.g := by
  intro R _ _ j D D' pD
  rcases pD with ⟨pw, w, wg, wr, xe, cpr, wpsi⟩
  refine ⟨?_, ?_⟩
  · have e : D'.X ≃ₗ[ℤ] (Fin j → D.X) := xe.toIntLinearEquiv
    unfold DegPre.rank
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp
  · rcases pw with ⟨pr, hom, lim⟩
    obtain ⟨c, ⟨hc⟩, hsm⟩ := exists_limit_fan_smooth_relDim_mul D.P.A D.P.g D.P.5 j
    let e := IsLimit.conePointUniqueUpToIso lim hc
    have hw : e.hom.left ≫ c.pt.hom = D'.P.A.hom := Over.w e.hom
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h3 := smoothOfRelativeDimension_comp (n := 0) (m := j * D.P.g) e.hom.left c.pt.hom
    rw [hw, zero_add] at h3
    let := D'.P.2
    have p : (𝟙_ (Over (Spec (CommRingCat.of R)))).left := (inferInstance : Nonempty (PrimeSpectrum R)).some
    exact relDim_eq_of_smoothOfRelativeDimension_grp D'.P.A.hom _ _ ((η[D'.P.A]).left p) D'.P.5 h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.RosatiPower

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]

private theorem padd_comp_eq_padd_comp_of_isMonHom {T H K : Over S} [GrpObj H] [GrpObj K] (q : H ⟶ K) [IsMonHom q]
    (a b : T ⟶ H) : padd H a b ≫ q = padd K (a ≫ q) (b ≫ q) := by
  unfold padd
  simp [IsMonHom.mul_hom]

private theorem comp_padd_eq_padd_comp {T T' H : Over S} [GrpObj H] (x : T ⟶ T') (a b : T' ⟶ H) :
    x ≫ padd H a b = padd H (x ≫ a) (x ≫ b) := by
  unfold padd
  first
  | simp
  | simp [Hom.mul_def]
  | simp [comp_lift_assoc]

theorem rosatiφ_comp (q : G' ⟶ G) [IsMonHom q] {f g : G ⟶ G} {f' g' : G' ⟶ G'}
    (hf : f' ≫ q = q ≫ f) (hg : g' ≫ q = q ≫ g) (k : Fin 6) :
    rosatiφ G' f' g' k ≫ q.left = (q ⊗ₘ q).left ≫ rosatiφ G f g k := by
  have e1 : (q ⊗ₘ q) ≫ fst G G = fst G' G' ≫ q := by simp
  have e2 : (q ⊗ₘ q) ≫ snd G G = snd G' G' ≫ q := by simp
  have key : ∀ (a : G' ⊗ G' ⟶ G') (b : G ⊗ G ⟶ G), a ≫ q = (q ⊗ₘ q) ≫ b →
      a.left ≫ q.left = (q ⊗ₘ q).left ≫ b.left := by
    intro a b h
    rw [← Over.comp_left, h, Over.comp_left]
  fin_cases k <;> refine key _ _ ?_ <;>
    simp only [padd_comp_eq_padd_comp_of_isMonHom, comp_padd_eq_padd_comp, Category.assoc, hf, hg, reassoc_of% e1, reassoc_of% e2, e1, e2]

theorem exists_restrict {A B : Over S} (q : A ⟶ B) (U : S.Opens) :
    ∃ n : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      n ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ q.left := by
  refine ⟨q.left.resLE (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  intro x hx
  rw [← Over.w q] at hx
  exact hx

private theorem exists_isGen_of_isGen_iso_of_isGen {X : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB)
    (u : LB.Iso A B) (hu : u.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ t' : LB.Gen A, t'.IsGen := by
  classical
  let tS : LB.Sec B := ⟨fun b => (t.s b : Γ(X, B.U b)), fun i j => by
    have e := congrArg Units.val (ht i j)
    simpa [res] using e⟩
  have hunit : ∀ a, IsUnit ((secOfIso tS hu hA hB).f a) := by
    intro a
    apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace
    intro x hx
    have hc := cover_inf hB a hx
    rw [TopologicalSpace.Opens.mem_iSup] at hc
    obtain ⟨b, hb⟩ := hc
    have hsp := secOfIso_spec tS hu hA hB a b
    have e1 : X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a) =
        X.presheaf.germ (A.U a ⊓ B.U b) x hb (rs inf_le_left ((secOfIso tS hu hA hB).f a)) := by
      simp only [rs, TopCat.Presheaf.germ_res_apply]
    change IsUnit (X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a))
    rw [e1, hsp, isoCand, map_mul]
    refine IsUnit.mul ((Units.isUnit _).map _) ?_
    simp only [rs, TopCat.Presheaf.germ_res_apply]
    exact (Units.isUnit (t.s b)).map _
  refine ⟨⟨fun a => (hunit a).unit⟩, fun i j => ?_⟩
  apply Units.ext
  have e := (secOfIso tS hu hA hB).compat i j
  simpa [res] using e

end GlobalTheory.RosatiPower

open GlobalTheory.RosatiPower in

theorem GlobalTheory.rosatiAdj_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f g : G ⟶ G) (f' g' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → (∀ i, g' ≫ p.pr i = p.pr i ≫ g) → RosatiAdj G L f g → RosatiAdj G' L' f' g' := by
  intro S G' G _ _ _ _ j p L L' hL hL' hiso f g f' g' hf hg hr
  have hm : ∀ i, IsMonHom (p.pr i) := p.hom
  unfold RosatiAdj at hr ⊢
  unfold boxLB at hiso
  intro s
  obtain ⟨U, hsU, t, ht⟩ := hr s
  refine ⟨U, hsU, ?_⟩
  obtain ⟨w, hw⟩ := hiso
  have hn : ∀ i, ∃ n : ((G' ⊗ G').hom ⁻¹ᵁ U).toScheme ⟶ ((G ⊗ G).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι = ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ (p.pr i ⊗ₘ p.pr i).left :=
    fun i => exists_restrict (p.pr i ⊗ₘ p.pr i) U
  choose n hn using hn
  have hc : ∀ i k, (((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) ≫ (p.pr i).left =
      n i ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι ≫ rosatiφ G f g k := by
    intro i k
    rw [Category.assoc, rosatiφ_comp (p.pr i) (hf i) (hg i) k, ← Category.assoc, ← hn i, Category.assoc]
  let t' : ∀ i, ((L.pull (p.pr i).left).LinComb
      (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε).Gen :=
    fun i => GeneratorPullback.pullAlong L (p.pr i).left (n i) _ rosatiε _ (hc i) t
  have ht' : ∀ i, (t' i).IsGen := by
    intro i
    exact LBxP.isGen_pullAlong L (Over.Hom.left (p.pr i)) (n i) _ rosatiε _ (hc i) t ht
  have hb := GlobalTheory.BoxSymmetry.isGen_boxGen L (fun i => (p.pr i).left) _ rosatiε t' ht'
  have hwi := linCombIso_isGen w hw (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε
  exact exists_isGen_of_isGen_iso_of_isGen (linComb_isLB _ hL' _ _) (linComb_isLB _ (linComb_isLB _ hL _ _) _ _) _ hwi _ hb

end
end

