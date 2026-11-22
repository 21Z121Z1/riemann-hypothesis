import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2909
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorCorrectedTorusCoordinateRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslRatio

theorem prod_gtφT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) :
    ∏ k, h (ρ.left ≫ DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h ((toUnit T' ≫ D.c χ) * (ρ ≫ b)).left)⁻¹ * h (toUnit T' ≫ D.c χ).left * h (ρ ≫ b).left *
        (h (1 : T' ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, ← comp_toUnit ρ, Category.assoc, ← MonObj.comp_mul, ← MonObj.comp_one ρ]
  show h (ρ ≫ ((toUnit T ≫ D.c χ) * b)).left ^ (-1 : ℤ) * h (ρ ≫ toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
    h (ρ ≫ b).left ^ (1 : ℤ) * h (ρ ≫ (1 : T ⟶ D.P.A)).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem formEq_translate {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R)
    {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (hT : T ⟶ T) (p : T ⟶ D.P.A)
    (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (hp : hT ≫ p = (p₂ ≫ β) * (toUnit T ≫ b)) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => hT.left ≫ D.Oφ p χ k)
        (Sum.elim (fun k : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ k.1 ≫ twφ D₂ D β b k.2)
          (fun k => (toUnit T).left ≫ DegPre.gtφT D _ b χ k)))
      (Sum.elim Oinvε (fun k => - Sum.elim (fun k : Fin 4 × Fin 3 => Oinvε k.1 * twε k.2) DegPre.gtε k))
      (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D.c χ) (D.c χ) k) ![1, -1, 1, -1] := by
  intro U _ h
  have hu : ∀ x : T ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit T := fun x => toUnit_unique _ _
  have ht : ∀ x : T ⟶ D₂.P.A, ∏ i, h (x.left ≫ twφ D₂ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.Oφ p₂ χ₂ k =
      ((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ k : Fin 4 × Fin 3, h (D₂.Oφ p₂ χ₂ k.1 ≫ twφ D₂ D β b k.2) ^ (Oinvε k.1 * twε k.2) =
      ∏ k : Fin 4, (h (((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] :
        Fin 4 → (T ⟶ D₂.P.A)) k ≫ β) * (toUnit T ≫ b)).left *
        (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left) ^ Oinvε k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (Oinvε k) (twε i), zpow_mul, hx]
  have h0 : (p₂ * (toUnit T ≫ D₂.c χ₂)) ≫ β * (toUnit T ≫ b) =
      (p₂ ≫ β) * (toUnit T ≫ b) * (toUnit T ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.assoc, hc, mul_right_comm]
  have h3 : (1 : T ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  have hC : ∏ k, h (hT.left ≫ D.Oφ p χ k) ^ (Oinvε k) =
      (h ((p₂ ≫ β) * (toUnit T ≫ b) * (toUnit T ≫ D.c χ)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h ((p₂ ≫ β) * (toUnit T ≫ b)).left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
    simp only [WeightPf.Oφ_comp]
    rw [Fin.prod_univ_four, ← hp]
    show h ((hT ≫ p) * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
      h (hT ≫ p).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
    simp only [zpow_neg, zpow_one]
  have hS : ∏ k, h ((toUnit T).left ≫ DegPre.gtφT D _ b χ k) ^ (DegPre.gtε k) =
      (h ((toUnit T ≫ D.c χ) * (toUnit T ≫ b)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h (toUnit T ≫ b).left * (h (1 : T ⟶ D.P.A).left)⁻¹ :=
    prod_gtφT (toUnit T) b χ h
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA, hC, hS, GlobalTheory.CoordCompare.prod_diff, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, h0, h3, _root_.one_mul, Category.assoc, hc]
  simp only [Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio_gen : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)), w.IsGen → ∀ (χ₂ : D₂.X) (χ : D.X), D₂.c χ₂ ≫ β = D.c χ → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ g.pG.left = g₂.pG.left ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b 0 → ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ GlobalTheory.CoordCompare.diffφ (D.prBe I e) (D.c χ) (D.c χ) k) ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val u r z J = val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ gp w hw χ₂ χ hc h hh hp
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let hT : T ⟶ T := Over.homMk h ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) hh))
  obtain ⟨t₁, ht₁, hv₁⟩ := GlobalTheory.Mum.GenTransport.exists_transport D.P.isLB D₂.P.isLB _ _ w hw _ _
    (g₂.t χ₂) (g₂.t_gen χ₂)
  have hF := formEq_translate D₂ D ((Over.map (thick R I e)).map g.q) (D.prBe I e) hT g.pG g₂.pG β gp.b
    (Over.OverMorphism.ext hp |>.trans (by
      show g₂.pG ≫ (β * (toUnit D₂.P.A ≫ gp.b)) = _
      rw [MonObj.comp_mul, comp_toUnit_assoc])) χ₂ χ hc
  obtain ⟨u, hu, hv⟩ := exists_gen D.P.isLB hF
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) h) (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ t₁
      (LB.pullGen D.P.L _ _ (gp.s χ) ((thickObj R I e G).hom ≫ thick R I e)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _) (DVR.invGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁ (DVR.pullGen_isGen _ _ _ _ (gp.isGen χ) _))))
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  exact (hv Z r z J hJ).trans ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_pull hJ _ _ r)
    ((val_inv _ r).trans (congrArg (·⁻¹) ((val_mul hJ _ _ r).trans
      (congrArg₂ (· * ·) (hv₁ Z r z J J' hJ hJ') (val_pull hJ _ _ r)))))))

end GlobalTheory.MumCmp.TranslRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMultiplicativeOnQuotientKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

theorem prod_psum_two {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x y : T ⟶ A) {V : Type}
    [CommGroup V] (h : (T.left ⟶ A.left) → V) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum A ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ A).left := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum A ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum A ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_mφ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    (a b : H₁ ⟶ H₂) {T : Over S} (x y : T ⟶ H₁) {V : Type} [CommGroup V] (h : (T.left ⟶ H₁.left ⨿ H₂.left) → V) :
    ∏ k, h ((lift x y).left ≫ mφ H₁ H₂ a b k) ^ mε k =
      (h (((x ≫ a) * (y ≫ b)).left ≫ coprod.inr) * (h ((x ≫ a).left ≫ coprod.inr))⁻¹ *
        (h ((y ≫ b).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ H₂).left ≫ coprod.inr)) *
      (h ((x * y).left ≫ coprod.inl) * (h (x.left ≫ coprod.inl))⁻¹ * (h (y.left ≫ coprod.inl))⁻¹ *
        h ((1 : T ⟶ H₁).left ≫ coprod.inl))⁻¹ := by
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) ((Finset.prod_congr rfl fun I _ => ?_).trans
    (prod_psum_two (x ≫ a) (y ≫ b) (fun q => h (q ≫ coprod.inr))))
    ((Finset.prod_congr rfl fun I _ => ?_).trans ((Finset.prod_inv_distrib _).trans
      (congrArg (·⁻¹) (prod_psum_two x y (fun q => h (q ≫ coprod.inl))))))
  · rw [mφ_comp]; rfl
  · rw [mφ_comp]; exact zpow_neg _ _

theorem push_comp_two {S S' : Scheme.{0}} {j : S' ⟶ S} {E₁ E₂ : Over S'} {A₁ A₂ : Over S}
    (p₁ : (Over.map j).obj E₁ ⟶ A₁) (p₂ : (Over.map j).obj E₂ ⟶ A₂) {c' : E₁ ⟶ E₂} {c : A₁ ⟶ A₂}
    (h : GlobalTheory.EndRosati.push p₂ c' = p₁ ≫ c) {T : Over S'} (x : T ⟶ E₁) :
    GlobalTheory.EndRosati.push p₂ (x ≫ c') = GlobalTheory.EndRosati.push p₁ x ≫ c := by
  simp only [GlobalTheory.EndRosati.push, Functor.map_comp, Category.assoc] at h ⊢
  rw [h]

theorem push_pG_pair {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
    {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
    [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f : G₁ ⟶ G₂}
    {fB : D₁.toPre.P.A ⟶ D₂.toPre.P.A}
    (hf : (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB) :
    GlobalTheory.EndRosati.push (U₂.gt e).pG ((Over.pullback (thick R I e)).map f) = (U₁.gt e).pG ≫ fB := by
  rw [GlobalTheory.EndRosati.push]
  simp only [GtCoord.pG]
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, Category.assoc]
  exact congrArg _ (GlobalTheory.EndRosati.push_fstG e fB)

theorem add_left_two {P₁ P₂ V : Type} [CommGroup P₁] [CommGroup P₂] [CommGroup V] (W₁ : P₁ → V) (W₂ : P₂ → V)
    {x x' y : P₁} {a a' b : P₂} {c₁ c₂ v v₁ v₂ : V}
    (h₁ : 1 = W₁ (x * x' * y) * (W₁ (x * x'))⁻¹ * (W₁ (x * y))⁻¹ * (W₁ (x' * y))⁻¹ * W₁ x * W₁ x' * W₁ y *
      (W₁ 1)⁻¹ * c₁)
    (h₂ : 1 = W₂ (a * a' * b) * (W₂ (a * a'))⁻¹ * (W₂ (a * b))⁻¹ * (W₂ (a' * b))⁻¹ * W₂ a * W₂ a' * W₂ b *
      (W₂ 1)⁻¹ * c₂)
    (h : v * c₁ = c₂ * (v₁ * v₂)) :
    (W₂ (a * a' * b) * (W₂ (a * a'))⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x * x' * y) * (W₁ (x * x'))⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ *
        v =
      ((W₂ (a * b) * (W₂ a)⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x * y) * (W₁ x)⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ * v₁) *
        ((W₂ (a' * b) * (W₂ a')⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x' * y) * (W₁ x')⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ * v₂) := by
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ e ⊢
  linear_combination (norm := abel) e₁ - e₂ + e

theorem add_right_two {P₁ P₂ V : Type} [CommGroup P₁] [CommGroup P₂] [CommGroup V] (W₁ : P₁ → V) (W₂ : P₂ → V)
    {x x' y : P₁} {a b b' : P₂} {c₁ c₂ v v₁ v₂ : V}
    (h₁ : 1 = W₁ (y * x * x') * (W₁ (y * x))⁻¹ * (W₁ (y * x'))⁻¹ * (W₁ (x * x'))⁻¹ * W₁ y * W₁ x * W₁ x' *
      (W₁ 1)⁻¹ * c₁)
    (h₂ : 1 = W₂ (a * b * b') * (W₂ (a * b))⁻¹ * (W₂ (a * b'))⁻¹ * (W₂ (b * b'))⁻¹ * W₂ a * W₂ b * W₂ b' *
      (W₂ 1)⁻¹ * c₂)
    (h : v * c₁ = c₂ * (v₁ * v₂)) :
    (W₂ (a * (b * b')) * (W₂ a)⁻¹ * (W₂ (b * b'))⁻¹ * W₂ 1) *
        (W₁ (y * (x * x')) * (W₁ y)⁻¹ * (W₁ (x * x'))⁻¹ * W₁ 1)⁻¹ * v =
      ((W₂ (a * b) * (W₂ a)⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (y * x) * (W₁ y)⁻¹ * (W₁ x)⁻¹ * W₁ 1)⁻¹ * v₁) *
        ((W₂ (a * b') * (W₂ a)⁻¹ * (W₂ b')⁻¹ * W₂ 1) * (W₁ (y * x') * (W₁ y)⁻¹ * (W₁ x')⁻¹ * W₁ 1)⁻¹ * v₂) := by
  rw [← _root_.mul_assoc a b b', ← _root_.mul_assoc y x x']
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ e ⊢
  linear_combination (norm := abel) e₁ - e₂ + e

end GlobalTheory.HomMum

end

namespace GlobalTheory.HomMum

set_option maxHeartbeats 1600000 in

theorem exists_gen_mul_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))), W.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) → ∀ (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), u.IsGen → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε), v.IsGen ∧ (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg W hW hW₁ hW₂ u hu hadd
  let f' := (Over.pullback (thick R I e)).map f
  let g' := (Over.pullback (thick R I e)).map g
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  have hL : (join U₁.LG.L U₂.LG.L).IsLB := join_isLB U₁.LG.isLB U₂.LG.isLB
  obtain ⟨u', hu', vu⟩ := exists_gen hL
    (φ' := fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) f' g' k ≫
      coprod.map (fstG I e G₁).left (fstG I e G₂).left) (ε' := mε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (by
      rw [mφ_push (fstG I e G₁) (fstG I e G₂) (GlobalTheory.EndRosati.fstG_mul e) (GlobalTheory.EndRosati.fstG_mul e)
        (GlobalTheory.EndRosati.push_fstG e f) (GlobalTheory.EndRosati.push_fstG e g) (fst _ _) (snd _ _) k, lift_fst_snd,
        Over.id_left, Category.id_comp]))
    (LB.pullGen (join U₁.LG.L U₂.LG.L) _ _ u
      (lift (GlobalTheory.EndRosati.push (fstG I e G₁) (fst (thickObj R I e G₁) (thickObj R I e G₁)))
        (GlobalTheory.EndRosati.push (fstG I e G₁) (snd (thickObj R I e G₁) (thickObj R I e G₁)))).left)
    (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨v, hv, vv⟩ := GlobalTheory.EndRosati.exists_gen_through hL (jn_isLB D₁.toPre D₂.toPre) W hW
    (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) f' g' k) mε u' hu'
  refine ⟨v, hv, fun T z J hJ x x' y hx => ?_⟩
  choose N hN using fun χ : T.left ⟶ G₁.left ⨿ G₂.left => exists_chart hL (χ z)
  have hN' : Good (join U₁.LG.L U₂.LG.L) z N := hN
  have gJ₁ : Good D₁.toPre.P.L z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) := (isPart_inl _ _).good hJ
  have gJ₂ : Good D₂.toPre.P.L z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) := (isPart_inr _ _).good hJ
  have gN₁ : Good U₁.LG.L z (rl N) := (isPart_inl _ _).good hN'
  have gN₂ : Good U₂.LG.L z (rr N) := (isPart_inr _ _).good hN'
  let W₁ : (T ⟶ thickObj R I e G₁) → (T.left.presheaf.stalk z)ˣ := fun q =>
    GlobalTheory.TorusInvariance.wVal U₁ e z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rl N) q.left
  let W₂ : (T ⟶ thickObj R I e G₂) → (T.left.presheaf.stalk z)ˣ := fun q =>
    GlobalTheory.TorusInvariance.wVal U₂ e z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rr N) q.left
  have hinl : ∀ q : T ⟶ thickObj R I e G₁, gw W (q.left ≫ coprod.inl) z
      (J ((q.left ≫ coprod.inl) ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
      (fun _ => N ((q.left ≫ coprod.inl) ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)) = W₁ q := fun q => by
    have := hW₁ T.left q.left z (J ((q.left ≫ (U₁.gt e).pG.left) ≫ coprod.inl))
      (N ((q.left ≫ (fstG I e G₁).left) ≫ coprod.inl)) (gJ₁ _) (gN₁ _)
    simp only [Category.assoc, coprod.inl_map] at this ⊢
    exact this
  have hinr : ∀ q : T ⟶ thickObj R I e G₂, gw W (q.left ≫ coprod.inr) z
      (J ((q.left ≫ coprod.inr) ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
      (fun _ => N ((q.left ≫ coprod.inr) ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)) = W₂ q := fun q => by
    have := hW₂ T.left q.left z (J ((q.left ≫ (U₂.gt e).pG.left) ≫ coprod.inr))
      (N ((q.left ≫ (fstG I e G₂).left) ≫ coprod.inr)) (gJ₂ _) (gN₂ _)
    simp only [Category.assoc, coprod.inr_map] at this ⊢
    exact this
  let p₁ : (T ⟶ thickObj R I e G₁) → ((Over.map (thick R I e)).obj T ⟶ G₁) := GlobalTheory.EndRosati.push (fstG I e G₁)
  let p₂ : (T ⟶ thickObj R I e G₂) → ((Over.map (thick R I e)).obj T ⟶ G₂) := GlobalTheory.EndRosati.push (fstG I e G₂)
  let q₁ : (T ⟶ thickObj R I e G₁) → ((Over.map (thick R I e)).obj T ⟶ D₁.toPre.P.A) :=
    GlobalTheory.EndRosati.push (U₁.gt e).pG
  let q₂ : (T ⟶ thickObj R I e G₂) → ((Over.map (thick R I e)).obj T ⟶ D₂.toPre.P.A) :=
    GlobalTheory.EndRosati.push (U₂.gt e).pG
  have hV : ∀ a b : T ⟶ thickObj R I e G₁, val v (lift a b).left z J =
      (W₂ ((a ≫ f') * (b ≫ g')) * (W₂ (a ≫ f'))⁻¹ * (W₂ (b ≫ g'))⁻¹ * W₂ 1) *
        (W₁ (a * b) * (W₁ a)⁻¹ * (W₁ b)⁻¹ * W₁ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (val u (lift (p₁ a) (p₁ b)).left z N) :=
    fun a b => by
      refine (vv _ _ z J N hJ hN').trans (congrArg₂ (· * ·) ?_
        ((vu _ _ z N hN').trans ((val_pull hN' _ _ _).trans (congrArg (val u · z N) (GlobalTheory.EndRosati.lift_push _ a b)))))
      refine (prod_mφ f' g' a b (fun ψ => gw W ψ z (J (ψ ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
        (fun _ => N (ψ ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)))).trans ?_
      beta_reduce
      erw [hinr ((a ≫ f') * (b ≫ g')), hinr (a ≫ f'), hinr (b ≫ g'), hinr 1, hinl (a * b), hinl a, hinl b, hinl 1]
  have hc₁ : ∀ a b c : T ⟶ thickObj R I e G₁,
      @id (T.left.presheaf.stalk z)ˣ (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
        (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₁ a) (q₁ b) (q₁ c)) =
      W₁ (a * b * c) * (W₁ (a * b))⁻¹ * (W₁ (a * c))⁻¹ * (W₁ (b * c))⁻¹ * W₁ a * W₁ b * W₁ c * (W₁ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV U₁.cubG (T := (Over.map (thick R I e)).obj T) z (rl N) (p₁ a) (p₁ b) (p₁ c)) :=
    fun a b c => (GlobalTheory.TorusInvariance.cube_val U₁ ![a, b, c] gJ₁ gN₁).trans
      (congrArg (· * _) (GlobalTheory.TorusInvariance.prod_psum a b c
        (GlobalTheory.TorusInvariance.wVal U₁ e z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rl N))))
  have hc₂ : ∀ a b c : T ⟶ thickObj R I e G₂,
      @id (T.left.presheaf.stalk z)ˣ (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
        (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₂ a) (q₂ b) (q₂ c)) =
      W₂ (a * b * c) * (W₂ (a * b))⁻¹ * (W₂ (a * c))⁻¹ * (W₂ (b * c))⁻¹ * W₂ a * W₂ b * W₂ c * (W₂ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV U₂.cubG (T := (Over.map (thick R I e)).obj T) z (rr N) (p₂ a) (p₂ b) (p₂ c)) :=
    fun a b c => (GlobalTheory.TorusInvariance.cube_val U₂ ![a, b, c] gJ₂ gN₂).trans
      (congrArg (· * _) (GlobalTheory.TorusInvariance.prod_psum a b c
        (GlobalTheory.TorusInvariance.wVal U₂ e z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rr N))))
  have C₁ := isCub_cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) gJ₁
  have C₂ := isCub_cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) gJ₂
  have c₁ : ∀ a b c, q₁ a = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) · (q₁ b) (q₁ c)) h).trans (C₁.face _ _)).symm.trans (hc₁ a b c)
  have c₂ : ∀ a b c, q₁ b = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₁ a) · (q₁ c)) h).trans (C₁.face₂ _ _)).symm.trans (hc₁ a b c)
  have d₁ : ∀ a b c, q₂ a = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) · (q₂ b) (q₂ c)) h).trans (C₂.face _ _)).symm.trans (hc₂ a b c)
  have d₂ : ∀ a b c, q₂ b = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₂ a) · (q₂ c)) h).trans (C₂.face₂ _ _)).symm.trans (hc₂ a b c)
  have hx' : q₁ x = 1 := hx
  have xf : q₂ (x ≫ f') = 1 :=
    (push_comp_two _ _ (push_pG_pair U₁ U₂ e hf) x).trans (by rw [show GlobalTheory.EndRosati.push (U₁.gt e).pG x = 1 from hx, MonObj.one_comp])
  have xg : q₂ (x ≫ g') = 1 :=
    (push_comp_two _ _ (push_pG_pair U₁ U₂ e hg) x).trans (by rw [show GlobalTheory.EndRosati.push (U₁.gt e).pG x = 1 from hx, MonObj.one_comp])
  have pf : ∀ a, p₁ a ≫ f = p₂ (a ≫ f') := fun a => (push_comp_two _ _ (GlobalTheory.EndRosati.push_fstG e f) a).symm
  have pg : ∀ a, p₁ a ≫ g = p₂ (a ≫ g') := fun a => (push_comp_two _ _ (GlobalTheory.EndRosati.push_fstG e g) a).symm
  have pm : p₁ x * p₁ x' = p₁ (x * x') := (GlobalTheory.EndRosati.fstG_mul e x x').symm
  obtain ⟨r₁, r₂⟩ := hadd ((Over.map (thick R I e)).obj T) z N hN' (p₁ x) (p₁ x') (p₁ y)
  rw [pm, pf, pf, pg] at r₁
  rw [pm, pf, pg, pg] at r₂
  rw [hV, hV, hV, hV, hV, hV, MonObj.mul_comp x x' f', MonObj.mul_comp x x' g']
  exact ⟨add_left_two W₁ W₂ (c₁ _ _ _ hx') (d₁ _ _ _ xf) r₁, add_right_two W₁ W₂ (c₂ _ _ _ hx') (d₂ _ _ _ xg) r₂⟩

end GlobalTheory.HomMum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorNearFibresOfFiniteFlat
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_gen_near_of_finFlat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsLocallyNoetherian Y → (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ x : Y', ∃ V : Y'.Opens, x ∈ V ∧ ∃ t : LB.Gen ((L'.pull k').pull (p' ⁻¹ᵁ V).ι), t.IsGen) → ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp hY hbij L hL hloc x
  haveI : IsNoetherianRing R := hR.1
  obtain ⟨hkf, hqc, hqs, hsurj, hcl, hclp, hO, d, b, hb⟩ :=
    GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties R R' ρ hfin.2.1 hfin.2.2 hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  obtain ⟨V, hV, y₀, hy₀, hxy, hE⟩ := GlobalTheory.T.exists_specialization_closed_in_affine_neighbourhood Y x
  obtain ⟨hclV, -⟩ := hE V le_rfl hV hy₀
  have hL' : (L.pull k').IsLB := LB.isLB_pull hL _
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre Y Y' Z' k hkf p' hqc hqs V hV y₀ hy₀ hclV (L.pull k') hL' (fun x' _ => hloc x')
  obtain ⟨V₁, hy₁, hV₁V, hV₁⟩ := GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap Z' Y (p' ≫ k) hcl (L.pull k') V s y₀ hy₀ hs
  obtain ⟨f, hf1, hf2⟩ := hV.exists_basicOpen_le ⟨y₀, hy₁⟩ hy₀
  have hV₂V : Y.basicOpen f ≤ V := Y.basicOpen_le f
  have hV₂ : IsAffineOpen (Y.basicOpen f) := hV.basicOpen f
  obtain ⟨-, M, hM, hMiff⟩ := hE (Y.basicOpen f) hV₂V hV₂ hf2
  have hcomm : ∀ z : Z', p (k' z) = k (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk'.w]
  have hle : k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) ≤ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := fun z hz => by
    show k (p' z) ∈ V
    rw [← hcomm]
    exact hV₂V hz
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section Z' (L.pull k') hL' _ _ hle s (fun z₀ hz₀ => hV₁ z₀ (by
    rw [Scheme.Hom.comp_apply, ← hcomm]
    exact hf1 hz₀))
  have hsurjp : Function.Surjective (p.app (Y.basicOpen f)).hom := (hbij _).2
  let e := RingEquiv.ofBijective (p.app (Y.basicOpen f)).hom (hbij _)
  haveI hm : (Ideal.comap e.symm.toRingHom M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  obtain ⟨hOc, hOq⟩ := hO _ hV₂
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_nonzero_section_of_finite_free_baseChange R R' ρ d b hb Z Z' k' (p ≫ y) (p' ≫ y') (hk'.paste_vert hk) (p ⁻¹ᵁ Y.basicOpen f) hOc hOq
    L hL σ hσ _ hm
  have hfib : ∀ z₀ : (p ⁻¹ᵁ Y.basicOpen f).toScheme, p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) = y₀ → z₀ ∈ nonzeroLocus u := by
    intro z₀ hz₀
    obtain ⟨z', hz'⟩ := hsurj ((p ⁻¹ᵁ Y.basicOpen f).ι z₀)
    have hz'O : z' ∈ k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) := by
      show k' z' ∈ p ⁻¹ᵁ Y.basicOpen f
      rw [hz']
      first | exact z₀.2 | simpa using z₀.2 | exact (Scheme.Opens.range_ι _).subset ⟨z₀, rfl⟩
    obtain ⟨w, hw⟩ : z' ∈ Set.range (k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι.base := by
      rw [Scheme.Opens.range_ι]; exact hz'O
    refine hu w (fun a ha => ?_) z₀ (by rw [← hz']; exact congrArg k'.base hw |>.symm)
    have ha₀ : e.symm a ∈ M := ha
    have ea : a = p.app (Y.basicOpen f) (e.symm a) := (e.apply_symm_apply a).symm
    intro hmem
    rw [ea, ← Scheme.preimage_basicOpen] at hmem
    have : k' ((k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι w) = (p ⁻¹ᵁ Y.basicOpen f).ι z₀ := by
      rw [← hz']; exact congrArg k'.base hw
    rw [this] at hmem
    have hmem' : p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) ∈ Y.basicOpen (e.symm a) := hmem
    rw [hz₀] at hmem'
    exact (hMiff _).1 ha₀ hmem'
  obtain ⟨V₃, hy₃, hV₃, hV₃u⟩ := GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap Z Y p hclp L _ u y₀ hf2 hfib
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section Z L hL (p ⁻¹ᵁ V₃) (p ⁻¹ᵁ Y.basicOpen f) (fun z hz => hV₃ hz) u
    (fun z hz => hV₃u z hz)
  exact ⟨V₃, hxy.mem_open V₃.isOpen hy₃, t, ht⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_transport_mumfordBundleIso : ∀ (SB SC : Scheme.{0}) (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (M : LB B.left) (N : LB C.left), M.IsLB → N.IsLB → ∀ (m : (G2 B).left ⟶ (G2 C).left) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen → ∀ (T : Over SB) (T₀ : Over SC) (x y : T ⟶ B) (x₀ y₀ : T₀ ⟶ C) (h : T.left ⟶ T₀.left), (lift x y).left ≫ m = h ≫ (lift x₀ y₀).left → ∀ t₀ : LB.Gen (LB.LinComb N (lamPts x₀ y₀) negε), t₀.IsGen → ∃ u : LB.Gen (LB.LinComb M (lamPts x y) negε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good N z J → Good M z J' → val u r z J' = lamVal w (r ≫ (lift x y).left) z J J' * val t₀ (r ≫ h) z J := by
  first | exact @GlobalTheory.GenTransport.gen_transport | exact GlobalTheory.GenTransport.gen_transport | (intros; apply GlobalTheory.GenTransport.gen_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointOfLiesOverGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoint_of_lies_over_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (M' : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (ξ : Sp W ⟶ M'.S), Function.Injective φ → ξ ≫ M'.π = spMap φ → ∃ (w : Sp W) (k : Sp (FractionRing R)), ξ w = M'.gp k := by
  first | exact @GlobalTheory.Mum.modif_pt_over_gen | exact GlobalTheory.Mum.modif_pt_over_gen | (intros; apply GlobalTheory.Mum.modif_pt_over_gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsUniformisationsWeilPairingGalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoints_uniformisations_weilPairing_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
      ∃ e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A),
        (∀ (k : ℕ) (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) ∧
        (∀ (σ : F →ₐ[FractionRing V] F) (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) ∧
        ∀ x : TFK (R := V) F ⟶ A'.A, (e x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := by
  first | exact @GlobalTheory.GenRestrict.exists_genericPoints_equiv_any | exact GlobalTheory.GenRestrict.exists_genericPoints_equiv_any | (intros; apply GlobalTheory.GenRestrict.exists_genericPoints_equiv_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedLineBundleSectionOverCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glued_lineBundleSection_over_cover : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  first | exact @GlobalTheory.UMin.ThBdl.locSec_glue | exact GlobalTheory.UMin.ThBdl.locSec_glue | (intros; apply GlobalTheory.UMin.ThBdl.locSec_glue <;> assumption)
end

