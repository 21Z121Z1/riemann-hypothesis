import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficients
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TrCoef

theorem exists_nestSec {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2))) :
    ∃ T : LB.Sec (LB.LinComb (LB.LinComb L F ε) ψ δ), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (I : (Z ⟶ X) → L.ι), Good L z I → sval T r z (fun χ j => I (χ ≫ F j)) = sval s r z I := by
  have le : ∀ q : K → J → L.ι, LB.wchart (LB.LinComb L F ε) ψ q ≤
      LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => q p.1 p.2) := fun q y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  have v : ∀ (q : K → J → L.ι) (y : Y) (hy : y ∈ LB.wchart (LB.LinComb L F ε) ψ q),
      gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2)) =
        gs (𝟙 Y) y _ (s.f fun p => q p.1 p.2) := fun q y hy => gs_res _ y (le q) hy _
  refine ⟨⟨fun q => (Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2),
    fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z I hI => ?_⟩
  · have htr : trF (L := LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' =
        trF (L := L) (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2) (𝟙 Y) y
          (fun p => q p.1 p.2) (fun p => q' p.1 p.2) := by
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
        (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (q k) (q' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k))).trans ?_
      simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
    refine ((gs_res (𝟙 Y) y _ hy _).trans (v q y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb (LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (v q' y hy.2)))).symm)
    refine (sec_trans s (𝟙 Y) y (le q hy.1) (le q' hy.2)).trans ?_
    rw [← htr]
    rfl
  · have hI' : Good (LB.LinComb L F ε) z (fun χ j => I (χ ≫ F j)) := fun χ => hI.mem F χ
    have hm := hI'.mem ψ r
    rw [sval_of s r z I (fun p => I ((r ≫ ψ p.1) ≫ F p.2)) (fun p => by rw [Category.assoc])]
    exact gs_res r z (le _) hm _

end GlobalTheory.MumCmp.TrCoef

namespace GlobalTheory.MumCmp.TrCoef

theorem formEq_coef {R : Type} [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (g : GtPt D (𝟙_ (Over (Sp R)))) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k)
        (Sum.elim (fun k => (toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k)
          (fun k => (toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k)))
      (Sum.elim (DegPre.famε 1) (Sum.elim DegPre.gtε ![-1, 1]))
      (fun p : Fin 4 × Fin 3 => D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2)
      (fun p => DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) := by
  intro U _ h
  have hu : ∀ x : D₂.P.A ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit D₂.P.A := fun x => toUnit_unique _ _
  have ht : ∀ x : D₂.P.A ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit D₂.P.A ≫ g.b)).left * (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ g.b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.famφB χ₂ k = ((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
      Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2) ^
      (DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
        Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k ≫ β) * (toUnit D₂.P.A ≫ g.b)).left *
        (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left) ^ DegPre.famε 1 k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (DegPre.famε 1 k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have hL1 : ∏ k, h (GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k) ^ DegPre.famε 1 k =
      h ((β * (toUnit D₂.P.A ≫ g.b)) * (toUnit D₂.P.A ≫ D.c χ)).left * (h (toUnit D₂.P.A ≫ D.c χ).left)⁻¹ *
        h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ 𝟙 D.P.A).left ^ (((1 : ℕ) : ℤ) - 1) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ (𝟙 D.P.A * (toUnit D.P.A ≫ D.c χ))).left ^ (1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ D.c χ).left ^ (-1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      toUnit_unique ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A) (toUnit D₂.P.A)]
    simp only [Nat.cast_one, sub_self, zpow_zero, _root_.one_mul, zpow_one, zpow_neg_one]
    rfl
  have hL2 : ∏ k, h ((toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k) ^ DegPre.gtε k =
      (h ((toUnit D₂.P.A ≫ D.c χ) * (toUnit D₂.P.A ≫ g.b)).left)⁻¹ * h (toUnit D₂.P.A ≫ D.c χ).left *
        h (toUnit D₂.P.A ≫ g.b).left * (h (1 : D₂.P.A ⟶ D.P.A).left)⁻¹ := by
    rw [Fin.prod_univ_four]
    show h (toUnit D₂.P.A ≫ ((toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ) * g.b)).left ^ (-1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ g.b).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ η[D.P.A]).left ^ (-1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc (toUnit D₂.P.A), ← Category.assoc (toUnit D₂.P.A),
      toUnit_unique (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R)))) (toUnit D₂.P.A)]
    simp only [zpow_one, zpow_neg_one]
    rfl
  have hL3 : ∏ k, h ((toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k) ^ (![-1, 1] : Fin 2 → ℤ) k =
      (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_two]
    show h (toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) * h (toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [zpow_one, zpow_neg_one]
    rfl
  have h0 : (𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂)) ≫ β = β * (toUnit D₂.P.A ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.id_comp, Category.assoc, hc]
  have h2 : (toUnit D₂.P.A ≫ D₂.c χ₂) ≫ β = toUnit D₂.P.A ≫ D.c χ := by rw [Category.assoc, hc]
  have h3 : (1 : D₂.P.A ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hL1, hL2, hL3, hA, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Category.id_comp, h0, h2, h3, _root_.one_mul]
  rw [mul_right_comm β (toUnit D₂.P.A ≫ D.c χ)]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_translated_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  intro R _ _ D D₂ β hβ g xe hc w hw ν hν f
  have key : ∀ χ : D₂.X, ∃ f₂ : D₂.SecB 1 χ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι),
      Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' →
      Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval f₂ r z J' := by
    intro χ
    haveI := hβ
    let u := LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit D₂.P.A).left)
      (LB.pullGen D.P.L _ _ ν (toUnit D₂.P.A).left)
    have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.isGen _) _)
      (DVR.pullGen_isGen _ _ _ _ hν _)
    let S := pullMulSec (f (xe χ)) (GlobalTheory.MumCmp.twφ D₂ D β g.b 0) u hu
    obtain ⟨S', hS'⟩ := exists_sec D.P.isLB (formEq_coef D D₂ β g χ (xe χ) (hc χ)) S
    obtain ⟨T, hT⟩ := exists_nestSec (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε (D₂.famφB χ) (DegPre.famε 1) S'
    have hA := LB.isLB_linComb D₂.P.isLB (D₂.famφB χ) (DegPre.famε 1)
    have hB := LB.isLB_linComb (LB.isLB_linComb D.P.isLB (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε)
      (D₂.famφB χ) (DegPre.famε 1)
    have hU := DVR.linCombIso_isGen w hw (D₂.famφB χ) (DegPre.famε 1)
    refine ⟨DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB,
      fun Z r z J J' hJ hJ' => ?_⟩
    have hJ'' : Good (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε) z
        (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := fun χ' => hJ.mem _ χ'
    have m₁ := hJ'.mem (D₂.famφB χ) r
    have m₂ := hJ''.mem (D₂.famφB χ) r
    have e1 : Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
        Geo.Tor.sval T r z (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := by
      rw [hT Z r z J hJ, hS' Z r z J hJ, sval_pullMulSec _ _ _ hu r z hJ, val_mul hJ, val_pull hJ, val_pull hJ]
    rw [e1]
    have e2 := DVR.ps_gs_secOfIso (LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB
      (fun k => J' (r ≫ D₂.famφB χ k)) (fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) r z ⟨m₁, m₂⟩
    have e3 := DVR.ps_gm_linCombIso w (D₂.famφB χ) (DegPre.famε 1)
      ((fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)), (fun k => J' (r ≫ D₂.famφB χ k))) r z ⟨m₂, m₁⟩
    rw [show Geo.Tor.sval (DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB) r z J' = _ from e2,
      e3]
    exact (Units.mul_inv_cancel_left _ _).symm
  choose f₂ hf₂ using key
  exact ⟨f₂, hf₂⟩

end GlobalTheory.MumCmp.TrCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionDifferenceStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_pushoutTorsorSection_difference : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ (b : Fn0 A) (D : Type) [CommRing D] [Algebra R D] (x : Pt A D) (s s' : RootFn A D), IsSec n b x s → IsSec n b x s' → ∃! e : D, ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D'), z ^ n = spOver φ ≫ x → s D' φ z - s' D' φ z = φ e := by
  first | exact @GlobalTheory.PtExt.isSec_sub_existsUnique | exact GlobalTheory.PtExt.isSec_sub_existsUnique | (intros; apply GlobalTheory.PtExt.isSec_sub_existsUnique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionMulDifferenceStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_pushoutTorsorSection_mul_difference : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) (s s' s'' : RootFn A D), IsSec n b x s → IsSec n b y s' → IsSec n b (x * y) s'' → ∃! e : D, ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'), z ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y → s'' D' φ (z * w) - s D' φ z - s' D' φ w = φ e := by
  first | exact @GlobalTheory.sec_mul_diff | exact GlobalTheory.sec_mul_diff | (intros; apply GlobalTheory.sec_mul_diff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKillingSquareTripleFibreCocycleMulTwo
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

namespace GlobalTheory.TwoTors

theorem sq_symm_of_cocycle {G M : Type} [CommGroup G] [CommGroup M] (c : G → G → M)
    (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) (h2 : ∀ x : G, x ^ 2 = 1) (x y : G) :
    c x y ^ 2 = c y x ^ 2 := by
  let a : G → G → Additive M := fun x y => Additive.ofMul (c x y)
  have hca : ∀ x y z, a x y + a (x * y) z = a y z + a x (y * z) := fun x y z => by
    simp only [a, ← ofMul_mul, hc]
  let e : G → G → Additive M := fun x y => a x y - a y x
  have emul : ∀ x y z, e (x * y) z = e x z + e y z := by
    intro x y z
    have h₁ := hca x y z
    have h₂ := hca z x y
    have h₃ := hca x z y
    rw [mul_comm z x] at h₂
    rw [mul_comm z y] at h₃
    have e₁ : a (x * y) z = a y z + a x (y * z) - a x y := by rw [← h₁]; abel
    have e₂ : a z (x * y) = a z x + a (x * z) y - a x y := by rw [h₂]; abel
    have e₃ : a x z = a z y + a x (y * z) - a (x * z) y := by rw [← h₃]; abel
    simp only [e]
    rw [e₁, e₂, e₃]
    abel
  have hone : ∀ y, e 1 y = 0 := by
    intro y
    have h₁ := hca 1 1 y
    have h₂ := hca y 1 1
    simp only [_root_.one_mul, _root_.mul_one] at h₁ h₂
    have : a 1 1 = a 1 y := by
      have := congrArg (· - a 1 y) h₁; simpa using this
    have : a y 1 = a 1 1 := by
      have := congrArg (· - a y 1) h₂; simpa using this
    simp only [e]
    rw [sub_eq_zero]
    rw [← ‹a 1 1 = a 1 y›, ‹a y 1 = a 1 1›]
  have key : e x y + e x y = 0 := by
    rw [← emul, ← pow_two, h2, hone]
  apply Additive.ofMul.injective
  rw [ofMul_pow, ofMul_pow]
  change 2 • a x y = 2 • a y x
  rw [← sub_eq_zero, ← smul_sub, two_nsmul]
  exact key

theorem isFinite_two {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hf : IsFinite (sq A).left) :
    IsFinite (Two A).hom := by
  have h := (IsPullback.of_hasPullback (sq A) η[A]).map (Over.forget S)
  have h₂ : IsFinite (pullback.snd (sq A) η[A]).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) h hf
  rw [← Over.w (pullback.snd (sq A) η[A])]
  exact MorphismProperty.comp_mem @IsFinite _ _ h₂ (inferInstanceAs (IsFinite (𝟙 S)))

end GlobalTheory.TwoTors

namespace GlobalTheory.TwoTors

theorem pullTop_pullTop {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    GlobalTheory.CharKer.pullTop f (GlobalTheory.CharKer.pullTop g u) = GlobalTheory.CharKer.pullTop (f ≫ g) u := by
  ext; simp [GlobalTheory.CharKer.pullTop]; rfl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def inclHom (T : Over S) : (T ⟶ Two A) →* (T ⟶ A) := MonoidHom.mk' (· ≫ incl A) mul_incl

theorem comp_dif {T T' : Over S} (g : T' ⟶ T) (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) :
    g ≫ dif a b h = dif (g ≫ a) (g ≫ b) (by rw [Category.assoc, h, Category.assoc]) :=
  two_ext (by rw [Category.assoc, dif_incl, dif_incl, MonObj.comp_mul, GrpObj.comp_inv])

theorem dif_incl_incl {T : Over S} (u v : T ⟶ Two A) (h : (u ≫ incl A) ≫ sq A = (v ≫ incl A) ≫ sq A) :
    dif (u ≫ incl A) (v ≫ incl A) h = u⁻¹ * v :=
  two_ext (by
    rw [dif_incl]
    change (inclHom T u)⁻¹ * inclHom T v = inclHom T (u⁻¹ * v)
    rw [map_mul, map_inv])

theorem incl_sq_eq {T : Over S} (u v : T ⟶ Two A) : (u ≫ incl A) ≫ sq A = (v ≫ incl A) ≫ sq A := by
  rw [comp_sq, comp_sq, incl_sq, incl_sq]

theorem sq_eq_one {T : Over S} (x : T ⟶ Two A) : x ^ 2 = 1 := by
  have h : inclHom T (x ^ 2) = inclHom T 1 := by rw [map_pow, map_one]; exact incl_sq x
  exact two_ext h

def tpt {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) : T ⟶ tripO A :=
  Over.homMk (GlobalTheory.PolRoot.tri (sq A).left a.left b.left c.left (by rw [← Over.comp_left, h₁, Over.comp_left])
    (by rw [← Over.comp_left, h₂, Over.comp_left])) (by
      show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom = T.hom
      rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
      exact Over.w a)

theorem tpt_ψ {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) :
    tpt a b c h₁ h₂ ≫ ψ A = lift (dif a b h₁) (dif b c h₂) := by
  have e₁ : tpt a b c h₁ h₂ ≫ t₁ A = a := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = a.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst])
  have e₂ : tpt a b c h₁ h₂ ≫ t₂ A = b := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = b.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_snd])
  have e₃ : tpt a b c h₁ h₂ ≫ t₃ A = c := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ = c.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_snd_assoc, pullback.lift_snd])
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, ψ, lift_fst, lift_fst, comp_dif]; congr 1 <;> assumption
  · rw [Category.assoc, ψ, lift_snd, lift_snd, comp_dif]; congr 1 <;> assumption

variable (A)

theorem fst_δ : (pullback.fst _ _ : Triple (sq A).left ⟶ _) ≫ (δ A).left = (dif (t₁ A) (t₂ A) (t₁₂_sq A)).left := by
  have : (Over.homMk (pullback.fst _ _) rfl : tripO A ⟶ pairO A) ≫ δ A = dif (t₁ A) (t₂ A) (t₁₂_sq A) := by
    rw [δ, comp_dif]; congr 1 <;> exact Over.OverMorphism.ext rfl
  exact congrArg CommaMorphism.left this

theorem snd_δ : (pullback.snd _ _ : Triple (sq A).left ⟶ _) ≫ (δ A).left = (dif (t₂ A) (t₃ A) (t₂₃_sq A)).left := by
  have w₂ : (pullback.snd _ _ : Triple (sq A).left ⟶ _) ≫ (pairO A).hom = (tripO A).hom := by
    show pullback.snd _ _ ≫ pullback.fst _ _ ≫ A.hom = pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom
    rw [← pullback.condition_assoc, snd_w]
  have : (Over.homMk (pullback.snd _ _) w₂ : tripO A ⟶ pairO A) ≫ δ A = dif (t₂ A) (t₃ A) (t₂₃_sq A) := by
    rw [δ, comp_dif]; congr 1
    all_goals first
      | exact Over.OverMorphism.ext rfl
      | exact Over.OverMorphism.ext (pullback.condition (f := pullback.snd (sq A).left (sq A).left)).symm
  exact congrArg CommaMorphism.left this

theorem tripleFibreProjOneThree_comp_fiberProductMulTwoToTwoTorsion : pr13 (sq A).left ≫ (δ A).left =
    (dif (t₁ A) (t₂ A) (t₁₂_sq A) * dif (t₂ A) (t₃ A) (t₂₃_sq A)).left := by
  have w₃ : pr13 (sq A).left ≫ (pairO A).hom = (tripO A).hom := by
    show pr13 _ ≫ pullback.fst _ _ ≫ A.hom = pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom
    rw [pr13, pullback.lift_fst_assoc, Category.assoc]
  have a₁ : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ s₁ A = t₁ A :=
    Over.OverMorphism.ext (by show pr13 _ ≫ pullback.fst _ _ = _; rw [pr13, pullback.lift_fst]; rfl)
  have a₃ : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ s₂ A = t₃ A :=
    Over.OverMorphism.ext (by show pr13 _ ≫ pullback.snd _ _ = _; rw [pr13, pullback.lift_snd]; rfl)
  have : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ δ A =
      dif (t₁ A) (t₂ A) (t₁₂_sq A) * dif (t₂ A) (t₃ A) (t₂₃_sq A) := by
    rw [δ, comp_dif]
    apply two_ext
    rw [dif_incl, mul_incl, dif_incl, dif_incl, a₁, a₃]
    group
  exact congrArg CommaMorphism.left this

theorem killsSq_of (c : Γ((Two A ⊗ Two A).left, ⊤)ˣ) (w : Γ((Two A).left, ⊤)ˣ) (D : Γ(Triple (sq A).left, ⊤)ˣ)
    (hc : GlobalTheory.CharKer.pullTop (ψ A).left c = D)
    (hw : ∀ (T : Over S) (x y : T ⟶ Two A), GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) *
      GlobalTheory.CharKer.pullTop (x * y).left w = GlobalTheory.CharKer.pullTop x.left w * GlobalTheory.CharKer.pullTop y.left w) :
    KillsSq (sq A).left D (GlobalTheory.CharKer.pullTop (δ A).left w⁻¹) := by
  unfold KillsSq
  rw [pullTop_pullTop, pullTop_pullTop, pullTop_pullTop, fst_δ, snd_δ, tripleFibreProjOneThree_comp_fiberProductMulTwoToTwoTorsion, ← hc, map_inv, map_inv, map_inv]
  have H := hw (tripO A) (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))
  rw [map_pow] at H
  have hψ : (ψ A).left = (lift (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))).left := rfl
  rw [hψ, _root_.mul_assoc, ← _root_.mul_inv, ← H, _root_.mul_inv, mul_inv_cancel_left]

end GlobalTheory.TwoTors

open GlobalTheory.TwoTors in

theorem GlobalTheory.TwoTors.killsSq_of_triCocycle : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → IsFinite ((𝟙 A) ^ 2 : A ⟶ A).left → ∀ D : Γ(Triple ((𝟙 A) ^ 2 : A ⟶ A).left, ⊤)ˣ,
    TriCocycle ((𝟙 A) ^ 2 : A ⟶ A).left D → ∃ u, KillsSq ((𝟙 A) ^ 2 : A ⟶ A).left D u := by
  intro K _ _ A _ _ hA hf D hD
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_base_globalUnit_abelianScheme_baseChange A (Two A ⊗ Two A) hA (t₁ A).left (ψ A).left (GlobalTheory.T.tripleFiberProductOverMulTwo_isPullback A) D
  have key : ∀ {T : Over (Sp K)} (a b d : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = d ≫ sq A) p₁ p₂,
      GlobalTheory.CharKer.pullTop (tri (sq A).left a.left b.left d.left p₁ p₂) D =
        GlobalTheory.CharKer.pullTop (lift (dif a b h₁) (dif b d h₂)).left c := by
    intro T a b d h₁ h₂ p₁ p₂
    rw [← hc, pullTop_pullTop, ← tpt_ψ a b d h₁ h₂]
    rfl
  have hcoc : ∀ (T : Over (Sp K)) (x y z : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c =
        GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c := by
    intro T x y z
    have H := hD T.left ((1 : T ⟶ Two A) ≫ incl A).left (x ≫ incl A).left ((x * y) ≫ incl A).left
      ((x * y * z) ≫ incl A).left (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left])
      (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left]) (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left])
    rw [key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _), key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _),
      key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _), key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _)] at H
    simp only [dif_incl_incl] at H
    have e₁ : (1 : T ⟶ Two A)⁻¹ * x = x := by group
    have e₂ : x⁻¹ * (x * y) = y := by group
    have e₃ : (1 : T ⟶ Two A)⁻¹ * (x * y) = x * y := by group
    have e₄ : (x * y)⁻¹ * (x * y * z) = z := by group
    have e₅ : x⁻¹ * (x * y * z) = y * z := by group
    rw [e₁, e₂, e₃, e₄, e₅] at H
    exact H
  have hsym : ∀ (T : Over (Sp K)) (x y : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) = GlobalTheory.CharKer.pullTop (lift y x).left (c ^ 2) := by
    intro T x y
    rw [map_pow, map_pow]
    exact sq_symm_of_cocycle (fun x y : T ⟶ Two A => GlobalTheory.CharKer.pullTop (lift x y).left c) (hcoc T) sq_eq_one x y
  have hcoc2 : ∀ (T : Over (Sp K)) (x y z : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) * GlobalTheory.CharKer.pullTop (lift (x * y) z).left (c ^ 2) =
        GlobalTheory.CharKer.pullTop (lift y z).left (c ^ 2) * GlobalTheory.CharKer.pullTop (lift x (y * z)).left (c ^ 2) := by
    intro T x y z
    simp only [map_pow]
    rw [← mul_pow, ← mul_pow, hcoc]
  obtain ⟨w, hw⟩ := GlobalTheory.T.symmetricTwoCocycle_finiteCommGroupScheme_coboundary K (Two A) (isFinite_two A hf) (c ^ 2) hcoc2 hsym
  refine ⟨GlobalTheory.CharKer.pullTop (δ A).left w⁻¹, ?_⟩
  exact killsSq_of A c w D hc hw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleFourthPowerPolarisedAbelianFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_veryAmple_fourthPower_polarisedAbelian_field : AmpleSt → ∀ (K : Type) [Field K] (P : PolAV (Sp K)), ∃ (m : ℕ) (b : Fin (m + 1) → H0 P.L 4), VeryAmpleAlong P.A.hom (𝟙 P.A.left) P.L b := by
  first | exact @GlobalTheory.Mum.veryAmpleAlong_field | exact GlobalTheory.Mum.veryAmpleAlong_field | (intros; apply GlobalTheory.Mum.veryAmpleAlong_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilComparisonGeneratorOfLambdaBundleIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

theorem exists_cmpGen_of_lbIso (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A)
    (H : LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)
      (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)) :
    ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  obtain ⟨w, hw⟩ := H
  have h₁ := isPart_inl P₁.L P₂.L
  have h₂ := isPart_inr P₁.L P₂.L
  have le : ∀ j : KK → (join P₁.L P₂.L).ι, LB.wchart (join P₁.L P₂.L) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) j ≤
      (LB.div (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)
        (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)).U
        (fun k => (j (.inl k)).2, fun k => (j (.inr k)).1) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => (h₂.mem _ _).1 (Set.mem_iInter.1 hy (.inl k)),
      Set.mem_iInter.2 fun k => (h₁.mem _ _).1 (Set.mem_iInter.1 hy (.inr k))⟩
  let c : ChartPull (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)
      (LB.div (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)
        (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)) (𝟙 _) :=
    { idx := fun j => (fun k => (j (.inl k)).2, fun k => (j (.inr k)).1)
      le := le
      g := fun y j j' hj hj' => by
        refine (gm_linComb (join P₁.L P₂.L) _ _ (𝟙 _) y j j' hj hj').trans ?_
        refine Eq.trans ?_ (gm_div _ _ (𝟙 _) y _ _ ⟨le j hj, le j' hj'⟩).symm
        refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹)
          (gm_linComb P₂.L _ _ (𝟙 _) y _ _ (le j hj).1 (le j' hj').1)
          (gm_linComb P₁.L _ _ (𝟙 _) y _ _ (le j hj).2 (le j' hj').2)).symm
        rw [Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ _) ?_)
          (Finset.prod_congr rfl fun k _ => (zpow_neg _ _).trans (congrArg (fun u => (u ^ _)⁻¹) ?_))
        · refine Eq.trans ?_ (h₂.g _ (𝟙 _ ≫ (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] k.down).left) y _ _
            ((h₂.mem _ _).1 (Set.mem_iInter.1 hj (.inl k))) ((h₂.mem _ _).1 (Set.mem_iInter.1 hj' (.inl k))))
          simp only [cmpφ, Sum.elim_inl, Category.assoc]
        · refine Eq.trans ?_ (h₁.g _ (𝟙 _ ≫ (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] k.down).left) y _ _
            ((h₁.mem _ _).1 (Set.mem_iInter.1 hj (.inr k))) ((h₁.mem _ _).1 (Set.mem_iInter.1 hj' (.inr k))))
          simp only [cmpφ, Sum.elim_inr, Category.assoc] }
  exact ⟨cGen c w, cGen_isGen c hw⟩

end GlobalTheory.Mum.Two.WeilCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_secondScalar_determined_of_nonzero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∃ α j, (F.f α).f j ≠ 0) → ∀ a b b' : W, a ≠ 0 → T.Exp a b s F → T.Exp a b' s F → b = b' := by
  first | exact @GlobalTheory.Mum.Trait.exp_unique | exact GlobalTheory.Mum.Trait.exp_unique | (intros; apply GlobalTheory.Mum.Trait.exp_unique <;> assumption)
end

