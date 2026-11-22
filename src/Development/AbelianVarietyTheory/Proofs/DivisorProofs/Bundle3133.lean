import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDet
section
namespace GlobalTheory
open Polynomial

theorem aeval_int_eq_eval₂ {A : Type} [Ring A] [inst : Algebra ℤ A] (x : A) (R : ℤ[X]) :
    @aeval ℤ A _ _ inst x R = eval₂ (Int.castRingHom A) x R := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

theorem prod_aeval_aroots_padic_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  intro p _ S _ _ N _ _ _ _ ψ u P R d hψ hP hd
  let K := FractionRing S
  have hg : Function.Injective ((algebraMap S K).comp ψ) :=
    (IsFractionRing.injective S K).comp hψ
  let ψ' : ℚ_[p] →+* K := IsFractionRing.lift hg
  have hψ' : ψ'.comp (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap S K).comp ψ :=
    IsLocalization.lift_comp _
  let Ω := AlgebraicClosure K
  letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp ψ').toAlgebra
  have hΩ : algebraMap ℚ_[p] Ω = (algebraMap K Ω).comp ψ' := rfl
  let j : PadicAlgCl p →ₐ[ℚ_[p]] Ω := IsAlgClosed.lift
  have hj : Function.Injective j := j.toRingHom.injective
  let uK : Module.End K (TensorProduct S K N) := u.baseChange K
  have key := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' K Ω (TensorProduct S K N) uK (R.map (Int.castRingHom K))
  have hF : ∀ {A : Type} [Ring A] [Algebra K A] (x : A), aeval x (R.map (Int.castRingHom K)) = aeval x R := by
    intro A _ _ x
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  simp only [hF] at key
  have hbc : aeval uK R = (aeval u R).baseChange K := by
    have := aeval_algHom_apply (Module.End.baseChangeHom S K N).toRingHom.toIntAlgHom u R
    exact this
  rw [hbc, LinearMap.det_baseChange, hd] at key
  have hch : uK.charpoly.aroots Ω = (P.map (algebraMap ℤ_[p] ℚ_[p])).aroots Ω := by
    rw [LinearMap.charpoly_baseChange, ← hP, aroots_def, aroots_def, map_map, map_map, map_map, hΩ]
    simp only [RingHom.comp_assoc, hψ']
  rw [hch] at key
  apply hj
  set Q := P.map (algebraMap ℤ_[p] ℚ_[p])
  have hroots : Q.aroots Ω = (Q.aroots (PadicAlgCl p)).map j := by
    have h := (IsAlgClosed.splits (Q.map (algebraMap ℚ_[p] (PadicAlgCl p)))).roots_map (j : PadicAlgCl p →+* Ω)
    rw [map_map, AlgHom.comp_algebraMap] at h
    rw [aroots_def, aroots_def, h]
    rfl
  rw [hroots, Multiset.map_map] at key
  rw [map_multiset_prod, Multiset.map_map, AlgHom.commutes]
  simp only [aeval_int_eq_eval₂] at key ⊢
  have e1 : ∀ a : PadicAlgCl p, j (eval₂ (Int.castRingHom _) a R) = eval₂ (Int.castRingHom Ω) (j a) R := by
    intro a
    change (j : PadicAlgCl p →+* Ω) (eval₂ (Int.castRingHom _) a R) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  simp only [Function.comp_def, e1] at key ⊢
  refine key.symm.trans ?_
  rw [hΩ, RingHom.comp_apply]
  congr 1
  exact (RingHom.congr_fun hψ' d).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdUnit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnifUnit

theorem prod_unit {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T₀ : Over (Sp R)} (r : T₀ ⟶ T)
    (P : T ⟶ D.P.A) (h : r ≫ P = 1) (χ : D.X) {U : Type} [CommGroup U] (f : (T₀.left ⟶ D.P.A.left) → U) :
    ∏ k, f (r.left ≫ D.Oφ P χ k) ^ Oinvε k = 1 := by
  have e : ∀ k, r.left ≫ D.Oφ P χ k = D.Oφ (1 : T₀ ⟶ D.P.A) χ k := fun k => by
    rw [← h]; exact (WeightPf.Oφ_comp r P χ k).trans rfl
  have e₀ : D.Oφ (1 : T₀ ⟶ D.P.A) χ 0 = D.Oφ (1 : T₀ ⟶ D.P.A) χ 1 :=
    congrArg (fun m : T₀ ⟶ D.P.A => m.left) (_root_.one_mul (toUnit T₀ ≫ D.c χ))
  have e₂ : D.Oφ (1 : T₀ ⟶ D.P.A) χ 2 = D.Oφ (1 : T₀ ⟶ D.P.A) χ 3 := rfl
  simp only [e]
  rw [Fin.prod_univ_four, e₀, e₂]
  simp [Oinvε]

theorem unit_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (S : Scheme.{0}) (s : S ⟶ Sp R) (G G₁ G₂ : Over S) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (σ₁ : G ⟶ G₁) (σ₂ : G ⟶ G₂) (P : (Over.map s).obj G ⟶ D.P.A) (P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A) (P₂ : (Over.map s).obj G₂ ⟶ D₂.P.A) (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ (q₁ χ)) Oinvε)) (t₂ : LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ (q₂ χ)) Oinvε)), IsMonHom σ₁ → IsMonHom σ₂ → IsBoxGen (Y := G.left) (Y₁ := G₁.left) (Y₂ := G₂.left) w σ₁.left σ₂.left t t₁ t₂ → (Over.map s).map η[G] ≫ P = 1 → LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ t₁ (eSec G₁)) (LB.oneGen D₁.P.L) → LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ t₂ (eSec G₂)) (LB.oneGen D₂.P.L) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec G)) (LB.oneGen D.P.L) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ w S s G G₁ G₂ _ _ _ σ₁ σ₂ P P₁ P₂ χ t t₁ t₂ h₁ h₂ H e u₁ u₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have v := H _ (eSec G) y J₁ J₂ J hJ₁ hJ₂ hJ
  have o := prod_unit D ((Over.map s).map η[G]) P e χ (om w y J₁ J₂ J)
  have a₁ : eSec G ≫ σ₁.left = 𝟙 _ ≫ eSec G₁ := (SumDeg.eSec_comp σ₁).trans (Category.id_comp _).symm
  have a₂ : eSec G ≫ σ₂.left = 𝟙 _ ≫ eSec G₂ := (SumDeg.eSec_comp σ₂).trans (Category.id_comp _).symm
  have b₁ : val t₁ (eSec G ≫ σ₁.left) y J₁ = 1 := (congrArg (fun r => val t₁ r y J₁) a₁).trans
    ((val_pull hJ₁ _ _ _).symm.trans ((val_corr hJ₁ u₁ (𝟙 _)).trans (val_one _)))
  have b₂ : val t₂ (eSec G ≫ σ₂.left) y J₂ = 1 := (congrArg (fun r => val t₂ r y J₂) a₂).trans
    ((val_pull hJ₂ _ _ _).symm.trans ((val_corr hJ₂ u₂ (𝟙 _)).trans (val_one _)))
  have c : val t (eSec G) y J = 1 :=
    ((congrArg₂ (· * ·) o rfl).trans (_root_.one_mul _)).symm.trans
      (v.trans ((congrArg₂ (· * ·) b₁ b₂).trans (_root_.one_mul _)))
  exact (val_pull hJ _ _ _).trans ((congrArg (fun r => val t r y J) (Category.id_comp _)).trans
    (c.trans (val_one _).symm))

end GlobalTheory.ProdUnifUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartCoordinateRatioMemModelRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_chart_coordinate_ratio_mem_model_ring : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (a : Fin (n + 1)) (z : M.Z), PCrd (M.pt ≫ h) c → z ∈ h ⁻¹ᵁ chart k n a → c a ≠ 0 ∧ ∀ z' ∈ h ⁻¹ᵁ chart k n a, ∀ b, c b / c a ∈ M.O z' := by
  first | exact @GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O | exact GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O | (intros; apply GlobalTheory.UMin.ChartDiv.chart_ratio_mem_O <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGramFlagCellFrame
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullGram_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ z : CxPts Y.str σ, InCell E E' φ f A u (under z) → pullGram E H φ f hf (upM u * A.map φ) z = fun τ => upM (fun j => ratVal (u j) z) τ * H A (ptMap σ f hf z) τ * (upM (fun j => ratVal (u j) z) τ)ᴴ := by
  intro F _ σ X Y ι _ m E E' φ f hf hR _c A u H hH z hz
  obtain ⟨hA, hB⟩ := hz
  funext τ
  rw [(GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH z).2 A hA _ hB τ]
  have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := fun τ => by
    change ((A τ).map φ).det ≠ 0
    have := RingHom.map_det (φ : X.Fn →+* Y.Fn) (A τ)
    rw [RingHom.mapMatrix_apply] at this
    change ((A τ).map (φ : X.Fn →+* Y.Fn)).det ≠ 0
    rw [← this]
    exact (map_ne_zero _).2 (Fr.det_ne hA τ)
  have e : upM u * A.map φ * (A.map φ)⁻¹ = upM u := by rw [mul_assoc, Mat.mul_inv hd, mul_one]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have h0 : ratVal (0 : Y.Fn) z = 0 := by simpa using hψ 0
  have h1 : ratVal (1 : Y.Fn) z = 1 := by simpa using hψ 1
  have hv : (upM u).map (ratVal · z) τ = upM (fun j => ratVal (u j) z) τ := by
    ext a b
    simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [h0, h1]
  rw [e, hv]

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackAevalEvenComplexFormsStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_aeval_evenComplexForms : ∀ (n n' : ℕ) (L : V n →L[ℂ] V n') (κ : Type) (w : κ → Ev n) (w' : κ → Ev n') (P : MvPolynomial κ ℂ), (∀ x, (w x : Alt n) = pull L (w' x : Alt n')) → ((aeval w P : Ev n) : Alt n) = pull L ((aeval w' P : Ev n') : Alt n') := by
  first | exact @GlobalTheory.FlagCell2.pull_aeval_even | exact GlobalTheory.FlagCell2.pull_aeval_even | (intros; apply GlobalTheory.FlagCell2.pull_aeval_even <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapCompLinearStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackComplexFormsLinearMap_comp_linear : ∀ (n n' n'' : ℕ) (L : V n →L[ℂ] V n') (L' : V n' →L[ℂ] V n'') (α : Alt n''), pull (L'.comp L) α = pull L (pull L' α) := by
  first | exact @GlobalTheory.FlagCell2.pull_comp_linear | exact GlobalTheory.FlagCell2.pull_comp_linear | (intros; apply GlobalTheory.FlagCell2.pull_comp_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIsoBaseChangeOverReducedClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_residue_apply_eq_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (w : Sp (ResidueField R)) :
    spMap (residue R) w = closedPoint R :=
  IsLocalRing.PrimeSpectrum.comap_residue _ _

theorem pullbackLeftPullbackSnd_congr_fst {X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (g'' : W ⟶ Z)
    (hg : g' ≫ g = g'') :
    (pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg).hom ≫ pullback.fst f g'' =
      pullback.fst _ _ ≫ pullback.fst f g := by
  subst hg
  simp [pullback.map]

theorem pullbackLeftPullbackSnd_congr_snd {X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (g'' : W ⟶ Z)
    (hg : g' ≫ g = g'') :
    (pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg).hom ≫ pullback.snd f g'' = pullback.snd _ _ := by
  subst hg
  simp [pullback.map]

theorem Emb.pullback_iso_of_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    (G' : Over S) [GrpObj G'] (hG : Smooth G'.hom) (E : Emb π G') (T : Scheme.{0}) (t : T ⟶ S)
    (k : T ⟶ Sp (ResidueField R)) (_hT : IsLocallyNoetherian T) (hTr : IsReduced T)
    (htk : t ≫ π = k ≫ spMap (residue R)) :
    ∃ (e : pullback G'.hom t ≅ pullback E.Y.hom k) (l : pullback G'.hom t ⟶ E.H.toScheme),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ l ≫ E.H.ι = pullback.fst _ _ ∧
      l ≫ E.f = e.hom ≫ pullback.fst _ _ ≫ E.j := by
  haveI := hG
  haveI : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
  haveI : IsImmersion E.j := E.imm
  haveI : Smooth E.Y.hom := E.smooth
  have hclosed : ∀ w : (pullback G'.hom t : Scheme.{0}), π (G'.hom (pullback.fst G'.hom t w)) = closedPoint R := by
    intro w
    have h1 : π (G'.hom (pullback.fst G'.hom t w)) = (pullback.fst G'.hom t ≫ G'.hom ≫ π) w := by simp
    rw [h1, pullback.condition_assoc, htk]
    simp only [Scheme.Hom.comp_apply]
    exact spMap_residue_apply_eq_closedPoint R _
  have hrng : Set.range (pullback.fst G'.hom t) ⊆ Set.range E.H.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact E.H_all _ (hclosed w)
  let l : pullback G'.hom t ⟶ E.H.toScheme := IsOpenImmersion.lift E.H.ι (pullback.fst G'.hom t) hrng
  have hl : l ≫ E.H.ι = pullback.fst G'.hom t := IsOpenImmersion.lift_fac _ _ _
  haveI : IsReduced (pullback G'.hom t) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G'.hom t)
  have hrj : Set.range (l ≫ E.f) ⊆ Set.range E.j := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R S π G' E).1 (l w) (by
      have e1 : E.H.ι (l w) = pullback.fst G'.hom t w := by rw [← Scheme.Hom.comp_apply, hl]
      rw [e1]; exact hclosed w)
    exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_of_isReduced_of_isImmersion_range _ _ _ (l ≫ E.f) E.j inferInstance E.imm hrj
  have hgY : g ≫ E.Y.hom = pullback.snd G'.hom t ≫ k := by
    rw [← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, reassoc_of% hg, E.f_over,
      reassoc_of% hl, pullback.condition_assoc, htk, Category.assoc]
  let h : pullback G'.hom t ⟶ pullback E.Y.hom k := pullback.lift g (pullback.snd G'.hom t) hgY
  have hh : h ≫ pullback.snd E.Y.hom k = pullback.snd G'.hom t := pullback.lift_snd _ _ _
  have hhf : h ≫ pullback.fst E.Y.hom k = g := pullback.lift_fst _ _ _
  haveI : IsIso h := by
    refine GlobalTheory.T.isIso_of_isIso_on_geometric_fibres_of_smooth T _ _ (pullback.snd G'.hom t) (pullback.snd E.Y.hom k) h hh inferInstance inferInstance ?_
    intro s
    let Ω := T.residueField s
    let x0 : Sp Ω ⟶ T := T.fromSpecResidueField s
    have hx : ∀ w, (x0 ≫ t ≫ π) w = closedPoint R := by
      intro w
      rw [htk]
      simp only [Scheme.Hom.comp_apply]
      exact spMap_residue_apply_eq_closedPoint R _
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x0 ≫ t ≫ π) hx
    have hκk : x0 ≫ k = spMap κ := by
      rw [← cancel_mono (spMap (residue R)), Category.assoc, ← htk, hκ]
      simp only [spMap, ← Spec.map_comp]
      rfl
    obtain ⟨Ω', _, io, e', l', -, hl1, hl2⟩ := E.fib Ω (x0 ≫ t) κ (by rw [Category.assoc]; exact hκ)
    let x : Sp Ω' ⟶ T := spMap io ≫ x0
    refine ⟨Ω', inferInstance, x, ?_, ?_⟩
    · let w : Sp Ω' := closedPoint Ω'
      refine ⟨w, ?_⟩
      show (spMap io ≫ T.fromSpecResidueField s) w = s
      rw [Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    · have hxk : x ≫ k = spMap (io.comp κ) := by
        simp only [x, Category.assoc, hκk, spMap, ← Spec.map_comp]
        rfl
      let α : pullback (pullback.snd G'.hom t) x ≅ pullback G'.hom (spMap io ≫ x0 ≫ t) :=
        pullbackLeftPullbackSndIso G'.hom t x ≪≫ pullback.congrHom rfl (Category.assoc _ _ _)
      let β : pullback (pullback.snd E.Y.hom k) x ≅ pullback E.Y.hom (spMap (io.comp κ)) :=
        pullbackLeftPullbackSndIso E.Y.hom k x ≪≫ pullback.congrHom rfl hxk
      have hα : α.hom ≫ pullback.fst G'.hom (spMap io ≫ x0 ≫ t) =
          pullback.fst (pullback.snd G'.hom t) x ≫ pullback.fst G'.hom t :=
        pullbackLeftPullbackSnd_congr_fst _ _ _ _ _
      have hαs : α.hom ≫ pullback.snd G'.hom (spMap io ≫ x0 ≫ t) = pullback.snd (pullback.snd G'.hom t) x :=
        pullbackLeftPullbackSnd_congr_snd _ _ _ _ _
      have hβ : β.hom ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) =
          pullback.fst (pullback.snd E.Y.hom k) x ≫ pullback.fst E.Y.hom k :=
        pullbackLeftPullbackSnd_congr_fst _ _ _ _ _
      have hβs : β.hom ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd (pullback.snd E.Y.hom k) x :=
        pullbackLeftPullbackSnd_congr_snd _ _ _ _ _
      have hll : pullback.fst (pullback.snd G'.hom t) x ≫ l = α.hom ≫ l' := by
        rw [← cancel_mono E.H.ι, Category.assoc, Category.assoc, hl, hl1, hα]
      have he's : e'.hom.left ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd G'.hom (spMap io ≫ x0 ≫ t) :=
        Over.w e'.hom
      let eb := α ≪≫ (Over.forget _).mapIso e' ≪≫ β.symm
      have key0 : ∀ φ : pullback (pullback.snd G'.hom t) x ⟶ pullback (pullback.snd E.Y.hom k) x,
          φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ h → φ ≫ pullback.snd _ _ = pullback.snd _ _ → φ = eb.hom := by
        intro φ hφ hφs
        have heb : eb.hom = α.hom ≫ e'.hom.left ≫ β.inv := rfl
        rw [heb, ← Category.assoc, Iso.eq_comp_inv]
        apply pullback.hom_ext
        · rw [← cancel_mono E.j, Category.assoc, Category.assoc, reassoc_of% hβ, Category.assoc, Category.assoc,
            ← hl2, ← reassoc_of% hll, reassoc_of% hφ, reassoc_of% hhf, hg]
        · rw [Category.assoc, Category.assoc, hβs, he's, hαs, hφs]
      rw [key0 (pullback.map _ x _ x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))]
      infer_instance
  exact ⟨asIso h, l, hh, hl, by rw [asIso_hom, reassoc_of% hhf, hg]⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsDiagMemMaximalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulled_back_period_constants_diag_mem_maximal : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V₁, w ≠ 0 ∧ (q a a : FractionRing V₁) = algebraMap V₁ _ w := by
  first | exact @GlobalTheory.PeriodPos.periods_pos_diag | exact GlobalTheory.PeriodPos.periods_pos_diag | (intros; apply GlobalTheory.PeriodPos.periods_pos_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllIsAlgebraicHfunTwist
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam

theorem qAll_isAlgebraic_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (y : Fin 2 → ZMod N), y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QAll (IsAlgebraic ℚ) N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hF s N _ L hs hL z hz κ y hy α
  have hy' : vmul y α ≠ 0 := fun h => hy (((GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.2.2.2.1 y α).1 h)
  exact GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients hE F hF s N _ hs (Nat.pos_of_ne_zero (NeZero.ne N)) (GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L _ hL) z hz κ _
    ((GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion N (vmul y α)).2.2 hy')

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterTrivialUnitIdeles
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EtaFinUnit

theorem quadChar_finPartI_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ b : Neutral.B1.Ideles (maximalRealSubfield E),
    b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (GlobalTheory.GalOfCusp.quadChar E).1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 := by
  intro E _ _ _ hU b hb
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E),
      w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) (GlobalTheory.GalOfCusp.quadChar E).1
    (GlobalTheory.GalOfCusp.quadChar E).2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hb) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hb v
  obtain ⟨w, rfl⟩ := hs v
  exact GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt E w (hU w) x hxu

end GlobalTheory.EtaFinUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPeriodNormalisedJetModularTransform
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma length_word_eq_sum {I : Type} [Fintype I] (κ : I → ℕ) :
    (_root_.GlobalTheory.HilbFam.word κ).length = ∑ i, κ i := by
  unfold _root_.GlobalTheory.HilbFam.word
  simp [List.length_flatMap, Finset.sum_toList]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma lineDeriv_const_mul_comp_smul {I : Type} (f : (I → ℂ) → ℂ) (a c : ℂ)
    (z v : I → ℂ) :
    lineDeriv ℂ (fun z => a * f (c • z)) z v = a * c * lineDeriv ℂ f (c • z) v := by
  simp only [lineDeriv]
  have h : (fun t : ℂ => a * f (c • (z + t • v))) =
      fun t => a * (fun s : ℂ => f (c • z + s • v)) (c * t) := by
    funext t
    simp only [smul_add, smul_smul, mul_comm c t]
  rw [h]
  calc deriv (fun t => a * (fun s : ℂ => f (c • z + s • v)) (c * t)) 0
      = a * deriv (fun t => (fun s : ℂ => f (c • z + s • v)) (c * t)) 0 := by
        rw [deriv_const_mul_field']
    _ = a * (c • deriv (fun s : ℂ => f (c • z + s • v)) (c * 0)) :=
        congrArg (a * ·) (deriv_comp_mul_left c (fun s : ℂ => f (c • z + s • v)) 0)
    _ = a * c * deriv (fun t : ℂ => f (c • z + t • v)) 0 := by
        rw [mul_zero, smul_eq_mul, mul_assoc]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma iterD_comp_smul {I : Type} [DecidableEq I] (c : ℂ)
    (u : List I) (f : (I → ℂ) → ℂ) (z : I → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u (fun z => f (c • z)) z =
      c ^ u.length * _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u f (c • z) := by
  induction u generalizing z with
  | nil => simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD]
  | cons i u ih =>
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD, List.foldr_cons] at ih ⊢
    rw [show List.foldr _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD (fun z => f (c • z)) u =
      fun z => c ^ u.length * List.foldr _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD f u (c • z) from funext ih]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.partialD
    rw [lineDeriv_const_mul_comp_smul, List.length_cons, pow_succ]

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma jet_mul_eq_pow_sum_mul {F : Type} [Field F] [NumberField F] (k : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (τ c t lam : ℂ) :
    _root_.GlobalTheory.HilbFam.jet k L κ τ (lam * c) (lam * t) =
      lam ^ (∑ i, κ i) * _root_.GlobalTheory.HilbFam.jet k L κ τ c t := by
  unfold _root_.GlobalTheory.HilbFam.jet
  rw [← length_word_eq_sum κ, ← smul_zero lam,
    ← iterD_comp_smul]
  congr 1
  · funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 2 <;> funext i <;> ring
  · exact smul_zero lam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.hfun_slash : _root_.GlobalTheory.LatJet.EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F), 1 ≤ s → 0 < N → _root_.GlobalTheory.HilbFam.HasLevel N L → ∀ (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (Ch Ch' : ℍ → ℂ) (τ : ℍ), (∃ L', _root_.GlobalTheory.HilbFam.HasLevel N L' ∧ L' = _root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) → Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch' τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I) → _root_.GlobalTheory.HilbFam.hfun (2 * s) L κ Ch (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ _root_.GlobalTheory.HilbFam.wt (2 * s) κ * _root_.GlobalTheory.HilbFam.hfun (2 * s) (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ Ch' τ := by
  intro _ F _ _ _ _ s N L _ _ _ κ γ Ch Ch' τ _ hCh
  have hP : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [_root_.GlobalTheory.HilbFam.hfun]
  rw [_root_.GlobalTheory.HilbFam.JetModular.jet_smul F (2 * s) L κ γ τ _ _ (even_two_mul s)]
  set j : ℂ := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) with hj
  set P : ℂ := 2 * Real.pi * Complex.I with hPdef
  have hc : P ^ 2 * Ch (γ • τ) - -P * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * j =
      j ^ 2 * (P ^ 2 * Ch' τ) := by
    rw [hCh]
    field_simp
    ring
  rw [hc, show -P * j ^ 2 = j ^ 2 * -P by ring, jet_mul_eq_pow_sum_mul,
    _root_.GlobalTheory.HilbFam.wt, ← pow_mul, pow_add j]
  ring

end GlobalTheory.HilbFam
end

