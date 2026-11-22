import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0213
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0689
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFrameResidueStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_residue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (k : Type) [Field k] (ψ : Γ(Z.X, U) →+* k), (p : k) ≠ 0 → (∀ τ, Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (w.bc ψ τ)) ∧ Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (fun i : Fin (letters Dw).length => w.bc ψ ((letters Dw).get i).1 ((letters Dw).get i).2) := by
  first | exact @GlobalTheory.HTLine.GenInd.ind_generic | exact GlobalTheory.HTLine.GenInd.ind_generic | (intros; apply GlobalTheory.HTLine.GenInd.ind_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralAppOfUniversallyClosed
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenPush

theorem app_injective_of_dense {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by
  intro a b hab
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  have h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥ := by
    rw [Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨x, hx1, ⟨y, rfl⟩⟩ := hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩
  have : y ∈ j ⁻¹ᵁ Z.basicOpen (a - b) := hx1
  rw [h0] at this
  exact this

theorem isIntegral_of_isIso_comp {A B C D : CommRingCat.{0}} (k : A ⟶ B) (f : B ⟶ C) (m : C ⟶ D) [IsIso k]
    [IsIso m] (h : (k ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv k ≫ (k ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv k)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app_of_universallyClosed {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (U : Z₂.Opens) (hU : IsAffineOpen U) : (ρ.app U).hom.IsIntegral := by
  have : IsAffine U.toScheme := hU
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ U)
  rw [morphismRestrict_appTop] at h
  have e : U.ι ''ᵁ ⊤ = U := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (p : A = B), IsIso (eqToHom p) := fun p => by
    subst p; rw [eqToHom_refl]; infer_instance
  refine @isIntegral_of_isIso_comp _ _ _ _ _ _ _ ?_ ?_ h
  · exact hi _
  · exact hi _

theorem exists_app_eq_of_isIntegralElem {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z]
    (j : T ⟶ Z) [IsOpenImmersion j] (hj : Dense (Set.range j)) (U : Z.Opens)
    (s : Γ(T, j ⁻¹ᵁ U)) (hs : (j.app U).hom.IsIntegralElem s) : ∃ h : Γ(Z, U), j.app U h = s :=
  GlobalTheory.T.exists_section_extending_of_dense_openImmersion j hj U s fun u hu => GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme j hj U s hs u hu

theorem app_surjective_of_dense {T Z₁ Z₂ : Scheme.{0}} [IsReduced Z₁] [GlobalTheory.IsNormalScheme Z₂]
    [IsLocallyNoetherian Z₂] (j₁ : T ⟶ Z₁) (j₂ : T ⟶ Z₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h₁ : Dense (Set.range j₁)) (h₂ : Dense (Set.range j₂)) (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (hρ : j₁ ≫ ρ = j₂) (U : Z₂.Opens) (hU : IsAffineOpen U) : Function.Surjective (ρ.app U).hom := by
  subst hρ
  intro t
  have ht : (ρ.app U).hom.IsIntegralElem t := isIntegral_app_of_universallyClosed ρ U hU t
  have hs : ((j₁ ≫ ρ).app U).hom.IsIntegralElem (j₁.app (ρ ⁻¹ᵁ U) t) := by
    change ((j₁.app (ρ ⁻¹ᵁ U)).hom.comp (ρ.app U).hom).IsIntegralElem _
    exact RingHom.IsIntegralElem.map ht _
  obtain ⟨h, hh⟩ := exists_app_eq_of_isIntegralElem (j₁ ≫ ρ) h₂ U _ hs
  refine ⟨h, app_injective_of_dense j₁ h₁ (ρ ⁻¹ᵁ U) ?_⟩
  rw [← hh]
  rfl

section Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_gen_id (Y : Model Xo c (RingHom.id c.F)) : IsReduced (gen Y) := by
  haveI : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  haveI : IsIso (genι Y) := GlobalTheory.VarFlag.isIso_genι
  exact isReduced_of_isOpenImmersion (genι Y)

theorem comp_genStr (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) : ρ ≫ genStr X = genStr Y := by
  haveI := isReduced_gen_id Y
  haveI : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  refine ext_of_isDominant Y.jQ ?_
  rw [← Category.assoc, hρ, X.jQ_over, Y.jQ_over]

theorem isProper_of_jQ (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) : IsProper ρ := by
  haveI := isProper_genStr X
  haveI : IsProper (ρ ≫ genStr X) := (comp_genStr X Y ρ hρ) ▸ isProper_genStr Y
  exact IsProper.of_comp ρ (genStr X)

theorem app_surjective (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) (U : (gen X).affineOpens) : Function.Surjective (ρ.app U.1).hom := by
  obtain ⟨hN, hL⟩ := GlobalTheory.ModelRelCompare.normal_genericFibre X (GlobalTheory.ModelRelCompare.isDedFrac_in_use c).1
  haveI : GlobalTheory.IsNormalScheme (gen X) := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsLocallyNoetherian (gen X) := hL
  haveI := isReduced_gen_id Y
  haveI := isProper_of_jQ X Y ρ hρ
  haveI := Y.jQ_open
  haveI := X.jQ_open
  exact app_surjective_of_dense Y.jQ X.jQ Y.jQ_dense X.jQ_dense ρ hρ U.1 U.2

end Models

end GlobalTheory.GenPush

theorem GlobalTheory.GenPush.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X), Y.jQ ≫ ρ = X.jQ →
    ∀ U : (gen X).affineOpens, Function.Surjective (ρ.app U.1).hom :=
  fun _ _ _ _ _ _ _ _ _ X Y ρ hρ U => GlobalTheory.GenPush.app_surjective X Y ρ hρ U
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRatioSer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz GlobalTheory.RayRos
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRosEx

section Series

variable {S : Type} [CommRing S] {ρ : Type}

def ser3 (M : Fin 2 → Fin 3 → S) (F : MvPowerSeries (Fin 2 × ρ) S) : MvPowerSeries (Fin 3 × ρ) S :=
  MvPowerSeries.subst
    (fun p : Fin 2 × ρ => ∑ i : Fin 3, MvPowerSeries.C (M p.1 i) * MvPowerSeries.X (i, p.2)) F

def LawL (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ser3 ![![1, 1, 0], ![0, 0, 1]] F = ser3 ![![1, 0, 0], ![0, 0, 1]] F * ser3 ![![0, 1, 0], ![0, 0, 1]] F

def LawR (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ser3 ![![1, 0, 0], ![0, 1, 1]] F = ser3 ![![1, 0, 0], ![0, 1, 0]] F * ser3 ![![1, 0, 0], ![0, 0, 1]] F

end Series

section Ratio

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left) {O : Type} [CommRing O]

def IsRatioSer (bar : O → O) (ch : ρ → O →+* S) {x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G} (e : Fr x0 L x) (c : O)
    {φ : Fin 6 → ((G ⊗ G).left ⟶ G.left)} (w : LB.Gen (LB.LinComb L φ rosatiε))
    (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ∀ m y J, Good L y J → (val w (pt2 x0 x m).left y J).val * gs (𝟙 _) y ⊤ (toΓ _ (psJet m F)) =
    (ratio6 x0 L bar ch e c m y J).val

end Ratio

end GlobalTheory.RayRosEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStarOfOfCover
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarCells

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem inCone_of_strict {m' n : ℕ} {σ : Fin m' → LinearMap.BilinForm ℤ X} (hσs : IsStrict bar φ σ)
    (hσl : φ.LinearOn σ) {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X)
    (hβp : ∀ i y, 0 ≤ β i y y) {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (σ j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • σ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hσs
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (σ j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β σ) (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (σ j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ σ).1 hσl b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

omit [Module O X] [Module.Finite O X] in

theorem inRCone_of_nsmul {m : ℕ} {σ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    {d : Fin m → ℕ} (hk : 0 < k) (h : k • β = ∑ j, d j • σ j) : InRCone σ β := by
  refine ⟨fun j => (d j : ℝ) / k, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have e := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at e
  have e' : (k : ℝ) * (β a b : ℝ) = ∑ j, (d j : ℝ) * (σ j a b : ℝ) := by exact_mod_cast e
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ j, (d j : ℝ) * (σ j a b : ℝ)) / k by rw [← e']; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PolFan.StarCells

namespace GlobalTheory.PolFan.StarCells

theorem isStarOf_of_cover (hcover : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j))) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' := by
  intro E _ _ _ H q ψ w ψ' hψ hw h1 h2
  refine ⟨h1, h2, ?_⟩
  intro X _ _ _ _ hX n γ' hγ'
  set B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ j, (1 : ℝ) • toReal (γ' j) with hBdef
  have hB : B ∈ psdCone H.bar X :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X n γ' _ hγ'.mem hγ'.nonneg fun _ => zero_le_one
  obtain ⟨S, -, hfin⟩ := (hψ X hX).finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hfin B hB
  set δ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hδdef
  have hδ : IsCell H.bar ψ δ := CarDim.isCell_pull_equiv hγ e.symm
  have hBδ : B = ∑ i, c i • toReal (δ i) := by
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simp only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hδdef, pull_apply,
      LinearEquiv.coe_coe]
    exact this
  have key : ∀ (k : ℕ) (σ : Fin k → LinearMap.BilinForm ℤ X), IsCell H.bar ψ' σ → B ∈ rcone σ →
      ∀ j, InRCone σ (γ' j) := by
    rintro k σ hσ ⟨t, ht, hBt⟩ j
    obtain ⟨kk, d, hk, hkd⟩ := inCone_of_strict hσ.strict hσ.linear hγ'.mem hγ'.nonneg (a := fun _ => 1) (b := t)
      (fun _ => zero_le_one) ht ((linearOn_iff ψ' γ').1 hγ'.linear _ fun _ => zero_le_one) hBt j one_ne_zero
    exact inRCone_of_nsmul hk hkd
  by_cases hc0 : ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ InRCone δ β ∧ w.evalZ β = 1
  · obtain ⟨β₀, hβ₀, hβ₀p, hin, hw1⟩ := hc0
    have hne : β₀ ≠ 0 := by
      intro h0
      have := (hw X hX).2.1 β₀ hβ₀ hβ₀p hw1 2 0 (by simp [h0])
      omega
    obtain ⟨m', s, h, hfc, hpos, hBc⟩ :=
      hcover X m δ β₀ B (fun i => (hδ.mem i).1) hδ.nonneg hne hin ⟨c, hc, hBδ⟩
    exact Or.inr ⟨m, δ, β₀, m', s, h, hδ, hβ₀, hβ₀p, hw1, hin, hfc, hpos,
      key _ _ (h2 X hX m δ hδ β₀ hβ₀ hβ₀p hw1 hin m' s h hfc hpos) hBc⟩
  · push_neg at hc0
    have h0 : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β = 0 := fun β hβ hp hi =>
      ((hw X hX).1 β hβ hp).resolve_right (hc0 β hβ hp hi)
    exact Or.inl ⟨m, δ, hδ, h0, key _ _ (h1 X hX m δ hδ h0) ⟨c, hc, hBδ⟩⟩

end GlobalTheory.PolFan.StarCells
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberBasis
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.LocM.MapComp GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

namespace GlobalTheory.LocM.LatCover

theorem exists_frame_of_rows : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (a : ∀ σ : E →+* ℂ, Fin (Dw.mult σ + 1) → GL (Fin n) Γ(Z.X, U)), (∀ σ (r : Fin (Dw.mult σ + 1)), LatCover.StepAt Z B g L σ r hU m (a σ r)) → ∀ (c : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → Fin n → Γ(Z.X, U)), (∀ σ, ∃ (M : GL (Fin n) Γ(Z.X, U)) (e : Fin (Dw.mult σ) ↪ Fin n), ∀ i l, M (e i) l = c σ i l) → (∀ σ (i : Fin (Dw.mult σ)), ∃ j : Fin n, (j : ℕ) < i + 1 ∧ ∀ l, c σ i l = ((a σ i.succ)⁻¹ : GL (Fin n) Γ(Z.X, U)) l j) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X), ⊤ ≤ x ⁻¹ᵁ U → Set.range x ⊆ Z.opn → ∃ u, Z.FlagAt x u ∧ HasCoord g L m x u fun σ i l => valR x U (c σ i l) := by
  intro hΦ E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg U hU V hUV n m hm a hst c hext hrow k _ x hxU hxo
  classical
  obtain ⟨φx, hφ, hval⟩ : ∃ φ : Γ(Z.X, U) →+* k, spMap φ ≫ hU.fromSpec = x ∧ ∀ f, valR x U f = φ f :=
    ⟨_, GlobalTheory.FlagMod.spMap_ev x hU hxU, fun f => by rw [valR, dif_pos hxU]; rfl⟩
  obtain ⟨τ, mu, htr, hπ⟩ := StepBasis.exists_isTrans hg (x (IsLocalRing.closedPoint k))
  have h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V := GlobalTheory.FlagMod.le_preimage_map g hUV hxU
  obtain ⟨Φ, hΦw⟩ := hΦ E H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k x h hxo τ mu hπ
  obtain ⟨a0, ψ0, h0⟩ := Z.exists_chart x hxo
  have fu0 := CommonMod.flagAt_chart Z h0
  have fu0' := fu0
  set u0 := (Z.fr a0).bc ψ0 with hu0
  obtain ⟨b, χ, hb, fr, sf⟩ := fu0

  let w : Vecs Dw (Y Z.i).t k := fun σ i => (tv (Φ.symm fun l => φx (c σ i l))).left
  have hwT : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (w σ i) := fun σ i => GlobalTheory.LieMet.isTan_tv _

  have hco : HasCoord g L m x w fun σ i l => valR x U (c σ i l) := by
    refine ⟨τ, mu, h, htr, fun σ i => ?_⟩
    obtain ⟨v, hv, e1, e2⟩ := hΦw (Φ.symm fun l => φx (c σ i l))
    exact ⟨v, hv, e1, fun l => by rw [e2, LinearEquiv.apply_symm_apply]; exact (hval _).symm⟩

  have hB : ∀ σ, ∃ (n' : ℕ) (v : Fin n' → (Sp (DualNumber k) ⟶ (Y Z.i).t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n'),
      (∀ i, v (e i) = w σ i) ∧ StepFrame.Bas (Y Z.i).t (x ≫ Z.π) v := by
    intro σ
    obtain ⟨M, e, hM⟩ := hext σ
    refine ⟨n, fun j => (tv (Φ.symm fun l => φx (M j l))).left, e, fun i => ?_, ?_⟩
    · show (tv (Φ.symm fun l => φx (M (e i) l))).left = (tv (Φ.symm fun l => φx (c σ i l))).left
      simp only [hM]
    · rw [StepFrame.bas_iff_full (fun j => GlobalTheory.LieMet.isTan_tv _)]
      have ee : (fun j => GlobalTheory.LieMet.tanOf (GlobalTheory.LieMet.isTan_tv (Φ.symm fun l => φx (M j l)))) =
          fun j => Φ.symm fun l => φx (M j l) := funext fun j => GlobalTheory.LieMet.tan_ext rfl
      rw [ee]
      have hli : LinearIndependent k fun j => Φ.symm fun l => φx (M j l) := by
        have hu : IsUnit (((M : Matrix (Fin n) (Fin n) Γ(Z.X, U))).map φx) :=
          (Matrix.GeneralLinearGroup.map φx M).isUnit
        exact (Matrix.linearIndependent_rows_of_isUnit hu).map' Φ.symm.toLinearMap Φ.symm.ker
      have : Module.Finite k (ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G) := Module.Finite.equiv Φ.symm
      refine (StepFrame.uniq_iff _).2 ⟨hli, hli.span_eq_top_of_card_eq_finrank' ?_⟩
      rw [LinearEquiv.finrank_eq Φ, Module.finrank_fin_fun, Fintype.card_fin]

  have hW : ∀ σ (i : Fin (Dw.mult σ)), ∃ cf : Fin (Dw.mult σ) → k,
      (∀ j : Fin (Dw.mult σ), (i : ℕ) + 1 ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z.i).t (x ≫ Z.π) (u0 σ) cf (w σ i) := by
    intro σ i
    obtain ⟨j0, hj0, hcj⟩ := hrow σ i
    let A := a σ i.succ
    let col : Fin n → (Sp (DualNumber k) ⟶ (Y Z.i).t.G.left) := fun j =>
      (tv (Φ.symm fun l => φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j))).left
    have hst' := hst σ i.succ k φx
    rw [hφ] at hst'
    have hstep : ∀ i' : Fin (Dw.mult σ), (i' : ℕ) < (i : ℕ) + 1 → ∃ cf : Fin n → k,
        (∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z.i).t (x ≫ Z.π) col cf (u0 σ i') := by
      intro i' hi'
      let w' := GlobalTheory.LieMet.tanOf (fr.1 σ i').1
      obtain ⟨v, hv, e1, e2⟩ := hΦw w'
      have hz := hst' v hv h ⟨τ, mu, u0, i', htr, fu0', by simpa using hi', e1⟩
      refine ⟨fun j => ∑ l, φx (A j l) * Φ w' l, fun j hj => ?_, ?_⟩
      · have := hz j (by simpa using hj)
        simpa only [e2] using this
      · refine (GlobalTheory.LieMet.isComb_iff (fun j => Φ.symm fun l => φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j)) _ w').2 ?_
        apply Φ.injective
        rw [map_sum]
        simp only [map_smul, LinearEquiv.apply_symm_apply]
        funext l
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have hI : ((A⁻¹ : GL (Fin n) Γ(Z.X, U)) : Matrix (Fin n) (Fin n) Γ(Z.X, U)) * (A : Matrix (Fin n) (Fin n) Γ(Z.X, U)) = 1 :=
          Units.inv_mul A
        have hinv : ∀ l', ∑ j, φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j) * φx (A j l') = if l = l' then 1 else 0 := by
          intro l'
          have := congrArg φx (congrFun (congrFun hI l) l')
          rw [Matrix.mul_apply, map_sum] at this
          simp only [map_mul] at this
          rw [this, Matrix.one_apply]
          split_ifs <;> simp
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ l', ∑ j, φx (A j l') * Φ w' l' * φx (((A⁻¹ : GL (Fin n) Γ(Z.X, U))) l j) =
            (if l = l' then 1 else 0) * Φ w' l' := fun l' => by
          rw [← hinv l', Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hr : (i : ℕ) + 1 ≤ Dw.mult σ := i.2
    obtain ⟨-, hsp⟩ := StepFrame.step_eq fr hr (fun j => GlobalTheory.LieMet.isTan_tv _) hstep
    obtain ⟨cf, hcf, hcomb⟩ := hsp j0 hj0
    refine ⟨cf, hcf, ?_⟩
    have ew : w σ i = col j0 := by
      show (tv (Φ.symm fun l => φx (c σ i l))).left = _
      simp only [hcj]
      rfl
    rw [ew]
    exact hcomb
  have key := StepFrame.isFrame_of_steps fr Z.ty hW hB
  exact ⟨w, ⟨b, χ, hb, key.1, sameFlag_trans (tan_chart Z hb) (fun σ j => (fr.1 σ j).1) (fun σ j => (key.1.1 σ j).1)
    sf key.2⟩, hco⟩

end GlobalTheory.LocM.LatCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeFrameFiberInjective
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

namespace GlobalTheory.LocM.LatCover

theorem mult_le_rank : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z.X) (h : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V), Set.range x ⊆ Z.opn → ∀ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ), g ≫ B.π = Z.π ≫ τ → ∃ Φ : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G ≃ₗ[k] (Fin n → k), ∀ w : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (x ≫ Z.π) (Y Z.i).t.G, ∃ (v : Sp (DualNumber k) ⟶ B.t.G.left) (hv : IsTanAtG B.t (x ≫ g) v), v ≫ B.tMap.φ = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv w).left ≫ mu.φ ∧ ∀ l, tanEv B.t hv h (L.N.incl.app V (m l)) = Φ w l) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (g : Z.X ⟶ B.X), IsMap Z B g → ∀ (U : Z.X.Opens) (hU : IsAffineOpen U) (V : B.X.Opens), U ≤ g ⁻¹ᵁ V → ∀ (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ (σ : E →+* ℂ) (a : GL (Fin n) Γ(Z.X, U)), LatCover.StepAt Z B g L σ (Dw.mult σ) hU m a → ∀ x : Z.X, x ∈ U → Dw.mult σ ≤ n := by
  intro hc E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L g hg U hU V hUV n m hm σ a _ x hx
  obtain ⟨k, _, φ, u, hu⟩ := GlobalTheory.LocM.StepFrame.exists_flagAt Z hU hx
  obtain ⟨τ, mu, -, hπ⟩ := GlobalTheory.LocM.StepBasis.exists_isTrans hg x
  have ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn := GlobalTheory.LocM.MapComp.range_subset_opn Z hu
  have h : ⊤ ≤ ((spMap φ ≫ hU.fromSpec) ≫ g) ⁻¹ᵁ V := by
    have h1 : ⊤ ≤ (spMap φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
      rintro y -
      exact hU.range_fromSpec.le ⟨spMap φ y, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rintro y -
    have := hUV (h1 (Set.mem_univ y))
    simpa [Scheme.Hom.comp_apply] using this
  obtain ⟨Φ, -⟩ := hc E H Dw Xo p W hp hW Y i₀ Z B L g hg V n m hm k (spMap φ ≫ hU.fromSpec) h ho τ mu hπ
  obtain ⟨a₀, ψ₀, -, fu, -⟩ := hu
  by_contra hlt
  push_neg at hlt
  let b : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (Y Z.i).t.G :=
    fun j => Φ.symm (Pi.single j 1)
  have hcomb : ∀ i : Fin (Dw.mult σ), (i : ℕ) < Dw.mult σ → ∃ cf : Fin n → k,
      (∀ j : Fin n, Dw.mult σ ≤ (j : ℕ) → cf j = 0) ∧
      IsCombAtG (Y Z.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (fun j => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (b j)).left) cf (u σ i) := by
    intro i _
    have ht : IsTanAtG (Y Z.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z.π) (u σ i) := (fu.1 σ i).1
    refine ⟨fun j => Φ (GlobalTheory.LieMet.tanOf ht) j, fun j hj => absurd (hj.trans_lt j.2) (lt_asymm hlt), ?_⟩
    refine (GlobalTheory.LieMet.isComb_iff b _ (GlobalTheory.LieMet.tanOf ht)).2 ?_
    apply Φ.injective
    ext l
    simp [b, map_sum, Pi.single_apply]
  have hs := GlobalTheory.LocM.StepFrame.step_eq fu le_rfl (fun j => GlobalTheory.LieMet.isTan_tv (b j)) hcomb
  omega

end GlobalTheory.LocM.LatCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelThreeToFourStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_three_to_four : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), p.S = SExt.none → LevelThreeCondition p.s → StepW (pinAnd (Has3 p.s)) (Has4 p.s) := by
  first | exact @GlobalTheory.Mem.SRe.UpS.stepW_has4 | exact GlobalTheory.Mem.SRe.UpS.stepW_has4 | (intros; apply GlobalTheory.Mem.SRe.UpS.stepW_has4 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieGramEqGramOf
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.FlagBundle GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ}

open Classical in

def gramOf (e : F ≃+* c.F) (G : EigMet Z σ) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) : Mat Dw.mult ℂ :=
  if h : ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g then
    fun τ => (G.gram (cxOf e σ hj y) h.choose τ)ᵀ
  else 0

theorem lieGram_eq_gramOf (e : F ≃+* c.F) {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ : Mat Dw.mult X.Fn) : lieGram e U hj f₀ A₀ = gramOf e (hodgeMet Z U) hj f₀ A₀ := rfl

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraintsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minkowskiWeyl_orthant_cone_integral_constraints : ∀ (n : ℕ) (A V : Set (Fin n → ℤ)), A.Finite → ∃ (r : ℕ) (v : Fin r → Fin n → ℕ), (∀ t : Fin n → ℝ, ((∀ i, 0 ≤ t i) ∧ (∀ a ∈ A, ∑ i, (a i : ℝ) * t i ≤ 0) ∧ (∀ b ∈ V, ∑ i, (b i : ℝ) * t i = 0)) ↔ ∃ c : Fin r → ℝ, (∀ k, 0 ≤ c k) ∧ t = ∑ k, c k • fun i => (v k i : ℝ)) ∧ ∀ t : Fin n → ℕ, (∀ a ∈ A, ∑ i, a i * (t i : ℤ) ≤ 0) → (∀ b ∈ V, ∑ i, b i * (t i : ℤ) = 0) → ∃ (k : ℕ) (c : Fin r → ℕ), 0 < k ∧ k • t = ∑ j, c j • v j := by
  first | exact @GlobalTheory.MinkWeylReal.cone_orthant_fg | exact GlobalTheory.MinkWeylReal.cone_orthant_fg | (intros; apply GlobalTheory.MinkWeylReal.cone_orthant_fg <;> assumption)
end

