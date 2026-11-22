import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEllipticCurveExistsOfUniformisation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem half_one_add_sqrt_quadratic {K : Type} [Field K] [CharZero K] {d : ℕ} (h4 : d % 4 = 3) {r w : K}
    (hr : r ^ 2 = -(d : K)) (hw : 2 * w = 1 + r) : w * w + (((1 + d) / 4 : ℕ) : K) = w := by
  have e : 4 * ((1 + d) / 4) = 1 + d := by omega
  have e' : (4 : K) * (((1 + d) / 4 : ℕ) : K) = 1 + d := by exact_mod_cast congrArg (Nat.cast : ℕ → K) e
  have e4 : (4 : K) ≠ 0 := by norm_num
  refine mul_left_cancel₀ e4 ?_
  have hr' : r = 2 * w - 1 := by linear_combination -hw
  subst hr'
  linear_combination e' + hr

theorem cmCurve_of_uniformisation : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → CMCurve := by
  intro hU hB hE d _ hs h4 K _ _ h2 ⟨r, hr⟩
  obtain ⟨w, bar, hw, -, hgen, hσ, σ₀, hσ₀⟩ := ringOfIntegers_sqrt_neg_three_mod_four d hs h4 K h2 r hr
  have hnr := (hσ σ₀).1
  choose 𝔟 h𝔟 using ClassGroup.mk0_surjective (R := 𝓞 K)
  obtain ⟨M, hM, κ, P, v, L₀, Q, t, L, δ, hκ, hP, hQ, hδ, hc, hβ⟩ := GlobalTheory.T.exists_numberField_defining_cm_curve_homs hU hB K h2 σ₀ hnr 𝔟
    (exists_cm_curves_of_weierstrass_curves (GlobalTheory.T.exists_ellipticCurve_polarised_lattice_family hU hB) K h2 σ₀ hnr 𝔟)
  have hv : IsTangent v := hP.2.1.1 0
  have hwc : ((κ (w : K) : M) : ℂ) = (1 + Complex.I * √d) / 2 := by
    have e := congrArg σ₀ hw
    rw [map_mul, map_add, map_one, map_ofNat, hσ₀] at e
    rw [hκ]
    linear_combination e / 2
  refine ⟨M, hM, κ (w : K), P, v, hwc, hP.1, hP.2.1, ?_, ?_, fun s => ?_,
    GlobalTheory.T.mean_log_lieNormSq_eq_mean_log_eta_alt hU hB hE K h2 σ₀ hnr 𝔟 h𝔟 M κ P v L₀ Q t L δ ⟨hκ, hP, hQ, hδ, hc⟩ hβ⟩
  · obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨β, -, hend, -⟩ := hβ
    obtain ⟨W, hW, hWv⟩ := hend w P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
    have hP₀ := GlobalTheory.T.ellipticCurve_lattice_baseChange_stable _ P v L₀ M _ P₀ φ v₀ hP hφ hv₀
    refine ⟨P₀, φ, v₀, W, hφ, hv₀, hP₀.2.1, hW, ?_, hWv⟩
    refine LieMultiple.quadratic_equation_of_derivative hU hB M (algebraMap M ℂ) P₀ v₀ W _ _ (hP₀.2.1.1 0)
      hP₀.2.2.1 hW hWv ?_
    have e := congrArg κ (half_one_add_sqrt_quadratic h4 hr hw)
    rwa [map_add, map_mul, map_natCast] at e
  · obtain ⟨c, hc0, hc⟩ := hc
    refine lattice_unif_fibre_eq_of_period hU _ P v _ (L₀ _) c _ hP.1 hv (hP.2.2.2 _) hc0 fun z => ?_
    rw [hc, hκ]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨m, n, rfl⟩ := hgen a
      exact ⟨m, n, by simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + n * w, by simp⟩
  · exact ⟨_, isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ (L₀ _) hP.1 hv (hP.2.2.2 _)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyDescendsToNumberField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.FamDesc

theorem exists_field (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (k : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] (P Q : Out.PolAV (Sp k)) {G H : Over (Sp ℂ)} [GrpObj G] [GrpObj H]
    {φ : G.left ⟶ P.A.left} {m : H.left ⟶ Q.A.left} (hP : IsGrpPullback G P.A (spMap (algebraMap k ℂ)) φ)
    (hQ : IsGrpPullback H Q.A (spMap (algebraMap k ℂ)) m) (f : G ⟶ H) [IsMonHom f] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ →
      ∀ (G₂ H₂ : Over (Sp k₂)) (φ₂ : G₂.left ⟶ P.A.left) (m₂ : H₂.left ⟶ Q.A.left) (φ₃ : G.left ⟶ G₂.left)
        (m₃ : H.left ⟶ H₂.left), φ₂ ≫ P.A.hom = G₂.hom ≫ spMap (IntermediateField.inclusion h₂).toRingHom →
        IsPullback m₂ H₂.hom Q.A.hom (spMap (IntermediateField.inclusion h₂).toRingHom) →
        φ₃ ≫ G₂.hom = G.hom ≫ spMap (algebraMap k₂ ℂ) → m₃ ≫ H₂.hom = H.hom ≫ spMap (algebraMap k₂ ℂ) →
        φ₃ ≫ φ₂ = φ → m₃ ≫ m₂ = m → ∃ f₂ : G₂ ⟶ H₂, f.left ≫ m₃ = φ₃ ≫ f₂.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso hP (isGrpPullback_pullback P.A _)
  obtain ⟨d, hd, hd'⟩ := grpPullback_iso hQ (isGrpPullback_pullback Q.A _)
  obtain ⟨K, f₁, j, hK, -, j₁, j₂, j₃⟩ := hom_descends_to_numberField hT hB k P Q (e.inv ≫ f ≫ d.hom) inferInstance
  have : IsScalarTower ℚ k K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : FiniteDimensional ℚ K := Module.Finite.trans k K
  refine ⟨K.restrictScalars ℚ, hfin, fun k₂ h₂ h₁ G₂ H₂ φ₂ m₂ φ₃ m₃ w₂ c₂ w₃ v₃ e₃ d₃ => ?_⟩
  let q : K →+* k₂ := (IntermediateField.inclusion h₁).toRingHom
  have s₁ : spMap q ≫ spMap (algebraMap k K) = spMap (IntermediateField.inclusion h₂).toRingHom :=
    (spMap_comp_spMap _ _).trans (congrArg spMap (RingHom.ext fun _ => rfl))
  have s₂ : spMap (algebraMap k₂ ℂ) ≫ spMap q = spMap K.val.toRingHom :=
    (spMap_comp_spMap _ _).trans (congrArg spMap (RingHom.ext fun _ => rfl))
  obtain ⟨i, i₁, i₂⟩ : ∃ i : G₂.left ⟶ pullback P.A.hom (spMap (algebraMap k K)),
      i ≫ pullback.fst _ _ = φ₂ ∧ i ≫ pullback.snd _ _ = G₂.hom ≫ spMap q :=
    ⟨pullback.lift φ₂ (G₂.hom ≫ spMap q) (by rw [w₂, Category.assoc, s₁]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have fw : f₁.left ≫ pullback.snd Q.A.hom (spMap (algebraMap k K)) = pullback.snd _ _ := Over.w f₁
  have ew : e.hom.left ≫ pullback.snd P.A.hom (spMap (algebraMap k ℂ)) = G.hom := Over.w e.hom
  have w : (i ≫ f₁.left ≫ pullback.fst _ _) ≫ Q.A.hom =
      G₂.hom ≫ spMap (IntermediateField.inclusion h₂).toRingHom := by
    have h : f₁.left ≫ pullback.fst Q.A.hom (spMap (algebraMap k K)) ≫ Q.A.hom =
        pullback.snd _ _ ≫ spMap (algebraMap k K) :=
      (congrArg (f₁.left ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) fw))
    refine (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((Category.assoc _ _ _).trans h)).trans ?_)
    rw [← Category.assoc, i₂, Category.assoc, s₁]
  have key : φ₃ ≫ i = e.hom.left ≫ j := by
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) i₁).trans e₃)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₁).trans he')).symm
    · refine ((Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) i₂).trans ?_)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₂).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) ew)))).symm
      rw [← Category.assoc, w₃, Category.assoc, s₂]
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : G₂ ⟶ H₂, f₂.left ≫ m₂ = i ≫ f₁.left ≫ pullback.fst _ _ :=
    ⟨Over.homMk (c₂.lift _ G₂.hom w) (c₂.lift_snd _ _ _), c₂.lift_fst _ _ _⟩
  refine ⟨f₂, c₂.hom_ext ?_ ?_⟩
  · have r : e.hom.left ≫ (e.inv ≫ f ≫ d.hom).left = f.left ≫ d.hom.left := by
      rw [← Over.comp_left, e.hom_inv_id_assoc, Over.comp_left]
    have a₁ : (φ₃ ≫ f₂.left) ≫ m₂ = e.hom.left ≫ j ≫ f₁.left ≫ pullback.fst _ _ :=
      (Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) hf₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) key).trans (Category.assoc _ _ _))))
    rw [a₁, Category.assoc, d₃, ← hd', ← Category.assoc, ← r, Category.assoc]
    exact congrArg (e.hom.left ≫ ·) j₃.symm
  · rw [Category.assoc, Category.assoc, Over.w, v₃, w₃, ← Category.assoc, Over.w]

theorem exists_mul {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj H] {G' H' : Over S'} [GrpObj H']
    {φ : G'.left ⟶ G.left} {m : H'.left ⟶ H.left} (w : φ ≫ G.hom = G'.hom ≫ j) (hm : IsGrpPullback H' H j m)
    {x' y' : G' ⟶ H'} {x y : G ⟶ H} (hx : x'.left ≫ m = φ ≫ x.left) (hy : y'.left ≫ m = φ ≫ y.left) :
    (x' * y').left ≫ m = φ ≫ (x * y).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ w
  have h := hm.2 G' x' y' (φ₀ ≫ x) (φ₀ ≫ y) hx.symm hy.symm
  rw [← MonObj.comp_mul] at h
  rw [← h]
  rfl

end GlobalTheory.CM.FamDesc

namespace GlobalTheory.CM
open FamDesc in

theorem isFam_descends_to_numberField : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (ω : k) (C : Ell H k ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp k)) (L : Submodule (𝓞 E) D.La) (ω' : ℂ) (C' : Ell H ℂ ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap (algebraMap k ℂ))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap k ℂ) φ → IsFam C' T' h L ψ' →
  ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ (ω₂ : k₂) (C₂ : Ell H k₂ ω₂) (φ₂ : C₂.P.A.left ⟶ C.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left) (T₂ : PAT H (Sp k₂)) (m₂ : SABMap T₂.t T.t (spMap (IntermediateField.inclusion h₂).toRingHom)) (m₃ : SABMap T'.t T₂.t (spMap (algebraMap k₂ ℂ))),
    EllMap C₂ C (IntermediateField.inclusion h₂).toRingHom φ₂ → EllMap C' C₂ (algebraMap k₂ ℂ) φ₃ → φ₃ ≫ φ₂ = φ → m₃.φ ≫ m₂.φ = m.φ → ∃ ψ : L → (C₂.P.A ⟶ T₂.t.G), IsFam C₂ T₂ h L ψ ∧ ∀ a, (ψ' a).left ≫ m₃.φ = φ₃ ≫ (ψ a).left := by
  intro hT hL E _ _ _ H k _ ω C D h T L ω' C' φ T' m ψ' hC hF
  have hfin := D.fin
  have : Module.Finite (𝓞 E) L := inferInstance
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have hg : AddMonoid.FG L := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨S, hS⟩ := hg.fg_top
  choose K hK hK' using fun a : L => @exists_field hT hL.polBaseChange k _ C.P T.pol _ _ _ _ _ _ hC.2.1.2.1 m.cart
    (ψ' a) (hF.1 a).isMonHom
  refine ⟨k ⊔ (K 0 ⊔ ⨆ a : S, K a), ?_, le_sup_left, ?_⟩
  · have := hK
    have : FiniteDimensional ℚ (⨆ a : S, K a : IntermediateField ℚ ℂ) := IntermediateField.finiteDimensional_iSup_of_finite
    infer_instance
  intro k₂ h₂ h₁ ω₂ C₂ φ₂ φ₃ T₂ m₂ m₃ e₂ e₃ eφ em
  have gen : ∀ a : L, K a ≤ k₂ → ∃ f₂ : C₂.P.A ⟶ T₂.t.G, (ψ' a).left ≫ m₃.φ = φ₃ ≫ f₂.left := fun a ha =>
    hK' a k₂ h₂ ha C₂.P.A T₂.t.G φ₂ m₂.φ φ₃ m₃.φ e₂.2.1.2.1.1.w m₂.cart.1 e₃.2.1.2.1.1.w m₃.cart.1.w eφ em
  have all : ∀ a : L, ∃ f₂ : C₂.P.A ⟶ T₂.t.G, (ψ' a).left ≫ m₃.φ = φ₃ ≫ f₂.left := by
    intro a
    have ha : a ∈ AddSubmonoid.closure (S : Set L) := hS ▸ AddSubmonoid.mem_top a
    induction ha using AddSubmonoid.closure_induction with
    | mem a ha => exact gen a (((le_iSup (fun a : S => K a) ⟨a, ha⟩).trans (le_sup_right.trans le_sup_right)).trans h₁)
    | zero => exact gen 0 ((le_sup_left.trans le_sup_right).trans h₁)
    | add a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x * y, by rw [hF.2.1]; exact exists_mul e₃.2.1.2.1.1.w m₃.cart hx hy⟩
  choose ψ hψ using all
  exact ⟨ψ, GlobalTheory.T.family_identities_descend_field_to_dedekind hL E H k₂ ω₂ C₂ D h T₂ L ψ ℂ ω' C' (algebraMap k₂ ℂ) φ₃ T' m₃ ψ'
    (algebraMap k₂ ℂ).injective e₃ hψ hF, hψ⟩

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyExtendsOverDedekindDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem isFam_extends_dedekind :
    Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ω' : K) (C' : Ell H K ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp K)) (m : SABMap T'.t T.t (spMap (algebraMap R K))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap R K) φ → IsFam C' T' h L ψ' → ∃ ψ : L → (C.P.A ⟶ T.t.G), IsFam C T h L ψ ∧ ∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left := by
  intro hL hD E _ _ _ H R K _ _ _ _ _ ω C D h T L ω' C' φ T' m ψ' hφ hψ'
  have key : ∀ a : L, ∃ F : C.P.A ⟶ T.t.G, (ψ' a).left ≫ m.φ = φ ≫ F.left := fun a => by
    obtain ⟨F, -, hF, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hD R K C.P.A T.t.G C'.P.A T'.t.G
      φ m.φ C.P.isAb T.ab hφ.2.1.2.1 m.cart (ψ' a) (hψ'.1 a).isMonHom
    exact ⟨F, hF⟩
  choose ψ hψ using key
  exact ⟨ψ, GlobalTheory.T.family_identities_descend_field_to_dedekind hL E H R ω C D h T L ψ K ω' C' (algebraMap R K) φ T' m ψ'
    (IsFractionRing.injective R K) hφ hψ hψ', hψ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLatticeDataOfAdaptedBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmPoint_lattice_data_of_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : PullbackSections.UnfAt U k x₀) (Xx : FD.DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), FD.LamBasis Xx La (hX ▸ x₀.1) lam → ∃ Z : CMLat W.per Dw.p Dw.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  first | exact @GlobalTheory.LamT.CMBasis.exists_cmLat_unfAt | exact GlobalTheory.LamT.CMBasis.exists_cmLat_unfAt | (intros; apply GlobalTheory.LamT.CMBasis.exists_cmLat_unfAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmPoint_localModel_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  first | exact @GlobalTheory.LamT.locMod_exists | exact GlobalTheory.LamT.locMod_exists | (intros; apply GlobalTheory.LamT.locMod_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoom
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory

theorem room_neg_log_epStar (f d L M k0 S : ℝ) (hf : 1 ≤ f) (hd : 1 ≤ d) (hL : 0 ≤ L)
    (hM : 0 < M) (hk : 0 < k0) (hS : 1 ≤ S)
    (h : Real.log (M * k0) ≤ 19 * L + 3 + Real.log d) :
    0 < epStar M f S k0 ∧ epStar M f S k0 ≤ 1 ∧
      -Real.log (epStar M f S k0) ≤ 19 * L + 6 + Real.log d + f + Real.log S := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hfS : 1 ≤ f * S := one_le_mul_of_one_le_of_one_le hf hS
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hlS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hpi := Real.pi_gt_three
  have hD : 0 < M * (f * S + 2) * k0 * Real.log 2 := by positivity
  unfold epStar
  refine ⟨lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  rcases min_choice 1 (Real.pi / (M * (f * S + 2) * k0 * Real.log 2)) with h1 | h1 <;> rw [h1]
  · rw [Real.log_one]; linarith
  · have hMk : 0 < M * k0 := by positivity
    have e : M * (f * S + 2) * k0 * Real.log 2 = (M * k0) * ((f * S + 2) * Real.log 2) := by ring
    rw [Real.log_div (by positivity) hD.ne', e, Real.log_mul hMk.ne' (by positivity)]
    have h2 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
    have h3 : Real.log ((f * S + 2) * Real.log 2) ≤ Real.log (3 * f * S) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h6 : Real.log (3 * f * S) = Real.log 3 + Real.log f + Real.log S := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    have h5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by positivity)
    linarith

theorem room_log_radius (f r : ℕ) (d e S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (he : 0 < e) (hS : 1 ≤ S) :
    0 < 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5)) =
      Real.log (1600 / 3) + Real.log r + (1 / 2) * Real.log f + (1 / 2) * Real.log S
        + 3 * Real.log ((f : ℝ) * r) + Real.log d - (1 / 2) * Real.log e := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hS' : (0 : ℝ) < S := by linarith
  have hd' : (0 : ℝ) < d := by linarith
  have h1 : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have h2 : 0 < Real.sqrt f := Real.sqrt_pos.2 hf'
  have h3 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr'
  have h4 : 0 < Real.sqrt (S * r) := Real.sqrt_pos.2 (by positivity)
  have E : 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) =
      1600 / 3 * Real.sqrt r * Real.sqrt f * Real.sqrt (S * r) * ((f : ℝ) * r) ^ 3 * d / Real.sqrt e := by
    unfold ReciprocityTheory.MultiplicativeHeights.approxR d5mu frameRadius
    field_simp
    norm_num
  rw [E]
  refine ⟨by positivity, ?_⟩
  rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by positivity) hd'.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) h4.ne',
    Real.log_mul (by positivity) h2.ne', Real.log_mul (by positivity) h3.ne',
    Real.log_pow, Real.log_sqrt he.le, Real.log_sqrt hf'.le, Real.log_sqrt hr'.le,
    Real.log_sqrt (by positivity), Real.log_mul hS'.ne' hr'.ne']
  push_cast
  ring

theorem room_of_constants : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (f r p0 : ℕ) (d L Om M k0 S : ℝ), 1 ≤ f → 1 ≤ r → p0 ≤ r → 1 ≤ d → 0 ≤ L → 0 < M → 0 < k0 → 1 ≤ S → Real.log (M * k0) ≤ 19 * L + 3 + Real.log d → 1 ≤ frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5) ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ S → ∀ C A : ℝ, C0 ≤ C → 2 ≤ A → (Formalism.L2.LamCM.pDeg Om + (1 / 2) * Real.log (frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5))) * (s + t) + s * Real.log ((r : ℝ) * frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5)) ≤ C * ((f : ℝ) * r + L + Real.log d + |Om|) ^ A * (1 + Real.log S) * S := by
  refine ⟨3000, by norm_num, ?_⟩
  intro f r p0 d L Om M k0 S hf hr hp hd hL hM hk hS h
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hp' : (p0 : ℝ) ≤ r := by exact_mod_cast hp
  obtain ⟨he0, he1, he2⟩ := room_neg_log_epStar f d L M k0 S hf' hd hL hM hk hS h
  obtain ⟨hX0, hX⟩ := room_log_radius f r d _ S hf hr hd he0 hS
  unfold frameBasisRadius
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt (epStar M f S k0) / Real.sqrt f))
    (3 * frameRadius S r / 5) with hXdef
  clear_value X
  have hle : Real.log (epStar M f S k0) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (f : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have hfn : (f : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_right (by linarith) hr'
  have hrn : (r : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_left (by linarith) hf'
  have a1 : 0 ≤ Real.log d := Real.log_nonneg hd
  have a2 : 0 ≤ Real.log S := Real.log_nonneg hS
  have a3 : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((f : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have b3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by linarith)
  have b4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < r by linarith)
  have b5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (f : ℝ) * r by linarith)
  have b6 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1600 / 3 by norm_num)
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  have hX1' : 1 ≤ X := by
    by_contra hc
    have := Real.log_neg hX0 (not_le.1 hc)
    linarith
  refine ⟨one_le_pow₀ hX1', ?_⟩
  intro s t hs ht hst C A hC hA
  have hOm := abs_nonneg Om
  set Z : ℝ := (f : ℝ) * r + L + Real.log d + |Om| with hZ
  have hZn : (f : ℝ) * r ≤ Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hXZ : Real.log X ≤ 600 * Z + Real.log S := by rw [hX]; linarith
  have hXZ' : Real.log X ≤ 600 * (Z * (1 + Real.log S)) := by
    have : Real.log S ≤ Z * Real.log S := le_mul_of_one_le_left a2 hZ1
    linarith
  have hpd : Formalism.L2.LamCM.pDeg Om ≤ Z := by unfold Formalism.L2.LamCM.pDeg; linarith
  have hlog : Real.log (X ^ (2 * p0 + 1)) ≤ 1800 * (Z ^ 2 * (1 + Real.log S)) := by
    rw [Real.log_pow]
    push_cast
    calc (2 * (p0 : ℝ) + 1) * Real.log X ≤ (3 * Z) * (600 * (Z * (1 + Real.log S))) :=
          mul_le_mul (by linarith) hXZ' hX1 (by linarith)
      _ = _ := by ring
  have hlog0 : 0 ≤ Real.log (X ^ (2 * p0 + 1)) := Real.log_nonneg (one_le_pow₀ hX1')
  rw [Real.log_mul (by positivity) (by positivity)]
  have hZW : Z ≤ Z ^ 2 * (1 + Real.log S) :=
    (le_self_pow₀ hZ1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hZA : Z ^ 2 ≤ Z ^ A := by
    have := Real.rpow_le_rpow_of_exponent_le hZ1 hA
    rwa [Real.rpow_two] at this
  set W := Z ^ 2 * (1 + Real.log S) with hW
  set Y := Real.log (X ^ (2 * p0 + 1)) with hY
  have hW0 : 0 ≤ W := by linarith
  have c1 : (Formalism.L2.LamCM.pDeg Om + 1 / 2 * Y) * (s + t) ≤ (901 * W) * S :=
    mul_le_mul (by linarith) hst (by linarith) (by linarith)
  have c2 : s * (Real.log r + Y) ≤ S * (1801 * W) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have c3 : 3000 * W ≤ C * Z ^ A * (1 + Real.log S) := by
    have : 3000 * Z ^ 2 ≤ C * Z ^ A := mul_le_mul hC hZA (by positivity) (by linarith)
    calc 3000 * W = (3000 * Z ^ 2) * (1 + Real.log S) := by rw [hW]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this (by linarith)
  have c4 : 3000 * W * S ≤ C * Z ^ A * (1 + Real.log S) * S :=
    mul_le_mul_of_nonneg_right c3 (by linarith)
  have c5 : 0 ≤ W * S := mul_nonneg hW0 (by linarith)
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_isogeny_of_surjective_points : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A, ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  first | exact @GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers | exact GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers | (intros; apply GlobalTheory.LamF.exists_inverse_isogeny_ringOfIntegers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerLogOmCore
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.LamT

theorem exists_kronecker_logOm_core : ∀ (D : D7) (T : Core D) (h : LawsCore T) (large₂ : SizeData₂ D), ∃ (_ : NeZero T.Q.H.d) (χ : DirichletCharacter ℂ T.Q.H.d), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm :=
  fun D T h large₂ => GlobalTheory.LamF.exists_kronecker_logOm_eq D T.Q h.pins.1 large₂

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebraSquaredLength_comp_pairing_hom : ThetaUnifAV → Out.Laws → ∀ (R : Type) [CommRing R] (P P' : Out.PolAV (Sp R)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (v : epsR R ⟶ P.A) (a : R) (s : R →+* ℂ) (r r' : ℝ), IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → IsTangent v → IsLieComb ![a] ![v] (v ≫ g) → IsLieNormSq P v s r → IsLieNormSq P' (v ≫ f) s r' → r' = (s a).re * r := by
  first | exact @GlobalTheory.NormHom.lieNormSq_comp | exact GlobalTheory.NormHom.lieNormSq_comp | (intros; apply GlobalTheory.NormHom.lieNormSq_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P), F.lieLat.FG ∧ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) = ⊤ := by
  first | exact @GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top | exact GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top | (intros; apply GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_localization_modelLieAlgebra : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  first | exact @GlobalTheory.CM.LieLoc.lieLat_localization | exact GlobalTheory.CM.LieLoc.lieLat_localization | (intros; apply GlobalTheory.CM.LieLoc.lieLat_localization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
  first | exact @GlobalTheory.LamT.fibKey_keyPB | exact GlobalTheory.LamT.fibKey_keyPB | (intros; apply GlobalTheory.LamT.fibKey_keyPB <;> assumption)
end

