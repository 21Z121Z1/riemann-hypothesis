import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0778
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRegularCharacterLabelRootProduct
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory.RegLabelChar

open Polynomial GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

theorem pow_congr (L : LabelDatum g) {n : ℕ} (hn : 0 < n) {t : ℂ} (ht : t ^ (g ^ n - 1) = 1) {a b : ℕ}
    (h : L.gen n ^ a = L.gen n ^ b) : t ^ a = t ^ b := by
  have hN := L.gen_order n hn
  have hq1 : 0 < g ^ n - 1 := by
    have := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
    omega
  have hpos : 0 < orderOf (L.gen n) := hN ▸ hq1
  have h2 : L.gen n ^ (a % orderOf (L.gen n)) = L.gen n ^ (b % orderOf (L.gen n)) := by
    rw [pow_mod_orderOf, pow_mod_orderOf, h]
  have h3 := pow_injOn_Iio_orderOf (Set.mem_Iio.2 (Nat.mod_lt a hpos)) (Set.mem_Iio.2 (Nat.mod_lt b hpos)) h2
  rw [hN] at h3
  rw [← Nat.mod_add_div a (g ^ n - 1), ← Nat.mod_add_div b (g ^ n - 1), pow_add, pow_add, pow_mul, pow_mul, ht,
    one_pow, one_pow, h3]

theorem thetaOf_eq (L : LabelDatum g) {n : ℕ} (hn : 0 < n) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : L.teich x ^ (g ^ n - 1) = 1) {z : Formalism.CyclotomicNorms.Fbar g} {k : ℕ} (hz : z = L.gen n ^ k) :
    thetaOf L n x z = L.teich x ^ k := by
  have he : ∃ m : ℕ, z = L.gen n ^ m := ⟨k, hz⟩
  unfold thetaOf
  rw [dif_pos he]
  exact pow_congr L hn hx ((Exists.choose_spec he).symm.trans hz)

theorem exists_regularChar :
    ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (hn : 0 < n) (P : (ZMod g)[X])
    (hP : IsPrimeLab n P) (K : Type) [Field K] [Finite K] (hK : Nat.card K = g ^ n) (ι : K →+* Formalism.CyclotomicNorms.Fbar g),
    ∃ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ ∧
      (∃ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ u : Kˣ, ((θ u : ℂˣ) : ℂ) = thetaOf L n x (ι u)) ∧
      ∀ u : Kˣ, ι u = L.gen n →
        ∏ j ∈ Finset.range n, (X - C ((θ (u ^ g ^ j) : ℂˣ) : ℂ)) = GlobalTheory.SerSys.TameGen.liftPoly L.teich P := by
  intro g _ L n hn P hP K _ _ hK ι
  classical
  haveI := Fintype.ofFinite K
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' hg1
  have hq1 : 0 < g ^ n - 1 := by omega
  haveI : NeZero (g ^ n - 1) := ⟨hq1.ne'⟩
  have hdegP : P.natDegree = n := hP.2.2.2
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Formalism.CyclotomicNorms.Fbar g) P (degree_pos_of_irreducible hP.2.1).ne'
  have hxmem : x ∈ Formalism.CyclotomicNorms.rootsBar P := by
    simpa [Formalism.CyclotomicNorms.rootsBar, hP.2.1.ne_zero, aeval_def, eval_map] using hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero'] at hx
    exact hP.2.2.1 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective).1 hx)
  have hxq : x ^ (g ^ n - 1) = 1 := by
    have h1 : x ^ g ^ n = x := (GlobalTheory.GreenExists.pow_eq_self_iff hP.2.1 hx n).2 (hdegP ▸ dvd_refl _)
    have h2 : x ^ (g ^ n - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, h1, one_mul]
    exact mul_right_cancel₀ hx0 h2
  have ht1 : L.teich x ^ (g ^ n - 1) = 1 := by rw [← map_pow, hxq, map_one]
  have hgo : orderOf (L.gen n) = g ^ n - 1 := L.gen_order n hn
  have hprim : IsPrimitiveRoot (L.gen n) (g ^ n - 1) := hgo ▸ IsPrimitiveRoot.orderOf _
  have hcardK : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hpow : ∀ u : Kˣ, ∃ k : ℕ, ι u = L.gen n ^ k := fun u => by
    have h1 : (ι u) ^ (g ^ n - 1) = 1 := by
      rw [← map_pow, ← hcardK, FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  let f : Kˣ →* ℂ :=
    { toFun := fun u => thetaOf L n x (ι u)
      map_one' := by
        rw [thetaOf_eq L hn ht1 (k := 0) (by rw [Units.val_one, map_one, pow_zero]), pow_zero]
      map_mul' := fun u v => by
        obtain ⟨a, ha⟩ := hpow u
        obtain ⟨b, hb⟩ := hpow v
        rw [thetaOf_eq L hn ht1 ha, thetaOf_eq L hn ht1 hb,
          thetaOf_eq L hn ht1 (k := a + b) (by rw [Units.val_mul, map_mul, ha, hb, pow_add]), pow_add] }
  have hf : ∀ u : Kˣ, ((f.toHomUnits u : ℂˣ) : ℂ) = thetaOf L n x (ι u) := fun u => rfl
  have hfpow : ∀ (u : Kˣ) (m : ℕ), ι u = L.gen n → ((f.toHomUnits (u ^ m) : ℂˣ) : ℂ) = L.teich x ^ m :=
    fun u m hu => by
      rw [hf]
      exact thetaOf_eq L hn ht1 (by rw [Units.val_pow_eq_pow_val, map_pow, hu])

  have hroots := GlobalTheory.GreenExists.rootsBar_eq hP.2.1 hx
  rw [hdegP] at hroots
  have hnd : (Formalism.CyclotomicNorms.rootsBar P).Nodup := by
    unfold Formalism.CyclotomicNorms.rootsBar
    exact nodup_roots ((PerfectField.separable_of_irreducible hP.2.1).map)
  rw [hroots] at hnd
  refine ⟨f.toHomUnits, ?_, ⟨x, hxmem, hf⟩, ?_⟩
  ·
    intro i j hi hj h
    obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hwo : orderOf w = g ^ n - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
    have hιw : orderOf (ι (w : K)) = g ^ n - 1 := by
      have h := orderOf_injective ι.toMonoidHom ι.injective (w : K)
      rw [orderOf_units, hwo] at h
      exact h
    have hwp : IsPrimitiveRoot (ι (w : K)) (g ^ n - 1) := hιw ▸ IsPrimitiveRoot.orderOf _
    obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one (hgo ▸ pow_orderOf_eq_one (L.gen n))
    have hu0 : ι ((w ^ k : Kˣ) : K) = L.gen n := by rw [Units.val_pow_eq_pow_val, map_pow, hk]
    have h1 := congrArg (fun φ : Kˣ →* ℂˣ => ((φ (w ^ k) : ℂˣ) : ℂ)) h
    simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h1
    have hθ0 : ((f.toHomUnits (w ^ k) : ℂˣ) : ℂ) = L.teich x := by
      rw [hf]
      exact (thetaOf_eq L hn ht1 (k := 1) (by rw [hu0, pow_one])).trans (pow_one _)
    rw [hθ0, ← map_pow, ← map_pow] at h1
    have h2 := L.teich_inj _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0) h1
    exact Multiset.inj_on_of_nodup_map hnd i (Finset.mem_range.2 hi) j
      (Finset.mem_range.2 hj) h2
  · intro u hu
    rw [GlobalTheory.SerSys.TameGen.liftPoly, hroots, Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun j _ => ?_
    rw [Function.comp_apply, hfpow u _ hu, map_pow L.teich]

end GlobalTheory.RegLabelChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueFieldEmbeddingPlaceOver
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem GlobalTheory.residue_ringOfIntegers_to_place : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g),
    ∃ ι : 𝓞 E' ⧸ w'.asIdeal →+* Formalism.CyclotomicNorms.Fbar g,
      ∀ x : 𝓞 E', ι (Ideal.Quotient.mk _ x) = redThrough A κ (algebraMap E' Ω (x : E')) := by
  intro E' Ω _ _ _ _ g _ A w' h' κ
  classical
  have hmem : ∀ x : 𝓞 E', algebraMap E' Ω (x : E') ∈ A := by
    intro x
    have hi : IsIntegral ℤ (algebraMap E' Ω (x : E')) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E' Ω)
    have h2 : IsIntegral A.valuation.integer (algebraMap E' Ω (x : E')) := hi.tower_top
    have h3 := (Valuation.integer.integers A.valuation).mem_of_integral h2
    obtain ⟨y, hy⟩ := h3
    rw [← hy]
    exact (A.valuation_le_one_iff _).1 (by simpa [Algebra.smul_def] using y.2)
  let φ : 𝓞 E' →+* A :=
    { toFun := fun x => ⟨algebraMap E' Ω (x : E'), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let ψ : 𝓞 E' →+* Formalism.CyclotomicNorms.Fbar g := κ.toRingHom.comp ((IsLocalRing.residue A).comp φ)
  have hker : ∀ x ∈ w'.asIdeal, ψ x = 0 := by
    intro x hx
    have hlt : A.valuation (algebraMap E' Ω (x : E')) < 1 := (h' x).2 hx
    have hm : φ x ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff (φ x)).2 hlt
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [(IsLocalRing.residue_eq_zero_iff (φ x)).2 hm, map_zero]
  refine ⟨Ideal.Quotient.lift _ ψ hker, fun x => ?_⟩
  rw [Ideal.Quotient.lift_mk]
  unfold redThrough
  rw [dif_pos (hmem x)]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpherStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_inertDatum_of_dictionary_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  first | exact @GlobalTheory.SatExist.exists_satAt | exact GlobalTheory.SatExist.exists_satAt | (intros; apply GlobalTheory.SatExist.exists_satAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivOutsideLoc
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitSec

theorem exists_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (u : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), ∃ x : GAf L n, TrivOutside {s.v} (x : GA L n) ∧ s.loc n x = u := by
  intro L _ _ _ n s u
  exact GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s u

end GlobalTheory.SplitSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponents
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec

theorem exists_isComp_of_rowDepth {D : D7} (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (h : GlobalTheory.HeightCounting.RowDepth D rep) : ∃ cp, IsComp I rep cp := by
  have : ∀ σ k v, ∃ c : GlobalTheory.GoodTypes.LocRep D k, ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (h : s.w = D.naut.plGw k v)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) ((D.naut.plGw k v).adicCompletion D.host.E))),
    GlobalTheory.HeightCounting.IsLocS (rep σ).S s (h ▸ τ) ∧ c = pull I k v τ := by
    intro σ k v
    obtain ⟨s, τ, hs, h1, -⟩ := h σ k v
    have gen : ∀ (w) (e : s.w = w), ∃ τ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E)),
        GlobalTheory.HeightCounting.IsLocS (rep σ).S s (e ▸ τ') := by
      rintro _ rfl
      exact ⟨τ, h1⟩
    obtain ⟨τ', a⟩ := gen _ hs
    exact ⟨_, s, hs, τ', a, rfl⟩
  choose c hc using this
  exact ⟨c, hc⟩

theorem exists_comp_irrSm_param (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (hrc : IsRc hL T I rc) (Rw : GlobalTheory.HeightCounting.RowSide D)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (h1 : GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR) (h2 : GlobalTheory.HeightCounting.RowDepth D rep) :
    ∃ cp : GlobalTheory.GoodTypes.Comp D, IsComp I rep cp ∧
      ∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  obtain ⟨cp, hc⟩ := exists_isComp_of_rowDepth I rep h2
  refine ⟨cp, hc, fun σ k v => ⟨?_, Model.param_eq hrc hc h1 σ k v⟩⟩
  obtain ⟨s, hs, τ, -, e⟩ := hc σ k v
  rw [e]
  exact Model.irrSm_pull I k v τ

end GlobalTheory.TypeRec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteTypeVectorDetectedLocalComponentEquivarian
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocProj

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → Function.Injective T → (∀ a, T a ∈ π.S) → (∀ x : GAf L n, TrivOutside {s.v} (x : GA L n) → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ f ∈ π.S, f ≠ 0 → ∃ p : (GAf L n → ℂ) →ₗ[ℂ] τ.V, p f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} (x : GA L n) → ∀ f' ∈ π.S, p (NG.rt L n x f') = τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) (p f') := by
  intro L _ _ _ n π s τ i T hi hic hT hTS hTeq f hf hf0
  classical
  obtain ⟨hdec, hcomm, huniq⟩ := GlobalTheory.SplitAdelic.main L n s
  choose lift hlift using fun A => (huniq A).exists
  have hlu : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A := fun A x hx e =>
    (huniq A).unique ⟨hx, e⟩ (hlift A)
  have tmul : ∀ {x y : GAf L n}, TrivOutside {s.v} x → TrivOutside {s.v} y → TrivOutside {s.v} (x * y) := by
    intro x y hx hy v hv
    show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]
  have tone : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let lh : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := lift
      map_one' := (hlu _ _ tone (map_one _)).symm
      map_mul' := fun A B => (hlu _ _ (tmul (hlift A).1 (hlift B).1)
        (by rw [map_mul, (hlift A).2, (hlift B).2])).symm }
  have hlh : ∀ x, TrivOutside {s.v} x → lh (s.loc n x) = x := fun x hx => (hlu _ x hx rfl).symm
  let ρ : Representation ℂ (GAf L n) π.S :=
    { toFun := fun g => (NG.rt L n g).restrict (fun f hf => π.stable g f hf)
      map_one' := by
        apply LinearMap.ext; intro f; apply Subtype.ext; funext x
        simp [NG.rt]
      map_mul' := fun a b => by
        apply LinearMap.ext; intro f; apply Subtype.ext; funext x
        simp [NG.rt, mul_assoc] }
  have hρ : ∀ g (f : π.S), ((ρ g f : π.S) : GAf L n → ℂ) = NG.rt L n g f := fun _ _ => rfl
  have hρirr : ρ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
      have h1 : (⟨g, hg⟩ : π.S) ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      exact hg0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h1))
    · have hle : P.toSubmodule.map π.S.subtype ≤ π.S := by
        rintro _ ⟨p, -, rfl⟩
        exact p.2
      have hst : ∀ h, ∀ g ∈ P.toSubmodule.map π.S.subtype, NG.rt L n h g ∈ P.toSubmodule.map π.S.subtype := by
        rintro h _ ⟨p, hp, rfl⟩
        exact ⟨ρ h p, P.apply_mem_toSubmodule h hp, rfl⟩
      rcases π.irr _ hle hst with h | h
      · left
        apply Subrepresentation.ext
        show P.toSubmodule = ⊥
        rw [eq_bot_iff]
        intro p hp
        have : (p : GAf L n → ℂ) ∈ P.toSubmodule.map π.S.subtype := ⟨p, hp, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
      · right
        apply Subrepresentation.ext
        show P.toSubmodule = ⊤
        rw [eq_top_iff]
        intro p _
        have : (p : GAf L n → ℂ) ∈ P.toSubmodule.map π.S.subtype := by rw [h]; exact p.2
        obtain ⟨q, hq, e'⟩ := this
        rwa [show q = p from Subtype.ext e'] at hq
  let mi : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map i.toRingHom
  have hmi : ∀ B, mi (Matrix.GeneralLinearGroup.map i.symm.toRingHom B) = B := fun B =>
    Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)
  let σ : Representation ℂ (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) τ.V := τ.ρ.comp mi
  have hσirr : σ.IsIrreducible := by
    have hτ := τ.irr
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
    · obtain ⟨P1, P2, hne⟩ := hτ.exists_pair_ne
      apply hne
      have e1 : P1 = ⊥ ∨ P1 = ⊤ := hτ.eq_bot_or_eq_top P1
      have e2 : P2 = ⊥ ∨ P2 = ⊤ := hτ.eq_bot_or_eq_top P2
      have htop : (⊥ : Subrepresentation τ.ρ) = ⊤ := by
        apply Subrepresentation.ext
        have h' := congrArg Subrepresentation.toSubmodule h
        exact h'
      rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;> simp [htop]
    · let P' : Subrepresentation τ.ρ := ⟨P.toSubmodule, fun g v hv => by
        have := P.apply_mem_toSubmodule (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) hv
        change τ.ρ (mi _) v ∈ P.toSubmodule at this
        rwa [hmi] at this⟩
      rcases hτ.eq_bot_or_eq_top P' with h | h
      · left; apply Subrepresentation.ext; have h' := congrArg Subrepresentation.toSubmodule h; exact h'
      · right; apply Subrepresentation.ext; have h' := congrArg Subrepresentation.toSubmodule h; exact h'
  have hV : ∃ a : τ.V, a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨P1, P2, hne⟩ := τ.irr.exists_pair_ne
    apply hne
    apply Subrepresentation.ext
    ext a
    simp [hcon a, P1.toSubmodule.zero_mem, P2.toSubmodule.zero_mem]
  let f0 : σ.IntertwiningMap (ρ.comp lh) :=
    { toLinearMap := LinearMap.codRestrict π.S T hTS
      isIntertwining' := fun A => by
        apply LinearMap.ext; intro a; apply Subtype.ext
        show T (τ.ρ (mi A) a) = NG.rt L n (lh A) (T a)
        have := hTeq (lh A) (hlift A).1 a
        rwa [show s.loc n (lh A) = A from (hlift A).2] at this }
  have hf0' : f0 ≠ 0 := by
    obtain ⟨a, ha⟩ := hV
    intro h
    apply ha
    apply hT
    have : (f0 a : GAf L n → ℂ) = 0 := by rw [h]; rfl
    simpa [f0] using this
  have hc : ∀ g, ∃ u, ∀ y, Commute ((lh u)⁻¹ * g) (lh y) := by
    intro g
    obtain ⟨x, y', hx, hy', rfl⟩ := hdec g
    refine ⟨s.loc n x, fun y => ?_⟩
    rw [hlh x hx, inv_mul_cancel_left]
    exact (hcomm _ _ (hlift y).1 hy').symm
  have hU : ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ _ W'), σ'.IsIrreducible →
      ∀ f' : σ'.IntertwiningMap (ρ.comp lh), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
    intro W' _ _ σ' hσ' f' hf'
    exact (GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ W' ρ lh σ σ' hρirr hσirr hσ' hc f0 hf0').2 f' hf'
  have hsum := (GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ τ.V ρ lh σ σ hρirr hσirr hσirr hc f0 hf0').1
  have hfne : (⟨f, hf⟩ : π.S) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨p0, hp0⟩ := GlobalTheory.T.exists_intertwiningMap_ne_zero_of_isotypic_irreducible _ _ _ (ρ.comp lh) σ hσirr hsum hU ⟨f, hf⟩ hfne
  obtain ⟨p, hp⟩ := LinearMap.exists_extend p0.toLinearMap
  have hpS : ∀ g (hg : g ∈ π.S), p g = p0 ⟨g, hg⟩ := fun g hg => by
    have := LinearMap.congr_fun hp ⟨g, hg⟩
    exact this
  refine ⟨p, by rw [hpS f hf]; exact hp0, fun x hx f' hf' => ?_⟩
  rw [hpS _ (π.stable x f' hf'), hpS f' hf']
  have e1 : (⟨NG.rt L n x f', π.stable x f' hf'⟩ : π.S) = (ρ.comp lh) (s.loc n x) ⟨f', hf'⟩ := by
    apply Subtype.ext
    show NG.rt L n x f' = NG.rt L n (lh (s.loc n x)) f'
    rw [hlh x hx]
  rw [e1]
  exact LinearMap.congr_fun (p0.isIntertwining' (s.loc n x)) ⟨f', hf'⟩

end GlobalTheory.LocProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowApplySubPowLtOne
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem valuation_pow_sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1) (hab : A.valuation (a - b) < 1) (k : ℕ) :
    A.valuation (a ^ k - b ^ k) < 1 := by
  rw [← Commute.geom_sum₂_mul (Commute.all a b), map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' ha _) (pow_le_one' hb _)
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) hab

theorem frob_pow_apply_sub_lt_one :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (q : ℕ) (σ : Ω ≃ₐ[F] Ω),
    Formalism.ConjugateSelfDual.IsFrob A q σ → ∀ (n : ℕ) (x : Ω), A.valuation x ≤ 1 → A.valuation ((σ ^ n) x - x ^ (q ^ n)) < 1 := by
  intro F Ω _ _ _ _ A q σ hσ n
  obtain ⟨hD, hF⟩ := hσ
  have hD' : σ ∈ ReciprocityTheory.Gal.Dec (F := F) A := hD
  have hle : ∀ y : Ω, A.valuation y ≤ 1 → A.valuation (σ y) ≤ 1 := by
    intro y hy
    rw [A.valuation_le_one_iff] at hy ⊢
    exact (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hD' y).mpr hy
  induction n with
  | zero =>
    intro x _
    simp
  | succ n ih =>
    intro x hx
    have e : (σ ^ (n + 1)) x - x ^ (q ^ (n + 1)) =
        σ ((σ ^ n) x - x ^ (q ^ n)) + ((σ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) := by
      rw [pow_succ' σ n, AlgEquiv.mul_apply, map_sub, map_pow, ← pow_mul, ← pow_succ']
      ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · exact (ReciprocityTheory.Gal.valuation_apply_lt_one_iff hD' _).mpr (ih x hx)
    · refine valuation_pow_sub_pow_lt_one A (hle x hx) ?_ (hF x hx) _
      rw [map_pow]; exact pow_le_one' hx _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOneStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_realLieChart_kernelOperator_at_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      HasFDerivAt (chart (kerOp ν k γ φ.1) g)
        (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) := by
  first | exact @GlobalTheory.JSW.hasFDerivAt_chart_kerOp | exact GlobalTheory.JSW.hasFDerivAt_chart_kerOp | (intros; apply GlobalTheory.JSW.hasFDerivAt_chart_kerOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficientsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyodo_theorem_matrix_unramifiedCoefficients : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)), IsRat r σ → (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) → (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) → (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) → (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) = (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) → ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) = ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  first | exact @GlobalTheory.PMon.hyodo_mat | exact GlobalTheory.PMon.hyodo_mat | (intros; apply GlobalTheory.PMon.hyodo_mat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_through_frame_eval_finitePoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (D : InertDatum L n v w) (U0 : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w n → ∀ p : locU n w →* Formalism.UG.GU D.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ y, D.loc y = b⁻¹ * cLoc w (F.j y) * b) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU D.σw n), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U0, NG.rt L n κ f = f) → ∀ (lam : W →ₗ[ℂ] ℂ) (φ : UA L n → ℂ), (∀ g, φ (F.j g) = lam (f g)) → ∀ g, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU D.σw n).comap p) (fun x => h (p x)) φ (F.j g) = lam (heckeFunI L n U0 D h f g) := by
  first | exact @GlobalTheory.InertTransfer.heckeVec_frame_eval | exact GlobalTheory.InertTransfer.heckeVec_frame_eval | (intros; apply GlobalTheory.InertTransfer.heckeVec_frame_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFderivRealLieChartEqSumKernelOperatorsStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fderiv_realLieChart_eq_sum_kernelOperators : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a,
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
        ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 := by
  first | exact @GlobalTheory.JSW.integral_fderiv_chart_eq | exact GlobalTheory.JSW.integral_fderiv_chart_eq | (intros; apply GlobalTheory.JSW.integral_fderiv_chart_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleSingleBlockSelfStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_jacquetModule_singleBlock_self : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (e : (Σ _ : Fin 1, Fin N) ≃ Fin N), IsSubquotient (piTensor fun _ : Fin 1 => π) (jac e π) := by
  first | exact @GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac | exact GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac | (intros; apply GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac <;> assumption)
end

