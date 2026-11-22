import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRPush
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.DZero

theorem valR_push {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ => h (Set.mem_univ _)
  rw [valR, valR, dif_pos h, dif_pos h']
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  rw [e1]
  exact congrArg (fun k => k.hom ((x.appLE U ⊤ h).hom f)) e2

theorem isD_zero : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), IsD ν d 0 (DegPre.zeroT D (TE R ℂ)) := by
  intro R _ _ _ _ D _ _ _ N ν g d U f hU
  have h0 : d.ex 0 = 1 := by
    have := d.ex_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have e : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
      (DegPre.zeroT D (TE R ℂ))).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    have : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        (DegPre.zeroT D (TE R ℂ)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id, h0, map_one, Hom.one_def, ← Category.assoc, comp_toUnit]
    rw [this, Over.comp_left]
    rfl
  rw [e, valR_push _ _ _ hU, map_zero, TrivSqZeroExt.inr_zero, add_zero]
  rfl

end GlobalTheory.MBLow.Cl.DZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CoeffValuation

theorem mem_of_forall_natCast {L : Type} [Field L] [NumberField L] (W : ValuationSubring L)
    (h : ∀ n : ℕ, n ≠ 0 → (n : L) ∉ W.nonunits) (x : L) : x ∈ W := by
  have halg : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 : m • x ∈ W := by
    have h : IsIntegral W (m • x) := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := L)).mp h
    exact hy ▸ y.2
  have h2 : ((m.natAbs : ℕ) : L)⁻¹ ∈ W := by
    have := h m.natAbs (Int.natAbs_ne_zero.mpr hm)
    rw [ValuationSubring.mem_nonunits_iff_or] at this
    by_contra hc
    exact this (Or.inr hc)
  have hm' : (m : L) ≠ 0 := Int.cast_ne_zero.mpr hm
  have h3 : (m : L)⁻¹ ∈ W := by
    rcases Int.natAbs_eq m with e | e
    · rw [e, Int.cast_natCast]; exact h2
    · rw [e, Int.cast_neg, Int.cast_natCast, inv_neg]; exact W.neg_mem _ h2
  have : x = (m : L)⁻¹ * (m • x) := by
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ hm']
  rw [this]
  exact W.mul_mem _ _ h3 h1

theorem dedekind_and_away {L : Type} [Field L] [NumberField L] (W : ValuationSubring L) :
    IsDedekindDomain W ∧ ∃ π : W, IsLocalization.Away π L := by
  by_cases h : ∃ n : ℕ, n ≠ 0 ∧ (n : L) ∈ W.nonunits
  · obtain ⟨n, hn, hW⟩ := h
    have := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField W hn hW).1
    refine ⟨inferInstance, ?_⟩
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
    refine ⟨π, ?_⟩
    refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨_, k, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr (pow_ne_zero k hπ.ne_zero))
    · intro z
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) z
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
      refine ⟨⟨a * (u⁻¹ : Wˣ), ⟨π ^ k, k, rfl⟩⟩, ?_⟩
      have hb1 : algebraMap W L (u * π ^ k) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr hb0
      rw [div_mul_eq_mul_div, div_eq_iff hb1, ← map_mul, ← map_mul]
      congr 1
      rw [mul_assoc, Units.inv_mul_cancel_left]
    · intro a b hab
      exact ⟨1, by rw [IsFractionRing.injective W L hab]⟩
  · have hall : ∀ x : L, x ∈ W := mem_of_forall_natCast W fun n hn hW => h ⟨n, hn, hW⟩
    have hbij : Function.Bijective (algebraMap W L) :=
      ⟨IsFractionRing.injective W L, fun x => ⟨⟨x, hall x⟩, rfl⟩⟩
    have hF : IsField W := (RingEquiv.ofBijective _ hbij).toMulEquiv.isField (Field.toIsField L)
    have : IsPrincipalIdealRing W := hF.isPrincipalIdealRing
    exact ⟨inferInstance, 1, IsLocalization.away_of_isUnit_of_bijective L isUnit_one hbij⟩

theorem isDedFrac_and_isOpenImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  intro E _ _ _ H l c W
  have := c.fin
  have : NumberField c.F := NumberField.mk
  obtain ⟨hD, π, hπ⟩ := dedekind_and_away W
  exact ⟨⟨⟨inferInstance, hD⟩, inferInstance, (inferInstance : IsFractionRing W c.F)⟩,
    IsOpenImmersion.of_isLocalization (S := c.F) π⟩

end GlobalTheory.CoeffValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartz
section
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ om₁ : Rep σ X W, M₁.IsWeil B.ψ χX χW om₁ ∧ ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨T, hTe, hTs⟩ := GlobalTheory.ModelTr.extEquiv (schA F (Fin n × Fin d)) e hbij
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (GlobalTheory.T.weil_eigen_bijective_good_model F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans (GlobalTheory.ModelTr.adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := GlobalTheory.T.weil_eigen_bijective_pair F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  refine ⟨trRep T om, isUWeilPair_trRep hgood
    (GlobalTheory.T.weil_eigen_bijective_paired_models F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe)
    (GlobalTheory.T.weil_eigen_bijective_regular F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe) hpair.weil, fun x Φ hΦ => ?_⟩
  have hpres : om x Φ ∈ schA F (Fin n × Fin d) := hpair.weil.isUSplitting.pres x Φ hΦ
  rw [trRep_apply, ← hTe Φ hΦ, LinearEquiv.symm_apply_apply, hTe _ hpres]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingUnitScalar
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.TateUnitPair

theorem lev_zsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (n : ℤ) (k : ℕ) :
    (n • t).lev k = t.lev k ^ n := by
  rfl

theorem lev_nsmul {p : ℕ} {M : Type} [CommGroup M] (t : Tate p M) (n : ℕ) (k : ℕ) :
    (n • t).lev k = t.lev k ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (tι : Dw.La →+ P.T) (ζ : ℕ → ℂ_[p]ˣ),
    (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) →
    (∀ (k : ℕ) a b, weil P.A (p ^ k) ((tι a).lev k) ((tι b).lev k) = ζ (p ^ k) ^ Dw.EF a b) →
    ∃ u : ℤ_[p], IsUnit u ∧ ∀ a b, pairT P.A P.eps (tι a) (tι b) = u * (Dw.EF a b : ℤ_[p]) := by
  intro E _ _ _ H Dw p _ _ P tι ζ hprim hcomp hweil
  have hp : p.Prime := Fact.out
  have hpk : ∀ k : ℕ, 0 < p ^ k := fun k => pow_pos hp.pos k
  let z : Tate p ℂ_[p]ˣ := Tate.mk (fun k => ζ (p ^ k)) fun k =>
    ⟨(hprim (p ^ k) (hpk k)).pow_eq_one, by
      rw [pow_succ]; exact hcomp (p ^ k) p (hpk k) hp.pos⟩
  refine ⟨P.eps.equiv.symm z, ?_, fun a b => ?_⟩
  · by_contra hu
    have hlt : ‖P.eps.equiv.symm z‖ < 1 := PadicInt.mem_nonunits.1 hu
    obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hlt
    have h1 : z = P.eps.equiv (P.eps.equiv.symm z) := (P.eps.equiv.apply_symm_apply z).symm
    rw [hc, ← smul_eq_mul, map_smul] at h1
    have h2 : z.lev 1 = 1 := by
      rw [h1]
      change ((p : ℤ_[p]) • P.eps.equiv c).lev 1 = 1
      rw [Nat.cast_smul_eq_nsmul, lev_nsmul]
      simpa using (P.eps.equiv c).lev_pow 1
    have h3 : IsPrimitiveRoot (ζ p) p := by simpa using hprim p hp.pos
    exact h3.ne_one hp.one_lt (by simpa [z] using h2)
  · have hw : weilT P.A p (tι a) (tι b) = (Dw.EF a b : ℤ) • z := Tate.ext fun k => by
      rw [lev_weilT, lev_zsmul, hweil]
      rfl
    change P.eps.equiv.symm (weilT P.A p (tι a) (tι b)) = _
    rw [hw, map_zsmul, zsmul_eq_mul, mul_comm]

end GlobalTheory.TateUnitPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumScalarEqOneInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_scalar_eq_one_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.InertScalar.scalar_eq_one | exact GlobalTheory.InertScalar.scalar_eq_one | (intros; apply GlobalTheory.InertScalar.scalar_eq_one <;> assumption)
end

