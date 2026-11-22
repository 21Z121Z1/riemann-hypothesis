import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLineBasis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FderivTorusCoordinateRatioEqZeroOfTangentStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_torusCoordinateRatio_eq_zero_of_tangent : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → 0 < n → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → (∀ x, DifferentiableAt ℂ (u x) 0) → (∀ x, u x 0 = 1) → ∀ (v : epsR ℂ ⟶ D.P.A) (ν : Out.GtPt D (epsR ℂ)) (z : Fin g → ℂ), Out.GtPt.IsPull (spMap (epsScaleR ((n : ℂ)⁻¹))) (sB (epsR ℂ) v) ν → IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) z v.left → (∀ x j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (ex 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (ex z) x j) 0 z)) → ∀ x, fderiv ℂ (u x) 0 z = 0 := by
  first | exact @GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero | exact GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero | (intros; apply GlobalTheory.AbelianLetters.fderiv_ratio_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FibreComparison
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem fibre_comparison : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) , (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → ∃ T₀ : ℝ, ∀ (w : ℂ) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr, T₀ < w.im → IsPeriod (Fu.Di i) ty P → Fu.u i P = y₀ → IsFibAt A Xo.univ.t lin cst w y₀ π fr → Function.Surjective π ∧ ∃ (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La), (∀ v, (Fu.ex i P (h v)).left = (π v).left) ∧ (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧ ∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k := by
  intro _ _ E _ _ _ H _ D l Xo σ g ty Fu A lin cst halt hdim
  refine ⟨0, fun w i P y₀ π fr _ hP hy hF => ?_⟩
  subst hy
  have hrk : Module.finrank ℤ A.La = 2 * g := by
    rw [A.finrank_La, ← Module.finrank_mul_finrank ℝ ℂ A.V, Complex.finrank_real_complex, hdim]
  obtain ⟨h, gam, h1, h2, h3, -, h5⟩ := fibre_hom_eq_exponential Fu i hP hdim hrk A.EF A.EF_bijective (A.Pw w) π
    hF.add hF.hol hF.per fr hF.fr_hol (fun j v hv => ((hF.frm v).1 j hv).ne_zero)
    (fun j j' v hv => (hF.frm v).2 j j' hv) (lin w) (cst w) (fun a j v hv => hF.fac a v j hv) (halt w)
  obtain ⟨h6, gamO, h7⟩ := h5 (fun e => A.actV e) hF.act (A.Pw_smul w)
  refine ⟨fun y => ?_, h.toContinuousLinearEquiv, gamO.symm, fun v => ?_, fun u => ?_, fun u v => ?_, h6⟩
  · obtain ⟨z, rfl⟩ := Fu.ex_onto i P hP y
    exact ⟨h.symm z, by rw [h1, h.apply_symm_apply]⟩
  · rw [h1]; rfl
  · change P u = h _
    rw [h2, ← h7, gamO.apply_symm_apply]
  · rw [← h3, ← h7, ← h7, gamO.apply_symm_apply, gamO.apply_symm_apply]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScalingStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_eval_natural_weight_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∀ (S : Type) [CommRing S] [Algebra c.F S] [IsReduced S], (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c F z = φ (evR Xo c F y)) ∧ (IsDomain S → (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y) ∧ ∀ (s : S) (y y' : FrPt Xo c S), FrChg (fun _ => 1) s y y' → evR Xo c F y' = s ^ n * evR Xo c F y) := by
  first | exact @GlobalTheory.ArcQ.evR_natural_weight_scaling | exact GlobalTheory.ArcQ.evR_natural_weight_scaling | (intros; apply GlobalTheory.ArcQ.evR_natural_weight_scaling <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpecStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_germs_localRing_convergent_divisible : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  first | exact @GlobalTheory.GermRing.germs_spec | exact GlobalTheory.GermRing.germs_spec | (intros; apply GlobalTheory.GermRing.germs_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermFormSumSmul
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.LatticeCovolumeL2

theorem hermForm_sum_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (c : Fin g → ℂ)
    (p : Fin g → Fin g → ℂ) :
    hermForm Hm z (∑ j, c j • p j) = ∑ j, hermForm Hm z (p j) * (starRingEnd ℂ) (c j) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, RCLike.star_def, mul_comm]

theorem riem_inv {g : ℕ} (Hm τ : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g → Fin g → ℂ)
    (hq : ∀ l, q l = ∑ j, τ j l • p j) (h1 : ∀ k l, (hermForm Hm (p k) (p l)).im = 0)
    (h2 : ∀ k l, (hermForm Hm (p k) (q l)).im = -(if k = l then 1 else 0)) :
    (Matrix.of fun k l => (hermForm Hm (p k) (p l)).re) * τ.map Complex.im = 1 := by
  ext k l
  have := h2 k l
  rw [hq, hermForm_sum_smul, Complex.im_sum] at this
  simp only [Complex.mul_im, h1, Complex.conj_im, zero_mul, add_zero, mul_neg, Finset.sum_neg_distrib,
    neg_inj] at this
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

theorem polar {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    2 * (hermForm Hm z w).re =
      (hermForm Hm (z + w) (z + w)).re - (hermForm Hm z z).re - (hermForm Hm w w).re := by
  have hs : hermForm Hm w z = (starRingEnd ℂ) (hermForm Hm z w) := by
    simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hH.apply j i, RCLike.star_def]
    ring
  have : hermForm Hm (z + w) (z + w) = hermForm Hm z z + hermForm Hm z w + hermForm Hm w z + hermForm Hm w w := by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    ring
  rw [this, hs]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem cols {g : ℕ} (h τ : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g → Fin g → ℂ)
    (hp : ∀ k, h.mulVec (p k) = Pi.single k 1) (hq : ∀ k, h.mulVec (q k) = τ.mulVec (Pi.single k 1)) (l : Fin g) :
    q l = ∑ j, τ j l • p j := by
  have hs : Function.Surjective (Matrix.toLin' h) := fun v =>
    ⟨∑ j, v j • p j, by
      simp only [Matrix.toLin'_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hp]
      ext i
      simp [Pi.single_apply]⟩
  apply LinearMap.injective_iff_surjective.2 hs
  simp only [Matrix.toLin'_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hp, hq]
  ext i
  simp [Pi.single_apply]

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} [Algebra (FractionRing ℂ) ℂ]
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {a : ArcIn Dw l β ℂ (σ.comp β)}
  {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} {Ha : HolArc Y σ a χ W Fu}
  {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th)

theorem card_le (h1 : Module.finrank (𝓞 E) a.D₀.X = 1) :
    Fintype.card {k // k ∈ Θ.S} ≤ Module.finrank ℚ E := by
  refine le_trans ?_ (finrank_int_le h1)
  refine LinearIndependent.fintype_card_le_finrank
    (b := fun k : {k // k ∈ Θ.S} => Ha.y (Θ.bas (Pi.single (.inr k.1) 1))) ?_
  rw [Fintype.linearIndependent_iff]
  intro u hu k
  have : Ha.y (Θ.bas (∑ k : {k // k ∈ Θ.S}, u k • Pi.single (.inr k.1) 1)) = 0 := by
    simpa only [map_sum, map_zsmul] using hu
  have := (Θ.ker _).1 this k.1 k.2
  simpa [Pi.single_apply, Subtype.coe_inj] using this

theorem mem_span (v : (Fu.Di Ha.i).La) (hv : ∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF v v' = 0) :
    v ∈ Submodule.span ℤ (Set.range fun k : {k // k ∈ Θ.S} => Θ.bas (Pi.single (.inl k.1) 1)) := by
  obtain ⟨u, rfl⟩ := Θ.bas.surjective v
  obtain ⟨h1, h2⟩ := (Θ.orth u).1 hv
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun k => u (.inl k.1), ?_⟩
  simp only [← map_zsmul, ← map_sum]
  congr 1
  ext (i | i)
  · by_cases hi : i ∈ Θ.S
    · rw [Finset.sum_apply, Finset.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro b _ hb
        have : i ≠ b.1 := fun e => hb (Subtype.ext e.symm)
        simp [this]
      · simp
    · rw [h2 i hi, Finset.sum_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      have : i ≠ b.1 := fun e => hi (e ▸ b.2)
      simp [this]
  · simp [h1]

end

theorem key (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (k : U.Comp) (ξ' : Fin r → E)
    (hG : GoodEmb c σ) (hU : IsUnf U) (hξ : ξ' ≠ 0) (h1 : Module.finrank (𝓞 E) a.D₀.X = 1)
    (w : ℂ) (x : (U.X k).dom) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ))
    (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La)
    (hL : ∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w v))
    (hγ : ∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v')
    (t : (Uw.F.Di Ha.i).La) (ht : ∀ v', Ha.y v' = 0 → (Uw.F.Di Ha.i).EF t v' = 0)
    (htξ : (Uw.φ k (γ t) : Fin r → E) = ξ') :
    Fintype.card {k // k ∈ Θ.S} = Module.finrank ℚ E ∧ ∃ b : {k // k ∈ Θ.S} → E,
      (∀ e : E, e • ξ' ∈ (U.X k).Λ ↔ e ∈ Submodule.span ℤ (Set.range b)) ∧
      (((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det =
        |((Algebra.discr ℚ b : ℚ) : ℝ)| * (∏ τ, (((U.X k).tt ξ' x.1 τ)⁻¹ / 2)) ^ 2 * ((Θ.τ w).map Complex.im).det := by
  let ψ : (Uw.F.Di Ha.i).La →ₗ[𝓞 E] (Fin r → E) :=
    (U.X k).Λ.subtype ∘ₗ (γ.trans (Uw.φ k)).toLinearMap
  have hψ : ∀ v, ψ v = (Uw.φ k (γ v) : Fin r → E) := fun _ => rfl
  have hinj : Function.Injective ψ := Subtype.val_injective.comp (γ.trans (Uw.φ k)).injective
  have hrange : LinearMap.range ψ = (U.X k).Λ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hψt : ψ t = ξ' := htξ
  obtain ⟨hcard, b, hb, hspan⟩ := exists_line_basis ψ hinj
    (fun v => ∀ v', Ha.y v' = 0 → (Uw.F.Di Ha.i).EF v v' = 0)
    (fun k : {k // k ∈ Θ.S} => Θ.bas (Pi.single (.inl k.1) 1))
    (fun c v hv v' hv' => by
      rw [Datum.adj]; exact hv _ (by rw [map_smul, hv', smul_zero]))
    (fun m v hm hv v' hv' => by
      have := hv v' hv'
      rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hm)
    (mem_span Θ) (card_le Θ h1) t ht (hψt ▸ hξ)
  rw [hψt] at hb hspan
  rw [hrange] at hspan
  refine ⟨hcard, b, hspan, ?_⟩
  obtain ⟨Hm, hR⟩ := (Uw.period k x).2.2.2.2
  have hmaj := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k x Hm hG hU hR).1
  let p : Fin Uw.g → Fin Uw.g → ℂ := fun j => Uw.Pm k x (γ (Θ.bas (Pi.single (.inl j) 1)))
  let q : Fin Uw.g → Fin Uw.g → ℂ := fun j => Uw.Pm k x (γ (Θ.bas (Pi.single (.inr j) 1)))
  have hq : ∀ j, q j = ∑ i, Θ.τ w i j • p i := fun j => by
    simp only [p, q, hL, ← map_smul, ← map_sum]
    congr 1
    exact cols Θ.h (Θ.τ w) _ _ (fun i => (Θ.per w i).1) (fun i => (Θ.per w i).2) j
  have hM := riem_inv Hm (Θ.τ w) p q hq
    (fun i j => by simp [p, hR.2.2, hγ, Θ.sympl, omegaStd])
    (fun i j => by
      simp only [p, q, hR.2.2, hγ, Θ.sympl, omegaStd]
      by_cases hij : i = j <;> simp [Pi.single_apply, hij, eq_comm])
  have hJ := det_compl _ _ hM (· ∈ Θ.S)
  have hQ : ∀ v (e : E), ψ v = e • ξ' → (hermForm Hm (Uw.Pm k x (γ v)) (Uw.Pm k x (γ v))).re =
      ∑ τ : (U.X k).Ψ, Complex.normSq (τ.1 e) * ((U.X k).tt ξ' x.1 τ)⁻¹ := by
    intro v e hv
    rw [hmaj, ← hψ, hv]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : Data.emb τ.1 (e • ξ') = τ.1 e • Data.emb τ.1 ξ' := by
      ext i; simp [Data.emb]
    rw [this, UnipMove.DeltaValuation.maj_smul, Data.tt, one_div, inv_inv]
    ring
  have hD := det_gram hcard (U.X k).Ψ (U.X k).cmType b (fun τ => ((U.X k).tt ξ' x.1 τ)⁻¹)
    (Matrix.toSquareBlockProp (Matrix.of fun i j => (hermForm Hm (p i) (p j)).re) (· ∈ Θ.S)) (fun i j => by
      have e0 := polar hR.1 (p i.1) (p j.1)
      have e1 := hQ _ _ (hb i)
      have e2 := hQ _ _ (hb j)
      have e3 := hQ (Θ.bas (Pi.single (.inl i.1) 1) + Θ.bas (Pi.single (.inl j.1) 1)) (b i + b j)
        (by rw [map_add, hb i, hb j, add_smul])
      rw [map_add, map_add] at e3
      simp only [p] at e0
      rw [e1, e2, e3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib] at e0
      change (hermForm Hm (p i.1) (p j.1)).re = _
      refine mul_left_cancel₀ (two_ne_zero) (e0.trans ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_add, Complex.normSq_add]
      ring)
  rw [← hD]
  convert hJ using 2 <;> first | rfl | congr!

theorem final {g s : ℕ} (hs : s ≤ g) {dY dO D : ℝ} (hY : 0 < dY) (hD : 0 < D) {ι : Type} [Fintype ι] (u : ι → ℝ)
    (hu : ∀ i, 0 < u i) (h : dO = D * (∏ i, (u i / 2)) ^ 2 * dY) :
    (Real.sqrt (2 ^ g * dY))⁻¹ = (Real.sqrt (2 ^ (g - s) * dO))⁻¹ *
      (Real.sqrt D * ((Real.sqrt (2 ^ s))⁻¹ * ∏ _i : ι, (2 : ℝ)⁻¹)) * ∏ i, u i := by
  have hp : 0 < ∏ i, (u i / 2) := Finset.prod_pos fun i _ => half_pos (hu i)
  have e : (∏ _i : ι, (2 : ℝ)⁻¹) * ∏ i, u i = ∏ i, (u i / 2) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => by ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_sub_cancel_left, h, pow_add, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, e]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul hD.le, Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]
  have := Real.sqrt_pos.2 hY
  have := Real.sqrt_pos.2 hD
  have : 0 < Real.sqrt (2 ^ s) := by positivity
  have : 0 < Real.sqrt (2 ^ m) := by positivity
  field_simp

theorem discr_bound {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = Module.finrank ℚ E) (b : ι → E)
    (h : ∀ c : 𝓞 E, (c : E) ∈ Submodule.span ℤ (Set.range b)) :
    Algebra.discr ℚ b ≠ 0 ∧ |Algebra.discr ℚ b| ≤ |((NumberField.discr E : ℤ) : ℚ)| := by
  classical
  let f : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ ι := Fintype.equivOfCardEq (by
    rw [hι, Module.finrank_eq_card_basis (integralBasis E)])
  have e : Algebra.discr ℚ (integralBasis E ∘ f.symm) = ((NumberField.discr E : ℤ) : ℚ) := by
    rw [Algebra.discr_reindex, coe_discr]
  rw [← e]
  refine discr_le b _ (fun i => ?_) (by rw [e]; exact_mod_cast discr_ne_zero E)
  rw [Function.comp_apply, integralBasis_apply]
  exact h _

theorem det_im_eq_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (k : U.Comp) (ξ' : Fin r → E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → Module.finrank (𝓞 E) a.D₀.X = 1 → ∃ C : ℝ, 0 < C ∧ C ≤ Real.sqrt |((NumberField.discr E : ℤ) : ℝ)| ∧ ∀ (w : ℂ) (x : (U.X k).dom) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), Ha.T < w.im → (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w v)) → (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') → (∃ t, (∀ v', Ha.y v' = 0 → (Uw.F.Di Ha.i).EF t v' = 0) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') → (Real.sqrt (2 ^ Uw.g * ((Θ.τ w).map Complex.im).det))⁻¹ = (Real.sqrt (2 ^ (Uw.g - Θ.S.card) * ((((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ * C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹ := by
  intro E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha th Θ k ξ' hG hU hξ h1
  by_cases hex : Fintype.card {k // k ∈ Θ.S} = Module.finrank ℚ E ∧ ∃ b : {k // k ∈ Θ.S} → E,
      ∀ e : E, e • ξ' ∈ (U.X k).Λ ↔ e ∈ Submodule.span ℤ (Set.range b)
  · obtain ⟨hcard, b₀, hb₀⟩ := hex
    have hO : ∀ c : 𝓞 E, (c : E) • ξ' ∈ (U.X k).Λ := fun c => (U.X k).Λ.smul_mem c hξ.1
    obtain ⟨n0, le0⟩ := discr_bound hcard b₀ (fun c => (hb₀ _).1 (hO c))
    have hD : (0 : ℝ) < |((Algebra.discr ℚ b₀ : ℚ) : ℝ)| := abs_pos.2 (by exact_mod_cast n0)
    refine ⟨Real.sqrt |((Algebra.discr ℚ b₀ : ℚ) : ℝ)| *
      ((Real.sqrt (2 ^ Θ.S.card))⁻¹ * ∏ _i : (U.X k).Ψ, (2 : ℝ)⁻¹), by positivity, ?_, ?_⟩
    · refine le_trans (mul_le_of_le_one_right (Real.sqrt_nonneg _) ?_) (Real.sqrt_le_sqrt (by exact_mod_cast le0))
      refine mul_le_one₀ (inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (one_le_pow₀ one_le_two))) (by positivity) ?_
      exact Finset.prod_le_one (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    · rintro w x L γ hw hL hγ ⟨t, ht, htξ⟩
      obtain ⟨-, b, hb, hdet⟩ := key E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hG hU hξ.2.2 h1 w x L γ hL hγ
        t ht htξ
      obtain ⟨n1, l1⟩ := discr_le b b₀ (fun i => (hb _).1 ((hb₀ _).2 (Submodule.subset_span ⟨i, rfl⟩))) n0
      obtain ⟨-, l2⟩ := discr_le b₀ b (fun i => (hb₀ _).1 ((hb _).2 (Submodule.subset_span ⟨i, rfl⟩))) n1
      have e : |((Algebra.discr ℚ b : ℚ) : ℝ)| = |((Algebra.discr ℚ b₀ : ℚ) : ℝ)| := by
        exact_mod_cast le_antisymm l1 l2
      rw [e] at hdet
      refine final (by simpa using Finset.card_le_univ Θ.S) (Θ.pos w hw).2.det_pos hD _ (fun τ => ?_) hdet
      rw [Data.tt, one_div, inv_inv]
      refine mul_pos ?_ ((U.X k).maj_pos x.2 τ ?_)
      · exact mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero τ.1).2 (U.X k).ξ0_ne))
      · intro h0
        exact hξ.2.2 (funext fun i => (map_eq_zero τ.1).1 (congrFun h0 i))
  · refine ⟨_, Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero E)), le_rfl, ?_⟩
    rintro w x L γ hw hL hγ ⟨t, ht, htξ⟩
    obtain ⟨hc, b, hb, -⟩ := key E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hG hU hξ.2.2 h1 w x L γ hL hγ
      t ht htξ
    exact absurd ⟨hc, b, hb⟩ hex

end GlobalTheory.LatticeCovolumeL2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemRealSpanPeriodsOfCharacterKernelStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_realSpan_periods_of_character_kernel : ∀ (g n : ℕ) (S : Finset (Fin g)) (h τ : Matrix (Fin g) (Fin g) ℂ) (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)) (ℓ : Fin g → (Fin g → ℂ) →ₗ[ℂ] ℂ), 0 < n → (τ.map Complex.im).PosDef → (∀ k, h.mulVec (p (Pi.single (.inl k) 1)) = Pi.single k 1 ∧ h.mulVec (p (Pi.single (.inr k) 1)) = τ.mulVec (Pi.single k 1)) → (∀ k ∈ S, ∀ k' ∈ S, ∀ s : ℂ, Complex.exp (ℓ k (s • p (Pi.single (.inl k') 1))) = eTwoPi (n * s * if k' = k then 1 else 0)) → (∀ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) → ∀ k ∈ S, Complex.exp (ℓ k (p u)) = 1) → ∀ z : Fin g → ℂ, (∀ k ∈ S, ℓ k z = 0) → z ∈ Submodule.span ℝ {q | ∃ u : Fin g ⊕ Fin g → ℤ, (∀ k ∈ S, u (.inr k) = 0) ∧ q = p u} := by
  first | exact @GlobalTheory.PeriodSpan.mem_span_periods | exact GlobalTheory.PeriodSpan.mem_span_periods | (intros; apply GlobalTheory.PeriodSpan.mem_span_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyConstPts
section
namespace GlobalTheory.ConstPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem nonempty_constPts : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) , Nonempty (ConstPts W Λ) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ
  choose g x τ h₁ h₂ h₃ h₄ using fun v : Λ.A.V => exists_constPoint W Λ.u (Λ.ex0 v) v.2 (Λ.ex0_b v)
  exact ⟨⟨g, h₁, x, h₂, h₃, τ, h₄⟩⟩

end GlobalTheory.ConstPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficients
section
noncomputable section

namespace GlobalTheory.SpanFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts GlobalTheory.AmpleSpan
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem top_le_of_mem {K : Type} [Field K] {Z : Scheme.{0}} (x : Sp K ⟶ Z) {V : Z.Opens} (p : Sp K) (h : x p ∈ V) :
    ⊤ ≤ x ⁻¹ᵁ V := fun q _ => by
  obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact h

theorem exists_lift {Z Y : Scheme.{0}} (x : Y ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ x' : Y ⟶ V.toScheme, x' ≫ V.ι = x :=
  ⟨IsOpenImmersion.lift V.ι x (by rintro _ ⟨p, rfl⟩; exact ⟨⟨x p, h trivial⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩

theorem nonempty_coords_of_basis (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    [StarRing (𝓞 E)] {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}}
    [IsLocallyNoetherian S] {s : S ⟶ Sp B} (o : Obj D l bb s) {A : AnArc (𝓞 E)} {y : Sp ℂ⸨X⸩ ⟶ S}
    (Φ : GenPts A o.t y) (hA : AnFin A) (hΦ : Φ.Rational) (N : ℕ) [NeZero N] (hN : 4 ≤ N) {n : ℕ} {α : Fin n → A.X}
    {th : Fin n → (Fin A.gB → ℂ) → ℂ} (hth : ∀ i, th i ∈ A.Theta N (α i))
    (hli : LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum N (α i) (th i) v))
    (hsp : ∀ α', ∀ th' ∈ A.Theta N α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧
      ∀ v, A.FSum N α' th' v = ∑ i, r i * A.FSum N (α i) (th i) v)
    (hrat : ∀ f : A.V → ℂ⸨X⸩, IsComb A N Set.univ f → (∀ v, f v ∈ Conv.convLaurent) →
      ∃ T : ℝ, IsComb A N (Conv.halfRing T) f ∧ ∀ v, f v ∈ Conv.halfRing T) : Nonempty (Coords Φ N) := by
  have hLB : o.t.PP.L.IsLB := o.t.PP.isLB
  have := o.proper
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  have hy := top_le_of_mem y _ hyU
  have : IsAffine U := hU
  obtain ⟨m, b, hb⟩ := exists_span_powOver hL.secBaseChange (objPolAV o) (N := N) (by omega) hU
  have emb : EmbedsBy (o.t.G.hom ∣_ U) b :=
    embedsBy_powOver o.t.G (hL.ample S (objPolAV o) N hN).2 hU b
      (hb _ _ (𝟙 _) _ (𝟙 _) IsPullback.of_id_fst (Fin N) (fun _ => 1) _ (Category.id_comp _) (by simp) b
        fun i => (secScal_iff_sval hLB).2 fun Z r z J _ => by rw [Category.comp_id])
  obtain ⟨g, hg⟩ := exists_lift y hy
  obtain ⟨h, e, sq⟩ := exists_isPullback_restrict o.t.G (φ := pullback.fst o.t.G.hom y)
    (f' := pullback.snd o.t.G.hom y) (g := g) (by rw [hg]; exact IsPullback.of_hasPullback _ _)
  choose b' hb' _ using fun i => existsUnique_secScal hLB (φ := fun _ : Fin N => (o.t.G.hom ⁻¹ᵁ U).ι)
    (ε := fun _ => 1) (h := h) (formEq_const (K' := Fin 1) (ε' := fun _ => (N : ℤ)) e (by simp)) (b i)
  have span := hb _ _ h _ g sq (Fin 1) (fun _ => (N : ℤ)) _ e (by simp) b' hb'
  choose f hf hf' using fun i => Φ.span N (b' i)
  have hfib : ∀ v, fib (Φ.x v) ≫ pullback.fst o.t.G.hom y = (Φ.x v).left := fun v => pullback.lift_fst _ _ _
  have val : ∀ i v (x' : Sp ℂ⸨X⸩ ⟶ (o.t.G.hom ⁻¹ᵁ U).toScheme) (j : o.t.PP.L.ι),
      x' ≫ (o.t.G.hom ⁻¹ᵁ U).ι = (Φ.x v).left → ⊤ ≤ (Φ.x v).left ⁻¹ᵁ o.t.PP.L.U j →
      valR x' ((Out.powOver o.t.G o.t.PP.L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f i v * Φ.τ v j ^ N :=
    fun i v x' j hx hj => by
      obtain rfl : x' = fib (Φ.x v) ≫ h := by
        rw [← cancel_mono (o.t.G.hom ⁻¹ᵁ U).ι, Category.assoc, e, hfib, hx]
      rw [← hfib] at hj
      exact (valR_of_secScal e (hb' i) _ j hj).trans (hf' i v j hj)
  have chart : ∀ v, ∃ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ o.t.PP.L.U j := fun v => by
    obtain ⟨j, hj⟩ := exists_chart hLB ((Φ.x v).left (default : PrimeSpectrum ℂ⸨X⸩))
    exact ⟨j, top_le_of_mem _ _ hj⟩
  have conv : ∀ i v, f i v ∈ Conv.convLaurent := fun i v => by
    obtain ⟨x₀, hx₀⟩ := hΦ.1 v
    obtain ⟨j, hj⟩ := chart v
    have down : ∀ V, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ V → ⊤ ≤ x₀ ⁻¹ᵁ V := fun V hV => by
      rw [← hx₀] at hV
      exact top_le_of_mem x₀ _ (hV (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial)
    obtain ⟨x₁, rfl⟩ := exists_lift x₀ (down (o.t.G.hom ⁻¹ᵁ U) (by
      have w : (Φ.x v).left ≫ o.t.G.hom = y := Over.w (Φ.x v)
      rw [← Scheme.Hom.comp_preimage, w]
      exact hy))
    have h1 := val i v _ j ((Category.assoc _ _ _).trans hx₀) hj
    have hx₁ : ⊤ ≤ x₁ ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L U N).U (fun _ => j) :=
      fun p _ => Set.mem_iInter.2 fun _ => down _ hj (x := p) trivial
    replace h1 := (HolHom.valR_spMap _ x₁ _ hx₁ _).symm.trans h1
    have h2 : Φ.τ v j ^ N ≠ 0 := pow_ne_zero _ ((Φ.frm v).1 j hj).ne_zero
    rw [← div_eq_iff h2] at h1
    rw [← h1]
    exact div_mem (Subtype.prop _) (pow_mem (hΦ.2 v j hj) _)
  obtain ⟨T, hm, hc, hz⟩ := exists_no_common_zero hA (by omega) hth hli hsp f (fun i => hrat _ (hf i) (conv i))
    fun β t ht => by
      obtain ⟨c, hc⟩ := span (Φ.sig N β t)
      refine ⟨fun i => valR (𝟙 _) ⊤ (c i), fun v => ?_⟩
      obtain ⟨j, hj⟩ := chart v
      have h2 : Φ.τ v j ^ N ≠ 0 := pow_ne_zero _ ((Φ.frm v).1 j hj).ne_zero
      rw [← hfib] at hj
      have hw : ⊤ ≤ fib (Φ.x v) ⁻¹ᵁ LB.wchart o.t.PP.L (fun _ : Fin 1 => pullback.fst o.t.G.hom y) (fun _ => j) :=
        fun z hz => Set.mem_iInter.2 fun _ => hj hz
      refine mul_right_cancel₀ h2 ((Φ.val N β t ht v j hj).symm.trans ?_)
      refine (congrArg (valR (fib (Φ.x v)) _) (hc fun _ => j)).trans ((HolHom.valR_eq _ _ hw _).trans ?_)
      rw [Finset.sum_mul]
      refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans ?_)
      rw [_root_.mul_assoc, ← hf' i v j hj]
      refine congrArg₂ (· * ·) ?_ (HolHom.valR_eq _ _ hw _).symm
      refine (HolHom.valR_eq _ _ hw _).symm.trans ((HolHom.valR_appLE _ _ ⊤ _ le_top _ hw).trans ?_)
      rw [fib, pullback.lift_snd]
  exact ⟨⟨T, U, hU, hy, m, b, emb, fun i v => ⟨f i v, hm i v⟩, hc, val, hz⟩⟩

theorem nonempty_coords : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) , AnFin A → Φ.Rational → ∀ (N : ℕ) [NeZero N], 4 ≤ N → Nonempty (Coords Φ N) := by
  intro hL _ E _ _ _ H _ D l B _ bb S _ s o A y Φ hA hΦ N _ hN
  obtain ⟨n, α, th, -, hth, hli, -, hsp⟩ := AnArc.exists_basis_FSum _ A hA N
  exact nonempty_coords_of_basis hL o Φ hA hΦ N hN hth hli hsp (exists_isComb_halfRing _ A hA N)

end GlobalTheory.SpanFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorPowScaleInvEqStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_pow_scale_inv_eq : ∀ (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ), 0 < n → IsTangent v → spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  first | exact @GlobalTheory.AbelianLetters.scale_tangent_pow | exact GlobalTheory.AbelianLetters.scale_tangent_pow | (intros; apply GlobalTheory.AbelianLetters.scale_tangent_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaCharOffNeZeroDifferentiableQuasiPeriodicStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCharOff_ne_zero_differentiable_quasiPeriodic' : ∀ (g : ℕ) (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ k ∈ S, c₁ k = 0) → thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (thetaCharOff S τ c₁ c₂) ∧ ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z, thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) = a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) * thetaCharOff S τ c₁ c₂ z := by
  first | exact @GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic | exact GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic | (intros; apply GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSumShiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_shift_eq_single_mul_fSum : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ (k : ℕ) [NeZero k] (la : A.La), (∀ α, (k : ℤ) ∣ A.be la.y α) → ∃ cz : A.V → ℂ, (∀ z, cz z ≠ 0) ∧ ∀ α, ∀ th ∈ A.Theta k α, ∃ th' ∈ A.Theta k (α + la.y), (th ≠ 0 → th' ≠ 0) ∧ ∀ z, (∀ F, IsFShift A k α th la z F ↔ F = HahnSeries.single (A.be la.y α / k) (cz z) * A.FSum k (α + la.y) th' z) ∧ ∀ w : ℂ, A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) = cz z * eTwoPi (w * ((A.be la.y α / k : ℤ) : ℂ)) * A.Sum k (α + la.y) th' w z := by
  first | exact @GlobalTheory.ArcPts.theta_sum_shift | exact GlobalTheory.ArcPts.theta_sum_shift | (intros; apply GlobalTheory.ArcPts.theta_sum_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioDifferentiableAtOriginStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinateRatio_differentiableAt_origin : ∀ [Algebra (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (s₀ : Out.GtPt D D.P.A), s₀.b = 𝟙 D.P.A ^ n → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n s₀ u → ∀ x, DifferentiableAt ℂ (u x) 0 := by
  first | exact @GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero | exact GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero | (intros; apply GlobalTheory.AbelianLetters.IsRatio.differentiableAt_zero <;> assumption)
end

