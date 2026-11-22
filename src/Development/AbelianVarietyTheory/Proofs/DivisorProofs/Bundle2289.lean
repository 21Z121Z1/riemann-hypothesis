import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapCompatibility
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.GenUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}

theorem rows_indep {A K : Type} [CommRing A] [Field K] (φ : A →+* K) {n g : ℕ} (h U : Fin n → Fin g → A)
    (hu : IsUnit (pairDet h U)) (a : Fin n → K) (ha : ∀ b, ∑ i, a i * φ (U i b) = 0) : a = 0 := by
  by_contra ha0
  let M : Matrix (Fin n) (Fin n) K := fun k k' => ∑ b, φ (h k' b) * φ (U k b)
  have hM : φ (pairDet h U) = M.det := by
    rw [pairDet, RingHom.map_det]
    congr 1
    ext k k'
    simp [M, map_sum, map_mul]
  have hdet : M.det = 0 := by
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨a, ha0, ?_⟩
    ext k'
    simp only [Matrix.vecMul, dotProduct, M, Pi.zero_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    calc ∑ k, a k * (φ (h k' b) * φ (U k b)) = φ (h k' b) * ∑ k, a k * φ (U k b) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [ha b, mul_zero]
  exact (hu.map φ).ne_zero (hM.trans hdet)

theorem rows_data (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) {A K : Type} [CommRing A] [Field K] [Algebra c.F K]
    (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A) (φ : A →+* K) {g : ℕ} (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left))
    (hbas : IsTanBasis Y.t ξ e) (yy : Sp K ⟶ Xo'.XF c') (hyy : yy ≫ Y.j = spMap φ ≫ ξ) (y : FrPt Xo c K)
    (hyx : yy ≫ r ≫ pullback.fst _ _ = y.x) (ρ : E →+* ℂ) (U : Fin (Dw.mult ρ) → Fin g → A)
    (heig : EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W ρ))) (bcV Y.t φ e) (fun k b => φ (U k b)))
    (hσ : ∀ a, φ (β (embV c' W ρ a)) = algebraMap c.F K (embK c ρ a)) :
    ∃ (w : Fin (Dw.mult ρ) → (Sp (DualNumber K) ⟶ Y.oF.t.G.left)) (G : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) K),
      (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e) (fun b => φ (U i b)) (w i ≫ Y.m.φ)) ∧
      (∀ i, IsCombAt y.x (y.u ρ) (G i) (w i ≫ ν.φ)) ∧
      (∀ h : Fin (Dw.mult ρ) → Fin g → A, IsUnit (pairDet h U) → G.det ≠ 0) := by
  have hb := isTanBasis_bc hbas φ
  let Eb : Fin g → PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G := fun b => GlobalTheory.LieMet.tanOf (hb.1 b)
  let C : Fin (Dw.mult ρ) → PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G := fun i => ∑ b, φ (U i b) • Eb b
  let Pm := GlobalTheory.LieMet.pushE Y.m yy hyy
  let Pν := GlobalTheory.LieMet.pushE ν yy hyx
  let N : Fin (Dw.mult ρ) → PullbackSections.TanM y.x Xo.univ.t.G := fun i => Pν (Pm.symm (C i))
  have hCc : ∀ i, IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (fun b => φ (U i b)) (PullbackSections.tv (C i)).left :=
    fun i => (GlobalTheory.LieMet.isComb_iff Eb _ (C i)).2 rfl
  have hsm : ∀ (a : K) (v : PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G), (PullbackSections.tv (a • v)).left = spMap (epsMul a) ≫ (PullbackSections.tv v).left :=
    fun _ _ => rfl
  have hact : ∀ (a : 𝓞 E) (v : PullbackSections.TanM (spMap φ ≫ ξ) Y.t.G),
      (PullbackSections.tv (PullbackSections.actR Y.t.act a v)).left = (PullbackSections.tv v).left ≫ (Y.t.act.act a).left := fun _ _ => rfl

  have hCe : ∀ i (a : 𝓞 E), PullbackSections.actR Y.t.act a (C i) = φ (β (embV c' W ρ a)) • C i := fun i a =>
    GlobalTheory.LieMet.tan_ext (by rw [hact, hsm]; exact heig i _ (hCc i) a)
  have hNe : ∀ i (a : 𝓞 E), PullbackSections.actR Xo.univ.t.act a (N i) = φ (β (embV c' W ρ a)) • N i := by
    intro i a
    have h1 : PullbackSections.actR Y.oF.t.act a (Pm.symm (C i)) = φ (β (embV c' W ρ a)) • Pm.symm (C i) := by
      apply Pm.injective
      refine (GlobalTheory.LieMet.pushE_act Y.m yy hyy a _).trans ?_
      rw [map_smul]
      simp only [Pm, LinearEquiv.apply_symm_apply]
      exact hCe i a
    show PullbackSections.actR Xo.univ.t.act a (Pν (Pm.symm (C i))) = _
    refine (GlobalTheory.LieMet.pushE_act ν yy hyx a _).symm.trans ?_
    show Pν _ = _
    rw [h1, map_smul]
  have hN : ∀ i, ∃! a, IsCombAt y.x (y.u ρ) a (PullbackSections.tv (N i)).left := fun i =>
    y.basis ρ _ (GlobalTheory.LieMet.isTan_tv (N i)) fun a => by
      rw [← hσ]
      exact congrArg (fun v => (PullbackSections.tv v).left) (hNe i a)
  choose G hG using fun i => (hN i).exists
  refine ⟨fun i => (PullbackSections.tv (Pm.symm (C i))).left, G, fun i => ?_, fun i => ?_, fun h hu hd => ?_⟩
  · rw [hyy, ← GlobalTheory.LieMet.left_pushE Y.m yy hyy, LinearEquiv.apply_symm_apply]
    exact hCc i
  · rw [← GlobalTheory.LieMet.left_pushE ν yy hyx]
    exact hG i
  · obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    let Ub : Fin (Dw.mult ρ) → PullbackSections.TanM y.x Xo.univ.t.G := fun j => GlobalTheory.LieMet.tanOf (y.tan ρ j)
    have hNi : ∀ i, N i = ∑ j, G i j • Ub j := fun i => (GlobalTheory.LieMet.isComb_iff Ub (G i) (N i)).1 (hG i)
    have h0 : ∑ i, a i • N i = 0 := by
      simp only [hNi, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrFun ha j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [this, zero_smul]
    have h1 : ∑ i, a i • C i = 0 := by
      have : Pν (Pm.symm (∑ i, a i • C i)) = 0 := by
        rw [← h0]; simp only [map_sum, map_smul]; rfl
      exact Pm.symm.injective (Pν.injective (this.trans ((congrArg Pν (map_zero Pm.symm)).trans (map_zero Pν)).symm))
    let cv : Fin g → K := fun b => ∑ i, a i * φ (U i b)
    have h2 : ∑ i, a i • C i = ∑ b, cv b • Eb b := by
      simp only [C, cv, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h3 : cv = 0 := by
      have hz := (GlobalTheory.LieMet.isComb_iff Eb cv 0).2 (h2.symm.trans h1).symm
      have hz' := (GlobalTheory.LieMet.isComb_iff Eb 0 0).2 (by simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero])
      exact (hbas.2 K φ _ (GlobalTheory.LieMet.isTan_tv 0)).unique hz hz'
    exact ha0 (rows_indep φ h U hu a fun b => congrFun h3 b)

end GlobalTheory.FlatModel.GenUniq

namespace GlobalTheory.FlatModel

theorem secValAt_unique_generic : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v → SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k φ v' → v = v' := by
  intro _ _ _ E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x _ Z τ s la p Xw hp hcov A _ _ _ ξ β _ hξs _ hξX g e U₁
    h₁ U₂ h₂ hbas heig hu₁ hu₂
  let K := FractionRing A
  let φ : A →+* K := algebraMap A K
  refine ⟨K, inferInstance, φ, IsFractionRing.injective A K, fun v v' hv hv' => ?_⟩
  have hsc : ∀ {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (f' : R₂ →+* R₃),
      spMap (f'.comp f) = spMap f' ≫ spMap f := fun f f' => by
    rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hinj : ∀ {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (f f' : R₁ →+* R₂), spMap f = spMap f' → f = f' :=
    fun f f' h => congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h)
  have hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hcov.2.2.1 Y
  have hrange : Set.range (spMap φ ≫ ξ) ⊆ Set.range Y.j := by
    rintro _ ⟨z, rfl⟩
    refine hcov.2.2.2.2.1 ?_
    have hz : (spMap φ).base z = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap φ (z : PrimeSpectrum K).asIdeal = ⊥
      haveI := (z : PrimeSpectrum K).isPrime
      rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum K).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective A K)
    show ξ.base ((spMap φ).base z) ∈ Xw
    rw [hz]
    exact hξX
  let yy := IsOpenImmersion.lift Y.j (spMap φ ≫ ξ) hrange
  have hyy : yy ≫ Y.j = spMap φ ≫ ξ := IsOpenImmersion.lift_fac _ _ _
  let ψ : c'.F →+* K := (Spec.preimage (yy ≫ pullback.snd _ _)).hom
  have hψ : spMap ψ = yy ≫ pullback.snd _ _ := Spec.map_preimage _
  letI : Algebra c.F K := (ψ.comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have hψβ : ψ.comp (c'.V W).subtype = φ.comp β := by
    refine hinj _ _ ?_
    rw [hsc, hsc, hψ, Category.assoc, ← GlobalTheory.LocM.BaseMdl.j_s, ← Category.assoc, hyy, Category.assoc, hξs]
  have hsnd : yy ≫ r ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [hcov.1, ← Category.assoc, ← hψ]
    exact (hsc _ _).symm
  have hx : (yy ≫ r ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
    rw [sOf, hsc, ← hsnd]
    simp only [Category.assoc, pullback.condition]
  obtain ⟨y, hyx⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (yy ≫ r ≫ pullback.fst _ _) hx
  have hT : Tested y := GlobalTheory.NonIntegralFrameExample.spread_holds Xo c K y
  have hpt : GlobalTheory.AllWt.ptF y = yy ≫ r := by
    unfold GlobalTheory.AllWt.ptF
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hyx, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, hsnd]
  have hσ : ∀ (ρ : E →+* ℂ) (a : 𝓞 E), φ (β (embV c' W ρ a)) = algebraMap c.F K (embK c ρ a) := by
    intro ρ a
    rw [← RingHom.comp_apply φ β, ← hψβ]
    show ψ ((embV c' W ρ a : c'.V W) : c'.F) = ψ (IntermediateField.inclusion hle (embK c ρ a))
    congr 1
  obtain ⟨w₁, G₁, hw₁, hg₁, hd₁⟩ :=
    GenUniq.rows_data Y r ν ξ β φ e hbas yy hyy y hyx.symm τ.1 U₁ (heig K φ).1 (hσ τ.1)
  obtain ⟨w₂, G₂, hw₂, hg₂, -⟩ :=
    GenUniq.rows_data Y r ν ξ β φ e hbas yy hyy y hyx.symm (conjEmb τ.1) U₂ (heig K φ).2 (hσ _)
  have e₁ := hv inferInstance yy hyy y hT hpt w₁ w₂ G₁ G₂ hw₁ hw₂ hg₁ hg₂
  have e₂ := hv' inferInstance yy hyy y hT hpt w₁ w₂ G₁ G₂ hw₁ hw₂ hg₁ hg₂
  exact mul_right_cancel₀ (hd₁ h₁ hu₁) (e₁.trans e₂.symm)

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherian
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.ModelNoeth

theorem isNoetherianRing_valuationSubring {L : Type} [Field L] [NumberField L] (V : ValuationSubring L) :
    IsNoetherianRing V := by
  by_cases h : ∃ n : ℕ, n ≠ 0 ∧ (n : L) ∈ V.nonunits
  · obtain ⟨n, hn, hV⟩ := h
    have := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hn hV).1
    infer_instance
  · push_neg at h
    have hall : ∀ x : L, x ∈ V := by
      intro x
      have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
      have := Algebra.IsAlgebraic.trans ℤ ℚ L
      obtain ⟨y, hy0, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple
      have hyx : y • x ∈ V := by
        have h' : IsIntegral V (y • x) := hy.tower_top
        obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp h'
        exact hz ▸ z.2
      have hn : (y.natAbs : L) ∉ V.nonunits := h _ (by simpa using hy0)
      rw [ValuationSubring.mem_nonunits_iff, not_lt] at hn
      have hn1 : V.valuation (y.natAbs : L) = 1 :=
        le_antisymm (by simpa using V.valuation_le_one (y.natAbs : V)) hn
      have hy1 : V.valuation (y : L) = 1 := by
        rcases Int.natAbs_eq y with e | e
        · rw [e]; simpa using hn1
        · rw [e]; simpa using hn1
      rw [← V.valuation_le_one_iff] at hyx ⊢
      rw [zsmul_eq_mul, map_mul, hy1, _root_.one_mul] at hyx
      exact hyx
    have hF : IsField V := by
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
      refine ⟨⟨(a : L)⁻¹, hall _⟩, Subtype.ext ?_⟩
      have : (a : L) ≠ 0 := fun e => ha (Subtype.ext e)
      simp [this]
    letI := hF.toField
    infer_instance

end GlobalTheory.ModelNoeth

open GlobalTheory.ModelNoeth in
theorem GlobalTheory.ModelNoeth.isNoetherianRing_of_isOpenImmersion :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X), IsOpenImmersion ξ → IsNoetherianRing A := by
  intro E _ _ _ H Dw l' Xo' c' W Y A _ ξ hξ
  have := c'.fin
  have : NumberField c'.F := {}
  have : IsNoetherianRing (c'.V W) := isNoetherianRing_valuationSubring _
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  have : IsProper (PSpace.str (c'.V W) N) := isProper_str _ _
  have : LocallyOfFiniteType (i ≫ PSpace.str (c'.V W) N) := inferInstance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str (c'.V W) N)
  exact isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion ξ)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_p_adic_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
      (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]),
      HTAt Y r ν yb yy P π ψ y → ∀ β : c'.V W →+* 𝓞_ℂ_[p], yb ≫ Y.s = spMap β →
      ∀ σ : E →+* ℂ, β.comp (embV c' W σ) = embInt c P.integers σ := by
  first | exact @GlobalTheory.FlatModel.htAt_embV_eq | exact GlobalTheory.FlatModel.htAt_embV_eq | (intros; apply GlobalTheory.FlatModel.htAt_embV_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionValueTangentEqAdicExpansionSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

open IsLocalRing GlobalTheory.FormalValue

theorem isLocalRing_dualNumber (V : Type) [CommRing V] [IsLocalRing V] : IsLocalRing (DualNumber V) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

theorem thick_closedPoint (V : Type) [CommRing V] [IsLocalRing V] [IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1))] :
    thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))) = closedPoint V := by
  show PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal V ^ (0 + 1))) (closedPoint _) = closedPoint V
  refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
  haveI : (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem pow_map_le_ker (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    (m.map (algebraMap V (DualNumber V))) ^ (e + 1) ≤
      RingHom.ker ((Ideal.Quotient.mk (m ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) := by
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact ha

theorem ker_dualMap_le (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    RingHom.ker (dualMap (Ideal.Quotient.mk (m ^ (e + 1)))) ≤ (m.map (algebraMap V (DualNumber V))) ^ (e + 1) := by
  intro z hz
  rw [RingHom.mem_ker] at hz
  have h₁ : Ideal.Quotient.mk (m ^ (e + 1)) z.fst = 0 := by
    have := congrArg TrivSqZeroExt.fst hz
    simpa [dualMap] using this
  have h₂ : Ideal.Quotient.mk (m ^ (e + 1)) z.snd = 0 := by
    have := congrArg TrivSqZeroExt.snd hz
    simpa [dualMap] using this
  rw [Ideal.Quotient.eq_zero_iff_mem] at h₁ h₂
  rw [← Ideal.map_pow]
  have hz' : z = algebraMap V (DualNumber V) z.fst + algebraMap V (DualNumber V) z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz']
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem dualMap_surjective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (dualMap f) := by
  intro w
  obtain ⟨a, ha⟩ := hf w.fst
  obtain ⟨b, hb⟩ := hf w.snd
  refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, ?_⟩
  ext <;> simp [dualMap, ha, hb]

theorem value_mul_sumI : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  intro V _ _ _ _ hV D A G _ _ _ U y gm₀ hy hT k jG J hjG hJ
  haveI : IsLocalRing (DualNumber V) := isLocalRing_dualNumber V
  haveI : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  haveI : IsAdicComplete (maximalIdeal V) V := hV
  haveI hJd : IsAdicComplete ((maximalIdeal V).map (algebraMap V (DualNumber V))) (DualNumber V) :=
    InertNorm.isAdicComplete_map_of_finite (maximalIdeal V) (DualNumber V)
  have hx : IsFormalPt U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) gm₀ y.left :=
    isFormalPt_of_surjective _ fun e => by
      obtain ⟨ye, h₁, h₂, h₃⟩ := hT e
      exact ⟨DualNumber (V ⧸ maximalIdeal V ^ (e + 1)), inferInstance, dualMap (Ideal.Quotient.mk _), ye,
        dualMap_surjective _ Ideal.Quotient.mk_surjective, ker_dualMap_le V _ e, h₁, h₂, h₃⟩
  have hL : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG := hjG
  have hM : ⊤ ≤ basePt gm₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := hJ _
  refine ⟨(tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹,
    ?_, fun σ f hE => ?_⟩
  · obtain ⟨g₀, hg₀⟩ := exists_isZero D.toPre (Over.mk (spMap (RingHom.id V)))
    haveI : IsAdicComplete ((maximalIdeal V).map (RingHom.id V)) V := by rw [Ideal.map_id]; exact hV
    have h₀ := isFormalPt_zero U.toUnifPre (RingHom.id V) hg₀
    have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    have hb₀ : basePt g₀ = spMap (RingHom.id V) ≫ eSec D.toPre.P.A := by
      refine (congrArg Over.Hom.left hg₀.1).trans ?_
      exact congrArg (· ≫ eSec D.toPre.P.A)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap (RingHom.id V))))))
    have hyE : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ y.left = eSec G := hy
    have hL₀ : ⊤ ≤ (spMap (RingHom.id V) ≫ eSec G) ⁻¹ᵁ U.LG.L.U jG := by
      rw [← hyE, ← Category.assoc]; exact top_le_comp hL _
    have hxe : ∀ e, eSec (thickObj V (maximalIdeal V) e G) ≫ (fstG (maximalIdeal V) e G).left =
        spMap ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) ≫
          y.left := fun e => by
      rw [ExpansionValueZero.eSec_fstG, ← hyE]
      show _ = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp
        (TrivSqZeroExt.fstHom V V V).toRingHom)) ≫ _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hM₀ : ⊤ ≤ basePt g₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
      haveI : IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1)) :=
        isLocalRing_quotient_pow (IsLocalRing.maximalIdeal.isMaximal V).ne_top 0
      have HC := hx.hasCoords (e := 0) _ (pow_map_le_ker V _ 0) (hxe 0)
      have h₂ : thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A = spMap _ ≫ gm₀.b.left :=
        (ExpansionValueZero.eSec_pG _ (U.gt 0)).symm.trans HC.2.1
      have h₃ : ⊤ ≤ (thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
        rw [h₂]; exact top_le_comp hM _
      have h₄ : eSec D.toPre.P.A (thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1)))) ∈
          D.toPre.P.L.U (J gm₀.b.left) := h₃ (Set.mem_univ _)
      rw [thick_closedPoint] at h₄
      rw [hb₀]
      exact top_le_comp (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of V) _ h₄).ge _
    have hfst : (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left) : DualNumber V).fst =
        (tau U.toUnifPre ((maximalIdeal V).map (RingHom.id V)) (spMap (RingHom.id V) ≫ eSec G) jG
          (J gm₀.b.left) : V) := by
      refine eq_of_forall_mk_eq (maximalIdeal V) fun e => ?_
      have a₁ := map_tau_mul_wVal hx hL hM _ (pow_map_le_ker V _ e) (hxe e)
      have a₂ := map_tau_mul_wVal h₀ hL₀ hM₀ (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))
        (by rw [Ideal.map_id, Ideal.mk_ker]) (xe := eSec (thickObj V (maximalIdeal V) e G))
        (by rw [hid, Category.id_comp]; exact ExpansionValueZero.eSec_fstG _ e G)
      exact (IsUnit.of_mul_eq_one_right _ a₂).mul_right_cancel (a₁.trans a₂.symm)
    have r₀ := tau_rig h₀ hb₀ hL₀ hM₀
    have hv : ∀ (U' : (Sp V).Opens) (f : Γ(Sp V, U')),
        valR (spMap (RingHom.id V)) U' f = valR (𝟙 (Sp V)) U' f := fun _ _ => by rw [hid]
    rw [hv, hv] at r₀
    have hW : (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left))⁻¹ : (DualNumber V)ˣ) : DualNumber V).fst *
        (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
          (J gm₀.b.left) : DualNumber V).fst = 1 := by
      rw [← TrivSqZeroExt.fst_mul, Units.inv_mul, TrivSqZeroExt.fst_one]
    unfold rigVal rigValD
    rw [← r₀, ← _root_.mul_assoc, ← hfst, hW, _root_.one_mul]
    rfl
  · refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
    haveI : IsLocalRing (DualNumber V ⧸ ((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1)) :=
      isLocalRing_quotient_pow (ne_top_of_isHausdorff _) n
    obtain ⟨F, hF⟩ := map_secVal_eq U.toUnifPre (hE n)
    obtain ⟨-, h₁⟩ := hF (DualNumber V) ((maximalIdeal V).map (algebraMap V (DualNumber V))) _ gm₀ y.left hx _
      (Ideal.Quotient.mk (((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1))) (by rw [Ideal.mk_ker])
    refine ⟨F, fun T hT => ?_⟩
    have hc : ∀ α ∈ T, CohCharts gm₀ α (J gm₀.b.left) (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
        (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) := fun α _ => by
      refine ⟨fun p _ => Set.mem_iInter.2 fun i => hJ (gm₀.b.left ≫ D.toPre.famφB α i) (Set.mem_univ p),
        fun p _ => Set.mem_iInter.2 fun i => hJ (D.toPre.gtφT (epsR V) gm₀.b α i) (Set.mem_univ p), ?_⟩
      have c : ∀ a, Sum.elim (fun _ : PUnit.{1} => J gm₀.b.left) (Sum.elim (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
          (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i))) a = J (Sum.elim (fun _ : PUnit.{1} => basePt gm₀)
            (Sum.elim (fun a => basePt gm₀ ≫ D.toPre.famφB α a) (coordφ gm₀ α)) a) := by
        rintro (a | a | a) <;> rfl
      exact fun a b hab => (c a).trans ((congrArg J hab).trans (c b).symm)
    have e := h₁ T jG (J gm₀.b.left) (fun α i => J (gm₀.b.left ≫ D.toPre.famφB α i))
      (fun α i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) hT hL hM hc
    rw [Ideal.Quotient.eq] at e
    have key := Ideal.mul_mem_left _
      (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹ :
        (DualNumber V)ˣ) ^ k : DualNumber V) e
    rw [mul_sub, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul] at key
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) key

end GlobalTheory.MBLow.TanExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProportiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_pullback_proportional_of_proportional : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (L L' : LB W), L.IsLB → L'.IsLB → ∀ (a b : ℕ), (∀ C : Closeds W, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L] = b * interNumRed ℂ C ![L']) → ∀ C : Closeds M, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L.pull f] = b * interNumRed ℂ C ![L'.pull f] := by
  first | exact @GlobalTheory.NumPull.interNumRed_pull_proportional | exact GlobalTheory.NumPull.interNumRed_pull_proportional | (intros; apply GlobalTheory.NumPull.interNumRed_pull_proportional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingLocalizationPowerSeriesUnStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_localization_powerSeries_uniformiser : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime, IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  first | exact @GlobalTheory.PowerSeriesUniformiser.main | exact GlobalTheory.PowerSeriesUniformiser.main | (intros; apply GlobalTheory.PowerSeriesUniformiser.main <;> assumption)
end

