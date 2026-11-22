import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomAlgebraisationOfReductions
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isMonHom_of_fst_mul_snd {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (g : A ⟶ B)
    (h : (fst A A * snd A A) ≫ g = (fst A A ≫ g) * (snd A A ≫ g)) : IsMonHom g := by
  have hm : ∀ (T : Over S) (x y : T ⟶ A), (x * y) ≫ g = (x ≫ g) * (y ≫ g) := fun T x y => by
    have := congrArg (lift x y ≫ ·) h
    simpa only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd] using this
  refine ⟨?_, ?_⟩
  · have h1 := hm (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S) ⟶ A) ≫ g = 1 := left_eq_mul.1 h1
    simpa [Hom.one_def] using h2
  · have e : (fst A A * snd A A) = μ[A] := by simp [Hom.mul_def]
    rw [e] at h
    rw [h, Hom.mul_def]
    congr 1

theorem mul_comp_of_isGrpPullback {S S' : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    {Y Z : Over S'} [GrpObj Y] [GrpObj Z] {t : S' ⟶ S} {a : Y.left ⟶ A.left} {b : Z.left ⟶ B.left}
    (ha : IsGrpPullback Y A t a) (hb : IsGrpPullback Z B t b) (f : Y ⟶ Z) [IsMonHom f] (g : A ⟶ B)
    (hg : a ≫ g.left = f.left ≫ b) (T : Over S') (x y : Over.mk (T.hom ≫ t) ⟶ A) :
    (x * y) ≫ g = (x ≫ g) * (y ≫ g) := by
  let x' : T ⟶ Y := Over.homMk (ha.1.lift x.left T.hom (Over.w x)) (ha.1.lift_snd _ _ _)
  let y' : T ⟶ Y := Over.homMk (ha.1.lift y.left T.hom (Over.w y)) (ha.1.lift_snd _ _ _)
  have hx : x.left = x'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have hy : y.left = y'.left ≫ a := (ha.1.lift_fst _ _ _).symm
  have h1 := ha.2 T x' y' x y hx hy
  have h2 := hb.2 T (x' ≫ f) (y' ≫ f) (x ≫ g) (y ≫ g)
    (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hg])
    (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hg])
  ext
  rw [h2, Over.comp_left, h1, ← MonObj.mul_comp, Over.comp_left, Category.assoc, Category.assoc, hg]

theorem grpHom_algebraise : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B], IsProper A.hom → IsProper B.hom → ∀ (Y Z : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] [∀ e, GrpObj (Z e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (δ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left) (a : ∀ e, (Y e).left ⟶ A.left) (b : ∀ e, (Z e).left ⟶ B.left), (∀ e, IsGrpPullback (Y e) A (thick R I e) (a e)) → (∀ e, β e ≫ a (e + 1) = a e) → (∀ e, IsGrpPullback (Z e) B (thick R I e) (b e)) → (∀ e, δ e ≫ b (e + 1) = b e) → ∀ f : ∀ e, Y e ⟶ Z e, (∀ e, IsMonHom (f e)) → (∀ e, β e ≫ (f (e + 1)).left = (f e).left ≫ δ e) → ∃ g : A ⟶ B, IsMonHom g ∧ (∀ e, a e ≫ g.left = (f e).left ≫ b e) ∧ ∀ g' : A ⟶ B, (∀ e, a e ≫ g'.left = (f e).left ≫ b e) → g' = g := by
  intro H R _ _ I hI A B _ _ hA hB Y Z _ _ β δ a b ha hβ hb hδ f hf hc
  obtain ⟨g, hg, hu⟩ := H R I hI A B hA inferInstance inferInstance inferInstance Y β a
    (fun e => (ha e).1) hβ (fun e => (f e).left ≫ b e)
    (fun e => by rw [Category.assoc, (hb e).1.w, ← Category.assoc, Over.w])
    (fun e => by rw [← Category.assoc, hc, Category.assoc, hδ])
  refine ⟨g, isMonHom_of_fst_mul_snd g ?_, hg, hu⟩
  haveI : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  refine H.hom_ext hI fun e => ?_
  haveI := hf e
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (pullback.snd (A ⊗ A).hom (thick R I e))
  let P : Over.mk (T.hom ≫ thick R I e) ⟶ A ⊗ A :=
    Over.homMk (pullback.fst (A ⊗ A).hom (thick R I e)) pullback.condition
  have key := mul_comp_of_isGrpPullback (ha e) (hb e) (f e) g (hg e) T (P ≫ fst A A) (P ≫ snd A A)
  have key' : P ≫ (fst A A * snd A A) ≫ g = P ≫ ((fst A A ≫ g) * (snd A A ≫ g)) := by
    rw [← Category.assoc, MonObj.comp_mul, key, MonObj.comp_mul, Category.assoc, Category.assoc]
  exact congrArg (·.left) key'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def HaarChart (X : Data E r) (c : ℝ≥0∞) : Prop :=
  ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ g, φ (frameOf X g) ∂haarR X = c * ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X)

def trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)
    (y : Frame X.Ψ r) : Frame X'.Ψ r :=
  fun τ' => (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') : Matrix (Fin r) (Fin r) ℂ)

example (X : Data E r) (y : Frame X.Ψ r) : trF X X (Equiv.refl _) y = y := by
  funext τ
  show mat (baseFr X) τ * (mat (baseFr X) τ)⁻¹ * mat y τ = mat y τ
  have h : (mat (baseFr X) τ).det ≠ 0 := (X.signature τ).choose_spec.1
  rw [Matrix.mul_nonsing_inv _ h.isUnit, Matrix.one_mul]

end

end GlobalTheory.FlagQuotHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLFrobeniusPowStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraProductCuspidalGL_frobenius_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (L : List (ℕ × ℕ)) (n : ℕ) (x : GL (Fin n) F), J θ L n (gal (t : F →+* F) n x) = J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) n x := by
  first | (exact @GlobalTheory.Shin.J_gal) | (exact GlobalTheory.Shin.J_gal) | (intros; apply GlobalTheory.Shin.J_gal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtDeformedProductDerivativeTerm
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum

theorem hasDerivAt_inv_pow_affine (c a b : ℂ) (n : ℕ) (u : ℂ) (hu : a + u * b ≠ 0) :
    HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (-(n : ℂ) * b * (a + u * b)⁻¹ ^ (n + 1))) u := by
  have h1 : HasDerivAt (fun t : ℂ => a + t * b) b u := by
    simpa using ((hasDerivAt_id u).mul_const b).const_add a
  have h2 : HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (n * (a + u * b)⁻¹ ^ (n - 1) * (-b / (a + u * b) ^ 2))) u :=
    ((h1.inv hu).pow n).const_mul c
  refine h2.congr_deriv ?_
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, div_eq_mul_inv, ← inv_pow]
    push_cast
    ring

theorem defCoord_ne_zero {E : Type} [Field E] [NumberField E] {I : Type} (φ : I → E →+* ℂ) (z : I → ℂ)
    (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) : defCoord φ z x i ≠ 0 := by
  intro h
  have hφ : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx
  have hpos : 0 < ‖φ i x‖ := norm_pos_iff.mpr hφ
  have hz1 : ‖z i‖ < 1 := hz i
  unfold defCoord at h
  have heq : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have hn : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [heq]
    rw [norm_neg, norm_mul, Complex.norm_conj]
  have hlt := mul_lt_of_lt_one_left hpos hz1
  linarith

theorem hasFDerivAt_dTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ)
    (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x)
      (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by
  intro E _ _ I _ _ φ k m x hx z hz
  set C : I → ℂ := fun i => ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) *
    (starRingEnd ℂ (φ i x)) ^ m i with hC
  have hd : ∀ i, HasFDerivAt (fun w : I → ℂ => C i * (defCoord φ w x i)⁻¹ ^ (k + m i))
      ((C i * (-((k + m i : ℕ) : ℂ) * starRingEnd ℂ (φ i x) * (defCoord φ z x i)⁻¹ ^ (k + m i + 1))) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i) z := by
    intro i
    have h1 := hasDerivAt_inv_pow_affine (C i) (φ i x) (starRingEnd ℂ (φ i x)) (k + m i) (z i)
      (defCoord_ne_zero φ z hz x hx i)
    have h2 := h1.comp_hasFDerivAt z (hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : I => ℂ) i z)
    exact h2
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hd i)
  have hfun : (fun w : I → ℂ => dTerm φ k m w x) =
      (fun w => ∏ i ∈ Finset.univ, C i * (defCoord φ w x i)⁻¹ ^ (k + m i)) := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  symm
  unfold dTerm
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [hC, hij]
  · simp only [hC, Pi.add_apply, Pi.single_eq_same, Finset.prod_range_succ]
    push_cast
    ring

end GlobalTheory.DeformedSum

example : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x) (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := GlobalTheory.DeformedSum.hasFDerivAt_dTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinNonconstantFourierSumSmoothHolomoStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinNonconstantFourierSum_smoothHolomorphic : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  first | exact @GlobalTheory.HeckeTwo.bOne_isGood | exact GlobalTheory.HeckeTwo.bOne_isGood | (intros; apply GlobalTheory.HeckeTwo.bOne_isGood <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeValueEqOfIsValue
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem isGVal_unique' {F : Type} [Field F] [NumberField F] {k : ℕ}
    {L : _root_.GlobalTheory.HilbFam.Lat F} {b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ} {G G' : ℂ}
    (h : _root_.GlobalTheory.HilbFam.IsGVal k L b a G)
    (h' : _root_.GlobalTheory.HilbFam.IsGVal k L b a G') : G = G' := by
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨h₁', h₂'⟩ := h'
  by_cases hk : k = 2
  · subst hk
    obtain ⟨H, hH, hsum, rfl⟩ := h₂ rfl
    obtain ⟨H', hH', hsum', rfl⟩ := h₂' rfl
    have hU : IsOpen {σ : ℂ | -1 / 2 < σ.re} := isOpen_lt continuous_const Complex.continuous_re
    have hC : IsPreconnected {σ : ℂ | -1 / 2 < σ.re} := (convex_halfSpace_re_gt _).isPreconnected
    have hone : (1 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num
    have hzero : (0 : ℂ) ∈ {σ : ℂ | -1 / 2 < σ.re} := by
      simp only [Set.mem_setOf_eq, Complex.zero_re]; norm_num
    have hev : H =ᶠ[nhds 1] H' := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with σ hσ
      exact (hsum σ hσ).unique (hsum' σ hσ)
    exact (hH.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hH'.analyticOnNhd hU) hC
      hone hev hzero
  · exact (h₁ hk).unique (h₁' hk)

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.gval_eq_of_isGVal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (G : ℂ),
    _root_.GlobalTheory.HilbFam.IsGVal k L b a G → _root_.GlobalTheory.HilbFam.gval k L b a = G := by
  intro F _ _ _ k L b a G hG
  have h : ∃ G, _root_.GlobalTheory.HilbFam.IsGVal k L b a G := ⟨G, hG⟩
  rw [_root_.GlobalTheory.HilbFam.gval, dif_pos h]
  exact isGVal_unique' h.choose_spec hG

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesLatticeDifferentiableOnStatement
section
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ),
  (∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z)) →
  DifferentiableOn ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 k 0) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  first | exact @GlobalTheory.eisSum_zero_differentiableOn | exact GlobalTheory.eisSum_zero_differentiableOn | (intros; apply GlobalTheory.eisSum_zero_differentiableOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSummandUnitSmul
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem coord_unit_smul {F : Type} [Field F]
    (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (ε : (𝓞 F)ˣ) (x : Fin 2 → F) (τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.HilbFam.coord b a (ε • x) τ =
      (τ ((ε : 𝓞 F) : F) : ℂ) * _root_.GlobalTheory.HilbFam.coord b a x τ := by
  have hsmul : ∀ j, (ε • x) j = ((ε : 𝓞 F) : F) * x j := fun j => rfl
  simp only [_root_.GlobalTheory.HilbFam.coord, hsmul, map_mul, Complex.ofReal_mul]
  ring

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.gTerm_unit_smul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (σ : ℂ) (b a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ)
    (ε : (𝓞 F)ˣ) (x : Fin 2 → F), Even k → _root_.GlobalTheory.HilbFam.gTerm k σ b a (ε • x) = _root_.GlobalTheory.HilbFam.gTerm k σ b a x := by
  intro F _ _ _ k σ b a ε x hk
  have hprod : ∏ τ, _root_.GlobalTheory.HilbFam.coord b a (ε • x) τ =
      ((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℂ) * ∏ τ, _root_.GlobalTheory.HilbFam.coord b a x τ := by
    simp only [coord_unit_smul, Finset.prod_mul_distrib]
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb]
  have hN : Algebra.norm ℚ ((ε : 𝓞 F) : F) = 1 ∨ Algebra.norm ℚ ((ε : 𝓞 F) : F) = -1 :=
    abs_eq (zero_le_one) |>.mp (NumberField.Units.norm F ε)
  unfold _root_.GlobalTheory.HilbFam.gTerm
  rw [hprod]
  rcases hN with hN | hN <;> simp [hN, hk.neg_pow]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem mulMat_stdLat_le {F : Type} [Field F] [NumberField F]
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    _root_.GlobalTheory.HilbFam.mulMat (_root_.GlobalTheory.HilbFam.stdLat F) A ≤
      _root_.GlobalTheory.HilbFam.stdLat F := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rintro _ ⟨y, hy, rfl⟩
  unfold _root_.GlobalTheory.HilbFam.stdLat at hy ⊢
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  simp only [LinearMap.coe_restrictScalars, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : y j * (A.map Int.cast) j i = ((A j i : 𝓞 F)) • y j := by
    simp [Algebra.smul_def, mul_comm]
  rw [hj]
  exact Submodule.smul_mem _ _ (hy j (Set.mem_univ j))

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)),
    _root_.GlobalTheory.HilbFam.HasLevel N L → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.twist N L α) := by
  intro F _ _ _ N L α hL
  obtain ⟨_, hle⟩ := hL
  unfold _root_.GlobalTheory.HilbFam.HasLevel _root_.GlobalTheory.HilbFam.twist
  refine ⟨fun x hx => Submodule.mem_sup_right ?_, sup_le ?_ (mulMat_stdLat_le _)⟩
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    convert Submodule.mem_map_of_mem hx using 1
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Matrix.natCast_apply] <;>
      rw [Algebra.smul_def, map_natCast, mul_comm]
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    exact (Submodule.map_mono hle).trans (mulMat_stdLat_le _)

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonneStatement
section
open GlobalTheory.Sandwich
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne : GlobalTheory.Published.PrismaticDieudonneHodge → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε := by
  first | exact @GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ | exact GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ | (intros; apply GlobalTheory.DieudonneSandwich.hodgeTateSandwich_of_prismaticDieudonne₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.HomothetyLatSum

variable {E : Type} [Field E] [NumberField E]

def mulQ (α : E) : Quotient (unitRel (E := E)) → Quotient (unitRel (E := E)) :=
  Quotient.map (fun x => α * x) (by rintro x x' ⟨u, h⟩; exact ⟨u, by rw [h]; ring⟩)

theorem mulQ_mk (α x : E) : mulQ α (Quotient.mk _ x) = Quotient.mk (unitRel (E := E)) (α * x) := rfl

theorem mulQ_mulQ (a b : E) (q : Quotient (unitRel (E := E))) : mulQ a (mulQ b q) = mulQ (a * b) q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, mulQ_mk, mulQ_mk, mul_assoc]

theorem mulQ_one (q : Quotient (unitRel (E := E))) : mulQ 1 q = q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, one_mul]

theorem mulQ_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))} (hq : q ∈ modUnits L) :
    mulQ α q ∈ modUnits ((fun x => α * x) '' L) := by
  obtain ⟨x, hx, h0, rfl⟩ := hq
  exact ⟨α * x, ⟨x, hx, rfl⟩, mul_ne_zero hα h0, rfl⟩

theorem mulQ_inv_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))}
    (hq : q ∈ modUnits ((fun x => α * x) '' L)) : mulQ α⁻¹ q ∈ modUnits L := by
  obtain ⟨_, ⟨x, hx, rfl⟩, h0, rfl⟩ := hq
  refine ⟨x, hx, fun h => h0 (by simp [h]), ?_⟩
  rw [mulQ_mk, inv_mul_cancel_left₀ hα]

def mulEquiv {α : E} (hα : α ≠ 0) (L : Set E) : modUnits L ≃ modUnits ((fun x => α * x) '' L) where
  toFun q := ⟨mulQ α q.1, mulQ_mem hα q.2⟩
  invFun q := ⟨mulQ α⁻¹ q.1, mulQ_inv_mem hα q.2⟩
  left_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, inv_mul_cancel₀ hα, mulQ_one])
  right_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, mul_inv_cancel₀ hα, mulQ_one])

variable {I : Type} [Fintype I]

theorem term_out_mulQ [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : E)
    (q : Quotient (unitRel (E := E))) :
    term φ (2 * s) κ σ (mulQ α q).out = term φ (2 * s) κ σ α * term φ (2 * s) κ σ q.out := by
  have h1 : mulQ α q = Quotient.mk _ (α * q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨u, hu⟩ := Quotient.exact ((Quotient.out_eq _).trans h1)
  rw [← term_mul, hu, (TermUnit.term_unit_and_norm E I φ hφ s κ σ _).1 u]

theorem term_eq_lamInf [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : Eˣ) :
    term φ (2 * s) κ σ α =
      (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) := by
  have key : ∀ i, ((‖φ i α‖ : ℝ) : ℂ) ^ (-2 * σ) = (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) ^ (-σ) := fun i => by
    have hp : 0 < ‖φ i α‖ := by simp
    have : (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) = ((‖φ i α‖ : ℝ) : ℂ) * ((‖φ i α‖ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.mul_cpow_ofReal_nonneg hp.le hp.le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hp.ne')]
    congr 1; ring
  rw [← TermUnit.prod_norm_sq hφ, ← TermUnit.prod_cpow _ _ (fun i => by positivity)]
  unfold term lamInf
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [key]
  have gen : ∀ (a c N : ℂ) (m n : ℕ), a⁻¹ ^ m * c ^ n * N = (a ^ m * c⁻¹ ^ n)⁻¹ * N := by
    intro a c N m n
    rw [mul_inv, inv_pow, inv_pow, inv_inv]
  exact gen _ _ _ _ _

theorem homothety (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (L : Set E) : Homothety φ (2 * s) L := by
  intro κ α S hS
  have hα : (α : E) ≠ 0 := α.ne_zero
  have hN : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]; exact hα
  have key : IsLatSum φ (2 * s) κ ((fun x => (α : E) * x) '' L)
      (fun σ => (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) * S σ) := by
    refine ⟨?_, fun σ hσ => ?_⟩
    · exact ((differentiable_neg.const_cpow (Or.inl hN)).const_mul _).mul hS.1
    · have h1 := (hS.2 σ hσ).mul_left
        ((lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ))
      have hf : ((fun q' : modUnits ((fun x => (α : E) * x) '' L) => term φ (2 * s) κ σ q'.1.out) ∘ mulEquiv hα L) =
          fun q : modUnits L => (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) *
            term φ (2 * s) κ σ q.1.out := funext fun q => by
        show term φ (2 * s) κ σ (mulQ (α : E) q.1).out = _
        rw [term_out_mulQ hφ, term_eq_lamInf hφ]
      rw [← (mulEquiv hα L).hasSum_iff, hf]
      exact h1
  refine ⟨key, fun S' hS' => ?_⟩
  rw [hS'.unique key]
  simp

end GlobalTheory.HomothetyLatSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentQuotientDatumCompatStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_quotient_datum_compat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (π : Γ →ₐ[ℤ_[p]] Λ) (e : Γ), IsIdempotentElem e → Function.Surjective π → RingHom.ker π = Ideal.span {1 - e} → ∀ (h : ℕ) (D : Datum ε h Γ), ∃ (h' : ℕ) (D' : Datum ε h' Λ) (iT : Matrix (Fin h) (Fin h') ℤ_[p]) (pT : Matrix (Fin h') (Fin h) ℤ_[p]) (iM : Matrix (Fin h) (Fin h') (Ainf p O)) (pM : Matrix (Fin h') (Fin h) (Ainf p O)), pT * iT = 1 ∧ iT * pT = D.ρT e ∧ pM * iM = 1 ∧ iM * pM = D.ρM e ∧ D'.F = pM * D.F * iT.map (ofPadic p O) ∧ D'.G = pT.map (ofPadic p O) * D.G * iM ∧ (∀ x, D'.ρT (π x) = pT * D.ρT x * iT) ∧ ∀ x, D'.ρM (π x) = pM * D.ρM x * iM := by
  first | exact @GlobalTheory.DetInv.datum_idempotent_part | exact GlobalTheory.DetInv.datum_idempotent_part | (intros; apply GlobalTheory.DetInv.datum_idempotent_part <;> assumption)
end

