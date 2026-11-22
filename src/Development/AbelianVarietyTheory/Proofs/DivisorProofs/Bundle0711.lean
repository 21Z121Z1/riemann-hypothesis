import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allPrim_of_abelianDeRhamFree (h : GlobalTheory.Published.AbelianDeRhamFree) (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  have hdim : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    haveI := hg
    haveI : SmoothOfRelativeDimension g (pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip hg
    exact inferInstanceAs (SmoothOfRelativeDimension (g + g) (pullback.fst A.hom A.hom ≫ A.hom))
  obtain ⟨f1, p1, r1, -⟩ := h R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := h R (A ⊗ A) (g + g)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hdim
  have one0 : ∀ c, pullOver (dp0 R) (𝟙 _) (1 : A ⟶ A) c = 0 := fun c => by
    haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
    rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]
  have id0 : ∀ c, pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := fun c => IsMor.pullCohomologyOne_id _ c
  let Ψ := (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) (1 : A ⟶ A))).prod
    (pullOver (dp0 R) (𝟙 _) (lift (1 : A ⟶ A) (𝟙 A)))
  have hs : Function.Surjective Ψ := fun ⟨a, b⟩ =>
    ⟨pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b, by
    refine Prod.ext ?_ ?_
    · change pullOver _ _ _ _ = a
      rw [map_add, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, one0, id0, add_zero]
    · change pullOver _ _ _ _ = b
      rw [map_add, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, one0, id0, zero_add]⟩
  have hb : Function.Bijective Ψ := Module.bijective_of_surjective_of_rankAtStalk_eq hs (by
    intro m hm
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring)
  refine eq_top_iff.2 fun c _ => (mem_prim_iff _ _ _ _).2 (hb.1 ?_)
  have e1 : lift (𝟙 A) (1 : A ⟶ A) ≫ μ[A] = 𝟙 A := by rw [← Hom.mul_def, _root_.mul_one]
  have e2 : lift (1 : A ⟶ A) (𝟙 A) ≫ μ[A] = 𝟙 A := by rw [← Hom.mul_def, _root_.one_mul]
  refine Prod.ext ?_ ?_
  · change pullOver _ _ _ _ = pullOver _ _ _ _
    rw [map_add, pullOver_pullOver, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, e1,
      one0, id0, add_zero]
  · change pullOver _ _ _ _ = pullOver _ _ _ _
    rw [map_add, pullOver_pullOver, pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, e2,
      one0, id0, zero_add]

theorem abelianDeRhamFree_toFree (h : GlobalTheory.Published.AbelianDeRhamFree) :
    GlobalTheory.Published.AbelianDeRham.Free := fun R _ A _ g hA hg =>
  ⟨allPrim_of_abelianDeRhamFree h R A g hA hg, h R A g hA hg⟩

theorem abelianDeRhamStructure_toFree (h : GlobalTheory.Published.AbelianDeRhamStructure) :
    GlobalTheory.Published.AbelianDeRham.Free :=
  abelianDeRhamFree_toFree h.1

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeformationComplexStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_deformation_complex : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ), (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∃ (A' : Over (Sp D)) (_ : GrpObj A') (q : A'.left ⟶ A₀.left) (i : A₀.left ⟶ A'.left), IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ IsGrpPullback A' A₀ (spMap (algebraMap ℂ D)) q ∧ IsGrpPullback A₀ A' (spMap π) i ∧ i ≫ q = 𝟙 _ := by
  first | exact @GlobalTheory.ConstLift.exists_constLift | exact GlobalTheory.ConstLift.exists_constLift | (intros; apply GlobalTheory.ConstLift.exists_constLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomAgreeLocusClosedSubschemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | (exact @GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme) | (exact GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme) | (intros; apply GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsSeparatedOfAffineBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem abelianScheme_left_isSeparated_of_affine :
    ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated := by
  intro R _ A _ h
  haveI : IsProper A.hom := h.proper
  refine ⟨?_⟩
  rw [← terminal.comp_from A.hom]
  infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameInvariantEqZeroOfTauDvd
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TauUniq

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε)

theorem p_cancel {b c : F.B} (h : (p : F.B) * b = p * c) : b = c := by
  have h1 := congrArg (algebraMap F.B F.Q) h
  simp only [map_mul, map_natCast] at h1
  exact F.frame.inj (F.frame.unit_p.mul_left_cancel h1)

theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem sigma_tau : F.σ F.τ = p * F.τ := by
  apply p_cancel F
  have hS : WittVector.frobenius (Sandwich.mu ε) =
      Sandwich.mu ε * ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i := by
    unfold Sandwich.mu
    rw [map_sub, map_one, frob_teich, mul_comm, geom_sum_mul]
  have hd : Sandwich.mu ε ∣ ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) := by
    have : ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) =
        ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    apply Finset.dvd_sum
    intro i _
    simpa [Sandwich.mu, one_pow] using sub_dvd_pow_sub_pow (WittVector.teichmuller p ε) 1 i
  have h0 := (F.τ_mul _).2 hd
  rw [map_sub, map_natCast] at h0
  have h1 : (p : F.B) * F.σ F.τ = F.a (WittVector.frobenius (Sandwich.mu ε)) := by
    rw [← F.σ_a, ← F.p_τ, map_mul, map_natCast]
  rw [h1, hS, map_mul, ← F.p_τ]
  linear_combination (p : F.B) * h0

theorem theta_tau [IsDomain O] : F.θ F.τ = 0 :=
  mul_self_eq_zero.1 (by rw [← map_mul, F.τ_sq, map_zero])

theorem dvd_tau {b : F.B} (h : F.τ ∣ b) : ∃ x, b = F.τ * F.a x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨x, y, rfl⟩ := F.gen c
  exact ⟨x, by rw [mul_add, ← mul_assoc, F.τ_sq, zero_mul, add_zero]⟩

theorem lift_exists {ι : Type} (M : Matrix ι ι F.B) :
    ∃ m : Matrix ι ι (Ainf p O), ∀ i j, F.τ ∣ M i j - F.a (m i j) := by
  choose x y h using fun i j => F.gen (M i j)
  exact ⟨Matrix.of x, fun i j => ⟨F.a (y i j), by rw [h i j, Matrix.of_apply]; ring⟩⟩

theorem step {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (u : ι → F.B) (u' : ι → Ainf p O)
    (hu : ∀ j, F.τ ∣ u j - F.a (u' j)) (i : ι) :
    F.τ ∣ M.mulVec (fun j => F.σ (u j)) i -
      F.a (m.mulVec (fun j => WittVector.frobenius (u' j)) i) := by
  have hI : Ideal.span {F.τ} ≤ (Ideal.span {F.τ}).comap F.σ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, sigma_tau]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  simp only [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hm hu ⊢
  have hs : ∀ j, Ideal.Quotient.mk (Ideal.span {F.τ}) (F.σ (u j)) =
      Ideal.Quotient.mk (Ideal.span {F.τ}) (F.a (WittVector.frobenius (u' j))) := by
    intro j
    rw [← F.σ_a, ← Ideal.quotientMap_mk (H := hI), hu j, Ideal.quotientMap_mk]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hm i j, hs j]

theorem iter {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (w : ι → Ainf p O) (n : ℕ) (i : ι) :
    F.τ ∣ (fun v : ι → F.B => M.mulVec fun j => F.σ (v j))^[n] (fun j => F.a (w j)) i -
      F.a ((fun v : ι → Ainf p O => m.mulVec fun j => WittVector.frobenius (v j))^[n] w i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact step F M m hm _ _ ih i

theorem nil_lift [IsDomain O] {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (hM : IsNil F.θ F.σ M) :
    IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) m := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun w i hu => hN (fun j => F.a (w j)) i ?_⟩
  obtain ⟨c, hc⟩ := iter F M m hm w N i
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add, map_mul, theta_tau, zero_mul, zero_add, F.θ_a]
  exact hu

theorem core (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    [Algebra O C] [IsDomain O] (hv : v.Integers O) (hε : IsPrimitiveSystem ε) {ι : Type} [Fintype ι]
    (M : Matrix ι ι F.B) (hM : IsNil F.θ F.σ M) (z : ι → Ainf p O)
    (hz : ∀ i, F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i) (i : ι) :
    F.τ * F.a (z i) = 0 := by
  obtain ⟨m, hm⟩ := lift_exists F M
  have key : ∀ i, Sandwich.mu ε ∣ z i - m.mulVec (fun j => WittVector.frobenius (z j)) i := by
    intro i
    rw [← F.τ_mul, map_sub, mul_sub, hz i]
    obtain ⟨c, hc⟩ := step F M m hm (fun j => F.a (z j)) z (fun j => by simp) i
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, mul_add, ← mul_assoc, F.τ_sq, zero_mul, zero_add, sub_self]
  exact (F.τ_mul _).2 ((GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι m (nil_lift F M m hm hM)).2 z key i)

theorem vec_eq {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (g : ι → F.B) (z : ι → Ainf p O)
    (hz : ∀ i, g i = F.τ * F.a (z i))
    (hg : ∀ i, M.mulVec (fun j => F.σ (g j)) i = (p : F.B) * g i) (i : ι) :
    F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i := by
  apply p_cancel F
  have e := hg i
  simp only [Matrix.mulVec, dotProduct, hz, map_mul, sigma_tau F] at e
  rw [← e]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem blk_mul_blk (d k : ℕ) (R : Type) [CommRing R] (u : R) :
    blk d k 1 u * blk d k u 1 = u • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) := by
  rw [blk, blk, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem eq_zero_of_tau_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → (∀ Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B, Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → (∀ i m, F.τ ∣ Y i m) → Y = 0) ∧ ∀ g : Fin d ⊕ Fin k → F.B, Matrix.mulVec (U * blk d k (p : F.B) 1) (fun i => F.σ (g i)) = (p : F.B) • g → (∀ i, F.τ ∣ g i) → g = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U hU hN1 hN2
  have hdet : IsUnit U.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det U).1 hU
  refine ⟨fun Y hY hdiv => ?_, fun g hg hdiv => ?_⟩
  · choose z hz using fun i c => dvd_tau F (hdiv i c)
    have hM : U.transpose⁻¹ * blk d k 1 (p : F.B) * Y.map F.σ = (p : F.B) • Y := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc (blk d k 1 (p : F.B)),
        ← Matrix.mul_assoc (blk d k 1 (p : F.B)), blk_mul_blk, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mul]
    ext i c
    rw [hz i c, Matrix.zero_apply]
    refine core F C v hv hε _ hN1 (fun j => z j c)
      (vec_eq F _ (fun j => Y j c) (fun j => z j c) (fun j => hz j c) (fun i => ?_)) i
    have e := congrArg (fun X => X i c) hM
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using e
  · choose z hz using fun i => dvd_tau F (hdiv i)
    funext i
    rw [hz i, Pi.zero_apply]
    exact core F C v hv hε _ hN2 z
      (vec_eq F _ g z hz (fun i => by simpa using congrFun hg i)) i

end GlobalTheory.TauUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderivStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  first | exact @GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | exact GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | (intros; apply GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssocEval
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Chart.Assoc

theorem isEval_comp (p : ℕ) {O A B σ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] B) (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨c, hc⟩ := hN f hf
  exact ⟨φ c, by simp [hc, map_mul, map_pow, map_natCast]⟩

theorem constantCoeff_op {O : Type} [CommRing O] {d : ℕ} {τ : Type}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ O) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (j : Fin d) : constantCoeff (op μ u v j) = 0 := by
  have h : ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    rintro (k | k) <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ j)

theorem dvd_pow_map (p : ℕ) {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (φ : A →ₐ[O] B) {a : A} (h : ∃ N : ℕ, (p : A) ∣ a ^ N) :
    ∃ N : ℕ, (p : B) ∣ φ a ^ N := by
  obtain ⟨N, c, hc⟩ := h
  exact ⟨N, φ c, by rw [← map_pow, hc, map_mul, map_natCast]⟩

end GlobalTheory.Chart.Assoc

namespace GlobalTheory.Chart.Assoc

theorem assoc_eval (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ}
    (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A)
    (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hx : ∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (h2 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂)
    (h3 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃)
    (hc : ∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) :
    ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  let Φ₁ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Algebra.TensorProduct.includeLeft (S := O))
  let Φ₃ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) := Algebra.TensorProduct.includeRight
  let Φ₂ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    (Algebra.TensorProduct.assoc O O O A A A).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom O A) (AlgHom.id O A))
  let Φ₄ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Bialgebra.comulAlgHom O A)
  have hnil : ∀ k, ∃ N : ℕ, (p : A ⊗[O] (A ⊗[O] A)) ∣ (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) k ^ N := by
    rintro (k | k | k)
    · exact dvd_pow_map p (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A ⊗[O] A)) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A))) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A))) (hx k)
  have sub := ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ hnil).2 E₃ h3).1
  have c1 : ∀ j, constantCoeff (x1 (R := O) (d := d) j) = 0 := fun j => by simp [x1]
  have c2 : ∀ j, constantCoeff (x2 (R := O) (d := d) j) = 0 := fun j => by simp [x2]
  have c3 : ∀ j, constantCoeff (x3 (R := O) (d := d) j) = 0 := fun j => by simp [x3]
  have ce : ∀ {u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O},
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) →
      ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    intro u v hu hv k; rcases k with k | k <;> simp [hu, hv]
  have L1 : ∀ j, E₃ (op μ x1 x2 j) = Φ₁ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₁ h2
    have := sub _ (Sum.elim x1 x2) (Φ₁.comp E₂) (ce c1 c2) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x1, x2, h3.1, Φ₁, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  have L3 : ∀ j, E₃ (op μ x2 x3 j) = Φ₃ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₃ h2
    have := sub _ (Sum.elim x2 x3) (Φ₃.comp E₂) (ce c2 c3) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x2, x3, h3.1, Φ₃, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  intro i
  have LL : E₃ (op μ (op μ x1 x2) x3 i) = Φ₂ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₂ h2
    have := sub _ (Sum.elim (op μ x1 x2) x3) (Φ₂.comp E₂)
      (ce (constantCoeff_op μ hμ _ _ c1 c2) c3) (by
      convert e using 2 with k
      rcases k with k | k
      · simp only [Sum.elim_inl]
        rw [L1]
        have key : ∀ c : A ⊗[O] A, Φ₁ c = (Algebra.TensorProduct.assoc O O O A A A) (c ⊗ₜ[O] 1) := by
          intro c
          induction c using TensorProduct.induction_on with
          | zero => simp
          | tmul a b => simp [Φ₁, Algebra.TensorProduct.one_def]
          | add a b ha hb => rw [map_add, ha, hb, TensorProduct.add_tmul, map_add]
        rw [key]
        simp [Φ₂]
      · simp [x3, h3.1, Φ₂, Algebra.TensorProduct.one_def]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  have RR : E₃ (op μ x1 (op μ x2 x3) i) = Φ₄ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₄ h2
    have := sub _ (Sum.elim x1 (op μ x2 x3)) (Φ₄.comp E₂)
      (ce c1 (constantCoeff_op μ hμ _ _ c2 c3)) (by
      convert e using 2 with k
      rcases k with k | k
      · simp [x1, h3.1, Φ₄, Algebra.TensorProduct.one_def]
      · simp only [Sum.elim_inr]
        rw [L3]
        simp [Φ₃, Φ₄]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  rw [LL, RR]
  have ka : ∀ w : (A ⊗[O] A) ⊗[O] A,
      (Algebra.TensorProduct.assoc O O O A A A) w = TensorProduct.assoc O A A A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      induction c using TensorProduct.induction_on with
      | zero => simp
      | tmul a a' => simp
      | add c c' hc hc' => rw [TensorProduct.add_tmul, map_add, hc, hc', map_add]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  have k2 : ∀ c : A ⊗[O] A, Φ₂ c = TensorProduct.assoc O A A A (LinearMap.rTensor A (Coalgebra.comul (R := O) (A := A)) c) := by
    intro c
    rw [← ka]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₂]
    | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]
  have k4 : ∀ c : A ⊗[O] A, Φ₄ c = LinearMap.lTensor A (Coalgebra.comul (R := O) (A := A)) c := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₄]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  rw [k2, k4, Coalgebra.coassoc_apply]

end GlobalTheory.Chart.Assoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditive
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

private theorem dualDistrib_eq_mul'_map {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : Module.Dual O M) (ψ : Module.Dual O N) (t : M ⊗[O] N) :
    dualDistrib O M N (φ ⊗ₜ ψ) t = LinearMap.mul' O O (TensorProduct.map φ ψ t) := by
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp [dualDistrib_apply]

theorem cartierDual_tangent_mod :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  intro O A _ _ _ _ _ _ a u
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_dual_quotient_form_eq_eval O A (Ideal.span {a})
    (u ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (CartierDual O A)) ∘ₗ
      (CartierDual.toDual O A).symm.toLinearMap)
  have hb' : ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := fun φ => hb φ.ofConv
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib O A A a (cobOne O A b) (fun φ ψ => by
    have hm := hb' (WithConv.toConv φ * WithConv.toConv ψ)
    rw [dUnit, AugCot.d_mul, map_add, map_smul, map_smul, ← dUnit, ← dUnit, hb', hb'] at hm
    simp only [Bialgebra.counitAlgHom_apply, CartierDual.counit_apply] at hm
    have hc : (WithConv.toConv φ * WithConv.toConv ψ).ofConv b =
        LinearMap.mul' O O (TensorProduct.map φ ψ (CoalgebraStruct.comul b)) := rfl
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, dualDistrib_eq_mul'_map,
      cobOne_apply]
    simp only [map_sub, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [← hc, ← hm]
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    ring)
  exact ⟨b, y, hy, hb'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinearStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeRhamPeriods_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ x y q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ y q' → IsPer u.ex u.Λ (x + y) (q + q') ∧ IsPer u.ex u.Λ (x - y) (q - q')) ∧ ∀ (a : ℂ) x q, IsPer u.ex u.Λ x q → IsPer u.ex u.Λ (a • x) (a • q) := by
  first | exact @GlobalTheory.CechPer.periods_linear | exact GlobalTheory.CechPer.periods_linear | (intros; apply GlobalTheory.CechPer.periods_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCocycleAffineOpenIsCoboundaryStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechOneCocycle_affineOpen_isCoboundary : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (K : Type) (W : K → X.Opens), (∀ i, W i ≤ U) → U ≤ ⨆ i, W i → ∀ f : ∀ i j, Γ(X, W i ⊓ W j), (∀ i j k, (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j)).op).hom (f i j) + (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k)).op).hom (f j k) = (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k)).op).hom (f i k)) → ∃ a : ∀ i, Γ(X, W i), ∀ i j, f i j = (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (a i) - (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (a j) := by
  first | exact @GlobalTheory.CechPer.cech_one_cocycle_split | exact GlobalTheory.CechPer.cech_one_cocycle_split | (intros; apply GlobalTheory.CechPer.cech_one_cocycle_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTermsStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_eq_additive_leading_terms : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (cob1 μ f) = coeff γ (cob1 (addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (cob2 μ c) = coeff γ (cob2 (addLaw R d) c) := by
  first | exact @GlobalTheory.CobLead.cob_eq_additive_lead | exact GlobalTheory.CobLead.cob_eq_additive_lead | (intros; apply GlobalTheory.CobLead.cob_eq_additive_lead <;> assumption)
end

