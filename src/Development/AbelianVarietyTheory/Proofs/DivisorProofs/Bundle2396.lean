import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExistsSmallMemIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0212
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0073
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0065
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPullbackFramedTangent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramedTransport

theorem exists_model_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → GlobalTheory.DeRham.epsRed K ≫ y' = frX P → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → ∃ (ι : A.left ⟶ TF.Y.t.G.left) (ι' : A'.left ⟶ TF.Y.t.G.left), IsGrpPullback A TF.Y.t.G (frX P ≫ TF.Y.j) ι ∧ IsGrpPullback A' TF.Y.t.G (y' ≫ TF.Y.j) ι' ∧ i ≫ ι' = ι ∧ (∀ σ k, (ub σ k).left ≫ ι = spMap (dualMap (ev (frX P ≫ TF.Y.j) U.1 hU)) ≫ v (e ⟨σ, k⟩)) ∧ LBIso (TF.Y.t.PP.L.pull ι) (Xo.univ.t.PP.L.pull π) ∧ ⨆ k, (Xo.univ.t.PP.L.pull π).U k = ⊤ := by
  intro E _ _ _ H Dw l Xo c TF U n e v K _ _ P hU hB y' hy' hred A _ A' _ π π' i ub hi hπ hπ' hiπ hub
  have hx : frX P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _
  have hπ0 : IsGrpPullback A Xo.univ.t.G (frX P ≫ pullback.fst _ _) π := hπ.congr hx.symm rfl
  have w0 : π ≫ Xo.univ.t.G.hom = (A.hom ≫ frX P) ≫ pullback.fst _ _ := by
    rw [hπ0.1.w, Category.assoc]
  have w1 : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ y') ≫ pullback.fst _ _ := by
    rw [hπ'.1.w, Category.assoc]
  let lam := TF.Y.m0.cart.1.lift π (A.hom ≫ frX P) w0
  let lam' := TF.Y.m0.cart.1.lift π' (A'.hom ≫ y') w1
  have hl0 : lam ≫ TF.Y.m0.φ = π := TF.Y.m0.cart.1.lift_fst _ _ _
  have hl0' : lam' ≫ TF.Y.m0.φ = π' := TF.Y.m0.cart.1.lift_fst _ _ _
  have hs : lam ≫ TF.Y.oF.t.G.hom = A.hom ≫ frX P := TF.Y.m0.cart.1.lift_snd _ _ _
  have hs' : lam' ≫ TF.Y.oF.t.G.hom = A'.hom ≫ y' := TF.Y.m0.cart.1.lift_snd _ _ _
  have g1 : IsGrpPullback A TF.Y.oF.t.G (frX P) lam :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ0.congr rfl hl0.symm) hs
  have g1' : IsGrpPullback A' TF.Y.oF.t.G y' lam' :=
    IsGrpPullback.cancel TF.Y.m0.cart (hπ'.congr rfl hl0'.symm) hs'
  have hil : i ≫ lam' = lam := by
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0', hiπ, hl0]
    · rw [Category.assoc, hs', hs, ← Category.assoc, hi.1.w, Category.assoc, hred]
  obtain ⟨w, hw, -⟩ := TF.Y.m.lin
  obtain ⟨w0', hw0, -⟩ := TF.Y.m0.lin
  have i1 : LBIso (TF.Y.oF.t.PP.L.pull lam) (TF.Y.t.PP.L.pull (lam ≫ TF.Y.m.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m.φ) (fun _ => TF.Y.m.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w, hw⟩
  have i2 : LBIso (TF.Y.oF.t.PP.L.pull lam) (Xo.univ.t.PP.L.pull (lam ≫ TF.Y.m0.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ lam lam rfl)
      (chartPullSame _ (fun _ => lam ≫ TF.Y.m0.φ) (fun _ => TF.Y.m0.φ) (fun _ => 1) lam (fun _ => rfl)) ⟨w0', hw0⟩
  rw [hl0] at i2
  refine ⟨lam ≫ TF.Y.m.φ, lam' ≫ TF.Y.m.φ, g1.comp TF.Y.m.cart, g1'.comp TF.Y.m.cart, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hil]
  · intro σ k
    rw [← hB σ k]
    unfold frVec
    rw [FlagMod.toModel_left, ← Category.assoc]
    congr 1
    apply TF.Y.m0.cart.1.hom_ext
    · rw [Category.assoc, hl0, hub, FlagMod.liftTan_univ]
    · rw [Category.assoc, hs, ← Category.assoc, Over.w (ub σ k), FlagMod.liftTan_over]
      rfl
  · exact LBIso.trans (pull_isLB TF.Y.t.PP.isLB _) (pull_isLB TF.Y.oF.t.PP.isLB _)
      (pull_isLB Xo.univ.t.PP.isLB _) i1.symm i2
  · exact (pull_isLB Xo.univ.t.PP.isLB π).cover

end GlobalTheory.FramedTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_semilinear_lift_of_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (P : Type) [AddCommGroup P] [Module R₀ P], Module.Projective R₀ P → ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (W : Submodule R M), (∀ r, π r = 0 → ∀ m ∈ W, r • m = 0) → ∀ (q : M →ₗ[R] M') (v : P →+ M'), (∀ r w, v (π r • w) = r • v w) → (∀ w, ∃ m ∈ W, q m = v w) → ∃ u : P →+ M, (∀ r w, u (π r • w) = r • u w) ∧ (∀ w, u w ∈ W) ∧ ∀ w, q (u w) = v w := by
  intro R R₀ _ _ π hπ P _ _ hP M M' _ _ _ _ W hW q v hv hq
  classical
  choose m hmW hmq using hq
  choose σ hσ using hπ
  have key : ∀ (r s : R) (x : M), x ∈ W → π r = π s → r • x = s • x := by
    intro r s x hx h
    have := hW (r - s) (by rw [map_sub, h, sub_self]) x hx
    rwa [sub_smul, sub_eq_zero] at this
  let f : P → R₀ →+ M := fun w => AddMonoidHom.mk' (fun c => σ c • m w) (by
    intro a b
    rw [← add_smul]
    exact key _ _ _ (hmW w) (by rw [map_add, hσ, hσ, hσ]))
  have hf : ∀ w c, f w c = σ c • m w := fun _ _ => rfl
  let g : (P →₀ R₀) →+ M := Finsupp.liftAddHom f
  have hg : ∀ w c, g (Finsupp.single w c) = σ c • m w := by
    intro w c
    simp only [g, Finsupp.liftAddHom_apply_single, hf]
  have g1 : ∀ r x, g (π r • x) = r • g x := by
    intro r x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
    | single w c =>
      rw [Finsupp.smul_single, hg, hg, smul_smul]
      exact key _ _ _ (hmW w) (by rw [map_mul, hσ, hσ, smul_eq_mul])
  have g2 : ∀ x, g x ∈ W := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact W.add_mem ha hb
    | single w c => rw [hg]; exact W.smul_mem _ (hmW w)
  have g3 : ∀ x, q (g x) = v (Finsupp.linearCombination R₀ id x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | single w c =>
      rw [hg, Finsupp.linearCombination_single, map_smul, hmq, ← hv, hσ]
      rfl
  obtain ⟨s, hs⟩ := hP.out
  refine ⟨g.comp s.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro r w
    show g (s (π r • w)) = r • g (s w)
    rw [map_smul, g1]
  · intro w
    exact g2 _
  · intro w
    show q (g (s w)) = v w
    rw [g3, hs]

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallCoprimeNorm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmallNorm

open Module

theorem exists_pow_between (N f : ℕ) (hN : 1 ≤ N) (hf : 1 ≤ f) :
    ∃ r : ℕ, 1 ≤ r ∧ N ≤ r ^ f ∧ r ^ f ≤ 2 ^ f * N := by
  classical
  have hex : ∃ r : ℕ, N ≤ r ^ f := ⟨N, Nat.le_self_pow (by omega) N⟩
  have hP : N ≤ (Nat.find hex) ^ f := Nat.find_spec hex
  have hr0 : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, zero_pow (by omega)] at hP; omega
    · exact h
  refine ⟨Nat.find hex, hr0, hP, ?_⟩
  rcases Nat.eq_or_lt_of_le hr0 with h | h
  · rw [← h, one_pow]
    calc 1 ≤ 2 ^ f := Nat.one_le_two_pow
      _ ≤ 2 ^ f * N := Nat.le_mul_of_pos_right _ hN
  · have hlt : (Nat.find hex - 1) ^ f < N :=
      not_le.mp (Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega))
    calc (Nat.find hex) ^ f ≤ (2 * (Nat.find hex - 1)) ^ f := Nat.pow_le_pow_left (by omega) f
      _ = 2 ^ f * (Nat.find hex - 1) ^ f := by rw [mul_pow]
      _ ≤ 2 ^ f * N := Nat.mul_le_mul_left _ hlt.le

theorem isCoprime_norm_of_eq {F : Type} [Field F] [NumberField F] (q : ℕ) (b y : 𝓞 F)
    (h : b = 1 + (q : 𝓞 F) * y) : IsCoprime (Algebra.norm ℤ b) (q : ℤ) := by
  classical
  have key : ((Algebra.norm ℤ b : ℤ) : ZMod q) = 1 := by
    rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis F), ← eq_intCast (Int.castRingHom (ZMod q)),
      RingHom.map_det, h, map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast]
    simp
  have hd : (q : ℤ) ∣ Algebra.norm ℤ b - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [key, sub_self]
  obtain ⟨m, hm⟩ := hd
  exact ⟨1, -m, by linarith⟩

theorem exists_small_coprime_norm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (q : ℕ), 1 ≤ q → ∃ C : ℕ,
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ → IsCoprime I (Ideal.span {(q : 𝓞 F)}) →
      ∃ b ∈ I, b ≠ 0 ∧ IsCoprime (Algebra.norm ℤ b) (q : ℤ) ∧
        ∃ k : ℕ, IsTotPos (((k : F)) ^ 2 - (b : F) ^ 2) ∧ k ^ Module.finrank ℚ F ≤ C * Ideal.absNorm I := by
  intro F _ _ _ q hq
  classical
  have hf : 0 < finrank ℚ F := finrank_pos
  set D : ℝ := Real.sqrt |(discr F : ℝ)| with hD_def
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  set c₀ : ℝ := 3 * D ^ ((finrank ℚ F : ℝ)⁻¹) with hc₀_def
  have hc₀ : 0 ≤ c₀ := by positivity
  have habs : ∀ (τ : F →+* ℝ) (y : F), |τ y| = InfinitePlace.mk (Complex.ofRealHom.comp τ) y := by
    intro τ y
    rw [InfinitePlace.apply, RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]
  set C₂ : ℝ := ∑ i, ∑ w : InfinitePlace F, w (integralBasis F i) with hC₂_def
  have hC₂ : ∀ (τ : F →+* ℝ) i, |τ (integralBasis F i)| ≤ ∑ w : InfinitePlace F, w (integralBasis F i) := by
    intro τ i
    rw [habs]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w (integralBasis F i))
      (fun w _ => apply_nonneg w _) (Finset.mem_univ _)
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
  set K₀ : ℕ := ⌈(q : ℝ) * c₀ * (C₂ + 1)⌉₊ + 1 with hK₀_def
  refine ⟨K₀ ^ finrank ℚ F * 2 ^ finrank ℚ F, ?_⟩
  intro I hI hcop
  have hN : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.2 (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h))
  obtain ⟨r, hr1, hNr, hr2⟩ := exists_pow_between (Ideal.absNorm I) (finrank ℚ F) hN hf

  obtain ⟨a₀, ha₀I, ha₀0, ha₀⟩ := ReciprocityTheory.ChartRestriction.G.TB.Mink.exists_small_mem_ideal' F I hI
  have hsmall : ∀ τ : F →+* ℝ, |τ (a₀ : F)| ≤ c₀ * r := by
    intro τ
    have h1 := ha₀ (Complex.ofRealHom.comp τ)
    rw [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs] at h1
    refine h1.le.trans ?_
    have hNr' : (Ideal.absNorm I : ℝ) ≤ (r : ℝ) ^ finrank ℚ F := by exact_mod_cast hNr
    calc 3 * ((Ideal.absNorm I : ℝ) * D) ^ ((finrank ℚ F : ℝ)⁻¹)
        ≤ 3 * (((r : ℝ) ^ finrank ℚ F) * D) ^ ((finrank ℚ F : ℝ)⁻¹) := by gcongr
      _ = c₀ * r := by
          rw [Real.mul_rpow (by positivity) hD, Real.pow_rpow_inv_natCast (by positivity) hf.ne', hc₀_def]
          ring

  rw [Ideal.isCoprime_iff_add, Ideal.one_eq_top, Ideal.eq_top_iff_one, Ideal.add_eq_sup, Submodule.mem_sup] at hcop
  obtain ⟨x, hxI, z, hz, hxz⟩ := hcop
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hq0 : (q : F) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  set b₀ : 𝓞 F := (q : 𝓞 F) * a₀ with hb₀_def
  have hb₀F : (b₀ : F) = (q : F) * (a₀ : F) := by simp [hb₀_def]
  have ha₀F : (a₀ : F) ≠ 0 := by simpa using ha₀0
  have hb₀ : (b₀ : F) ≠ 0 := by rw [hb₀F]; exact mul_ne_zero hq0 ha₀F
  have hb₀I : b₀ ∈ I := Ideal.mul_mem_left _ _ ha₀I

  set zz : F := (x : F) / (b₀ : F) with hzz
  set c := (integralBasis F).repr zz with hc
  set t : 𝓞 F := ∑ i, ⌊c i⌋ • RingOfIntegers.basis F i with ht_def
  have hdec : zz - (t : F) = ∑ i, ((Int.fract (c i) : ℚ) : F) * integralBasis F i := by
    have h1 : zz = ∑ i, ((c i : ℚ) : F) * integralBasis F i := by
      conv_lhs => rw [← (integralBasis F).sum_repr zz]
      simp [Rat.smul_def, hc]
    have h2 : (t : F) = ∑ i, (((⌊c i⌋ : ℤ) : ℚ) : F) * integralBasis F i := by
      simp [ht_def, integralBasis_apply, zsmul_eq_mul]
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.fract, ← sub_mul]; push_cast; ring
  have hfr : ∀ τ : F →+* ℝ, |τ (zz - (t : F))| ≤ C₂ := by
    intro τ
    rw [hdec, map_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_mul, map_ratCast, abs_mul]
    have e1 : |((Int.fract (c i) : ℚ) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by exact_mod_cast Int.fract_nonneg _)]
      exact_mod_cast (Int.fract_lt_one _).le
    calc |((Int.fract (c i) : ℚ) : ℝ)| * |τ (integralBasis F i)| ≤ 1 * |τ (integralBasis F i)| := by
          gcongr
      _ ≤ _ := by rw [_root_.one_mul]; exact hC₂ τ i

  obtain ⟨s, hs0, hs⟩ : ∃ s : 𝓞 F, x - b₀ * s ≠ 0 ∧ ∀ τ : F →+* ℝ, |τ (zz - (s : F))| ≤ C₂ + 1 := by
    by_cases h0 : x - b₀ * t = 0
    · refine ⟨t + 1, ?_, fun τ => ?_⟩
      · intro h; apply ha₀0
        have : b₀ = 0 := by linear_combination h0 - h
        rw [hb₀_def] at this
        rcases mul_eq_zero.1 this with h' | h'
        · exact absurd (by exact_mod_cast h' : (q : F) = 0) hq0
        · exact h'
      · have : τ (zz - ((t + 1 : 𝓞 F) : F)) = τ (zz - (t : F)) - 1 := by
          push_cast; simp only [map_sub, map_add, map_one]; ring
        rw [this]
        calc |τ (zz - (t : F)) - 1| ≤ |τ (zz - (t : F))| + |(1 : ℝ)| := abs_sub _ _
          _ ≤ C₂ + 1 := by rw [abs_one]; linarith [hfr τ]
    · exact ⟨t, h0, fun τ => (hfr τ).trans (by linarith)⟩
  set b : 𝓞 F := x - b₀ * s with hb_def
  have hbI : b ∈ I := I.sub_mem hxI (Ideal.mul_mem_right _ _ hb₀I)
  have hbq : b = 1 + (q : 𝓞 F) * (-u - a₀ * s) := by
    rw [hb_def, hb₀_def]; linear_combination hxz
  have hbF : (b : F) = (b₀ : F) * (zz - (s : F)) := by
    rw [hzz, hb_def]; push_cast; field_simp
  have hbnd : ∀ τ : F →+* ℝ, |τ (b : F)| < (K₀ * r : ℕ) := by
    intro τ
    rw [hbF, map_mul, abs_mul, hb₀F, map_mul, map_natCast, abs_mul, Nat.abs_cast]
    have hr : (0 : ℝ) < r := by exact_mod_cast hr1
    have hK : (q : ℝ) * c₀ * (C₂ + 1) < K₀ := by
      rw [hK₀_def]; push_cast; linarith [Nat.le_ceil ((q : ℝ) * c₀ * (C₂ + 1))]
    calc (q : ℝ) * |τ (a₀ : F)| * |τ (zz - (s : F))| ≤ (q : ℝ) * (c₀ * r) * (C₂ + 1) := by
          gcongr
          · exact hsmall τ
          · exact hs τ
      _ = ((q : ℝ) * c₀ * (C₂ + 1)) * r := by ring
      _ < K₀ * r := by gcongr
      _ = ((K₀ * r : ℕ) : ℝ) := by push_cast; ring
  refine ⟨b, hbI, hs0, isCoprime_norm_of_eq q b _ hbq, K₀ * r, ?_, ?_⟩
  · intro τ
    have h := abs_lt.1 (hbnd τ)
    rw [map_sub, map_pow, map_pow, map_natCast]
    nlinarith [h.1, h.2]
  · rw [mul_pow, _root_.mul_assoc]
    exact Nat.mul_le_mul_left _ hr2

end GlobalTheory.SmallNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothNhdsOfSmoothOverLocalScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Desc

theorem exists_smooth_nhds_of_smooth_fromSpecStalk :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) (x : Sp R) (V W : P.Opens), W ≤ V → Smooth (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → LocallyOfFiniteType (W.ι ≫ p) → ∀ z : P, z ∈ W → (p z).asIdeal ≤ x.asIdeal → ∃ W' : P.Opens, z ∈ W' ∧ W' ≤ W ∧ Smooth (W'.ι ≫ p) := by
  intro R _ _ P p x V W hWV hV hW z hz hle
  have : LocallyOfFinitePresentation (W.ι ≫ p) := inferInstance
  have : Flat ((Sp R).fromSpecStalk x) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ x
  have : SurjectiveOnStalks ((Sp R).fromSpecStalk x) := inferInstance
  have e : W.ι ≫ p = P.homOfLE hWV ≫ V.ι ≫ p := by simp
  have h1 : Smooth (Limits.pullback.snd (P.homOfLE hWV ≫ V.ι ≫ p) ((Sp R).fromSpecStalk x)) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  have h2 : Smooth (Limits.pullback.snd (W.ι ≫ p) ((Sp R).fromSpecStalk x)) := by
    rw [e]; exact h1
  have hs : p z ⤳ x := (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 hle
  obtain ⟨y, hy⟩ : p z ∈ Set.range ((Sp R).fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hs
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.ι ≫ p)
    (g := (Sp R).fromSpecStalk x) (⟨z, hz⟩ : W) y hy.symm
  have h3 := GlobalTheory.GenSpread.mem_smoothLocus_of_isPullback
    (IsPullback.of_hasPullback (W.ι ≫ p) ((Sp R).fromSpecStalk x)) w
  rw [hw] at h3
  have h4 : Smooth ((W.ι ≫ p).smoothLocus.ι ≫ W.ι ≫ p) := GlobalTheory.smooth_smoothLocus_ι_comp _
  refine ⟨W.ι ''ᵁ (W.ι ≫ p).smoothLocus, ⟨⟨z, hz⟩, h3, rfl⟩, W.ι_image_le _, ?_⟩
  rw [← Scheme.Hom.isoImage_inv_ι, Category.assoc, Category.assoc]
  infer_instance

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProperModelFinitelyGeneratedSubring
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SmoothProperModel

theorem exists_smooth_proper_model : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f →
    ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧
      IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  intro k _ X f hsm hpr
  obtain ⟨R₀, _, φ, X₀, f₀, π, hm⟩ := GlobalTheory.T.scheme_models_spread k X f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := GlobalTheory.T.smooth_spreads_out k R₀ φ X X₀ f f₀ π hm hsm
  have m₁ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := GlobalTheory.T.isProper_spreads_out k R₁ φ₁ X _ f _ _ m₁ hpr
  have m₂ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  have sm₂' : Smooth (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := inferInstance
  let ψ₃ : R₂ →+* φ₂.range := φ₂.rangeRestrict
  have e₃ : φ₂.range.subtype.comp ψ₃ = φ₂ := by ext x; rfl
  have ft₃ : Algebra.FiniteType ℤ φ₂.range :=
    haveI := ft₂
    Algebra.FiniteType.of_surjective ψ₃.toIntAlgHom φ₂.rangeRestrict_surjective
  have m₃ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₃ ft₃ m₂
  exact ⟨φ₂.range, _, _, _, ft₃, inferInstance, inferInstance, m₃.2.2.2.2⟩

end GlobalTheory.SmoothProperModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpenStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_genericEigenFrame_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ (GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι)), GlobalTheory.LogKSDiv.genPt TF Z ≫ s₀ TF.Y Z = spMap φ₀ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ τ i, f₀.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧ ∀ (a : 𝓞 E) (k : Fin n), IsCombAtG TF.Y.t (LogKS.chart U) v ((Matrix.diagonal fun j => constFn TF.Y.s U.1 (embK c (e.symm j).1 a)) k) (v k ≫ (TF.Y.t.act.act a).left) := by
  first | exact @GlobalTheory.LogKSDiv.spread_genFrame | exact GlobalTheory.LogKSDiv.spread_genFrame | (intros; apply GlobalTheory.LogKSDiv.spread_genFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadMorphismBasicOpenAgreeFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_spread_basicOpen_agree : ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp R) (B Z B₀ : Scheme.{0})
    (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → QuasiCompact pB → QuasiSeparated pB → IsSeparated pZ →
    LocallyOfFinitePresentation pZ → ∀ (φ₀ : B₀ ⟶ B) (u₀ : B₀ ⟶ Z), Flat φ₀ → u₀ ≫ pZ = φ₀ ≫ pB →
    ∀ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB →
    (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)),
      t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u) →
    ∃ g : R, g ∉ x.asIdeal ∧ ∀ (Y : Scheme.{0}) (a : Y ⟶ B), (∀ y : Y, g ∉ (pB (a y)).asIdeal) →
      ∃ u' : Y ⟶ Z, u' ≫ pZ = a ≫ pB ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Y),
        t₀ ≫ φ₀ = t ≫ a → t₀ ≫ u₀ = t ≫ u' := by
  intro R _ _ x B Z B₀ pB pZ hfl hqc hqs hsep hlfp φ₀ u₀ hφfl hu₀ u hu hagree
  haveI := hfl; haveI := hqc; haveI := hqs; haveI := hsep; haveI := hlfp; haveI := hφfl
  obtain ⟨V, hxV, -, w, g₀, hw, hwg, hg₀⟩ :=
    GlobalTheory.StalkLimit.exists_spread (IsPullback.of_hasPullback pB ((Sp R).fromSpecStalk x)) pZ u hu
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open (a := x) hxV V.isOpen

  have key : pullback.fst φ₀ (pullback.fst pB V.ι) ≫ u₀ = pullback.snd φ₀ (pullback.fst pB V.ι) ≫ g₀ := by
    let qN : pullback φ₀ (pullback.fst pB V.ι) ⟶ Sp R := pullback.fst _ _ ≫ φ₀ ≫ pB
    haveI : Flat qN := inferInstance
    haveI : IsDominant ((Sp R).fromSpecStalk x) := by
      refine ⟨Dense.mono (s₁ := {genericPoint (Sp R)}) ?_ ?_⟩
      · rw [Set.singleton_subset_iff, Scheme.range_fromSpecStalk]
        exact genericPoint_specializes x
      · rw [dense_iff_closure_eq]
        exact (genericPoint_spec (Sp R)).trans (by simp)
    haveI : IsSchemeTheoreticallyDominant ((Sp R).fromSpecStalk x) := .of_isDominant _
    have hPB := IsPullback.of_hasPullback qN ((Sp R).fromSpecStalk x)
    haveI : IsSchemeTheoreticallyDominant (pullback.fst qN ((Sp R).fromSpecStalk x)) :=
      .of_isPullback hPB.flip
    refine ext_of_schDom pZ ?_ (pullback.fst qN ((Sp R).fromSpecStalk x)) ?_
    · simp only [Category.assoc, hu₀, hg₀]
      rw [pullback.condition_assoc]
    · let m : pullback qN ((Sp R).fromSpecStalk x) ⟶ pullback pB ((Sp R).fromSpecStalk x) :=
        pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _ ≫ φ₀) (pullback.snd _ _)
          (by rw [Category.assoc, Category.assoc]; exact pullback.condition)
      have hm : m ≫ pullback.fst pB ((Sp R).fromSpecStalk x) =
          pullback.fst qN ((Sp R).fromSpecStalk x) ≫ pullback.fst φ₀ (pullback.fst pB V.ι) ≫ φ₀ :=
        pullback.lift_fst _ _ _
      have h1 := hagree _ (pullback.fst _ _ ≫ pullback.fst _ _) m ((Category.assoc _ _ _).trans hm.symm)
      have h2 : m ≫ w = pullback.fst qN ((Sp R).fromSpecStalk x) ≫ pullback.snd φ₀ (pullback.fst pB V.ι) := by
        rw [← cancel_mono (pullback.fst pB V.ι)]
        rw [Category.assoc, hw, hm, Category.assoc, pullback.condition]
      rw [← Category.assoc, h1, ← hwg, ← Category.assoc, h2, Category.assoc]
  refine ⟨g, hxg, fun Y a ha => ?_⟩
  have hrange : Set.range (a ≫ pB) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hgV (ha y)
  let k : Y ⟶ pullback pB V.ι :=
    pullback.lift a (IsOpenImmersion.lift V.ι (a ≫ pB) hrange) (IsOpenImmersion.lift_fac _ _ _).symm
  refine ⟨k ≫ g₀, ?_, fun T t₀ t ht => ?_⟩
  · rw [Category.assoc, hg₀, pullback.lift_fst_assoc]
  · have := pullback.lift t₀ (t ≫ k) (by rw [ht, Category.assoc, pullback.lift_fst]) ≫= key
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
    exact this

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkMapIdentityModMaximalOfFixedPointStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_map_identity_mod_maximal_of_fixed_point : ∀ (X : Scheme.{0}) [IsIntegral X] (b : X ≅ X) (x : X), X.fromSpecResidueField x ≫ b.hom = X.fromSpecResidueField x → ∃ st : X.presheaf.stalk x →+* X.presheaf.stalk x, (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom = spMap st ≫ X.fromSpecStalk x ∧ (∀ a, IsLocalRing.residue (X.presheaf.stalk x) (st a) = IsLocalRing.residue (X.presheaf.stalk x) a) ∧ ∀ a, GlobalTheory.functionFieldMap b.hom (algebraMap (X.presheaf.stalk x) X.functionField a) = algebraMap (X.presheaf.stalk x) X.functionField (st a) := by
  first | exact @GlobalTheory.FixStalk.fixes_stalk | exact GlobalTheory.FixStalk.fixes_stalk | (intros; apply GlobalTheory.FixStalk.fixes_stalk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCmOrderActionMatrixOnAffineOpenStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_cmOrderActionMatrix_on_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∃ A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(X, U.1), ∀ a i, IsCombAtG t (GlobalTheory.LogKS.chart U) v (A a i) (v i ≫ (t.act.act a).left) := by
  first | exact @GlobalTheory.ActMatrix.actMatrix | exact GlobalTheory.ActMatrix.actMatrix | (intros; apply GlobalTheory.ActMatrix.actMatrix <;> assumption)
end

