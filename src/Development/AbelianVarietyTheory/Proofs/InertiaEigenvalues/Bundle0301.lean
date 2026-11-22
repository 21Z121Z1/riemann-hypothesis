import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Formalism.SharpRestriction.LevelLetterCocycles.TWSet
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCocyclesFinitelyGeneratedModPrime

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaRestrictionPolynomialConditionSecondForm
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.PolynomialInertiaAction

open GlobalTheory.Cut.PolyInertia

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  intro D i r ρ π Xs S _ hG _ v hv hP c
  obtain ⟨P, hP0, hPu⟩ := hP
  obtain ⟨-, hdec, hψ, -, -, -, -, ⟨hT, -⟩, -, ⟨hπ, -⟩, -⟩ := hG
  set γ0 := D.nd.gam0 i v with hγ0
  let a : S.X' → MatN D.nd i := fun x' =>
    Polynomial.aeval (rO D.nd i r (S.p x') γ0) (P.map (evT D.nd i (S.p x')))
  have ha_eq : ∀ x', a x' = ∑ k : Fin (P.natDegree + 1),
      evT D.nd i (S.p x') (P.coeff k) • rO D.nd i r (S.p x') (γ0 ^ (k : ℕ)) := by
    intro x'
    simp only [a, aeval_map_eq_sum, map_pow]
  have ha : InR' D.nd r S a := by
    refine ⟨P.natDegree + 1, fun k x' => evT D.nd i (S.p x') (P.coeff k), fun k => γ0 ^ (k : ℕ),
      fun k => hT _ (P.coeff k).2, ?_⟩
    funext x'
    rw [ha_eq, Finset.sum_apply]
  have h1 : InR' D.nd r S 1 := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
    funext x'
    simp
  have hchi : chiU D.nd i ((c : ℕ) + 1) γ0 = chiU D.nd i 1 γ0 :=
    (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v (D.nd.SQ_l i v (Or.inl hv)) γ0 (D.nd.locNd_chebotarevPlace_mem i v)).2 _
      (Nat.le_add_left _ _) c.2
  have hval : S.ψχ c a = (P.map (evT D.nd i π)).eval (D.nd.zeta i v) := by
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    let u := S.e.symm (0, Pi.single c 1)
    have hu : (S.e u).2 c = 1 := by simp [u]
    have e1 := congrArg (fun z => z.2 c) (hψ a ha u)
    simp only [hu, mul_one] at e1
    have e2 : ((a S.π').map (toK D.nd i)).mulVec u = ∑ k : Fin (P.natDegree + 1),
        toK D.nd i (evT D.nd i π (P.coeff k)) •
          (mapM (toK D.nd i) (rO D.nd i r π) (γ0 ^ (k : ℕ))).mulVec u := by
      rw [ha_eq, hπ]
      change ((toK D.nd i).mapMatrix _).mulVec u = _
      rw [map_sum, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.smul_mulVec]
      congr 1
      ext p q
      simp [mapM]
    rw [e2, map_sum, Prod.snd_sum, Finset.sum_apply] at e1
    change toK D.nd i _ = toK D.nd i _
    rw [← e1, ← Polynomial.coe_aeval_eq_eval, aeval_map_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hdec]
    simp only [Prod.smul_snd, Pi.smul_apply, hu, mul_one, map_pow, hchi, smul_eq_mul, map_mul,
      Units.val_pow_eq_pow_val]
    rfl
  rw [resIne, cocChi, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, hφ, hφ0, rfl⟩, rfl⟩
  funext γ
  change φ (yg D.nd r S γ) = 0
  have hy : InY D.nd r S (yg D.nd r S γ) :=
    ⟨1, fun _ => 1, fun _ => γ, fun _ => h1, by simp⟩
  have hay : InY D.nd r S (a * yg D.nd r S γ) :=
    ⟨1, fun _ => a, fun _ => γ, fun _ => ha, by simp⟩
  have hz : φ (a * yg D.nd r S γ) = 0 := by
    refine hφ0 _ hay fun x' hx' => ?_
    have h := hP0 (S.p x') hx' γ γ.2
    have : yg D.nd r S γ x' = (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) *
          Eel D.nd S x') := by
      rw [yg, sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [Pi.mul_apply, this, mul_smul_comm, ← mul_assoc]
    simp only [a]
    rw [h, zero_mul, smul_zero]
  rw [hφ a ha _ hy, matKO_smul_one, hval] at hz
  exact hPu.smul_eq_zero.mp hz

end GlobalTheory.Cut.PolynomialInertiaAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralNormLe
section
noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NonPowerRoot

theorem norm_pow_finrank {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] K] (x : K) :
    ‖(x : PadicAlgCl l)‖ ^ Module.finrank ℚ_[l] K = ‖Algebra.norm ℚ_[l] x‖ := by
  have h := Algebra.norm_eq_prod_embeddings ℚ_[l] (PadicAlgCl l) x
  have h2 : ∀ σ : K →ₐ[ℚ_[l]] PadicAlgCl l, ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
    intro σ
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
      minpoly.algHom_eq σ σ.injective]
    congr 1
    exact (minpoly.algHom_eq K.val K.val.injective x).symm
  rw [← PadicAlgCl.norm_extends, h, norm_prod]
  simp only [h2, Finset.prod_const, Finset.card_univ]
  rw [AlgHom.card]

theorem exists_not_pow {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] K] (u : PadicAlgCl l) (hu : u ∈ K) (h1 : 1 < ‖u‖) :
    ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, ‖y‖ ^ (m + 1) ≠ ‖u‖ := by
  have hd : 0 < Module.finrank ℚ_[l] K := Module.finrank_pos
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have key : ∀ y ∈ K, 0 < ‖y‖ → ∃ k : ℤ, ‖y‖ ^ Module.finrank ℚ_[l] K = (l : ℝ) ^ k := by
    intro y hy hy0
    have h := norm_pow_finrank K ⟨y, hy⟩
    have h0 : Algebra.norm ℚ_[l] (⟨y, hy⟩ : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact (pow_pos hy0 _).ne' h
    exact ⟨_, h.trans (Padic.norm_eq_zpow_neg_valuation h0)⟩
  obtain ⟨k, hk⟩ := key u hu (by linarith)
  have hk0 : 0 < k := by
    have : (1 : ℝ) < (l : ℝ) ^ k := by
      rw [← hk]; exact one_lt_pow₀ h1 hd.ne'
    exact (one_lt_zpow_iff_right₀ hl).mp this
  refine ⟨k.toNat, by omega, fun y hy hyu => ?_⟩
  have hy0 : 0 < ‖y‖ := by
    rcases (norm_nonneg y).eq_or_lt with h | h
    · rw [← h, zero_pow (Nat.succ_ne_zero _)] at hyu; linarith
    · exact h
  obtain ⟨a, ha⟩ := key y hy hy0
  have : (l : ℝ) ^ (a * ((k.toNat + 1 : ℕ) : ℤ)) = (l : ℝ) ^ k := by
    rw [zpow_mul, ← ha, ← hk, ← hyu, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
  have h3 : a * ((k.toNat + 1 : ℕ) : ℤ) = k := zpow_right_injective₀ (by linarith) hl.ne' this
  have h4 : ((k.toNat + 1 : ℕ) : ℤ) = k + 1 := by omega
  rw [h4] at h3
  rcases le_or_gt a 0 with h | h
  · nlinarith
  · nlinarith

theorem exists_root {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) (u : Ω) {m : ℕ} (hm : 0 < m) :
    ∃ y : Ω, y ^ (m + 1) + y ^ m + u = 0 ∧ 1 ≤ A.valuation y := by
  by_contra hne
  push_neg at hne
  set Q : Polynomial Ω := X ^ (m + 1) + X ^ m + C u with hQ
  have hdeg : Q.natDegree = m + 1 := by
    rw [hQ]; compute_degree!
    all_goals omega
  have hmon : Q.Monic := by
    rw [hQ]; monicity!
    all_goals omega
  have hnext : Q.nextCoeff = 1 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hdeg, hQ]
    simp [coeff_X_pow, coeff_C, hm.ne']
  have hs := (IsAlgClosed.splits Q).nextCoeff_eq_neg_sum_roots_of_monic hmon
  have hlt : A.valuation Q.roots.sum < 1 := by
    refine Multiset.sum_induction (fun z => A.valuation z < 1) _ ?_ ?_ ?_
    · intro a b ha hb
      exact A.valuation.map_add_lt ha hb
    · simp
    · intro a ha
      have := (mem_roots hmon.ne_zero).mp ha
      apply hne
      simpa [hQ] using this
  have : Q.roots.sum = -1 := by rw [← hnext, hs, neg_neg]
  rw [this] at hlt
  simp at hlt

theorem root_unique {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {u : Ω} (hu : A.valuation u < 1) (n : ℕ)
    {a b : Ω} (ha : a ∈ A) (hb : b ∈ A) (h1 : u * a ^ n + a + 1 = 0) (h2 : u * b ^ n + b + 1 = 0) : a = b := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨a, ha⟩ : A) ⟨b, hb⟩ n
  have hc' : a ^ n - b ^ n = (a - b) * (c : Ω) := by
    simpa using congrArg (fun z : A => (z : Ω)) hc
  by_contra hab
  have h3 : (a - b) * (u * c + 1) = 0 := by linear_combination h1 - h2 - u * hc'
  have h4 : u * c = -1 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · linear_combination h
  have h5 : A.valuation (u * c) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hu (A.valuation_le_one c)
  rw [h4] at h5
  simp at h5

theorem norm_le_one {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : Formalism.BasicNotions.LocBridge l E Ω (ReciprocityTheory.Gal.Dec A) O) (u : E)
    (hu : A.valuation (algebraMap E Ω u) < 1) : ‖Bw.j (algebraMap E Ω u)‖ ≤ 1 := by
  by_contra h1
  push_neg at h1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI := Bw.Kw.2
  obtain ⟨m, hm, hK⟩ := exists_not_pow Bw.Kw.1 _ (Bw.j_E u) h1
  obtain ⟨y, hy, hy1⟩ := exists_root A (algebraMap E Ω u) hm
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy1
  have hyA : y⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hy1
  have hroot : algebraMap E Ω u * y⁻¹ ^ (m + 1) + y⁻¹ + 1 = 0 := by
    have : algebraMap E Ω u = -(y ^ (m + 1) + y ^ m) := by linear_combination hy
    rw [this, inv_pow]
    field_simp
    ring
  have hfix : ∀ g : ReciprocityTheory.Gal.Dec (F := E) A, (g : Ω ≃ₐ[E] Ω) y = y := by
    intro g
    have h2 : (g : Ω ≃ₐ[E] Ω) y⁻¹ ∈ A := (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec g.2 _).mpr hyA
    have h3 := congrArg (g : Ω ≃ₐ[E] Ω) hroot
    simp only [map_add, map_mul, map_pow, map_one, map_zero, AlgEquiv.commutes] at h3
    have h4 := root_unique A hu (m + 1) h2 hyA h3 hroot
    rw [map_inv₀] at h4
    exact inv_injective h4
  have hmem : Bw.j y ∈ Bw.Kw.1 := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨g, hg⟩ := Bw.e.surjective ⟨σ, hσ⟩
    have := Bw.e_comm g y
    rw [hg, hfix g] at this
    exact this
  apply hK _ hmem
  have hz := congrArg Bw.j hy
  simp only [map_add, map_pow, map_zero] at hz
  set z := Bw.j y
  set w := Bw.j (algebraMap E Ω u)
  have hw : ‖w‖ = ‖z‖ ^ m * ‖z + 1‖ := by
    have : w = -(z ^ m * (z + 1)) := by linear_combination hz
    rw [this, norm_neg, norm_mul, norm_pow]
  have hz1 : 1 < ‖z‖ := by
    by_contra hle
    push_neg at hle
    have h5 : ‖z + 1‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max z 1).trans (max_le hle (by simp))
    have h6 : ‖z‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hle
    have := mul_le_one₀ h6 (norm_nonneg _) h5
    linarith
  have h7 : ‖z + 1‖ = ‖z‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hz1.ne')]
    simpa using hz1.le
  rw [hw, h7, pow_succ]

theorem integral_norm_le {l : ℕ} [Fact l.Prime] {y : PadicAlgCl l} (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  let B : ValuationSubring (PadicAlgCl l) := (Valued.v (R := PadicAlgCl l)).valuationSubring
  have h1 : IsIntegral B y := hy.tower_top
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have h2 : Valued.v y ≤ 1 := by
    rw [← hb]; exact b.2
  rw [← PadicAlgCl.valuation_coe]
  exact_mod_cast h2

theorem norm_lt_one_iff : ∀ {l : ℕ} [Fact (Nat.Prime l)] {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω},
    Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : Formalism.BasicNotions.LocBridge l E Ω (ReciprocityTheory.Gal.Dec A) O) (x : 𝓞 E),
      ‖(Formalism.BasicNotions.LocBridge.j Bw : Ω → Formalism.BasicNotions.Loc.Om l) ((algebraMap E Ω : E → Ω) (↑x : E))‖ < (1 : ℝ) ↔
        x ∈ v.asIdeal := by
  intro l _ E Ω _ _ _ _ _ v A hA O _ _ _ Bw
  let φ : 𝓞 E →+* PadicAlgCl l := (Bw.j.comp (algebraMap E Ω)).comp (algebraMap (𝓞 E) E)
  have hφ : ∀ x : 𝓞 E, φ x = Bw.j (algebraMap E Ω (x : E)) := fun _ => rfl
  have hle : ∀ x : 𝓞 E, ‖φ x‖ ≤ 1 := fun x =>
    integral_norm_le ((RingOfIntegers.isIntegral x).map φ.toIntAlgHom)
  let P : Ideal (𝓞 E) :=
    { carrier := {x | ‖φ x‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖φ (a + b)‖ < 1
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        show ‖φ (c * a)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ x, x ∈ P ↔ ‖φ x‖ < 1 := fun _ => Iff.rfl
  have hPp : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]; simp
    · rw [hP, map_mul, norm_mul] at hab
      by_contra hn
      rw [not_or, hP, hP, not_lt, not_lt] at hn
      nlinarith [hn.1, hn.2]
  have hP0 : P ≠ ⊥ := by
    intro h
    have hl : (l : 𝓞 E) ∈ P := by
      rw [hP, map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    rw [h, Ideal.mem_bot] at hl
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hl)
  have hPv : P ≤ v.asIdeal := by
    intro s hs
    by_contra hsv
    obtain ⟨a, t, ht, hat⟩ := v.isMaximal.exists_inv hsv
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hsv v.asIdeal.zero_mem
    have hs1 : 1 ≤ A.valuation (algebraMap E Ω (s : E)) := not_lt.mp (fun h => hsv ((hA s).mp h))
    have ht1 := (hA t).mpr ht
    have hu : A.valuation (algebraMap E Ω ((t : E) / (s : E))) < 1 := by
      rw [map_div₀, map_div₀, div_lt_one₀ (lt_of_lt_of_le zero_lt_one hs1)]
      exact ht1.trans_le hs1
    have h1 := norm_le_one Bw _ hu
    have hφs : 0 < ‖φ s‖ := by
      rw [norm_pos_iff, hφ]
      simpa using hs0
    rw [map_div₀, map_div₀, norm_div, ← hφ, ← hφ, div_le_one hφs] at h1
    have htP : t ∈ P := (hP t).mpr (h1.trans_lt hs)
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, ← hat]
    exact P.add_mem (P.mul_mem_left a hs) htP
  have heq : P = v.asIdeal := (hPp.isMaximal hP0).eq_of_le v.isPrime.ne_top hPv
  intro x
  rw [← heq, hP, hφ]

end GlobalTheory.NonPowerRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDual
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.BlochKatoDuality.Br

namespace GlobalTheory.TatePair

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)

theorem cup_coboundary_right (hopen : IsOpen (Set.range (algebraMap O LL))) (c : ↥(divisibleCocycles LA'))
    (d : ↥(latticeCocycles LA)) (hc : (c : G → A'.V ⧸ LA'.T) ∈ BD LA') :
    cupModuloIntegers PD hd L1 hL1 c d ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hcg : ∀ h, (c : G → A'.V ⧸ LA'.T) h =
      repD LA' h (Submodule.Quotient.mk v) - Submodule.Quotient.mk v := fun h =>
    (congrFun hw h).symm
  have hT : IsOpen (L1.T : Set LL) := integers_isOpen PD L1 hL1 hopen
  have hcont : Continuous fun g : G => P ((d : G → A.V) g) (A'.ρ g v) :=
    (IsModuleTopology.continuous_bilinear_of_finite_left P).comp
      (d.2.1.1.prodMk (A'.cont v))
  have hlc : IsLocallyConstant fun g : G =>
      -(Submodule.Quotient.mk (P ((d : G → A.V) g) (A'.ρ g v)) : LL ⧸ L1.T) :=
    (locConst_mk L1.T hT _ hcont).neg
  refine ⟨fun g => -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d),
    ⟨hlc, fun _ => Submodule.mem_top⟩, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  show repD L1 g (-torsionPairing PD hd L1 hL1 (repD LA' h (Submodule.Quotient.mk v)) (evT LA h d))
      - -torsionPairing PD hd L1 hL1 (repD LA' (g * h) (Submodule.Quotient.mk v)) (evT LA (g * h) d)
      + -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d) =
    cupModuloIntegers PD hd L1 hL1 c d (g, h)
  rw [cup_apply_alt]
  simp only [hcg, map_neg, ← torsionPairing_equivariant, lattice_cocycle_mul, map_mul, Module.End.mul_apply, map_add,
    map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

end Gen

theorem integral_pairing : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type)
    [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
      (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m →
    ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T),
      (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧
      (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' m hd
  obtain ⟨e⟩ := GlobalTheory.T.tate_H2_period_datum hT l P K LL O hG L1 hL1
  obtain ⟨⟨hO, hDVR, hFr⟩, -, -, htr, hopen⟩ := hG
  haveI := hO
  haveI := hDVR
  haveI := hFr
  haveI := htr
  obtain ⟨pr, hpr⟩ := exists_pr (P.PD K) hopen hd L1 hL1
  refine ⟨(pr.compr₂ e.toLinearMap).flip ∘ₗ Submodule.mkQ _, ?_, ?_, ?_⟩
  · intro d c
    show e (pr c (Submodule.Quotient.mk d)) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact hpr c d
  · intro d c hdB
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_mem_coboundaries (P.PD K) hd L1 hL1 c d hdB
  · intro d c hc
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_coboundary_right (P.PD K) hd L1 hL1 hopen c d hc

end GlobalTheory.TatePair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
section
noncomputable section

open GlobalTheory.TwSys Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ConjugatePlaceSplitting

theorem isSplitPl_of_isConjPl {D : D7} {P P' : PlE D.host} (hs : IsSplitPl D.host P)
    (hc : IsConjPl D.host P P') : IsSplitPl D.host P' := by
  obtain ⟨x, hx, hy⟩ := hs
  have hc' := GlobalTheory.TwistDet.isConjPl_iff.1 hc
  have h1 : GlobalTheory.TwistDet.conjInt D x ∈ P'.asIdeal := (hc' x).1 hx
  have h2 : x ∉ P'.asIdeal := fun h => hy (GlobalTheory.TwistDet.conjInt D x) rfl
    ((hc' (GlobalTheory.TwistDet.conjInt D x)).2 (by rwa [GlobalTheory.TwistDet.conjInt_conjInt]))
  refine ⟨GlobalTheory.TwistDet.conjInt D x, h1, fun y hy' => ?_⟩
  have : y = x := by
    rw [← GlobalTheory.TwistDet.conjInt_conjInt x]
    exact RingOfIntegers.ext hy'
  rwa [this]

end GlobalTheory.ConjugatePlaceSplitting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JDANEqRangeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_image_aN_eq_range_sum : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL), ∃ (r : ℕ) (y : Fin r → TW (RW LL) T), E.tie.jD T '' (aN W T letπ : Set (W.DD T)) = Set.range fun a : Fin r → AA K LL => ∑ i, inclR LL (E.tie.io (a i)) • y i := by
  first | exact @GlobalTheory.NL.WkRange.jD_aN_eq_range | exact GlobalTheory.NL.WkRange.jD_aN_eq_range | (intros; apply GlobalTheory.NL.WkRange.jD_aN_eq_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelInverseFibreProductLatticesStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_inverse_fibreProduct_lattices : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → (∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) ∧ (∀ (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f → (∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) → ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x) ∧ ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k)) (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), Onto T A q → Onto T' A' q' → IsHom A A' g → ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L), (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧ ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  first | exact @GlobalTheory.RedFun.SubLat.ker_inv_fibre | exact GlobalTheory.RedFun.SubLat.ker_inv_fibre | (intros; apply GlobalTheory.RedFun.SubLat.ker_inv_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCocyclesFinitelyGeneratedModPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCocycles_finitelyGenerated_mod_prime : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∃ s : Finset ↥(latticeCocycles LA), ∀ c : ↥(latticeCocycles LA), ∃ (a : ↥(latticeCocycles LA) → O) (c' : ↥(latticeCocycles LA)), ((c : ↥(GK K) → A.V) - ∑ i ∈ s, a i • (i : ↥(GK K) → A.V) - ((l : ℕ) : O) • (c' : ↥(GK K) → A.V)) ∈ latticeCoboundaries LA := by
  first | exact @GlobalTheory.LatRed.cocycles_fg_mod_l | exact GlobalTheory.LatRed.cocycles_fg_mod_l | (intros; apply GlobalTheory.LatRed.cocycles_fg_mod_l <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientsClosedSubQuotSumStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeQuotients_closed_sub_quot_sum : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 → lam ∣ x) → (∀ (A B : Ob k G) f, IsHom A B f → Function.Injective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) ∧ (∀ (A B : Ob k G) f, IsHom A B f → Function.Surjective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) ∧ (∀ (A B C : Ob k G) i j, IsHom A C i → IsHom B C j → Function.Surjective (i.coprod j) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin C.m → k)), Onto T C q) ∧ ∀ (T : LocLat G Qp LL O) (e₀ : ↥T.L.T), (∀ g x, T.ρ g x = x) → e₀ ≠ 0 → Submodule.span O {e₀} = ⊤ → ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  first | exact @GlobalTheory.RedFun.LatQuot.lattice_quotients | exact GlobalTheory.RedFun.LatQuot.lattice_quotients | (intros; apply GlobalTheory.RedFun.LatQuot.lattice_quotients <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCutCoboundaryModuleLeUnitDeltaStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → lenCob i (WpO D.nd i ρ π) (cocRho i r S Xs) ≤ ((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') ∧ ∀ c : Fin D.R.t, lenCob i (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) ≤ 2 * lenQ i (del51 D.nd S S.π') := by
  first | exact @GlobalTheory.Cut.CobOrd.main | exact GlobalTheory.Cut.CobOrd.main | (intros; apply GlobalTheory.Cut.CobOrd.main <;> assumption)
end

