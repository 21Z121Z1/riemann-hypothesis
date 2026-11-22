import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0014
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FirstLatticeBaseChange
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0036
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0008
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0003
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0012
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0009

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousLineBundle
section
open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousLine

theorem sum_scale {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
    (u : Fin n → MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ)
    (hu : ∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    ∑ j, ‖eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 =
      (∏ k, ‖c k‖ ^ a k) ^ 2 * ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PositivityTheory.Xgn.multihomogeneous_eval_scale K ι (u j) a c z (hu j), norm_mul, mul_pow, norm_prod]
  simp only [norm_pow]

theorem sum_pos {σ : Type} {n : ℕ} (u : Fin n → MvPolynomial σ ℤ) (z : σ → ℂ)
    (h : ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) :
    0 < ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 := by
  obtain ⟨j, hj⟩ := h
  exact Finset.sum_pos' (fun i _ => sq_nonneg _)
    ⟨j, Finset.mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩

theorem sqrt_scale (x y N D : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt ((x ^ 2 * N) / (y ^ 2 * D)) = x / y * Real.sqrt (N / D) := by
  rw [mul_div_mul_comm, ← div_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hx hy)]

end PositivityTheory.Xgn.MultihomogeneousLine

theorem PositivityTheory.Xgn.multihomogeneous_line_bundle : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) := by
  intro K _ _ ι _ A a b n u v hu hv hu0 hv0 hsm hconj
  refine ⟨⟨fun k => A.a k + (a k : ℤ) - (b k : ℤ),
    fun z => A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
      (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)), ?_, ?_⟩, rfl, ?_, ?_, fun _ => rfl⟩
  · intro z hz
    exact mul_pos (A.pos z hz) (Real.sqrt_pos.mpr (div_pos
      (MultihomogeneousLine.sum_pos u z (hu0 z hz)) (MultihomogeneousLine.sum_pos v z (hv0 z hz))))
  · intro c z hc
    rw [A.smul c z hc, MultihomogeneousLine.sum_scale u a hu, MultihomogeneousLine.sum_scale v b hv,
      MultihomogeneousLine.sqrt_scale _ _ _ _
        (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)
        (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)]
    have : ∀ k, ‖c k‖ ^ (A.a k + (a k : ℤ) - (b k : ℤ)) = ‖c k‖ ^ A.a k * ‖c k‖ ^ a k / ‖c k‖ ^ b k := by
      intro k
      have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      rw [zpow_sub₀ h0, zpow_add₀ h0, zpow_natCast, zpow_natCast]
    simp only [this, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  · have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ =>
        ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) :=
      ContDiff.sum fun j _ => PositivityTheory.Xgn.polynomial_norm_square_smooth _ (u j)
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ =>
        ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2) :=
      ContDiff.sum fun j _ => PositivityTheory.Xgn.polynomial_norm_square_smooth _ (v j)
    exact ContDiffOn.mul hsm (ContDiffOn.sqrt
      (hN.contDiffOn.div hD.contDiffOn fun z hz => (MultihomogeneousLine.sum_pos v z (hv0 z hz)).ne')
      fun z hz => (div_pos (MultihomogeneousLine.sum_pos u z (hu0 z hz))
        (MultihomogeneousLine.sum_pos v z (hv0 z hz))).ne')
  · intro z
    have := hconj z
    simp only [this, PositivityTheory.Xgn.polynomial_eval_complex_conjugate, RCLike.norm_conj]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousTwistFinite
section
open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousTwistFinite
open GroundTheory.Heights₂.Heights.NumbersDVR

theorem homog_prod {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (c : ∀ k, ι k)
    (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k) d := by
  have h := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)
    (fun k => d k • blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, c k⟩).pow (d k))
  have e : ∑ k, d k • blockWeight ι ⟨k, c k⟩ = d := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

theorem eval_mul_ne {K : Type} [Fintype K] {ι : K → Type} (c : ∀ k, ι k)
    (d : K → ℕ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (u : MvPolynomial (Σ k, ι k) ℤ)
    (hu : eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) :
    eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)) ≠ 0 := by
  rw [map_mul, map_mul]
  refine mul_ne_zero hu ?_
  simp only [map_prod, map_pow, MvPolynomial.map_X, MvPolynomial.eval_X]
  exact Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ (hc k))

end PositivityTheory.Xgn.MultihomogeneousTwistFinite

theorem PositivityTheory.Xgn.multihomogeneous_twist_finite : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) := by
  intro K _ _ ι _ Q bf bg hQmul hQ hU hV
  obtain ⟨TU, hTU, hselU⟩ :=
    PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {u | ∃ a b v, Q a b u v}
  obtain ⟨TV, hTV, hselV⟩ :=
    PositivityTheory.Xgn.finite_nonvanishing_selection (Σ k, ι k) {v | ∃ a b u, Q a b u v}
  have wU : ∀ t : TU, ∃ a b v, Q a b t.1 v := fun t => hTU t.2
  have wV : ∀ t : TV, ∃ a b u, Q a b u t.1 := fun t => hTV t.2
  choose aU bU vU hqU using wU
  choose aV bV uV hqV using wV
  obtain ⟨A, hA⟩ : ∃ A : K → ℕ, A = bg + (∑ t, aU t + ∑ t, aV t) := ⟨_, rfl⟩
  have leU : ∀ t k, aU t k ≤ A k := by
    intro t k
    rw [hA]
    simp only [Pi.add_apply, Finset.sum_apply]
    have := Finset.single_le_sum (f := fun t => aU t k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    omega
  have leV : ∀ t k, aV t k ≤ A k := by
    intro t k
    rw [hA]
    simp only [Pi.add_apply, Finset.sum_apply]
    have := Finset.single_le_sum (f := fun t => aV t k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
    omega
  have hbgA : ∀ k, bg k ≤ A k := by
    intro k
    rw [hA]
    simp only [Pi.add_apply]
    omega
  obtain ⟨B, hB⟩ : ∃ B : K → ℕ, B = A + bf - bg := ⟨_, rfl⟩
  have hAB : A + bf = B + bg := by
    funext k
    rw [hB]
    simp only [Pi.add_apply, Pi.sub_apply]
    have := hbgA k
    omega
  have lift : ∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ) (c : ∀ k, ι k), Q a b u v →
      (∀ k, a k ≤ A k) →
      Q A B (u * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k)
        (v * ∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - a) k) := by
    intro a b u v c hq hle
    have h := hQmul a b (A - a) u v _ hq (MultihomogeneousTwistFinite.homog_prod c (A - a))
    obtain ⟨_, _, hab⟩ := hQ a b u v hq
    have e1 : a + (A - a) = A := by
      funext k
      simp only [Pi.add_apply, Pi.sub_apply]
      have := hle k
      omega
    have e2 : b + (A - a) = B := by
      funext k
      have h1 := congrFun hab k
      have h2 := congrFun hAB k
      simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
      have := hle k
      omega
    rw [e1, e2] at h
    exact h
  let e := Fintype.equivFin ((TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)))
  let uu : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ :=
    Sum.elim (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k)
      (fun p => uV p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)
  let vv : (TU × (∀ k, ι k)) ⊕ (TV × (∀ k, ι k)) → MvPolynomial (Σ k, ι k) ℤ :=
    Sum.elim (fun p => vU p.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aU p.1) k)
      (fun p => p.1.1 * ∏ k, (X ⟨k, p.2 k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ (A - aV p.1) k)
  refine ⟨A, B, _, fun j => uu (e.symm j), fun j => vv (e.symm j), hAB, ?_, ?_, ?_⟩
  · intro j
    show Q A B (uu (e.symm j)) (vv (e.symm j))
    generalize e.symm j = w
    rcases w with ⟨t, c⟩ | ⟨t, c⟩
    · exact lift _ _ _ _ c (hqU t) (leU t)
    · exact lift _ _ _ _ c (hqV t) (leV t)
  · intro z hz
    obtain ⟨a, b, u, v, hq, hu⟩ := hU z hz
    choose c hc using hz
    obtain ⟨t, ht, htne⟩ := hselU z ⟨u, ⟨a, b, v, hq⟩, hu⟩
    refine ⟨e (Sum.inl (⟨t, ht⟩, c)), ?_⟩
    simp only [uu, Equiv.symm_apply_apply, Sum.elim_inl]
    exact MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne
  · intro z hz
    obtain ⟨a, b, u, v, hq, hv⟩ := hV z hz
    choose c hc using hz
    obtain ⟨t, ht, htne⟩ := hselV z ⟨v, ⟨a, b, u, hq⟩, hv⟩
    refine ⟨e (Sum.inr (⟨t, ht⟩, c)), ?_⟩
    simp only [vv, Equiv.symm_apply_apply, Sum.elim_inr]
    exact MultihomogeneousTwistFinite.eval_mul_ne c _ z hc _ htne
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFamPull
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_pull
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)
open PositivityTheory.Xgn.A_pull_line (comb)
open PositivityTheory.Xgn.A_pull_exists (pow_mul_mem)
open GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC (smul_mem_spanOver mem_spanOver_of_mem)

theorem latFamily_join {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {K : Type} [Fintype K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) {K' : Type} [Fintype K'] {ι' : K' → Type}
    [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V]
    (L : (∀ k, ι k) → AddSubgroup V) (hfam : IsLatFamily O x L) (f : V → V) (hf : ∀ v, f v = v) :
    IsLatFamily O (joinCoord x z) (fun s =>
      spanOver (chartRing O (mseg (joinCoord x z)) s) (f '' (L (restrictChart s) : Set V))) := by
  have hj : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (joinCoord x z) s =
      mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) :=
    fun s => PositivityTheory.Xgn.A_pull_line.mseg_join (AlgHom.id O Ω) x z s
  have hne : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (joinCoord x z) s ≠ 0 →
      mseg x (restrictChart s) ≠ 0 := by
    intro s hs
    rw [hj] at hs
    exact left_ne_zero_of_mul hs
  refine ⟨fun s _ a ha v hv => smul_mem_spanOver _ _ ha hv, ?_⟩
  intro s t hs ht v hv
  beta_reduce at hv ⊢
  have hq := div_mem_chartRing (o := O) (mseg (joinCoord x z)) t s
  set q := mseg (joinCoord x z) s / mseg (joinCoord x z) t with hqdef
  rw [spanOver] at hv
  induction hv using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hy
    obtain ⟨n, hn⟩ := pow_mul_mem (joinCoord x z) s t hs a ha
    obtain ⟨m, hm⟩ := hfam.2 _ _ (hne s hs) (hne t ht) e he
    have hw := div_mem_chartRing (o := O) (mseg (joinCoord x z)) t (comb (restrictChart t) s)
    set w := mseg (joinCoord x z) (comb (restrictChart t) s) / mseg (joinCoord x z) t with hwdef
    have ht' := hne t ht
    have hqw : q = w * (mseg x (restrictChart s) / mseg x (restrictChart t)) := by
      have h1 : mseg (joinCoord x z) (comb (restrictChart t) s) =
          mseg x (restrictChart t) * mseg z (fun k => s (.inr k)) := hj _
      rw [hqdef, hwdef, h1, hj s]
      field_simp
    refine ⟨n + m, ?_⟩
    have h : q ^ (n + m) • a • f e = (q ^ n * a * w ^ m) •
        f ((mseg x (restrictChart s) / mseg x (restrictChart t)) ^ m • e) := by
      rw [hf, hf, smul_smul, smul_smul, pow_add, mul_assoc (q ^ n * a), ← mul_pow, ← hqw]
      congr 1
      ring
    rw [h]
    exact smul_mem_spanOver _ _ (mul_mem hn (pow_mem hw m)) (mem_spanOver_of_mem _ ⟨_, hm, rfl⟩)
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : q ^ (m + n) • (a + b) = q ^ n • q ^ m • a + q ^ m • q ^ n • b := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n m]
    rw [h]
    exact add_mem (smul_mem_spanOver _ _ (pow_mem hq n) hm) (smul_mem_spanOver _ _ (pow_mem hq m) hn)
  | neg a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

theorem charData {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    (hinj : Function.Injective (algebraMap O Ω)) {F : Type} [Zero F] [One F] {Sg : Type} (p : ℕ)
    (hp : p.Prime) (w : O) (χ : Sg → F → O)
    (h : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O) ∧ (0 : F) ≠ 1 ∧
      ∀ τ, χ τ 0 = 0 ∧ χ τ 1 = 1) (R : Subalgebra O Ω) :
    CharData R p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
  obtain ⟨h0, ⟨u, hu, hw⟩, -, h01, hχ⟩ := h
  obtain ⟨u, rfl⟩ := hu
  refine ⟨?_, R.algebraMap_mem _, ⟨algebraMap O Ω ((u⁻¹ : Oˣ) * w ^ (p - 2)), R.algebraMap_mem _, ?_⟩, h01,
    fun τ => ⟨?_, ?_, fun a => R.algebraMap_mem _⟩⟩
  · rw [← map_natCast (algebraMap O Ω)]
    exact (map_ne_zero_iff _ hinj).2 h0
  · have h2 : p - 1 = p - 2 + 1 := by have := hp.two_le; omega
    rw [← map_mul, mul_assoc, ← pow_succ, ← h2, hw, Units.inv_mul_cancel_left, map_natCast]
  · simp only [(hχ τ).1, map_zero]
  · simp only [(hχ τ).2, map_one]

theorem mul_std_le {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {n : ℕ} (R R' : Subalgebra O Ω)
    (w : Ω) (A : AddSubgroup (Fin n → Ω)) (h : mulLat w (stdLat R _) ≤ A) :
    mulLat w (stdLat R' _) ≤ spanOver R' (bcMap Ω Ω _ '' (A : Set (Fin n → Ω))) := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' : ∀ i, y i ∈ R' := fun i => hy i (Set.mem_univ i)
  have e : (DistribMulAction.toAddMonoidHom (Fin n → Ω) w) y =
      ∑ i, y i • (w • (Pi.single i (1 : Ω) : Fin n → Ω)) := by
    change w • y = _
    conv_lhs => rw [pi_eq_sum_univ' y]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [e]
  refine sum_mem fun i _ => smul_mem_spanOver _ _ (hy' i) (mem_spanOver_of_mem _ ⟨_, h ⟨Pi.single i 1, ?_, rfl⟩, rfl⟩)
  intro j _
  change (Pi.single i (1 : Ω) : Fin n → Ω) j ∈ R
  rw [Pi.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

theorem span_eq {O Ω V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V]
    (R : Subalgebra O Ω) (L L' : AddSubgroup V) (h : L = L') (f : V → V) (hf : ∀ v, f v = v) :
    AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • e} = spanOver R (f '' (L' : Set V)) := by
  obtain rfl : f = id := funext hf
  rw [h, Set.image_id]
  rfl

end PositivityTheory.Xgn.A_fam_pull

theorem PositivityTheory.Xgn.t_fam_pull : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), IsLatticeFamily O (joinCoord x z) p w χ φ (pullFamily O x z D) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg (joinCoord x z)) c) _) ≤ (pullFamily O x z D c).af (chartRing O (mseg (joinCoord x z)) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))))) ∧ ((∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i))) ∧ ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∃ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)), HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' ∧ ∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x hinj F _ _ _ n Sg _ r s p hp w χ φ D hD K' _ _ ι' _ z
  have hc := ((PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 K' ι' z).2
  have hcd := PositivityTheory.Xgn.A_fam_pull.charData hinj p hp w χ hD.char
  refine ⟨⟨?_, fun τ => ?_, hD.char, fun c h => ?_, fun c h => ?_⟩, fun h1 => ⟨fun c h => ?_, fun haf =>
    ⟨fun c h τ => ?_, fun h2 c h => ?_⟩, fun hl τ i => ?_⟩, fun Lie W Om OmHT hB => ?_⟩
  · exact PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ hD.famM _ (fun _ => rfl)
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hD.fam τ
    exact ⟨PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a1 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a2 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a3 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a4 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a5 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a6 _ (fun _ => rfl),
      PositivityTheory.Xgn.A_fam_pull.latFamily_join x z _ a7 _ (fun _ => rfl)⟩
  · exact (GlobalTheory.T.lattice_base_change_larger_ring_holds (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1) Ω _
      (fun a ha => (hc c h).2 ha)).2
  · exact PositivityTheory.Xgn.test_facts_base_change (D (restrictChart c)) _ _ (hc c h).2 p _ _ φ (hD.test _ (hc c h).1)
  · exact ((PositivityTheory.Xgn.good_lattice_base_change (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1)
      (h1 _ (hc c h).1)).2 Ω _ (fun a ha => (hc c h).2 ha)).1
  · have e := ((((PositivityTheory.Xgn.good_lattice_base_change (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1)
      (h1 _ (hc c h).1)).2 Ω _ (fun a ha => (hc c h).2 ha)).2 τ).1)
    exact (PositivityTheory.Xgn.A_fam_pull.mul_std_le _ _ _ _ (haf _ (hc c h).1 τ)).trans e.ge
  · exact ((GlobalTheory.T.lattice_second_goodness (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1)
      (h1 _ (hc c h).1) (h2 _ (hc c h).1) (haf _ (hc c h).1)).2 Ω _ (fun a ha => (hc c h).2 ha)).1
  · obtain ⟨u, a, hu, hA⟩ := hl τ i
    refine ⟨u, pullDeg (K' := K') a, hu, fun c h v => ?_⟩
    refine PositivityTheory.Xgn.A_pull_line.main (AlgHom.id O Ω) x z u a _ hA
      (fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i) (fun c h => ?_) c h v
    have e := ((((PositivityTheory.Xgn.good_lattice_base_change (D (restrictChart c)) _ p _ _ (hcd _) (hD.base _ (hc c h).1)
      (h1 _ (hc c h).1)).2 Ω _ (fun a ha => (hc c h).2 ha)).2 τ).2.2 i)
    exact e.trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ rfl _ (fun _ => rfl)).symm
  · choose Lie' hLie using fun τ => (PositivityTheory.Xgn.t_pull_exists O Ω K ι x _ _ (Lie τ)).1 K' ι' z
    choose W' hW using fun τ => (PositivityTheory.Xgn.t_pull_exists O Ω K ι x _ _ (W τ)).1 K' ι' z
    choose Om' hOm using fun τ => (PositivityTheory.Xgn.t_pull_exists O Ω K ι x _ _ (Om τ)).1 K' ι' z
    choose OmHT' hOmHT using fun τ => (PositivityTheory.Xgn.t_pull_exists O Ω K ι x _ _ (OmHT τ)).1 K' ι' z
    refine ⟨Lie', W', Om', OmHT', fun τ c h => ?_, fun τ => ⟨hLie τ, hW τ, hOm τ, hOmHT τ⟩⟩
    obtain ⟨b1, b2, b3, b4⟩ := hB τ _ (hc c h).1
    exact ⟨(hLie τ c h).trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ b1 _ (fun _ => rfl)),
      (hW τ c h).trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ b2 _ (fun _ => rfl)),
      (hOm τ c h).trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ b3 _ (fun _ => rfl)),
      (hOmHT τ c h).trans (PositivityTheory.Xgn.A_fam_pull.span_eq _ _ _ b4 _ (fun _ => rfl))⟩
end

