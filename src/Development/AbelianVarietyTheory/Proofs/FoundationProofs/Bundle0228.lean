import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramLocallyUnimodular
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.GramLoc

theorem exists_common_denom {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (p : Ideal R) [p.IsPrime] (L M : Submodule R W) (hM : M.FG) (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p L) :
    ∃ s : R, s ∉ p ∧ ∀ y ∈ M, s • y ∈ L := by
  obtain ⟨T, rfl⟩ := hM
  have h1 : ∀ y : T, ∃ s : R, s ∈ p.primeCompl ∧ s • (y : W) ∈ L := fun y =>
    h (Submodule.subset_span y.2)
  choose f hf hf' using h1
  refine ⟨∏ y, f y, Submonoid.prod_mem p.primeCompl (fun y _ => hf y), ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    classical
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : T)), mul_smul]
    exact L.smul_mem _ (hf' ⟨x, hx⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L.smul_mem _ hx

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def locRing (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {a | ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * a = r}
  mul_mem' := by
    rintro a b ⟨s, hs, r, hr⟩ ⟨t, ht, u, hu⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, r * u, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_neg] at *
    rw [← hr, ← hu]; ring
  one_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, 1, by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, r, hr⟩ ⟨t, ht, u, hu⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, t * r + s * u, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_neg] at *
    rw [← hr, ← hu]; ring
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, 0, by simp⟩
  neg_mem' := by
    rintro a ⟨s, hs, r, hr⟩
    refine ⟨s, hs, -r, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_neg] at *
    rw [← hr]; ring

theorem det_mem_subring (S : Subring K) (P : Matrix (Fin n) (Fin n) K) (h : ∀ a b, P a b ∈ S) :
    P.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem col_mem_colLat (B : GL (Fin n) K) (j : Fin n) :
    (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ colLat B :=
  Submodule.subset_span ⟨j, rfl⟩

theorem coord_of_mem_colLat (B : GL (Fin n) K) (x : Fin n → K) (hx : x ∈ colLat B) (j : Fin n) :
    ∃ r : 𝓞 K, (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) j = r := by
  unfold colLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have h : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.inv_mul B
    have h2 := congrFun (congrFun h j) i
    refine ⟨if j = i then 1 else 0, ?_⟩
    change (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) j i = _
    rw [h2, Matrix.one_apply]
    split_ifs <;> simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨u, hu⟩ := hy
    exact ⟨r + u, by rw [Matrix.mulVec_add, Pi.add_apply, hr, hu]; simp⟩
  | smul a x _ hx =>
    obtain ⟨r, hr⟩ := hx
    refine ⟨a * r, ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, hr, Algebra.smul_def]
    simp

variable [StarRing K]

theorem vw_nonneg_of_mem (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ∈ locRing w) :
    0 ≤ vw w a := by
  obtain ⟨s, hs, r, hr⟩ := ha
  by_cases h0 : a = 0
  · rw [h0, ValuationRepresentative.vw_zero]
  have hs0 : (s : K) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have h1 := ValuationRepresentative.vw_mul w _ _ hs0 h0
  have h2 : vw w (s : K) = 0 := idxChange_cnt_unit (K := K) w hs
  have h3 := ValuationRepresentative.vw_int_nonneg w r
  rw [hr, h2] at h1
  omega

theorem cO_notMem (w : HeightOneSpectrum (𝓞 K)) (t : 𝓞 K) (ht : t ∉ (conjPl w).asIdeal) :
    cO K t ∉ w.asIdeal := by
  intro h
  apply ht
  have := Ideal.mem_map_of_mem (cO K) h
  rwa [ValuationRepresentative.cO_cO] at this

theorem mem_localization_of_mem {w : HeightOneSpectrum (𝓞 K)} (M : Submodule (𝓞 K) (Fin n → K)) :
    M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := fun x hx =>
  ⟨1, one_mem _, by simpa using hx⟩

theorem gram_mem (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hM : hdualFr G M = M) (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (hB : IsBasisAt (conjPl w) M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) a b ∈ locRing w := by
  unfold IsBasisAt at hB hB'
  have h1 := mem_localization_of_mem (w := conjPl w) _ (col_mem_colLat B a)
  have h2 := mem_localization_of_mem (w := w) _ (col_mem_colLat B' b)
  rw [← hB] at h1
  rw [← hB'] at h2
  obtain ⟨t, ht, h1⟩ := h1
  obtain ⟨u, hu, h2⟩ := h2
  rw [← hM] at h2
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h2 _ h1)
  refine ⟨cO K t * u, fun h => (w.isPrime.mem_or_mem h).elim (cO_notMem w t ht) hu, r, ?_⟩
  change _ = algebraMap (𝓞 K) K r
  rw [hr, Matrix.mul_assoc]
  have hc : ((cO K t * u : 𝓞 K) : K) = star (t : K) * (u : K) := by
    rw [← ValuationRepresentative.cO_apply]; exact map_mul (algebraMap (𝓞 K) K) _ _
  rw [hc]
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply,
    Algebra.smul_def, Matrix.conjTranspose_apply, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change star (t : K) * (u : K) * _ = star (t : K) * _ * (_ * ((u : K) * _))
  ring

theorem gram_inv_mem (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K))
    (hG : IsUnit G.det) (hfg : M.FG)
    (hM : hdualFr G M = M) (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K)
    (hB : IsBasisAt (conjPl w) M B) (hB' : IsBasisAt w M B') (a b : Fin n) :
    (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) a b ∈ locRing w := by
  unfold IsBasisAt at hB hB'
  obtain ⟨t, ht, h1⟩ := exists_common_denom (conjPl w).asIdeal (colLat B) M hfg
    (hB ▸ mem_localization_of_mem M)
  set C : Matrix (Fin n) (Fin n) K := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hC
  set x : Fin n → K := fun i => (G⁻¹ * Cᴴ) i b with hx
  have hGx : G *ᵥ x = fun i => star (C b i) := by
    funext i
    change (G * (G⁻¹ * Cᴴ)) i b = _
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hG, Matrix.conjTranspose_apply]
  have hxM : cO K t • x ∈ hdualFr G M := by
    intro y hy
    obtain ⟨r, hr⟩ := coord_of_mem_colLat B _ (h1 y hy) b
    refine Submodule.mem_one.2 ⟨cO K r, ?_⟩
    change ((cO K r : 𝓞 K) : K) = _
    rw [ValuationRepresentative.cO_apply, ← hr, Matrix.mulVec_smul, Matrix.mulVec_smul, hGx]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.smul_apply,
      Algebra.smul_def, star_mul', Finset.mul_sum, star_sum, ← hC]
    refine Finset.sum_congr rfl fun i _ => ?_
    change star (t : K) * _ = _ * (star (t : K) * _)
    ring
  rw [hM] at hxM
  have h3 := mem_localization_of_mem (w := w) M hxM
  rw [hB'] at h3
  obtain ⟨u, hu, h3⟩ := h3
  obtain ⟨r, hr⟩ := coord_of_mem_colLat B' _ h3 a
  refine ⟨u * cO K t, fun h => (w.isPrime.mem_or_mem h).elim hu (cO_notMem w t ht), r, ?_⟩
  rw [← hr, ← mul_smul, Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  rfl

theorem gram_locally_unimodular : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (G : Matrix (Fin n) (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)), Gᴴ = G → IsUnit G.det → IsSelfDualK G M → ∀ (w : HeightOneSpectrum (𝓞 K)) (B B' : GL (Fin n) K), IsBasisAt (conjPl w) M B → IsBasisAt w M B' → (∀ a b, 0 ≤ vw w (((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) a b)) ∧ vw w ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)).det = 0 := by
  intro K _ _ _ n G M _ hG hM w B B' hB hB'
  have hfg : M.FG := hM.1.fg
  have h1 := gram_mem G M hM.2 w B B' hB hB'
  have h2 := gram_inv_mem G M hG hfg hM.2 w B B' hB hB'
  refine ⟨fun a b => vw_nonneg_of_mem w _ (h1 a b), ?_⟩
  have d1 := vw_nonneg_of_mem w _ (det_mem_subring _ _ h1)
  have d2 := vw_nonneg_of_mem w _ (det_mem_subring _ _ h2)
  have e : ((B : Matrix (Fin n) (Fin n) K)ᴴ * G * (B' : Matrix (Fin n) (Fin n) K)) *
      (((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (G⁻¹ * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ)) = 1 := by
    have e1 : (B' : Matrix (Fin n) (Fin n) K) * ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.mul_inv B'
    have e2 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 :=
      Units.inv_mul B
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B' : Matrix (Fin n) (Fin n) K), e1, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hG, ← Matrix.conjTranspose_mul, e2,
      Matrix.conjTranspose_one]
  have e' := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_one] at e'
  have e3 := ValuationRepresentative.vw_mul w _ _ (left_ne_zero_of_mul_eq_one e') (right_ne_zero_of_mul_eq_one e')
  rw [e', ValuationRepresentative.vw_one] at e3
  omega

end GlobalTheory.GramLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HodgeTateCupKummerClassesEqDlogDeterminant
section
open GlobalTheory.K5 Polynomial

noncomputable section

namespace GlobalTheory.K5.KummerCup

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem map_mk_mem {n : ℕ} (f : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω) (hx : f (xn p n) ∈ S)
    (hy : f (yn p n) ∈ S) (x : On p n) : f x ∈ S := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hC : ∀ Q : Polynomial (O0 p), f (Ideal.Quotient.mk (towerIdeal p n) (C Q)) ∈ S := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add a b ha hb => rw [map_add, map_add, map_add]; exact S.add_mem ha hb
    | monomial j b =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow]
      refine S.mul_mem ?_ (S.pow_mem hx j)
      have e : (Ideal.Quotient.mk (towerIdeal p n)) (C (C b)) = algebraMap (O0 p) (On p n) b := rfl
      rw [e, f.commutes]
      exact S.algebraMap_mem b
  induction P using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add, map_add]; exact S.add_mem ha hb
  | monomial j Q =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
    exact S.mul_mem (hC Q) (S.pow_mem hy j)

theorem pp_ne (m : ℕ) : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem q_pow (T : Tower p Ω) : ∀ m, T.qq m ^ (p ^ m) = T.qq 0
  | 0 => by simp
  | m + 1 => by rw [pow_succ', pow_mul, T.qpow, q_pow T m]

theorem qO_unit : IsUnit (qO p) := by
  have : IsUnit (HahnSeries.single (1 : ℤ) (1 : ℤ_[p]) : Lau p) := by
    refine ⟨⟨HahnSeries.single (1 : ℤ) (1 : ℤ_[p]), HahnSeries.single (-1 : ℤ) (1 : ℤ_[p]), ?_, ?_⟩, rfl⟩
    · rw [HahnSeries.single_mul_single]; simp
    · rw [HahnSeries.single_mul_single]; simp
  exact this.map _

theorem qq_ne_zero (T : Tower p Ω) (m : ℕ) : T.qq m ≠ 0 := by
  intro h
  have h0 := q_pow T m
  rw [h, zero_pow (pp_ne m), T.q0] at h0
  exact ((qO_unit (p := p)).map (algebraMap (O0 p) Ω)).ne_zero h0.symm

theorem zeta_mem (T : Tower p Ω) (m : ℕ) : T.ζ m ∈ integralClosure (O0 p) Ω := by
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pp_ne (p := p) m)) ?_
  rw [(T.prim m).pow_eq_one]
  exact isIntegral_one

theorem qq_mem (T : Tower p Ω) (m : ℕ) : T.qq m ∈ integralClosure (O0 p) Ω := by
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pp_ne (p := p) m)) ?_
  rw [q_pow, T.q0]
  exact isIntegral_algebraMap

theorem zeta_sub_one_ne (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n) : T.ζ n - 1 ≠ 0 :=
  sub_ne_zero.mpr ((T.prim n).ne_one (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt))

theorem p_div_mem (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n) :
    (p : Ω) / (T.ζ n - 1) ∈ integralClosure (O0 p) Ω := by
  classical
  have hne := zeta_sub_one_ne T hn
  have hpos : 0 < p ^ n := Nat.pos_of_ne_zero (pp_ne n)
  have h1 : eval 1 (cyclotomic (p ^ n) Ω) = (p : Ω) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact eval_one_cyclotomic_prime_pow m
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (T.prim n), eval_prod,
    ← Finset.mul_prod_erase _ _ ((mem_primitiveRoots hpos).mpr (T.prim n))] at h1
  have hR : (∏ μ ∈ (primitiveRoots (p ^ n) Ω).erase (T.ζ n), eval 1 (X - C μ)) ∈
      integralClosure (O0 p) Ω := by
    refine Subalgebra.prod_mem _ fun μ hμ => ?_
    have hμ' := (mem_primitiveRoots hpos).mp (Finset.mem_of_mem_erase hμ)
    simp only [eval_sub, eval_X, eval_C]
    refine Subalgebra.sub_mem _ (Subalgebra.one_mem _) ?_
    refine IsIntegral.of_pow hpos ?_
    rw [hμ'.pow_eq_one]
    exact isIntegral_one
  generalize (∏ μ ∈ (primitiveRoots (p ^ n) Ω).erase (T.ζ n), eval 1 (X - C μ)) = R at h1 hR
  simp only [eval_sub, eval_X, eval_C] at h1
  have : (p : Ω) / (T.ζ n - 1) = -R := by
    rw [div_eq_iff hne, ← h1]; ring
  rw [this]
  exact Subalgebra.neg_mem _ hR

theorem mem_Gn {T : Tower p Ω} {n : ℕ} {g : Gal p Ω} :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl

theorem fix_emb {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) {g : Gal p Ω}
    (hg : g ∈ Gn T n) (x : On p n) : g (ι x) = ι x :=
  map_mk_mem ι (AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id _ _))
    (by rw [hι.1]; exact (mem_Gn.mp hg).1) (by rw [hι.2]; exact (mem_Gn.mp hg).2) x

theorem emb_mem {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) (x : On p n) :
    ι x ∈ integralClosure (O0 p) Ω :=
  map_mk_mem ι _ (by rw [hι.1]; exact zeta_mem T n) (by rw [hι.2]; exact qq_mem T n) x

theorem kum_add {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Gn T n) :
    a (g * h) = a g + a h := by
  haveI : NeZero (p ^ n) := ⟨pp_ne n⟩
  have h1 := ha _ ((Gn T n).mul_mem hg hh)
  rw [AlgEquiv.mul_apply, ha h hh, map_mul, map_pow, (mem_Gn.mp hg).1, ha g hg, ← mul_assoc,
    ← pow_add] at h1
  have h2 := mul_right_cancel₀ hr h1
  rw [← pow_mod_orderOf, ← (T.prim n).eq_orderOf] at h2
  have h3 := (T.prim n).pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero (pp_ne n))) (ZMod.val_lt _) h2
  apply ZMod.val_injective
  rw [ZMod.val_add, ← h3, add_comm]

theorem kum_eq {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Gn T n)
    (e : h r = g r) : a h = a g := by
  haveI : NeZero (p ^ n) := ⟨pp_ne n⟩
  rw [ha g hg, ha h hh] at e
  exact ZMod.val_injective _
    ((T.prim n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (mul_right_cancel₀ hr e))

open Classical in

def ext0 {M : Type} [Zero M] (H : Subgroup (Gal p Ω)) (a : Gal p Ω → M) (g : Gal p Ω) : M :=
  if g ∈ H then a g else 0

theorem cochainExtendByZeroSubgroup_of_mem {M : Type} [Zero M] {H : Subgroup (Gal p Ω)} (a : Gal p Ω → M) {g : Gal p Ω}
    (hg : g ∈ H) : ext0 H a g = a g := if_pos hg

theorem matrixExtendByZero_add {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) : ∀ g ∈ Gn T n, ∀ h ∈ Gn T n,
    ext0 (Gn T n) a (g * h) = ext0 (Gn T n) a g + ext0 (Gn T n) a h := by
  intro g hg h hh
  rw [cochainExtendByZeroSubgroup_of_mem a hg, cochainExtendByZeroSubgroup_of_mem a hh, cochainExtendByZeroSubgroup_of_mem a ((Gn T n).mul_mem hg hh), kum_add hr ha hg hh]

theorem cochainExtendByZero_kummer_congr_of_action {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (e1 : h (T.ζ n) = g (T.ζ n))
    (e2 : h (T.qq n) = g (T.qq n)) (e : h r = g r) : ext0 (Gn T n) a h = ext0 (Gn T n) a g := by
  have hiff : h ∈ Gn T n ↔ g ∈ Gn T n := by rw [mem_Gn, mem_Gn, e1, e2]
  by_cases hg : g ∈ Gn T n
  · rw [cochainExtendByZeroSubgroup_of_mem a hg, cochainExtendByZeroSubgroup_of_mem a (hiff.mpr hg), kum_eq hr ha hg (hiff.mpr hg) e]
  · unfold ext0
    rw [if_neg hg, if_neg (fun hh => hg (hiff.mp hh))]

theorem kummerTower_coboundaryOne_prime_smul {k : ℕ} {H : Subgroup (Gal p Ω)} {f f' : Gal p Ω → Ω} (hf : Cob1 k H f)
    (e : ∀ g ∈ H, f' g = (p : Ω) * f g) : Cob1 k H f' := by
  obtain ⟨x, hx, h⟩ := hf
  have hp : IsIntegral (O0 p) (p : Ω) := (integralClosure (O0 p) Ω).natCast_mem p
  refine ⟨(p : Ω) * x, hp.mul hx, fun g hg => ?_⟩
  obtain ⟨z, hz, hz'⟩ := h g hg
  refine ⟨(p : Ω) * z, hp.mul hz, ?_⟩
  rw [e g hg, map_mul, map_natCast]
  linear_combination (p : Ω) * hz'

theorem kummerTower_coboundaryTwo_congr {k : ℕ} {H : Subgroup (Gal p Ω)} {f f' : Gal p Ω → Gal p Ω → Ω} (hf : Cob2 k H f)
    (e : ∀ g ∈ H, ∀ h ∈ H, f' g h = f g h) : Cob2 k H f' := by
  obtain ⟨w, hw, h⟩ := hf
  exact ⟨w, hw, fun g hg g' hg' => (e g hg g' hg') ▸ h g hg g' hg'⟩

theorem root_ne_zero {T : Tower p Ω} {n : ℕ} (hn : 1 ≤ n) (ι : On p n →ₐ[O0 p] Ω) {k : ℤ}
    {w : (On p n)ˣ} {r : Ω} (hr : r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w) : r ≠ 0 := by
  rintro rfl
  rw [zero_pow (pp_ne n)] at hr
  exact mul_ne_zero (zpow_ne_zero k (zeta_sub_one_ne T hn)) (w.isUnit.map ι).ne_zero hr.symm

theorem coef_int {T : Tower p Ω} {n : ℕ} (hn : 1 ≤ n) {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι)
    (c : ℕ) (k : ℤ) (β : On p n) :
    IsInt p ((p : Ω) ^ (c + 1) * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1))) := by
  have hp : (p : Ω) ∈ integralClosure (O0 p) Ω := (integralClosure (O0 p) Ω).natCast_mem p
  have e : (p : Ω) ^ (c + 1) * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) =
      (p : Ω) ^ (c + 1) * ι β + (p : Ω) ^ c * (k : Ω) * T.ζ n * ((p : Ω) / (T.ζ n - 1)) := by ring
  rw [e]
  exact add_mem (mul_mem (pow_mem hp _) (emb_mem hι β))
    (mul_mem (mul_mem (mul_mem (pow_mem hp _) (intCast_mem _ k)) (zeta_mem T n)) (p_div_mem T hn))

theorem coef_int' {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι)
    (c : ℕ) (α : On p n) : IsInt p ((p : Ω) ^ c * ι α) := by
  have hp : (p : Ω) ∈ integralClosure (O0 p) Ω := (integralClosure (O0 p) Ω).natCast_mem p
  exact mul_mem (pow_mem hp _) (emb_mem hι α)

theorem coef_fix {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) {g : Gal p Ω}
    (hg : g ∈ Gn T n) (k : ℤ) (β : On p n) :
    g (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) = ι β + (k : Ω) * T.ζ n / (T.ζ n - 1) := by
  rw [map_add, map_div₀, map_mul, map_sub, map_one, map_intCast, fix_emb hι hg, (mem_Gn.mp hg).1]

theorem cup_kummer_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k l : ℤ) (w w' : (On p n)ˣ) (α β α' β' : On p n), IsDlog p n (w : On p n) α β → IsDlog p n (w' : On p n) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w → s ^ (p ^ n) = (T.ζ n - 1) ^ l * ι w' →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a → IsKum T n (Gn T n) s b →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob2 n (Gn T n) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ c * (ι (fPi p n k l α β α' β') / (T.ζ n - 1)) * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p _ hp2
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.T.kummerCochain_eq_dlog_combination_finiteLevel p hp2
  refine ⟨4 * (c + 1), ?_⟩
  intro Ω _ _ hΩ T n hn ι hι k l w w' α β α' β' hw hw' r s hr hs a b lz lq ha hb hz hq
  have r0 := root_ne_zero hn ι hr
  have s0 := root_ne_zero hn ι hs
  have z0 : T.ζ (2 * n) ≠ 0 := (T.prim (2 * n)).ne_zero (pp_ne _)
  have q0 := qq_ne_zero T (2 * n)
  have h1 := hc Ω hΩ T n hn ι hι k w α β hw r hr a lz lq ha hz hq
  have h2 := hc Ω hΩ T n hn ι hι l w' α' β' hw' s hs b lz lq hb hz hq
  have key := GlobalTheory.T.kummer_cochain_cup_product_congruence p hp2 Ω (Gn T n) n (c + 1) (ext0 (Gn T n) a) (ext0 (Gn T n) b)
    (ext0 (Gn T n) lz) (ext0 (Gn T n) lq) (ι α) (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1))
    (ι α') (ι β' + (l : Ω) * T.ζ n / (T.ζ n - 1))
    (matrixExtendByZero_add r0 ha) (matrixExtendByZero_add s0 hb) (matrixExtendByZero_add z0 hz) (matrixExtendByZero_add q0 hq)
    (fun g hg => ⟨fix_emb hι hg _, coef_fix hι hg _ _, fix_emb hι hg _, coef_fix hι hg _ _⟩)
    (coef_int' hι _ _) (coef_int hn hι _ _ _) (coef_int' hι _ _) (coef_int hn hι _ _ _)
    (fun g => ⟨{T.ζ n, T.qq n, r, s, T.ζ (2 * n), T.qq (2 * n)}, fun h hS =>
      ⟨cochainExtendByZero_kummer_congr_of_action r0 ha (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action s0 hb (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action z0 hz (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action q0 hq (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp))⟩⟩)
    (kummerTower_coboundaryOne_prime_smul h1 fun g hg => by simp only [cochainExtendByZeroSubgroup_of_mem _ hg]; ring)
    (kummerTower_coboundaryOne_prime_smul h2 fun g hg => by simp only [cochainExtendByZeroSubgroup_of_mem _ hg]; ring)
  refine kummerTower_coboundaryTwo_congr key fun g hg h hh => ?_
  have hne := zeta_sub_one_ne T hn
  have e : ι (fPi p n k l α β α' β') / (T.ζ n - 1) =
      ι α * (ι β' + (l : Ω) * T.ζ n / (T.ζ n - 1)) - (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ι α' := by
    simp only [fPi, map_sub, map_mul, map_add, map_intCast, map_one, hι.1]
    field_simp
    ring
  simp only [cochainExtendByZeroSubgroup_of_mem _ hg, cochainExtendByZeroSubgroup_of_mem _ hh, e]

end GlobalTheory.K5.KummerCup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwiningGlOfUnitary
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem zpow_mul_eq_iff_toNat (d x y : ℂ) (hd : d ≠ 0) (a b : ℤ) :
    d ^ a * x = d ^ b * y ↔ d ^ (a - b).toNat * x = d ^ (b - a).toNat * y := by
  have ha : d ^ a = d ^ (min a b) * d ^ (a - b).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  have hb : d ^ b = d ^ (min a b) * d ^ (b - a).toNat := by
    rw [← zpow_natCast, ← zpow_add₀ hd]; congr 1; omega
  rw [ha, hb, mul_assoc, mul_assoc, mul_right_inj' (zpow_ne_zero _ hd)]

theorem exists_coef_sqRep (n : ℕ) (mu : DomWeight n) (f : nablaSq ℂ n mu)
    (l : Module.Dual ℂ (nablaSq ℂ n mu)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : GL (Fin n) ℂ,
      l (sqRep ℂ n mu g f) = (g : Matrix (Fin n) (Fin n) ℂ).det ^ mu.detShift *
        eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2) P := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend l
  obtain ⟨P, hP⟩ := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.1 n n f L
  refine ⟨rename Prod.swap P, fun g => ?_⟩
  rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, sqRep_coe, sqAct, map_smul, hP, eval_rename]
  simp only [detPow, smul_eq_mul, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem intertwining_gl_of_unitary (n : ℕ) (mu nu : DomWeight n)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu))
    (g : GL (Fin n) ℂ) (f : nablaSq ℂ n mu) :
    φ (sqRep ℂ n mu g f) = sqRep ℂ n nu g (φ f) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero]
  obtain ⟨P, hP⟩ := exists_coef_sqRep n mu f (l ∘ₗ φ.toLinearMap)
  obtain ⟨Q, hQ⟩ := exists_coef_sqRep n nu (φ f) l
  let D : MvPolynomial (Fin n × Fin n) ℂ := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  have hD : ∀ m : Matrix (Fin n) (Fin n) ℂ, eval (fun x => m x.1 x.2) D = m.det := by
    intro m
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
  have key : ∀ g : GL (Fin n) ℂ, l (φ (sqRep ℂ n mu g f)) = l (sqRep ℂ n nu g (φ f)) ↔
      eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.1 x.2)
        (D ^ (mu.detShift - nu.detShift).toNat * P - D ^ (nu.detShift - mu.detShift).toNat * Q) = 0 := by
    intro g
    have h1 : l (φ (sqRep ℂ n mu g f)) = _ := hP g
    rw [h1, hQ, zpow_mul_eq_iff_toNat _ _ _ (Matrix.GeneralLinearGroup.det_ne_zero g)]
    simp only [map_sub, map_mul, map_pow, hD, sub_eq_zero]
  have hz := GlobalTheory.Branching.rowAct_coef_poly_and_unitary_dense.2 n _ fun u hu =>
    (key (unitaryIncl n ⟨u, hu⟩)).1 (congrArg l (φ.isIntertwining _ _ ⟨u, hu⟩ f))
  rw [key, hz, map_zero]

end GlobalTheory.Branching
end

