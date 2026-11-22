import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutRealSyzygy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutRealSyzygy.flagIntegral_zero (f N : ℕ) : RestTerms.flagIntegral f N 0 = 0 := by
  simp [RestTerms.flagIntegral]

theorem RestCutRealSyzygy.proof (h₁ : RestTerms.RestTermWellDefined.Statement)
    (h₂ : RestCutPsiFlag.Statement) : RestCutRealSyzygy.Statement := by
  intro f N R hR m hm1 hmN τ G hG
  apply KRest.eq_zero_of_forall_psi
  intro ψ
  rw [(h₂ f N).2 ψ, KRest.psiPoly_map_mul]
  set Rψ : ℕ → Fin f → RestTerms.RootRing f N := fun l σ => KRest.psiPoly ψ (R l σ) with hRψ
  have hsyz : RestTerms.IsPowerSumDecomposition f N 0 Rψ := by
    have h0 := congrArg (KRest.psiPoly ψ) hR
    rw [map_zero, map_sum] at h0
    simp_rw [map_sum, KRest.psiPoly_map_mul] at h0
    exact h0.symm
  have hzero : RestTerms.IsPowerSumDecomposition f N 0 (fun _ _ => 0) := by
    simp [RestTerms.IsPowerSumDecomposition]
  have h := h₁ f N 0 Rψ (fun _ _ => 0) hsyz hzero m hm1 hmN τ G hG
  simp only [RestTerms.restTerm, mul_zero, RestCutRealSyzygy.flagIntegral_zero] at h
  have hm : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  exact (mul_eq_zero.mp h).resolve_left hm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutRestHom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace KRest

theorem isHomogeneous_vandermondeOf {σ R : Type*} [CommRing R] {m : ℕ}
    (v : Fin m → MvPolynomial σ R) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (RestTerms.vandermondeOf v).IsHomogeneous (∑ i : Fin m, (Finset.Ioi i).card) := by
  unfold RestTerms.vandermondeOf
  refine IsHomogeneous.prod _ _ _ fun i _ => ?_
  have h := IsHomogeneous.prod (Finset.Ioi i) (fun j => v i - v j) (fun _ => 1)
    fun j _ => (hv i).sub (hv j)
  simpa using h

theorem add_mul_add_sub_one (r a : ℕ) :
    (r + a) * (r + a - 1) = r * (r - 1) + a * (a - 1) + 2 * (r * a) := by
  rcases r with _ | r
  · simp
  rcases a with _ | a
  · simp
  have h1 : r + 1 + (a + 1) - 1 = r + a + 1 := by omega
  rw [h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
  ring

end KRest

theorem RestCutRestHom.proof : RestCutRestHom.Statement := by
  intro f r a c

  have hy : ∀ τ i, (RestTerms.yRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_C_mul_X _ _
  have hz : ∀ τ i, (RestTerms.zRoot f r a c τ i).IsHomogeneous 1 := fun τ i =>
    isHomogeneous_X _ _

  have hμ : (RestTerms.smallBlockMu f r a c).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => hy τ i

  set dy := ∑ i : Fin r, (Finset.Ioi i).card with hdy
  set dz := ∑ i : Fin a, (Finset.Ioi i).card with hdz
  have hfib : (RestTerms.fibreClass f r a c).IsHomogeneous (f * (dy + dz)) := by
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
      (fun τ => RestTerms.vandermondeOf (RestTerms.yRoot f r a c τ) *
        RestTerms.vandermondeOf (RestTerms.zRoot f r a c τ)) (fun _ => dy + dz)
      fun τ _ => (KRest.isHomogeneous_vandermondeOf _ (hy τ)).mul
        (KRest.isHomogeneous_vandermondeOf _ (hz τ))
    simpa [RestTerms.fibreClass, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h

  have hdy2 : dy * 2 = r * (r - 1) := KRest.sum_card_Ioi_mul_two r
  have hdz2 : dz * 2 = a * (a - 1) := KRest.sum_card_Ioi_mul_two a
  have hdeg : 1 * (f * (r * a)) + f * (dy + dz) = RestTerms.topDegree f (r + a) := by
    have hS : (r + a) * (r + a - 1) / 2 = r * a + (dy + dz) := by
      rw [KRest.add_mul_add_sub_one, ← hdy2, ← hdz2]
      have : dy * 2 + dz * 2 + 2 * (r * a) = 2 * (r * a + (dy + dz)) := by ring
      rw [this, Nat.mul_div_cancel_left _ two_pos]
    rw [RestTerms.topDegree, hS]
    ring
  refine ⟨?_, ?_⟩
  · rw [← hdeg]
    exact (hμ.pow _).mul hfib
  · have h := (hμ.pow (f * (r * a) + 1)).mul hfib
    have he : 1 * (f * (r * a) + 1) + f * (dy + dz) = RestTerms.topDegree f (r + a) + 1 := by
      rw [← hdeg]; ring
    rw [he] at h
    exact h

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTermEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutTermEq.proof (h₁ : RestCutRealSyzygy.Statement) (h₂ : RestCutPsiFlag.Statement)
    (h₃ : RestCutTransportPsum.Statement) : RestCutTermEq.Statement := by
  intro f j k N e I c hcomp F Q₀ hQ₀ hQ₀h Q hQ m hm1 hmN τ G hG
  have hNjk : N = j + k := by simpa using Fintype.card_congr e
  subst hNjk
  have hf : 0 < f := Fin.pos τ
  set E' : Fin f × (Fin j ⊕ Fin k) → Fin f × Fin (j + k) := fun p => (p.1, e.symm p.2) with hE'
  have hpr : ∀ x : RootPoly f j k, restRename f j k (j + k) e (rename E' x) = x := by
    intro x
    rw [restRename, rename_rename]
    convert rename_id_apply x
    funext p
    simp [hE']
  have hrp : ∀ x : MvPolynomial (Fin f × Fin (j + k)) ℝ, rename E' (restRename f j k (j + k) e x) = x := by
    intro x
    rw [restRename, rename_rename]
    convert rename_id_apply x
    funext p
    simp [hE']
  have hpsum : ∀ l σ, rename E' (rootPsum f j k l σ) =
      map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) := by
    intro l σ
    rw [← h₃ f j k (j + k) e l σ]
    exact hrp _
  set R : ℕ → Fin f → MvPolynomial (Fin f × Fin (j + k)) ℝ :=
    fun l σ => rename E' (Q σ l) - map (algebraMap ℚ ℝ) (Q₀ l σ) with hR
  have hsyz : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
      map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * R l σ = 0 := by
    simp only [hR, mul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have h1 : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
        map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) * rename E' (Q σ l) =
        rename E' (restTransport f j k (j + k) e F) := by
      rw [hQ.2, map_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [map_mul, hpsum]
    have h2 : ∑ l ∈ Finset.Icc 1 (j + k), ∑ σ : Fin f,
        map (algebraMap ℚ ℝ) (RestTerms.blockPowerSum f (j + k) l σ) *
          map (algebraMap ℚ ℝ) (Q₀ l σ) = map (algebraMap ℚ ℝ) F := by
      rw [hQ₀]
      simp only [map_sum, map_mul]
    rw [h1, h2]
    exact hrp _
  have hzero := h₁ f (j + k) R hsyz m hm1 hmN τ G hG
  have hDle : j + k ≤ flagDim f j k + 1 := by
    have h1 : (j + k - 1) * 2 ≤ (j + k) * (j + k - 1) := by
      rcases Nat.lt_or_ge (j + k) 2 with h | h
      · interval_cases h : (j + k) <;> simp
      · rw [mul_comm]; exact Nat.mul_le_mul_right _ h
    have h2 : j + k - 1 ≤ (j + k) * (j + k - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 h1
    have h3 : (j + k) * (j + k - 1) / 2 ≤ flagDim f j k := by
      unfold flagDim; exact Nat.le_mul_of_pos_left _ hf
    omega
  have hdeg : m - 1 + (flagDim f j k + 1 - m) = flagDim f j k := by omega
  have hQh : (rename E' (Q τ m)).IsHomogeneous (flagDim f j k + 1 - m) :=
    (hQ.1 τ m hm1 hmN).rename_isHomogeneous
  have hQ₀m := hQ₀h m τ hm1 hmN
  have hsplit : restTransport f j k (j + k) e G * Q τ m =
      restRename f j k (j + k) e (map (algebraMap ℚ ℝ) G * R m τ) +
        restRename f j k (j + k) e (map (algebraMap ℚ ℝ) (G * Q₀ m τ)) := by
    rw [← map_add, hR]
    simp only
    rw [map_mul (map (algebraMap ℚ ℝ)) G, ← mul_add, sub_add_cancel, map_mul, hpr]
    rfl
  rw [hsplit, map_add, hcomp _ ?_, hcomp _ ?_, hzero, (h₂ f (j + k)).1]
  · ring
  · rw [← hdeg]; exact ((hG.mul hQ₀m).map _)
  · rw [← hdeg]
    exact (hG.map _).mul (hQh.sub (hQ₀m.map _))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutTransportFirst

theorem map_vandermondeOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (RestTerms.vandermondeOf v) = RestTerms.vandermondeOf (fun i => φ (v i)) := by
  simp [RestTerms.vandermondeOf, map_prod, map_sub]

theorem transport_X (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (p : Fin f × Fin N) :
    restTransport f j k N e (X p) = X (p.1, e p.2) := by
  simp [restTransport, restRename]

theorem transport_C (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (c : ℚ) :
    restTransport f j k N e (C c) = C (c : ℝ) := by
  simp [restTransport, restRename]

theorem transport_yRoot (f j k : ℕ) (τ : Fin f) (i : Fin j) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.yRoot f j k .first τ i) =
      -X (τ, Sum.inl i) := by
  have h : (⟨i.val, by have := i.isLt; omega⟩ : Fin (j + k)) = Fin.castAdd k i := Fin.ext rfl
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, map_mul, transport_C,
    transport_X, h, restFirstEquiv, finSumFinEquiv_symm_apply_castAdd]
  simp

theorem transport_zRoot (f j k : ℕ) (τ : Fin f) (i : Fin k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.zRoot f j k .first τ i) =
      X (τ, Sum.inr i) := by
  have h : (⟨j + i.val, by have := i.isLt; omega⟩ : Fin (j + k)) = Fin.natAdd j i := Fin.ext rfl
  simp only [RestTerms.zRoot, RestTerms.zIndex, transport_X, h, restFirstEquiv,
    finSumFinEquiv_symm_apply_natAdd]

theorem transport_mu (f j k : ℕ) (hjk : j < k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallBlockMu f j k .first) =
      smallMu f j k := by
  have hkj : ¬ k ≤ j := by omega
  simp only [RestTerms.smallBlockMu, map_sum, transport_yRoot, smallMu, if_neg hkj]

theorem transport_fib (f j k : ℕ) (hjk : j < k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.fibreClass f j k .first) =
      fibre f j k := by
  have hkj : ¬ k ≤ j := by omega
  simp only [RestTerms.fibreClass, map_prod, map_mul, map_vandermondeOf, transport_yRoot,
    transport_zRoot, fibre, if_neg hkj, vandermonde, KRest.det_rev_pow_eq_vandermondeOf]

end RestCutTransportFirst

theorem RestCutTransportFirst.proof : RestCutTransportFirst.Statement := by
  intro f j k hjk
  have hn : f * (j * k) = f * j * k := (Nat.mul_assoc f j k).symm
  refine ⟨?_, ?_⟩
  · rw [RestTerms.restPolynomial, map_mul, map_pow, RestCutTransportFirst.transport_mu f j k hjk,
      RestCutTransportFirst.transport_fib f j k hjk, restInput, hn]
  · rw [map_mul, map_pow, RestCutTransportFirst.transport_mu f j k hjk,
      RestCutTransportFirst.transport_fib f j k hjk, degreeInput, hn]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutTransportLast

theorem transport_X (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (p : Fin f × Fin N) :
    restTransport f j k N e (X p) = X (p.1, e p.2) := by
  simp [restTransport, restRename]

theorem transport_C (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (c : ℚ) :
    restTransport f j k N e (C c) = C (c : ℝ) := by
  simp [restTransport, restRename]

theorem lastEquiv_top (j k : ℕ) (i : Fin j) (h : (i : ℕ) < k + j) :
    restLastEquiv j k ⟨i, h⟩ = Sum.inl i := by
  have : (finCongr (Nat.add_comm k j)) ⟨i, h⟩ = Fin.castAdd k i := Fin.ext rfl
  simp only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd]

theorem lastEquiv_bottom (j k : ℕ) (i : Fin k) (h : j + (i : ℕ) < k + j) :
    restLastEquiv j k ⟨j + i, h⟩ = Sum.inr i := by
  have : (finCongr (Nat.add_comm k j)) ⟨j + i, h⟩ = Fin.natAdd j i := Fin.ext rfl
  simp only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]

theorem transport_yRoot (f j k : ℕ) (τ : Fin f) (i : Fin k) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.yRoot f k j .last τ i) =
      X (τ, Sum.inr i) := by
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, map_mul, transport_C,
    transport_X, lastEquiv_bottom]
  simp

theorem transport_zRoot (f j k : ℕ) (τ : Fin f) (i : Fin j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.zRoot f k j .last τ i) =
      X (τ, Sum.inl i) := by
  simp only [RestTerms.zRoot, RestTerms.zIndex, transport_X, lastEquiv_top]

theorem map_vandermondeOf {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) {m : ℕ}
    (v : Fin m → R) : g (RestTerms.vandermondeOf v) = RestTerms.vandermondeOf fun i => g (v i) := by
  simp only [RestTerms.vandermondeOf, map_prod, map_sub]

theorem transport_mu (f j k : ℕ) (hk : k ≤ j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.smallBlockMu f k j .last) =
      smallMu f j k := by
  simp only [RestTerms.smallBlockMu, map_sum, transport_yRoot, smallMu, if_pos hk]

theorem transport_fib (f j k : ℕ) (hk : k ≤ j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.fibreClass f k j .last) =
      fibre f j k := by
  simp only [RestTerms.fibreClass, fibre, if_pos hk, map_prod, map_mul, map_vandermondeOf,
    transport_yRoot, transport_zRoot, vandermonde, KRest.det_rev_pow_eq_vandermondeOf]

end RestCutTransportLast

open RestCutTransportLast in

theorem RestCutTransportLast.proof : RestCutTransportLast.Statement := by
  intro f j k hk
  have hn : f * (k * j) = f * j * k := by ring
  refine ⟨?_, ?_⟩
  · rw [RestTerms.restPolynomial, map_mul, map_pow, transport_mu f j k hk, transport_fib f j k hk,
      hn]
    rfl
  · rw [map_mul, map_pow, transport_mu f j k hk, transport_fib f j k hk, hn]
    rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportPsum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutTransportPsum.proof : RestCutTransportPsum.Statement := by
  intro f j k N e m τ
  simp only [restTransport, restRename, RestTerms.blockPowerSum, rootPsum, RingHom.comp_apply,
    map_sum, map_pow, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X]
  exact Equiv.sum_comp e (fun i => (X (τ, i) : RootPoly f j k) ^ m)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem RestTermSharp.proof (h₁ : RestCutCaseSharp.Statement)
    (h₂ : RestCutTransportLast.Statement) (h₃ : RestCutTransportFirst.Statement)
    (h₄ : RestCutLieLast.Statement) (h₅ : RestCutLieFirst.Statement) :
    RestTermSharp.Statement := by
  intro f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  by_cases hkj : k ≤ j
  · obtain ⟨hF, hJ⟩ := h₂ f j k hkj
    exact h₁ f j k k j .last (restLastEquiv j k) hf hj hk hk hj (Nat.add_comm k j)
      (Nat.mul_comm k j) hF hJ (h₄ f j k hkj) I hI vol hvol P hP B₀ hB φ
  · have hjk : j < k := by omega
    obtain ⟨hF, hJ⟩ := h₃ f j k hjk
    exact h₁ f j k j k .first (restFirstEquiv j k) hf hj hk hj hk rfl rfl hF hJ (h₅ f j k hjk)
      I hI vol hvol P hP B₀ hB φ

theorem RestTerm.proof (h : RestTermSharp.Statement) : RestTerm.Statement := by
  refine ⟨1.6, by norm_num, ?_⟩
  intro f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  obtain ⟨hex, hall⟩ := h f j k hf hj hk I hI vol hvol P hP B₀ hB φ
  refine ⟨hex, fun Q hQ => ?_⟩
  obtain ⟨hs, hb⟩ := hall Q hQ
  refine ⟨hs, hb.trans ?_⟩
  have hmin : (1 : ℝ) ≤ ((min j k : ℕ) : ℝ) := by exact_mod_cast le_min hj hk
  have hnn : 0 ≤ (((f * j * k : ℕ) : ℝ) + 1) * vol * |I (degreeInput f j k)| := by positivity
  have := mul_nonneg (sub_nonneg.2 hmin) hnn
  nlinarith

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyCocycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyCocycle.Statement : Prop :=
  ∀ (e : ℕ) (M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → P.PosDef →
    ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M P k =
      ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M N k + ∑ k ∈ Finset.range (e + 1), chartMixedEnergy N P k

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(1 : ℂ), 9] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) ≠
      (Matrix.diagonal ![(1 : ℂ), 9] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num,
    Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one, fun h => by
    have h1 := congrFun (congrFun h 0) 0
    norm_num at h1⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyDiagonal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyDiagonal.Statement : Prop :=
  ∀ (e : ℕ) (l : Fin (e + 1) → ℝ), (∀ j, 0 < l j) →
    ∑ k ∈ Finset.range (e + 1),
        chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) k =
      1 / 2 * (∑ j, Real.log (l j)) * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

example : ∀ j, 0 < (![4, 1] : Fin (1 + 1) → ℝ) j := fun j => by fin_cases j <;> norm_num

example (e : ℕ) (l : Fin (e + 1) → ℝ) (hl : ∀ j, 0 < l j) :
    (Matrix.diagonal fun j => (l j : ℂ)).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by simpa using hl j

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → ∀ k : ℕ,
    Integrable (fun y : Fin e → ℂ => (hermChartPot M y - hermChartPot N y) *
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y)

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) ≠ 1 :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one, fun h => by
    have h1 := congrFun (congrFun h 0) 0
    simp at h1⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartEnergyLinearInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M N C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → C.det ≠ 0 → ∀ k : ℕ,
    chartMixedEnergy (Cᴴ * M * C) (Cᴴ * N * C) k = chartMixedEnergy M N k

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (!![0, 1; 1, 0] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).det ≠ 0 :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one, by
    simp [Matrix.det_fin_two]⟩

end

end GroundTheory.Heights₂.Heights
end

