import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.GaussJetBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixUnitIntegralCombEmbeddedHoms
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.EntryHomComb

open Matrix

variable {p : ℕ} [Fact p.Prime]

theorem det_map_isUnit (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {P : Matrix (Fin N) (Fin N) D.host.E}
    (h : P.det ≠ 0) : IsUnit (P.map ρ).det := by
  have := ρ.map_det P
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact Ne.isUnit ((map_ne_zero ρ).2 h)

theorem coord_le_one (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {P : Matrix (Fin N) (Fin N) D.host.E} (hP : LocBasisW D ρ L P) {x : Fin N → D.host.E} (hx : x ∈ L) (m : Fin N) :
    ‖((P.map ρ)⁻¹ *ᵥ fun i => ρ (x i)) m‖ ≤ 1 := by
  obtain ⟨s, hs, c, hc⟩ := hP.2.2 x hx
  have hs0 : ρ (s : D.host.E) ≠ 0 := by
    intro h; rw [h, norm_zero] at hs; exact zero_ne_one hs
  have e : ∀ i, (s : D.host.E) * x i = ∑ a, (c a : D.host.E) * P i a := fun i => by
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply] at this
    exact this
  have h1 : (fun i => ρ (x i)) = (P.map ρ) *ᵥ fun a => (ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have h2 := congrArg ρ (e i)
    rw [map_mul, map_sum] at h2
    simp only [map_mul] at h2
    calc ρ (x i) = (ρ (s : D.host.E))⁻¹ * (ρ (s : D.host.E) * ρ (x i)) := by field_simp
      _ = _ := by
        rw [h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
  rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (det_map_isUnit D ρ hP.1), Matrix.one_mulVec, norm_mul,
    norm_inv, hs, inv_one, one_mul]
  exact GlobalTheory.JetTieCompare.norm_int_le ρ (c m)

theorem inv_mul_le_one (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B P : Matrix (Fin N) (Fin N) _}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (m b : Fin N) : ‖((P.map ρ)⁻¹ * B) m b‖ ≤ 1 := by
  obtain ⟨n, r, x, hr, hx, hcol⟩ := hB.2.2 b
  have : ((P.map ρ)⁻¹ * B) m b = ∑ k, r k * ((P.map ρ)⁻¹ *ᵥ fun i => ρ (x k i)) m := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hr k) (norm_nonneg _) (coord_le_one D ρ hP (hx k) m)

theorem inv_mul_le_one' (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B : Matrix (Fin N) (Fin N) ℂ_[p]}
    {P : Matrix (Fin N) (Fin N) D.host.E}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (a i : Fin N) : ‖(B⁻¹ * P.map ρ) a i‖ ≤ 1 := by
  obtain ⟨s, hs, hmem⟩ := hP.2.1 i
  have h := hB.2.1 _ hmem a
  rw [hρ] at h
  have e : (fun j => ρ ((s • P.transpose i) j)) = ρ (s : D.host.E) • fun j => ρ (P j i) := by
    funext j
    change ρ ((s : D.host.E) * P j i) = ρ (s : D.host.E) * ρ (P j i)
    rw [map_mul]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hs, one_mul] at h
  convert h using 2
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem entry_comb : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (τ : D.what₂.Tau) (B : Matrix (Fin N) (Fin N) ℂ_[p]) (B' : Matrix (Fin N') (Fin N') ℂ_[p]), GL3Columns.BasR D lm τ L B → GL3Columns.BasR D lm τ L' B' → ∀ (a : Fin N) (b : Fin N'), ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (A : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, A j ∈ homL D L L') ∧ ∀ k l, B' k b * B⁻¹ a l = ∑ j, r j * tauEmb D lm τ (A j k l) := by
  intro D N N' L L' hA p _ lm τ B B' hB hB' a b
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lm τ
  obtain ⟨P, hP⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L hA.2.2.1.1 hA.2.2.1.2.1
  obtain ⟨P', hP'⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L' hA.2.2.2.1 hA.2.2.2.2.1
  choose s hs hsA using fun q : Fin N' × Fin N =>
    GlobalTheory.Proof.DirectionalDerivative.exists_smul_mem_homL D ρ hA.2.2.1.1 hP hP' q.2 q.1
  have hs0 : ∀ q, ρ (s q) ≠ 0 := fun q h => by rw [← norm_eq_zero, hs q] at h; exact one_ne_zero h
  let e := Fintype.equivFin (Fin N' × Fin N)
  have hdet := det_map_isUnit D ρ hP.1
  have hdet' := det_map_isUnit D ρ hP'.1
  have hinv : (P.map ρ)⁻¹ = (P⁻¹).map ρ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hP.1), Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  refine ⟨Fintype.card (Fin N' × Fin N),
    fun j => ((P'.map ρ)⁻¹ * B') (e.symm j).1 b * (B⁻¹ * P.map ρ) a (e.symm j).2 * (ρ (s (e.symm j)))⁻¹,
    fun j => Matrix.of fun k l => s (e.symm j) * (P' k (e.symm j).1 * P⁻¹ (e.symm j).2 l), fun j => ?_,
    fun j => hsA _, fun k l => ?_⟩
  · rw [norm_mul, norm_mul, norm_inv, hs, inv_one, mul_one]
    exact mul_le_one₀ (inv_mul_le_one D ρ hρ hB' hP' _ b) (norm_nonneg _) (inv_mul_le_one' D ρ hρ hB hP a _)
  · have e1 : B' k b = ∑ m, ρ (P' k m) * ((P'.map ρ)⁻¹ * B') m b := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_left (P'.map ρ) B' hdet']
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    have e2 : B⁻¹ a l = ∑ i, (B⁻¹ * P.map ρ) a i * ρ (P⁻¹ i l) := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_right (P.map ρ) B⁻¹ hdet, hinv]
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    rw [e1, e2, Finset.sum_mul_sum, ← Fintype.sum_prod_type', hρ, ← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.of_apply, map_mul]
    field_simp [hs0 (e.symm j)]

end GlobalTheory.EntryHomComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormNatCastCoprime
section
open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetsPairing

noncomputable section

namespace GlobalTheory.UnitaryBases

section General

variable {E : Type} [Field E] [StarRing E] {N : ℕ}

theorem stdH_eq (x y : Fin N → E) : stdH E N x y = star x ⬝ᵥ y := rfl

theorem stdH_mulVec (γ : Matrix.unitaryGroup (Fin N) E) (x y : Fin N → E) :
    stdH E N ((γ : Matrix (Fin N) (Fin N) E).mulVec x) ((γ : Matrix (Fin N) (Fin N) E).mulVec y) = stdH E N x y := by
  have h : (γ : Matrix (Fin N) (Fin N) E).conjTranspose * (γ : Matrix (Fin N) (Fin N) E) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 γ.2
  rw [stdH_eq, stdH_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem mulVec_surjective (γ : Matrix.unitaryGroup (Fin N) E) :
    Function.Surjective (γ : Matrix (Fin N) (Fin N) E).mulVec := by
  intro y
  have h : (γ : Matrix (Fin N) (Fin N) E) * star (γ : Matrix (Fin N) (Fin N) E) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 γ.2
  exact ⟨(star (γ : Matrix (Fin N) (Fin N) E)).mulVec y, by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]⟩

variable [NumberField E]

theorem mem_smulLat (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ SDLat.smulLat γ L ↔ ∃ x ∈ L, γ.mulVec x = y := by
  unfold SDLat.smulLat
  rw [Submodule.mem_map]
  rfl

theorem isSDLat_smulLat (γ : Matrix.unitaryGroup (Fin N) E) {L : Submodule (𝓞 E) (Fin N → E)} (hL : IsSDLat E N L) :
    IsSDLat E N (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L) := by
  obtain ⟨h1, h2, h3⟩ := hL
  refine ⟨h1.map _, ?_, fun y => ?_⟩
  · have e : (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) E) L : Set (Fin N → E)) =
        (Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)) '' (L : Set (Fin N → E)) := rfl
    rw [e, ← Submodule.map_span, h2, Submodule.map_top, LinearMap.range_eq_top]
    exact mulVec_surjective γ
  · obtain ⟨y, rfl⟩ := mulVec_surjective γ y
    constructor
    · intro hy x hx
      obtain ⟨y', hy', e⟩ := (mem_smulLat _ _ _).1 hy
      obtain ⟨x', hx', rfl⟩ := (mem_smulLat _ _ _).1 hx
      rw [← e, stdH_mulVec]
      exact (h3 y').1 hy' x' hx'
    · intro h
      refine (mem_smulLat _ _ _).2 ⟨y, (h3 y).2 fun x hx => ?_, rfl⟩
      rw [← stdH_mulVec γ]
      exact h _ ((mem_smulLat _ _ _).2 ⟨x, hx, rfl⟩)

end General

end GlobalTheory.UnitaryBases
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuDCardLeASq
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem nuD_card_le_a_sq : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) ≤ (Fm.L x i).sc.a ^ 2 := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.nuRow_nonneg_le_ten_mul eps Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  have hr := h1 x (le_trans (le_max_left _ _) hx) hx1 i u (j + 1)
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)
  simp only [Nat.add_sub_cancel] at hr
  obtain ⟨hkN, -, -, -, -, h4, -, -, -, hS⟩ := h2 x (le_trans (le_max_right _ _) hx) hx1 i
  have hsx := Fm.L_x x i hx1
  rw [GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]
  have hsum := Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j))
    (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b)
    (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
    have : (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le
      omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.k)
  have hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := Nat.cast_nonneg _
  have hNk := le_mul_of_one_le_left hN0 hk
  have heta := (Fm.L x i).etaSz_pos
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10 := by linarith
  rw [hsx] at h4
  have hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b := by positivity
  have h5 := mul_le_mul_of_nonneg_right hN hxb
  have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by
    unfold Scale.a
    rw [hsx]
  rw [ha]
  have h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qdStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)), N.l i ∉ H.small → N.l i ≠ H.q → N.l i ≠ H.d → (nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (N.l i) := by
  first | exact @GlobalTheory.bridge_field_le_unramified | exact GlobalTheory.bridge_field_le_unramified | (intros; apply GlobalTheory.bridge_field_le_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.InertCompare

open Formalism.FrobeniusOrbits GlobalTheory.Proof.IdempotentLatticeSequence

theorem ne_of_inert (D : D7) (l : ℕ) (h : IsResidueClassZero D l ∨ IsSg D l) : l ∉ D.host.small ∧ l ≠ D.host.q ∧ l ≠ D.host.d := by
  rcases h with h | h
  · have k := (primeClass_eq_inert_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩
  · have k := (primeClass_eq_signal_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩

theorem primeOf_liesOver {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (ρ : E →+* ℂ_[l]) :
    (primeOf ρ).LiesOver (Ideal.span {(l : ℤ)}) := by
  have := primeOf_isPrime ρ
  refine ⟨(span_prime_isMaximal l Fact.out).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact natCast_mem_primeOf ρ

theorem galE_frob_snd (D : D7) (l : ℕ) [Fact l.Prime] (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (hd : l ≠ D.host.d)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) :
    (D.host.galE σ).2 = D.R.iota (G.hP D l) := by
  have hc : l.Coprime D.host.condN :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).2 (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd)
  have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D l := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
  have e1 := (D.host.toHostAx.frob_iff l hc P σ).1 hσ
  have e2 := (@Formalism.HC.HostAx.frob_iff _ D.host.toHostAx l _ hc P₀ hP₀ hL₀ σ₀).1 hσ₀
  unfold Formalism.MainNotions.G.hP
  rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀]
  exact congrArg Prod.snd (e1.trans e2.symm)

theorem plGG_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) :
    plGG D (posPl D l z 1) = plGG D z * D.host.galE σ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  have hC := factClassFrob D.R D.host l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P σ hσ
  have hH := galE_frob_snd D l h2 hq hd P σ hσ
  have hpl : ∀ z : Bool × HH D, plGG D z = ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
    rintro ⟨b, t⟩
    cases b <;> rfl
  rw [hpl, hpl]
  refine Prod.ext ?_ ?_
  · rcases h with h | h
    · have h1 := hC.2.2.1 h
      have hs : ¬ IsSg D l := fun hs => by
        have := h.symm.trans hs
        cases this
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, partner, hs]
      cases z.1 <;> simp
    · have h1 := hC.2.1.1 h
      have hp : (partner D l z.2 1).1 = true := decide_eq_true ⟨h, odd_one⟩
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, hp]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH, posPl, partner, one_smul]
    rw [Formalism.HC.Frame.iota_add]

theorem exists_frob_step (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] :
    ∃ φ : D.host.E ≃ₐ[ℚ] D.host.E, IsArithFrobAt ℤ φ P ∧ ∀ z : Bool × HH D,
      plGG D (posPl D l z 1) = plGG D z * D.host.galE φ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  obtain ⟨φ, hφ⟩ := (D.host.der.frob l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P).1
  exact ⟨φ, hφ, plGG_posPl_one D l h P φ hφ⟩

theorem embT_tauPl (D : D7) (z : Bool × HH D) : embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold embT tauPl
  rw [Equiv.apply_symm_apply]

theorem emb_mul_galE {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) :
    H.emb (g * H.galE σ) x = H.emb g (σ x) := by
  have he : H.sigmaOf (g * H.galE σ) = H.sigmaOf g * σ := by
    unfold Host.sigmaOf
    rw [map_mul, MulEquiv.symm_apply_apply]
  change H.φ₀ (H.sigmaOf (g * H.galE σ) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem rhoH_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) (x : D.host.E) :
    rhoH D lam (tauPl D (posPl D l z 1)) x = rhoH D lam (tauPl D z) (σ (D.host.conj x)) := by
  rw [rhoH_apply, rhoH_apply, embT_tauPl, embT_tauPl, plGG_posPl_one D l h P σ hσ z,
    ← D.host.galE_conjE, emb_mul_galE, emb_mul_galE]

theorem samePrime_step : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), (IsResidueClassZero D l ∨ IsSg D l) →
    ∀ z : Bool × HH D, SamePrime (rhoH D lam (tauPl D (posPl D l z 1))) (rhoC D lam (tauPl D z)) := by
  intro D l _ lam h z a
  have := primeOf_isPrime (rhoH D lam (tauPl D z))
  have := primeOf_liesOver (rhoH D lam (tauPl D z))
  obtain ⟨φ, hφ, -⟩ := exists_frob_step D l h (primeOf (rhoH D lam (tauPl D z)))
  rw [rhoH_posPl_one D l lam h _ φ hφ]
  have hc := AlgHom.IsArithFrobAt.comap_eq hφ
  have := Ideal.ext_iff.1 hc (D.host.conj • a)
  exact this

end GlobalTheory.InertCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReductionTrivialOnWildInertiaStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_trivial_on_wild_inertia : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.LabTame D.nd D.naut → GlobalTheory.RowTie.RowRepAtG D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  first | exact @GlobalTheory.RowWildTame.main | exact GlobalTheory.RowWildTame.main | (intros; apply GlobalTheory.RowWildTame.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
section
noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.LvT.KerLat

theorem rowGen_diag_monomial_one (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (d : Fin r × Fin n →₀ ℕ) :
    rowGen R a a (monomial d 1) =
      (1 + Polynomial.X) ^ (Finsupp.weight (rowW r n) d a) * Polynomial.C (monomial d 1) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have e : (monomial (f + g) (1 : R) : MvPolynomial (Fin r × Fin n) R) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, hf, hg, map_add, Pi.add_apply, pow_add, map_mul]
    ring
  | single v c =>
    obtain ⟨b, s⟩ := v
    rw [← X_pow_eq_monomial, map_pow, map_pow]
    unfold rowGen
    rw [aeval_X]
    by_cases h : b = a
    · subst h
      have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) b = c := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index]
      rw [e, ← mul_pow]
      simp only [if_true]
      congr 1
      ring
    · have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) a = 0 := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index, Ne.symm h]
      rw [e]
      simp [h]

theorem rowGen_diag_homog (R : Type) [CommRing R] {r n : ℕ} (μ : Fin r → ℕ) (a : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    rowGen R a a f = (1 + Polynomial.X) ^ (μ a) * Polynomial.C f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : (monomial d (coeff d f) : MvPolynomial (Fin r × Fin n) R) = coeff d f • monomial d 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, rowGen_diag_monomial_one, hf (mem_support_iff.mp hd), ← mul_smul_comm,
    Polynomial.smul_C]

theorem rowDiv_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ →
    (∀ (a b : Fin r) (k : ℕ), ∃ μ' : Fin r → ℕ, IsWeightedHomogeneous (rowW r n) (rowDiv R a b k f) μ') ∧
      ∀ (a : Fin r) (k : ℕ), rowDiv R a a k f = ((μ a).choose k) • f := by
  intro R _ r n μ f hf
  refine ⟨fun a b k => ?_, fun a k => ?_⟩
  · have hZ : IsWeightedHomogeneous (rowZ r n) f (fun i => (μ i : ℤ)) := by
      intro d hd
      funext i
      rw [weight_rowZ, hf hd]
    have h := rowDiv_shift R _ a b k f hZ
    refine ⟨fun i => ((((fun i => (μ i : ℤ)) + k • (Pi.single a 1 - Pi.single b 1) : Fin r → ℤ)) i).toNat,
      fun d hd => ?_⟩
    funext i
    rw [← h hd, weight_rowZ, Int.toNat_natCast]
  · unfold rowDiv
    rw [rowGen_diag_homog R μ a f hf, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow, nsmul_eq_mul]

end GlobalTheory.ValCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSubStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_restrict_eq_top_of_absIrrSub_alt : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W), AbsIrrSub ρ W → Submodule.span k (Set.range fun g => (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  first | exact @GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | exact GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | (intros; apply GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdAtServed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

theorem std_at_served : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → 2 * rG L.sc ≤ D.R.k → ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Y.Fl u w hg).t (Y.Fl u w hg).mm (Y.Fl u w hg).c (D.gat u w hg).P.r ((Y.Fl u w hg).TT v) ((Y.Fl u w hg).a v) ((Y.Fl u w hg).b v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) := by
  intro D u w hg L hT X Y hLT hk v
  obtain ⟨hmm, -, -, hr, -⟩ := hLT u w hg
  have hS := (D.gat u w hg).P.setting v
  have hgk := hT.gat_k u w hg
  have hrG : 1 ≤ rG L.sc := Nat.succ_le_succ (Nat.zero_le _)
  have hm2 := D.R.two_le_m
  refine ⟨hg.1, hg.2.1, hS.two_le, hS.even, ?_, ?_, ?_, (Y.Fl u w hg).base v, (D.gat u w hg).P.dom v, ?_, ?_⟩
  · rw [hr]; split_ifs <;> omega
  · rw [hr, hgk]; split_ifs <;> omega
  · rw [hmm]; omega
  · exact fun s => ⟨le_trans (le_max_left _ _) ((Y.Fl u w hg).w_ge v s),
      le_trans (le_max_right _ _) ((Y.Fl u w hg).w_ge v s)⟩
  · exact fun s l hl _ => (Y.Fl u w hg).w_mono v s l hl

end GlobalTheory.TwU
end

