import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IterateFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0103
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegScale
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.NormScale

theorem deg_scale : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N N' : (K →+* ℂ) → V → ℝ) (t : (K →+* ℂ) → ℝ), HasGram N → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ x = t σ * N σ x) → HasGram N' ∧ ∀ L : Submodule (𝓞 K) V, L.FG → deg N' L = deg N L - (Formalism.HN.rkK L : ℝ) * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by
  intro K V _ _ _ _ _ _ _ N N' t hN ht hc hN'
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  set X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun v => ((t v.embedding : ℂ)⁻¹) • X v with hX'
  have htc : ∀ v : InfinitePlace K, (t v.embedding : ℂ) ≠ 0 := fun v => by
    exact_mod_cast (ht v.embedding).ne'
  have hinv : ∀ v, (X' v)⁻¹ = (t v.embedding : ℂ) • (X v)⁻¹ := fun v => by
    refine Matrix.inv_eq_left_inv ?_
    simp only [hX', Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ (hG v).1,
      inv_mul_cancel₀ (htc v), one_smul]
  have hfc : ∀ v x, Formalism.HermitianLatticesTheory.fcoord b X' v x = (t v.embedding : ℂ) • Formalism.HermitianLatticesTheory.fcoord b X v x := fun v x => by
    simp only [Formalism.HermitianLatticesTheory.fcoord, hinv]
    exact Matrix.smul_mulVec _ _ _
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt b X' v x = t v.embedding * Formalism.HermitianLatticesTheory.normAt b X v x := fun v x => by
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, hfc, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ht _)]
  have hG' : IsGram b X' N' := fun v => by
    refine ⟨?_, fun x => by rw [hnorm, (hG v).2, hN']⟩
    simp only [hX', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (inv_ne_zero (htc v)))).mul (hG v).1
  refine ⟨hG'.hasGram, fun L hL => ?_⟩
  have hgram : ∀ v {j : ℕ} (e : Fin j → V), Formalism.HN.gramPl b X' v e = (((t v.embedding) ^ 2 : ℝ) : ℂ) • Formalism.HN.gramPl b X v e := by
    intro v j e
    ext a c
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hfc, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hdet : ∀ v {j : ℕ} (e : Fin j → V), (Formalism.HN.gramPl b X' v e).det.re =
      t v.embedding ^ (2 * j) * (Formalism.HN.gramPl b X v e).det.re := by
    intro v j e
    rw [hgram, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul, ← pow_mul]
  haveI : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj : Formalism.HN.rkK L = Module.finrank K (Submodule.span K (L : Set V)) := rfl
  generalize Module.finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj
  obtain ⟨-, g1, m1⟩ := GlobalTheory.SlopeExt.rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  obtain ⟨-, g2, m2⟩ := GlobalTheory.SlopeExt.rk_mul_mu_eq b X' (fun v => (hG' v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  have hlog : ∀ v, Real.log (Formalism.HN.gramPl b X' v e).det.re =
      (2 * j : ℝ) * Real.log (t v.embedding) + Real.log (Formalism.HN.gramPl b X v e).det.re := fun v => by
    rw [hdet, Real.log_mul (pow_pos (ht _) _).ne' (g1 v).ne', Real.log_pow]
    push_cast; ring
  have hsum : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K (fun v => Real.log (t v.embedding))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]; exact congrArg Real.log (hc σ).symm
  have hfin : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [← NumberField.Embeddings.card K ℂ, this]
    rfl
  have hP : (Formalism.HN.nPl K : ℝ) ≠ 0 := by exact_mod_cast Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero
  rw [Finset.sum_congr rfl (fun v _ => hlog v), Finset.sum_add_distrib, ← Finset.mul_sum] at m2
  simp only [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, slope_sq_eq hG hL, slope_sq_eq hG' hL, hj, hsum, hfin]
  have key : (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X' L) = (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X L)
      - 2 * j * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by linarith
  field_simp
  linear_combination key

end GlobalTheory.NormScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

open TopologicalSpace

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem mem_nonzeroLocus_iff_comb {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} {Ψ : X ⟶ B₀} (hcov : ⨆ i, nonzeroLocus (b i) = ⊤)
    (hG : Generates a φ p c) (hP : Proport a b φ p Ψ c) {z : X} {q : N.ι} (hq : φ z ∈ N.U q) {k : H.ι}
    (hk : Ψ z ∈ H.U k) (i : Fin mB) :
    Ψ z ∈ nonzeroLocus (b i) ↔ IsUnit (comb a φ p c z q i) := by
  obtain ⟨j₀, hj₀⟩ := hG z q hq
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (Ψ z)))
  have u₀ := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i₀) Ψ z hk).1 hi₀
  have e₀ := hP z q k hq hk i₀ j₀
  have ub : IsUnit (gs Ψ z (H.U k) ((b j₀).f k)) := by
    have := u₀.mul hj₀
    rw [e₀] at this
    exact isUnit_of_mul_isUnit_left this
  have e := hP z q k hq hk j₀ i
  rw [GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i) Ψ z hk]
  constructor
  · intro h
    have := h.mul hj₀
    rw [← e] at this
    exact isUnit_of_mul_isUnit_right this
  · intro h
    have := ub.mul h
    rw [e] at this
    exact isUnit_of_mul_isUnit_left this

theorem gs_eval_eq {Rg : Type} [CommRing Rg] {fB : B₀ ⟶ Sp Rg} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H}
    {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)} {Ψ₁ Ψ₂ : X ⟶ B₀}
    (hcov : ⨆ i, nonzeroLocus (b i) = ⊤) (hH : H.IsLB) (hN : N.IsLB) (hG : Generates a φ p c)
    (h₁ : Proport a b φ p Ψ₁ c) (h₂ : Proport a b φ p Ψ₂ c) (e : Ψ₁ ≫ fB = Ψ₂ ≫ fB) {i : Fin mB}
    {r : Fin mB → Γ(B₀, nonzeroLocus (b i))} (hr : ∀ j, GlobalTheory.AmpleSpan.IsRatio (b j) (b i) (r j)) (x : X)
    (m₁ : Ψ₁ x ∈ nonzeroLocus (b i)) (m₂ : Ψ₂ x ∈ nonzeroLocus (b i)) (P : MvPolynomial (Fin mB) Γ(Sp Rg, ⊤)) :
    gs Ψ₁ x _ (MvPolynomial.eval₂Hom (fB.appLE ⊤ (nonzeroLocus (b i)) le_top).hom r P) =
      gs Ψ₂ x _ (MvPolynomial.eval₂Hom (fB.appLE ⊤ (nonzeroLocus (b i)) le_top).hom r P) := by
  obtain ⟨q, hq⟩ := exists_chart hN (φ x)
  have key : ∀ Ψ : X ⟶ B₀, Proport a b φ p Ψ c → Ψ x ∈ nonzeroLocus (b i) → ∀ j,
      gs Ψ x _ (r j) * comb a φ p c x q i = comb a φ p c x q j := fun Ψ hP m j => by
    obtain ⟨k, hk⟩ := exists_chart hH (Ψ x)
    have ub := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i) Ψ x hk).1 m
    have e₁ := hP x q k hq hk j i
    rw [(hr j).gs Ψ x m hk] at e₁
    refine ub.mul_left_cancel ?_
    rw [← e₁]
    ring
  have uc : IsUnit (comb a φ p c x q i) := by
    obtain ⟨k, hk⟩ := exists_chart hH (Ψ₁ x)
    exact (mem_nonzeroLocus_iff_comb hcov hG h₁ hq hk i).1 m₁
  induction P using MvPolynomial.induction_on with
  | C a₀ =>
    rw [MvPolynomial.eval₂Hom_C, GlobalTheory.AmpleSpan.gs_const fB _ Ψ₁ x m₁, GlobalTheory.AmpleSpan.gs_const fB _ Ψ₂ x m₂, e]
  | add P Q hP hQ => rw [map_add, gs_add _ x _ m₁, gs_add _ x _ m₂, hP, hQ]
  | mul_X P j hP =>
    rw [map_mul, gs_mul _ x _ m₁, gs_mul _ x _ m₂, hP, MvPolynomial.eval₂Hom_X']
    exact congrArg _ (uc.mul_right_cancel ((key Ψ₁ h₁ m₁ j).trans (key Ψ₂ h₂ m₂ j).symm))

theorem eq_of_proport : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (Ψ₁ Ψ₂ : X ⟶ B₀), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → GlobalTheory.HomFixUniv.Generates a φ p c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₁ c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₂ c → Ψ₁ ≫ fB = Ψ₂ ≫ fB → Ψ₁ = Ψ₂ := by
  intro Rg _ A₀ B₀ X T fB N H mA mB a b φ p c Ψ₁ Ψ₂ hE hH hN hG h₁ h₂ e
  obtain ⟨hcov, hloc⟩ := hE
  have hW : ⨆ i, Ψ₁ ⁻¹ᵁ nonzeroLocus (b i) = ⊤ := by
    refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (Ψ₁ x)))
    exact ⟨i, hi⟩
  let 𝒰 := X.openCoverOfIsOpenCover (fun i => Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)) hW
  refine 𝒰.hom_ext _ _ fun i => ?_
  obtain ⟨ha, r, hr, hs⟩ := hloc i
  have m₂ : ∀ x, Ψ₁ x ∈ nonzeroLocus (b i) → Ψ₂ x ∈ nonzeroLocus (b i) := fun x hx => by
    obtain ⟨q, hq⟩ := exists_chart hN (φ x)
    obtain ⟨k₁, hk₁⟩ := exists_chart hH (Ψ₁ x)
    obtain ⟨k₂, hk₂⟩ := exists_chart hH (Ψ₂ x)
    exact (mem_nonzeroLocus_iff_comb hcov hG h₂ hq hk₂ i).2 ((mem_nonzeroLocus_iff_comb hcov hG h₁ hq hk₁ i).1 hx)
  change (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι ≫ Ψ₁ = (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι ≫ Ψ₂
  have w₁ : ∀ w : (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).toScheme, Ψ₁ ((Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι w) ∈ nonzeroLocus (b i) :=
    fun w => w.2
  refine GlobalTheory.SecRingIso.hom_ext_affine ha (fun w => w₁ w) (fun w => m₂ _ (w₁ w)) fun f w => ?_
  obtain ⟨P, rfl⟩ := hs f
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp _ Ψ₁ w _ (w₁ w), ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp _ Ψ₂ w _ (m₂ _ (w₁ w))]
  exact congrArg _ (gs_eval_eq hcov hH hN hG h₁ h₂ e hr _ (w₁ w) (m₂ _ (w₁ w)) P)

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleEmbeddingLevel
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open scoped Formalism.Per

namespace GlobalTheory.ConjPeriod.CompatEx

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow (P : LocPrime l) (K : FinExt l) (t : ↥(K0 K) →ₐ[ℚ_[l]] Om l) :
    ∃ j : ℕ, ∀ c : ↥(K0 K), t c = (((⇑(P.PD K).σ)^[j] c : ↥(K0 K)) : Om l) := by
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨emb, hbij, hemb⟩ := GlobalTheory.HWL.Letters.exists_emb_of_fixed (P.PD K).σ (P.PD K).σ_bij
    (GlobalTheory.HWL.Letters.sigma_fixed P K) (K0 K).val
  obtain ⟨i₀, hi₀⟩ := hbij.2 (K0 K).val
  obtain ⟨i₁, hi₁⟩ := hbij.2 t
  have h : ∀ (k : ℕ) (c : ↥(K0 K)), emb i₁ c = emb (i₁ + k) ((⇑(P.PD K).σ)^[k] c) := by
    intro k c
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, Function.iterate_succ_apply', Nat.cast_succ, ← add_assoc, ← hemb (i₁ + k)]
      rfl
  refine ⟨(i₀ - i₁).val, fun c => ?_⟩
  rw [← hi₁, h (i₀ - i₁).val c, ZMod.natCast_zmod_val, add_sub_cancel, hi₀]
  rfl

theorem pow_wA (a : ℕ) [NeZero a] (j : ℕ) (w : Wq l a) :
    (Per.φA l ^ j) (wA l a w) = wA l a ((sigma l a ^ j) w) := by
  refine WittVector.ext fun i => ?_
  rw [RingHom.coe_pow, coeff_iter]
  change (Fq.val l a (w.coeff i)) ^ l ^ j = Fq.val l a (((sigma l a ^ j) w).coeff i)
  rw [coeff_sigma_pow, map_pow]

theorem exists_sigma (P : LocPrime l) (K : FinExt l) (κ : W0 K → ↥(K0 K))
    (hκ : ∀ w, algebraMap ↥(K0 K) ↥K.1 (κ w) = oK K (thetaW (fK K) K w)) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) :
    ∃ j : ℕ, ∀ w : W0 K, ((oK K (thetaW (fK K) K ((sigma l (fK K) ^ j) w)) : ↥K.1) : Om l) =
      s (oK K (thetaW (fK K) K w)) := by
  obtain ⟨j, hj⟩ := exists_pow P K (s.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))
  refine ⟨j, fun w => ?_⟩
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l (fK K) → Wq l (fK K))) :=
    span_teich l (fK K) ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    rcases eq_or_ne x 0 with rfl | h0
    · simp only [WittVector.teichmuller_zero, map_zero, ZeroMemClass.coe_zero]
    · have h1 := one_lt_pow_l l (fK K)
      have hd : ¬ l ∣ l ^ fK K - 1 := fun hd =>
        hl.out.not_dvd_one ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne _))).1 hd)
      have h2 : x ^ (l ^ fK K - 1) = 1 := mul_right_cancel₀ h0 (by
        rw [← pow_succ, Nat.sub_add_cancel h1.le, one_mul]
        exact Fq.pow_card x)
      have h3 : κ (WittVector.teichmuller l x) ^ (l ^ fK K - 1) = 1 :=
        (algebraMap ↥(K0 K) ↥K.1).injective (by
          rw [map_pow, hκ, ← map_pow, ← map_pow, ← map_pow, h2, map_one, map_one, map_one, map_one])
      have h4 := GlobalTheory.FrobOrder.iterate_of_pow (P.PD K).σ _ l
        (GlobalTheory.FrobOrder.sigma_root P K _ (by omega) hd h3) j
      have h5 := hj (κ (WittVector.teichmuller l x))
      rw [h4] at h5
      rw [sigma_pow_teich, map_pow, map_pow, ← hκ]
      exact h5.symm
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]
  | add x y _ _ hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]
  | smul c x _ hx =>
    have hc : oK K (algebraMap ℤ_[l] ↥(OL K) c) = algebraMap ℚ_[l] ↥K.1 (c : ℚ_[l]) := rfl
    rw [Algebra.smul_def, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, AlgEquiv.commutes,
      AlgHom.commutes, hc, AlgHom.commutes, MulMemClass.coe_mul, hx]
    rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (s : ↥K.1 →ₐ[ℚ_[l]] Om l), ∃ j : ℕ, Compat T K j s := by
  intro l _ P AI T K s
  choose κ hκ hκ' using GlobalTheory.PZ.PeriodVector.exists_unram T K
  obtain ⟨j, hj⟩ := exists_sigma P K κ hκ s
  refine ⟨j, fun w => ?_⟩
  have h1 : ∀ c : ↥(K0 K), P.ιB (algebraMap ↥(K0 K) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := fun c => by
    rw [← P.PD_ι K, AlgHom.commutes]
    rfl
  change P.ιB (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l)
    ((GlobalTheory.MemLoc.phiA l ^ j) (aC l (wA l (fK K) w))))) = _
  rw [phiA_pow_aC, pow_wA, ← hj, ← hκ]
  have h2 : ∀ a : Per.Ainf l, algebraMap (Per.Acris l) (Per.Bcris l) (aC l a) = Per.aB l a :=
    fun a => (GlobalTheory.RingIface.aB_eq_alg l a).symm
  rw [h2, ← hκ', RingEquiv.symm_apply_apply, h1]
  rfl

end GlobalTheory.ConjPeriod.CompatEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrAlgClosureOverFiniteDvrExtension
section
open IsLocalRing

namespace GlobalTheory

theorem exists_dvr_over_finite_ext : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr V → GlobalTheory.LN.CDvr W → ∀ io : V →+* W, io.Finite → Function.Injective io → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∃ N : ℕ, ∀ (T' : Subring F) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v, (f v : F) = algebraMap (FractionRing V) F (algebraMap V _ v)) → (∀ π, Irreducible π → Irreducible (f π)) → ∃ (T'' : Subring F) (_ : IsDiscreteValuationRing T'') (g : W →+* T'') (e : ℕ), T' ≤ T'' ∧ (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ ∀ π, Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ Associated (g π) (ϖ ^ e) := by
  classical
  intro V W _ _ _ _ _ _ hV hW io hio hinj F _ _ _ _ hcomp
  obtain ⟨hVd, -, hV0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨hWd, -, -⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  set φV : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V _) with hφV
  set φW : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hφW
  have hφWinj : Function.Injective φW :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  have hφVinj : Function.Injective φV :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  haveI : CharZero F := (RingHom.charZero_iff hφVinj).1 hV0
  have hc : ∀ v, φW (io v) = φV v := hcomp
  letI := io.toAlgebra
  haveI : Module.Finite V W := hio
  obtain ⟨n, gens, hspan⟩ := Module.Finite.exists_fin (R := V) (M := W)
  refine ⟨n, ?_⟩
  intro T' hT' f hf hirr
  set s : Finset F := Finset.univ.image (fun i => φW (gens i)) with hs
  have hcard : s.card ≤ n := by
    calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have K1 : ∀ w : W, φW w ∈ Submodule.span T' (s : Set F) := by
    intro w
    have hw : w ∈ Submodule.span V (Set.range gens) := by rw [hspan]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span (by simp [hs])
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul v x _ hx =>
      have : φW (v • x) = (f v) • φW x := by
        rw [Algebra.smul_def, map_mul, Subring.smul_def, smul_eq_mul, hf]
        exact congrArg (· * φW x) (hc v)
      rw [this]; exact Submodule.smul_mem _ _ hx
  have h1 : (1 : F) ∈ Submodule.span T' (s : Set F) := by simpa using K1 1
  have hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F) := by
    intro x hx y hy
    simp only [hs, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
    rw [← map_mul]; exact K1 _
  obtain ⟨T'', hT'', hle, hsT, hdom, hden⟩ := GlobalTheory.T.exists_dominating_dvr_containing_finset F T' hT' s h1 hmul
  have K2 : ∀ x ∈ Submodule.span T' (s : Set F), x ∈ T'' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hsT x hx
    | zero => exact T''.zero_mem
    | add x y _ _ hx hy => exact T''.add_mem hx hy
    | smul t x _ hx => rw [Subring.smul_def, smul_eq_mul]; exact T''.mul_mem (hle t.2) hx
  let g : W →+* T'' := φW.codRestrict T'' (fun w => K2 _ (K1 w))
  have hg : ∀ w, (g w : F) = φW w := fun w => rfl
  have hginj : Function.Injective g := fun a b h => hφWinj (by simpa [hg] using congrArg Subtype.val h)
  haveI := hT''
  obtain ⟨πV, hπV⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfπ := hirr πV hπV
  obtain ⟨ϖ, hϖ, e', he1, he2, hassoc⟩ := GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span F T' T'' hT' hT'' hle hdom s hden (f πV) hfπ
  obtain ⟨πW, hπW⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hioπ : io πV ≠ 0 := fun h => hπV.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_pow_irreducible hioπ hπW
  have hgπ : g πW ≠ 0 := fun h => hπW.ne_zero (hginj (by rw [h, map_zero]))
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hgπ hϖ
  have hgio : g (io πV) = Subring.inclusion hle (f πV) := by
    apply Subtype.ext
    rw [hg, hc]
    exact (hf πV).symm
  have hA : Associated (ϖ ^ e') (ϖ ^ (k * a)) := by
    have h2 : Associated (g (io πV)) ((g πW) ^ a) := by
      rw [← map_pow]; exact ha.map g
    rw [hgio] at h2
    rw [pow_mul]
    exact hassoc.symm.trans (h2.trans hk.pow_pow)
  have hka : e' = k * a := by
    apply le_antisymm
    · exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.dvd
    · exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.symm.dvd
  have hk0 : k ≠ 0 := by rintro rfl; simp at hka; omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at hka; omega
  refine ⟨T'', hT'', g, k, hle, fun w => rfl, Nat.one_le_iff_ne_zero.2 hk0, ?_, ?_⟩
  · calc k ≤ k * a := Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero ha0)
      _ = e' := hka.symm
      _ ≤ s.card := he2
      _ ≤ n := hcard
  · intro π hπ
    exact ⟨ϖ, hϖ, ((IsDiscreteValuationRing.associated_of_irreducible W hπ hπW).map g).trans hk⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisStableTorsionFamilyKer
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mulStable_intCast_add_sub (L : PeriodPair) (s : ℂ) (a : ℤ) (h : MulStable L s) :
    MulStable L (a + s) ∧ MulStable L (a - s) := by
  have ha : ∀ ω ∈ L.lattice, (a : ℂ) * ω ∈ L.lattice := fun ω hω => by
    have := L.lattice.smul_mem a hω
    rwa [zsmul_eq_mul] at this
  refine ⟨fun ω hω => ?_, fun ω hω => ?_⟩
  · rw [add_mul]; exact add_mem (ha ω hω) (h ω hω)
  · rw [sub_mul]; exact sub_mem (ha ω hω) (h ω hω)

theorem normSq_natCast_add_sub_sqrtNegNat (p a : ℕ) :
    Complex.normSq (((a : ℤ) : ℂ) + sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) ∧
      Complex.normSq (((a : ℤ) : ℂ) - sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) := by
  have h : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  constructor <;> simp [sqrtNegNat, Complex.normSq_apply, h, sq]

theorem exists_stable_family_ker : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ, ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (T : ι → ℂ), Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 ∧ Fintype.card ι = 2 * (N - 1) ∧ Stable L F T ∧ ∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice := by
  intro p F L t hp _ h3 hD V
  obtain ⟨a, N, hN, hodd, hmod, hv⟩ := GlobalTheory.T.exists_sq_add_prime_odd_mod_three_valuation_one p V hp h3
  obtain ⟨hs, hs'⟩ := mulStable_intCast_add_sub L (sqrtNegNat p) (a : ℤ) hD.mul
  obtain ⟨hn, hn'⟩ := normSq_natCast_add_sub_sqrtNegNat p a
  rw [← hN] at hn hn'
  have hN0 : (N : ℝ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have h0 : ((a : ℤ) : ℂ) + sqrtNegNat p ≠ 0 := fun h => hN0 (by rw [← hn, h, map_zero])
  have h0' : ((a : ℤ) : ℂ) - sqrtNegNat p ≠ 0 := fun h => hN0 (by rw [← hn', h, map_zero])
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hs
  obtain ⟨S', hS'⟩ := kerRepsExist L _ h0' hs'
  have hc := kerRepsCard L _ S h0 hs hS
  have hc' := kerRepsCard L _ S' h0' hs' hS'
  rw [hn] at hc
  rw [hn'] at hc'
  have hc1 : S.card + 1 = N := by exact_mod_cast hc
  have hc1' : S'.card + 1 = N := by exact_mod_cast hc'
  have hfac : (N : ℂ) = (((a : ℤ) : ℂ) - sqrtNegNat p) * (((a : ℤ) : ℂ) + sqrtNegNat p) := by
    have := sqrtNegNat_sq p
    rw [hN]; push_cast
    linear_combination this
  refine ⟨N, S ⊕ S', inferInstance, Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ)), hodd, hmod, hv,
    ?_, GlobalTheory.T.stable_sum_elim_of_isKerReps_add_sub_sqrtNegNat p F L a S S' hD.g₂_mem hD.g₃_mem hD.mul hS hS', ?_⟩
  · rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]; omega
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · refine ⟨(hS.1 x hx).2, ?_⟩
      show (N : ℂ) * x ∈ _
      rw [hfac, mul_assoc]
      exact hs' _ (hS.1 x hx).1
    · refine ⟨(hS'.1 x hx).2, ?_⟩
      show (N : ℂ) * x ∈ _
      rw [hfac, mul_comm (_ - _), mul_assoc]
      exact hs _ (hS'.1 x hx).1

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogRedStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiLog_red_coboundary_and_linear : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ quasiLog p h, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w := by
  first | exact @GlobalTheory.Katz.exists_quasiLog_red | exact GlobalTheory.Katz.exists_quasiLog_red | (intros; apply GlobalTheory.Katz.exists_quasiLog_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRapidSuperpositionCharacters
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

theorem exists_rapid_superposition_characters :
    ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (Φ : Z → ℂ), ContDiff ℝ ∞ Φ → HasCompactSupport Φ → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (κ : X → ℂ) (τ : X → Z →L[ℝ] ℝ), Measurable κ ∧ (∀ z, Measurable fun x => τ x z) ∧ (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) ∧ ∀ z, Φ z = ∫ x, κ x * (𝐞 (τ x z) : ℂ) ∂ν := by
  intro Z _ _ _ Φ hΦ hc
  obtain ⟨m, A, φ, hφ, hint, hinv⟩ := GlobalTheory.fourier_inversion_real_linear_forms (hc.toSchwartzMap hΦ)
  let B : EuclideanSpace ℝ (Fin m) →L[ℝ] (Z →L[ℝ] ℝ) := (2 * Real.pi)⁻¹ • A
  have hB : ∀ w z, 2 * Real.pi * B w z = A w z := by
    intro w z
    have : (2 * Real.pi) ≠ 0 := by positivity
    simp only [B, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  refine ⟨EuclideanSpace ℝ (Fin m), inferInstance, volume, inferInstance, φ, fun w => B w,
    hφ.measurable, fun z => ?_, fun N => ?_, fun z => ?_⟩
  · exact (by fun_prop : Continuous fun x => B x z).measurable
  · refine ((hint N).const_mul ((1 + ‖B‖) ^ N)).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact (by fun_prop : Continuous fun x => ‖φ x‖ * (1 + ‖B x‖) ^ N).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc, ← mul_pow, mul_comm]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ N) (norm_nonneg _)
      have h1 := B.le_opNorm w
      nlinarith [norm_nonneg B, norm_nonneg w]
  · have h := hinv z
    have h0 : (hc.toSchwartzMap hΦ) z = Φ z := rfl
    rw [h0] at h
    rw [h]
    congr 1
    ext w
    rw [Real.fourierChar_apply, hB]

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsLieStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isLie_of_isFrame_of_QL : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  first | exact @GlobalTheory.QLog.Chart.existsUnique_isLie | exact GlobalTheory.QLog.Chart.existsUnique_isLie | (intros; apply GlobalTheory.QLog.Chart.existsUnique_isLie <;> assumption)
end

