import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCuspFormTransvectionConstantTermsZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLe
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem abs_factorial_mul_chi_twist_lbPow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hproj d F _ hsupp L hL
  have hv : DiffVanish (d + 1) (chiPic k F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hproj hsupp
  obtain ⟨p, hpdeg, hpeval, hpcoeff⟩ := hv.exists_polynomial_int ℚ (cls L hL) 0
  obtain ⟨C, hC⟩ := abs_factorial_mul_eval_sub_top_le d p hpdeg
  refine ⟨C, fun m => ?_⟩
  have hmd : multiDiff (fun _ : Fin d => cls L hL) (chiPic k F) 0 =
      interNum k F (fun _ : Fin d => L) :=
    hv.multiDiff_chiPic (L := fun _ : Fin d => L) (by simp) (fun _ => hL) 0
  have hchi : chi k (twist F (lbPow L m)) = chiPic k F ((m : ℤ) • cls L hL) := by
    rw [← twistZ_natCast]
    exact chi_twistZ k F hL (m : ℤ)
  have heval : p.eval (m : ℚ) = (chi k (twist F (lbPow L m)) : ℚ) := by
    have e := hpeval (m : ℤ)
    rw [zero_add, ← hchi, Int.cast_natCast] at e
    exact e
  have hfac : (d.factorial : ℚ) * p.coeff d = (interNum k F (fun _ : Fin d => L) : ℚ) := by
    rw [hpcoeff, hmd, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]
  have h := hC m
  rw [heval, hfac] at h
  have h' : ((|(d.factorial : ℤ) * chi k (twist F (lbPow L m)) -
      interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
      ((C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) : ℚ) := by
    push_cast
    exact h
  exact_mod_cast h'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasesBlockTriangularOfReducedEtaleFiltrat
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ExpFrame PowerSeries Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachBlock

theorem finrank_sup_span_singleton_of_not_mem : ∀ (K : Type) [Field K] (n : ℕ) (W : Submodule K (Fin n → K)) (x : Fin n → K), x ∉ W → Module.finrank K ↥(W ⊔ Submodule.span K {x}) = Module.finrank K W + 1 := by
  intro K _ n W x hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ W.zero_mem)
  have hinf : W ⊓ Submodule.span K {x} = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzW, hzs⟩ := Submodule.mem_inf.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hzs
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using W.smul_mem c⁻¹ hzW) hx
  have := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span K {x})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0] at this
  exact this

theorem laurent_eq_unit_mul_X_zpow : ∀ (F : Type) [Field F] (x : LaurentSeries F), x ≠ 0 → ∃ (w : (PowerSeries F)ˣ) (k : ℤ), x = ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k := by
  intro F _ x hx
  have hsingle : ∀ k : ℤ, (HahnSeries.single k (1 : F) : LaurentSeries F) = ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
    · rw [zpow_natCast, ← map_pow, HahnSeries.ofPowerSeries_X_pow]
      try simp
    · rw [zpow_neg, zpow_natCast, ← map_pow, HahnSeries.ofPowerSeries_X_pow]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [HahnSeries.single_mul_single]
      simp
  have hunit : IsUnit x.powerSeriesPart := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero]
    exact isUnit_iff_ne_zero.2 (fun h => hx (HahnSeries.coeff_order_eq_zero.1 h))
  refine ⟨hunit.unit, x.order, ?_⟩
  rw [IsUnit.unit_spec, ← hsingle, mul_comm]
  exact (LaurentSeries.single_order_mul_powerSeriesPart x).symm

theorem sub_coord_smul_col_mem : ∀ (F : Type) [Field F] (n : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (z : Fin n → PowerSeries F) (p : Fin n), (∀ a : Fin n, a ≠ p → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec z) a ≠ 0 → (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c a : PowerSeries F) : LaurentSeries F)) ∈ U) → (fun c => ((z c : PowerSeries F) : LaurentSeries F)) - (((((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec z) p : PowerSeries F) : LaurentSeries F) • (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c p : PowerSeries F) : LaurentSeries F)) ∈ U := by
  intro F _ n U g z p h
  set v := (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F))).mulVec z with hv
  have hz : z = (g : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec v := by
    rw [hv, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hsum : (fun c => ((z c : PowerSeries F) : LaurentSeries F)) =
      ∑ a, ((v a : PowerSeries F) : LaurentSeries F) • (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c a : PowerSeries F) : LaurentSeries F)) := by
    funext c
    conv_lhs => rw [hz]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, map_sum, mul_comm]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ p), add_sub_cancel_left]
  refine U.sum_mem fun a ha => ?_
  by_cases h0 : v a = 0
  · simp [h0]
  · exact U.smul_mem _ (h a (Finset.ne_of_mem_erase ha) h0)

theorem adapted_bases_of_redFilt : ∀ (ι : Type) (σ : Equiv.Perm ι) (l n t : ℕ) (F : Type) [Field F] (un : PowerSeries F) (P D : ι → Matrix (Fin n) (Fin n) (PowerSeries F)) (Pψ Dψ : Fin t → ι → PowerSeries F), 0 < l → Nonempty ι → GlobalTheory.WachBlock.RedFilt σ l un P D Pψ Dψ → ∃ (g : ι → (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (b : Fin n → ℕ) (pos : Fin t → Fin n) (w : ι → Fin t → (PowerSeries F)ˣ) (kap : ι → Fin t → ℤ), (Function.Injective pos ∧ ∀ s j, b j = b (pos s) → j = pos s) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * kap (σ i) s) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ kap i s * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) := by
  intro ι σ l n t F _ un P D Pψ Dψ hl hne hR
  classical
  obtain ⟨R, V, rs, e, m, hrs, hV, hdim, hphi, hgam, hline, hrelP, hrelG⟩ := hR
  obtain ⟨i0⟩ := hne
  let K := LaurentSeries F
  let d : Fin (R + 1) → ℕ := fun k => Module.finrank K (V i0 k)
  have hdi : ∀ i k, Module.finrank K (V i k) = d k := fun i k => hdim k i i0
  have hdmono : Monotone d := fun a b hab => Submodule.finrank_mono ((hV i0).2.2 hab)
  have hdlast : d (Fin.last R) = n := by
    show Module.finrank K (V i0 (Fin.last R)) = n
    rw [(hV i0).2.1, finrank_top, Module.finrank_fin_fun]
  have hdle : ∀ k, d k ≤ n := fun k => hdlast ▸ hdmono (Fin.le_last k)

  choose g hg using fun i => GlobalTheory.T.exists_unit_matrix_adapted_to_flag F n R (V i) (hV i).2.2
  have hg' : ∀ i k (j : Fin n), (j : ℕ) < d k → lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a j) ∈ V i k :=
    fun i k j hj => hg i k j (by rw [hdi]; exact hj)

  have hex : ∀ j : Fin n, ∃ k, ∃ h : k < R + 1, (j : ℕ) < d ⟨k, h⟩ :=
    fun j => ⟨R, Nat.lt_succ_self R, by have := hdlast; simp only [Fin.last] at this; rw [this]; exact j.2⟩
  let b : Fin n → ℕ := fun j => Nat.find (hex j)
  have hbR : ∀ j, b j < R + 1 := fun j => (Nat.find_spec (hex j)).1
  have hb : ∀ (j : Fin n) (k : Fin (R + 1)), (j : ℕ) < d k ↔ b j ≤ (k : ℕ) := by
    intro j k
    constructor
    · intro h
      exact Nat.find_min' (hex j) ⟨k.2, h⟩
    · intro h
      obtain ⟨h1, h2⟩ := Nat.find_spec (hex j)
      exact lt_of_lt_of_le h2 (hdmono (show (⟨b j, h1⟩ : Fin (R + 1)) ≤ k from h))

  have hentP : ∀ i (a j : Fin n), Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) a j =
      (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
        (phiV l (P i) (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c j)) a := by
    intro i a j
    simp only [Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi, phiV, Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hentG : ∀ i (a j : Fin n), Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) a j =
      (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
        (gamV un (D i) (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c j)) a := by
    intro i a j
    simp only [Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam, gamV, Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hbtP : ∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b := by
    intro i a j hlt
    rw [hentP]
    have hmem := hphi i ⟨b j, hbR j⟩ _ (hg' (σ i) ⟨b j, hbR j⟩ j ((hb j _).2 le_rfl))
    refine GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i ⟨b j, hbR j⟩) (g i) (fun j' hj' => hg i _ j' hj') _ hmem a ?_
    rw [hdi]
    exact Nat.le_of_not_lt (fun h => absurd ((hb a _).1 h) (Nat.not_le.2 hlt))
  have hbtG : ∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b := by
    intro i a j hlt
    rw [hentG]
    have hmem := hgam i ⟨b j, hbR j⟩ _ (hg' i ⟨b j, hbR j⟩ j ((hb j _).2 le_rfl))
    refine GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i ⟨b j, hbR j⟩) (g i) (fun j' hj' => hg i _ j' hj') _ hmem a ?_
    rw [hdi]
    exact Nat.le_of_not_lt (fun h => absurd ((hb a _).1 h) (Nat.not_le.2 hlt))

  have hstep : ∀ s, d (rs s).succ = d (rs s).castSucc + 1 := by
    intro s
    show Module.finrank K (V i0 (rs s).succ) = Module.finrank K (V i0 (rs s).castSucc) + 1
    rw [(hline i0 s).2]
    exact finrank_sup_span_singleton_of_not_mem K n _ _ (hline i0 s).1
  let pos : Fin t → Fin n := fun s => ⟨d (rs s).castSucc, by have := hstep s; have := hdle (rs s).succ; omega⟩
  have hpos_lt : ∀ s, (pos s : ℕ) < d (rs s).succ := fun s => by simp only [pos]; rw [hstep]; omega
  have hpos_nlt : ∀ s, ¬ (pos s : ℕ) < d (rs s).castSucc := fun s => by simp [pos]
  have hsing : ∀ s j, b j = b (pos s) → j = pos s := by
    intro s j h
    have h1 : (j : ℕ) < d (rs s).succ := (hb j _).2 (h ▸ (hb (pos s) _).1 (hpos_lt s))
    have h2 : ¬ (j : ℕ) < d (rs s).castSucc := fun hj => hpos_nlt s ((hb (pos s) _).2 (h ▸ (hb j _).1 hj))
    rw [hstep] at h1
    ext
    simp only [pos]
    omega
  have hbpos : ∀ s, b (pos s) = (rs s : ℕ) + 1 := by
    intro s
    have h1 := (hb (pos s) _).1 (hpos_lt s)
    have h2 : ¬ b (pos s) ≤ ((rs s).castSucc : ℕ) := fun h => hpos_nlt s ((hb (pos s) _).2 h)
    simp only [Fin.val_succ, Fin.coe_castSucc] at h1 h2
    omega
  have hinj : Function.Injective pos := by
    intro s s' h
    have h' : b (pos s) = b (pos s') := by rw [h]
    rw [hbpos, hbpos] at h'
    exact hrs (Fin.ext (by omega))

  have hcoef : ∀ i s, ∃ c : K, c ≠ 0 ∧ lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) - c • lau (e i s) ∈
      V i (rs s).castSucc := by
    intro i s
    have hmem := hg' i (rs s).succ (pos s) (hpos_lt s)
    rw [(hline i s).2, Submodule.mem_sup] at hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      rw [zero_smul, add_zero] at hyz
      have h0 := GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i (rs s).castSucc) (g i) (fun j' hj' => hg i _ j' hj') _ (hyz ▸ hy) (pos s)
        (by rw [hdi] <;> exact Nat.le_of_not_lt (hpos_nlt s))
      have h1 : (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
          (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) (pos s) = 1 := by
        have := congrFun (congrFun (Units.inv_mul (g i)) (pos s)) (pos s)
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
      rw [h1] at h0
      exact one_ne_zero h0
    · rw [← hyz, add_sub_cancel_right]
      exact hy
  choose c hc0 hc using hcoef
  choose w k hwk using fun i s => laurent_eq_unit_mul_X_zpow F (c i s) (hc0 i s)
  have hc' : ∀ i s, lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) -
      (((w i s : F⟦X⟧) : K) * ((X : F⟦X⟧) : K) ^ k i s) • lau (e i s) ∈ V i (rs s).castSucc :=
    fun i s => hwk i s ▸ hc i s
  have hcoe : ∀ p : F⟦X⟧, p ≠ 0 → ((p : F⟦X⟧) : K) ≠ 0 := fun p hp h =>
    hp (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  have hX : ((X : F⟦X⟧) : K) ≠ 0 := hcoe _ X_ne_zero
  have hlow : ∀ s (a : Fin n), a ≠ pos s → ¬ b (pos s) < b a → (a : ℕ) < d (rs s).castSucc := by
    intro s a ha hlt
    refine (hb a _).2 ?_
    have h1 : b a ≠ b (pos s) := fun h => ha (hsing s a h)
    have h2 := hbpos s
    simp only [Fin.coe_castSucc]
    omega

  let θF : F⟦X⟧ →+* F⟦X⟧ := (PowerSeries.substAlgHom (PowerSeries.HasSubst.X_pow (R := F) hl.ne')).toRingHom
  have hθF : ∀ y, θF y = frob0 l y := fun y => by simp [θF, frob0, PowerSeries.coe_substAlgHom]
  have hθFX : θF X = X ^ l := by
    rw [hθF, frob0, PowerSeries.subst_X (PowerSeries.HasSubst.X_pow hl.ne')]
  have hrelF : ∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * (k (σ i) s + m (σ i) s)) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) := by
    intro i s
    have hdP := sub_coord_smul_col_mem F n (V i (rs s).castSucc) (g i) (phiV l (P i) (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s))) (pos s)
      (fun a ha hne => hg' i _ a (hlow s a ha (fun h => hne (by rw [← hentP]; exact hbtP i h))))
    rw [← hentP] at hdP
    have hθFe : ⇑θF = frob0 l := funext hθF
    have key := GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt F n θF (P i) (V (σ i) (rs s).castSucc) (V i (rs s).castSucc)
      (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e (σ i) s)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (w (σ i) s) (w i s) (k (σ i) s) (k i s) (m i s) (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s))
      (((X : F⟦X⟧) : K) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i : F⟦X⟧) : K))
      (by rw [hθFX]; exact hcoe _ (pow_ne_zero _ X_ne_zero))
      (fun y hy => by rw [hθFe]; exact hphi i _ y hy) (hc' (σ i) s) (hc' i s) (hline i s).1
      (by rw [hθFe]; exact hdP) (by rw [hθFe]; exact hrelP i s)
    rw [hθFX, hθF] at key
    simp only [map_pow] at key
    rw [mul_add, zpow_add₀ hX, zpow_add₀ hX, zpow_mul, zpow_natCast]
    linear_combination key

  have hgs : (gamSer 0 un : F⟦X⟧) ≠ 0 := by
    refine mul_ne_zero X_ne_zero (fun h => ?_)
    have := congrArg PowerSeries.constantCoeff h
    simp at this
  have hgc : MvPowerSeries.constantCoeff (gamSer 0 un : F⟦X⟧) = 0 := by
    show PowerSeries.constantCoeff (gamSer 0 un : F⟦X⟧) = 0
    simp [gamSer]
  let θG : F⟦X⟧ →+* F⟦X⟧ := (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hgc)).toRingHom
  have hθG : ∀ y, θG y = gam0 0 un y := fun y => by simp [θG, gam0, PowerSeries.coe_substAlgHom]
  have hθGX : θG X = gamSer 0 un := by
    rw [hθG, gam0, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hgc)]
  have hrelΓ : ∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) := by
    intro i s
    have hdG := sub_coord_smul_col_mem F n (V i (rs s).castSucc) (g i) (gamV un (D i) (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s))) (pos s)
      (fun a ha hne => hg' i _ a (hlow s a ha (fun h => hne (by rw [← hentG]; exact hbtG i h))))
    rw [← hentG] at hdG
    have hθGe : ⇑θG = gam0 0 un := funext hθG
    have key := GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt F n θG (1 + (X : F⟦X⟧) • D i) (V i (rs s).castSucc) (V i (rs s).castSucc)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (w i s) (w i s) (k i s) (k i s) (m i s) (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s))
      (((gamSer 0 un : F⟦X⟧) : K) ^ m i s * ((1 + X * Dψ s i : F⟦X⟧) : K))
      (by rw [hθGX]; exact hcoe _ hgs)
      (fun y hy => by rw [hθGe]; exact hgam i _ y hy) (hc' i s) (hc' i s) (hline i s).1
      (by rw [hθGe]; exact hdG) (by rw [hθGe]; exact hrelG i s)
    rw [hθGX, hθG] at key
    rw [zpow_add₀ (hcoe _ hgs), zpow_add₀ hX]
    linear_combination key
  exact ⟨g, b, pos, w, fun i s => k i s + m i s, ⟨hinj, hsing⟩, hbtP, hbtG, hrelF, hrelΓ⟩

end GlobalTheory.WachBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPointStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedFrame_eventually_near_complexPoint : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  first | exact @GlobalTheory.GoodTop.frame_eventually | exact GlobalTheory.GoodTop.frame_eventually | (intros; apply GlobalTheory.GoodTop.frame_eventually <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory

theorem addGroupFG_sec_of_isArithVar : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ B : LB X, B.IsLB → AddGroup.FG B.Sec := by
  intro k _ X _ p D h B hB
  letI : Algebra k Γ(X, ⊤) :=
    ((Scheme.Hom.appTop p).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  have hf : ∀ r : k, algebraMap k Γ(X, ⊤) r =
      (Scheme.Hom.appTop p) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) := fun _ => rfl
  haveI := h.finite
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hfin : Module.Finite k (coh (twist (QCoh.structureModule X) B) 0) :=
    finite_coh_twist_of_isProjOver hf (QCoh.structureModule X) h.isProjOver hB 0
  haveI : Module.Finite ℤ (coh (twist (QCoh.structureModule X) B) 0) := Module.Finite.trans k _
  have hfg : AddGroup.FG (coh (twist (QCoh.structureModule X) B) 0) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact AddGroup.fg_of_surjective (f := (cohZeroTwistEquiv B).toAddEquiv.toAddMonoidHom)
    (cohZeroTwistEquiv B).toAddEquiv.surjective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCuspFormTransvectionConstantTermsZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCuspForm_transvection_constantTerms_zero : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, IsHolCusp X la P → ZCusp V (adel V dict (muPin V dict mu c) P) := by
  first | exact @GlobalTheory.HolDict.TransvCusp.zCusp_adel | exact GlobalTheory.HolDict.TransvCusp.zCusp_adel | (intros; apply GlobalTheory.HolDict.TransvCusp.zCusp_adel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHomActionRealCoordinatesEq
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem actOF_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (g : GAF σ JS) (h : GAF σ JT) (v : IxF F nS nT → ℂ),
        actOF σ JS JT g h (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ θ _ ι hι g h v
  have hfin : ∀ u : IxF F nS nT → ℂ, (iotaVF ι u).map (finPartF F E) = 0 := fun u => real_iotaVF hι u
  have hL : (actOF σ JS JT g h (iotaVF ι v)).map (finPartF F E) = 0 := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hfin, Matrix.mul_zero, Matrix.zero_mul]
  have hcpt : ∀ (u : IxF F nS nT → ℂ) w, compAtF θ w (iotaVF ι u) = GlobalTheory.RealWeil.cpt u w := by
    intro u w
    ext i j
    exact hι.comp _ w
  have hC : ∀ w, compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
      compAtF θ w (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v)) := by
    intro w
    have e : compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
        compAtF θ w (mtF σ JT h) * compAtF θ w (iotaVF ι v) * compAtF θ w (mtF σ JS g⁻¹) := by
      unfold actOF compAtF
      rw [Matrix.map_mul, Matrix.map_mul]
    rw [e, hcpt, hcpt, mMF_apply, GlobalTheory.RealWeil.cpt_blk]
  ext i j
  rw [← sub_eq_zero]
  refine hι.ext _ ?_ fun w => ?_
  · have h1 : finPartF F E (actOF σ JS JT g h (iotaVF ι v) i j) = 0 := congrFun (congrFun hL i) j
    have h2 : finPartF F E (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) i j) = 0 := congrFun (congrFun (hfin _) i) j
    rw [RingHom.map_sub, h1, h2, sub_zero]
  · have h3 := congrFun (congrFun (hC w) i) j
    simp only [compAtF, Matrix.map_apply, RingHom.comp_apply] at h3
    rw [RingHom.map_sub, RingHom.map_sub, h3, sub_self]

end GlobalTheory.RealWeilF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwapStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ x y : WOF F E nS nT,
      symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  first | exact @GlobalTheory.SymplSkew.symplOF_swap | exact GlobalTheory.SymplSkew.symplOF_swap | (intros; apply GlobalTheory.SymplSkew.symplOF_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensityStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density : ∀ {n : ℕ} {Y : Type} [TopologicalSpace Y] (e : OpenPartialHomeomorph Y (V n)) {S : Set Y} {d : Y → ℝ}, IsOpen S → (∀ y ∈ S, y ∈ e.source → ∃ g : V n → ℝ, ContinuousAt g (e y) ∧ ∀ᶠ z in 𝓝 y, d z = g (e z)) → AEMeasurable (fun v => d (e.symm v)) (volume.restrict (e.target ∩ e.symm ⁻¹' S)) := by
  first | exact @GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous | exact GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous | (intros; apply GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicIndependentEtaleTowerCoordinates
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem etTower_coords_algebraicIndependent {K L : Type} [Field K] [Field L] (cK : ℂ →+* K)
    (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) :
    IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
    Function.Injective (MvPolynomial.eval₂Hom ι τ) →
    (letI := cL.toAlgebra; AlgebraicIndependent ℂ
      (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  intro h hx hinj
  letI := cL.toAlgebra
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let φ : MvPolynomial (Fin n) ℂ →+* R := MvPolynomial.eval₂Hom c0 x
  have hφinj : Function.Injective φ := by
    have hxK : Function.Injective (MvPolynomial.eval₂Hom cK (fun i => (x i : K))) := by
      letI := cK.toAlgebra
      have h1 := hx.1
      rw [algebraicIndependent_iff_injective_aeval] at h1
      exact h1
    have hcomp : R.subtype.comp φ = MvPolynomial.eval₂Hom cK (fun i => (x i : K)) := by
      ext <;> simp [φ, c0]
    intro a b e
    apply hxK
    rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, e]
  have key : (T.subtype.comp ((MvPolynomial.eval₂Hom ι τ).comp ((MvPolynomial.map φ).comp
        (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).toRingEquiv.toRingHom)))
        = (MvPolynomial.aeval (Sum.elim (fun i => (τ i : L)) (fun i => (ι (x i) : L)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have := h.const a
      simp [φ, c0, MvPolynomial.sumAlgEquiv_C_inl]
      exact this
    · rintro (i | j) <;> simp [φ, MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]
  have hy : Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)) ∘ finSumFinEquiv
      = Sum.elim (fun i => (τ i : L)) (fun i => (ι (x i) : L)) := by
    ext (i | j) <;> simp
  rw [← algebraicIndependent_equiv finSumFinEquiv, hy, algebraicIndependent_iff_injective_aeval,
    injective_iff_map_eq_zero]
  intro P hP
  have hP' : T.subtype.comp ((MvPolynomial.eval₂Hom ι τ).comp ((MvPolynomial.map φ).comp
        (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).toRingEquiv.toRingHom)) P = 0 := by
    rw [key]; exact hP
  have h1 : MvPolynomial.eval₂Hom ι τ (MvPolynomial.map φ (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n) P)) = 0 :=
    Subtype.ext hP'
  have h2 := (injective_iff_map_eq_zero _).1 hinj _ h1
  have h3 := (injective_iff_map_eq_zero _).1 (MvPolynomial.map_injective φ hφinj) _ h2
  exact (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).map_eq_zero_iff.1 h3

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostLowerTriangularDiagMinorIsUnitStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (O : Subring K) (g : Mat m K), AlmostLow τ a b g → Par 0 O g → (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → g x.1 x.2 x.2 ≠ 0 ∧ (g x.1 x.2 x.2)⁻¹ ∈ O) ∧ minor τ a b g ≠ 0 ∧ (minor τ a b g)⁻¹ ∈ O := by
  first | exact @GlobalTheory.FlagPush.almostLow_units | exact GlobalTheory.FlagPush.almostLow_units | (intros; apply GlobalTheory.FlagPush.almostLow_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDerivCutoffConnectionDifferenceEqStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, DifferentiableAt ℝ ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b)) = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | exact GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | (intros; apply GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub <;> assumption)
end

