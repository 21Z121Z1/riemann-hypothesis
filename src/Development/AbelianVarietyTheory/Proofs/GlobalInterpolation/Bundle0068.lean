import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0062
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemIff
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare.StabPart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}
  {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F} {k : ℕ}

theorem prP_symm (a b : v.adicCompletion F) : prP s (s.symm (a, b)) = a := by
  show (s (s.symm (a, b))).1 = a
  rw [s.apply_symm_apply]

theorem prPbar_symm (a b : v.adicCompletion F) : prPbar s (s.symm (a, b)) = b := by
  show (s (s.symm (a, b))).2 = b
  rw [s.apply_symm_apply]

theorem map_mulVec_bc {A K : Type} [CommRing A] [CommRing K] (p : A →+* K) (g : GL (Fin k) A)
    (x : Fin k → A) :
    (fun i => p (((g : Matrix (Fin k) (Fin k) A) *ᵥ x) i)) =
      ((bc p g : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ fun j => p (x j) :=
  funext fun _ => RingHom.map_mulVec p _ _ _

theorem mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (x : Fin k → E ⊗[F] v.adicCompletion F) :
    x ∈ Λ ↔ (fun i => prP s (x i)) ∈ partOf (prP s) Λ ∧
      (fun i => prPbar s (x i)) ∈ partOf (prPbar s) Λ := by
  rw [mem_partOf _ (sur_prP hs), mem_partOf _ (sur_prPbar hs)]
  refine ⟨fun hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩, ?_⟩
  rintro ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩
  have h1 : s.symm (1, 0) ∈ intV E v :=
    (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩)
  have h2 : s.symm (0, 1) ∈ intV E v :=
    (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩)
  have hx : x = (⟨_, h1⟩ : intV E v) • a + (⟨_, h2⟩ : intV E v) • b := by
    funext i
    show x i = s.symm (1, 0) * a i + s.symm (0, 1) * b i
    apply s.injective
    have e1 : (s (a i)).1 = (s (x i)).1 := congrFun ha' i
    have e2 : (s (b i)).2 = (s (x i)).2 := congrFun hb' i
    rw [map_add, map_mul, map_mul, s.apply_symm_apply, s.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_mul, Prod.fst_mul, one_mul, zero_mul, add_zero, e1]
    · rw [Prod.snd_add, Prod.snd_mul, Prod.snd_mul, one_mul, zero_mul, zero_add, e2]
  rw [hx]
  exact Λ.add_mem (Λ.smul_mem _ ha) (Λ.smul_mem _ hb)

theorem mulVec_mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (y z : Fin k → v.adicCompletion F) :
    (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => s.symm (y i, z i)) ∈ Λ ↔
      ((bc (prP s) g : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ y ∈ partOf (prP s) Λ ∧
      ((bc (prPbar s) g : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ z ∈ partOf (prPbar s) Λ := by
  rw [mem_iff hs, map_mulVec_bc, map_mulVec_bc]
  simp only [prP_symm, prPbar_symm]

theorem symm_mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (y z : Fin k → v.adicCompletion F) :
    (fun i => s.symm (y i, z i)) ∈ Λ ↔ y ∈ partOf (prP s) Λ ∧ z ∈ partOf (prPbar s) Λ := by
  rw [mem_iff hs]
  simp only [prP_symm, prPbar_symm]

theorem stabPart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (k : ℕ) (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)), (∀ x, x ∈ Λ ↔ (fun i => prP s (x i)) ∈ partOf (prP s) Λ ∧ (fun i => prPbar s (x i)) ∈ partOf (prPbar s) Λ) ∧ (∀ g : GL (Fin k) (E ⊗[F] v.adicCompletion F), g ∈ stabGL Λ ↔ bc (prP s) g ∈ stabGL (partOf (prP s) Λ) ∧ bc (prPbar s) g ∈ stabGL (partOf (prPbar s) Λ)) ∧ ∀ B : GL (Fin k) (E ⊗[F] v.adicCompletion F), (∀ y : Fin k → E ⊗[F] v.adicCompletion F, (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ Λ ↔ ∀ i, y i ∈ intV E v) → GlobalTheory.OverCompare.IsFrame (partOf (prP s) Λ) (bc (prP s) B) ∧ GlobalTheory.OverCompare.IsFrame (partOf (prPbar s) Λ) (bc (prPbar s) B) := by
  intro F E _ _ _ _ _ σ v s hs k Λ
  refine ⟨mem_iff hs Λ, fun g => ⟨fun hg => ⟨fun y => ?_, fun z => ?_⟩, fun hg x => ?_⟩,
    fun B hB => ⟨fun y => ?_, fun z => ?_⟩⟩
  · have h : _ ↔ _ := hg (fun i => s.symm (y i, (0 : Fin k → v.adicCompletion F) i))
    rw [mulVec_mem_iff hs, symm_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, and_true] using h
  · have h : _ ↔ _ := hg (fun i => s.symm ((0 : Fin k → v.adicCompletion F) i, z i))
    rw [mulVec_mem_iff hs, symm_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, true_and] using h
  · rw [mem_iff hs Λ x, mem_iff hs Λ (_ *ᵥ x), map_mulVec_bc, map_mulVec_bc]
    exact and_congr (hg.1 _) (hg.2 _)
  · have h := hB (fun i => s.symm (y i, (0 : Fin k → v.adicCompletion F) i))
    rw [mulVec_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, and_true, hs.2.2, RingEquiv.apply_symm_apply, Pi.zero_apply] using h
  · have h := hB (fun i => s.symm ((0 : Fin k → v.adicCompletion F) i, z i))
    rw [mulVec_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, true_and, hs.2.2, RingEquiv.apply_symm_apply, Pi.zero_apply] using h

end GlobalTheory.OverCompare.StabPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemLocLatIffOfFrame
section
namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

theorem _root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ u ∈ _root_.Formalism.BasicNotions.intV E v, u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) = 1 := by
  have hc0 : (c : F) ≠ 0 := by
    intro h
    apply hc
    rw [show c = 0 from RingOfIntegers.coe_eq_zero_iff.mp h]
    exact v.asIdeal.zero_mem
  have hmem : algebraMap F (v.adicCompletion F) (c : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [_root_.GlobalTheory.LocalLattice.algebraMap_mem_adicCompletionIntegers_iff,
      _root_.GlobalTheory.LocalLattice.mem_localRing_iff]
    refine ⟨c, hc, ?_⟩
    rw [Algebra.smul_def, show algebraMap (𝓞 F) F c = (c : F) from rfl, mul_inv_cancel₀ hc0]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  refine ⟨1 ⊗ₜ[F] algebraMap F (v.adicCompletion F) (c : F)⁻¹, ?_, ?_⟩
  · unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt _root_.Formalism.UG.intOE
    exact Subring.subset_closure (Or.inr ⟨⟨_, hmem⟩, rfl⟩)
  · unfold _root_.Formalism.UG.inclE
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply', ← map_mul, inv_mul_cancel₀ hc0, map_one]

end GlobalTheory.OverCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.HCEntries

variable {D : D7} {L : SizeData₂ D}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by unfold Ranks.n; exact D.R.ord_pos
  exact_mod_cast this

theorem one_le_k (D : D7) : (1 : ℝ) ≤ D.R.k := by
  have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact_mod_cast this

theorem one_le_letterBlockLength (D : D7) : (1 : ℝ) ≤ D.R.t := by
  have : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega
  exact_mod_cast this

theorem eta_k_le (h : SizeEta L) : L.etaSz ≤ L.sc.b ∧ (D.R.k : ℝ) ≤ L.sc.b := by
  obtain ⟨h1, h2, -⟩ := h
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hf : (1 : ℝ) ≤ D.R.f := by
    have := one_le_n D
    unfold Ranks.f
    push_cast
    linarith
  have hk3 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 3 := le_self_pow₀ hk (by norm_num)
  have htf : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) hf
  have hP : (D.R.k : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    hk3.trans (le_mul_of_one_le_left (by positivity) htf)
  rw [le_div_iff₀ (by linarith)] at h2
  constructor <;> nlinarith

theorem b'_Sc_le (h : SizeLstar L) : L.sc.b' + L.Sc ≤ L.sc.b := by
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hn := one_le_n D
  have hL := one_le_scL L
  have hb := one_le_b L
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by
    have : D.R.m ≤ D.R.t := by have := D.R.three_m_lt_t; omega
    exact_mod_cast this
  have h0 : 0 ≤ szlStar L := by unfold szlStar; positivity
  have h1 : szlStar L ≤ L.sc.b := by
    unfold szlStar
    rw [div_le_iff₀ (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have e1 : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hn)
    have e2 : L.Sc + D.R.t + L.sc.L ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      le_mul_of_one_le_left (by positivity) e1
    have e3 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    linarith
  have h2 : 0 ≤ L.sc.b / szlStar L := div_nonneg (by linarith) h0
  linarith [h.1]

theorem bT_le (hLa : SizeLa L) (hR : SizeRho L) (hB : SizeBot L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hk := one_le_k D
  have hb := b'_pos L
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg (by linarith) _) hLa.1
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx.le
  have h1 : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by positivity
  have h2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  unfold SizeRho at hR
  have h3 : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h4 := hB t
  have h5 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h6 := mul_le_mul_of_nonneg_right h3 hb.le
  linarith

theorem aT_le (L : SizeData₂ D) (t : D.host.TT) : (L.aT t : ℝ) ≤ 2 * L.sc.x * L.sc.b := by
  have hx := L.sc.one_lt_alt
  have hb := one_le_b L
  have h1 := (L.aT_win t).2
  have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_k D) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num))
  have h3 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
    div_le_self (by unfold Scale.a; positivity) h2
  have h4 : L.sc.a = L.sc.x * L.sc.b := rfl
  linarith

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem wj_bounds (h : SizesAt L) (hx : 2 ≤ L.sc.x) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    0 ≤ wj D j τ ∧ wj D j τ ≤ 3 * L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hR, hB, -, -, hE, -, hS, -⟩ := h
  have hb := one_le_b L
  have hb' := b'_pos L
  have he := (eta_k_le hE).1
  have hbb : L.sc.b' ≤ L.sc.b := by linarith [b'_Sc_le hS, L.Sc_pos]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht⟩ := exists_top ha
    obtain ⟨a1, a2⟩ := L.win_top j h1 h2 τ t ht
    have a3 := L.bT_ge t
    have a4 := bT_le hLa hR hB t
    have a5 : 0 ≤ L.sc.b' / L.sc.x := by positivity
    have a6 : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
    constructor <;> linarith
  · by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨a1, a2⟩ := L.win_thick j h1 h2 τ hc
      constructor <;> linarith
    · obtain ⟨a1, a2⟩ := L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, ha, hc⟩
      have hn := one_le_n D
      have a5 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
      have a6 : L.sc.w'' D.R.n ≤ L.sc.b' :=
        div_le_self hb'.le (one_le_mul_of_one_le_of_one_le (by linarith) hn)
      constructor <;> linarith

theorem b_bounds (h : SizesAt L) (hx : 2 ≤ L.sc.x) (τ : D.what₂.Tau) (j : Fin D.R.m) :
    -L.sc.b ≤ (((D.hc τ).b j : ℚ) : ℝ) ∧ (((D.hc τ).b j : ℚ) : ℝ) ≤ 3 * L.sc.b := by
  obtain ⟨a1, a2⟩ := wj_bounds h hx (j.1 + 1) (by omega) j.2 τ
  have hw : wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (by simp)]
    rfl
  rw [hw] at a1 a2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := h
  have he := (eta_k_le hE).1
  have a3 := abs_le.1 (L.be_close τ j j)
  have a4 : (D.hc τ).b j ≤ (D.hc τ).e j := by
    have := (D.hc τ).gap_be j
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have a5 : (((D.hc τ).b j : ℚ) : ℝ) ≤ (((D.hc τ).e j : ℚ) : ℝ) := by exact_mod_cast a4
  push_cast at a3
  constructor <;> linarith [a3.1]

theorem sigPar_bound (h : SizesAt L) (hx : 2 ≤ L.sc.x) (τ : D.what₂.Tau) (l : ℕ) :
    |((sigPar D τ l : ℚ) : ℝ)| ≤ 4 * L.sc.b := by
  have hb := one_le_b L
  have hS : L.Sc ≤ L.sc.b := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    linarith [b'_Sc_le hS, b'_pos L]
  unfold sigPar
  split_ifs with h1 h2
  · obtain ⟨a1, a2⟩ := L.cloud_v τ ⟨l, h1⟩
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := b_bounds h hx τ ⟨_, h2⟩
    rw [abs_le]
    push_cast
    constructor <;> linarith
  · simp only [Rat.cast_zero, abs_zero]
    linarith

theorem u_bound (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (l : Fin D.R.k) : |(((D.hcW u τ).u l : ℚ) : ℝ)| ≤ 4 * L.sc.x * L.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm := D.R.two_le_m
  have hb := one_le_b L
  have hxb : 2 * L.sc.b ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx (by linarith)
  have hb1 := b_bounds h hx τ ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -, hS, -⟩ := h
  have hkb := (eta_k_le hE).2
  have hS : L.Sc ≤ L.sc.b := by linarith [b'_Sc_le hS, b'_pos L]
  obtain ⟨r, hr⟩ := l
  rw [abs_le]
  by_cases h0 : r = 0
  · subst h0
    rw [D.hcW_first u τ hr]
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    refine ⟨by linarith [h2.1], ?_⟩
    by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht⟩ := exists_top ha
      rw [(L.top_u τ t hr ht).1]
      linarith [aT_le L t]
    · have h1 := P.cloud_place_bound τ (by omega) ha
      push_cast at h1
      linarith [h2.2]
  · by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega)]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      have h3 : -(((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) := by
        exact_mod_cast (D.hc τ).u_last_gt (by omega) (by omega)
      have h4 : (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by
        have := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
        have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hr⟩ :=
          Fin.ext (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
        simp only at this
        rw [e] at this
        exact_mod_cast this
      constructor <;> linarith [h2.2, hb1.2]

theorem entries : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, (∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, 0 ≤ wj (Fm.D x i) j τ ∧ wj (Fm.D x i) j τ ≤ 3 * (Fm.L x i).sc.b ∧ wSz (Fm.D x i) j τ = wj (Fm.D x i) j τ) ∧ (∀ u τ (l : Fin (Fm.D x i).R.k), |((((Fm.D x i).hcW u τ).u l : ℚ) : ℝ)| ≤ 4 * x * (Fm.L x i).sc.b) ∧ (∀ τ l, |((sigPar (Fm.D x i) τ l : ℚ) : ℝ)| ≤ 4 * (Fm.L x i).sc.b)) := by
  intro eps Fm
  refine ⟨2, fun x hx2 hx i => ?_⟩
  have hS := Fm.sizes x hx i
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have h2 : 2 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx2
  refine ⟨fun j hj τ => ?_, fun u τ l => ?_, fun τ l => sigPar_bound hS h2 τ l⟩
  · obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
    obtain ⟨a1, a2⟩ := wj_bounds hS h2 j h1 hm τ
    refine ⟨a1, a2, ?_⟩
    unfold wSz wj
    rw [dif_pos ⟨h1, hm⟩, dif_pos (by omega)]
  · have := u_bound hS (Fm.params x hx i) h2 u τ l
    rwa [hsx] at this

end GlobalTheory.HCEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PairingScaledDirectionsEqPeriodPairing
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomFin

theorem pairing_scaled : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  intro D cc δ δ₀ B N N' g S e p _ lam Ω r b y a hq _ _ hb
  have hphi : ∀ z : D.host.E, D.host.φ₀ z ∈ Qbar := fun z => by
    have hx : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
    exact (mem_algebraicClosure_iff).2 (hx.algHom D.host.φ₀.toRatAlgHom)

  have hlin : ∀ (c : ℂ) (z w : Fin g → ℂ), JMB.beta S.d S.Hm (c • z) w = c * JMB.beta S.d S.Hm z w := by
    intro c z w
    simp only [JMB.beta, JMB.hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  set n := Ideal.absNorm cc
  have key : ∀ i, JMB.lamA lam (JMB.beta S.d S.Hm ((δ₀ / δ) • e (δ • embV D B.tor y)) (e (δ • embV D B.tor (b i))))
      = (lamC lam (δ / δ₀))⁻¹ * ((n : ℂ_[p]))⁻¹ * lamC lam (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
    intro i
    rw [hlin, hb]
    set z := D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)
    have hz := hphi ((hYY D y (b i) : D.host.K) : D.host.E)
    have heq : δ₀ / δ * (z / (n : ℂ)) = (((⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ : Qbar) : ℂ) := by
      have hc : (((n : Qbar)) : ℂ) = (n : ℂ) := by norm_cast
      simp only [IntermediateField.coe_mul, IntermediateField.coe_inv, hc]
      rw [inv_div]; ring
    have hmem : δ₀ / δ * (z / (n : ℂ)) ∈ Qbar := by rw [heq]; exact SetLike.coe_mem _
    unfold JMB.lamA lamC
    rw [dif_pos hmem, dif_pos hq, dif_pos hz]
    have : (⟨δ₀ / δ * (z / (n : ℂ)), hmem⟩ : Qbar) = (⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ := Subtype.ext heq
    rw [this, map_mul, map_mul, map_inv₀, map_inv₀, map_natCast]
  unfold JMB.pairD pairN
  simp only [key]
  have hzc : ∀ i, JMB.zc (a i) = zc (a i) := fun i => rfl
  simp only [hzc, mul_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.MomFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimePowSmulGoodLiftMemSetupLattice
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory

theorem goodLift_pow_smul_mem : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : JMB.Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok →
    ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d,
      ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
      ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  intro g S p _ lam N₀ n hS y hy
  have hw : ∀ x ∈ S.La, JMB.w0 S.d • x ∈ S.La := hS.2.2.2.2.2.1
  have hzs : ∀ (z : ℤ) (x : Fin g → ℂ), x ∈ S.La → ((z : ℂ)) • x ∈ S.La := by
    intro z x hx
    rw [Int.cast_smul_eq_zsmul ℂ z x]
    exact S.La.smul_mem z hx
  have hp : ((p : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, ⟨u, v, hκ⟩, _, x, hx, rfl⟩ := hy
    rw [smul_smul, mul_div_cancel₀ _ hp, hκ]
    have : ((u : ℂ) + (v : ℂ) * JMB.w0 S.d) * (N₀ : ℂ) = ((u * N₀ : ℤ) : ℂ) + ((v * N₀ : ℤ) : ℂ) * JMB.w0 S.d := by
      push_cast; ring
    rw [this, add_smul, mul_smul]
    exact S.La.add_mem (hzs _ _ hx) (hzs _ _ (hw x hx))
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact S.La.add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact S.La.neg_mem ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotientStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFractions_represent_primeNormQuotient : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  first | exact @GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | exact GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | (intros; apply GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelativeDeterminantIsometryNormOne
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory

theorem det_mul_conj_eq_one_of_preserves {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E →+* E)
    {n : Type} [Fintype n] [DecidableEq n] (φ : (n → K) →ₗ[K] (n → K))
    (h : ∀ v u : n → K, ∑ w, algebraMap K E (φ v w) * cj (algebraMap K E (φ u w))
      = ∑ w, algebraMap K E (v w) * cj (algebraMap K E (u w))) :
    algebraMap K E (LinearMap.det φ) * cj (algebraMap K E (LinearMap.det φ)) = 1 := by
  set A := LinearMap.toMatrix' φ with hA
  have key : ((algebraMap K E).mapMatrix A).transpose * (cj.mapMatrix ((algebraMap K E).mapMatrix A)) = 1 := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hA,
      LinearMap.toMatrix'_apply]
    rw [this, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, hA,
    LinearMap.det_toMatrix'] at hd
  exact hd

theorem detRel_mul_conj_eq_one (D : D7) (γ₀ γ : IsoK D) :
    ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  refine det_mul_conj_eq_one_of_preserves (K := D.host.K) (E := D.host.E) (D.host.conj : D.host.E →+* D.host.E) _ ?_
  intro v u
  have h1 := γ.isom (γ₀.g.symm v) (γ₀.g.symm u)
  have h2 := γ₀.isom (γ₀.g.symm v) (γ₀.g.symm u)
  simp only [LinearEquiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsicStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) := by
  first | exact @GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic | exact GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic | (intros; apply GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic <;> assumption)
end

