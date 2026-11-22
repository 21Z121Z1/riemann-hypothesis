import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0680
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0746
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0690
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0681
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0679
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0148
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0741
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem dvd_of_exp_eq_one (k : ℤ) (N : ℕ) (hN : 0 < N)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (k : ℂ) / N) = 1) : (N : ℤ) ∣ k := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_eq_iff hN'] at hm
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : (2 * Real.pi * Complex.I) * ((k : ℂ) + m * N) = 0 := by linear_combination -hm
  have h4 : ((k + m * N : ℤ) : ℂ) = 0 := by push_cast; exact (mul_eq_zero.1 h3).resolve_left hpi
  have h5 : k + m * N = 0 := by exact_mod_cast h4
  exact ⟨-m, by linarith⟩

theorem eq_of_exp_eq (m m' : ℤ) (h : ∀ N : ℕ, 0 < N → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / N) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (m' : ℂ) / N)) : m = m' := by
  have hN : 0 < (m - m').natAbs + 1 := Nat.succ_pos _
  have h1 := h _ hN
  have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (((m - m' : ℤ)) : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ)) = 1 := by
    have e : -(2 * Real.pi * Complex.I) * (((m - m' : ℤ)) : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) =
        -(2 * Real.pi * Complex.I) * (m : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) -
          -(2 * Real.pi * Complex.I) * (m' : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 := dvd_of_exp_eq_one _ _ hN h2
  have h4 : m - m' = 0 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [Int.abs_eq_natAbs]; push_cast; omega)
  omega

theorem hermForm_im_sum (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (x y : Fin r → ℤ) :
    (hermForm Hm (∑ j, x j • lam j) (∑ j, y j • lam j)).im =
      ∑ i, ∑ j, (x i : ℝ) * (y j : ℝ) * (hermForm Hm (lam i) (lam j)).im := by
  have hs : ∀ (k : ℤ) (v : Fin g → ℂ), k • v = (k : ℂ) • v := fun k v => (Int.cast_smul_eq_zsmul ℂ k v).symm
  simp only [hermForm, hs, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, star_intCast, Finset.mul_sum, Complex.im_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem logDom_facts (n a : ℕ) : IsOpen (logDom n a) ∧ Convex ℝ (logDom n a) ∧
    (∀ s, AnalyticAt ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧
    Set.MapsTo (logExp a) (logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) :=
  GlobalTheory.T.punctPolydiscUniversalCover_open_convex_exp_analytic n a

theorem logExp_ne_zero (n a : ℕ) (s : Fin n → ℂ) (k : Fin n) (hk : (k : ℕ) < a) : logExp a s k ≠ 0 := by
  simp [logExp, hk, Complex.exp_ne_zero]

theorem isLatFam_comp (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) : IsLatFam B K → IsOpen B' →
    AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B → IsLatFam B' (fun b => K (φ b)) :=
  GlobalTheory.T.isLatFam_comp_of_analyticOnNhd m n g B B' K φ

theorem det_ne_zero_of_herm (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ)
    (M : Matrix (Fin r) (Fin r) ℤ) : (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ lam →
    Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 :=
  GlobalTheory.T.det_ne_zero_of_imHermForm_integral_real_basis g r Hm lam M

theorem linIndep_rows (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) :
    LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) :=
  GlobalTheory.T.rat_linearIndependent_coords_of_real_independent g r r₀ lam u A

theorem bounded_span (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ)
    (A : Fin r₀ → Fin r → ℤ) (C : ℝ) : (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) →
    ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' :=
  GlobalTheory.T.bounded_combination_of_span_coordinate_rows X g r r₀ T lam u A C

theorem mem_of_isLatBasis {g r : ℕ} {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (h : IsLatBasis K b) (i : Fin r) :
    b i ∈ K :=
  (h.2 (b i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩

theorem span_top_of_isLatBasis {g r : ℕ} {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (h : IsLatBasis K b)
    (hK : Submodule.span ℝ K = ⊤) : Submodule.span ℝ (Set.range b) = ⊤ := by
  rw [eq_top_iff, ← hK, Submodule.span_le]
  intro w hw
  obtain ⟨m, rfl⟩ := (h.2 w).1 hw
  exact Submodule.sum_mem _ fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := b) j)) _

end GlobalTheory.ShFam.Hor.LogCh.Core

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem core : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ (∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r₀ K ζ Pair hK hζan hζli hζK hζ0 hζbd hstd huniq hprop hinner hS
  obtain ⟨hDo, hDc, hEa, hEm⟩ := logDom_facts n a
  have hDp : IsPreconnected (logDom n a) := hDc.isPreconnected
  have hEd : Differentiable ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) := fun s => (hEa s).differentiableAt
  have hK' : IsLatFam (logDom n a) (fun s => K (logExp a s)) :=
    isLatFam_comp n n g _ _ K (logExp a) hK hDo (fun s _ => hEa s) hEm
  have hin := fun s (hs : s ∈ logDom n a) => hinner _ (hEm hs) (fun k hk => logExp_ne_zero n a s k hk)
  obtain ⟨lam, hlamD, hlamB⟩ := GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex n g (2 * g) (logDom n a) (fun s => K (logExp a s)) hDo hDc
    (fun s hs => GlobalTheory.T.exists_analytic_local_lattice_basis n g (logDom n a) (fun s => K (logExp a s)) s hK' hs (hin s hs).choose_spec.2.2.1)
  have hmem : ∀ s ∈ logDom n a, ∀ i, lam s i ∈ K (logExp a s) := fun s hs i => mem_of_isLatBasis (hlamB s hs) i
  have hlamDi : ∀ i, DifferentiableOn ℂ (fun s => lam s i) (logDom n a) := fun i => differentiableOn_pi.1 hlamD i
  let s₀ : Fin n → ℂ := fun _ => (-1 / 2 : ℂ)
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    split_ifs <;> norm_num [s₀]
  obtain ⟨Hm₀, -, hpos₀, hspan₀, hint₀, hpair₀⟩ := hin s₀ hs₀
  have hMex : ∀ i j, ∃ m : ℤ, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = m := fun i j =>
    hint₀ _ (hmem s₀ hs₀ i) _ (hmem s₀ hs₀ j)
  obtain ⟨M, hM₀⟩ : ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ, ∀ i j, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = M i j :=
    ⟨fun i j => (hMex i j).choose, fun i j => (hMex i j).choose_spec⟩

  have hM : ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) →
      (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) →
        Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
          (Complex.exp_ne_zero _))) →
      ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j := by
    intro s hs Hm hint hpair i j
    obtain ⟨m', hm'⟩ := hint _ (hmem s hs i) _ (hmem s hs j)
    have key : m' = M i j := by
      apply eq_of_exp_eq
      intro N hN
      have h1 := hpair₀ N _ _ hN (hmem s₀ hs₀ i) (hmem s₀ hs₀ j)
      have h2 := hprop n N (logDom n a) (logExp a) (fun s => lam s i) (fun s => lam s j) _ s₀ s hN hDo hDp
        hEd.differentiableOn hEm (hlamDi i) (hlamDi j) (fun b hb => ⟨hmem b hb i, hmem b hb j⟩) hs₀ hs h1
      have h3 := hpair N _ _ hN (hmem s hs i) (hmem s hs j)
      have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
      simp only [Units.val_mk0, hm', hM₀, Complex.ofReal_intCast] at h4
      exact h4
    rw [hm', key]

  have hstdK : ∀ j : Fin g, ∀ s ∈ logDom n a, (Pi.single j 1 : Fin g → ℂ) ∈ K (logExp a s) := by
    intro j s hs
    obtain ⟨i, hi⟩ := hstd j
    rw [← hi _ (hEm hs)]
    exact hζK _ (hEm hs) i
  have hρex : ∀ j : Fin g, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a,
      (Pi.single j 1 : Fin g → ℂ) = ∑ k, m k • lam s k := fun j =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun _ => Pi.single j 1) s₀ hDp
      hlamD.continuousOn continuousOn_const hlamB (fun s hs => hstdK j s hs) hs₀
  choose mρ hmρ using hρex

  have hζc : ContinuousOn ζ (Metric.ball 0 1) := hζan.continuousOn
  have hζEc : ∀ i, ContinuousOn (fun s => ζ (logExp a s) i) (logDom n a) := fun i =>
    (continuousOn_pi.1 (hζc.comp hEd.continuous.continuousOn hEm)) i
  have hAex : ∀ i, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a, ζ (logExp a s) i = ∑ k, m k • lam s k := fun i =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun s => ζ (logExp a s) i) s₀ hDp
      hlamD.continuousOn (hζEc i) hlamB (fun s hs => hζK _ (hEm hs) i) hs₀
  choose A hA using hAex

  have hz₁ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := hEm hs₀
  have hsumK : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ z j ∈ K z := by
    intro z hz c
    obtain ⟨H, hH⟩ := hK.2.1 z hz
    have hj : ∀ j, ζ z j ∈ H := fun j => by rw [← SetLike.mem_coe, hH]; exact hζK z hz j
    rw [← hH]
    exact H.sum_mem fun j _ => H.zsmul_mem (hj j) _
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζan.differentiableOn
  have hsumD : ∀ c : Fin r₀ → ℤ, DifferentiableOn ℂ (fun z => ∑ j, c j • ζ z j) (Metric.ball 0 1) := by
    intro c
    have h : ∀ j ∈ (Finset.univ : Finset (Fin r₀)), DifferentiableOn ℂ (fun z => c j • ζ z j) (Metric.ball 0 1) :=
      fun j _ => (differentiableOn_pi.1 hζd j).const_smul (c j)
    refine (DifferentiableOn.sum h).congr fun z _ => ?_
    simp [Finset.sum_apply]
  have hsum_eq : ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ (logExp a s₀) j = ∑ k, (∑ i, c i • A i) k • lam s₀ k := by
    intro c
    simp only [fun i => hA i s₀ hs₀, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hform : ∀ x y : Fin (2 * g) → ℤ, (hermForm Hm₀ (∑ k, x k • lam s₀ k) (∑ k, y k • lam s₀ k)).im =
      ((x ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ y : ℤ) : ℝ) := by
    intro x y
    rw [hermForm_im_sum]
    simp only [hM₀, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ c c' : Fin r₀ → ℤ, (fun j => (c j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, c i • A i) ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ (∑ i, c' i • A i) := by
    intro N hN
    obtain ⟨S, hcard, hSp⟩ := hS N hN
    refine ⟨S, hcard, fun c c' hc => ?_⟩
    have h1 := hSp c c' hc
    have h2 := hprop n N (Metric.ball 0 1) id (fun z => ∑ j, c j • ζ z j) (fun z => ∑ j, c' j • ζ z j) 1 0
      (logExp a s₀) hN Metric.isOpen_ball (convex_ball 0 1).isPreconnected differentiableOn_id (Set.mapsTo_id _)
      (hsumD c) (hsumD c') (fun b hb => ⟨hsumK b hb c, hsumK b hb c'⟩) (Metric.mem_ball_self one_pos) hz₁ h1
    have h3 := hpair₀ N _ _ hN (hsumK _ hz₁ c) (hsumK _ hz₁ c')
    have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
    simp only [Units.val_mk0, Units.val_one, id, hsum_eq, hform, Complex.ofReal_intCast] at h4
    exact dvd_of_exp_eq_one _ N hN h4
  have hdet : (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ).det ≠ 0 :=
    det_ne_zero_of_herm g (2 * g) Hm₀ (lam s₀) M hpos₀ (hlamB s₀ hs₀).1
      (span_top_of_isLatBasis (hlamB s₀ hs₀) hspan₀) hM₀
  have hlinQ := linIndep_rows g (2 * g) r₀ (lam s₀) (ζ (logExp a s₀)) A (hζli _ hz₁) (fun i => hA i s₀ hs₀)
  have hco := GlobalTheory.T.coisotropic_sublattice_of_torsion_count (2 * g) r₀ M A hdet hlinQ hdvd

  obtain ⟨C, hC⟩ := hζbd
  have hgr := GlobalTheory.T.periods_polyGrowth_of_bounded_coisotropic n a g (2 * g) lam ((M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ).map (Int.cast : ℤ → ℝ))
    (Submodule.span ℝ (Set.range fun i j => (A i j : ℝ))) hlamD
    (fun s hs => by
      obtain ⟨Hm, hH, hpos, hspan, hint, hpair⟩ := hin s hs
      exact ⟨(hlamB s hs).1, span_top_of_isLatBasis (hlamB s hs) hspan, Hm, hH, hpos, fun i j => by
        rw [hM s hs Hm hint hpair i j]; simp⟩)
    (fun v hv => hco v fun i => hv _ (Submodule.subset_span (Set.mem_range_self (f := fun i j => (A i j : ℝ)) i)))
    (fun w hw => by
      obtain ⟨C', hC'⟩ := bounded_span (Fin n → ℂ) g (2 * g) r₀ (logDom n a) lam (fun s => ζ (logExp a s)) A C
        (fun s hs i => hA i s hs) (fun s hs => hC _ (hEm hs)) w hw
      exact ⟨C', fun s hs _ => hC' s hs⟩)
  refine ⟨2 * g, lam, fun j k => (mρ j k : ℂ), hlamD.continuousOn,
    fun s hs => ⟨(hlamB s hs).1.restrict_scalars' ℤ, (hlamB s hs).2, fun j => ?_⟩, hgr⟩
  rw [hmρ j s hs]
  exact Finset.sum_congr rfl fun k _ => Int.cast_smul_eq_zsmul ℂ _ _

end GlobalTheory.ShFam.Hor.LogCh.Core
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitCharacterNontrivial
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.CompRamified

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← WithZero.exp_log hx0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem exists_int_locK_ne (χ : HChar L) (t : SplitPlace L) (ht : χ.TameAt t.w) (hr : ¬ χ.UnrAt t.w) :
    ∃ b : 𝓞 (maximalRealSubfield L), b ∉ t.v.asIdeal ∧ ∃ k : Lˣ,
      (k : L) = ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b : 𝓞 L) : L) ∧ χ.locK t.w k ≠ 1 := by
  classical
  simp only [HChar.UnrAt, not_forall] at hr
  obtain ⟨x, hx, hne⟩ := hr
  have hx' : Valued.v (x : t.w.adicCompletion L) = 1 := hx
  obtain ⟨a, ha⟩ := adic_exists_approx t.w (x : t.w.adicCompletion L) (le_of_eq hx')
  obtain ⟨b, hb⟩ := adic_exists_approx t.v (t.i (a : L)) (t.split_le_one a)
  set c : 𝓞 L := algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b with hcdef
  have hac : a - c ∈ t.w.asIdeal := by
    show a - c ∈ t.ideal
    rw [t.split_mem_ideal]
    have e : t.i ((c : 𝓞 L) : L) =
        algebraMap (𝓞 (maximalRealSubfield L)) (t.v.adicCompletion (maximalRealSubfield L)) b := by
      rw [hcdef, split_coe_algebraMap, AlgHom.commutes]; rfl
    have e2 : ((a - c : 𝓞 L) : L) = (a : L) - (c : L) := by push_cast; rfl
    rw [e2, map_sub, e]
    exact hb
  have hval : ∀ z : 𝓞 L, Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) z) = t.w.valuation L (z : L) := fun z => by
    exact adic_valued_algebraMap (R := 𝓞 L) (K := L) t.w (z : L)
  have hxc : Valued.v ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) < 1 := by
    have e : (x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c =
        ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ a) + algebraMap (𝓞 L) _ (a - c) := by
      rw [map_sub]; ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha ?_)
    rw [hval]
    exact (t.w.valuation_lt_one_iff_mem (a - c)).2 hac
  have hc1 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) = 1 := by
    have e : algebraMap (𝓞 L) (t.w.adicCompletion L) c =
        (x : t.w.adicCompletion L) - ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) := by ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hx']; exact hxc)]
    exact hx'
  have hbv : b ∉ t.v.asIdeal := by
    intro hm
    have h1 := (t.split_alg_mem b).2 hm
    have h2 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) < 1 := by
      rw [hval]; exact (t.w.valuation_lt_one_iff_mem c).2 h1
    rw [hc1] at h2
    exact lt_irrefl _ h2
  have hc0 : (c : L) ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 L) (t.w.adicCompletion L) c = 0 := by
      show algebraMap L (t.w.adicCompletion L) (c : L) = 0
      rw [h0, map_zero]
    rw [this, map_zero] at hc1
    exact zero_ne_one hc1
  refine ⟨b, hbv, Units.mk0 (c : L) hc0, rfl, ?_⟩
  intro h1
  apply hne
  set y : (t.w.adicCompletion L)ˣ := atFin t.w (Units.mk0 (c : L) hc0) with hydef
  have hy : (y : t.w.adicCompletion L) = algebraMap (𝓞 L) (t.w.adicCompletion L) c := rfl
  have hu : IsUnitAt t.w (y * x⁻¹) := by
    show Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ)) : t.w.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hc1, hx', inv_one, mul_one]
  have hsub : Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : ((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1 =
        -((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) * (x : t.w.adicCompletion L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hy]
      field_simp
      ring
    rw [e, map_mul, Valuation.map_neg, map_inv₀, hx', inv_one, mul_one]
    exact le_exp_neg_one_of_lt_one' hxc
  have h2 := ht (y * x⁻¹) hu hsub
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [← h2]
  exact h1

end Gen

end GlobalTheory.CompRamified

open GlobalTheory.CompRamified in

theorem GlobalTheory.CompRamified.exists_unit_ne_one : ∀ (D : D7) (cf : CharFrame D) (j : Fin D.R.m) (ξH : HChar D.host.E) (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), ξH.TrivOn D.host.F → (∀ u, ξH.TameAt u) → s.v ∈ qPl D (cf.mu0 j * ξH) → NG.IsCompAt (cf.mu0 j * ξH) s ξ → ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1 := by
  classical
  intro D cf j ξH s ξ htr hta hq hc
  set η := cf.mu0 j * ξH with hη
  have htame : ∀ u, η.TameAt u := fun u x hx h1 => by
    rw [hη, HChar.loc_mul, (cf.isMu0 j).tame u x hx h1, hta u x hx h1, one_mul]
  have htriv : ∀ k : (D.host.F)ˣ, ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, η.locK P (upF D.host.F k) = 1 := fun k => by
    have h1 := (cf.isMu0 j).triv.1 s.v k
    have h2 := htr.1 s.v k
    rw [GlobalTheory.GalToHecke.resFin_eq] at h1 h2
    rw [hη]
    show ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, ((cf.mu0 j).locK P (upF D.host.F k) * ξH.locK P (upF D.host.F k)) = 1
    rw [Finset.prod_mul_distrib, h1, h2, one_mul]
  obtain ⟨-, w, hw, hram⟩ := hq
  have key : ∃ b : 𝓞 (maximalRealSubfield D.host.E), b ∉ s.v.asIdeal ∧ ∃ k : (D.host.E)ˣ,
      (k : D.host.E) = ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) ∧
        η.locK w k ≠ 1 := by
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e
    · subst e
      exact exists_int_locK_ne η s (htame _) hram
    · have e2 := (GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w e).1
      have h := exists_int_locK_ne η (GlobalTheory.TypeTame.conjSP s) (e2 ▸ htame _) (e2 ▸ hram)
      rw [e2] at h
      exact h
  obtain ⟨b, hbv, k, hk, hne⟩ := key
  have hb0 : ((b : maximalRealSubfield D.host.E) : D.host.E) ≠ 0 := by
    intro h0
    apply hbv
    have : (b : maximalRealSubfield D.host.E) = 0 := by exact_mod_cast h0
    have : b = 0 := RingOfIntegers.coe_eq_zero_iff.mp this
    rw [this]; exact s.v.asIdeal.zero_mem
  have hF0 : (b : maximalRealSubfield D.host.E) ≠ 0 := fun h => hb0 (by rw [h]; rfl)
  set f : (D.host.F)ˣ := Units.mk0 (b : maximalRealSubfield D.host.E) hF0 with hfdef
  have hfk : upF D.host.F f = k := by
    apply Units.ext
    rw [hk]
    rfl
  have hsw : η.locK s.w k ≠ 1 := by
    by_cases e : s.w = w
    · rwa [e]
    have hc' : IsConjPl D.host w s.w := (GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw).resolve_left e
    have hab : aboveF (L := D.host.E) D.host.F s.v = {s.w, w} := by
      ext P
      rw [GlobalTheory.GalToHecke.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hP
        have hov : NG.OverPl P s.v := by rw [← hP]; rfl
        rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s P hov with e' | e'
        · exact Or.inl e'.symm
        · exact Or.inr (GlobalTheory.HeightCounting.TrueConjLabels.eq_of_isConjPl e' hc')
      · rintro (rfl | rfl)
        · exact HeightOneSpectrum.ext s.w_under
        · exact HeightOneSpectrum.ext hw
    have h := htriv f
    rw [hab, Finset.prod_pair e, hfk] at h
    intro h1
    rw [h1, one_mul] at h
    exact hne h
  refine ⟨Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k, ?_, ?_⟩
  · show Valued.v (s.i (k : D.host.E)) = 1
    rw [hk, s.split_val_alg]
    refine le_antisymm (s.v.valuation_le_one b) (not_lt.1 fun h => hbv ((s.v.valuation_lt_one_iff_mem b).1 h))
  · rw [hc.2 k]
    exact hsw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAddCharZmodEqOfNeOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory

theorem exists_nontrivial_addChar_eq_of_ne (p : ℕ) [Fact p.Prime] (Pr : Prop) (φ : AddChar (ZMod p) ℂ) (h : Pr → φ ≠ 1) :
    ∃ ψ' : AddChar (ZMod p) ℂ, ψ' ≠ 1 ∧ (Pr → ψ' = φ) := by
  by_cases hP : Pr
  · exact ⟨φ, h hP, fun _ => rfl⟩
  · refine ⟨ZMod.stdAddChar, ?_, fun h' => absurd h' hP⟩
    intro h1
    have hprim := ZMod.isPrimitive_stdAddChar p
    apply hprim (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, h1]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCellStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
    ∃ (δ' : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ'), LinearIndependent ℤ δ' ∧
      (∀ i, IsPrim bar (⟨δ' i, h.mem i⟩ : balForms bar X)) ∧ ∀ β, InRCone δ β → InRCone δ' β := by
  first | exact @GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim | exact GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim | (intros; apply GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowFormsAdelicDecoratedLatticesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowForms_adelic_decoratedLattices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    L.βX = 1 → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ s : ∀ t, Seed.RowSideT (famR X I hX U Xg tr) L cX (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) t, (∀ t,       (∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
        eG ((s t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∧
      Bridge.CoefTie X.toD7.sp.X' cX.coef (s t).pres (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) c0R (pairV (labLL X.toD7) _ gramR)
        (nabAt (labLL X.toD7) _) (delAt (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') (s t).pres ((famR X I hX U Xg tr).heckeRI t)
        (fun i => Formalism.L2.Col.InertTypeOk X.toD7.sp.X'.rank i.2)
        (fun i => IsLabElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1 (labIn X.toD7.sp.X'.rank i.2))
        fun i => IsLocElt X.toD7.sp.X' (i.1.1 : PlI X.B px).1)) ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => (s t).pres.extL φ)  := by
  first | exact @GlobalTheory.Mem.R3.RowsRead.exists_rowSide | exact GlobalTheory.Mem.R3.RowsRead.exists_rowSide | (intros; apply GlobalTheory.Mem.R3.RowsRead.exists_rowSide <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantLabellingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_starSubdivision_invariant_labelling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H lab → SimpLab H.bar q φ lab → IsTwInv H w → IsCentreSet H.bar q φ w →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' →
    ∃ lab' : InvFun (𝓞 E), IsTwInv H lab' ∧ SimpLab H.bar q ψ' lab' := by
  first | exact @GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star | exact GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star | (intros; apply GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentDimAndBaseDimStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagComponent_dim_and_base_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) ∧ X.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
  first | exact @GlobalTheory.FlagBaseDim.dims | exact GlobalTheory.FlagBaseDim.dims | (intros; apply GlobalTheory.FlagBaseDim.dims <;> assumption)
end

