import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensity
section
noncomputable section

open GlobalTheory.CompanionTheory.ThTot

namespace GlobalTheory.CompanionTheory.ThTot.SchwT

section Analysis

variable {E E₁ E₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

theorem norm_iter_comp_le (A : E →L[ℝ] E₁) (hA : ‖A‖ ≤ 1) (f : SchwartzMap E₁ ℂ) (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun w => f (A w)) z‖ ≤ ‖iteratedFDeriv ℝ n f (A z)‖ := by
  have h : iteratedFDeriv ℝ n (fun w => f (A w)) z =
      (iteratedFDeriv ℝ n f (A z)).compContinuousLinearMap fun _ => A :=
    A.iteratedFDeriv_comp_right (f := f) (f.smooth n) z le_rfl
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖A‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hA
  exact mul_le_of_le_one_right (norm_nonneg _) this

def tens (A : E →L[ℝ] E₁) (B : E →L[ℝ] E₂) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : ∀ z, ‖z‖ ≤ max ‖A z‖ ‖B z‖) (f : SchwartzMap E₁ ℂ) (g : SchwartzMap E₂ ℂ) : SchwartzMap E ℂ where
  toFun z := f (A z) * g (B z)
  smooth' := ((f.smooth ⊤).comp A.contDiff).mul ((g.smooth ⊤).comp B.contDiff)
  decay' := by
    intro k n
    choose Cf hCf using fun (a : ℕ × ℕ) => f.decay' a.1 a.2
    choose Cg hCg using fun (a : ℕ × ℕ) => g.decay' a.1 a.2
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (Cf (k, i) * Cg (0, n - i) + Cf (0, i) * Cg (k, n - i)), fun z => ?_⟩
    have hf1 : ContDiff ℝ n (fun w => f (A w)) := (f.smooth n).comp A.contDiff
    have hg1 : ContDiff ℝ n (fun w => g (B w)) := (g.smooth n).comp B.contDiff
    have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := n) (N := n) hf1 hg1 z le_rfl
    have hz : ‖z‖ ^ k ≤ ‖A z‖ ^ k + ‖B z‖ ^ k := by
      rcases le_total ‖A z‖ ‖B z‖ with h | h
      · have : ‖z‖ ≤ ‖B z‖ := (hAB z).trans (max_le h le_rfl)
        exact (pow_le_pow_left₀ (norm_nonneg _) this k).trans (le_add_of_nonneg_left (by positivity))
      · have : ‖z‖ ≤ ‖A z‖ := (hAB z).trans (max_le le_rfl h)
        exact (pow_le_pow_left₀ (norm_nonneg _) this k).trans (le_add_of_nonneg_right (by positivity))
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => f (A z) * g (B z)) z‖
        ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ * ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖ :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1), ‖z‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ * ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖) :=
          Finset.mul_sum _ _ _
      _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          set a := ‖iteratedFDeriv ℝ i f (A z)‖
          set b := ‖iteratedFDeriv ℝ (n - i) g (B z)‖
          have ha0 : 0 ≤ a := norm_nonneg _
          have hb0 : 0 ≤ b := norm_nonneg _
          have h1 : ‖A z‖ ^ k * a ≤ Cf (k, i) := hCf (k, i) (A z)
          have h2 : b ≤ Cg (0, n - i) := by
            have := hCg (0, n - i) (B z)
            simp only [pow_zero, one_mul] at this
            exact this
          have h3 : a ≤ Cf (0, i) := by
            have := hCf (0, i) (A z)
            simp only [pow_zero, one_mul] at this
            exact this
          have h4 : ‖B z‖ ^ k * b ≤ Cg (k, n - i) := hCg (k, n - i) (B z)
          have hn0 : (0 : ℝ) ≤ n.choose i := by positivity
          have hA' := norm_iter_comp_le A hA f i z
          have hB' := norm_iter_comp_le B hB g (n - i) z
          have hAk : 0 ≤ ‖A z‖ ^ k := by positivity
          have hBk : 0 ≤ ‖B z‖ ^ k := by positivity
          have e1 : ‖A z‖ ^ k * a * b ≤ Cf (k, i) * Cg (0, n - i) :=
            mul_le_mul h1 h2 hb0 ((mul_nonneg hAk ha0).trans h1)
          have e2 : a * (‖B z‖ ^ k * b) ≤ Cf (0, i) * Cg (k, n - i) :=
            mul_le_mul h3 h4 (mul_nonneg hBk hb0) (ha0.trans h3)
          calc ‖z‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ *
                ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖)
              ≤ (‖A z‖ ^ k + ‖B z‖ ^ k) * ((n.choose i : ℝ) * a * b) := by
                refine mul_le_mul hz ?_ (by positivity) (by positivity)
                exact mul_le_mul (mul_le_mul_of_nonneg_left hA' hn0) hB' (norm_nonneg _) (by positivity)
            _ = (n.choose i : ℝ) * (‖A z‖ ^ k * a * b + a * (‖B z‖ ^ k * b)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hn0

@[simp] theorem tens_apply (A : E →L[ℝ] E₁) (B : E →L[ℝ] E₂) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : ∀ z, ‖z‖ ≤ max ‖A z‖ ‖B z‖) (f : SchwartzMap E₁ ℂ) (g : SchwartzMap E₂ ℂ) (z : E) :
    tens A B hA hB hAB f g z = f (A z) * g (B z) := rfl

end Analysis

section Coord

variable {T : Type*} [Fintype T] {r s p : ℕ}

def topL (T : Type*) [Fintype T] (r s p : ℕ) : (T → Fin (r + s) → Fin p → ℂ) →L[ℝ] (T → Fin r → Fin p → ℂ) where
  toFun t := fun τ i j => t τ (Fin.castAdd s i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def botL (T : Type*) [Fintype T] (r s p : ℕ) : (T → Fin (r + s) → Fin p → ℂ) →L[ℝ] (T → Fin s → Fin p → ℂ) where
  toFun t := fun τ i j => t τ (Fin.natAdd r i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem norm_coord_le (t : T → Fin r → Fin p → ℂ) (τ : T) (i : Fin r) (j : Fin p) : ‖t τ i j‖ ≤ ‖t‖ :=
  (norm_le_pi_norm (t τ i) j).trans ((norm_le_pi_norm (t τ) i).trans (norm_le_pi_norm t τ))

theorem norm_le_of_coord {t : T → Fin r → Fin p → ℂ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ τ i j, ‖t τ i j‖ ≤ C) : ‖t‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun τ => (pi_norm_le_iff_of_nonneg hC).2 fun i =>
    (pi_norm_le_iff_of_nonneg hC).2 fun j => h τ i j

theorem norm_topL_le : ‖topL T r s p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by
    rw [one_mul]
    exact norm_le_of_coord (norm_nonneg _) fun τ i j => norm_coord_le t τ _ j

theorem norm_botL_le : ‖botL T r s p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by
    rw [one_mul]
    exact norm_le_of_coord (norm_nonneg _) fun τ i j => norm_coord_le t τ _ j

theorem norm_le_max (t : T → Fin (r + s) → Fin p → ℂ) : ‖t‖ ≤ max ‖topL T r s p t‖ ‖botL T r s p t‖ := by
  refine norm_le_of_coord (le_max_of_le_left (norm_nonneg _)) fun τ i j => ?_
  induction i using Fin.addCases with
  | left a => exact le_max_of_le_left (norm_coord_le (topL T r s p t) τ a j)
  | right b => exact le_max_of_le_right (norm_coord_le (botL T r s p t) τ b j)

end Coord

section Finite

variable {R : Type} {tR : TopologicalSpace R} {r s p : ℕ}

def joinR (a : Fin r → Fin p → R) (b : Fin s → Fin p → R) : Fin (r + s) → Fin p → R :=
  fun i j => Fin.addCases (motive := fun _ => R) (fun u => a u j) (fun v => b v j) i

theorem continuous_joinR :
    Continuous fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.addCases with
  | left a => simp only [joinR, Fin.addCases_left]; fun_prop
  | right b => simp only [joinR, Fin.addCases_right]; fun_prop

theorem sb_tensor {g : (Fin r → Fin p → R) → ℂ} {g' : (Fin s → Fin p → R) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin r → Fin p → R)) (hg' : g' ∈ GlobalTheory.WeilM.SB (Fin s → Fin p → R)) :
    (fun u : Fin (r + s) → Fin p → R =>
      g (fun i j => u (Fin.castAdd s i) j) * g' (fun i j => u (Fin.natAdd r i) j)) ∈
      GlobalTheory.WeilM.SB (Fin (r + s) → Fin p → R) := by
  obtain ⟨hl, hc⟩ := hg
  obtain ⟨hl', hc'⟩ := hg'
  have hT : Continuous fun u : Fin (r + s) → Fin p → R => fun (i : Fin r) (j : Fin p) => u (Fin.castAdd s i) j := by
    fun_prop
  have hB : Continuous fun u : Fin (r + s) → Fin p → R => fun (i : Fin s) (j : Fin p) => u (Fin.natAdd r i) j := by
    fun_prop
  have hlc := (hl.comp_continuous hT).mul (hl'.comp_continuous hB)
  refine ⟨hlc, ?_⟩
  set G : (Fin (r + s) → Fin p → R) → ℂ := fun u =>
    g (fun i j => u (Fin.castAdd s i) j) * g' (fun i j => u (Fin.natAdd r i) j) with hG
  have hlG : IsLocallyConstant G := hlc
  have hclosed : IsClosed (Function.support G) := by
    have : Function.support G = (G ⁻¹' {0})ᶜ := by ext u; simp [Function.mem_support]
    rw [this]
    exact (hlG.isOpen_fiber 0).isClosed_compl
  have hK : IsCompact ((fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2) ''
      (tsupport g ×ˢ tsupport g')) := (IsCompact.prod hc hc').image continuous_joinR
  have hsub : Function.support G ⊆ (fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2) ''
      (tsupport g ×ˢ tsupport g') := by
    intro u hu
    have hu' : G u ≠ 0 := hu
    refine ⟨(fun i j => u (Fin.castAdd s i) j, fun i j => u (Fin.natAdd r i) j), ⟨?_, ?_⟩, ?_⟩
    · exact subset_tsupport _ (left_ne_zero_of_mul hu')
    · exact subset_tsupport _ (right_ne_zero_of_mul hu')
    · funext i j
      induction i using Fin.addCases with
      | left a => simp [joinR]
      | right b => simp [joinR]
  have : HasCompactSupport G := by
    unfold HasCompactSupport tsupport
    rw [hclosed.closure_eq]
    exact hK.of_isClosed_subset hclosed hsub
  exact this

end Finite

theorem schwTensor : SchwTensor := by
  intro D θ _ r s p φ hφ φ' hφ'
  induction hφ using Submodule.span_induction with
  | zero =>
    convert (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).zero_mem using 1
    funext y; simp
  | add a b _ _ ha hb =>
    have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).add_mem ha hb
    convert this using 1
    funext y; simp [add_mul]
  | smul c a _ ha =>
    have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).smul_mem c ha
    convert this using 1
    funext y; simp [mul_assoc]
  | mem a ha =>
    obtain ⟨f, g, hg, rfl⟩ := ha
    induction hφ' using Submodule.span_induction with
    | zero =>
    convert (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).zero_mem using 1
    funext y; simp
    | add a b _ _ ha hb =>
      have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).add_mem ha hb
      convert this using 1
      funext y; simp [mul_add]
    | smul c a _ ha =>
      have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).smul_mem c ha
      convert this using 1
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    | mem b hb =>
      obtain ⟨f', g', hg', rfl⟩ := hb
      refine Submodule.subset_span ⟨tens (topL _ r s p) (botL _ r s p) norm_topL_le norm_botL_le norm_le_max f f',
        _, sb_tensor hg hg', ?_⟩
      funext y
      simp only [tens_apply]
      exact mul_mul_mul_comm _ _ _ _

end GlobalTheory.CompanionTheory.ThTot.SchwT

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheetIntegralProjectionFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem sameOrbit_of_segre_eq {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
    {z z' : (Σ k, κ k) → ℂ} (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) (h : segre z = segre z') :
    SameOrbit z z' := by
  classical
  choose a ha using hz
  have hs : ∀ b : ∀ k, κ k, ∏ k, z ⟨k, b k⟩ = ∏ k, z' ⟨k, b k⟩ := fun b => congrFun h b
  have hpa : ∏ k, z ⟨k, a k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ha k
  have ha' : ∀ k, z' ⟨k, a k⟩ ≠ 0 := fun k => by
    have h' : ∏ k, z' ⟨k, a k⟩ ≠ 0 := hs a ▸ hpa
    exact Finset.prod_ne_zero_iff.1 h' k (Finset.mem_univ _)
  refine ⟨fun k => z ⟨k, a k⟩ / z' ⟨k, a k⟩, fun k => div_ne_zero (ha k) (ha' k), ?_⟩
  funext p
  rcases p with ⟨k, j⟩
  show z ⟨k, j⟩ = z ⟨k, a k⟩ / z' ⟨k, a k⟩ * z' ⟨k, j⟩
  have split : ∀ w : (Σ k, κ k) → ℂ, ∏ l, w ⟨l, Function.update a k j l⟩ =
      w ⟨k, j⟩ * ∏ l ∈ Finset.univ.erase k, w ⟨l, a l⟩ := by
    intro w
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have split0 : ∀ w : (Σ k, κ k) → ℂ, ∏ l, w ⟨l, a l⟩ =
      w ⟨k, a k⟩ * ∏ l ∈ Finset.univ.erase k, w ⟨l, a l⟩ := fun w =>
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)).symm
  have e1 := hs (Function.update a k j)
  rw [split z, split z'] at e1
  have e2 := hs a
  rw [split0 z, split0 z'] at e2
  have hP : ∏ l ∈ Finset.univ.erase k, z ⟨l, a l⟩ ≠ 0 := by
    rw [split0 z] at hpa
    exact right_ne_zero_of_mul hpa
  rw [div_mul_eq_mul_div, eq_div_iff (ha' k)]
  apply mul_right_cancel₀ hP
  linear_combination z' ⟨k, a k⟩ * e1 - z' ⟨k, j⟩ * e2

theorem finsum_fibre_eq (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n)
    [IsClosedImmersion i] (D : ℕ) (Ψ : LinProj n D) (N : Pol n)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1))
    (hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ) {ι : Type}
    (e : ι → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : ι → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (S : ι → Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀))
    (hpc : ∀ l, IsPiece i Ψ N (e l) (Γ l)) (hS : ∀ l, S l ⊆ (e l).source)
    (hd : Pairwise (Function.onFun Disjoint S)) (v : Fin D → ℂ)
    (hcov : ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
        ∃ y, Over i y z ∧ y ∈ ⋃ l, S l)
    (h : (((k : Fin (m + 1)) → Bk n k) → ℂ) → ℝ) (T : ι → ℝ)
    (hT : ∀ l, v ∈ (e l) '' S l → h (segre (Γ l v)) = T l) :
    ∑ᶠ w ∈ fibre (ptIdeal (i (genericPoint X))) Ψ v, h w =
      ∑' l, ((e l) '' S l).indicator (fun _ => T l) v := by
  classical
  set P := ptIdeal (i (genericPoint X)) with hPdef
  let Lv : Set ι := {l | v ∈ (e l) '' S l}
  let f : ι → (((k : Fin (m + 1)) → Bk n k) → ℂ) := fun l => segre (Γ l v)
  have hy : ∀ l ∈ Lv, (e l).symm v ∈ S l ∧ v ∈ (e l).target := by
    rintro l ⟨y, hyS, rfl⟩
    exact ⟨by rw [(e l).left_inv (hS l hyS)]; exact hyS, (e l).map_source (hS l hyS)⟩
  have hpc' : ∀ l ∈ Lv, Over i ((e l).symm v) (Γ l v) ∧ Γ l v ∈ mcPts P ∧
      Ψ (segre (Γ l v)) = Fin.cons 1 v := by
    intro l hl
    obtain ⟨_, _, hp⟩ := hpc l
    obtain ⟨h1, h2, h3, -⟩ := hp v (hy l hl).2
    exact ⟨h1, h2, h3⟩
  have himg : fibre P Ψ v = f '' Lv := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl, hzv⟩
      obtain ⟨y, hyz, hyS⟩ := hcov z hz hzv
      obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hyS
      have hys := hS l hl
      have hvt : (e l) y ∈ (e l).target := (e l).map_source hys
      obtain ⟨_, _, hp⟩ := hpc l
      obtain ⟨o1, o2, o3, -⟩ := hp ((e l) y) hvt
      rw [(e l).left_inv hys] at o1
      have hso : SameOrbit z (Γ l ((e l) y)) :=
        (GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit m n X i y y z _ hyz o1).1 rfl
      have hvv : v = (e l) y := by
        have r1 := ratios_of_proj Ψ hzv
        have r2 := ratios_of_proj Ψ o3
        have r3 := ratios_eq_of_sameOrbit Ψ hso (by rw [o3]; simp)
        rw [← r1, r3, r2]
      refine ⟨l, ⟨y, hl, hvv.symm⟩, ?_⟩
      show segre (Γ l v) = segre z
      rw [hvv]
      obtain ⟨c, hc, hzc⟩ := hso
      have hseg := segre_orbit hzc
      have h1 : (∏ k, c k) = 1 := by
        have h0 := congrArg (fun u => u 0) (congrArg Ψ hseg)
        simp only [map_smul, hzv, o3, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at h0
        exact h0.symm
      rw [hseg, h1, one_smul]
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨_, h2, h3⟩ := hpc' l hl
      exact ⟨Γ l v, h2, rfl, h3⟩
  have hinj : Set.InjOn f Lv := by
    intro l hl l' hl' hll
    obtain ⟨o1, o2, -⟩ := hpc' l hl
    obtain ⟨o1', -, -⟩ := hpc' l' hl'
    have hso := sameOrbit_of_segre_eq o2.1 hll
    have hyy := (GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit m n X i _ _ _ _ o1 o1').2 hso
    by_contra hne
    exact Set.disjoint_left.1 (hd hne) (hy l hl).1 (by rw [hyy]; exact (hy l' hl').1)
  have hfin : (fibre P Ψ v).Finite := ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite _ _ _ _ Ψ hP hΨ v
  have hLfin : Lv.Finite := Set.Finite.of_finite_image (himg ▸ hfin) hinj
  rw [himg, finsum_mem_image hinj]
  have hind : ∀ l, ((e l) '' S l).indicator (fun _ => T l) v = Lv.indicator T l := by
    intro l
    by_cases hl : l ∈ Lv
    · have hl' : v ∈ (e l) '' S l := hl
      simp [hl, hl']
    · have hl' : v ∉ (e l) '' S l := hl
      simp [hl, hl']
  simp_rw [hind]
  rw [tsum_eq_finsum (hLfin.subset Set.support_indicator_subset), ← finsum_mem_def]
  exact finsum_mem_congr rfl fun l hl => hT l hl

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleGluing
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.OneStepProof

open GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem subset_hull (S : Set (Sm E N)) : S ⊆ (hull S : Submodule ℂ (Sm E N)) := by
  intro φ hφ
  refine (Submodule.mem_sInf).2 ?_
  rintro U ⟨hS, -⟩
  exact hS hφ

theorem hull_le {S : Set (Sm E N)} {U : Submodule ℂ (Sm E N)} (hS : S ⊆ U) (hU : IsStable U) : hull S ≤ U :=
  sInf_le ⟨hS, hU⟩

theorem hull_ne_bot {S : Set (Sm E N)} {φ : Sm E N} (hφ : φ ∈ S) (h0 : φ ≠ 0) : hull S ≠ ⊥ := by
  intro h
  have h1 : φ ∈ (hull S : Submodule ℂ (Sm E N)) := subset_hull S hφ
  rw [h] at h1
  exact h0 ((Submodule.mem_bot ℂ).1 h1)

theorem exists_ne_of_hull {S : Set (Sm E N)} (hst : IsStable (hull S)) (T : Sm E N →ₗ[ℂ] Sm E N)
    (he : ∀ o, ∀ χ ∈ hull S, T (act o χ) = act o (T χ)) {ψ : Sm E N} (hψ : ψ ∈ hull S) (hT : T ψ ≠ 0) :
    ∃ φ ∈ S, T φ ≠ 0 := by
  by_contra hcon
  have hz : ∀ φ ∈ S, T φ = 0 := by
    intro φ hφ
    by_contra h
    exact hcon ⟨φ, hφ, h⟩
  have hK : IsStable (hull S ⊓ LinearMap.ker T) := by
    intro o χ hχ
    refine Submodule.mem_inf.2 ⟨hst o χ hχ.1, ?_⟩
    have h0 : T χ = 0 := LinearMap.mem_ker.1 hχ.2
    rw [LinearMap.mem_ker, he o χ hχ.1, h0, map_zero]
  have hS : S ⊆ (hull S ⊓ LinearMap.ker T : Submodule ℂ (Sm E N)) := fun φ hφ =>
    Submodule.mem_inf.2 ⟨subset_hull S hφ, LinearMap.mem_ker.2 (hz φ hφ)⟩
  exact hT (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (hull_le hS hK hψ)).2)

theorem sm_ne_zero {φ : Sm E N} {x : GA E N} (h : φ.1 x ≠ 0) : φ ≠ 0 := by
  rintro rfl
  exact h rfl

theorem oneStep_of_parts : PairSlices → PairRestrict → PairFD → SliceType → PairStep₁ → PairStep₂ → HullGen → CapEquiv →
    OneStep := by
  intro hSl hRe hFD hST hP₁ hP₂ hHG hCE
  intro E _ _ _ a b ι _ K₁ K₂ W₁ W₂ Θ₁ Θ₂ Ω₁ Ω₂ f m₁ m₂ hW₁ hW₂ hF₁ hF₂ hf hT hs₁ hs₂ hA₁ hA₂ hN₁ hN₂ hC₁ hC₂ hI₁ hI₂
    hD₁ hD₂ hP
  obtain ⟨fd₁, fd₂⟩ := hFD E a b ι _ _ f hP
  have ty₁ : ∀ φ ∈ slices₁ f, TypeB K₁ W₁ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).1 φ m h
  have ty₂ : ∀ φ ∈ slices₂ f, TypeB K₂ W₂ φ := by
    rintro φ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ (f i) (hT i)).2 φ m h
  obtain ⟨st₁, fg₁⟩ := hHG E a K₁ W₁ _ ty₁ fd₁
  obtain ⟨st₂, fg₂⟩ := hHG E b K₂ W₂ _ ty₂ fd₂

  have hU₁ : hull (slices₁ f) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hf
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    obtain ⟨φ, hφ⟩ := hs₁ i x.2
    refine hull_ne_bot (φ := φ) ⟨i, x.2, hφ⟩ (sm_ne_zero (x := x.1) ?_)
    rw [hφ]
    exact hx
  obtain ⟨t₁, T₁, r₁, g₁, l₁, e₁, i₁, ψ, hψ, hTψ⟩ :=
    hF₁ _ st₁ hA₁ fg₁ hN₁ hC₁ (fun τ => ⟨m₁ τ, hI₁ τ, hD₁ τ⟩) hU₁
  obtain ⟨φ, ⟨i₀, y, hφ⟩, hTφ⟩ := exists_ne_of_hull st₁ T₁ e₁ hψ hTψ
  obtain ⟨G₁ne, G₁p, G₁t, G₁h⟩ := hP₁ E a b ι K₁ K₂ W₁ W₂ _ t₁.space _ T₁ f hW₁ hW₂ st₁ e₁ i₁ hP hT
    ⟨i₀, y, φ, hφ, hTφ⟩

  have hsl : ∀ i m, sl₂ (ap₁ T₁ (f i)) m ∈ hull (slices₂ f) ∧
      (sl₂ (ap₁ T₁ (f i)) m).1 = fun x => ap₁ T₁ (f i) (m, x) :=
    fun i m => (hSl E a b _ _ _ (G₁p i)).2 m
  have hss : slices₂ (fun i => ap₁ T₁ (f i)) ⊆ (hull (slices₂ f) : Submodule ℂ (Sm E b)) := by
    rintro χ ⟨i, m, h⟩
    have hχ : χ = sl₂ (ap₁ T₁ (f i)) m := Subtype.ext (h.trans (hsl i m).2.symm)
    rw [hχ]
    exact (hsl i m).1
  have hle : hull (slices₂ fun i => ap₁ T₁ (f i)) ≤ hull (slices₂ f) := hull_le hss st₂
  have ty₂' : ∀ χ ∈ slices₂ (fun i => ap₁ T₁ (f i)), TypeB K₂ W₂ χ := by
    rintro χ ⟨i, m, h⟩
    exact (hST E a b K₁ K₂ W₁ W₂ _ (G₁t i)).2 χ m h
  obtain ⟨st₂', fg₂'⟩ := hHG E b K₂ W₂ _ ty₂' (hFD E a b ι _ _ _ G₁p).2
  have G₁p' : ∀ i, ap₁ T₁ (f i) ∈ pairSpace t₁.space (hull (slices₂ fun i => ap₁ T₁ (f i))) := fun i =>
    hRe E a b _ _ _ _ (G₁p i) fun m χ h => subset_hull _ ⟨i, m, h⟩
  have hU₂ : hull (slices₂ fun i => ap₁ T₁ (f i)) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 G₁ne
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hi
    refine hull_ne_bot (φ := sl₂ (ap₁ T₁ (f i)) x.1) ⟨i, x.1, (hsl i x.1).2⟩ (sm_ne_zero (x := x.2) ?_)
    rw [(hsl i x.1).2]
    exact hx

  obtain ⟨t₂, T₂, r₂, g₂, l₂, e₂, i₂, ψ', hψ', hTψ'⟩ :=
    hF₂ _ st₂' (fun χ hχ => hA₂ χ (hle hχ)) fg₂' (fun χ hχ => hN₂ χ (hle hχ))
      (by
        obtain ⟨z, hz, h⟩ := hC₂
        exact ⟨z, hz, fun χ hχ => h χ (hle hχ)⟩)
      (fun τ => ⟨m₂ τ, ⟨(hI₂ τ).1, fun u χ hχ => (hI₂ τ).2 u χ (hle hχ)⟩, hD₂ τ⟩) hU₂
  obtain ⟨χ, ⟨i₃, y₃, hχ⟩, hTχ⟩ := exists_ne_of_hull st₂' T₂ e₂ hψ' hTψ'
  obtain ⟨Gne, Gp, Gt, Gh⟩ := hP₂ E a b ι K₁ K₂ W₁ W₂ _ _ t₂.space T₂ (fun i => ap₁ T₁ (f i)) hW₁ hW₂ st₂' e₂ i₂ G₁p' G₁t
    ⟨i₃, y₃, χ, hχ, hTχ⟩
  exact ⟨t₁, t₂, fun i => ap₂ T₂ (ap₁ T₁ (f i)), T₁ ψ, T₂ ψ', r₁, r₂, g₁, g₂, l₁, l₂, Gne, Gp, Gt,
    fun h c e => Gh h c (G₁h h c e), i₁ ψ hψ, hTψ,
    hCE E a _ T₁ ψ m₁ st₁ e₁ hψ (fun τ u => (hI₁ τ).2 u ψ hψ),
    i₂ ψ' hψ', hTψ',
    hCE E b _ T₂ ψ' m₂ st₂' e₂ hψ' (fun τ u => (hI₂ τ).2 u ψ' (hle hψ'))⟩

end GlobalTheory.CompanionTheory.EGlue.OneStepProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPowStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_card_le_absNorm_pow : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ → Finite {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ∧ Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ≤ Ideal.absNorm 𝔞 ^ m := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard.tor_card | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard.tor_card | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard.tor_card <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivarianceStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_additive_character_equivariance : Ad3.SchwartzSpaceL2.SPsi := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerPsi.sPsi | exact GlobalTheory.CompanionTheory.WhittakerPsi.sPsi | (intros; apply GlobalTheory.CompanionTheory.WhittakerPsi.sPsi <;> assumption)
end

