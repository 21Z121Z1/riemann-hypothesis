import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
import Mathlib.Topology.Algebra.MvPolynomial
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.LemmaDensOfSteps

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def idTerm (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : B.DTerm k r Wp Wq where
  coef := fun _ => ContinuousLinearMap.id ℂ _
  coefAdj := fun _ => ContinuousLinearMap.id ℂ _
  word := []
  word_lie := by simp
  adj_id := by intros; rfl

theorem id_inDDPlus (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) : C6.InDDPlus D fib L 0 0 [idTerm k r Wp Wq] := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT
    constructor <;> intro g₀ _ <;>
      exact ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ _, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  · intro p _ f _ g _
    simp [B.opApply, B.Rw, B.rho, idTerm]
  · intro T hT
    simp only [List.mem_singleton] at hT
    subst hT
    refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, 0, [], ?_, ?_, by simp [idTerm], by simp, ?_⟩
    · exact ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
    · intro l _ _; exact ⟨rfl, rfl⟩
    · intro g _
      simp [C6.monoM, C6.Epart, idTerm]
      rfl

theorem opApply_id (F : B.Mat k r → (Wq →L[ℂ] Wp)) : B.opApply [idTerm k r Wp Wq] F = F := by
  funext g; simp [B.opApply, B.Rw, idTerm]

theorem opOrder_le (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq) (h : C6.InDDPlus D fib L o κ Θ) :
    B.opOrder Θ ≤ o := by
  have hw : ∀ T ∈ Θ, T.word.length ≤ o := fun T hT => by
    obtain ⟨P, a, b, c, es, hP, hab, hlen, hlie, hco⟩ := h.2.2 T hT
    omega
  unfold B.opOrder
  clear h
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (hw T (by simp)) (ih (fun T' hT' => hw T' (by simp [hT'])))

theorem bigPos_sub (D : B.RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : C6.bigPos D ⊆ C6.domL D L :=
  fun _ hg => ⟨hg.1, hg.2.1, fun l _ => hg.2.2 l (Finset.mem_univ l)⟩

theorem smoothCoef_mono {U V : Set (B.Mat k r)} (hUV : U ⊆ V) {Θ : B.DiffOp k r Wp Wq}
    (h : B.SmoothCoef V Θ) : B.SmoothCoef U Θ :=
  fun T hT => ⟨fun g hg => (h T hT).1 g (hUV hg), fun g hg => (h T hT).2 g (hUV hg)⟩

theorem commutes_mono (D : B.RealPlaceData k r Wp Wq) {U V : Set (B.Mat k r)} (hUV : U ⊆ V)
    {Θ : B.DiffOp k r Wp Wq} (h : B.Commutes D V Θ) : B.Commutes D U Θ :=
  fun p hp f hf g hg => h p hp f hf g (hUV hg)

theorem inCC_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m m' : ℕ} (hm : m' ≤ m)
    {F : B.Mat k r → E} (hF : B.InCC A m F) : B.InCC A m' F := by
  obtain ⟨c, hck, hb⟩ := hF
  exact ⟨c, B5.ckOn_mono (by exact_mod_cast hm) hck, fun u v hu hv hl g hg => hb u v hu hv (le_trans hl hm) g hg⟩

theorem gf_cont (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => Gf k r z z' g := by
  obtain ⟨q, _, hq⟩ := P.gram_function_polynomial k r z z'
  have h1 : Continuous fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ) := by
    have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) =
        fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
    rw [e]
    refine (MvPolynomial.continuous_eval q).comp ?_
    refine continuous_pi fun i => ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Sum.elim_inl]; exact continuous_id.matrix_elem a b
    · simp only [Sum.elim_inr]; exact continuous_star.comp (continuous_id.matrix_elem a b)
  have := Complex.continuous_re.comp h1
  refine this.congr fun g => ?_
  simp

theorem rw_zero (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (G : B.Mat k r → (Wq →L[ℂ] Wp))
    (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ v : List (B.Mat k r), (∀ X ∈ v, B.inLie k r X) →
      ∀ g ∈ B.GV k r, Gf k r D.z D.z' g < ε → B.Rw v G g = 0 := by
  intro v
  induction v with
  | nil =>
    intro _ g hg hlt
    by_contra h
    exact absurd (hG g hg h) (not_le.2 hlt)
  | cons X v ih =>
    intro hv g hg hlt
    have hX : B.inLie k r X := hv X (by simp)
    have hv' : ∀ Y ∈ v, B.inLie k r Y := fun Y hY => hv Y (by simp [hY])
    simp only [B.Rw, List.foldr_cons]
    show deriv (fun t : ℝ => List.foldr RdV G v (g * NormedSpace.exp ((t : ℂ) • X))) 0 = 0
    have hc : Continuous fun t : ℝ => Gf k r D.z D.z' (g * NormedSpace.exp ((t : ℂ) • X)) :=
      (gf_cont k r D.z D.z').comp (B5.curve_contDiff g X).continuous
    have h0 : (fun t : ℝ => Gf k r D.z D.z' (g * NormedSpace.exp ((t : ℂ) • X))) 0 < ε := by
      show Gf k r D.z D.z' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) < ε
      rw [B5.curve_zero]; exact hlt
    have hev := (hc.tendsto 0).eventually (gt_mem_nhds h0)
    have : (fun t : ℝ => List.foldr RdV G v (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 :=
      hev.mono fun t ht => ih hv' _ (B5.curve_mem hg hX t) ht
    rw [this.deriv_eq, deriv_const]

theorem op_supp (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (Θ : B.DiffOp k r Wp Wq) (G : B.Mat k r → (Wq →L[ℂ] Wp))
    (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ g ∈ B.GV k r, B.opApply Θ G g ≠ 0 → ε ≤ Gf k r D.z D.z' g := by
  intro g hg hne
  by_contra hlt
  push Not at hlt
  apply hne
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [rw_zero D G hG T.word T.word_lie g hg hlt, map_zero]

theorem cut_supp (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (χ₀ : ℝ → ℝ) (de : ℝ) (L : Finset (Fin (r + 2)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) :
    ∀ g ∈ B.GV k r, C6.cutAll D χ₀ de L F g ≠ 0 → ε ≤ Gf k r D.z D.z' g := by
  intro g hg hne
  apply hF g hg
  intro h0
  apply hne
  simp [C6.cutAll, h0]

end ops

end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

namespace Formalism.FourierDecayAlt.P

open DifferentialOperatorClasses

theorem big_cell_vanishing_of_commute' : C6.BigCellVanishingOfCommute := by
  intro hJ
  obtain ⟨c₃, hc₃, hJ⟩ := hJ
  refine ⟨c₃, hc₃, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D Θ A F hS hC hR hA hF g hg
  obtain ⟨h1, h2, h3⟩ := hJ k r Wp Wq D Θ A F hS hC hA hF
  rw [h3 g hg]
  exact hR _ h1 h2 g hg

theorem vanishing_of_components_true : C6.VanishingOfParts := by
  intro hV0 hBC hBA hVT hLD Cb hCb
  obtain ⟨c₃, hc₃, hV0⟩ := hV0
  obtain ⟨CV, hLD⟩ := hLD
  obtain ⟨C₁, hC₁⟩ := hBA Cb CV hCb
  obtain ⟨C₂, hC₂⟩ := hVT c₃ Cb hc₃ hCb
  refine ⟨3 * (max C₁ 0 + max C₂ 0), ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ D nf fib L o κ N As Θ ε de χ₀ A₀ F γ O hr hε hde hχ hfib hΘ hrad ho hκ hAs1 hAs2
    hA₀ hF hsupp hrel hG

  set n : ℕ := 2 * r + k + 1 with hn
  have hn3 : 3 ≤ n := by omega
  have hn' : 2 * r + 2 ≤ n + 1 := by omega
  have hsq : (n + 1) ^ 2 ≤ 3 * n ^ 2 := by nlinarith
  have hcu : (n + 1) ^ 3 ≤ 3 * n ^ 3 := by nlinarith
  have hA1 : N * (n + 1) ^ 2 ≤ 3 * As := by
    calc N * (n + 1) ^ 2 ≤ N * (3 * n ^ 2) := Nat.mul_le_mul_left _ hsq
      _ = 3 * (N * n ^ 2) := by ring
      _ ≤ 3 * As := Nat.mul_le_mul_left _ hAs1
  have hA2 : (n + 1) ^ 3 ≤ 3 * As := le_trans hcu (Nat.mul_le_mul_left _ hAs2)
  have hNn : (0 : ℝ) ≤ Cb * N := by positivity
  have ho' : (o : ℝ) ≤ Cb * N * ((n + 1 : ℕ) : ℝ) := by
    refine le_trans ho ?_
    have : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    exact mul_le_mul_of_nonneg_left this hNn
  have hP : (0 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 * As := by positivity
  have hAs3 : ((3 * As : ℕ) : ℝ) = 3 * (As : ℝ) := by push_cast; ring
  have hC1 : C₁ * ((r : ℝ) + 1) ^ 4 * ((3 * As : ℕ) : ℝ) ≤ A₀ := by
    rw [hAs3]
    have : C₁ * ((r : ℝ) + 1) ^ 4 * (3 * (As : ℝ)) ≤ 3 * (max C₁ 0 + max C₂ 0) * ((r : ℝ) + 1) ^ 4 * As := by
      have : C₁ * (((r : ℝ) + 1) ^ 4 * As) ≤ (max C₁ 0 + max C₂ 0) * (((r : ℝ) + 1) ^ 4 * As) :=
        mul_le_mul_of_nonneg_right (by have := le_max_left C₁ 0; have := le_max_right C₂ 0; linarith) hP
      nlinarith
    linarith
  have hC2 : C₂ * ((r : ℝ) + 1) ^ 4 * ((3 * As : ℕ) : ℝ) ≤ A₀ := by
    rw [hAs3]
    have : C₂ * ((r : ℝ) + 1) ^ 4 * (3 * (As : ℝ)) ≤ 3 * (max C₁ 0 + max C₂ 0) * ((r : ℝ) + 1) ^ 4 * As := by
      have : C₂ * (((r : ℝ) + 1) ^ 4 * As) ≤ (max C₁ 0 + max C₂ 0) * (((r : ℝ) + 1) ^ 4 * As) :=
        mul_le_mul_of_nonneg_right (by have := le_max_left C₂ 0; have := le_max_right C₁ 0; linarith) hP
      nlinarith
    linarith

  have hBud := hC₁ r (n + 1) N o κ (3 * As) A₀ hr hn' hA1 hA2 ho' hκ hC1
  have hThr := hC₂ r (n + 1) N o (3 * As) A₀ hr hn' hA1 hA2 ho' hC2

  have hcut : B.InCC (A₀ - 3 * ((r : ℝ) + 1) * ((o : ℝ) + 1)) (o + 1) (C6.cutAll D χ₀ de L F) := by
    have := hBC k r Wp Wq D nf fib L 0 0 [idTerm k r Wp Wq] ε de χ₀ A₀ F hε hde hχ hfib
      (id_inDDPlus D fib L) hF hsupp (o + 1)
    rw [opApply_id] at this
    have e : A₀ - ((0 : ℕ) : ℝ) - 3 * ((r : ℝ) + 1) * (((o + 1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)) =
        A₀ - 3 * ((r : ℝ) + 1) * ((o : ℝ) + 1) := by push_cast; ring
    rw [e] at this
    exact this
  have hord := opOrder_le D fib L o κ Θ hΘ

  have hbig : ∀ g ∈ C6.bigPos D, B.JF D (B.opApply Θ (C6.cutAll D χ₀ de L F)) g = 0 := by
    refine hV0 k r Wp Wq D Θ (A₀ - 3 * ((r : ℝ) + 1) * ((o : ℝ) + 1)) (C6.cutAll D χ₀ de L F)
      (smoothCoef_mono (bigPos_sub D L) hΘ.1) (commutes_mono D (bigPos_sub D L) hΘ.2.1) hrad ?_
      (inCC_mono (by omega) hcut)
    have h1 : (B.opOrder Θ : ℝ) ≤ o := by exact_mod_cast hord
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    have h3 : (B.opOrder Θ : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1 ≤ (o : ℝ) + r * ((n + 1 : ℕ) : ℝ) + 1 := by
      have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) r)
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ c₃ * ((r : ℝ) + 1) ^ 2)
    linarith

  have hcl := hBC k r Wp Wq D nf fib L o κ Θ ε de χ₀ A₀ F hε hde hχ hfib hΘ hF hsupp (C6.mmV CV r)
  refine hLD k r Wp Wq D (A₀ - κ - 3 * ((r : ℝ) + 1) * (((C6.mmV CV r : ℕ) : ℝ) + o)) ε (C6.mmV CV r)
    (B.opApply Θ (C6.cutAll D χ₀ de L F)) γ O hr hε ?_ le_rfl hcl
    (op_supp D Θ _ (cut_supp D χ₀ de L F hsupp)) hbig hrel hG
  refine le_trans ?_ hBud
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (α := ℝ) r)
  unfold C6.AV
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (α := ℝ) CV)
  have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have h0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (r : ℝ) ^ 3)
  have := mul_le_mul h2 h2 h0 (by positivity)
  nlinarith

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CasimirEigenvalueCoefficients
section
open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Qb1

variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]

def SV (σ : Mx k r → (Vs →L[ℂ] Vs)) (w : Vs) : Prop := CkOn ⊤ (GV k r) (fun g => σ g w)

theorem one_mem_GV : (1 : Mx k r) ∈ GV k r := by
  show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem ckOn_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (h : CkOn m (GV k r) f) : CkOn m (GV k r) f' := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  exact ⟨U, F, a, b, c, fun g hg hgG => (he g hgG).symm.trans (d g hg hgG)⟩

theorem ckOn_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (h : CkOn m (GV k r) f) (h' : CkOn m (GV k r) f') : CkOn m (GV k r) (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  obtain ⟨U', F', a', b', c', d'⟩ := h' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, a.inter a', ⟨b, b'⟩, ?_, ?_⟩
  · exact (c.mono Set.inter_subset_left).add (c'.mono Set.inter_subset_right)
  · intro g hg hgG
    show f g + f' g = F g + F' g
    rw [d g hg.1 hgG, d' g hg.2 hgG]

theorem ckOn_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f : Mx k r → E} (s : ℂ)
    (h : CkOn m (GV k r) f) : CkOn m (GV k r) (fun g => s • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  refine ⟨U, fun g => s • F g, a, b, ?_, ?_⟩
  · exact c.const_smul s
  · intro g hg hgG
    show s • f g = s • F g
    rw [d g hg hgG]

theorem sv_add {σ : Mx k r → (Vs →L[ℂ] Vs)} {w w' : Vs} (h : SV σ w) (h' : SV σ w') : SV σ (w + w') := by
  unfold SV at *
  have := ckOn_add h h'
  simpa only [map_add] using this

theorem sv_smul {σ : Mx k r → (Vs →L[ℂ] Vs)} {w : Vs} (s : ℂ) (h : SV σ w) : SV σ (s • w) := by
  unfold SV at *
  have := ckOn_smul s h
  simpa only [map_smul] using this

theorem sv_zero (σ : Mx k r → (Vs →L[ℂ] Vs)) : SV σ (0 : Vs) := by
  have := sv_smul (σ := σ) (w := (0 : Vs)) 0 (by
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun g _ _ => by simp⟩)
  simpa using this

variable {σ : Mx k r → (Vs →L[ℂ] Vs)}

theorem hasDerivAt_orbit (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    HasDerivAt (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) w) (σ g (dRep σ X w)) 0 := by
  have h1 := B5.rdV_hasDerivAt (B5.ckOn_mono (m := 1) le_top hw) (one_mem_GV (k := k) (r := r)) hX
  simp only [Matrix.one_mul] at h1
  have hd : dRep σ X w = RdV X (fun g => σ g w) 1 := h1.deriv
  rw [hd]
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 g hg _ (B5.exp_mem hX t)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', this,
    ContinuousLinearMap.comp_apply]

theorem rdV_orbit (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X (fun x => σ x w) g = σ g (dRep σ X w) :=
  (hasDerivAt_orbit hrep hw hX hg).deriv

theorem rdV_coeff (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) (ℓ : Vs →L[ℂ] ℂ) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X (fun x => ℓ (σ x w)) g = ℓ (σ g (dRep σ X w)) := by
  have h := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_orbit hrep hw hX hg)
  exact h.deriv

theorem sv_dRep (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) : SV σ (dRep σ X w) := by
  have h : CkOn ⊤ (GV k r) (RdV X (fun x => σ x w)) :=
    B5.ckOn_RdV (m := ⊤) hX (by rw [top_add]; exact hw)
  exact ckOn_congr (fun g hg => rdV_orbit hrep hw hX hg) h

theorem lie1 (Z : Mx k r) : inLie k r (hpart1 (Hpk k r) Z) := Qx2.hpart1_lie Z

theorem lie2 (Z : Mx k r) : inLie k r (hpart2 (Hpk k r) Z) := Qx2.hpart2_lie Z

theorem sv_ecRep (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (Z : Mx k r) :
    SV σ (EcRep (Hpk k r) σ Z w) :=
  sv_add (sv_dRep hrep hw (lie1 Z)) (sv_smul _ (sv_dRep hrep hw (lie2 Z)))

def stepV (σ : Mx k r → (Vs →L[ℂ] Vs)) (c : ℂ) (a b : Fin (2 * r + k + 1)) (y : Vs) : Vs :=
  (if a = b then c • y else 0) + EcRep (Hpk k r) σ (Matrix.single a b 1) y

theorem sv_stepV (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (c : ℂ) (a b : Fin (2 * r + k + 1)) :
    SV σ (stepV σ c a b w) := by
  unfold stepV
  refine sv_add ?_ (sv_ecRep hrep hw _)
  split_ifs
  · exact sv_smul c hw
  · exact sv_zero σ

theorem top_coeff (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) (ℓ : Vs →L[ℂ] ℂ) (c : ℂ)
    (a b : Fin (2 * r + k + 1)) {g : Mx k r} (hg : g ∈ GV k r) :
    QuantumDeterminants.Top (EH k r) c a b (fun x => ℓ (σ x w)) g = ℓ (σ g (stepV σ c a b w)) := by
  unfold QuantumDeterminants.Top stepV EcRep
  simp only [EH, EabH]
  rw [rdV_coeff hrep hw (lie1 _) ℓ hg, rdV_coeff hrep hw (lie2 _) ℓ hg]
  split_ifs <;> simp [map_add, map_smul]

theorem rdV_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) {X : Mx k r} (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact he _ (B5.curve_mem hg hX t)

theorem top_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (c : ℂ) (a b : Fin (2 * r + k + 1)) {g : Mx k r} (hg : g ∈ GV k r) :
    QuantumDeterminants.Top (EH k r) c a b f g = QuantumDeterminants.Top (EH k r) c a b f' g := by
  unfold QuantumDeterminants.Top
  simp only [EH, EabH]
  rw [he g hg, rdV_local he (lie1 _) hg, rdV_local he (lie2 _) hg]

theorem steps (hrep : IsCRepOn (UH (Hpk k r)) σ) (ℓ : Vs →L[ℂ] ℂ) :
    ∀ (L : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (w : Vs), SV σ w →
      SV σ (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w) ∧
      ∀ g ∈ GV k r, (L.map fun p => QuantumDeterminants.Top (EH k r) p.1 p.2.1 p.2.2).foldr (fun T h => T h) (fun x => ℓ (σ x w)) g =
        ℓ (σ g (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w)) := by
  intro L
  induction L with
  | nil => intro w hw; exact ⟨hw, fun g _ => rfl⟩
  | cons p L ih =>
    intro w hw
    obtain ⟨h1, h2⟩ := ih w hw
    refine ⟨sv_stepV hrep h1 _ _ _, fun g hg => ?_⟩
    simp only [List.map_cons, List.foldr_cons]
    rw [top_local (f' := fun x => ℓ (σ x (L.foldr (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w))) h2 _ _ _ hg]
    exact top_coeff hrep h1 ℓ _ _ _ hg

theorem qminor_coeff (hrep : IsCRepOn (UH (Hpk k r)) σ) (ℓ : Vs →L[ℂ] ℂ) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) {w : Vs} (hw : SV σ w) {g : Mx k r} (hg : g ∈ GV k r) :
    qminorOp (EH k r) a b u (fun x => ℓ (σ x w)) g =
      ℓ (σ g (qmF (fun a b => EcRep (Hpk k r) σ (Matrix.single a b 1)) a b u w)) := by
  unfold qminorOp qmF
  rw [Finset.sum_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Pi.smul_apply, map_smul, map_smul]
  congr 1
  have e1 : (List.ofFn fun i : Fin t => QuantumDeterminants.Top (EH (E := ℂ) k r) (u - ((i : ℕ) : ℂ)) (a (τ i)) (b i)) =
      (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).map
        (fun p => QuantumDeterminants.Top (EH (E := ℂ) k r) p.1 p.2.1 p.2.2) := by
    rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun i : Fin t => fun y : Vs =>
      (if a (τ i) = b i then (u - ((i : ℕ) : ℂ)) • y else 0) +
        EcRep (Hpk k r) σ (Matrix.single (a (τ i)) (b i) 1) y).foldr (fun T h => T h) w =
      (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).foldr
        (fun p y => stepV σ p.1 p.2.1 p.2.2 y) w := by
    have e3 : (List.ofFn fun i : Fin t => fun y : Vs =>
        (if a (τ i) = b i then (u - ((i : ℕ) : ℂ)) • y else 0) +
          EcRep (Hpk k r) σ (Matrix.single (a (τ i)) (b i) 1) y) =
        (List.ofFn fun i : Fin t => ((u - ((i : ℕ) : ℂ)), a (τ i), b i)).map
          (fun (p : ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (y : Vs) => stepV σ p.1 p.2.1 p.2.2 y) := by
      rw [List.map_ofFn]; rfl
    rw [e3, List.foldr_map]
  rw [e1, e2]
  exact (steps hrep ℓ _ w hw).2 g hg

theorem qmF_reindex {X : Type*} [AddCommGroup X] [Module ℂ X] {n : ℕ} (Eop : Fin n → Fin n → X → X) (u : ℂ) (x : X) :
    ∀ (t : ℕ) (h : t = n) (a : Fin t → Fin n), (∀ j, (a j).val = j.val) →
      qmF Eop a a u x = qmF Eop (id : Fin n → Fin n) id u x := by
  intro t h a ha
  subst h
  have : a = id := funext fun j => Fin.ext (ha j)
  subst this
  rfl

end Qb1

theorem casimir_eigenvalue_coefficients : Formalism.FourierDecayAlt.Q.EigenCoeff := by
  intro Vs _ _ k r σ v lam hrep hsm hC ℓ Y g hg
  have hw : Qb1.SV σ v := by
    intro g₀ hg₀
    have hmem : ∀ x ∈ GV k r, x ∈ Glev k r 0 := fun x hx =>
      ⟨hx, fun a ha => absurd ha (by simp)⟩
    obtain ⟨U, F, a, b, c, d⟩ := hsm g₀ ⟨hmem g₀ hg₀, trivial⟩
    exact ⟨U, F, a, b, c, fun x hx hxG => d x hx (hmem x hxG)⟩
  unfold CV capL
  rw [Qb1.qminor_coeff hrep ℓ _ _ _ hw hg,
    Qb1.qmF_reindex _ _ _ (mdim k r 0) (by simp [mdim]) (posL k r 0) (fun j => by simp [posL]), hC,
    map_smul, map_smul]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp only [uC, mdim, Fin.val_zero, Nat.sub_zero]
  push_cast
  ring

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.InnerDensityOfAveraging
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem inner_density_of_averaging : Formalism.FourierDecayAlt.DensityAveraging.DensStepJOfAvg := by
  rintro ⟨C0, hI⟩ hAvg
  refine ⟨C0, ?_⟩
  intro CV hCV k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ H hrel hG hc hMore
  obtain ⟨S, hS⟩ := hI CV hCV k r Wp Wq D A ε mm F' γ H hrel hG hc
  obtain ⟨C', x₁, hb⟩ := hS hMore
  exact S.tie (hAvg S.β S.β_ne S.V S.p S.s S.w S.a C' x₁ S.w_inj hb S.k₀)

theorem top_density_of_averaging : Formalism.FourierDecayAlt.DensityAveraging.DensStepTopOfAvg := by
  rintro ⟨C0, hI⟩ hAvg
  refine ⟨C0, ?_⟩
  intro CV hCV k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ H hrel hG hc hMore
  obtain ⟨S, hS⟩ := hI CV hCV k r Wp Wq D A ε mm F' γ H hrel hG hc
  obtain ⟨C', x₁, hb⟩ := hS hMore
  exact S.tie (hAvg S.β S.β_ne S.V S.p S.s S.w S.a C' x₁ S.w_inj hb S.k₀)

def averagingDatumInhabited {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Formalism.FourierDecayAlt.DensityAveraging.AvgDatum D F' γ where
  V := ℂ
  p := normSeminorm ℂ ℂ
  β := 1
  β_ne := one_ne_zero
  s := 1
  w := fun _ => 0
  w_inj := fun i j _ => Subsingleton.elim i j
  a := fun _ => 1
  k₀ := 0
  tie := fun h => absurd h (by simp)

end Formalism.FourierDecayAlt.P
end
end

