import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFdGramCut
section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

section
variable {k r : ℕ}

def Rel (z z' : Fin (2 * r + k + 1) → ℂ) (a b : B.Mat k r) : Prop :=
  ∃ n ∈ C2.N0set k r z, ∃ m ∈ C2.N0set k r z, ∃ n' ∈ C2.N0set k r z', ∃ m' ∈ C2.N0set k r z',
  ∃ c ∈ UWset k r z, ∃ c' ∈ UWset k r z',
    b = c * (n⁻¹ * a * n') * c' ∧ c * (m⁻¹ * a * m') * c' = a

def nrm (T : B.Mat k r → B.Mat k r × B.Mat k r) (g : B.Mat k r) : B.Mat k r := (T g).1 * g * (T g).2

end

def GramSlice : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
  ∃ T : B.Mat k r → B.Mat k r × B.Mat k r,
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → (T g).1 ∈ UWset k r z ∧ (T g).2 ∈ UWset k r z') ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, T (n⁻¹ * g * n') = T g) ∧
    (∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r, 0 < Gf k r z z' g₁ → Zhat k r z z' g₁ = Zhat k r z z' g₂ →
      Rel z z' (nrm T g₁) (nrm T g₂)) ∧
    (∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ → ∃ (O : Set (B.Mat k r)) (Tl : B.Mat k r → B.Mat k r × B.Mat k r),
      IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Tl O ∧
      ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
        (Tl g).1 ∈ UWset k r z ∧ (Tl g).2 ∈ UWset k r z' ∧ Rel z z' (nrm Tl g) (nrm T g))

def SmoothRep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq),
    (∀ h₀ ∈ UWset k r D.z, ∃ (O : Set (B.Mat k r)) (P : B.Mat k r → (Wp →L[ℂ] Wp)),
      IsOpen O ∧ h₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P O ∧ ∀ h ∈ O, h ∈ UWset k r D.z → P h = D.π h) ∧
    (∀ h₀ ∈ UWset k r D.z', ∃ (O : Set (B.Mat k r)) (P : B.Mat k r → (Wq →L[ℂ] Wq)),
      IsOpen O ∧ h₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P O ∧ ∀ h ∈ O, h ∈ UWset k r D.z' → P h = D.π' h)

def FibEquivU : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), ∀ c ∈ UWset k r D.z, ∀ c' ∈ UWset k r D.z',
      fibInt D μ0 μ0' F (c * g * c') = (D.π c).comp ((fibInt D μ0 μ0' F g).comp (D.π' c'))

def FiberIntegralUnipotentInvariant : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), ∀ n ∈ C2.N0set k r D.z, ∀ n' ∈ C2.N0set k r D.z',
      fibInt D μ0 μ0' F (n⁻¹ * g * n') = fibInt D μ0 μ0' F g

section
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

def repE (A : W →L[ℂ] W) : W ≃L[ℂ] W := by
  classical
  exact if hA : ∀ v, ‖A v‖ = ‖v‖ then
    (LinearEquiv.ofInjectiveEndo (A : W →ₗ[ℂ] W) (fun v w h => by
      have h1 := hA (v - w)
      have h2 : A (v - w) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
      rw [h2, norm_zero] at h1
      exact sub_eq_zero.mp (norm_eq_zero.mp h1.symm))).toContinuousLinearEquiv
  else ContinuousLinearEquiv.refl ℂ W

theorem repE_coe (A : W →L[ℂ] W) (hA : ∀ v, ‖A v‖ = ‖v‖) : ((repE A : W ≃L[ℂ] W) : W →L[ℂ] W) = A := by
  unfold repE
  rw [dif_pos hA]
  ext v
  rfl

end

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem fib_rel (hE : FibEquivU) (hN : FiberIntegralUnipotentInvariant) (D : B.RealPlaceData k r Wp Wq) {μ0 μ0' : Measure (Mt k r)}
    (h0 : B.IsHaarOn (C2.N0set k r D.z) μ0) (h0' : B.IsHaarOn (C2.N0set k r D.z') μ0')
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) {a b : B.Mat k r} (hR : Rel D.z D.z' a b) :
    fibInt D μ0 μ0' F b = fibInt D μ0 μ0' F a := by
  obtain ⟨n, hn, m, hm, n', hn', m', hm', c, hc, c', hc', hb, ha⟩ := hR
  have hE' := hE
  unfold FibEquivU at hE'
  have hN' := hN
  unfold FiberIntegralUnipotentInvariant at hN'
  have e1 := hE' k r Wp Wq D μ0 μ0' h0 h0' F (n⁻¹ * a * n') c hc c' hc'
  have e2 := hE' k r Wp Wq D μ0 μ0' h0 h0' F (m⁻¹ * a * m') c hc c' hc'
  rw [hN' k r Wp Wq D μ0 μ0' h0 h0' F a n hn n' hn'] at e1
  rw [hN' k r Wp Wq D μ0 μ0' h0 h0' F a m hm m' hm', ha] at e2
  rw [hb, e1, ← e2]

theorem one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  simp [UWset, UH]

theorem gf_N (D : B.RealPlaceData k r Wp Wq) {g n n' : B.Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) :
    Gf k r D.z D.z' (n⁻¹ * g * n') = Gf k r D.z D.z' g := by
  have hs : n⁻¹ ∈ Sset k r D.z := by
    simp only [Sset, Set.mem_setOf_eq]
    exact ⟨1, one_mem_UW D.z, n⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn, by rw [one_mul]⟩
  have hs' : n' ∈ Sset k r D.z' := by
    simp only [Sset, Set.mem_setOf_eq]
    exact ⟨1, one_mem_UW D.z', n', hn', by rw [one_mul]⟩
  have hD := Formalism.QuantumDeterminants.dInv
  unfold DInv at hD
  simp only [Gf, hD k r D.z D.z' D.z_mem D.z'_mem _ hs _ hs' g]

theorem gf_zhat (z z' : Fin (2 * r + k + 1) → ℂ) {g₁ g₂ : B.Mat k r} (hZ : Zhat k r z z' g₁ = Zhat k r z z' g₂) :
    Gf k r z z' g₁ = Gf k r z z' g₂ := by
  simp only [Gf, Dmin, hZ]

end

theorem fdGram_of (hS : GramSlice) (hR : SmoothRep) (hE : FibEquivU) (hN : FiberIntegralUnipotentInvariant) : FdGram := by
  unfold FdGram
  intro k r Wp Wq _ _ _ _ _ _ D μ0 μ0' hr h0 h0'
  have hS' := hS
  unfold GramSlice at hS'
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ :=
    hS' k r D.z D.z' D.k_pos hr ⟨D.z_mem, D.T_pos⟩ ⟨D.z'_mem, D.T'_pos⟩
  have hR' := hR
  unfold SmoothRep at hR'
  have hE' := hE
  unfold FibEquivU at hE'
  have key : ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c c' g : B.Mat k r), c ∈ UWset k r D.z →
      c' ∈ UWset k r D.z' →
      ((repE (D.π c) : Wp →L[ℂ] Wp)).comp ((fibInt D μ0 μ0' F g).comp (repE (D.π' c') : Wq →L[ℂ] Wq)) =
        fibInt D μ0 μ0' F (c * g * c') := by
    intro F c c' g hc hc'
    rw [repE_coe _ (D.π_unitary c hc), repE_coe _ (D.π'_unitary c' hc'),
      hE' k r Wp Wq D μ0 μ0' h0 h0' F g c hc c' hc']
  simp only [IsFrameAlg, FdLocal, frVal]
  refine ⟨fun g => (repE (D.π (T g).1), repE (D.π' (T g).2)), ⟨?_, ?_⟩, ?_⟩
  · intro g hg hG n hn n' hn'
    refine ⟨by rw [gf_N D hn hn']; exact hG, ?_⟩
    dsimp only
    rw [hT2 g hg hG n hn n' hn']
  · intro F g₁ hg₁ g₂ hg₂ hG hZ
    have hG₂ : 0 < Gf k r D.z D.z' g₂ := by rw [← gf_zhat D.z D.z' hZ]; exact hG
    obtain ⟨hc₁, hc₁'⟩ := hT1 g₁ hg₁ hG
    obtain ⟨hc₂, hc₂'⟩ := hT1 g₂ hg₂ hG₂
    dsimp only
    rw [key F _ _ g₁ hc₁ hc₁', key F _ _ g₂ hc₂ hc₂']
    exact (fib_rel hE hN D h0 h0' F (hT3 g₁ hg₁ g₂ hg₂ hG hZ)).symm
  · intro g₀ hg₀ hG₀
    obtain ⟨O₁, Tl, hO₁, hg₀O, hTl, hTlP⟩ := hT4 g₀ hg₀ hG₀
    obtain ⟨hu₀, hu₀', -⟩ := hTlP g₀ hg₀O hg₀ hG₀
    obtain ⟨O₂, P, hO₂, hmem₂, hP, hPeq⟩ := (hR' k r Wp Wq D).1 _ hu₀
    obtain ⟨O₃, P', hO₃, hmem₃, hP', hPeq'⟩ := (hR' k r Wp Wq D).2 _ hu₀'
    have hc1 : ContinuousOn (Prod.fst ∘ Tl) O₁ := continuous_fst.comp_continuousOn hTl.continuousOn
    have hc2 : ContinuousOn (Prod.snd ∘ Tl) O₁ := continuous_snd.comp_continuousOn hTl.continuousOn
    have hd1 := contDiff_fst.comp_contDiffOn hTl
    have hd2 := contDiff_snd.comp_contDiffOn hTl
    have hO : IsOpen ((O₁ ∩ (Prod.fst ∘ Tl) ⁻¹' O₂) ∩ (Prod.snd ∘ Tl) ⁻¹' O₃) :=
      (hc2.mono Set.inter_subset_left).isOpen_inter_preimage (hc1.isOpen_inter_preimage hO₁ hO₂) hO₃
    refine ⟨(O₁ ∩ (Prod.fst ∘ Tl) ⁻¹' O₂) ∩ (Prod.snd ∘ Tl) ⁻¹' O₃, fun g => P (Tl g).1,
      fun g => P' (Tl g).2, hO, ⟨⟨hg₀O, hmem₂⟩, hmem₃⟩, ?_, ?_, ?_⟩
    · exact hP.comp (hd1.mono fun x hx => hx.1.1) (fun x hx => hx.1.2)
    · exact hP'.comp (hd2.mono fun x hx => hx.1.1) (fun x hx => hx.2)
    · intro g hgO hgV hG F
      obtain ⟨hu, hu', hrel⟩ := hTlP g hgO.1.1 hgV hG
      obtain ⟨hc, hc'⟩ := hT1 g hgV hG
      dsimp only
      rw [key F _ _ g hc hc', hPeq (Tl g).1 hgO.1.2 hu, hPeq' (Tl g).2 hgO.2 hu',
        ← hE' k r Wp Wq D μ0 μ0' h0 h0' F g _ hu _ hu']
      exact fib_rel hE hN D h0 h0' F hrel

end PI.UnitaryGroupMassFormula.DLm.Gram
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundH
section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def skewOf {r : ℕ} (T : Fin r → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => ((T a b - T b a : ℝ) : ℂ) + Complex.I * ((T a b + T b a : ℝ) : ℂ)

def Pz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  1 - ((∑ j, Complex.normSq (zW k r z j) : ℝ) : ℂ)⁻¹ • Matrix.vecMulVec (zW k r z) (star (zW k r z))

def psiZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : (Fin r → Fin (k + 1) → ℂ) × (Fin r → Fin r → ℝ)) : Mt k r :=
  unipotentBlockMatrix k r (Matrix.of p.1 * Pz k r z) (skewOf p.2)

def rhoZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (B0 : Fin r → Fin (k + 1) → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∑ a, Complex.normSq ((Matrix.of B0 *ᵥ zW k r z) a))))

def nuZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Measure (Mt k r) :=
  (((volume : Measure (Fin r → Fin (k + 1) → ℂ)).withDensity (rhoZ k r z)).prod
    (volume : Measure (Fin r → Fin r → ℝ))).map (psiZ k r z)

def UnipotentHaarMultipleExplicit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ0 : Measure (Mt k r)), 1 ≤ k → 1 ≤ r → C2.StdZ k r z →
    B.IsHaarOn (C2.N0set k r z) μ0 → ∃ c : ℝ≥0, 0 < c ∧ nuZ k r z = c • μ0

def ExplicitUnipotentVolumeBound : Prop :=
  ∃ C : ℕ, ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
      ∀ v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ, ε ≤ Complex.normSq (Mf k r z v).det → ∀ R : ℝ, 0 ≤ R →
        nuZ k r z {x | (Matrix.of x : B.Mat k r) ∈ C2.N0set k r z ∧
            tN (fun b => (Matrix.of x : B.Mat k r)⁻¹ *ᵥ v b) ≤ R} ≤
          ENNReal.ofReal (K * (1 + zN (Mf k r z v)) ^ ((C : ℝ) * XF k r) * (1 + R) ^ ((C : ℝ) * XF k r))

end PI.UnitaryGroupMassFormula.DLm
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFlWitt
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Lifts

namespace FLW

variable {n : ℕ}

theorem herm_add_l (H : Matrix (Fin n) (Fin n) ℂ) (u u' w : Fin n → ℂ) :
    herm H (u + u') w = herm H u w + herm H u' w := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

theorem herm_smul_l (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u w : Fin n → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_add_r (H : Matrix (Fin n) (Fin n) ℂ) (u w w' : Fin n → ℂ) :
    herm H u (w + w') = herm H u w + herm H u w' := by
  simp [herm, star_add, add_dotProduct]

theorem herm_smul_r (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u w : Fin n → ℂ) :
    herm H u (c • w) = star c * herm H u w := by
  simp [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem unitary_of_herm (H M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ u v, herm H (M *ᵥ u) (M *ᵥ v) = herm H u v) :
    Mᴴ * H * M = H := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [herm, Matrix.mulVec_single_one] at this
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  convert this using 1
  · simp [dotProduct, Matrix.mulVec, Matrix.col, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.sum_comm]
  · simp [dotProduct, Matrix.mulVec, Pi.single_apply]

end FLW

theorem wittHpk (k r : ℕ) {ι : Type} [Fintype ι] (x y : ι → Fin (2 * r + k + 1) → ℂ)
    (hx : LinearIndependent ℂ x) (hy : LinearIndependent ℂ y)
    (hg : ∀ i j, herm (Hpk k r) (x i) (x j) = herm (Hpk k r) (y i) (y j)) :
    ∃ g ∈ B.GV k r, ∀ i, g *ᵥ x i = y i := by
  set H := Hpk k r with hHdef
  have hHh : Hᴴ = H := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hHH : H * H = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  let Bf : (Fin (2 * r + k + 1) → ℂ) →ₗ⋆[ℂ] (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun u v => herm H v u)
      (fun u u' v => FLW.herm_add_r H v u u')
      (fun c u v => by rw [FLW.herm_smul_r, smul_eq_mul]; rfl)
      (fun u v v' => FLW.herm_add_l H v v' u)
      (fun c u v => by rw [FLW.herm_smul_l, smul_eq_mul]; rfl)
  have hB : ∀ u v, Bf u v = herm H v u := fun u v => rfl
  have hsym : ∀ a b, star (Bf a b) = Bf b a := by
    intro a b
    rw [hB, hB, ggHerm_swap H hHh a b]
  have hnd : ∀ a, (∀ b, Bf a b = 0) → a = 0 := by
    intro a ha
    have h0 := ha (H *ᵥ a)
    rw [hB] at h0
    simp only [herm, Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec] at h0
    have h1 : ∑ i, Complex.normSq (a i) = 0 := by
      have : (∑ i, Complex.normSq (a i) : ℂ) = star a ⬝ᵥ a := by
        simp [dotProduct, Complex.mul_conj, mul_comm]
      exact_mod_cast this.trans h0
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (a j))).1 h1 i (Finset.mem_univ _)
    simpa using this
  let U := Submodule.span ℂ (Set.range x)
  let bU : Module.Basis ι ℂ U := Module.Basis.span hx
  have hbU : ∀ a, (bU a : Fin (2 * r + k + 1) → ℂ) = x a := fun a => by
    show ((Module.Basis.span hx a : U) : Fin (2 * r + k + 1) → ℂ) = x a
    rw [Module.Basis.span_apply]
  let f : U →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) := bU.constr ℂ y
  have hf : ∀ a, f (bU a) = y a := fun a => bU.constr_basis ℂ y a
  have hfsum : ∀ u : U, f u = ∑ a, bU.repr u a • y a := by
    intro u
    conv_lhs => rw [← bU.sum_repr u]
    rw [map_sum]; simp only [map_smul, hf]
  have husum : ∀ u : U, (u : Fin (2 * r + k + 1) → ℂ) = ∑ a, bU.repr u a • x a := by
    intro u
    conv_lhs => rw [← bU.sum_repr u]
    rw [Submodule.coe_sum]; simp only [Submodule.coe_smul, hbU]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hfsum] at hu
    have hc := Fintype.linearIndependent_iff.mp hy _ hu
    have : bU.repr u = 0 := by ext a; simp [hc a]
    simpa using this
  have hsum_l : ∀ (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      herm H (∑ a, c a • v a) w = ∑ a, c a * herm H (v a) w := by
    intro c v w
    simp [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have hsum_r : ∀ (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      herm H w (∑ a, c a • v a) = ∑ a, star (c a) * herm H w (v a) := by
    intro c v w
    simp [herm, star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hisom : ∀ u v : U, Bf (f u) (f v) = Bf u v := by
    intro u v
    rw [hB, hB, hfsum, hfsum, husum, husum, hsum_l, hsum_l]
    apply Finset.sum_congr rfl; intro a _
    rw [hsum_r, hsum_r]
    congr 1
    apply Finset.sum_congr rfl; intro b _
    rw [hg]
  obtain ⟨g, hgB, hgf⟩ := _root_.witt_extension_theorem ℂ (Fin (2 * r + k + 1) → ℂ) Bf hsym hnd U f hinj hisom
  refine ⟨LinearMap.toMatrix' (g : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ)), ?_, fun i => ?_⟩
  · show _ * H * _ = H
    apply FLW.unitary_of_herm
    intro u v
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    have := hgB v u
    rw [hB, hB] at this
    exact this
  · rw [LinearMap.toMatrix'_mulVec]
    have := hgf (bU i)
    rw [hbU, hf] at this
    exact this

end PI.UnitaryGroupMassFormula.DLm.Lifts
end
end

