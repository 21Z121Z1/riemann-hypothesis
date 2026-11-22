import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0158
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBLiftV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsotropicNormalFormFullStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ImageProdLoc
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mem_Wb_iff (S : C.HidaSetting E Wp Wq) (m : ℕ) (u : S.W) : u ∈ S.base.Wb m ↔ u ∈ S.base.Wall ∧ S.base.cnt u ≤ m :=
  Finset.mem_filter

theorem Wb_mono (S : C.HidaSetting E Wp Wq) {m m' : ℕ} (h : m ≤ m') : S.base.Wb m ⊆ S.base.Wb m' := by
  intro u hu
  rw [mem_Wb_iff] at hu ⊢
  exact ⟨hu.1, hu.2.trans h⟩

theorem prob_sum_sub {W : Type} {A Wd : Finset W} {θ : W → ℝ} (hθ : TB.IsProb A θ) (h : A ⊆ Wd) :
    ∑ u ∈ Wd, θ u = 1 := by
  rw [← hθ.2.2]
  exact (Finset.sum_subset h fun u _ hu => hθ.2.1 u hu).symm

theorem blockPSD_same {α : Type} (Y : Finset α) (κ : α → α → ℂ) (hκ : TB.PSDOn Y κ) : KB.BlockPSD Y Y κ κ κ := by
  rw [blockPSD_iff]
  have := JCx1.decay.psd_pull Y κ hκ (Y.disjSum Y) (Sum.elim id id) (by
    intro x hx
    rcases x with p | p
    · rw [Finset.inl_mem_disjSum] at hx; exact hx
    · rw [Finset.inr_mem_disjSum] at hx; exact hx)
  refine PBB.psd_congr _ _ _ (fun x hx y hy => ?_) this
  rcases x with p | p <;> rcases y with q | q
  · rfl
  · rfl
  · rw [Finset.inr_mem_disjSum] at hx
    rw [Finset.inl_mem_disjSum] at hy
    simp only [blk, Sum.elim_inl, Sum.elim_inr, id]
    exact psd_herm Y κ hκ hy hx
  · rfl

theorem image_prod_loc {X : Type} (σ : E →+* ℂ) (Y : Finset (TB.Pt E)) (Xs : Finset X) :
    (Y ×ˢ Xs).image (fun p : TB.Pt E × X => (C.loc σ p.1, p.2)) = (Y.image (C.loc σ)) ×ˢ Xs := by
  ext ⟨a, x⟩
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨h, x', ⟨hh, hx'⟩, rfl, rfl⟩; exact ⟨⟨h, hh, rfl⟩, hx'⟩
  · rintro ⟨⟨h, hh, rfl⟩, hx⟩; exact ⟨h, x, ⟨hh, hx⟩, rfl, rfl⟩

theorem germ_global (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (w' : S.W)
    (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = b - 1) :
    ∃ (P Q : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ),
      (∀ v, ∀ h ∈ Y, ∀ h' ∈ Y,
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)]))) ∧
      GermData Y (fun v p q => KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)])
          (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])) P Q
        (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
  have hloc : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = b - 1 := by
    intro v h hh
    obtain ⟨h0, hh0, rfl⟩ := Finset.mem_image.1 hh
    rw [JCx1.needs.ptSize_loc]; exact hY h0 hh0
  have hsup : ∀ v, ∃ B : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w'.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t)])‖ ≤ B := by
    intro v
    have hs : ∀ h ∈ Y.image (C.loc (S.σ v)), LocSup S v ε (n - 1) b (w'.1 v) h := by
      intro h hh
      refine locSup_all S hpos hI hg v Λ (hLL v) (hGL v) (fun b s hb hs hbs => hΛ0 b s hb hs hbs v) ε hε (n - 1)
        (by omega) b hb (by omega) h (hloc v h hh) (w'.1 v) ⟨w', rfl⟩ ?_
      have := PBB.len_le_cnt S w' v
      have hk : (n - 1 - 1) * C.Kst ≤ n * C.Kst := Nat.mul_le_mul_right _ (by omega)
      omega
    choose! Bh hBh using hs
    refine ⟨∑ h ∈ Y.image (C.loc (S.σ v)), max (Bh h) 0, fun h hh t ht => ?_⟩
    have := hBh h hh t ht
    rw [show b + (n - 1) - 1 = b + n - 2 by omega] at this
    exact this.trans ((le_max_left _ _).trans (Finset.single_le_sum (f := fun h => max (Bh h) 0)
      (fun _ _ => le_max_right _ _) hh))
  have hG' : ∀ v, ∃ (Pu Pa : C.LPt × ℂ → C.LPt × ℂ → ℂ),
      (∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)),
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)]))) ∧
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (fun p q => KB.gN S v ε (b + n - 2) (w'.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])) Pu Pa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ x : ℂ, x ≠ 0 → ‖Pa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)), ∀ σ : ℂ,
        Tendsto (fun x => Pa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => Pu (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => conj (Pu (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) := by
    intro v
    obtain ⟨h1, Pu, Pa, h2, h3, h4⟩ := hGL v ε hε b n hb hn hbn (w'.1 v) ⟨w', rfl⟩ (Y.image (C.loc (S.σ v)))
      (hloc v) (hsup v)
    exact ⟨Pu, Pa, h1, h2, h3, h4⟩
  choose Pu Pa hcont hblk hB' hlim using hG'
  choose Bs hBs using hsup
  choose B' hB'' using hB'
  have mem : ∀ v, ∀ h ∈ Y, C.loc (S.σ v) h ∈ Y.image (C.loc (S.σ v)) := fun v h hh => Finset.mem_image_of_mem _ hh
  refine ⟨fun v p q => Pu v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v p q => Pa v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v h hh h' hh' => hcont v _ (mem v h hh) _ (mem v h' hh'), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v Xs hXs
    have := hblk v Xs hXs
    rw [← image_prod_loc (S.σ v) Y Xs] at this
    exact PBB.blockPSD_pull (Y ×ˢ Xs) (fun p : TB.Pt E × ℂ => (C.loc (S.σ v) p.1, p.2)) _ _ _ this
  · refine ⟨∑ v, (max (Bs v) 0 + max (B' v) 0), Finset.sum_nonneg fun v _ => by positivity,
      fun v h hh x hx => ⟨?_, ?_⟩⟩
    · refine ((hBs v _ (mem v h hh) x⁻¹ (inv_ne_zero hx)).trans (le_max_left (Bs v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_right (le_max_right (B' v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
    · refine ((hB'' v _ (mem v h hh) x hx).trans (le_max_left (B' v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_left (le_max_right (Bs v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.2

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermVectorIdentity
section
theorem Formalism.FourierDecayAlt.P.sign_permutation_identity : Formalism.FourierDecayAlt.C3.SignE :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.sign_permutation_identity

theorem Formalism.FourierDecayAlt.P.antidiagonal_determinant : Formalism.FourierDecayAlt.C3.AntiDiagDet :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.antidiagonal_determinant

theorem Formalism.FourierDecayAlt.P.derivative_leading_zb : Formalism.FourierDecayAlt.C3.DleadZb :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb

theorem Formalism.FourierDecayAlt.P.minors_first_case : Formalism.FourierDecayAlt.C3.MinorsFirstCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.minors_first_case

theorem Formalism.FourierDecayAlt.P.third_polynomial_expansion : Formalism.FourierDecayAlt.C3.MinorsThirdCase :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_polynomial_expansion

theorem Formalism.FourierDecayAlt.P.first_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_identity

theorem Formalism.FourierDecayAlt.P.second_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_peeling_identity

theorem Formalism.FourierDecayAlt.P.third_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_peeling_identity

theorem Formalism.FourierDecayAlt.P.fourth_peeling_identity : Formalism.FourierDecayAlt.C3.PeelingDualCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.fourth_peeling_identity

theorem Formalism.FourierDecayAlt.P.peeling_of_parts : Formalism.FourierDecayAlt.C3.PeelOfParts :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.peeling_of_parts

theorem Formalism.FourierDecayAlt.P.first_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionOmittedColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_expansion_identity

theorem Formalism.FourierDecayAlt.P.second_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionDualColumn :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_expansion_identity

theorem Formalism.FourierDecayAlt.P.column_indicator_expansion : Formalism.FourierDecayAlt.C3.ExpansionCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion

theorem Formalism.FourierDecayAlt.P.fourth_expansion_identity : Formalism.FourierDecayAlt.C3.ExpansionDualCovector :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.fourth_expansion_identity

theorem Formalism.FourierDecayAlt.P.first_expansion_of_parts : Formalism.FourierDecayAlt.C3.ExpansionFirstCaseFromComponents :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.first_expansion_of_parts

theorem Formalism.FourierDecayAlt.P.second_expansion_of_parts : Formalism.FourierDecayAlt.C3.ExpansionSecondCaseFromComponents :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.second_expansion_of_parts

theorem Formalism.FourierDecayAlt.P.third_expansion_of_parts : Formalism.FourierDecayAlt.C3.ExpansionThirdCaseFromComponents :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.third_expansion_of_parts

theorem Formalism.FourierDecayAlt.P.fourth_expansion_of_parts : Formalism.FourierDecayAlt.C3.ExpansionFourthCaseFromComponents :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.fourth_expansion_of_parts

theorem Formalism.FourierDecayAlt.P.chain_first_identity : Formalism.FourierDecayAlt.C3.LastColumnChain :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.chain_first_identity

theorem Formalism.FourierDecayAlt.P.chain_first_of_parts : Formalism.FourierDecayAlt.C3.LastColumnChainFromComponents :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.chain_first_of_parts

theorem Formalism.FourierDecayAlt.P.right_derivative_rule_psi : Formalism.FourierDecayAlt.C3.RuleRightDpsi :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.right_derivative_rule_psi

theorem Formalism.FourierDecayAlt.P.leading_term_identity : Formalism.FourierDecayAlt.C3.LeadAA :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity

theorem Formalism.FourierDecayAlt.P.leading_term_vector_identity : Formalism.FourierDecayAlt.C3.LeadAAv :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_vector_identity

theorem Formalism.FourierDecayAlt.P.dpsi_is_derivation : Formalism.FourierDecayAlt.C3.DpsiDerivation :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.dpsi_is_derivation

theorem Formalism.FourierDecayAlt.P.isotropicNormalFormFull_statement : Formalism.FourierDecayAlt.C3.IsotropicNormalFormFull :=
  Formalism.FourierDecayAlt.P.SignAntidiagonal.isotropicNormalFormFull_statement
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QuadInner1
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem hphi_meas : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
    (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_hn measurable_id

theorem quad_inner {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μW μN μW' : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN] [SigmaFinite μW']
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS2 : muSof μW' μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
      ∂(muSof μW' μN) ∂(muSof μW μN) = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hae2 : ∀ᵐ s ∂(muSof μW' μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS2
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t.1 * γ * (Matrix.of t.2)⁻¹ * Matrix.of zz')‖ₑ) := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    exact measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz))
      measurable_fst) mγ) (meas_inv measurable_snd)) (meas_const_mt zz'))
  calc ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
        ∂(muSof μW' μN) ∂(muSof μW μN)
      = ∫⁻ s, ∫⁻ s', ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * γ * (Matrix.of s')⁻¹ * Matrix.of zz')‖ₑ
          ∂(muSof μW' μN) ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        apply lintegral_congr_ae
        filter_upwards [hae2] with s' hs'
        have hY : Matrix.of s * γ * (Matrix.of s')⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul hs hγ) (MatrixMultiplicationContinuity.uh_inv hs').1
        have hM : (Matrix.of zz)⁻¹ * (Matrix.of s * γ * (Matrix.of s')⁻¹) * Matrix.of zz' ∈
            Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hY) hz'
        rw [coef_eq hds hz hY hz', ← hee0 _ hM]
        simp only [Matrix.mul_assoc]
    _ = ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of zz)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
          (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of zz')‖ₑ ∂(μW'.prod μN) ∂(μW.prod μN) := by
        unfold muSof
        rw [lintegral_map (hJ.lintegral_prod_right' (ν := (μW'.prod μN).map
          (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r)))) hphi_meas]
        apply lintegral_congr
        intro p
        have hK : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r =>
            ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) *
              γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ) := by
          have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r => (fun i j => ((Matrix.of zz)⁻¹ *
              Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) * γ) i j :
                Formalism.QuantumDeterminants.Mt k r)) := measurable_const
          exact measurable_enorm_composition he0 (meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt zz'))
        show ∫⁻ y, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r) * γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ ∂((μW'.prod μN).map
              (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
                (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))) = _
        rw [lintegral_map hK hphi_meas]
        rfl
    _ = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := rfl

theorem quad_inner1 {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN) =
      Lam1 e0 (μW.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t * Matrix.of zz')‖ₑ) :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz)) measurable_id) (meas_const_mt zz'))
  calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN)
      = ∫⁻ s, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz')‖ₑ ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        have hM : (Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hs) hz'
        rw [coef_eq hds hz hs hz', ← hee0 _ hM]
    _ = Lam1 e0 (μW.prod μN) zz zz' := by
        unfold muSof Lam1
        rw [lintegral_map hJ hphi_meas]
        rfl

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfHaar
section
open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieJ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem haar_prop {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : B.IsHaarOn U μ) (hν : B.IsHaarOn U ν) : ∃ c : ℝ≥0∞, ν = c • μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r U μ ν hU hμ hν.conc hν.left hν.finite_compact
  exact ⟨c, by rw [hc, ENNReal.smul_def]⟩

theorem sfinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) : SFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem jfScale : Formalism.FourierDecayAlt.P.PTie.JFScale := by
  intro k r Wp Wq _ _ _ _ Bs Bs' hz hz' hπ hπ'
  have hW := Bs.haarW
  have hW' := Bs.haarW'
  rw [hz] at hW
  rw [hz'] at hW'
  obtain ⟨a, ha⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z) Bs'.haarW hW
  obtain ⟨a', ha'⟩ := haar_prop (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs'.z') Bs'.haarW' hW'
  obtain ⟨b, hb⟩ := haar_prop (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) Bs'.haarN Bs.haarN
  have := sfinite_of_haar Bs'.haarW
  have := sfinite_of_haar Bs'.haarW'
  have := sfinite_of_haar Bs'.haarN
  refine ⟨(((a * b) * (a' * b)).toReal : ℂ), fun F => ?_⟩
  funext g
  simp only [B.JF, Pi.smul_apply]
  rw [hz, hz', hπ, hπ', ha, ha', hb]
  unfold besselJ
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [integral_smul_measure, Complex.coe_smul]
  congr 2
  ring

end Formalism.FourierDecayAlt.P.PTieJ

namespace Formalism.FourierDecayAlt.P

theorem jacquet_scaling : Formalism.FourierDecayAlt.P.PTie.JFScale := PTieJ.jfScale

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SiteTransport
section
open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section comp

variable {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V'']
  [Module ℂ V''] {T : V →ₗ[ℂ] V'} {T' : V' →ₗ[ℂ] V''}

theorem rel_comp {A : Pr V} {A' : Pr V'} {A'' : Pr V''} (h : Rel T A A') (h' : Rel T' A' A'') :
    Rel (T' ∘ₗ T) A A'' := by
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have h1 := LinearMap.congr_fun h.1 v
    have h2 := LinearMap.congr_fun h'.1 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]
  · have h1 := LinearMap.congr_fun h.2 v
    have h2 := LinearMap.congr_fun h'.2 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]

theorem mrel_comp {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    {M'' : Matrix (Fin 2) (Fin 2) (Pr V'')} (h : MRel T M M') (h' : MRel T' M' M'') : MRel (T' ∘ₗ T) M M'' :=
  fun a b => rel_comp (h a b) (h' a b)

variable {S : Type} [Fintype S] [DecidableEq S]

end comp

section bT

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem mrel_Ts {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) (Y : ℂ) : MRel T (Wd.Ts σ Y) (Wd.Ts σ' Y) := by
  unfold Wd.Ts; exact mrel_Tm Y hp hc hci

theorem arel_bT {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) : ∀ w : List (Wd.Letter ℂ S), ARel T (Wd.bT σ w) (Wd.bT σ' w)
  | [] => by unfold Wd.bT; exact arel_one
  | l :: w => by
    unfold Wd.bT Wd.vlet
    refine arel_mul (arel_ins _ (brel_lift0 ?_)) (arel_bT hp hc hci w)
    split_ifs
    · exact mrel_Ts hp hc hci _
    · intro a b
      rw [Matrix.map_apply, Matrix.map_apply]
      exact rel_star (mrel_Ts hp hc hci _ a b)

end bT

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem site_ops {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (l : Fin ρ) :
    Rel (trL ht z z' π π') (L.p (shS l)) (Ls.p l) ∧ Rel (trL ht z z' π π') (L.c (shS l)) (Ls.c l) ∧
      Rel (trL ht z z' π π') (L.ci (shS l)) (Ls.ci l) := by
  have hop := fun (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  refine ⟨?_, ?_, ?_⟩
  · rw [hL.1, hLs.1]
    exact rel_mk (fun v => hop 0 v) (fun v => by simp only [LinearMap.neg_apply, hop 3, map_neg])
  · rw [hL.2.2.1, hLs.2.2.1]
    exact rel_mk (fun v => hop 1 v) (fun v => hop 4 v)
  · rw [hL.2.2.2.1, hLs.2.2.2.1]
    exact rel_mk (fun v => hop 2 v) (fun v => hop 5 v)

theorem qqi_rel_n {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (n : ℕ) (hn : n ≤ ρ) (Y : ℂ) :
    MRel (trL ht z z' π π') (P5.QQi L st ⟨n + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨n, by omega⟩ Y) := by
  have hQ : MRel (trL ht z z' π π') (st.QQ Y) (sts.QQ Y) := by
    rw [hst, hsts]
    exact mrel_smul s fun a b => rel_mk (fun v => t_tr ht hz hz' X Xs Y a b v) (fun v => t_tr ht hz hz' X Xs _ b a v)
  unfold P5.QQi
  exact mrel_mul (mrel_mul (mrel_conjTranspose (tprod_rel ht hL hLs _ _ n rfl)) hQ) (tprod_rel ht hL hLs _ _ n rfl)

end one

end Formalism.FourierDecayAlt.P.PTieB

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

end Formalism.FourierDecayAlt.P
end
end

