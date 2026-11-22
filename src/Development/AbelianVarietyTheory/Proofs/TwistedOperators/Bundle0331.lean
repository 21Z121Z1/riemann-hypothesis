import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0110
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0111
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0093
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingHypothesesGridParametersLargeScale
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

private theorem dualPar_dualPar' (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  rw [Finset.image_image]
  simp [Function.comp_def]

private theorem shift_zero_lemma_2 (S : SPar) : GlobalTheory.SignedHC.shift 0 S = S := by
  unfold GlobalTheory.SignedHC.shift
  simp

private theorem exists_par_of_gridData_bounds {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {ε : Fin (n + 1) → Bool}
    {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {B : ℝ}
    (hke : Even G.k) (hme : Even G.m) (hm2 : 2 ≤ G.m) (hn : n + 1 = G.k + G.m) (h3 : 3 ≤ n)
    (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hvk : 2 ≤ G.v G.k + G.b 1)
    (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.b (l + 1))
    (hga : 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.ga) (hvk0 : 0 ≤ G.v G.k) (hb1 : 0 < G.b 1)
    (ha0 : ((G.a 0 : ℚ) : ℝ) ≤ B) (hbm : (G.b G.m : ℝ) ≤ B)
    (hl : IsEnum (G.parPi 0) lam ε) (hm : IsEnum G.parD0 mu ε') :
    ∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu B := by
  have hga0 : 0 < G.ga := by
    have h0 : (0 : ℝ) < 1000 * ((n : ℝ) + 1) ^ 3 := by positivity
    exact_mod_cast h0.trans_le hga
  have hH : (2 : ℝ) ≤ 1000 * ((n : ℝ) + 1) ^ 3 := by
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have hvk1 : 1 ≤ G.v G.k + G.b 1 := by omega
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.card_minus_signs_half_of_even hme hga0 hl hm
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv ε ε' (hc.trans hc'.symm)
  obtain ⟨hHl, hHm⟩ := GlobalTheory.T.harish_chandra_param_of_even hke hme hn hl hm
  have hw := GlobalTheory.T.interlaced_signed_parameters hga0 hvk1 hl hm
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.parameters_separated_by_one hga0 hv (by omega) hl hm
  obtain ⟨hwl, hwm, hgl, hgm⟩ := GlobalTheory.T.parameters_spacing_and_gap hH hga hv hvk hb hl hm
  have habs : ∀ a c, a ≠ c → 2 ≤ |lam a - lam c| := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact (hwl a c h).trans (le_abs_self _)
    · rw [abs_sub_comm]
      exact (hwl c a h).trans (le_abs_self _)
  have hB := GlobalTheory.T.signed_parameters_bounded hvk0 hb1 ha0 hbm hl hm
  have hk2 := G.two_le_k
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => ε' i = false)
  have hneg : ∃ i, ε' i = false := by
    have hpos : 0 < (Finset.univ.filter fun i => ε' i = false).card := by
      rw [hc']
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hpos : (Finset.univ.filter fun i => ε' i = false).card ≤ (Finset.univ.filter fun i => ε' i = true).card := by
    have heq : (Finset.univ.filter fun i => ¬ ε' i = false) = Finset.univ.filter fun i => ε' i = true := by
      ext i
      simp
    rw [heq, Finset.card_univ, Fintype.card_fin] at hsum
    omega
  exact ⟨e, he, h3, hHl, hHm, hw, GlobalTheory.T.isInterlaced_sub_single_of_spread hw habs hs1 hs2, hwl, hwm, hgl, hgm, hneg, hpos, hB⟩

theorem realInputPar : Ev fun {D} _ _ {sc} _ _ _ => ∀ (τ : D.what₂.Tau) (ε : Fin (D.R.r + 1) → Bool) (lam : Fin (D.R.r + 1) → ℝ)
    (ε' : Fin D.R.r → Bool) (mu : Fin D.R.r → ℝ), IsEnum (Node.par D sc.cGap (.core 0) τ) lam ε →
    IsEnum (dualPar (parB (Ptw D) 0 τ)) mu ε' → (∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu (sc.b ^ 2)) ∧
      Real.log (8 * ((D.R.r : ℝ) + 1) * sc.b ^ 2) ≤ 6 * Real.log sc.b ∧ 0 ≤ Real.log sc.b := by
  intro _ _ _
  refine ⟨0, fun D large₂ _ _ hS T L μ0 _ Gr W M _ => ?_⟩
  intro τ ε lam ε' mu hlam hmu
  obtain ⟨hv, hvk, hb, hga, hvk0, hb1, ha0, hbm, hb1', hb4⟩ := GlobalTheory.T.chiGridNumericalData_realPlace_gap_size_bounds D large₂ hS τ
  have hl : IsEnum ((GlobalTheory.ChiGrid.num D 1 τ).parPi 0) lam ε := hlam
  have hD : dualPar (parB (Ptw D) 0 τ) = (GlobalTheory.ChiGrid.num D 1 τ).parD0 := by
    rw [← GlobalTheory.SignedHC.GridData.parD_zero_zero, parB, ← parV_zero D 1 (Nat.zero_le _) τ, dualPar_dualPar']
    show GlobalTheory.SignedHC.shift (if Odd (0 + 0) then -(1 / 2) else 0) _ = _
    rw [if_neg (by decide), shift_zero_lemma_2]
  have hm' : IsEnum (GlobalTheory.ChiGrid.num D 1 τ).parD0 mu ε' := hD ▸ hmu
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  refine ⟨exists_par_of_gridData_bounds (n := D.R.r) D.R.k_even D.R.m_even h2m
    (by show D.R.r + 1 = D.R.k + D.R.m; omega) (by omega) hv hvk hb hga hvk0 hb1 ha0 hbm hl hm', ?_,
    Real.log_nonneg hb1'⟩
  have hbpos : 0 < large₂.sc.b := by linarith
  show Real.log (8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2) ≤ 6 * Real.log large₂.sc.b
  have h6 := Real.log_pow large₂.sc.b 6
  push_cast at h6
  rw [← h6]
  apply Real.log_le_log (by positivity)
  calc 8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2 ≤ large₂.sc.b ^ 4 * large₂.sc.b ^ 2 := by gcongr
    _ = large₂.sc.b ^ 6 := by ring

end GlobalTheory.SepPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachMultMapEquivariantSobolevContinu
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GKExtFields

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem dRep_rep_conj (M : DSModel V S) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : M.H τ) :
    dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  unfold Formalism.L2.Theta.dRep DSModel.rep
  congr 1
  funext t
  have h1 : t • ((M.fr τ)⁻¹ * X * M.fr τ) = (M.fr τ)⁻¹ * (t • X) * M.fr τ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, Matrix.exp_conj' _ _ (M.fr_unit τ)]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem foldr_dRep_conj (M : DSModel V S) (τ : D.what₂.Tau) (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (w : M.H τ) :
    (l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ).foldr (dRep (M.rep τ)) w = l.foldr (dRep (M.σ τ)) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_rep_conj]

theorem conj_mem_lieAt (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have h1 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have h3 : (M.fr τ)ᴴ * (Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ = 0 := by
    rw [hX']; simp
  simp only [conjTranspose_mul, Matrix.mul_assoc, h1, h2]
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using h3

theorem multMap_fields : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)) (N : ℕ) (π : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) → (∀ x d, GlobalTheory.Size.growthSob θ V d N (ι x) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x, ι (π τ g x) = rTr V ((GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ g) (ι x)) → ∀ T : MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) E, (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) → (∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → ι (T (Function.update v τ w)) = rTr V (atTau θ V τ g) (ι (T v))) ∧ ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := by
  intro D θ V S M E _ _ _ _ _ _ p ι N π hp hfin hπ T hTe hTc
  refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg' : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
      GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hg
    rw [hTe τ _ hg' v w hw, hπ τ _ hg']
    have he : (GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ (M.fr τ * g * (M.fr τ)⁻¹) = atTau θ V τ g := by
      show atTau θ V τ ((M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ) = atTau θ V τ g
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    rw [he]
  · let f : M.sm τ →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (ι.comp (T.toLinearMap v τ))
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend f
    have hℓw : ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := fun w => by
      have := LinearMap.congr_fun hℓ w
      simpa [f, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ?_, hℓw⟩
    obtain ⟨L, C, hL, hC⟩ := hTc τ 0 v
    refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), GlobalTheory.Grow.height V x ^ N * C, ?_, fun w hw => ?_⟩
    · intro l hl X hX
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
      obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.GKExtFields.conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
    · have hmem : w ∈ M.sm τ := Submodule.subset_span hw
      have hw' : ℓ w = ι (T (Function.update v τ ⟨w, hmem⟩)) x := hℓw ⟨w, hmem⟩
      rw [hw']
      set y := T (Function.update v τ ⟨w, hmem⟩)
      have hpos : 0 < GlobalTheory.Grow.height V x ^ N := pow_pos (GlobalTheory.Grow.height_pos V x) N
      have hsz : p 0 y = (GlobalTheory.Size.growthSize V N (ι y)).toReal := by
        rw [hp]; simp [GlobalTheory.Size.growthSob]
      have hne : GlobalTheory.Size.growthSize V N (ι y) ≠ ⊤ := by
        have := hfin y 0; simpa [GlobalTheory.Size.growthSob] using this
      have hb : ‖ι y x‖ ≤ GlobalTheory.Grow.height V x ^ N * p 0 y := by
        have h1 : ENNReal.ofReal (‖ι y x‖ / GlobalTheory.Grow.height V x ^ N) ≤ GlobalTheory.Size.growthSize V N (ι y) :=
          le_iSup (fun g => ENNReal.ofReal (‖ι y g‖ / GlobalTheory.Grow.height V g ^ N)) x
        rw [ENNReal.ofReal_le_iff_le_toReal hne, div_le_iff₀ hpos, ← hsz] at h1
        linarith
      have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
          fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L (⟨w, hmem⟩ : M.sm τ) := by
        unfold GlobalTheory.SmoothGlob.sobNorm
        rw [List.map_map]
        congr 1
        refine List.map_congr_left fun l _ => ?_
        simp only [Function.comp_apply, GlobalTheory.GKExtFields.foldr_dRep_conj]
      rw [hs, mul_assoc]
      exact hb.trans (mul_le_mul_of_nonneg_left (hC ⟨w, hmem⟩) hpos.le)

end GlobalTheory.GKExtFields

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClosureGKSubmodule
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.GKClosure

open GlobalTheory.MatrixCoeffAgree

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem inner_exp_eq_zero (hπ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) {Y : Submodule ℂ H} (hY : IsGKSub ε π Y) {w : H}
    (hw : w ∈ Yᗮ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) {y : H} (hy : y ∈ Y)
    (han : AnalyticOnUJ ε fun g => ⟪w, π g y⟫_ℂ) (t : ℝ) : ⟪w, π (NormedSpace.exp (t • X)) y⟫_ℂ = 0 := by
  set G : H → ℝ → ℂ := fun z s => ⟪w, π (NormedSpace.exp (s • X)) z⟫_ℂ with hGdef
  have hderiv : ∀ z ∈ Y, ∀ s, HasDerivAt (G z) (G (dRep π X z) s) s := by
    intro z hz s
    have h1 := hasDerivAt_orbit hπ hX (hasDerivAt_zero_of_smoothVec hX (hY.smooth z hz)) s
    exact ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
  have hiter : ∀ k, ∀ z ∈ Y, iteratedDeriv k (G z) 0 = 0 := by
    intro k
    induction k with
    | zero =>
      intro z hz
      simp only [iteratedDeriv_zero, hGdef, zero_smul, NormedSpace.exp_zero, hπ.1, ContinuousLinearMap.one_apply]
      exact Submodule.inner_left_of_mem_orthogonal hz hw
    | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ']
      have : deriv (G z) = G (dRep π X z) := funext fun s => (hderiv z hz s).deriv
      rw [this, ih _ (hY.lieStable X hX z hz)]
  have han' : ∀ s, AnalyticAt ℝ (G y) s := by
    intro s
    have h1 := han.analytic_exp one_mem_UJset hX s
    simpa only [Matrix.one_mul] using h1
  exact eq_zero_of_iteratedDeriv han' (fun k => hiter k y hy) t

theorem conjTranspose_mem_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have := congrArg Matrix.conjTranspose (show k * Jm ε = Jm ε * k from hk.2)
  simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at this
  exact this.symm

theorem isKStableOn_orthogonal (hπ : IsAdmRep ε π) {Y : Submodule ℂ H} (hY : IsKStableOn ε π Y) :
    IsKStableOn ε π Yᗮ := by
  intro k hk u hu
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hk' := conjTranspose_mem_Kset hk
  have h1 : π k (π kᴴ y) = y := by
    have := hπ.1.2 k (mem_UJset_of_mem_Kset hk) kᴴ (mem_UJset_of_mem_Kset hk')
    rw [show k * kᴴ = 1 from Matrix.mem_unitaryGroup_iff.1 hk.1, hπ.1.1] at this
    exact (congrArg (fun A : H →L[ℂ] H => A y) this).symm
  rw [← h1, GlobalTheory.KPerp.inner_map_map_of_norm (hπ.2.2.1 k hk)]
  exact Submodule.inner_right_of_mem_orthogonal (hY _ hk' y hy) hu

theorem topologicalClosure_inf_kFinVec [CompleteSpace H] (hπ : IsAdmRep ε π) {Y : Submodule ℂ H}
    (hle : Y ≤ kFinVec ε π) (hY : IsKStableOn ε π Y) : Y.topologicalClosure ⊓ kFinVec ε π = Y := by
  refine le_antisymm (fun v hv => ?_) (le_inf Y.le_topologicalClosure hle)
  have hZ : Y ⊔ (Yᗮ ⊓ kFinVec ε π) = kFinVec ε π := by
    by_contra hne
    obtain ⟨a, ha0, ha, hz⟩ := GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec n ε H π hπ _ (sup_le hle inf_le_right)
      (fun k hk x hx => by
        obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add]
        exact Submodule.add_mem_sup (hY k hk y hy)
          ⟨isKStableOn_orthogonal hπ hY k hk u hu.1, isKStableOn_kFinVec ε π k hk u hu.2⟩) hne
    have haY : a ∈ Yᗮ := (Submodule.mem_orthogonal' _ _).2 fun y hy => hz y (Submodule.mem_sup_left hy)
    exact ha0 (inner_self_eq_zero.1 (hz a (Submodule.mem_sup_right ⟨haY, ha⟩)))
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.1 (hZ.symm ▸ hv.2 : v ∈ Y ⊔ (Yᗮ ⊓ kFinVec ε π))
  have h1 : u ∈ Y.topologicalClosure := by
    simpa using Y.topologicalClosure.sub_mem hv.1 (Y.le_topologicalClosure hy)
  rw [← Submodule.orthogonal_orthogonal_eq_closure] at h1
  have h2 : u = 0 := inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hu.1 h1)
  rwa [h2, add_zero]

theorem topologicalClosure_stable_inf_kFinVec : GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π → ∀ Y : Submodule ℂ H, IsGKSub ε π Y → (∀ g ∈ UJset ε, ∀ v ∈ Y.topologicalClosure, π g v ∈ Y.topologicalClosure) ∧ Y.topologicalClosure ⊓ kFinVec ε π = Y := by
  intro hA n ε H _ _ _ π hπ Y hY
  refine ⟨fun g hg v hv => ?_, topologicalClosure_inf_kFinVec hπ hY.kFin hY.kStable⟩
  have key : ∀ y ∈ Y, π g y ∈ Y.topologicalClosure := by
    intro y hy
    obtain ⟨k, hk, X, hX, rfl⟩ := ReciprocityTheory.ChartRestriction.DS.polar_UJ (show g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε from hg)
    have hk' : k ∈ Kset ε := hk
    have hZ := conj_mem_lieSet hk' (show X ∈ lieSet ε from hX.1)
    have hky := hY.kStable k hk' y hy
    rw [mul_exp_eq hk', hπ.1.2 _ (exp_mem_UJset hZ 1) _ (mem_UJset_of_mem_Kset hk'),
      ContinuousLinearMap.comp_apply, ← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    exact inner_exp_eq_zero hπ.1 hY hw hZ hky (GlobalTheory.T.admissible_unitary_K_finite.2 hA n ε H π hπ _ w (hY.kFin _ hky)) 1
  have : Y.topologicalClosure ≤ Y.topologicalClosure.comap (π g : H →ₗ[ℂ] H) :=
    Y.topologicalClosure_minimal key (Y.isClosed_topologicalClosure.preimage (π g).continuous)
  exact this hv

end GlobalTheory.GKClosure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffEqZeroOfSumTraceProjectionsInequivalentIrre
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.TraceSep

theorem exists_smul_eq_ite {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (h : ∀ i j, i ≠ j → ∀ f : M i →ₗ[R] M j, f = 0) (i₀ : ι) (s : ∀ i, Finset (M i)) :
    ∃ r : R, ∀ i, ∀ m ∈ s i, r • m = if i = i₀ then m else 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionOnto.main
  | exact _root_.GlobalTheory.OrthogonalProjectionOnto.main
  | (apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionOnto.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionOnto.main ..)

end GlobalTheory.TraceSep

namespace GlobalTheory.TraceSep

theorem hasFinTrace_compress {V : Type} [AddCommGroup V] [Module ℂ V] (P : V →ₗ[ℂ] V) (hP : P ∘ₗ P = P)
    [FiniteDimensional ℂ (LinearMap.range P)] (A : V →ₗ[ℂ] V) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P ∘ₗ A ∘ₗ P)
      (LinearMap.trace ℂ (LinearMap.range P) (P.rangeRestrict ∘ₗ A ∘ₗ (LinearMap.range P).subtype)) := by
  have hfix : ∀ u ∈ LinearMap.range P, P u = u := by
    rintro u ⟨w, rfl⟩; exact LinearMap.congr_fun hP w
  have hBU : LinearMap.range (P ∘ₗ A ∘ₗ P) ≤ LinearMap.range P := LinearMap.range_comp_le_range _ _
  haveI : FiniteDimensional ℂ (LinearMap.range (P ∘ₗ A ∘ₗ P)) := Submodule.finiteDimensional_of_le hBU
  refine ⟨inferInstance, ?_⟩
  have hQ : ∀ u, (P.rangeRestrict ∘ₗ A ∘ₗ (LinearMap.range P).subtype) u ∈
      (LinearMap.range (P ∘ₗ A ∘ₗ P)).comap (LinearMap.range P).subtype := by
    intro u
    refine ⟨u, ?_⟩
    simp [hfix u u.2]
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hQ,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hBU)]
  congr 1
  ext ⟨x, hx⟩
  simp [LinearEquiv.conj_apply, Submodule.comapSubtypeEquivOfLe, hfix x (hBU hx)]

theorem coeff_eq_zero_of_sum_trace_eq_zero : ∀ (G : Type) [Group G] (n : ℕ) (W : Fin n → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), (∀ i, (σ i).IsIrreducible) → (∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))) → ∀ (P : ∀ i, W i →ₗ[ℂ] W i), (∀ i, P i ∘ₗ P i = P i) → (∀ i, FiniteDimensional ℂ (LinearMap.range (P i))) → ∀ a : Fin n → ℂ, (∀ (g : G) (c : Fin n → ℂ), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P i ∘ₗ σ i g ∘ₗ P i) (c i)) → ∑ i, a i * c i = 0) → ∀ i, P i ≠ 0 → a i = 0 := by
  intro G _ n W _ _ σ hirr hne P hP hfin a hsum i₀ hi₀
  let Q : ∀ i, MonoidAlgebra ℂ G → Module.End ℂ (LinearMap.range (P i)) := fun i y =>
    (P i).rangeRestrict ∘ₗ (σ i).asAlgebraHom y ∘ₗ (LinearMap.range (P i)).subtype
  have hlin : ∀ y, ∑ i, a i * LinearMap.trace ℂ _ (Q i y) = 0 := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      refine hsum g _ fun i => ?_
      have := hasFinTrace_compress (P i) (hP i) (σ i g)
      simpa [Q, Representation.asAlgebraHom_of] using this
    | add x y hx hy =>
      simp only [Q, map_add, LinearMap.add_comp, LinearMap.comp_add, mul_add,
        Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy, add_zero]
    | smul c x hx =>
      simp only [Q, map_smul, LinearMap.smul_comp, LinearMap.comp_smul, smul_eq_mul] at hx ⊢
      rw [Finset.sum_congr rfl fun i _ => mul_left_comm (a i) c _, ← Finset.mul_sum, hx, mul_zero]
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (σ i).asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (hirr i)
  have hzero : ∀ i j, i ≠ j → ∀ f : (σ i).asModule →ₗ[MonoidAlgebra ℂ G] (σ j).asModule, f = 0 := by
    intro i j hij f
    haveI := hirr i
    haveI := hirr j
    haveI := hne i j hij
    haveI := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i) (σ j)).toEquiv.symm.subsingleton
    exact Subsingleton.elim _ _
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (LinearMap.range (P i)))) ℂ (LinearMap.range (P i)) :=
    fun i => Module.finBasis ℂ _
  obtain ⟨x, hx⟩ := exists_smul_eq_ite (R := MonoidAlgebra ℂ G) (fun i => (σ i).asModule) hzero i₀
    (fun i => Finset.univ.image fun k => (((b i k : LinearMap.range (P i)) : W i) : (σ i).asModule))
  have hQx : ∀ i, Q i x = if i = i₀ then LinearMap.id else 0 := by
    intro i
    refine (b i).ext fun k => ?_
    have h1 := hx i _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    change (σ i).asAlgebraHom x (b i k : W i) = _ at h1
    have hfix : P i (b i k : W i) = b i k := by
      obtain ⟨w, hw⟩ := (b i k).2
      rw [← hw]; exact LinearMap.congr_fun (hP i) w
    apply Subtype.ext
    by_cases hi : i = i₀
    · subst hi
      have h1' : (σ i).asAlgebraHom x (b i k : W i) = b i k := by simpa using h1
      simp [Q, h1', hfix]
    · have h1' : (σ i).asAlgebraHom x (b i k : W i) = 0 :=
        h1.trans (if_neg hi)
      simp [Q, h1', hi]
  have h := hlin x
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [hQx i, if_neg hi, map_zero, mul_zero])
    (by simp)] at h
  rw [hQx i₀, if_pos rfl, LinearMap.trace_id] at h
  have hpos : 0 < Module.finrank ℂ (LinearMap.range (P i₀)) := by
    rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot, Ne, LinearMap.range_eq_bot]
    exact hi₀
  have hne0 : (Module.finrank ℂ (LinearMap.range (P i₀)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  exact (mul_eq_zero.1 h).resolve_right hne0

end GlobalTheory.TraceSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjSmoothVectorConjugateModelMemSmoothStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_smooth_vector_conjugate_model_mem_smooth : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  first | exact @GlobalTheory.ConjSmooth.cj_mem_sm | exact GlobalTheory.ConjSmooth.cj_mem_sm | (intros; apply GlobalTheory.ConjSmooth.cj_mem_sm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelFrameMatrixFactsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_model_frame_matrix_facts_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  first | exact @GlobalTheory.PackLocFacts.frame_facts | exact GlobalTheory.PackLocFacts.frame_facts | (intros; apply GlobalTheory.PackLocFacts.frame_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateThetaLiftMatchedHeckeCombinationStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_theta_lift_matched_hecke_combination : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → GlobalTheory.GalLift.IsProjOf R i σ thP th → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.VacFix R.ψ ω P → ∀ cV cW, GlobalTheory.Hk3.Match R.ψ ω P (GlobalTheory.Hk3.dualC cV) cW → ∀ y y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) → (R.HW i σ).e (th y') = postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) := by
  first | exact @GlobalTheory.ConjLiftHecke.lift_match | exact GlobalTheory.ConjLiftHecke.lift_match | (intros; apply GlobalTheory.ConjLiftHecke.lift_match <;> assumption)
end

