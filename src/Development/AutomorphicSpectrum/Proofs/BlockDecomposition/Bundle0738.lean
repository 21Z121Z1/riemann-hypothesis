import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0734
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0735
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorant
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem exists_eval_points {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (N : ℕ) (x : Fin N → X) (f : Fin N → X → ℂ), (∀ i, f i ∈ W) ∧
      ∀ w ∈ W, ∀ y, w y = ∑ i, w (x i) * f i y := by
  classical
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hch : ∀ φ : s, ∃ x, ev x = φ.1 := fun φ => hs φ.2
  choose pt hpt using hch
  let e := s.equivFin
  let x : Fin s.card → X := fun i => pt (e.symm i)
  let T : W →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun i => ev (x i)
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hle : Submodule.span ℂ (s : Set (Module.Dual ℂ W)) ≤ LinearMap.ker (Module.Dual.eval ℂ W w) := by
      rw [Submodule.span_le]
      intro φ hφ
      have h1 : T w (e ⟨φ, hφ⟩) = 0 := by rw [hw]; rfl
      have h2 : ev (x (e ⟨φ, hφ⟩)) w = 0 := h1
      have h3 : ev (x (e ⟨φ, hφ⟩)) = φ := by
        show ev (pt (e.symm (e ⟨φ, hφ⟩))) = φ
        rw [Equiv.symm_apply_apply, hpt]
      rw [h3] at h2
      exact h2
    refine Subtype.ext (funext fun y => ?_)
    have hy : ev y ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ W)) :=
      hspan ▸ Submodule.subset_span ⟨y, rfl⟩
    exact hle hy
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective hT
  refine ⟨s.card, x, fun i => (L (Pi.single i 1)).1, fun i => (L _).2, ?_⟩
  intro w hw y
  have h1 : L (T ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hL _
  have h2 : T ⟨w, hw⟩ = ∑ i, w (x i) • (Pi.single i (1 : ℂ) : Fin s.card → ℂ) := by
    ext j
    simp [T, ev, Finset.sum_apply, Pi.single_apply]
  rw [h2, map_sum] at h1
  have h3 := congrArg (fun v : W => v.1 y) h1
  simp only [map_smul] at h3
  simpa [Submodule.coe_sum, Finset.sum_apply] using h3.symm

theorem rank_one_majorant_of_parts : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  intro hCont hFin hOrb hIwa D n ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl hl0 Φ hΦ C hC
  have hcart : ∀ τ, IsCartanInv (gramAt D (V1 D) τ)
      ((fun _ => 1 : D.what₂.Tau → Matrix (Fin (V1 D).rank) (Fin (V1 D).rank) ℂ) τ) :=
    fun τ => GlobalTheory.AdForm.VacStd.cartan_of_gram (GlobalTheory.AdForm.VacStd.gram_of_eq _ _ 1 rfl) τ
  obtain ⟨W, hWfd, hWle, hWK⟩ :=
    hFin D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl (fun _ => 1) hcart Φ hΦ
  haveI := hWfd
  obtain ⟨N, x, f, hfW, hrep⟩ := exists_eval_points W
  have hcont := hCont D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω Φ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ K D n, ‖(ω k Φ).1 (x i)‖ ≤ B := by
    intro i
    have hc : Continuous fun k : G D n => (ω k Φ).1 (x i) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB⟩ := HeightExists.isCompact_K.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩
  choose B hB0 hB using hB
  obtain ⟨A₁, A₂, R, hA₁, hA₂, hiwa⟩ := hIwa D n C hC
  have hM := fun i => hOrb D n θ hθ l hl0 (f i) (hWle (hfW i)) A₁ A₂ hA₁ hA₂
  choose M hMs hMpos hMle using hM
  have hc0 : 0 ≤ (max R 0) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  refine ⟨(((max R 0) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i,
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hMs i)), ?_⟩
  intro h hh y
  obtain ⟨m, t, k, a, b, hk, rfl, hm, ht, ha1, ha2, hR⟩ := hiwa h hh
  set c : ℝ := (max R 0) ^ ((1 : ℝ) / 2) with hc
  have e1 : ‖(ω (m * t * k) Φ).1 y‖ =
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) * ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hω.levi m a hm, hω.unip t b ht,
      norm_mul, norm_mul, norm_mul, hψ.2.1, norm_npow (hom_pos _ _)]
    have hre : (((V1 D).rank : ℂ) / 2).re = (1 : ℝ) / 2 := by
      show ((((1 : ℕ) : ℂ)) / 2).re = (1 : ℝ) / 2
      norm_num
    rw [hre, Circle.norm_coe, one_mul, one_mul]
  have e2 : ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ ≤ ∑ i, B i * ‖M i y‖ := by
    rw [hrep _ (hWK k hk)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB i k hk) (hMle i a ha1 ha2 y) (norm_nonneg _) (hB0 i)
  have e3 : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) ≤ c :=
    Real.rpow_le_rpow (NNReal.coe_nonneg _) (hR.trans (le_max_left _ _)) (by norm_num)
  have e4 : ∀ i, M i y = ((‖M i y‖ : ℝ) : ℂ) := by
    intro i
    have h1 := hMpos i y
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      rw [show M i y = (((M i y).re : ℝ) : ℂ) from Complex.ext (by simp) (by simp [h1.2])]
      simp [abs_of_nonneg h1.1]
    · simp [h1.2]
  have e5 : ‖((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y‖ = c * ∑ i, B i * ‖M i y‖ := by
    have h1 : ((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y =
        ((c * ∑ i, B i * ‖M i y‖ : ℝ) : ℂ) := by
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [← e4 i]
    rw [h1, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg hc0 (Finset.sum_nonneg fun i _ => mul_nonneg (hB0 i) (norm_nonneg _))
  rw [e1, e5]
  exact mul_le_mul e3 e2 (norm_nonneg _) hc0

end GlobalTheory.CompanionTheory.ThTot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspShuffle

open Zc.Comb

variable {α β : Type*}

theorem interleave_filter (f : β → α) (q : β → Bool) (P : List β) :
    Interleave ((P.filter q).map f) ((P.filter fun p => !q p).map f) (P.map f) := by
  induction P with
  | nil => exact Zc.Comb.Interleave.nil
  | cons p P ih =>
    cases hq : q p with
    | true =>
      simp only [List.filter_cons, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.left ih
    | false =>
      simp only [List.filter_cons, hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.right ih

theorem shuffle_range (f : β → α) (c : β → ℕ) (n : ℕ) : ∀ (s : ℕ) (P : List β),
    (∀ p ∈ P, s ≤ c p ∧ c p < s + n) →
      Shuffle ((List.range' s n).map fun i => (P.filter fun p => c p = i).map f) (P.map f) := by
  induction n with
  | zero =>
    intro s P hP
    have hnil : P = [] := List.eq_nil_iff_forall_not_mem.mpr fun p hp => by
      have := hP p hp
      omega
    subst hnil
    exact Zc.Comb.Shuffle.nil
  | succ n ih =>
    intro s P hP
    simp only [List.range'_succ, List.map_cons]
    refine Zc.Comb.Shuffle.cons (v := (P.filter fun p => !decide (c p = s)).map f) ?_
      (GlobalTheory.CompanionTheory.CuspShuffle.interleave_filter f (fun p => decide (c p = s)) P)
    have h := ih (s + 1) (P.filter fun p => !decide (c p = s)) (by
      intro p hp
      rw [List.mem_filter] at hp
      have h1 := hP p hp.1
      have hne : c p ≠ s := by simpa using hp.2
      omega)
    convert h using 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range'_1] at hi
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro p _
    by_cases hc : c p = i
    · have his : i ≠ s := by omega
      simp [hc, his]
    · simp [hc]

theorem shuffle_of_colouring {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (D : Fin h → List α)
    (hD : ∀ i, Zc.Cos.sub W c i = D i) : Shuffle (List.ofFn D) W := by
  have key := GlobalTheory.CompanionTheory.CuspShuffle.shuffle_range W.get (fun p => (c p : ℕ)) h 0 (List.finRange W.length)
    (fun p _ => ⟨Nat.zero_le _, by simpa using (c p).isLt⟩)
  convert key using 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range', ← hD]
      unfold Zc.Cos.sub
      congr 1
      apply List.filter_congr
      intro p _
      simp [Fin.ext_iff]
  · apply List.ext_getElem <;> simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decWord_eq_decW (Δ : Segment k) : Zc.Cos.decWord Δ = decW Δ := by
  unfold Zc.Cos.decWord Zc.M.decW
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    ext
    simp only [Fin.val_rev, List.length_ofFn]
    omega

theorem inShW_of_wd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : LSegJacquet k) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k) (hΔ : ∀ i, IsLSeg (Δ i) (x i).rep) (w : List (IrrGL k))
    (hc : ∀ c ∈ w, c.IsCusp) (hw : Wd (prodIrr x hd) w) : InShW (Finset.univ.val.map Δ) w := by
  obtain ⟨hsum, hne⟩ := hw
  have hmult := GlobalTheory.T.segment_product_jacquet_shuffle_count hA hL Δ x hd hΔ w hc
  have hpos : Zc.Cos.jmL w (GlobalTheory.LocGL.prodIrr x hd) ≠ 0 := by
    unfold Zc.Cos.jmL
    rw [dif_pos hsum]
    exact hne
  rw [hmult] at hpos
  have hcard : Zc.Cos.shuffleCount w (fun i => Zc.Cos.decWord (Δ i)) ≠ 0 := by exact_mod_cast hpos
  unfold Zc.Cos.shuffleCount at hcard
  obtain ⟨col, hcol⟩ := Finset.card_ne_zero.mp hcard
  have hcol' : ∀ i, Zc.Cos.sub w col i = Zc.Cos.decWord (Δ i) := by simpa using hcol
  unfold Zc.M.InShW
  refine ⟨List.ofFn Δ, ?_, ?_⟩
  · rw [Fin.univ_val_map]
  · rw [List.map_ofFn]
    have e : (Zc.M.decW ∘ Δ) = fun i => Zc.Cos.decWord (Δ i) :=
      funext fun i => (GlobalTheory.CompanionTheory.CuspShuffle.decWord_eq_decW (Δ i)).symm
    rw [e]
    exact GlobalTheory.CompanionTheory.CuspShuffle.shuffle_of_colouring w col _ hcol'

end GlobalTheory.CompanionTheory.CuspShuffle

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_space_covolume_formula : PositivityTheory.SiegelWeilFormula.KWhit.MeasP.TupCovol := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol | exact GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol | (intros; apply GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExpSkewHermitian
section
open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed GlobalTheory.CompanionTheory.GLK
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.UnitaryExp

theorem exists_unitary_diag {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (h1 : Kᴴ * K = 1) (h2 : K * Kᴴ = 1) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      Vᴴ * K * V = Matrix.diagonal z ∧ ∀ a, ‖z a‖ = 1 := by
  classical
  set A : Matrix (Fin n) (Fin n) ℂ := K + Kᴴ with hA
  set B : Matrix (Fin n) (Fin n) ℂ := Complex.I • (K - Kᴴ) with hB
  have hAh : Aᴴ = A := by
    simp [hA, Matrix.conjTranspose_add, add_comm]
  have hBh : Bᴴ = B := by
    simp [hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, smul_sub]
    abel
  have hAB : A * B = B * A := by
    have e : (K + Kᴴ) * (K - Kᴴ) = (K - Kᴴ) * (K + Kᴴ) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
      abel
    rw [hA, hB, Matrix.mul_smul, Matrix.smul_mul, e]
  obtain ⟨V, hV, hD⟩ := GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag ({A, B} : Set (Matrix (Fin n) (Fin n) ℂ))
    (by
      rintro X (rfl | rfl)
      · exact hAh
      · exact hBh)
    (by
      rintro X (rfl | rfl) Y (rfl | rfl)
      · rfl
      · exact hAB
      · exact hAB.symm
      · rfl)
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hKAB : K = (1 / 2 : ℂ) • (A - Complex.I • B) := by
    simp only [hA, hB, smul_smul, Complex.I_mul_I]
    module
  have hDd : (Vᴴ * K * V).IsDiag := by
    have e : Vᴴ * K * V = (1 / 2 : ℂ) • (Vᴴ * A * V - Complex.I • (Vᴴ * B * V)) := by
      conv_lhs => rw [hKAB]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [e]
    exact ((hD A (by simp)).sub ((hD B (by simp)).smul _)).smul _
  refine ⟨V, Matrix.diag (Vᴴ * K * V), hV1, hV2, hDd.diagonal_diag.symm, fun a => ?_⟩
  set D := Vᴴ * K * V with hDdef
  have hDD : Dᴴ * D = 1 := by
    have e : Dᴴ = Vᴴ * Kᴴ * V := by
      simp [hDdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e, hDdef]
    calc Vᴴ * Kᴴ * V * (Vᴴ * K * V) = Vᴴ * Kᴴ * (V * Vᴴ) * K * V := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (Kᴴ * K) * V := by
          rw [hV2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hV1]
  have hent : star (D a a) * D a a = 1 := by
    have h := congrFun (congrFun hDD a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · simpa [Matrix.conjTranspose_apply] using h
    · intro b _ hb
      have : D b a = 0 := hDd hb
      simp [this]
    · simp
  have hn : ‖D a a‖ ^ 2 = 1 := by
    have h3 : ((‖D a a‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := Complex.conj_mul' (D a a)
      push_cast
      rw [← this]
      simpa using hent
    exact_mod_cast h3
  have h0 : 0 ≤ ‖D a a‖ := norm_nonneg _
  show ‖D a a‖ = 1
  nlinarith [sq_nonneg (‖D a a‖ - 1), sq_nonneg (‖D a a‖ + 1)]

theorem exists_skew_exp_eq (n : ℕ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ X : Mat n, Xᴴ = -X ∧ uG k = expG X 1 := by
  classical
  have h1 : (k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (k : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 k.2
  have h2 : (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  obtain ⟨V, z, hV1, hV2, hD, hz⟩ := exists_unitary_diag _ h1 h2
  set w : Fin n → ℂ := fun a => (Complex.arg (z a) : ℂ) * Complex.I with hw
  have hexp : ∀ a, NormedSpace.exp (w a) = z a := by
    intro a
    have := Complex.norm_mul_exp_arg_mul_I (z a)
    rw [hz a] at this
    simpa [hw, Complex.exp_eq_exp_ℂ] using this
  have hk : (k : Matrix (Fin n) (Fin n) ℂ) = V * Matrix.diagonal z * Vᴴ := by
    rw [← hD]
    calc (k : Matrix (Fin n) (Fin n) ℂ)
        = (V * Vᴴ) * (k : Matrix (Fin n) (Fin n) ℂ) * (V * Vᴴ) := by
          rw [hV2]; simp
      _ = V * (Vᴴ * (k : Matrix (Fin n) (Fin n) ℂ) * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
  refine ⟨V * Matrix.diagonal w * Vᴴ, ?_, ?_⟩
  · have hs : star w = -w := by
      funext a
      simp [hw]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
    have hn : Matrix.diagonal (-w) = -Matrix.diagonal w := (Matrix.diagonal_neg w).symm
    rw [hn, Matrix.neg_mul, Matrix.mul_neg]
  · refine Units.ext ?_
    let Vu : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨V, Vᴴ, hV2, hV1⟩
    have e := Matrix.exp_units_conj Vu (Matrix.diagonal w)
    have e2 : NormedSpace.exp (Matrix.diagonal w) = Matrix.diagonal z := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext a
      rw [Pi.exp_def]
      exact hexp a
    rw [e2] at e
    have e3 : ((expG (V * Matrix.diagonal w * Vᴴ) 1 : G n) : Mat n) =
        NormedSpace.exp (V * Matrix.diagonal w * Vᴴ) := by
      simp
    rw [e3]
    exact hk.trans e.symm

end GlobalTheory.CompanionTheory.UnitaryExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.whitHeredity | exact GlobalTheory.CompanionTheory.Rodier.whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Rodier.whitHeredity <;> assumption)
end

