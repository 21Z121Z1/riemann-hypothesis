import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0049
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0050

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticSectionIsAlgebraic
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem holomorphicSections_algebraic_of_isProper : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → IsProper p → ∀ (R : AnRead p (RingHom.id ℂ) D) (B : LB Y), B.IsLB → ∀ s ∈ R.holSec B, ∃ t : B.Sec, secVal p (RingHom.id ℂ) t = s := by
  intro Y p D hs hp R B hB s hsec
  have hcont (j : B.ι) : ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j)) :=
    (hsec.2 j).continuousOn (isOpen_ptsIn _)
  have loc (i : B.ι) (x : B.U i) : ∃ V : Y.Opens, x.1 ∈ V ∧ V ≤ B.U i ∧ ∃ c : Γ(Y, V),
      ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V c y = s i y := by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.exists_open_isDomain_of_smooth_complex Y p D hs x
    obtain ⟨V, hVa, hx, hV⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (U := U ⊓ B.U i) (x := x.1) ⟨hxU, x.2⟩
    have ha : IsAffineOpen V := hVa
    have hi := hV.trans inf_le_right
    have hd := hU V (hV.trans inf_le_left) hx
    have hh := (hsec.2 i).mono (ptsIn_mono hi)
    obtain ⟨n, u, C, m, hC⟩ := GlobalTheory.T.holomorphic_section_moderate_growth Y p hp B hB s hsec.1 hcont i V ha hi
    obtain ⟨a, b, hb, e⟩ := SerreSections.exists_mul_eq_of_polynomial_growth Y p D hs R V ha hd _ hh n u C m hC
    exact ⟨V, hx, hi, GlobalTheory.exists_ev_eq_of_continuousOn_quotient Y p D hs V ha hd _ (hh.continuousOn (isOpen_ptsIn _)) a b hb e⟩
  choose V hx hV c hc using loc
  have glue (i : B.ι) : ∃ f : Γ(Y, B.U i), ∀ y ∈ ptsIn p (RingHom.id ℂ) (B.U i),
      ev p (RingHom.id ℂ) _ f y = s i y := by
    obtain ⟨f, hf, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf (V i) (B.U i)
      (fun x => homOfLE (hV i x)) (fun x h => Opens.mem_iSup.2 ⟨⟨x, h⟩, hx i _⟩) (c i) fun x x' =>
        GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs (V i x ⊓ V i x') _ _ fun y hy =>
          ((ev_res inf_le_left hy _).trans (hc i x y (mem_ptsIn_inf.1 hy).1)).trans
            ((ev_res inf_le_right hy _).trans (hc i x' y (mem_ptsIn_inf.1 hy).2)).symm
    refine ⟨f, fun y hy => ?_⟩
    have hy' : y ∈ ptsIn p (RingHom.id ℂ) (V i ⟨_, mem_ptsIn.1 hy⟩) := mem_ptsIn.2 (hx i _)
    rw [← hc i _ y hy', ← hf]
    exact (ev_res _ hy' _).symm
  choose f hf using glue
  refine ⟨⟨f, fun i j => GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs _ _ _ fun y hy => ?_⟩, funext₂ fun i y => ?_⟩
  · have h := mem_ptsIn_inf.1 hy
    refine (ev_res inf_le_left hy _).trans (Eq.trans ?_ (ev_mul _ _ _).symm)
    rw [hf i y h.1, hsec.1.1 i j y h.1 h.2, ← hf j y h.2]
    exact congrArg _ (ev_res inf_le_right hy _).symm
  · by_cases h : y ∈ ptsIn p (RingHom.id ℂ) (B.U i)
    · exact hf i y h
    · exact (ev_of_notMem h _).trans (hsec.1.2 i y h).symm

end GlobalTheory.CompanionTheory.Gaga
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeries
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

section Chain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasDerivAt_one_sub_pow_succ_div_factorial (N : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ))
      (-((1 - s) ^ N / (N.factorial : ℝ))) s := by
  have h0 : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h1 : HasDerivAt (fun t : ℝ => (1 - t) ^ (N + 1)) (((N + 1 : ℕ) : ℝ) * (1 - s) ^ (N + 1 - 1) * (-1)) s :=
    h0.pow (N + 1)
  refine (h1.div_const ((N + 1).factorial : ℝ)).congr_deriv ?_
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem hasDerivAt_sum_one_sub_pow_div_factorial_smul {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s)
    (N : ℕ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t)
      (((1 - s) ^ N / (N.factorial : ℝ)) • f (N + 1) s) s := by
  induction N with
  | zero => simpa using hf 0 s
  | succ N ih =>
    have h2 := ih.add ((hasDerivAt_one_sub_pow_succ_div_factorial N s).smul (hf (N + 1) s))
    convert h2 using 1
    · funext t
      exact Finset.sum_range_succ _ _
    · rw [neg_smul]
      abel

theorem norm_chain_sub_partial_le {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s) (N : ℕ) {A : ℝ}
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f (N + 1) s‖ ≤ A) :
    ‖f 0 1 - ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0‖ ≤ A / ((N + 1).factorial : ℝ) := by
  let F : ℝ → E := fun t => ∑ m ∈ Finset.range (N + 1), ((1 - t) ^ m / (m.factorial : ℝ)) • f m t
  have hF1 : F 1 = f 0 1 := by
    simp [F, Finset.sum_range_succ']
  have hF0 : F 0 = ∑ m ∈ Finset.range (N + 1), ((m.factorial : ℝ)⁻¹) • f m 0 := by
    simp [F]
  have hD : ∀ t, HasDerivAt F (((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t) t :=
    fun t => hasDerivAt_sum_one_sub_pow_div_factorial_smul hf N t
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun t => F t - F 0) (a := 0) (b := 1)
    (f' := fun t => ((1 - t) ^ N / (N.factorial : ℝ)) • f (N + 1) t)
    (B := fun t => A / ((N + 1).factorial : ℝ) - A * ((1 - t) ^ (N + 1) / ((N + 1).factorial : ℝ)))
    (B' := fun t => A * ((1 - t) ^ N / (N.factorial : ℝ)))
    (fun t _ => ((hD t).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun t _ => ((hD t).sub_const (F 0)).hasDerivWithinAt)
    (by simp [div_eq_mul_inv])
    (fun t => (((hasDerivAt_one_sub_pow_succ_div_factorial N t).const_mul A).const_sub
      (A / ((N + 1).factorial : ℝ))).congr_deriv (by ring))
    (fun t ht => by
      have hc : 0 ≤ (1 - t) ^ N / (N.factorial : ℝ) := by
        have : 0 ≤ 1 - t := by linarith [ht.2]
        positivity
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_comm A]
      exact mul_le_mul_of_nonneg_left (hA t ⟨ht.1, ht.2.le⟩) hc)
  have h1 := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simp only [hF1, hF0, sub_self, zero_pow (Nat.succ_ne_zero N), zero_div, mul_zero, sub_zero] at h1
  exact h1

theorem hasSum_chain {f : ℕ → ℝ → E} (hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s) {a : ℕ → ℝ}
    (ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m)
    (hs : Summable fun m : ℕ => a m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => ((m.factorial : ℝ)⁻¹) • f m 0) (f 0 1) := by
  have hn : Summable fun m : ℕ => ‖((m.factorial : ℝ)⁻¹) • f m 0‖ := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (ha m 0 ⟨le_rfl, zero_le_one⟩) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hn, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hs.tendsto_atTop_zero
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn1 => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [norm_sub_rev]
  exact norm_chain_sub_partial_le hf N (ha (N + 1))

end Chain

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_exp_smul_real {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end Exp

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}

theorem exp_add_smul_real (X : Matrix (Fin n) (Fin n) ℂ) (s h : ℝ) :
    NormedSpace.exp ((s + h) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (h • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right h)

theorem isSmoothVec_iterate_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H}
    (hs : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => exact hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (hasDerivAt_dRep_and_isSmoothVec hG hrep ih hX).2

theorem hasDerivAt_orbit_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H}
    (hu : IsSmoothVec G π u) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (π (NormedSpace.exp (s • X)) (dRep π X u)) s := by
  have hd := (hasDerivAt_dRep_and_isSmoothVec hG hrep hu hX).1
  have hmem : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G := hX
  have heq : (fun t : ℝ => π (NormedSpace.exp (t • X)) u) =
      fun t => π (NormedSpace.exp (s • X)) (π (NormedSpace.exp ((t - s) • X)) u) := by
    funext t
    have h1 : NormedSpace.exp (t • X) = NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X) := by
      rw [← exp_add_smul_real, add_sub_cancel]
    rw [h1, hrep.2 _ (hmem s) _ (hmem (t - s))]
    rfl
  rw [heq]
  have hd' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) u) (dRep π X u) (s - s) := by
    rw [sub_self]
    exact hd
  have hc := hd'.comp_sub_const s s
  exact ((π (NormedSpace.exp (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hc

theorem exists_bound_orbit_Icc [CompleteSpace H] (hc : ∀ v, ContinuousOn (fun g => π g v) G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp (s • X))‖ ≤ B := by
  have hcont : ∀ w, ContinuousOn (fun s : ℝ => π (NormedSpace.exp (s • X)) w) (Set.Icc 0 1) := by
    intro w
    exact (hc w).comp (continuous_exp_smul_real X).continuousOn (fun s _ => hX s)
  have hb : ∀ w, ∃ C, ∀ i : Set.Icc (0 : ℝ) 1, ‖π (NormedSpace.exp ((i : ℝ) • X)) w‖ ≤ C := by
    intro w
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont w)
    exact ⟨C, fun i => hC i i.2⟩
  obtain ⟨B, hB⟩ := banach_steinhaus (g := fun i : Set.Icc (0 : ℝ) 1 => π (NormedSpace.exp ((i : ℝ) • X))) hb
  exact ⟨B, fun s hs => hB ⟨s, hs⟩⟩

theorem norm_iterate_dRep_le {C : ℝ}
    (hb : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ HCSS.lieOf G) →
      ‖l.foldr (dRep π) v‖ ≤ C ^ (l.length + 1) * l.length.factorial * (l.map mnorm).prod)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    ‖(dRep π X)^[m] v‖ ≤ C ^ (m + 1) * m.factorial * mnorm X ^ m := by
  have hfold : ∀ k, List.foldr (dRep π) v (List.replicate k X) = (dRep π X)^[k] v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']
  have h := hb (List.replicate m X) (fun Y hY => by rw [List.eq_of_mem_replicate hY]; exact hX)
  rw [hfold, List.length_replicate, List.map_replicate, List.prod_replicate] at h
  exact h

theorem mnorm_nonneg' (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X := by
  unfold mnorm
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _

theorem hasSum_orbit_of_wordBound : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) {v : H} (hs : IsSmoothVec G π v)
    (hw : WordBound G π v), ∃ r : ℝ, 0 < r ∧ ∀ X ∈ HCSS.lieOf G, mnorm X < r →
      HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (dRep π X)^[m] v) (π (NormedSpace.exp X) v) := by
  intro n G H _ _ _ π hG hrep hc v hs hw
  obtain ⟨C, hC0, hC⟩ := hw
  refine ⟨C⁻¹, inv_pos.mpr hC0, fun X hX hXr => ?_⟩
  obtain ⟨B, hB⟩ := exists_bound_orbit_Icc hc hX
  let f : ℕ → ℝ → H := fun m s => π (NormedSpace.exp (s • X)) ((dRep π X)^[m] v)
  have hf : ∀ m s, HasDerivAt (f m) (f (m + 1) s) s := by
    intro m s
    have := hasDerivAt_orbit_smooth hG hrep (isSmoothVec_iterate_dRep hG hrep hs hX m) hX s
    simpa only [f, Function.iterate_succ_apply'] using this
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hmX := mnorm_nonneg' X
  let a : ℕ → ℝ := fun m => B * (C ^ (m + 1) * m.factorial * mnorm X ^ m)
  have ha : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖f m s‖ ≤ a m := by
    intro m s hs'
    calc ‖f m s‖ ≤ ‖π (NormedSpace.exp (s • X))‖ * ‖(dRep π X)^[m] v‖ := (π _).le_opNorm _
      _ ≤ B * (C ^ (m + 1) * m.factorial * mnorm X ^ m) :=
        mul_le_mul (hB s hs') (norm_iterate_dRep_le hC hX m) (norm_nonneg _) hB0
  have hsum : Summable fun m : ℕ => a m / (m.factorial : ℝ) := by
    have heq : (fun m : ℕ => a m / (m.factorial : ℝ)) = fun m => (B * C) * (C * mnorm X) ^ m := by
      funext m
      have : (m.factorial : ℝ) ≠ 0 := by positivity
      simp only [a]
      field_simp
      ring
    rw [heq]
    refine Summable.mul_left _ (summable_geometric_of_lt_one (mul_nonneg hC0.le hmX) ?_)
    calc C * mnorm X < C * C⁻¹ := mul_lt_mul_of_pos_left hXr hC0
      _ = 1 := mul_inv_cancel₀ hC0.ne'
  have key := hasSum_chain hf ha hsum
  have h1 : f 0 1 = π (NormedSpace.exp X) v := by
    simp [f]
  have h2 : ∀ m, f m 0 = (dRep π X)^[m] v := by
    intro m
    simp [f, hrep.1]
  rw [h1] at key
  simp only [h2] at key
  convert key using 1
  funext m
  rw [show ((m.factorial : ℂ)⁻¹) = (((m.factorial : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.coe_smul]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterInfinityType
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeArch

open InfinitePlace.Completion

variable {E : Type} [Field E] [NumberField E]

theorem infiniteEmbedding_eq (w : InfinitePlace E) (a : (w.Completion)ˣ) :
    (infiniteEmbedding w a : IdeleGroup E) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w a := by
  classical
  refine Units.ext (Prod.ext ?_ rfl)
  show Pi.mulSingle w (a : w.Completion) = Pi.mulSingle w (a : w.Completion)
  congr!

theorem component_on_field (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) (k : Eˣ) :
    (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) (Formalism.L2.Host.atInf _ k) : Circle) : ℂ) =
      (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ n i := by
  have h := (GlobalTheory.InfTypeLocal.infType_iff_local E I φ hφ χ.1 χ.2.1 n).1 hn i k
  rw [HeckeCharacter.infiniteComponent_apply, coe_toIdele, infiniteEmbedding_eq]
  exact h

theorem denseRange_atInf_place (w : InfinitePlace E) : DenseRange (Formalism.L2.Host.atInf w) :=
  ((Function.surjective_eval w).denseRange.comp (GlobalTheory.InfTypeLocal.denseRange_atInf E)
    (continuous_apply w) : DenseRange _)

theorem component_eq (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I)
    (e : (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hec : Continuous e)
    (he : ∀ k : E, e (algebraMap E _ k) = φ i k) (a : ((InfinitePlace.mk (φ i)).Completion)ˣ) :
    (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) a : Circle) : ℂ) =
      (e a / ((‖e a‖ : ℝ) : ℂ)) ^ n i := by
  have h1 : Continuous fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ => e u :=
    hec.comp Units.continuous_val
  have h2 : ∀ u : ((InfinitePlace.mk (φ i)).Completion)ˣ, e u ≠ 0 := fun u =>
    (map_ne_zero _).2 u.ne_zero
  have h3 : ∀ u : ((InfinitePlace.mk (φ i)).Completion)ˣ, ((‖e u‖ : ℝ) : ℂ) ≠ 0 := fun u => by
    exact_mod_cast norm_ne_zero_iff.2 (h2 u)
  have key : (fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ =>
      (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) u : Circle) : ℂ)) =
      fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ => (e u / ((‖e u‖ : ℝ) : ℂ)) ^ n i := by
    refine (denseRange_atInf_place _).equalizer ?_ ?_ ?_
    · exact continuous_subtype_val.comp (map_continuous _)
    · exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _
        fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
    · funext k
      show _ = (e (algebraMap E _ (k : E)) / ((‖e (algebraMap E _ (k : E))‖ : ℝ) : ℂ)) ^ n i
      rw [he]
      exact component_on_field χ hu hφ n hn i k
  exact congrFun key a

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    (starRingEnd ℂ) z / ((‖z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [inv_div, div_eq_div_iff h0 hz, Complex.conj_mul']
  ring

theorem params (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) (hc : (InfinitePlace.mk (φ i)).IsComplex) :
    (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧
      ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  set w := InfinitePlace.mk (φ i) with hw
  set T := toHecke χ hu with hT
  have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hc
  set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc with he
  have hec : Continuous e.symm := (isometryEquivComplexOfIsComplex hc).symm.continuous
  set ψ : ℂˣ →ₜ* Circle := (T.infiniteComponent w).comp (unitsContinuousHom e.symm hec) with hψ
  obtain ⟨p, -, huniq⟩ := existsUnique_complexUnits_circle ψ
  have hι : ∀ z : ℂˣ, extensionEmbedding w ((unitsContinuousHom e.symm hec z : (w.Completion)ˣ) : w.Completion) = z :=
    fun z => e.apply_symm_apply (z : ℂ)
  have hnorm : ∀ z : ℂˣ, ‖((unitsContinuousHom e.symm hec z : (w.Completion)ˣ) : w.Completion)‖ = ‖(z : ℂ)‖ := fun z => by
    rw [← hι z]
    exact ((isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm
  have h1 : ∀ z : ℂˣ, (ψ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (T.infiniteWeight w, 2 * T.infiniteTau w).1 *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((((T.infiniteWeight w, 2 * T.infiniteTau w).2 : ℝ) : ℂ) * Complex.I) := fun z => by
    have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
    show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
    rw [HeckeCharacter.infiniteComponent_eq, hι, hnorm, InfinitePlace.mult, if_neg hnr,
      ofReal_pow_cpow hpos]
    congr 2
    push_cast
    ring
  have h2 : ∃ s : ℤ, s.natAbs = (n i).natAbs ∧ ∀ z : ℂˣ, (ψ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (s, (0 : ℝ)).1 *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((((s, (0 : ℝ)).2 : ℝ) : ℂ) * Complex.I) := by
    have h0 : ∀ k : E, extensionEmbedding w (algebraMap E _ k) = w.embedding k := fun k =>
      extensionEmbedding_coe w (WithAbs.toAbs _ k)
    have hcont := (isometry_extensionEmbedding w).continuous
    rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
    · refine ⟨n i, rfl, fun z => ?_⟩
      have := component_eq χ hu hφ n hn i (extensionEmbedding w) hcont
        (fun k => by rw [h0, hw, h]) (unitsContinuousHom e.symm hec z)
      show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
      rw [this, hι]
      simp
    · refine ⟨-n i, by simp, fun z => ?_⟩
      have := component_eq χ hu hφ n hn i ((starRingEnd ℂ).comp (extensionEmbedding w))
        (Complex.continuous_conj.comp hcont)
        (fun k => by
          rw [RingHom.comp_apply, h0, hw, h]
          simp) (unitsContinuousHom e.symm hec z)
      show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
      rw [this, RingHom.comp_apply, hι, Complex.norm_conj, conj_div_norm z.ne_zero, inv_zpow, ← zpow_neg]
      simp
  obtain ⟨s, hs, h2⟩ := h2
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have e3 := e1.trans e2.symm
  have e4 : T.infiniteWeight w = s := congrArg Prod.fst e3
  have e5 : 2 * T.infiniteTau w = 0 := congrArg Prod.snd e3
  exact ⟨by linarith, by rw [e4, hs]⟩

theorem infiniteParams_of_hasInf : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → ∀ i : I, (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  intro E _ _ _ I _ φ hφ χ hu n hn i
  exact params χ hu (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ) n hn i
    (IsTotallyComplex.isComplex _)

end GlobalTheory.CompanionTheory.HeckeArch
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionConjugationStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_conjugation : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_of_smooth_vector : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G), HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ IsSmoothVec G π (dRep π X v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteEpsilonFactorDependenceOnS
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeBridge

theorem finEps_shift : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ), finEps χ a s = finEps χ a (1 / 2) * (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s) :=
  fun _ _ _ χ a s => GlobalTheory.HeckeEpsAbs.finEps_eq χ a s

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IdealInvariantsOneOrbit
section
namespace GlobalTheory.CompanionTheory.CM

theorem idealInvariantsOneOrbit : GlobalTheory.Published.IdealInvariantsOneOrbitSt :=
  GlobalTheory.Published.ComplexMultiplicationJSt.oneOrbit GlobalTheory.T.complex_multiplication_jacquet_shalika

end GlobalTheory.CompanionTheory.CM
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetOfInducedFiltration
section
theorem _root_.GlobalTheory.T.jacquetOfInducedFiltration' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetOfInducedFiltration k := GlobalTheory.T.jacquet_of_induced_filtration
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_of_linear_group_closed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G), (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X + Y ∈ HCSS.lieOf G) ∧ (∀ (r : ℝ) X, X ∈ HCSS.lieOf G → r • X ∈ HCSS.lieOf G) ∧ (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X * Y - Y * X ∈ HCSS.lieOf G) ∧ (∀ k ∈ G, ∀ X ∈ HCSS.lieOf G, k * X * k⁻¹ ∈ HCSS.lieOf G) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBoundStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_coefficient_norm_bound : ∀ {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hli : LinearIndependent ℝ b), ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstantStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nelson_exists_word_growth_constant : ∀ {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {d : ℕ} (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a) (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖) (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V), ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ C ^ (l.length + 1) * l.length.factorial * ‖u‖ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson.word_growth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspaceStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vectors_invariant_subspace : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π), (∀ u v : H, IsSmoothVec G π u → IsSmoothVec G π v → IsSmoothVec G π (u + v)) ∧ (∀ (c : ℂ) (v : H), IsSmoothVec G π v → IsSmoothVec G π (c • v)) ∧ (∀ g ∈ G, ∀ v : H, IsSmoothVec G π v → IsSmoothVec G π (π g v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed <;> assumption)
end

