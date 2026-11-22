import Mathlib
import GroundTheory.PAdicHodge.ConvergesAtOfNormLeSeq
import GroundTheory.PAdicHodge.BoundOfEventuallyAntitone
import GroundTheory.PAdicHodge.Bundle0006
import GroundTheory.PAdicHodge.Bundle0008
import GroundTheory.PAdicHodge.ExtRobbaFixedSum
import GroundTheory.PAdicHodge.WAFracAnn
import GroundTheory.PAdicHodge.ToUntiltFieldEqZeroIff
import GroundTheory.PAdicHodge.ExtRobbaRoot

-- bundled from GroundTheory.PAdicHodge.ExtRobbaBezout
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  [IsAlgClosed L] [CompleteSpace L]

theorem rootExists : T.RootExists := fun _ _ hx _ hr0 hrρ hm => T.exists_point_dvd hx hr0 hrρ hm

theorem isBezout_robbaTilde : IsBezout T.RobbaTilde := T.isBezout_of_rootExists T.rootExists

end TeichLift

namespace ExtRobba

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)] [CharZero K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP (IsLocalRing.ResidueField (normInteger K)) p]
  [PerfectRing (IsLocalRing.ResidueField (normInteger K)) p]
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [CharP L p] [PerfectRing L p] [IsAlgClosed L]
variable (ι : IsLocalRing.ResidueField (normInteger K) →+* L) {ϖ : normInteger K}
  (hϖ : Irreducible ϖ) (hι : ∀ a, ‖ι a‖ ≤ 1)

end ExtRobba

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.ExtRobbaFixedBridge
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def fixRad : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

def tildeOf (b : T.B) (hb : T.ConvAll b) : T.RobbaTilde := T.ofRad fixRad (T.ofAll b hb fixRad)

variable {T}

theorem ofRad_ofAll_eq (b : T.B) (hb : T.ConvAll b) (σ σ' : Set.Ioo (0 : ℝ) 1) :
    T.ofRad σ (T.ofAll b hb σ) = T.ofRad σ' (T.ofAll b hb σ') := by
  let m : Set.Ioo (0 : ℝ) 1 := ⟨min σ σ', lt_min σ.2.1 σ'.2.1, (min_le_left _ _).trans_lt σ.2.2⟩
  have h1 : (m : ℝ) ≤ σ := min_le_left _ _
  have h2 : (m : ℝ) ≤ σ' := min_le_right _ _
  rw [← T.ofRad_res h1, res_ofAll, ← T.ofRad_res h2, res_ofAll]

theorem tildeOf_eq (b : T.B) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.tildeOf b hb = T.ofRad σ (T.ofAll b hb σ) := ofRad_ofAll_eq b hb fixRad σ

theorem tildeOf_congr {b b' : T.B} (hb : T.ConvAll b) (hb' : T.ConvAll b') (h : b = b') :
    T.tildeOf b hb = T.tildeOf b' hb' := by subst h; rfl

theorem tildeOf_mul {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) :
    T.tildeOf (a * b) (ha.mul hb) = T.tildeOf a ha * T.tildeOf b hb := by
  rw [tildeOf, tildeOf, tildeOf, ofAll_mul, map_mul]

theorem convAll_πB : T.ConvAll T.πB := by
  have := convAll_πB_zpow (T := T) 1
  rwa [zpow_one] at this

theorem tildeOf_πB : T.tildeOf T.πB convAll_πB = T.πTilde := by
  rw [tildeOf, ← T.ofRad_πExt fixRad]
  rfl

def shiftCorr (τ : AddAut T.B) (s : ℤ) (b : T.B) : T.B :=
  if 0 ≤ s then ∑ l ∈ Finset.range s.toNat, ((l : ℤ) • τ) b
  else -∑ l ∈ Finset.range (-s).toNat, ((-((l : ℤ) + 1)) • τ) b

namespace TeichFrob

variable (F : T.TeichFrob)

theorem tildeFrob_tildeOf {b : T.B} (hb : T.ConvAll b) :
    F.tildeFrob (T.tildeOf b hb) = T.tildeOf (F.toB b) (F.convAll_toB hb) := by
  rw [tildeOf, tildeOf, F.tildeFrob_ofRad, F.extFrob_ofAll]
  exact ofRad_ofAll_eq _ _ _ _

def tildeW (y : T.RobbaTilde) : T.RobbaTilde := T.πTilde * F.tildeFrob y

end TeichFrob

namespace TeichFrob

variable (F : T.TeichFrob)

end TeichFrob

theorem DigLe.π_pow_mul {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) (N : ℕ) :
    T.DigLe (T.π ^ N * x) Θ := by
  induction N with
  | zero => simpa using hx
  | succ N ih => rw [pow_succ', mul_assoc]; exact (digLe_π_mul_iff hΘ).2 ih

theorem exists_eq_π_pow_mul_digLe {x : Γ} {M : ℕ} (hx : x ∈ Ideal.span {T.π ^ M}) {Θ : ℝ}
    (hd : T.DigLe x Θ) : ∃ x', x = T.π ^ M * x' ∧ T.DigLe x' Θ := by
  obtain ⟨x', rfl⟩ := T.mem_span_pow.1 hx
  refine ⟨x', rfl, fun n => ?_⟩
  have := hd (n + M)
  rwa [T.coeff_π_pow_mul_add] at this

theorem gaussNorm_π_pow_mul_le {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) (M : ℕ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) : gaussNorm (T.zcoeff (T.π ^ M * x)) r ≤ r ^ M * Θ := by
  have hπ : ConvergesAt (T.zcoeff (T.π ^ M)) r := by
    rw [T.zcoeff_π_pow]; exact convergesAt_pi_single _ _ _
  rw [T.gaussNorm_zcoeff_mul hr0 hr1 hπ (hx.convergesAt hr0 hr1), T.zcoeff_π_pow,
    gaussNorm_pi_single _ _ hr0, norm_one, one_mul, zpow_natCast]
  exact mul_le_mul_of_nonneg_left (hx.gaussNorm_le hΘ hr0 hr1) (pow_nonneg hr0.le M)

end TeichLift

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.WAFracAnnPt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0}

def ξAnn (ξ : T.int) : T.Ann ρ0 σ0 := T.coeAnn ⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩

theorem ξAnn_eq_toAnn (ξ : T.int) : T.ξAnn (ρ0 := ρ0) (σ0 := σ0) ξ = T.toAnn ρ0 σ0 (T.ξExt ξ ρ0) := by
  rw [ξExt, toAnn_coe]; rfl

variable {ξ : T.int} (hξ : T.IsPrimOne ξ)

include hξ in
theorem annNorm_ξAnn (r : AnnRad ρ0 σ0) :
    T.annNorm ρ0 σ0 r (T.ξAnn ξ) = max (T.ptRad ξ) r := by
  rw [ξAnn_eq_toAnn, annNorm_toAnn, T.extNorm_ξExt hξ]; rfl

include hξ in
theorem ptRad_le_annNorm_ξAnn (r : AnnRad ρ0 σ0) : T.ptRad ξ ≤ T.annNorm ρ0 σ0 r (T.ξAnn ξ) := by
  rw [T.annNorm_ξAnn hξ]; exact le_max_left _ _

variable (hr : T.ptRad ξ ∈ Set.Icc (σ0 : ℝ) ρ0)

def ptAnnRad : AnnRad ρ0 σ0 := ⟨T.ptRad ξ, hr⟩

def coreEval : T.AnnCore ρ0 σ0 →+* T.UntiltField hξ := T.ptEvalEconOf hξ hr.2

theorem norm_coreEval_le (b : T.AnnCore ρ0 σ0) :
    ‖T.coreEval hξ hr b‖ ≤ gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) (T.ptAnnRad hr) :=
  T.norm_ptEvalB_le hξ (T.convergesAt_coreVal b (T.ptAnnRad hr))

theorem uniformContinuous_coreEval : UniformContinuous (T.coreEval hξ hr) :=
  LipschitzWith.uniformContinuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
    refine (T.norm_coreEval_le hξ hr (a - b)).trans ?_
    rw [dist_annCore]
    exact T.gaussNorm_coreVal_le (a - b) (T.ptAnnRad hr))

def annEval : T.Ann ρ0 σ0 →+* T.UntiltField hξ :=
  Completion.extensionHom (T.coreEval hξ hr) (T.uniformContinuous_coreEval hξ hr).continuous

theorem annEval_coe (b : T.AnnCore ρ0 σ0) :
    T.annEval hξ hr (b : T.Ann ρ0 σ0) = T.ptEvalB hξ (T.coreVal ρ0 σ0 b) :=
  Completion.extensionHom_coe _ _ b

theorem annEval_coeAnn (b : T.Econ ρ0) : T.annEval hξ hr (T.coeAnn b) = T.ptEvalB hξ b :=
  T.annEval_coe hξ hr _

theorem continuous_annEval : Continuous (T.annEval hξ hr) := Completion.continuous_extension

theorem norm_annEval_le (x : T.Ann ρ0 σ0) :
    ‖T.annEval hξ hr x‖ ≤ T.annNorm ρ0 σ0 (T.ptAnnRad hr) x :=
  Completion.induction_on x
    (isClosed_le ((T.continuous_annEval hξ hr).norm) (T.continuous_annNorm _))
    fun b => by rw [annEval_coe, annNorm_coe]; exact T.norm_coreEval_le hξ hr b

theorem annEval_toAnn (w : T.RobbaExt ρ0) : T.annEval hξ hr (T.toAnn ρ0 σ0 w) = T.ptEval hξ hr.2 w :=
  Completion.induction_on w
    (isClosed_eq ((T.continuous_annEval hξ hr).comp T.continuous_toAnn) (T.continuous_ptEval hξ hr.2))
    fun b => by rw [toAnn_coe, annEval_coeAnn, ptEval_coe]

theorem annEval_ξAnn : T.annEval hξ hr (T.ξAnn ξ) = 0 := by
  rw [ξAnn_eq_toAnn, annEval_toAnn, T.ptEval_ξExt hξ hr.2]

theorem exists_bdd_approx_ann (x : T.Ann ρ0 σ0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (U : Γ) (hU : T.IsBddElt U), ∀ r : AnnRad ρ0 σ0,
      T.annNorm ρ0 σ0 r (x - T.coeAnn ⟨T.bddB U N, T.bddB_mem_Econ hU N ρ0⟩) < ε := by
  obtain ⟨b, hb⟩ := T.exists_coeAnn_near x (half_pos hε)
  obtain ⟨N, U, hU, hUb⟩ := T.exists_bdd_approx (b : T.RobbaExt ρ0) σ0 (half_pos hε)
  refine ⟨N, U, hU, fun r => ?_⟩
  have h2 : T.annNorm ρ0 σ0 r (T.coeAnn b - T.coeAnn ⟨T.bddB U N, T.bddB_mem_Econ hU N ρ0⟩) < ε / 2 := by
    rw [← toAnn_coe, ← toAnn_coe, ← map_sub, annNorm_toAnn]
    exact hUb (annIoc r) r.2.1
  have e : x - T.coeAnn ⟨T.bddB U N, T.bddB_mem_Econ hU N ρ0⟩ =
      (x - T.coeAnn b) + (T.coeAnn b - T.coeAnn ⟨T.bddB U N, T.bddB_mem_Econ hU N ρ0⟩) := by ring
  rw [e]
  exact (T.annNorm_add_le r _ _).trans_lt (max_lt ((hb r).trans (half_lt_self hε))
    (h2.trans (half_lt_self hε)))

theorem annEval_eq_zero_iff (x : T.Ann ρ0 σ0) :
    T.annEval hξ hr x = 0 ↔ ∃ y, x = T.ξAnn ξ * y := by
  constructor
  swap
  · rintro ⟨y, rfl⟩
    rw [map_mul, T.annEval_ξAnn hξ hr, zero_mul]
  intro hx0
  have hr0 := T.ptRad_pos' hξ
  have key : ∀ j : ℕ, ∃ (N : ℕ) (U : Γ) (hU : T.IsBddElt U), ∀ r : AnnRad ρ0 σ0,
      T.annNorm ρ0 σ0 r (x - T.coeAnn ⟨T.bddB U N, T.bddB_mem_Econ hU N ρ0⟩) < 1 / (j + 1) :=
    fun j => T.exists_bdd_approx_ann x Nat.one_div_pos_of_nat
  choose N U hU hUx using key
  set b : ℕ → T.Ann ρ0 σ0 := fun j => T.coeAnn ⟨T.bddB (U j) (N j), T.bddB_mem_Econ (hU j) (N j) ρ0⟩
    with hbdef
  have hbx : ∀ r : AnnRad ρ0 σ0, Tendsto (fun j => T.annNorm ρ0 σ0 r (x - b j)) atTop (𝓝 0) :=
    fun r => squeeze_zero (fun j => T.annNorm_nonneg r _) (fun j => (hUx j r).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

  set v : ℕ → T.UntiltField hξ := fun j => T.ptEvalB hξ (T.bddB (U j) (N j)) with hvdef
  have hvn : Tendsto (fun j => ‖v j‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) (hbx (T.ptAnnRad hr))
    have e : v j = -T.annEval hξ hr (x - b j) := by
      rw [map_sub, hx0, zero_sub, neg_neg, hbdef, annEval_coeAnn]
    rw [e, norm_neg]
    exact T.norm_annEval_le hξ hr _
  obtain ⟨J0, hJ0⟩ := eventually_atTop.1 (hvn.eventually (ge_mem_nhds one_pos))

  have loc : ∀ j, ∃ (Y : Γ) (hY : T.IsBddElt Y) (e : T.Econ ρ0), J0 ≤ j →
      b j = T.ξAnn ξ * T.coeAnn ⟨T.bddB Y (N j), T.bddB_mem_Econ hY (N j) ρ0⟩ + T.coeAnn e ∧
        ∀ r : AnnRad ρ0 σ0, T.annNorm ρ0 σ0 r (T.coeAnn e) ≤ ‖v j‖ := by
    intro j
    by_cases hj : J0 ≤ j
    · obtain ⟨Y, hY, z, hz, V, hV, hUY⟩ := T.exists_bddB_eq_ξ_mul_add hξ (hU j) (N j) (hJ0 j hj)
      have hz1 : ‖z‖ ≤ 1 := hz ▸ hJ0 j hj
      refine ⟨Y, hY, ⟨_, T.coe_teich_mul_mem_Econ hz1 hV⟩, fun _ => ⟨?_, fun r => ?_⟩⟩
      · simp only [hbdef, ξAnn, ← map_mul, ← map_add]
        congr 1
        exact Subtype.ext hUY
      · rw [annNorm_coeAnn]
        show gaussNorm (T.coeffB (algebraMap Γ T.B (T.teich z * V))) r ≤ ‖v j‖
        rw [coeffB_algebraMap, ← hz]
        exact T.gaussNorm_teich_mul_int_le hV (σ0.2.1.trans_le r.2.1) (r.2.2.trans_lt ρ0.2.2)
    · exact ⟨0, ⟨1, one_ne_zero, by simp, by simp [T.int.zero_mem]⟩, 0, fun h => absurd h hj⟩
  choose Y hY e he using loc
  set y : ℕ → T.Ann ρ0 σ0 := fun j => T.coeAnn ⟨T.bddB (Y j) (N j), T.bddB_mem_Econ (hY j) (N j) ρ0⟩
    with hydef
  have hξy : ∀ r : AnnRad ρ0 σ0, Tendsto (fun j => T.annNorm ρ0 σ0 r (x - T.ξAnn ξ * y j)) atTop (𝓝 0) := by
    intro r
    have hmax : Tendsto (fun j => max (T.annNorm ρ0 σ0 r (x - b j)) ‖v j‖) atTop (𝓝 0) := by
      simpa using (hbx r).max hvn
    refine squeeze_zero' (Eventually.of_forall fun j => T.annNorm_nonneg r _) ?_ hmax
    filter_upwards [eventually_ge_atTop J0] with j hj
    obtain ⟨hbj, hej⟩ := he j hj
    have : x - T.ξAnn ξ * y j = (x - b j) + T.coeAnn (e j) := by
      rw [hbj]; simp only [hydef]; ring
    rw [this]
    exact (T.annNorm_add_le _ _ _).trans (max_le_max le_rfl (hej r))

  have hcau : ∀ r : AnnRad ρ0 σ0, ∀ ε > 0, ∃ J, ∀ j ≥ J, ∀ k ≥ J, T.annNorm ρ0 σ0 r (y j - y k) ≤ ε := by
    intro r ε hε
    have hεr : 0 < ε * T.ptRad ξ := mul_pos hε hr0
    obtain ⟨J, hJ⟩ := eventually_atTop.1 ((hξy r).eventually (gt_mem_nhds hεr))
    refine ⟨J, fun j hj k hk => ?_⟩
    have hjk : T.annNorm ρ0 σ0 r (T.ξAnn ξ * (y j - y k)) < ε * T.ptRad ξ := by
      have e2 : T.ξAnn ξ * (y j - y k) = -(x - T.ξAnn ξ * y j) + (x - T.ξAnn ξ * y k) := by ring
      rw [e2]
      refine (T.annNorm_add_le _ _ _).trans_lt (max_lt ?_ (hJ k hk))
      rw [annNorm_neg]; exact hJ j hj
    rw [annNorm_mul] at hjk
    have hξge := T.ptRad_le_annNorm_ξAnn hξ r
    by_contra hcon
    have hcon' := not_le.1 hcon
    have := mul_le_mul hξge hcon'.le hε.le (T.annNorm_nonneg r _)
    linarith
  obtain ⟨y₀, hy₀⟩ := T.exists_limit_ann fun ε hε => by
    obtain ⟨J1, h1⟩ := hcau (annIn ρ0 σ0) ε hε
    obtain ⟨J2, h2⟩ := hcau (annOut ρ0 σ0) ε hε
    exact ⟨max J1 J2, fun j hj k hk => ⟨h1 j (le_of_max_le_left hj) k (le_of_max_le_left hk),
      h2 j (le_of_max_le_right hj) k (le_of_max_le_right hk)⟩⟩
  refine ⟨y₀, T.eq_of_annNorm_sub ?_ ?_⟩
  all_goals
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (T.annNorm_nonneg _ _)
    rw [zero_add]
  · obtain ⟨J1, hJ1⟩ := eventually_atTop.1 ((hξy (annIn ρ0 σ0)).eventually (gt_mem_nhds hε))
    have hB : T.annNorm ρ0 σ0 (annIn ρ0 σ0) (T.ξAnn ξ) * ε / (T.annNorm ρ0 σ0 (annIn ρ0 σ0) (T.ξAnn ξ) + 1)
        < ε := by
      have hξ0 := T.annNorm_nonneg (annIn ρ0 σ0) (T.ξAnn ξ)
      rw [mul_div_assoc]
      calc T.annNorm ρ0 σ0 (annIn ρ0 σ0) (T.ξAnn ξ) * (ε / (T.annNorm ρ0 σ0 (annIn ρ0 σ0) (T.ξAnn ξ) + 1))
          < (T.annNorm ρ0 σ0 (annIn ρ0 σ0) (T.ξAnn ξ) + 1) * (ε / (T.annNorm ρ0 σ0 (annIn ρ0 σ0) (T.ξAnn ξ) + 1)) :=
            mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
        _ = ε := by field_simp
    have hpos : 0 < ε / (T.annNorm ρ0 σ0 (annIn ρ0 σ0) (T.ξAnn ξ) + 1) := by
      have := T.annNorm_nonneg (annIn ρ0 σ0) (T.ξAnn ξ); positivity
    obtain ⟨J2, hJ2⟩ := eventually_atTop.1 (((hy₀ (annIn ρ0 σ0)).eventually (gt_mem_nhds hpos)))
    set j := max J1 J2
    have e : x - T.ξAnn ξ * y₀ = (x - T.ξAnn ξ * y j) + T.ξAnn ξ * (y j - y₀) := by ring
    rw [e]
    refine (T.annNorm_add_le _ _ _).trans (max_le (hJ1 j (le_max_left _ _)).le ?_)
    rw [annNorm_mul]
    exact (mul_le_mul_of_nonneg_left (hJ2 j (le_max_right _ _)).le (T.annNorm_nonneg _ _)).trans
      (by rw [← mul_div_assoc]; exact hB.le)
  · obtain ⟨J1, hJ1⟩ := eventually_atTop.1 ((hξy (annOut ρ0 σ0)).eventually (gt_mem_nhds hε))
    have hB : T.annNorm ρ0 σ0 (annOut ρ0 σ0) (T.ξAnn ξ) * ε / (T.annNorm ρ0 σ0 (annOut ρ0 σ0) (T.ξAnn ξ) + 1)
        < ε := by
      have hξ0 := T.annNorm_nonneg (annOut ρ0 σ0) (T.ξAnn ξ)
      rw [mul_div_assoc]
      calc T.annNorm ρ0 σ0 (annOut ρ0 σ0) (T.ξAnn ξ) * (ε / (T.annNorm ρ0 σ0 (annOut ρ0 σ0) (T.ξAnn ξ) + 1))
          < (T.annNorm ρ0 σ0 (annOut ρ0 σ0) (T.ξAnn ξ) + 1) * (ε / (T.annNorm ρ0 σ0 (annOut ρ0 σ0) (T.ξAnn ξ) + 1)) :=
            mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
        _ = ε := by field_simp
    have hpos : 0 < ε / (T.annNorm ρ0 σ0 (annOut ρ0 σ0) (T.ξAnn ξ) + 1) := by
      have := T.annNorm_nonneg (annOut ρ0 σ0) (T.ξAnn ξ); positivity
    obtain ⟨J2, hJ2⟩ := eventually_atTop.1 (((hy₀ (annOut ρ0 σ0)).eventually (gt_mem_nhds hpos)))
    set j := max J1 J2
    have e : x - T.ξAnn ξ * y₀ = (x - T.ξAnn ξ * y j) + T.ξAnn ξ * (y j - y₀) := by ring
    rw [e]
    refine (T.annNorm_add_le _ _ _).trans (max_le (hJ1 j (le_max_left _ _)).le ?_)
    rw [annNorm_mul]
    exact (mul_le_mul_of_nonneg_left (hJ2 j (le_max_right _ _)).le (T.annNorm_nonneg _ _)).trans
      (by rw [← mul_div_assoc]; exact hB.le)

theorem exists_annEval_eq (w : T.UntiltField hξ) : ∃ e : T.Econ ρ0, T.annEval hξ hr (T.coeAnn e) = w := by
  obtain ⟨z, V, hV, -, -, hzV⟩ := T.exists_lift_value' hξ w
  have hc : algebraMap Γ T.B (T.teich z * V) ∈ T.Econ ρ0 := by
    rw [mem_Econ, coeffB_algebraMap]
    exact T.convergesAt_zcoeff_mul ρ0.2.1 ρ0.2.2 (T.convergesAt_teich z _)
      (T.convergesAt_of_mem_int hV ρ0.2.1 ρ0.2.2)
  refine ⟨⟨_, hc⟩, ?_⟩
  rw [annEval_coeAnn]
  show T.ptEvalB hξ (algebraMap Γ T.B (T.teich z * V)) = w
  rw [ptEvalB_algebraMap, T.ptE_teich_mul hξ z V
    (T.convergesAt_of_mem_int hV (T.ptRad_pos' hξ) (T.ptRad_lt_one' hξ)), hzV]

theorem exists_bezout_ann {x : T.Ann ρ0 σ0} (hx : T.annEval hξ hr x ≠ 0) :
    ∃ a b : T.Ann ρ0 σ0, a * T.ξAnn ξ + b * x = 1 := by
  obtain ⟨e, he⟩ := T.exists_annEval_eq hξ hr (T.annEval hξ hr x)⁻¹
  have h0 : T.annEval hξ hr (1 - T.coeAnn e * x) = 0 := by
    rw [map_sub, map_one, map_mul, he, inv_mul_cancel₀ hx, sub_self]
  obtain ⟨y, hy⟩ := (T.annEval_eq_zero_iff hξ hr _).1 h0
  exact ⟨y, T.coeAnn e, by linear_combination -hy⟩

end TeichLift

end GroundTheory.PAdicHodge
end
end

