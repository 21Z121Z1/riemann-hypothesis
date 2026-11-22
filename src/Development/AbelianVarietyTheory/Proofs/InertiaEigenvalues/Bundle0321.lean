import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0195
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0162
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremPhiModulesExactTriple
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.InertiaEigenvalues

theorem lifting_along_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  intro O K _ _ _ _ _ l e a _ _ _ _ _ _ ι₀ ι₁ ι₂ _ _ _ _ _ _ η H D₀ D₁ D₂ F G N Sig U hH y₂ hy₂ m₂ hm₂ h0
  obtain ⟨hex, hnum, htype, hch2⟩ := hH
  have hl : l.Prime := Fact.out
  have hts : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (NeZero.ne a)
  obtain ⟨hr1, hr4, hrper⟩ := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hl ha hts Sig N hnum.frob_mem hnum.zero_mem_Sig
    hnum.card_Sig hnum.two_le
  set r := maxPeriod l Sig with hr
  obtain ⟨hL1, hL2, hL3, -, -, hL6⟩ :=
    GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η r hnum.two_le hnum.one_le hnum.lt hr4 hnum.large
  have hl2 : l ≠ 2 := by
    have h8 : 8 ≤ N ^ 3 := by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hnum.two_le 3
    have := hnum.large
    generalize H * N ^ 2 = A at this
    generalize N ^ 3 = B at this h8
    omega

  have hB : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H :=
    ⟨hnum.frob_mem, hnum.zero_mem_Sig, hnum.card_Sig, hnum.two_le, hnum.range_U, hnum.zero_mem_U,
      hnum.card_U, hnum.one_le, hnum.lt, hnum.large⟩
  obtain ⟨-, hkM, -, hkMinv, -, hkY'⟩ :=
    GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow O K l e a ι₁ ι₂ Sig U N η H hB D₁ D₂ htype hch2 G hex.finiteLength
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N r with hρ
  have hcast : ∀ v : Vec K a ι₂, (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N : ℕ) • v = (l : K) ^ ρ • v := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul K]
    push_cast
    rfl
  obtain ⟨y₁, hy₁, hGy₁⟩ := hkY' y₂ hy₂
  obtain ⟨m₁, hm₁, hGm₁⟩ := hkMinv m₂ hm₂
  rw [hcast] at hGy₁ hGm₁
  have hG1 : G.app (y₁ + D₁.phi m₁) = (l : K) ^ ρ • (y₂ + D₂.phi m₂) := by
    rw [map_add, G.app_phi, hGy₁, hGm₁, map_smul, smul_add]

  set ω := D₁.Mon (y₁ + D₁.phi m₁) with hω
  have hω1 : (l : K) ^ (η * (r + 1)) • ω ∈ D₁.Z :=
    GlobalTheory.T.breuilKisinDescent_pow_smul_monodromy_add_phi_mem O K l e a ι₁ η H D₁ hnum.one_le hnum.lt (by omega) hL2 r hr1
      (fun τ c hc => hrper c (htype.chars_subset τ hc)) hL6 hl2 y₁ hy₁ m₁ hm₁

  obtain ⟨hjmp, -, hinj, hker⟩ := GlobalTheory.T.breuilKisin_exactTriple_jumps_characters_lift O K l e a ι₀ ι₁ ι₂ η H D₀ D₁ D₂ F G hex
  have hGω : G.onPol ((l : K) ^ (η * (r + 1)) • ω) = 0 := by
    rw [map_smul, hω, G.onPol_Mon, hG1, map_smul, h0, smul_zero, smul_zero]
  obtain ⟨w₀, hw₀, hFw₀⟩ := hker ρ (fun y hy => by
      obtain ⟨x, hx, h⟩ := hkM y hy
      exact ⟨x, hx, h.trans (hcast y)⟩) _ hω1 hGω
  rw [smul_smul, ← pow_add] at hFw₀
  have hy₁Y : y₁ + D₁.phi m₁ ∈ D₁.Yl := by
    refine D₁.desc.mem_Yl_iff.2 ⟨0, ?_⟩
    rw [pow_zero, one_smul]
    refine add_mem (D₁.desc.Y'_le_Y η hy₁) ⟨?_, fun g => ?_⟩
    · exact (mem_divE (l := l) (e := e)).2 (D₁.upper _ (D₁.phi_mem_L hm₁.1))
    · rw [D₁.desc.act_phi, hm₁.2 g]
  obtain ⟨-, wm, hwm, hLcwm⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι₁ η H D₁ _ hy₁Y
  have hIm := (GlobalTheory.T.breuilKisinDescent_monodromy_image_valuation O K l e a ι₁ η H D₁ U N htype.jumps_subset
    (fun i hi => Finset.mem_Icc.2 (hnum.range_U i hi)) hnum.card_U hnum.lt).1
  obtain ⟨w', hw', hFw'⟩ := GlobalTheory.T.lift_image_eulerE_invariants_quotient O K l e a ι₀ ι₁ η H D₀ D₁ F U hIm ω
    ⟨wm, hwm, hLcwm⟩ _ ⟨w₀, D₀.desc.mem_Zl_of_mem_Z hw₀, hFw₀⟩

  set c₂ := GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂ N η r with hc₂
  have hw₀eq : (l : K) ^ c₂ • D₀.Lc w' = w₀ := by
    apply hinj
    rw [map_smul, hFw', hFw₀, hc₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁, add_comm]
  have hjmp0 : D₀.jumps ⊆ (U : Set ℤ) := hjmp.trans htype.jumps_subset
  have hIcc : U ⊆ Finset.Icc (-(η : ℤ)) H := fun i hi => Finset.mem_Icc.2 (hnum.range_U i hi)
  obtain ⟨y, hy, hLcy⟩ := GlobalTheory.T.exists_mem_tameDescent_class_eq_of_pow_mem O K l e a ι₀ η H D₀ U N hjmp0 hIcc hnum.card_U
    hnum.lt (by omega) hL2 c₂ w' hw' (hw₀eq ▸ hw₀)

  have hff := (GlobalTheory.T.breuilKisinDescent_finite_free_invertPrime O K l e a ι₀ η H D₀).1
  obtain ⟨y₀, hy₀, hMy₀⟩ := GlobalTheory.T.exists_monodromy_eq_leadingCoeff_breuilKisinDescent O K l e a ι₀ η H D₀ U N hjmp0 hIcc hnum.card_U
    hnum.one_le hnum.lt hL3 hL2 (GlobalTheory.T.isAdicComplete_twistedInvariantLattice O K l e a ι₀ η H D₀)
    (GlobalTheory.T.isHausdorff_invariants_quotient_of_finiteFree O K l e a ι₀ η H D₀ hff) y hy

  have hGF : ∀ v : Vec K a ι₀, G.app (F.app v) = 0 := by
    intro v
    rw [eq_sum_bas v, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [F.app_smul_tot, G.app_smul_tot]
    have h1 : F.app (bas i) ∈ D₁.M := F.app_mem_M (D₀.bas_mem_M i)
    rw [(hex.exact _ h1).2 ⟨bas i, D₀.bas_mem_M i, rfl⟩, smul_zero]
  set n := c₂ + η + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL N η with hn
  have hs {κ : Type} (v : Vec K a κ) : ((l : O) ^ n) • v = (l : K) ^ n • v := by
    rw [← algebraMap_smul K, map_pow, map_natCast]
  have h3 : ((l : O) ^ n • y₁ - F.app y₀) + D₁.phi ((l : O) ^ n • m₁) =
      (l : K) ^ n • (y₁ + D₁.phi m₁) - F.app y₀ := by
    rw [hs, hs, map_smul, smul_add]
    abel
  refine ⟨_, sub_mem (Submodule.smul_mem _ ((l : O) ^ n) hy₁) (F.app_mem_Y' hy₀), _,
    Submodule.smul_mem _ ((l : O) ^ n) hm₁, ?_, ?_⟩
  · rw [h3, map_sub, map_smul, ← hω, ← F.onPol_Mon, hMy₀, hLcy, map_smul, hFw']
    exact sub_self _
  · rw [h3, map_sub, G.app.map_smul_of_tower, hGF, sub_zero, hG1, smul_smul, ← pow_add]
    rfl

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentCyclotomicEigenvectorsWeights
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem actC_apply_eq_σC {l : ℕ} [Fact l.Prime] (g : GQ l) (y : ℂ_[l]) :
    GlobalTheory.Cyc.Model.actC g y = Formalism.Per.σC g y := by
  change GlobalTheory.Cyc.Model.extHom g y = Formalism.Per.σC g y
  have hc : Continuous (Formalism.Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Formalism.Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (GlobalTheory.Cyc.Model.extHom_cont g) hc
  | ih x => exact (GlobalTheory.Cyc.Model.extHom_coe g x).trans (GlobalTheory.RingBasics.σC_coe g x).symm

theorem linIndep_of_eigen_weights : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n ℂ_[l]) (ι : Type) [Fintype ι] (v : ι → n → ℂ_[l]) (w : ι → ℤ), (∀ (g : ↥(GK K)) j, (A g).mulVec (fun i => Formalism.Per.σC (g : GQ l) (v j i)) = algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) • v j) → (∀ (a : ℤ) (c : ι → Om l), (∀ j, c j ∈ K.1) → (∀ j, w j ≠ a → c j = 0) → ∑ j, (c j : ℂ_[l]) • v j = 0 → c = 0) → LinearIndependent ℂ_[l] v := by
  intro l _ P n _ _ K A ι _ v w hA hK
  classical

  set e : GQ l → ℤ → ℂ_[l] := fun g k => algebraMap ℚ_[l] ℂ_[l] ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) with he
  have e_ne : ∀ g k, e g k ≠ 0 := fun g k => by
    simp only [he, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[l] ℂ_[l]).injective, Units.ne_zero,
      not_false_eq_true]
  have e_sub : ∀ g (a b : ℤ), e g (a - b) * e g b = e g a := fun g a b => by
    simp only [he, ← map_mul, ← Units.val_mul, ← zpow_add, sub_add_cancel]
  have hcyc : GlobalTheory.Cyc.IsCyc P.χQ := P.χQ_cyc
  rw [Fintype.linearIndependent_iff]
  suffices key : ∀ m : ℕ, ∀ a : ι → ℂ_[l], (Finset.univ.filter (fun j => a j ≠ 0)).card = m →
      ∑ j, a j • v j = 0 → a = 0 by
    intro a ha j
    exact congrFun (key _ a rfl ha) j
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hcard hrel
  by_contra hne
  obtain ⟨j0, hj0⟩ : ∃ j0, a j0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set b : ι → ℂ_[l] := fun j => (a j0)⁻¹ * a j with hb
  have hbrel : ∑ j, b j • v j = 0 := by
    simp only [hb, mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  have hb0 : b j0 = 1 := by simp only [hb, inv_mul_cancel₀ hj0]
  have hsupp : ∀ j, b j ≠ 0 ↔ a j ≠ 0 := fun j => by
    simp only [hb, ne_eq, mul_eq_zero, inv_eq_zero, hj0, false_or]

  have htw : ∀ g : ↥(GK K), ∀ j, Formalism.Per.σC (g : GQ l) (b j) * e g (w j) = e g (w j0) * b j := by
    intro g
    have h1 : (∑ j, Formalism.Per.σC (g : GQ l) (b j) • (fun i => Formalism.Per.σC (g : GQ l) (v j i))) = 0 := by
      funext i
      have hi := congrFun hbrel i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      rw [← map_zero (Formalism.Per.σC (g : GQ l)), ← hi, map_sum]
      simp only [map_mul]
    have h2 : ∑ j, (Formalism.Per.σC (g : GQ l) (b j) * e g (w j)) • v j = 0 := by
      have := congrArg (fun u => (A g).mulVec u) h1
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hA, Matrix.mulVec_zero, smul_smul] at this
      exact this
    set d : ι → ℂ_[l] := fun j => Formalism.Per.σC (g : GQ l) (b j) * e g (w j) - e g (w j0) * b j with hd
    have hdrel : ∑ j, d j • v j = 0 := by
      simp only [hd, sub_smul, Finset.sum_sub_distrib]
      rw [h2]
      simp only [mul_smul, ← Finset.smul_sum, hbrel, smul_zero, sub_zero]
    have hdsub : Finset.univ.filter (fun j => d j ≠ 0) ⊆ (Finset.univ.filter (fun j => a j ≠ 0)).erase j0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
      refine ⟨?_, ?_⟩
      · rintro rfl
        apply hj
        simp only [hd, hb0, map_one, one_mul, mul_one, sub_self]
      · rw [← hsupp]
        intro hbj
        apply hj
        simp only [hd, hbj, map_zero, zero_mul, mul_zero, sub_self]
    have hlt : (Finset.univ.filter (fun j => d j ≠ 0)).card < m := by
      rw [← hcard]
      refine lt_of_le_of_lt (Finset.card_le_card hdsub) (Finset.card_erase_lt_of_mem ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj0
    have hd0 := ih _ hlt d rfl hdrel
    intro j
    exact sub_eq_zero.1 (congrFun hd0 j)

  have hin : ∀ j, ∃ x : Om l, x ∈ K.1 ∧ (x : ℂ_[l]) = b j ∧ (w j ≠ w j0 → x = 0) := by
    intro j
    have hfix : ∀ g ∈ GK K, GlobalTheory.Cyc.chiC P.χQ (w j - w j0) g * GlobalTheory.Cyc.Model.actC g (b j) = b j := by
      intro g hg
      rw [actC_apply_eq_σC]
      have h := htw ⟨g, hg⟩ j
      change Formalism.Per.σC g (b j) * e g (w j) = e g (w j0) * b j at h
      change e g (w j - w j0) * Formalism.Per.σC g (b j) = b j
      apply mul_left_cancel₀ (e_ne g (w j0))
      rw [← h, ← e_sub g (w j) (w j0)]
      ring
    have hT := GlobalTheory.Cyc.tate_invariants_twist l GlobalTheory.Cyc.Model.actC P.χQ GlobalTheory.Cyc.Model.isActC_actC hcyc K
      (w j - w j0) (b j) hfix
    by_cases hw : w j = w j0
    · obtain ⟨x, hxK, hx⟩ := hT.2 (sub_eq_zero.2 hw)
      exact ⟨x, hxK, hx, fun h => absurd hw h⟩
    · have hbj : b j = 0 := hT.1 (sub_ne_zero.2 hw)
      exact ⟨0, K.1.zero_mem, by rw [hbj]; exact UniformSpace.Completion.coe_zero, fun _ => rfl⟩
  choose c hcK hcb hc0 using hin
  have hc : c = 0 := hK (w j0) c hcK hc0 (by simp only [hcb]; exact hbrel)
  have : b j0 = 0 := by rw [← hcb j0, hc, Pi.zero_apply]; exact UniformSpace.Completion.coe_zero
  rw [hb0] at this
  exact one_ne_zero this

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationCocycleRationalContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
open Matrix

namespace GlobalTheory.PMon

theorem matrixHomRepresentationCocycleCoords_cocycle {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {G : Type*} [Group G] (ρ : G →* GL (a ⊕ b) R) (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (c : G → Matrix a b R)
    (hρ : ∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) = Matrix.fromBlocks (ρ₁ g : Matrix a a R) (c g) 0 (ρ₂ g : Matrix b b R))
    (g h : G) :
    extCoc ρ₂ c (g * h) = extCoc ρ₂ c g + ((homRep ρ₁ ρ₂ g : GL (a × b) R) : Matrix (a × b) (a × b) R).mulVec (extCoc ρ₂ c h) := by
  have hc : c (g * h) = (ρ₁ g : Matrix a a R) * c h + c g * (ρ₂ h : Matrix b b R) := by
    have := congrArg (fun M : GL (a ⊕ b) R => Matrix.toBlocks₁₂ (M : Matrix (a ⊕ b) (a ⊕ b) R)) (map_mul ρ g h)
    simp only [Units.val_mul, hρ, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂] at this
    simpa using this
  unfold extCoc
  rw [homRep_apply, homUnit_val, kronecker_transpose_mulVec]
  rw [hc, map_mul, _root_.mul_inv_rev, Units.val_mul]
  have h2 : (ρ₂ h : Matrix b b R) * (((ρ₂ h)⁻¹ : GL b R) : Matrix b b R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.add_mul, Matrix.mul_assoc (c g), ← Matrix.mul_assoc (ρ₂ h : Matrix b b R), h2, Matrix.one_mul]
  funext p
  simp only [vecM, Pi.add_apply, Matrix.add_apply, Matrix.mul_assoc]
  ring

theorem extCoc_rat_cont_cocycle : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → (∀ g i, fr l r (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) ∧ (∀ i, Continuous fun g => ((extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g h, extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) (g * h) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g + (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK))) g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).mulVec (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) h)) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hrat hρ
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have hent : ∀ g (i : a) (k : b), c g i k = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inr k) := by
    intro g i k; rw [hρ]; rfl
  have hinv : ∀ g (k j : b), (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)) k j =
      (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr j) := by
    intro g k j; rw [← map_inv, hρ]; rfl
  have hform : ∀ g (i : a × b), extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i =
      ∑ k, (ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) *
        (ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) := by
    intro g i
    simp only [extCoc, vecM, MonoidHom.comp_apply, Matrix.mul_apply, hent, hinv]
  have hcι : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
  refine ⟨?_, ?_, ?_⟩
  · intro g i
    rw [hform, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hrat.rat, hrat.rat]
  · intro i
    have : (fun g => ((extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) = fun g =>
        ∑ k, (((ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) : ↥(MaximalUnramifiedExtension l)) : Om l) *
          (((ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      funext g
      rw [hform]
      push_cast
      rfl
    rw [this]
    refine continuous_finset_sum _ fun k _ => ?_
    exact ((hrat.cont _ _).comp hcι).mul ((hrat.cont _ _).comp (continuous_inv.comp hcι))
  · intro g h
    exact matrixHomRepresentationCocycleCoords_cocycle (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hρ (ι g)) g h

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTensorSemistablePeriodRingSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem monSt_surjective_onto {l : ℕ} [Fact l.Prime] (P : LocPrime l) :
    Function.Surjective (monSt P) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a =>
    have hn : ((n + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    refine ⟨-Polynomial.monomial (n + 1) (((n + 1 : ℕ) : ℚ_[l])⁻¹ • a), ?_⟩
    rw [map_neg, monSt_apply, neg_neg, Polynomial.derivative_monomial, Nat.add_sub_cancel,
      ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem monV_surjective_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V],
      Function.Surjective (monV P ℚ_[l] V) := by
  intro l _ P V _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul v b =>
    obtain ⟨c, rfl⟩ := monSt_surjective_onto P b
    exact ⟨v ⊗ₜ c, monV_tmul P v c⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAlgebraMap
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.GroupLayer

variable {l : ℕ} [Fact l.Prime]

theorem v_le_iff (P : LocPrime l) (LL : FinExt l) (x y : ↥LL.1) :
    P.v LL y ≤ P.v LL x ↔ ‖(x : Om l)‖ ≤ ‖(y : Om l)‖ := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL
  by_cases hy : y = 0
  · subst hy
    simp only [AddValuation.map_zero, top_le_iff, AddValuation.top_iff, ZeroMemClass.coe_zero,
      norm_zero, norm_le_zero_iff, ZeroMemClass.coe_eq_zero]
  · have hne : P.v LL y ≠ ⊤ := fun h => hy ((AddValuation.top_iff _).1 h)
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hq, h2, (h1 y q).1 hq.symm]

theorem norm_coe_algebraMap (LL : FinExt l) (a : ℤ_[l]) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) a) : ↥LL.1) : Om l)‖ = ‖a‖ := by
  change ‖algebraMap ℚ_[l] (Om l) (a : ℚ_[l])‖ = ‖(a : ℚ_[l])‖
  simp

theorem norm_pow_sub_one (LL : FinExt l) (a : ℤ_[l]) (k : ℕ) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 ((algebraMap ℤ_[l] ↥(OL LL) a) ^ k) - 1 : ↥LL.1) : Om l)‖
      = ‖a ^ k - 1‖ := by
  rw [← norm_coe_algebraMap LL (a ^ k - 1), map_sub, map_sub, map_one, map_one, map_pow (algebraMap ℤ_[l] ↥(OL LL))]

theorem norm_sub_one (LL : FinExt l) (a : ℤ_[l]) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) a) - 1 : ↥LL.1) : Om l)‖
      = ‖a - 1‖ := by
  simpa only [pow_one] using norm_pow_sub_one LL a 1

noncomputable def congSub (l : ℕ) [Fact l.Prime] (s : ℕ) : Subgroup ℤ_[l]ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(l : ℤ_[l]) ^ s})).toMonoidHom).ker

theorem mem_congSub (s : ℕ) (u : ℤ_[l]ˣ) :
    u ∈ congSub l s ↔ ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← Ideal.Quotient.eq, congSub, MonoidHom.mem_ker,
    Units.ext_iff]
  simp

theorem nonempty_gamS : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l),
    Good K s LL → Nonempty (GamS P K s LL) := by
  intro l _ P K s LL hG
  obtain ⟨emb, hbij, hσ⟩ := GlobalTheory.HWL.exists_letters l P K s LL hG
  obtain ⟨hs1, hs2, hKs, -⟩ := hG
  obtain ⟨χ, hχ, -, honto⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨one, hone1, hone2⟩ := GlobalTheory.HWL.exists_unitLat l K LL
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL
  let χK : ↥(GK K) →* ℤ_[l]ˣ := χ.comp (GK K).subtype
  obtain ⟨gam, gamK, D, hgam, hD, hK, hKeq, hK1⟩ := GlobalTheory.PadicUnitSub.exists_gam_gamK_torsion l s χK.range hs1 hs2 (fun u hu => by
    obtain ⟨g, hg, hgu⟩ := honto K s hKs u hu
    exact ⟨⟨g, hg⟩, hgu⟩)
  let χΓ : ↥χK.range →* (↥(OL LL))ˣ :=
    (Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom).comp χK.range.subtype
  have hχΓ : ∀ g : ↥χK.range, (χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) ((g : ℤ_[l]ˣ) : ℤ_[l]) :=
    fun _ => rfl
  have hres : ∀ g : ↥(GK K), algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) =
      algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) ((χK g : ℤ_[l]ˣ) : ℤ_[l])) := fun g => by
    rw [P.PD_χ, ← hχ]; rfl
  have hs : ((s : ℚ) : WithTop ℚ) = (s : WithTop ℚ) := by norm_cast
  have hz : (l : ℝ) ^ (-((s : ℚ) : ℝ)) = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  refine ⟨{ emb := emb, emb_bij := hbij, emb_σ := hσ, n_eq := rfl, v_l := ?_, s_pos := hs1,
            s_two := fun h => hs2 (by rwa [P.PD_p] at h), Gam := ↥χK.range,
            resΓ := χK.rangeRestrict, resΓ_onto := χK.rangeRestrict_surjective, χΓ := χΓ,
            χΓ_res := fun g => (hres g).symm, χΓ_inj := ?_, gam := gam, gam_gen := ?_, DelF := D,
            DelF_def := hD, gamK := gamK, gamK_gen := ?_, gamK_eq := ?_,
            gamK_eq_one := fun h h' => hK1 h (by rwa [P.PD_p] at h'),
            GKs := (congSub l s).comap χK, GKs_def := ?_, one := one, one_triv := hone1,
            one_line := hone2 }⟩
  · rw [P.PD_p]
    have := (h1 (l : ↥LL.1) 1).2 (by
      have h := norm_coe_algebraMap LL (l : ℤ_[l])
      rw [map_natCast, map_natCast] at h
      rw [h, PadicInt.norm_p]; simp [Real.rpow_neg_one])
    simpa using this
  · intro a b hab
    have h := congrArg (fun u : (↥(OL LL))ˣ => (u : ↥(OL LL))) hab
    simp only [hχΓ] at h
    have h0 := norm_coe_algebraMap LL (((a : ℤ_[l]ˣ) : ℤ_[l]) - ((b : ℤ_[l]ˣ) : ℤ_[l]))
    rw [map_sub, h, sub_self, map_zero, ZeroMemClass.coe_zero, norm_zero, eq_comm, norm_eq_zero,
      sub_eq_zero] at h0
    exact Subtype.ext (Units.ext h0)
  · rw [← hs, h1, hχΓ, norm_sub_one, hgam, hz]
  · intro g
    rw [v_le_iff, hχΓ, hχΓ, norm_pow_sub_one, norm_pow_sub_one]
    exact hK g
  · intro h
    refine hKeq fun g => ?_
    have := h g
    rwa [v_le_iff, hχΓ, hχΓ, norm_pow_sub_one, norm_pow_sub_one] at this
  · intro g
    rw [Subgroup.mem_comap, mem_congSub, ← hs, h2, hres, norm_sub_one, hz]

end GlobalTheory.HWL.GroupLayer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitCont
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst

namespace GlobalTheory.LTChar

variable {l : ℕ} [Fact l.Prime]

theorem orbit_cont (y : ℂ_[l]) : Continuous fun g : GQ l => Formalism.Per.σC g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨z, hz⟩ : ∃ z : Om l, dist y (z : ℂ_[l]) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  let F := adjExt (z : Om l)
  haveI := F.2
  have hH : IsOpen ((F.1.fixingSubgroup : Subgroup (GQ l)) : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isOpen F.1
  have hU : IsOpen {g : GQ l | g₀⁻¹ * g ∈ F.1.fixingSubgroup} :=
    hH.preimage (continuous_const.mul continuous_id)
  have hg₀ : g₀ ∈ {g : GQ l | g₀⁻¹ * g ∈ F.1.fixingSubgroup} := by
    simp only [Set.mem_setOf_eq, inv_mul_cancel]
    exact Subgroup.one_mem _
  filter_upwards [hU.mem_nhds hg₀] with g hg
  have hgz : g z = g₀ z := by
    have h := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg z (mem_adjExt z)
    rw [AlgEquiv.mul_apply] at h
    have h' := congrArg g₀ h
    rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
  have e : Formalism.Per.σC g y - Formalism.Per.σC g₀ y =
      Formalism.Per.σC g (y - z) + Formalism.Per.σC g₀ ((z : ℂ_[l]) - y) := by
    rw [map_sub, map_sub, GlobalTheory.RingBasics.σC_coe, GlobalTheory.RingBasics.σC_coe, hgz]
    ring
  rw [dist_eq_norm, e]
  calc _ ≤ ‖Formalism.Per.σC g (y - z)‖ + ‖Formalism.Per.σC g₀ ((z : ℂ_[l]) - y)‖ := norm_add_le _ _
    _ = ‖y - z‖ + ‖y - z‖ := by rw [GlobalTheory.RingBasics.norm_σC, GlobalTheory.RingBasics.norm_σC, norm_sub_rev (z : ℂ_[l]) y]
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.LTChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEqStatement
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ = zIdem τ' → RepIso τ.ρ τ'.ρ := by
  first | exact @GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | exact GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | (intros; apply GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple <;> assumption)
end

