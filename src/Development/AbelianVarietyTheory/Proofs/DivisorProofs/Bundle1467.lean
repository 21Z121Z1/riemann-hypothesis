import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffOneRealOfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSymplecticSplitting
section
open scoped SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.SympNormal

open GlobalTheory.ArchUniq Module

section Gen

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def omegaL {P : V → V → ℝ} (h : IsPairing P) : (V × V) →ₗ[ℝ] (V × V) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (omega P)
    (fun w w' w'' => by simp only [omega, Prod.fst_add, Prod.snd_add, h.addL, h.addR]; ring)
    (fun c w w' => by simp only [omega, Prod.smul_fst, Prod.smul_snd, h.smulL, h.smulR, smul_eq_mul]; ring)
    (fun w w' w'' => by simp only [omega, Prod.fst_add, Prod.snd_add, h.addL, h.addR]; ring)
    (fun c w w' => by simp only [omega, Prod.smul_fst, Prod.smul_snd, h.smulL, h.smulR, smul_eq_mul]; ring)

@[simp] theorem omegaL_apply {P : V → V → ℝ} (h : IsPairing P) (w w' : V × V) :
    omegaL h w w' = omega P w w' := rfl

end Gen

section Main

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
variable {P : V → V → ℝ} {P₁ : V₁ → V₁ → ℝ} {j : V₁ × V₁ → V × V} {L : Set (V × V)}

def jL (hS : Setup P P₁ j L) : (V₁ × V₁) →ₗ[ℝ] (V × V) where
  toFun := j
  map_add' := hS.add
  map_smul' := hS.smul

def LSub (hS : Setup P P₁ j L) : Submodule ℝ (V × V) where
  carrier := L
  add_mem' {a b} ha hb := hS.max _ (fun l hl => by
      rw [← omegaL_apply hS.pair, map_add, LinearMap.add_apply]; simp [hS.iso _ ha _ hl, hS.iso _ hb _ hl])
    (fun w => by rw [← omegaL_apply hS.pair, map_add, LinearMap.add_apply]; simp [hS.orth _ ha, hS.orth _ hb])
  zero_mem' := hS.max _ (fun l _ => by simp [omega, hS.pair.zero_left, hS.pair.zero_right])
    (fun w => by simp [omega, hS.pair.zero_left, hS.pair.zero_right])
  smul_mem' c a ha := hS.max _ (fun l hl => by
      rw [← omegaL_apply hS.pair, map_smul, LinearMap.smul_apply]; simp [hS.iso _ ha _ hl])
    (fun w => by rw [← omegaL_apply hS.pair, map_smul, LinearMap.smul_apply]; simp [hS.orth _ ha])

def iotaL (hS : Setup P P₁ j L) : ((V₁ × V₁) × LSub hS) →ₗ[ℝ] (V × V) :=
  (jL hS).coprod (LSub hS).subtype

def deltaL (hS : Setup P P₁ j L) (m : ℕ) (f g : Fin m → V × V) :
    ((V₁ × (Fin m → ℝ)) × (V₁ × (Fin m → ℝ))) →ₗ[ℝ] V × V where
  toFun s := j (s.1.1, s.2.1) + ∑ i, s.1.2 i • f i + ∑ i, s.2.2 i • g i
  map_add' s t := by
    have : ((s + t).1.1, (s + t).2.1) = ((s.1.1, s.2.1) + (t.1.1, t.2.1) : V₁ × V₁) := rfl
    rw [this, hS.add]
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c s := by
    have : ((c • s).1.1, (c • s).2.1) = (c • (s.1.1, s.2.1) : V₁ × V₁) := rfl
    rw [this, hS.smul]
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
      RingHom.id_apply, smul_add]

end Main

end GlobalTheory.SympNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittaker
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem bad_part_le_locShare : ∀ (D : D7) (Γ V : Type) [Group Γ] [Finite Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G0g D.nd) (ι : G0g D.nd →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D P lam ψ → ∀ (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup (G0g D.nd)), (∀ k, IsHalf D k (H k)) → ∀ (n : Fin 2 → ℕ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → ∀ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) → ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) : ℝ) ≤ c * (locShare D (fun k _ => eUk D k (ψ₀ k)) 0 (S 0) + locShare D (fun k _ => eUk D k (ψ₀ k)) 1 (S 1)) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  intro D Γ V _ _ _ _ _ π ι hs ρ P lam ψ hW lamb hlamb H hH n c hemb hn ψ₀ hψ₀
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  haveI : Finite (G0g D.nd) := Finite.of_injective ι (fun a b h => by
    have := congrArg π h; rwa [hs.1, hs.1] at this)
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨S, hbad, hsplit⟩ := GlobalTheory.T.one_sub_goodIdempotent_eq_badTupleSums D
  have hloc : ∀ k, locShare D (fun k' v => eUk D k' (ψ ⟨k', v⟩)) k (S k) =
      locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) := by
    intro k
    unfold locShare
    refine Finset.sum_congr rfl fun t _ => Finset.prod_congr rfl fun v _ => ?_
    exact GlobalTheory.T.weight_upperUnitriangularIdempotent_indep_character D k _ _ (hW.1 ⟨k, v⟩) (hψ₀ k) (t v)
  refine ⟨S, hbad, ?_⟩
  have key := GlobalTheory.T.finrank_eigen_inf_ker_le_of_semidirect_split (G0g D.nd) Γ V π ι hs ρ P lam lamb hlamb H n D.ntypes.e0
    (fun k => badElt D k (S k)) (fun k => locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k)) c hemb hn
    (fun k => (GlobalTheory.BadCount.IdemCen.badElt_idem_central D k (S k)).1)
    (fun k a => (GlobalTheory.BadCount.IdemCen.badElt_idem_central D k (S k)).2 a)
    (by simpa using hsplit)
    (fun k g hg => (GlobalTheory.BadCount.badElt_mul_lvlIdem D P lam ψ hW k (S k) (H k) (hH k)).1 g hg)
    (fun k => by rw [← hloc k]; exact (GlobalTheory.BadCount.badElt_mul_lvlIdem D P lam ψ hW k (S k) (H k) (hH k)).2)
  simpa using key

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnipotentConjConeDiagonalBoundStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockUnipotent_conj_coneDiagonal_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → r j / r i ≤ C ∧ ∀ z : BlockIx a j → Cinf E, ∃ z' : BlockIx a j → Cinf E, ‖z'‖ ≤ C * (r j / r i) * ‖z‖ ∧ ∀ τ : ℝ, unip (τ • z) * d = d * unip (τ • z') := by
  first | exact @GlobalTheory.unip_mul_diag_cone | exact GlobalTheory.unip_mul_diag_cone | (intros; apply GlobalTheory.unip_mul_diag_cone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEntriesOfIsCompactClosureZpowersUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BddCpt

theorem bdd_entries_of_isCompact_closure_zpowers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (t ^ k).1.1 i j ∈ Ov E w := by
  intro E _ _ _ n w t hK
  have hO : IsOpen ((Ov E w : Set (w.adicCompletion E))) := Valued.isOpen_valuationSubring _
  have hNe : (nhdsWithin (0 : w.adicCompletion E) {0}ᶜ).NeBot := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot 0
  have hev : ∀ᶠ a in nhds (0 : w.adicCompletion E),
      ∀ s ∈ closure (Subgroup.zpowers t : Set (UL n w)), ∀ i j, a * s.1.1 i j ∈ Ov E w := by
    refine hK.eventually_forall_of_forall_eventually fun s _ => ?_
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) := by fun_prop
    have h0 : (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) (0, s) ∈ (Ov E w : Set _) := by
      simp only [zero_mul]; exact (Ov E w).zero_mem
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
  obtain ⟨a, ha, ha0⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set (w.adicCompletion E))))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (w.adicCompletion E))))).exists
  exact ⟨a, ha0, fun k i j => ha _ (subset_closure ⟨k, rfl⟩) i j⟩

end GlobalTheory.BddCpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleIntegralZpowMulHoloMulEqSum
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
namespace GlobalTheory

theorem circleIntegral_zpow_mul_holo_sum {X : Type} (s₀ : ℂ) (r : ℝ) (V : Set ℂ)
    (Φ : ℂ → X → ℂ) (hr : 0 < r) (hV : IsOpen V) (hball : Metric.closedBall s₀ r ⊆ V)
    (hΦ : ∀ g, DifferentiableOn ℂ (Φ · g) V) :
    ∀ n : ℕ, ∀ (χ : ℂ → ℂ) (j : ℤ), DifferentiableOn ℂ χ V → (-j).toNat = n →
    ∃ c : ℕ → ℂ, ∀ g, circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
      ∑ i ∈ Finset.range (-j).toNat, c i * circleIntegral (fun z => (z - s₀) ^ (j + i) * Φ z g) s₀ r := by
  have hs₀V : V ∈ 𝓝 s₀ := hV.mem_nhds (hball (Metric.mem_closedBall_self hr.le))
  have hsph : ∀ z ∈ Metric.sphere s₀ r, z - s₀ ≠ 0 := by
    intro z hz h
    rw [Metric.mem_sphere, dist_eq_norm, h, norm_zero] at hz
    exact hr.ne hz
  have hzpow : ∀ k : ℤ, ContinuousOn (fun z : ℂ => (z - s₀) ^ k) (Metric.sphere s₀ r) := by
    intro k
    exact ((continuousOn_id.sub continuousOn_const)).zpow₀ k (fun z hz => Or.inl (hsph z hz))
  have hsphV : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hball
  intro n
  induction n with
  | zero =>
    intro χ j hχ hn
    refine ⟨0, fun g => ?_⟩
    rw [hn, Finset.sum_range_zero]
    have hj : 0 ≤ j := by omega
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    simp only [zpow_natCast]
    apply DiffContOnCl.circleIntegral_eq_zero hr.le
    have hd : DifferentiableOn ℂ (fun z => (z - s₀) ^ m * (χ z * Φ z g)) V :=
      (((differentiableOn_id.sub_const s₀).pow m)).mul (hχ.mul (hΦ g))
    exact (hd.mono (Metric.closure_ball_subset_closedBall.trans hball)).diffContOnCl
  | succ n ih =>
    intro χ j hχ hn
    have hχ' : DifferentiableOn ℂ (dslope χ s₀) V := (Complex.differentiableOn_dslope hs₀V).2 hχ
    have hn' : (-(j + 1)).toNat = n := by omega
    obtain ⟨c', hc'⟩ := ih (dslope χ s₀) (j + 1) hχ' hn'
    refine ⟨fun i => Nat.casesOn i (χ s₀) c', fun g => ?_⟩
    have hcont : ContinuousOn (Φ · g) (Metric.sphere s₀ r) := (hΦ g).continuousOn.mono hsphV
    have hcontχ' : ContinuousOn (dslope χ s₀) (Metric.sphere s₀ r) := hχ'.continuousOn.mono hsphV
    have hsplit : circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
        circleIntegral (fun z => χ s₀ * ((z - s₀) ^ j * Φ z g) +
          (z - s₀) ^ (j + 1) * (dslope χ s₀ z * Φ z g)) s₀ r := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      have h0 := hsph z hz
      have hχz : χ z = χ s₀ + (z - s₀) * dslope χ s₀ z := by
        have := sub_smul_dslope χ s₀ z
        rw [smul_eq_mul] at this
        rw [this]; ring
      simp only
      rw [hχz, zpow_add_one₀ h0]
      ring
    rw [hsplit, circleIntegral.integral_add, circleIntegral.integral_const_mul, hc' g, hn, hn',
      Finset.sum_range_succ']
    · rw [add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.cast_succ]
        congr 2
        funext z
        congr 2
        ring
      · simp
    · exact ContinuousOn.circleIntegrable hr.le
        (continuousOn_const.mul ((hzpow j).mul hcont))
    · exact ContinuousOn.circleIntegrable hr.le
        ((hzpow (j + 1)).mul (hcontχ'.mul hcont))

theorem circleIntegral_zpow_mul_holo_mul_eq_sum {X : Type} (s₀ : ℂ) (r : ℝ) (V : Set ℂ)
    (χ : ℂ → ℂ) (Φ : ℂ → X → ℂ) : 0 < r → IsOpen V →
    Metric.closedBall s₀ r ⊆ V → DifferentiableOn ℂ χ V → (∀ g, DifferentiableOn ℂ (Φ · g) V) →
    ∀ j : ℤ, ∃ c : ℕ → ℂ, ∀ g, circleIntegral (fun z => (z - s₀) ^ j * (χ z * Φ z g)) s₀ r =
      ∑ i ∈ Finset.range (-j).toNat, c i * circleIntegral (fun z => (z - s₀) ^ (j + i) * Φ z g) s₀ r :=
  fun hr hV hball hχ hΦ j =>
    circleIntegral_zpow_mul_holo_sum s₀ r V Φ hr hV hball hΦ _ χ j hχ rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmCurveGoodOutsidePrime
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem shortTwist_Δ (d a b : ℂ) :
    (shortTwist d a b).Δ = d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem shortTwist_c₄ (d a b : ℂ) :
    (shortTwist d a b).c₄ = d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [shortTwist, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem shortTwist_j {d a b : ℂ} (hd : d ≠ 0) [(shortTwist d a b).IsElliptic]
    [(⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).IsElliptic] :
    (shortTwist d a b).j = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).j := by
  have h0 : (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ ≠ 0 :=
    (WeierstrassCurve.IsElliptic.isUnit (W := (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ))).ne_zero
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    shortTwist_Δ, shortTwist_c₄]
  field_simp

theorem j_congr_of_eq {W W' : WeierstrassCurve ℂ} (h : W = W') [W.IsElliptic] [W'.IsElliptic] :
    W.j = W'.j := by
  subst h; rfl

end GlobalTheory.CMModel

namespace GlobalTheory.Published

theorem cmCurveGoodOutsidePrime : CMCurveGoodOutsidePrimeSt := by
  intro p hp h4 h3
  obtain ⟨L₀, hL₀⟩ := exists_isIntegersLattice (p := p) hp.pos
  obtain ⟨-, -, hms⟩ := GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable p L₀ hp h3 hL₀
  have him : (sqrtNegNat p).im ≠ 0 := by
    simp only [sqrtNegNat, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
  have hjint := GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L₀ (sqrtNegNat p) hms him
  have hjQ : IsIntegral ℚ (latticeCurve L₀).j := hjint.tower_top
  haveI : FiniteDimensional ℚ ℚ⟮(latticeCurve L₀).j⟯ := IntermediateField.adjoin.finiteDimensional hjQ
  haveI hNF : NumberField ℚ⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite ℚ _
  obtain ⟨L₁, t₁, hD₁, hj₁⟩ := GlobalTheory.T.exists_sqrtNegPrimeKernelDatum_of_integersLattice p L₀ hp h4 h3 hL₀
  obtain ⟨L, t, hD, hj, hsq⟩ := GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem p _ L₁ t₁ hp h4 h3 hD₁
  set F := ℚ⟮(latticeCurve L₀).j⟯ with hFdef
  have hg₂ : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) (ofNat_mem _ 4)
  have hg₃ : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) (ofNat_mem _ 4)
  let dF : F := if p % 8 = 3 then 1 else -(p : F)
  let dC : ℂ := if p % 8 = 3 then 1 else -(p : ℂ)
  have hdC : ((dF : F) : ℂ) = dC := by
    simp only [dF, dC]; split_ifs <;> simp
  have hdC0 : dC ≠ 0 := by
    simp only [dC]; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr (by exact_mod_cast hp.ne_zero)
  let A : WeierstrassCurve F := shortTwist dF ⟨-L.g₂ / 4, hg₂⟩ ⟨-L.g₃ / 4, hg₃⟩
  have hmap : A.map (algebraMap F ℂ) = shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4) := by
    rw [← hdC]
    ext <;> simp [A, shortTwist, WeierstrassCurve.map]
  have hlat : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L := rfl
  have hΔA : A.Δ ≠ 0 := by
    intro h0
    have := congrArg (algebraMap F ℂ) h0
    rw [← WeierstrassCurve.map_Δ, hmap, shortTwist_Δ, hlat, map_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hdC0) (latticeCurve_Δ_ne_zero L) this
  haveI hE : A.IsElliptic := ⟨Ne.isUnit hΔA⟩
  have hmin : HasMinimalDiscriminant A (-(p : F) ^ 3) := by
    intro w
    obtain ⟨V, hV⟩ := GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime F w
    have hloc := GlobalTheory.T.quadraticTwist_cmCurve_model_discriminant_negPrimeCube p F L t hp h4 h3 hD hsq V
    have hD0 : (-(p : F) ^ 3) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    have hmod : ModelAt V F (A.map (algebraMap F ℂ)) ((-(p : F) ^ 3 : F) : ℂ) := by
      rw [hmap]
      convert hloc using 1
      push_cast; rfl
    obtain ⟨C, u, hI, hΔ⟩ := GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt F w V A _ hV hD0 hmod
    have hram := GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg p L₀ w hp hL₀
    exact ⟨C, u, GlobalTheory.T.isMinimal_of_discr_eq_unit_mul_neg_prime_cube p F w (C • A) u hram hI hΔ, hΔ⟩
  refine ⟨F, hNF, A, ⟨hNF, hE, L₀, hL₀, rfl, ?_, hmin.hasGoodReductionOutside⟩, hmin⟩
  have e1 : ((A.j : F) : ℂ) = (A.map (algebraMap F ℂ)).j := (A.map_j (algebraMap F ℂ)).symm
  haveI : (shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4)).IsElliptic := hmap ▸ inferInstance
  haveI : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ).IsElliptic :=
    inferInstanceAs (latticeCurve L).IsElliptic
  rw [e1, j_congr_of_eq hmap, shortTwist_j hdC0, j_congr_of_eq hlat, hj, hj₁]

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt
section
noncomputable section

namespace GlobalTheory.ThK.FiniteLevelDerivatives

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem compFin_eq_zero_of_at {x : AE F E} (hx : At (evI F) x) (v : HeightOneSpectrum (𝓞 F)) : compFin F E v x = 0 := by
  let u : AF F := (0, 1)
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h0 : u • x = 0 := hx u hu
  have hs : compFin F E v (algebraMap (AF F) (AE F E) u) = 1 := by
    have h2 : sndA F u = 1 := rfl
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (u ⊗ₜ[F] (1 : E)) = 1
    rw [Algebra.TensorProduct.map_tmul, evFin, AlgHom.comp_apply, h2, map_one, AlgHom.id_apply]
    rfl
  have h1 := congrArg (compFin F E v) h0
  rwa [Algebra.smul_def, map_mul, hs, one_mul, map_zero] at h1

theorem toGAd_mem_infPts (hσ : ∀ x, σ (σ x) = x) {d : ℕ} (W : Spc F E d) {c : E} (hc : c ≠ 0) {k : UA σ W.J}
    (hk : k ∈ UAt σ W (evI F)) : toGAd hσ W.J hc k ∈ infPts σ (c • W.J.map σ) := by
  rw [mem_infPts_iff_forall]
  intro v
  apply matHom_injective
  rw [matHom_proj, map_one]
  apply Units.ext
  show (mat k).map (compFin F E v) = 1
  ext i j
  have h : At (evI F) ((mat k - 1) i j) := fun u hu => congrFun (congrFun (hk u hu) i) j
  have h1 := compFin_eq_zero_of_at h v
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

end GlobalTheory.ThK.FiniteLevelDerivatives

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.ConjLoc

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def conjSchR (κ : Type) [Fintype κ] : SInf F κ →L[ℝ] SInf F κ :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem conjSchR_apply {κ : Type} [Fintype κ] (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    conjSchR κ f x = starRingEnd ℂ (f x) := rfl

def conjSchCLM {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : SInf F κ →L[ℂ] SInf F κ₁) : SInf F κ →L[ℂ] SInf F κ₁ where
  toFun f := conjSchR κ₁ (T (conjSchR κ f))
  map_add' f g := by simp only [map_add]
  map_smul' c f := by
    have h : conjSchR κ (c • f) = starRingEnd ℂ c • conjSchR κ f := by
      refine SchwartzMap.ext fun y => ?_; simp only [conjSchR_apply, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
    refine SchwartzMap.ext fun x => ?_
    rw [h, map_smul, conjSchR_apply, RingHom.id_apply, SchwartzMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      smul_eq_mul, map_mul, Complex.conj_conj, conjSchR_apply]
  cont := (conjSchR κ₁).continuous.comp (T.continuous.comp (conjSchR κ).continuous)

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) :
    (fun x => starRingEnd ℂ (φ x)) ∈ SB X :=
  ⟨h.1.comp (starRingEnd ℂ), h.2.comp_left (g := starRingEnd ℂ) (map_zero _)⟩

theorem conj_stdInd_apply (κ : Type) (v : Pl F) (y : κ → Fv F v) :
    starRingEnd ℂ (stdInd F κ v y) = stdInd F κ v y := by
  unfold stdInd
  by_cases hy : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
  · rw [Set.indicator_of_mem hy, Pi.one_apply, map_one]
  · rw [Set.indicator_of_notMem hy, map_zero]

theorem conj_stdInd (κ : Type) (v : Pl F) :
    (fun y => starRingEnd ℂ (stdInd F κ v y)) = stdInd F κ v :=
  funext (conj_stdInd_apply κ v)

theorem conj_pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x : κ → AF F) :
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) x := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, conjSchR_apply, map_mul]
  congr 1
  exact MulEquiv.map_finprod (starRingAut : ℂ ≃+* ℂ).toMulEquiv _

theorem isLocOp_conjLin {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ)
    (he : IsLocOp e) : IsLocOp (conjLin e) := by
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  refine ⟨conjSchCLM ei, fun v => conjLin (ev v), fun v φ hφ => conj_mem_SB (hSB v _ (conj_mem_SB hφ)), ?_, ?_⟩
  · filter_upwards [hstd] with v hv
    funext y
    rw [conjLin_apply, conj_stdInd, hv, conj_stdInd_apply]
  · intro f φ hφ hfin
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) :=
      funext (conj_pure f φ)
    have hfin' : ∀ᶠ v in cofinite, (fun y => starRingEnd ℂ (φ v y)) = stdInd F κ v := by
      filter_upwards [hfin] with v hv
      rw [hv, conj_stdInd]
    rw [h1, hloc _ _ (fun v => conj_mem_SB (hφ v)) hfin', conj_pure]
    rfl

end GlobalTheory.DblEval.ConjLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermEqZero
section
noncomputable section

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem IsCuspForm.mem_cuspForms {φ : Sm E a} (h : IsCuspForm φ) : φ.1 ∈ cuspForms E a :=
  (UpperTheory.V.Cm.isCuspForm_iff φ).1 h

theorem IsCuspForm.constantTerm_eq_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (φ : Sm E a) (h : IsCuspForm φ) : AutomorphicForm.IsCuspidal (K := E) (n := a) φ.1 :=
  h.mem_cuspForms.2

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRationalSectionsEqPowProductLinearFormsStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_rational_sections_eq_pow_product_linearForms : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → S.deepRank s ≤ (Finset.univ.filter fun k => (col k).j = S.D).card → ∃ γ : E, ∀ l : Fin S.N → E, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = γ * (∏ p, ∑ k, l k * Φ.y p k) ^ S.expo := by
  first | exact @GlobalTheory.HSShort.det_rational_eq_pow | exact GlobalTheory.HSShort.det_rational_eq_pow | (intros; apply GlobalTheory.HSShort.det_rational_eq_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalEigenIntertwinersStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_eigen_intertwiners : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W), FiniteDimensional ℂ W → ∀ (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)), N ≤ maps L W hW → (∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) → FiniteDimensional ℂ N := by
  first | exact @GlobalTheory.AutGrowth.finiteDimensional_capEigen_maps | exact GlobalTheory.AutGrowth.finiteDimensional_capEigen_maps | (intros; apply GlobalTheory.AutGrowth.finiteDimensional_capEigen_maps <;> assumption)
end

