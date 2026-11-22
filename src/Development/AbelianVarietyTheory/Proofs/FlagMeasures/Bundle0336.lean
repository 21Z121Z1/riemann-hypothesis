import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsPeriodMapDet
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraParameterDescent
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUtoU

variable {n : ℕ}

theorem rhoNh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    rhoNh ε (fun a => lam a - c) = rhoNh ε lam := by
  funext a
  simp only [rhoNh, sub_lt_sub_iff_right]

theorem rhoCh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    rhoCh ε (fun a => lam a - c) = rhoCh ε lam := by
  funext a
  simp only [rhoCh, sub_lt_sub_iff_right]

theorem lowCh_sub_const (ε : Fin n → Bool) (lam : Fin n → ℝ) (c : ℝ) :
    lowCh ε (fun a => lam a - c) = fun a => lowCh ε lam a - c := by
  funext a
  simp only [lowCh, rhoNh_sub_const, rhoCh_sub_const, Pi.add_apply, Pi.sub_apply]
  ring

theorem exists_sum_eq_int (hn : 1 ≤ n) (lam : Fin n → ℝ) (hU : IsParU lam) :
    ∃ m : ℤ, ∑ a, lam a = (m : ℝ) := by
  choose k hk using hU.2
  obtain ⟨t, ht⟩ := Nat.even_mul_pred_self n
  refine ⟨(t : ℤ) + ∑ a, k a, ?_⟩
  have hlam : ∀ a, lam a = ((n : ℝ) - 1) / 2 + (k a : ℝ) := fun a => by linarith [hk a]
  have hcast : (n : ℝ) * ((n : ℝ) - 1) = 2 * (t : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) ht
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hn, Nat.cast_one] at this
    linarith
  simp only [hlam, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  linarith

theorem extension_main : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ), IsParU lam → ∃ m : ℤ, ∑ a, lam a = (m : ℝ) ∧ IsParS (fun a => lam a - (m : ℝ) / n) ∧ (IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∃ π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), Ext ε m π' π ∧ IsHCU ε lam π) := by
  intro n hn ε H _ _ π' lam hU
  obtain ⟨m, hm⟩ := exists_sum_eq_int hn lam hU
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨m, hm, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.sum_sub_distrib, hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · intro a b h
    exact hU.1 (by simpa using h)
  · intro a b
    obtain ⟨ka, hka⟩ := hU.2 a
    obtain ⟨kb, hkb⟩ := hU.2 b
    exact ⟨ka - kb, by push_cast; linarith⟩
  · intro hS
    obtain ⟨⟨hcomp, hnt, hrep, hirr, hsq⟩, hinf, ⟨S0, hS0, huniq⟩, habove⟩ := hS
    have hcent := GlobalTheory.T.harish_chandra_central_action n hn ε H π' lam m hU hm ⟨⟨hcomp, hnt, hrep, hirr, hsq⟩, hinf, ⟨S0, hS0, huniq⟩, habove⟩
    obtain ⟨π, hext, hrepU⟩ := GlobalTheory.T.extend_special_unitary_rep n hn ε H m π' hrep hcent
    refine ⟨π, hext, ?_⟩
    obtain ⟨-, hirrIff, -, -⟩ := GlobalTheory.T.extension_preserves_properties n hn ε H m π' π hext
    have hsqIff := GlobalTheory.T.square_integrable_iff_extension n hn ε H m π' π hext hrepU
    have hinfU := GlobalTheory.T.infinitesimal_character_extension n hn ε H m π' π hext _ hinf
    obtain ⟨-, hKT⟩ := GlobalTheory.T.weights_of_extension n hn ε H m π' π hext
    have hlow := lowCh_sub_const ε lam ((m : ℝ) / n)
    have hsumLow : ∑ a, lowCh ε lam a = (m : ℝ) := by
      have h0 := hS0.1
      rw [hlow, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at h0
      field_simp at h0
      linarith
    have hKTlow : ∀ S : Submodule ℂ H, IsKTypeU ε lam π (lowCh ε lam) S ↔
        IsKTypeS ε (fun a => lam a - (m : ℝ) / n) π' (lowCh ε (fun a => lam a - (m : ℝ) / n)) S := by
      intro S
      rw [hKT lam (lowCh ε lam) ((m : ℝ) / n) S, hlow]
      exact ⟨fun h => h.2, fun h => ⟨hsumLow, h⟩⟩
    refine ⟨⟨hcomp, hnt, hrepU, hirrIff.2 hirr, hsqIff.2 hsq⟩, ?_, ⟨S0, (hKTlow S0).2 hS0, fun S hS => huniq S ((hKTlow S).1 hS)⟩, ?_⟩
    · convert hinfU using 2 with a
      push_cast
      field_simp
      ring
    · intro μ S hμS
      obtain ⟨-, hμS'⟩ := (hKT lam μ ((m : ℝ) / n) S).1 hμS
      obtain ⟨c, hc, heq⟩ := habove _ S hμS'
      refine ⟨c, fun a b hab => by simpa using hc a b hab, ?_⟩
      funext a
      have := congrFun heq a
      rw [hlow] at this
      simp only [Pi.add_apply] at this ⊢
      linarith

end GlobalTheory.SUtoU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightBoundByInfinityNorm
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TauNorm

theorem exists_bound {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, ‖L B‖ ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  classical
  set c : ℝ := ∑ i, ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖ with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c, hc0, fun B => ?_⟩
  have hB : L B = ∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]
    simp [map_sum, ← map_smul, Matrix.smul_single]
  have hle : ∀ i j, ‖L (Matrix.single i j (1 : ℂ))‖ ≤ c := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖L (Matrix.single i j (1 : ℂ))‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  rw [hB]
  calc ‖∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ))‖
      ≤ ∑ i, ∑ j, ‖B i j‖ * ‖L (Matrix.single i j (1 : ℂ))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_smul _ _).le))
    _ ≤ ∑ i, ∑ j, ‖B i j‖ * c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hle i j) (norm_nonneg _)
    _ = c * ∑ i, ∑ j, ‖B i j‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exp_dOp_le {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, P * B * Q ≠ 0 → Real.exp (GlobalTheory.Count.dOp (P * B * Q)) ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun B => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))
      map_add' := fun B B' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a B => by simp }
  obtain ⟨c, hc, h⟩ := exists_bound L
  refine ⟨c, hc, fun B hB => ?_⟩
  have hpos : 0 < ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hB
    have h1 : Matrix.toEuclideanLin (P * B * Q) = 0 :=
      LinearMap.toContinuousLinearMap.injective (h0.trans (map_zero _).symm)
    exact Matrix.toEuclideanLin.injective (h1.trans (map_zero _).symm)
  unfold GlobalTheory.Count.dOp
  rw [Real.exp_log hpos]
  exact h B

theorem exp_mean_le {ι : Type} [Fintype ι] [Nonempty ι] (d : ι → ℝ) (K : ℝ) (h : ∀ v, Real.exp (d v) ≤ K) :
    Real.exp ((∑ v, d v) / Fintype.card ι) ≤ K := by
  obtain ⟨v₀, hv₀⟩ := Finite.exists_max d
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmean : (∑ v, d v) / Fintype.card ι ≤ d v₀ := by
    rw [div_le_iff₀ hcard]
    calc ∑ v, d v ≤ ∑ _v : ι, d v₀ := Finset.sum_le_sum fun v _ => hv₀ v
      _ = d v₀ * Fintype.card ι := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact (Real.exp_le_exp.2 hmean).trans (h v₀)

theorem card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
  simp only [AutInst.f]
  omega

theorem inv_tau_mul_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 = 1) (K : ℝ)
    (h : ∀ v, Real.exp (GlobalTheory.Count.dOp (uMat (g.1 v))) ≤ K) :
    (GlobalTheory.Count.tau1 I (x * g))⁻¹ ≤ (GlobalTheory.Count.tau1 I x)⁻¹ * K := by
  have hK1 : g.2 ∈ I.Kset := by
    rw [hg]
    show ((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    simp only [OneMemClass.coe_one]
    exact one_mem _
  have hlog := GlobalTheory.TauLipschitz.log_trunc_le I hn x g hK1
  have hx := GlobalTheory.TauLipschitz.trunc_pos I hn x
  have hxg := GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)
  have hmean : Real.exp (GlobalTheory.Dec.dSum I g.1 / I.f) ≤ K := by
    have := exp_mean_le (fun v => GlobalTheory.Count.dOp (uMat (g.1 v))) K h
    rw [card_places] at this
    simpa only [GlobalTheory.Dec.dSum] using this
  have hdiv : GlobalTheory.Count.tau1 I x / GlobalTheory.Count.tau1 I (x * g) ≤ K := by
    rw [← Real.exp_log (div_pos hx hxg), Real.log_div hx.ne' hxg.ne']
    exact (Real.exp_le_exp.2 (by linarith)).trans hmean
  rw [inv_mul_eq_div, le_div_iff₀ hx, inv_mul_eq_div]
  exact hdiv

theorem sum_le_normInf {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (g : GA D V) (τ : D.what₂.Tau) :
    ∑ i, ∑ j, ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ ≤ normInf θ V g := by
  unfold Formalism.L2.Theta.normInf
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun τ => ∑ i, ∑ j, (‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
    (fun _ _ => by positivity) (Finset.mem_univ τ))
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    le_add_of_nonneg_right (norm_nonneg _)

theorem uMat_ne_zero (I : AutInst) (hn : 1 ≤ I.n) (g : I.GA) (v : InfinitePlace I.F) : uMat (g.1 v) ≠ 0 := by
  have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact Units.ne_zero _

end GlobalTheory.TauNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndicatorCompletedLatticeEqFinprodLocal
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU

theorem eventually_vecLoc_mem_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) (y : Fin n → Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, vecLoc v y ∈ latLoc F L v := by
  have := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n),
    Filter.eventually_all.2 fun i => eventually_map_evalV_mem_intLoc (y i)] with v h h1
  rw [h, mem_latLoc_stdLattice]
  exact h1

theorem indicator_latHat_eq_finprod :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ X : Fin 1 → Fin n → Af F ⊗[F] E,
      {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}.indicator
        (1 : (Fin 1 → Fin n → Af F ⊗[F] E) → ℂ) X =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) := by
  intro F E _ _ _ _ _ n L hL X
  have key : ∀ v : HeightOneSpectrum (𝓞 F), vecLoc v (X 0) ∈ latLoc F L v →
      {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator
          (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v X) = 1 := fun v hv =>
    Set.indicator_of_mem (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
  by_cases h : X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))
  · rw [Set.indicator_of_mem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h,
      finprod_congr fun v => key v ((mem_latHat_iff hL.fg _).1 h v), finprod_one]
    rfl
  · rw [Set.indicator_of_notMem
      (s := {X : Fin 1 → Fin n → Af F ⊗[F] E | X 0 ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))}) h]
    rw [mem_latHat_iff hL.fg, not_forall] at h
    obtain ⟨v, hv⟩ := h
    refine (finprod_eq_zero _ v ?_ ?_).symm
    · exact Set.indicator_of_notMem
        (s := {Y : Fin 1 → Fin n → Fv F v ⊗[F] E | Y 0 ∈ GlobalTheory.AdelicU.latLoc F L v}) hv _
    · exact Set.Finite.subset (Filter.eventually_cofinite.1 (eventually_vecLoc_mem_latLoc L hL (X 0)))
        fun u hu hu' => hu (key u hu')

end GlobalTheory.AdelicU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompactStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantExtension_integrableOn_compact : ∀ (B : RowsAut) (C : Set B.I.GA), IsCompact C → ∃ M : ℝ, ∀ F : B.I.L2 B.μf B.fund, IntegrableOn (B.I.ext F) C (B.I.muA B.μf) ∧ ∫ y in C, ‖B.I.ext F y‖ ∂(B.I.muA B.μf) ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.LocalL2Isometry.ext_integrableOn | exact GlobalTheory.LocalL2Isometry.ext_integrableOn | (intros; apply GlobalTheory.LocalL2Isometry.ext_integrableOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHCParamOfSetup
section
open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom.LowVec

variable {k r : ℕ}

abbrev flagSpan (k r : ℕ) (a : Fin (r + 1)) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} => bvec (eI k r b.1))

theorem mem_flagSpan {a : Fin (r + 1)} {y : Fin (2 * r + k + 1) → ℂ} :
    y ∈ flagSpan k r a ↔ ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0 := by
  constructor
  · intro hy i hi
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have := b.2
      exact Pi.single_eq_of_ne (fun e => by rw [e] at hi; simp only [eI] at hi; omega) _
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  · intro hy
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : a.val ≤ i.val
    · rw [hy i hi, Pi.single_zero]; exact Submodule.zero_mem _
    · have ha := a.isLt
      have : (Pi.single i (y i) : Fin (2 * r + k + 1) → ℂ) = y i • bvec (eI k r ⟨i.val, by omega⟩) := by
        rw [bvec, ← Pi.single_smul, smul_eq_mul, mul_one]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨i.val, by omega⟩, by simpa using hi⟩, rfl⟩)

theorem mulVec_sub {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z)
    (a : Fin (r + 1)) {y : Fin (2 * r + k + 1) → ℂ} (hy : y ∈ flagSpan k r a) :
    ∃ y' ∈ flagSpan k r a, s *ᵥ (fvec k r z a - y) = fvec k r z a - y' := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hc := ((WeylGroupFacts.nset_iff m).1 hm).2
  have ha := a.isLt
  have h1 : fvec k r z a - m *ᵥ (fvec k r z a - y) ∈ flagSpan k r a := by
    refine mem_flagSpan.2 fun i hi => ?_
    have : (m *ᵥ (fvec k r z a - y)) i = ((1 : Mat k r) *ᵥ (fvec k r z a - y)) i := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j.val ≤ r + k ∧ (j.val ≤ i.val ∨ r ≤ i.val)
      · rw [hc i j hj.1 hj.2, Matrix.one_apply]
      · have e1 : y j = 0 := mem_flagSpan.1 hy j (by omega)
        have e2 : fvec k r z a j = 0 := by
          unfold fvec
          split_ifs with h'
          · exact Pi.single_eq_of_ne (fun e => by rw [e] at hj; simp only [eI] at hj; omega) _
          · exact hz j (by omega)
        simp [e1, e2]
    rw [Pi.sub_apply, this, Matrix.one_mulVec, Pi.sub_apply, mem_flagSpan.1 hy i hi]; ring
  have h2 : ∀ x ∈ flagSpan k r a, h *ᵥ x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact (hh.2.1 b.1).1
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  have h3 : h *ᵥ fvec k r z a = fvec k r z a := by
    unfold fvec
    split_ifs with h'
    · exact (hh.2.1 _).1
    · exact hh.2.2
  refine ⟨_, h1, ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have := h2 _ h1
  rw [Matrix.mulVec_sub, h3] at this
  rw [sub_sub_cancel]
  exact sub_right_injective this

theorem lA_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s : Mat k r} (hs : s ∈ Sset k r z) (g : Mat k r)
    (a : Fin (r + 1)) : lA k r z (s * g) a = lA k r z g a := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hu : IsUnit s.det := by
    obtain ⟨h, hh, m, hm, rfl⟩ := hs
    rw [Matrix.det_mul]
    exact ((uHGroup _ _ hH).2.2 h hh.1).1.mul ((uHGroup _ _ hH).2.2 m hm.1).1
  unfold lA
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz ((sGroup k r z hz).2.2 s hs) a hy
    exact ⟨y', hy', by rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, e]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', e⟩ := mulVec_sub hz hs a hy
    refine ⟨y', hy', ?_⟩
    rw [← e, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem eucl_unitary {N : ℕ} {t : Matrix (Fin N) (Fin N) ℂ} (ht : t ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (v : Fin N → ℂ) : eucl (t *ᵥ v) = eucl v := by
  have e : ∀ v : Fin N → ℂ, ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = star v ⬝ᵥ v := fun v => by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  have h1 : tᴴ * t = 1 := Matrix.mem_unitaryGroup_iff'.1 ht
  unfold eucl
  congr 1
  apply Complex.ofReal_injective
  rw [e, e, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]

theorem lA_right (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) {t : Mat k r}
    (ht : t ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    lA k r z (g * t) a = lA k r z g a := by
  have h1 : t⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    rw [Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 ht)]
    exact Unitary.star_mem ht
  unfold lA
  simp only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, eucl_unitary h1]

theorem measurable_lA (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    Measurable fun x : Mt k r => lA k r z (Matrix.of x) a := by
  refine measurable_of_Iio fun t => ?_
  have ho : IsOpen {x : Mt k r | ∃ y ∈ flagSpan k r a, eucl (Matrix.of x *ᵥ (fvec k r z a - y)) < t} := by
    simp only [Set.ofPred_exists, Set.ofPred_and]
    refine isOpen_iUnion fun y => IsOpen.inter isOpen_const (isOpen_lt ?_ continuous_const)
    simp only [eucl, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  have hi : Measurable fun x : Mt k r => (fun i j => (Matrix.of x)⁻¹ i j : Mt k r) := by
    have h1 : Continuous fun x : Mt k r => (Matrix.of x).det := Continuous.matrix_det continuous_id
    have h2 : Continuous fun x : Mt k r => (Matrix.of x).adjugate := Continuous.matrix_adjugate continuous_id
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact h1.measurable.inv.mul (h2.matrix_elem i j).measurable
  convert hi ho.measurableSet using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_ofPred_eq, lA]
  refine (csInf_lt_iff ?_ ?_).trans ⟨?_, ?_⟩
  · exact ⟨0, by rintro _ ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩
  · exact Set.nonempty_of_mem (x := eucl ((Matrix.of x)⁻¹ *ᵥ (fvec k r z a - 0))) ⟨0, Submodule.zero_mem _, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩; exact ⟨y, hy, h⟩
  · rintro ⟨y, hy, h⟩; exact ⟨_, ⟨y, hy, rfl⟩, h⟩

theorem exists_filt_zero (hA : LowAny) (hK : LowestK) {P : Mat k r} {A : HRep k r} {μ : Fin (2 * r + k + 1) → ℝ}
    {F : Flag k r} {κ : ℝ} (hP : IsCayleyU k r (sgnCN k r) P) (hμ : IsHCParam μ) (hD : A.IsDSAt P μ) (hF : F.Ok κ)
    {B : A.H → F.W} (hB : F.Iso A B) {w : A.H} (hw : w ∈ A.iso P (lowK (sgnCN k r) μ)) :
    ∃ w₀ ∈ A.filt P μ 0, ‖w₀‖ₑ = ‖w‖ₑ ∧ ∀ Φ : (Fin (r + 1) → ℝ) → ℝ, Measurable Φ →
      A.mass F.ν B (fun g => Φ (lA k r F.z g)) w = A.mass F.ν B (fun g => Φ (lA k r F.z g)) w₀ := by
  obtain ⟨v, hv, hv0, hvw⟩ := (hK k r P A μ hP hμ hD).1.2.2.2.1
  have hf : v ∈ A.filt P μ 0 := Submodule.subset_span ⟨_, _, by simp [dist1], by simp [dist1], hv, hvw⟩
  have hn : ‖w‖ = ‖((‖w‖ / ‖v‖ : ℝ) : ℂ) • v‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hv0)]
  refine ⟨((‖w‖ / ‖v‖ : ℝ) : ℂ) • v, Submodule.smul_mem _ _ hf, ?_, fun Φ hΦ => ?_⟩
  · rw [← ofReal_norm, ← ofReal_norm, ← hn]
  · refine hA k r P A μ F κ hP hμ hD hF B hB _ (hΦ.comp (measurable_pi_lambda _ (measurable_lA F.z))) ?_ ?_ w hw _
      (Submodule.smul_mem _ _ hv) hn
    · intro g _ s hs
      exact congrArg Φ (funext (lA_left hF.1 hs g))
    · intro g _ t _ ht
      exact congrArg Φ (funext (lA_right F.z g ht))

theorem isHCParam_of_setup {c Ch bv h q : ℝ} {P : Mat k r} {lam μ : Fin (2 * r + k + 1) → ℝ}
    {R : (Fin (2 * r + k + 1) → ℝ) → HRep k r} (hS : Setup k r c Ch P lam bv h q R) (hμ : InPP lam q μ) :
    IsHCParam μ := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · linarith [hμ.gap hab.ne, hS.2.2.1.le_gap hS.2.1 hab, hS.2.1.1.1 hab]
  · obtain ⟨m, hm⟩ := hμ.1 a
    obtain ⟨m', hm'⟩ := hS.2.1.1.2 a
    exact ⟨m + m', by rw [Int.cast_add]; linarith⟩

theorem momentLow : LowAny → MomentCor → LowestK → MomentLow := by
  intro hA hC hK c hc
  obtain ⟨Ch, hCh, H⟩ := hC c hc
  refine ⟨Ch, hCh, fun k r P lam bv h q₀ b R hS F κ hF hZ hT q μ B hB w hw => ⟨fun h1 h2 => ?_, fun l hl h1 h2 => ?_⟩⟩
  · have h0 : InPP lam q₀ μ := h1.mono (sub_le_self _ (Nat.cast_nonneg _))
    obtain ⟨w₀, hw₀, hn, hm⟩ := exists_filt_zero hA hK hS.1 (isHCParam_of_setup hS h0) (hS.2.2.2.2 μ h0) hF hB hw
    have h3 := (H k r P lam bv h q₀ b R hS F κ hF hZ hT 0 q μ B hB w₀ hw₀).1 h1 (by rwa [zero_add])
    rw [MomAll, hn] at h3
    refine ⟨fun a => ⟨?_, ?_⟩, fun t ht => ?_⟩
    · exact (hm (fun x => x a ^ (2 * q)) (by fun_prop)).trans_le (h3.1 a).1
    · exact (hm (fun x => (x a)⁻¹ ^ (2 * q)) (by fun_prop)).trans_le (h3.1 a).2
    · refine (hm (Set.indicator {x | ∃ a, t * H1 k r (Tz k r F.z) κ b 4 bv ≤ max (x a) (x a)⁻¹} 1)
        (measurable_one.indicator ?_)).trans_le (h3.2 t ht)
      rw [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun a => measurableSet_le measurable_const (by fun_prop)
  · have h0 : InPP lam q₀ μ := h1.mono (sub_le_self _ (Nat.cast_nonneg _))
    obtain ⟨w₀, hw₀, hn, hm⟩ := exists_filt_zero hA hK hS.1 (isHCParam_of_setup hS h0) (hS.2.2.2.2 μ h0) hF hB hw
    have h3 := (H k r P lam bv h q₀ b R hS F κ hF hZ hT 0 q μ B hB w₀ hw₀).2 l hl h1 (by rwa [zero_add])
    rw [MomProd, hn] at h3
    exact (hm (fun x => (∏ a : Fin l, x (Fin.castLE hl a)) ^ (2 * q)) (by fun_prop)).trans_le h3

end GlobalTheory.Mom.LowVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletionStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhat_indicator_localLatticeCompletion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ v : HeightOneSpectrum (𝓞 F), IsSB ({X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ)) := by
  first | exact @GlobalTheory.LatticeIndicator.isSB_indicator_latLoc | exact GlobalTheory.LatticeIndicator.isSB_indicator_latLoc | (intros; apply GlobalTheory.LatticeIndicator.isSB_indicator_latLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInterStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter : ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund A : Set I.GA), I.IsFundDom (I.muA μf) fund → MeasurableSet A → (∀ γ ∈ I.GFset, ∀ x ∈ A, γ * x ∈ A) → covol I.GFset (I.muA μf) A = I.muA μf (A ∩ fund) ∧ 0 < I.muA μf fund := by
  first | exact @GlobalTheory.CovolRat.covol_eq_inter_fund | exact GlobalTheory.CovolRat.covol_eq_inter_fund | (intros; apply GlobalTheory.CovolRat.covol_eq_inter_fund <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslateLeMultiplicityFundamentalStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_translate_le_multiplicity_fundamental : ∀ (B : RowsAut) (S : Set B.I.Ginf) (y : B.I.GA) (Φ : B.I.GA → ENNReal), 1 ≤ B.I.n → 1 ≤ B.g → MeasurableSet S → (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) → Measurable Φ → (∀ γ ∈ B.I.GFset, ∀ z, Φ (γ * z) = Φ z) → (∀ k ∈ B.I.Kg B.g, ∀ z, Φ (z * (1, k)) = Φ z) → B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) ≤ ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * ∫⁻ z in B.fund, Φ z ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.BoundedUnfold.lintegral_le_multiplicity | exact GlobalTheory.BoundedUnfold.lintegral_le_multiplicity | (intros; apply GlobalTheory.BoundedUnfold.lintegral_le_multiplicity <;> assumption)
end

