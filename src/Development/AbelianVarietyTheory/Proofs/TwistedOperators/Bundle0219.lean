import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedMatrixGroupOfLocalMultiplier
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatPoint

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem ev_apply (v : HeightOneSpectrum (𝓞 F)) (x : Af F) : evalV F v x = x v := rfl

theorem val_coe_one (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    Valued.v (algebraMap F (Af F) (t : F) v) = 1 := by
  rw [GlobalTheory.Ker.MovLev.val_coe]; exact v.intValuation_eq_one_iff.2 ht

theorem coe_ne_zero (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    algebraMap F (Af F) (t : F) v ≠ 0 := fun h0 => by
  have := val_coe_one t v ht
  rw [h0, map_zero] at this
  exact zero_ne_one this

theorem div_int {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F)
    (t : 𝓞 F) (ht : t ∉ v.asIdeal) : x * (algebraMap F (Af F) (t : F) v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [map_mul, map_inv₀, val_coe_one t v ht, inv_one, mul_one]
  exact hx

def mulG (I : Ideal (𝓞 F)) : AddSubgroup (Af F) :=
  AddSubgroup.closure {x | ∃ t ∈ I, ∃ β ∈ intAf F, x = algebraMap F (Af F) (t : F) * β}

theorem mem_mulG (I : Ideal (𝓞 F)) {γ : Af F} (hγ : γ ∈ intAf F)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), evalV F w γ = 0 ∨ ∃ t ∈ I, t ∉ w.asIdeal) : γ ∈ mulG I := by
  by_cases h0 : γ = 0
  · rw [h0]; exact zero_mem _
  obtain ⟨w₀, hw₀⟩ : ∃ w, γ w ≠ 0 := by
    by_contra H
    push_neg at H
    exact h0 (FiniteAdeleRing.ext F fun v => H v)
  obtain ⟨t₁, ht₁I, ht₁w⟩ := (h w₀).resolve_left hw₀
  have ht₁0 : t₁ ≠ 0 := fun e => ht₁w (e ▸ w₀.asIdeal.zero_mem)
  have hspan : Ideal.span {t₁} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht₁0
  set Z := (Ideal.finite_factors hspan).toFinset with hZdef
  have hZ : ∀ v, v ∈ Z ↔ t₁ ∈ v.asIdeal := fun v => by
    rw [hZdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t ∈ I, γ v = 0 ∨ t ∉ v.asIdeal := fun v =>
    (h v).elim (fun e => ⟨0, I.zero_mem, Or.inl e⟩) fun ⟨t, ht, hv⟩ => ⟨t, ht, Or.inr hv⟩
  choose τ hτI hτ using h'
  obtain ⟨c, hc, hc'⟩ : ∃ c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ∀ v, algebraMap F (Af F) (τ v : F) v * c v = γ v := by
    refine ⟨fun v => if γ v = 0 then 0 else γ v * (algebraMap F (Af F) (τ v : F) v)⁻¹, fun v => ?_, fun v => ?_⟩
    · dsimp only
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ ((hτ v).resolve_left hv)
    · dsimp only
      split_ifs with hv
      · rw [mul_zero, hv]
      · rw [mul_comm, mul_assoc, inv_mul_cancel₀ (coe_ne_zero _ _ ((hτ v).resolve_left hv)), mul_one]
  have hb₁ : ∀ v : HeightOneSpectrum (𝓞 F),
      (if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹) ∈ v.adicCompletionIntegers F :=
    fun v => by
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ hv
  obtain ⟨β₁, hβ₁, eβ₁⟩ : ∃ β₁ : Af F, β₁ ∈ intAf F ∧
      ∀ v, β₁ v = if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹ :=
    ⟨GlobalTheory.Ker.MovLev.ofInt _ hb₁, fun v => hb₁ v, fun _ => rfl⟩
  have hbw : ∀ w v : HeightOneSpectrum (𝓞 F), (if v = w then c v else 0) ∈ v.adicCompletionIntegers F :=
    fun w v => by
      split_ifs
      exacts [hc v, zero_mem _]
  have hβex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ β : Af F, β ∈ intAf F ∧ ∀ v, β v = if v = w then c v else 0 :=
    fun w => ⟨GlobalTheory.Ker.MovLev.ofInt _ (hbw w), fun v => hbw w v, fun _ => rfl⟩
  choose β hβ eβ using hβex
  have e : γ = algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w := by
    refine FiniteAdeleRing.ext F fun v => ?_
    change evalV F v γ = evalV F v (algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w)
    rw [map_add, map_sum, map_mul]
    simp only [map_mul, ev_apply, eβ₁, eβ]
    by_cases hv : t₁ ∈ v.asIdeal
    · have hvZ : v ∈ Z := (hZ v).2 hv
      rw [Finset.sum_eq_single v (fun w _ hwv => by rw [if_neg (Ne.symm hwv), mul_zero])
        (fun hn => absurd hvZ hn), if_pos hv, if_pos rfl, mul_zero, zero_add, hc']
    · rw [Finset.sum_eq_zero (fun w hw => by
        have hne : v ≠ w := fun e => hv (e ▸ (hZ w).1 hw)
        rw [if_neg hne, mul_zero]), if_neg hv, add_zero, mul_comm, mul_assoc,
        inv_mul_cancel₀ (coe_ne_zero _ _ hv), mul_one]
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨t₁, ht₁I, β₁, hβ₁, rfl⟩) (sum_mem fun w _ => ?_)
  exact AddSubgroup.subset_closure ⟨τ w, hτI w, β w, hβ w, rfl⟩

theorem pairA_mul_tmul {E : Type} [Field E] [Algebra F E] (s : F) (β : Af F) (x : E) :
    pairA F 0 (algebraMap F (Af F) s * β) ⊗ₜ[F] x = pairA F 0 β ⊗ₜ[F] (algebraMap F E s * x) := by
  have h : pairA F 0 (algebraMap F (Af F) s * β) = s • pairA F 0 β :=
    Prod.ext (by change (0 : Ainf F) = s • 0; rw [smul_zero]) (by change _ = s • β; rw [Algebra.smul_def]; rfl)
  rw [h, TensorProduct.smul_tmul, Algebra.smul_def]

end Gen

theorem mem_hatA_of_div : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  intro D S T A hA γ hγ y hy
  let I : Ideal (𝓞 D.host.F) :=
    { carrier := {t | algebraMap D.host.F D.host.E (t : D.host.F) • y ∈ A}
      add_mem' := fun {a b} ha hb => by
        change algebraMap D.host.F D.host.E ((a : D.host.F) + (b : D.host.F)) • y ∈ A
        rw [map_add, add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change algebraMap D.host.F D.host.E (0 : D.host.F) • y ∈ A
        rw [map_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c {x} hx => by
        change algebraMap D.host.F D.host.E ((c : D.host.F) * (x : D.host.F)) • y ∈ A
        rw [map_mul, mul_smul]
        exact hA c _ hx }
  have hmem := mem_mulG I hγ fun w => (hy w).imp id fun ⟨t, ht, hA'⟩ => ⟨t, hA', ht⟩
  let f : Af D.host.F →+ WO S T :=
    { toFun := fun α => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a
      map_zero' := Matrix.ext fun a k => by
        change pairA D.host.F 0 0 ⊗ₜ[D.host.F] y k a = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun α β => Matrix.ext fun a k => by
        change pairA D.host.F 0 (α + β) ⊗ₜ[D.host.F] y k a =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a + pairA D.host.F 0 β ⊗ₜ[D.host.F] y k a
        rw [← TensorProduct.add_tmul]
        congr 1
        exact Prod.ext (add_zero 0).symm rfl }
  have hle : mulG I ≤ (hatA S T A).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, β, hβ, rfl⟩
    refine AddSubgroup.subset_closure ⟨β, hβ, _, ht, ?_⟩
    refine Matrix.ext fun a k => ?_
    change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (t : D.host.F) * β) ⊗ₜ[D.host.F] y k a =
      pairA D.host.F 0 β ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) • y) k a
    rw [pairA_mul_tmul, Matrix.smul_apply, smul_eq_mul]
  exact hle hmem

end GlobalTheory.HatPoint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfTypePlaceReductionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_of_type_place_reductions : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (y : GL (Fin T.rank) (EAf D)), LT.Q = ∅ → y ∈ UA D.sp.cm T.gram → y ∈ St βT → ∀ (a b : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1)), (∀ PP, a PP ∈ blockTri (blkOf LT.r LT.t)) → (∀ PP, b PP ∈ blockTri (blkOf LT.r LT.t)) → (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H → (fun PP => upperLeftBlock LT.hr (b PP)) ∈ LT.P.H → (∀ PP : ↥LT.Pg, b PP * redFn βT PP.1 y = a PP) → y ∈ lev D.sp.cm T.gram βT LT := by
  first | exact @GlobalTheory.MemLevRed.mem_lev_of_reductions | exact GlobalTheory.MemLevRed.mem_lev_of_reductions | (intros; apply GlobalTheory.MemLevRed.mem_lev_of_reductions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemMaximalCompactOfMapsFockVectorToFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.CompactStab

open scoped ComplexOrder

variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_kset_of_block {h : Matrix (Fin n) (Fin n) ℂ} (hh : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε)
    (hb : ∀ j k, ε j ≠ ε k → (hᴴ * h) j k = 0 ∨ (hᴴ * h) k j = 0) : h ∈ Formalism.REAL.Kset ε := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  set J := Formalism.REAL.Jm ε with hJd
  have h1 : (J * hᴴ * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, hJ]
  have h2 : h * (J * hᴴ * J) = 1 := mul_eq_one_comm.1 h1
  have h3 : h * J * hᴴ = J := by
    calc h * J * hᴴ = h * J * hᴴ * (J * J) := by rw [hJ, Matrix.mul_one]
      _ = (h * (J * hᴴ * J)) * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h2, Matrix.one_mul]
  set P := hᴴ * h with hP
  have hPh : Pᴴ = P := by rw [hP, conjTranspose_mul, conjTranspose_conjTranspose]
  have hb' : ∀ j k, ε j ≠ ε k → P j k = 0 := by
    intro j k hjk
    rcases hb j k hjk with h0 | h0
    · exact h0
    · rw [← hPh, conjTranspose_apply, h0, star_zero]
  have hc : P * J = J * P := by
    ext j k
    simp only [hJd, Formalism.REAL.Jm, mul_diagonal, diagonal_mul]
    by_cases hjk : ε j = ε k
    · rw [hjk, mul_comm]
    · simp [hb' j k hjk]
  have h4 : P * J * P = J := by
    calc P * J * P = hᴴ * (h * J * hᴴ) * h := by simp only [hP, Matrix.mul_assoc]
      _ = J := by rw [h3, hh]
  have h5 : P * P = 1 := by
    calc P * P = (J * J) * P * P := by rw [hJ, Matrix.one_mul]
      _ = J * (P * J * P) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h4, hJ]
  have h6 : IsUnit (1 + P) :=
    (Matrix.PosDef.add_posSemidef Matrix.PosDef.one (Matrix.posSemidef_conjTranspose_mul_self h)).isUnit
  have h7 : P = 1 := by
    apply h6.mul_left_cancel
    rw [add_mul, h5, one_mul, mul_one, add_comm]
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 h7, ?_⟩
  have h8 : h * hᴴ = 1 := mul_eq_one_comm.1 h7
  calc h * J = h * (hᴴ * J * h) := by rw [hh]
    _ = (h * hᴴ) * J * h := by simp only [Matrix.mul_assoc]
    _ = J * h := by rw [h8, Matrix.one_mul]

theorem exp_iJ_mem (t : ℝ) : NormedSpace.exp (t • (Complex.I • Formalism.REAL.Jm ε)) ∈ Formalism.REAL.Kset ε := by
  have h1 : (Complex.I • Formalism.REAL.Jm ε)ᴴ = -(Complex.I • Formalism.REAL.Jm ε) := by
    rw [conjTranspose_smul, Formalism.REAL.Jm_conjTranspose]; simp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, h1,
      star_trivial, smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • (Complex.I • Formalism.REAL.Jm ε))).neg_right, add_neg_cancel,
      NormedSpace.exp_zero]
  · exact (((Commute.refl (Formalism.REAL.Jm ε)).smul_left _).smul_left t).exp_left

theorem exp_conj_of_mul {a b X : Matrix (Fin n) (Fin n) ℂ} (hab : a * b = 1) (t : ℝ) :
    NormedSpace.exp (t • (a * X * b)) = a * NormedSpace.exp (t • X) * b := by
  have hb : a⁻¹ = b := Matrix.inv_eq_right_inv hab
  have ha : IsUnit a := IsUnit.of_mul_eq_one b hab
  rw [← hb, ← Matrix.exp_conj _ _ ha, Matrix.mul_smul, Matrix.smul_mul]

theorem deriv_mem {Z : Type} (F : Submodule ℂ (Z → ℂ)) [FiniteDimensional ℂ F] {f : ℝ → Z → ℂ} {v : Z → ℂ}
    (hf : ∀ t, f t ∈ F) (hd : ∀ z, HasDerivAt (fun t => f t z) (v z) 0) : v ∈ F := by
  have ht : Filter.Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) • (f t - f 0)) (nhdsWithin 0 {0}ᶜ) (nhds v) := by
    rw [tendsto_pi_nhds]
    intro z
    have := hasDerivAt_iff_tendsto_slope.1 (hd z)
    refine this.congr fun t => ?_
    simp [slope]
  exact F.closed_of_finiteDimensional.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun t => F.smul_mem _ (F.sub_mem (hf t) (hf 0)))

theorem mem_compact : ∀ (n : ℕ) (ε : Fin n → Bool) (fr G : Matrix (Fin n) (Fin n) ℂ) (σ Z : Type) [Finite σ] (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Z → ℂ)) (R : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (Z → ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (MvPolynomial σ ℂ)), IsUnit fr → frᴴ * Formalism.REAL.Jm ε * fr = G → Function.Injective pt → R 1 = 1 → (∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, R (g * g') = R g * R g') → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ φ z, HasDerivAt (fun t : ℝ => R (NormedSpace.exp (t • X)) (pt φ) z) (pt (L X φ) z) 0) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ φ, ∃ ψ, ψ.totalDegree ≤ φ.totalDegree ∧ R (fr⁻¹ * k * fr) (pt φ) = pt ψ) → (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → (∃ j k, ε j ≠ ε k ∧ (fr * X * fr⁻¹) j k ≠ 0 ∧ (fr * X * fr⁻¹) k j ≠ 0) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ m : ℕ, (L X ^ m) φ ∈ F) → ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ φ φ', φ ≠ 0 → pt φ' = R g (pt φ) → ∃ k ∈ Formalism.REAL.Kset ε, g = fr⁻¹ * k * fr := by
  intro n ε fr G σ Z _ pt R L hfr hG hinj hR1 hmul hder hK hgrow g hg φ φ' hφ hφ'
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hJh := Formalism.REAL.Jm_conjTranspose ε
  set J := Formalism.REAL.Jm ε with hJd
  have hdet := (Matrix.isUnit_iff_isUnit_det fr).1 hfr
  have f1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hdet
  have f2 : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul fr hdet
  have f1' : ∀ x : Matrix (Fin n) (Fin n) ℂ, fr * (fr⁻¹ * x) = x := fun x => by
    rw [← Matrix.mul_assoc, f1, Matrix.one_mul]
  have f2' : ∀ x : Matrix (Fin n) (Fin n) ℂ, fr⁻¹ * (fr * x) = x := fun x => by
    rw [← Matrix.mul_assoc, f2, Matrix.one_mul]
  have f3' : ∀ x : Matrix (Fin n) (Fin n) ℂ, (fr⁻¹)ᴴ * (frᴴ * x) = x := fun x => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, f1, conjTranspose_one, Matrix.one_mul]
  have J' : ∀ x : Matrix (Fin n) (Fin n) ℂ, J * (J * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have cU : ∀ x : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → fr⁻¹ * x * fr ∈ Formalism.QuantumDeterminants.UH G := by
    intro x hx
    show (fr⁻¹ * x * fr)ᴴ * G * (fr⁻¹ * x * fr) = G
    calc (fr⁻¹ * x * fr)ᴴ * G * (fr⁻¹ * x * fr) = frᴴ * (xᴴ * J * x) * fr := by
          simp only [← hG, conjTranspose_mul, Matrix.mul_assoc, f1', f3']
      _ = G := by rw [hx, hG]
  obtain ⟨h, rfl⟩ : ∃ h, g = fr⁻¹ * h * fr := ⟨fr * g * fr⁻¹, by simp only [Matrix.mul_assoc, f2', f2, Matrix.mul_one]⟩
  have hh : hᴴ * J * h = J := by
    have e : (fr⁻¹ * h * fr)ᴴ * G * (fr⁻¹ * h * fr) = G := hg
    have e2 := congrArg (fun x => (fr⁻¹)ᴴ * x * fr⁻¹) e
    simpa only [← hG, conjTranspose_mul, Matrix.mul_assoc, f1', f3', f1, Matrix.mul_one] using e2
  refine ⟨h, mem_kset_of_block hh ?_, rfl⟩
  set h' := J * hᴴ * J with hh'
  have h1 : h' * h = 1 := by
    rw [hh', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc hᴴ, hh, hJ]
  have h2 : h * h' = 1 := mul_eq_one_comm.1 h1
  have h3 : h'ᴴ * J * h' = J := by
    calc h'ᴴ * J * h' = J * (h * h') := by
          simp only [hh', conjTranspose_mul, hJh, conjTranspose_conjTranspose, Matrix.mul_assoc, J']
      _ = J := by rw [h2, Matrix.mul_one]
  have hY' : h' * (Complex.I • J) * h = Complex.I • (J * (hᴴ * h)) := by
    simp only [hh', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, J']
  set Y := fr⁻¹ * (h' * (Complex.I • J) * h) * fr with hY
  have hYG : Yᴴ * G + G * Y = 0 := by
    rw [hY, hY']
    simp only [← hG, conjTranspose_mul, conjTranspose_smul, hJh, conjTranspose_conjTranspose, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, J', f1', f3']
    simp
  have cm : ∀ x y : Matrix (Fin n) (Fin n) ℂ, (fr⁻¹ * x * fr) * (fr⁻¹ * y * fr) = fr⁻¹ * (x * y) * fr := by
    intro x y
    simp only [Matrix.mul_assoc, f1']
  have cR : ∀ x y : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → yᴴ * J * y = J →
      R (fr⁻¹ * (x * y) * fr) = R (fr⁻¹ * x * fr) * R (fr⁻¹ * y * fr) := by
    intro x y hx hy
    rw [← cm, hmul _ (cU x hx) _ (cU y hy)]
  have kU : ∀ k ∈ Formalism.REAL.Kset ε, kᴴ * J * k = J := by
    intro k hk
    have e1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
    have e2 : k * J = J * k := hk.2
    rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have mU : ∀ x y : Matrix (Fin n) (Fin n) ℂ, xᴴ * J * x = J → yᴴ * J * y = J → (x * y)ᴴ * J * (x * y) = J := by
    intro x y hx hy
    calc (x * y)ᴴ * J * (x * y) = yᴴ * (xᴴ * J * x) * y := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [hx, hy]
  let F₀ : Submodule ℂ (Z → ℂ) :=
    (MvPolynomial.restrictTotalDegree σ ℂ φ'.totalDegree).map (R (fr⁻¹ * h' * fr) ∘ₗ pt)
  have : FiniteDimensional ℂ F₀ := inferInstance
  have m0 : pt φ ∈ F₀ := by
    refine ⟨φ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_⟩
    rw [LinearMap.comp_apply, hφ', ← Module.End.mul_apply, ← cR _ _ h3 hh, h1, Matrix.mul_one, f2, hR1,
      Module.End.one_apply]
  have st : ∀ (t : ℝ), ∀ v ∈ F₀, R (NormedSpace.exp (t • Y)) v ∈ F₀ := by
    rintro t _ ⟨ψ, hψ, rfl⟩
    have hk := exp_iJ_mem (ε := ε) t
    obtain ⟨ψ', hd, he⟩ := hK _ hk ψ
    refine ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).2
      (hd.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hψ)), ?_⟩
    rw [hY, exp_conj_of_mul f2, exp_conj_of_mul h1, LinearMap.comp_apply, LinearMap.comp_apply, ← he,
      ← Module.End.mul_apply, ← Module.End.mul_apply, ← cR _ _ h3 (kU _ hk),
      ← cR _ _ (mU _ _ (mU _ _ h3 (kU _ hk)) hh) h3, Matrix.mul_assoc _ h, h2, Matrix.mul_one]
  have hm : ∀ m : ℕ, (L Y ^ m) φ ∈ F₀.comap pt := by
    intro m
    induction m with
    | zero => exact m0
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact deriv_mem F₀ (fun t => st t _ ih) (hder Y hYG _)
  have hF : FiniteDimensional ℂ (F₀.comap pt) :=
    FiniteDimensional.of_injective (pt.submoduleComap F₀) (by
      intro a b hab
      exact Subtype.ext (hinj (congrArg Subtype.val hab)))
  intro j k hjk
  by_contra hc
  rw [not_or] at hc
  refine hgrow Y hYG ⟨j, k, hjk, ?_⟩ φ hφ _ hF hm
  have e : fr * Y * fr⁻¹ = Complex.I • (J * (hᴴ * h)) := by
    rw [hY, hY']
    simp only [Matrix.mul_assoc, f1', f1, Matrix.mul_one]
  rw [e]
  simp only [hJd, Formalism.REAL.Jm, Matrix.smul_apply, diagonal_mul, smul_eq_mul]
  constructor
  · refine mul_ne_zero Complex.I_ne_zero (mul_ne_zero ?_ hc.1)
    split_ifs <;> norm_num
  · refine mul_ne_zero Complex.I_ne_zero (mul_ne_zero ?_ hc.2)
    split_ifs <;> norm_num

end GlobalTheory.Chain.RealIt.CompactStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemUnipotentRadicalIffIotaMemAdelicRadical
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeOntoCusp

theorem mem_NI_iff_iota : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) := by
  intro D r C hC g
  let I := Formalism.IndefR.RationalEmbedding.inst D
  let T := (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  obtain ⟨L, R, hL, hR⟩ :=
    GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E) (J := (D.sp.Y 0).gram) I.J_det hC.2.1
  have key : ∀ h : GA D (D.sp.Y 0),
      T h ∈ I.NA (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) ↔
      GlobalTheory.CuspCompare.UnipEq (incA D) C R (Formalism.UG.cT (starRingEnd D.host.E) C * (D.sp.Y 0).gram) L
        ((matHom (D.sp.Y 0) h).1 - 1) := fun h => by
    have hs : (Formalism.IndefR.RationalEmbedding.iota D).symm (T h) = h := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply h
    refine GlobalTheory.CuspCompare.mem_NA_iff I (fun v => Formalism.IndefR.Eqv.thetaC D ((Formalism.L2.Host.tauPl D).symm v))
      (fun v => Formalism.IndefR.Eqv.isInfFam_thetaC D ((Formalism.L2.Host.tauPl D).symm v)) h (T h) ?_ (fun v => ?_) hL hR
    · have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (T h)).2
      have h2 := hb.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin I) hs)
      unfold Formalism.L2.SG.AdBridge.ofHAFin at h2
      rw [Formalism.L2.SG.EvalTIota.tauF_eq_i] at h2
      exact h2
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hb := Formalism.L2.SG.EvalTIota.infMat_brg_i (T h) ρ
      rw [hs] at hb
      simp only [Equiv.symm_apply_apply]
      exact hb.symm
  have hW : I.IsIsot (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff I _).2 ⟨r, C, hC, rfl⟩
  refine GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I _ hW).1 (fun g => ?_) g
  rw [key]
  exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)

end GlobalTheory.SeeOntoCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MonomialMemRangeGlue
section
noncomputable section

namespace GlobalTheory.MonomialRangeMembership

open MvPolynomial

theorem monomial_mem_range_glue {D : Formalism.BasicNotions.D7} {a b : ℕ}
    (m : Formalism.IndefR.Datum.FVar D b a →₀ ℕ) :
    (monomial m (1 : ℂ) : Formalism.IndefR.Links.PolF D b a) ∈
      Set.range (GlobalTheory.Chain.RealIt.glue (D := D) (a := a) (b := b)) := by
  refine ⟨fun τ => ∏ s : Fin b × Fin a, X s ^ m (τ, s), ?_⟩
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  unfold GlobalTheory.Chain.RealIt.glue
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [map_prod, map_pow, rename_X]

theorem span_range_glue : ∀ {D : Formalism.BasicNotions.D7} {a b : Nat}, @Eq (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.span Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing) (@Set.range (Formalism.IndefR.Links.PolF D b a) (@Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D) → GlobalTheory.Chain.RealIt.LPol b a) (@GlobalTheory.Chain.RealIt.glue D a b))) (@Top.top (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.instTop Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing))) := by
  intro D a b
  rw [eq_top_iff, ← (basisMonomials (Formalism.IndefR.Datum.FVar D b a) ℂ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  rw [coe_basisMonomials]
  exact monomial_mem_range_glue m

end GlobalTheory.MonomialRangeMembership
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotLocallyFiniteQuadraticMulAddDegreeNonraisingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_locallyFinite_quadraticMul_add_degreeNonraising : ∀ (σ : Type) [Finite σ] (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)), Q ≠ 0 → Q.IsHomogeneous 2 → (∀ P, (L P).totalDegree ≤ P.totalDegree) → ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ), FiniteDimensional ℂ F → ¬ ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ∈ F := by
  first | exact @GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add | exact GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add | (intros; apply GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProjectionToLeviStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_projection_to_levi : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∃ μ : UJ ε → UJ ε, ContinuousOn μ (parab ε W : Set (UJ ε)) ∧ (∀ p ∈ parab ε W, μ p ∈ leviOne ε W) ∧
      (∀ p ∈ parab ε W, ∀ q ∈ parab ε W, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ (x : Fin a → ℝ) (t : UJ ε), IsSplit ε W x t →
        u * m * t ∈ parab ε W ∧ μ (u * m * t) = m := by
  first | exact @GlobalTheory.LeviProj.exists_leviOne_part | exact GlobalTheory.LeviProj.exists_leviOne_part | (intros; apply GlobalTheory.LeviProj.exists_leviOne_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalLevelRelIndexLiftLevelEqCardStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_relIndex_liftLevel_eq_card : ∀ (D : D7) (T0 : Type) (C : LevCh D T0) (μ0 : T0), C.Is μ0 → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → C.Pg ⊆ Z → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), levG (Wc D i) (C.βW i) (C.datWp i C.triv) ≤ levG (Wc D i) (C.βW i) (C.datWp i P) ∧ (levG (Wc D i) (C.βW i) (C.datWp i C.triv)).relIndex (levG (Wc D i) (C.βW i) (C.datWp i P)) = Nat.card P.H ∧ Nat.card P.H ≠ 0 := by
  first | exact @GlobalTheory.LevIdx.levidx | exact GlobalTheory.LevIdx.levidx | (intros; apply GlobalTheory.LevIdx.levidx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientMeasureFibrationStatement
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_fibration : ∀ (A : Type) [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [SecondCountableTopology A] [LocallyCompactSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A] (B : Type) [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [SecondCountableTopology B] [LocallyCompactSpace B] [T2Space B] [MeasurableSpace B] [BorelSpace B] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (e : A × B ≃ₜ* H) (TA : Subgroup A) (TB : Subgroup B) (T : Subgroup H), (∀ a b, e (a, b) ∈ T ↔ a ∈ TA ∧ b ∈ TB) → IsClosed (T : Set H) → IsMulCommutative T → ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (da : Measure A) [da.IsHaarMeasure] (ds : Measure TA) [ds.IsHaarMeasure] (φ : H → ℂ), LeftInv T φ → Integrable (descend T φ) (quotMeas T dt dh) → (∀ b, quotInt TA ds da (fun a => φ (e (a, b))) = 0) → quotInt T dt dh φ = 0 := by
  first | exact @GlobalTheory.Orb.FubiniQuot.quotInt_eq_zero_of_fiber | exact GlobalTheory.Orb.FubiniQuot.quotInt_eq_zero_of_fiber | (intros; apply GlobalTheory.Orb.FubiniQuot.quotInt_eq_zero_of_fiber <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNegStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_form_re_neg_of_ne_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ x, g x = g 0 * Complex.exp (M x x)) → ∀ v, v ≠ 0 → (M v v).re < 0 := by
  first | exact @GlobalTheory.schwartz_gaussian_form_re_neg | exact GlobalTheory.schwartz_gaussian_form_re_neg | (intros; apply GlobalTheory.schwartz_gaussian_form_re_neg <;> assumption)
end

