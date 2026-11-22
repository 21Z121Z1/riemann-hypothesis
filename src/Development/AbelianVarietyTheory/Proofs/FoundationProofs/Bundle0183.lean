import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataTowerUnionAdjoin
section
noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.TrTower

section Sep

variable {L : Type*} [Field L] {G : Type*} [Group G] [MulSemiringAction G L]

theorem isSep_mul_right {v : Valuation L ℝ≥0} {N : Subgroup G} {n : ℕ} {a b : Fin n → L} {c : L}
    (h : IsSep v N a b c) {d : L} (hd : d ∈ Fix L N) (hdv : v d ≤ 1) (hcd : v (c * d) ≤ 1) :
    IsSep v N (fun i => a i * d) b (c * d) where
  a_mem i := mul_mem (h.a_mem i) hd
  b_mem := h.b_mem
  c_mem := mul_mem h.c_mem hd
  a_le i := by rw [map_mul]; exact mul_le_one' (h.a_le i) hdv
  b_le := h.b_le
  c_le := hcd
  sum_in σ hσ := by
    simp_rw [mul_right_comm _ d]; rw [← Finset.sum_mul, h.sum_in σ hσ]
  sum_out σ hσ := by
    simp_rw [mul_right_comm _ d]; rw [← Finset.sum_mul, h.sum_out σ hσ, zero_mul]

theorem isSep_swap {v : Valuation L ℝ≥0} {N : Subgroup G} {n : ℕ} {a b : Fin n → L} {c : L}
    (h : IsSep v N a b c) : IsSep v N b a c where
  a_mem := h.b_mem
  b_mem := h.a_mem
  c_mem := h.c_mem
  a_le := h.b_le
  b_le := h.a_le
  c_le := h.c_le
  sum_in σ hσ := by
    have h1 := congrArg (σ • ·) (h.sum_in σ⁻¹ (inv_mem hσ))
    have hc : σ • c = c := h.c_mem ⟨σ, hσ⟩
    simp only [Finset.smul_sum, smul_mul', smul_inv_smul, hc] at h1
    simpa [mul_comm] using h1
  sum_out σ hσ := by
    have h1 := congrArg (σ • ·) (h.sum_out σ⁻¹ (fun h' => hσ (by simpa using inv_mem h')))
    simp only [Finset.smul_sum, smul_mul', smul_inv_smul, smul_zero] at h1
    simpa [mul_comm] using h1

end Sep

section Tower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def fixInt {H : Subgroup (Gal p Ω)} (V : Subgroup H) :
    Subalgebra (O0 p) (integralClosure (O0 p) Ω) where
  carrier := {s | ∀ g : V, g • (s : Ω) = s}
  mul_mem' {x y} hx hy g := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_mul] at *
    rw [smul_mul', hx g, hy g]
  add_mem' {x y} hx hy g := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
    rw [smul_add, hx g, hy g]
  algebraMap_mem' r g := by
    show g • (algebraMap (O0 p) Ω r) = _
    exact ((g : H) : Gal p Ω).commutes r

theorem towerAlg_fixed (T : Tower p Ω) {s : integralClosure (O0 p) Ω} (hs : s ∈ towerAlg T)
    (g : ↥(⨅ n, Gn T n)) : g • (s : Ω) = s := by
  have hle : towerAlg T ≤ fixInt (⊤ : Subgroup ↥(⨅ n, Gn T n)) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩) g
    · exact ((GlobalTheory.K5.Basic.mem_gn T m _).1 (Subgroup.mem_iInf.1 (g : ↥(⨅ n, Gn T n)).2 m)).1
    · exact ((GlobalTheory.K5.Basic.mem_gn T m _).1 (Subgroup.mem_iInf.1 (g : ↥(⨅ n, Gn T n)).2 m)).2
  exact hle hs ⟨g, trivial⟩

end Tower

end GlobalTheory.AlmostEt.TrTower

namespace GlobalTheory.AlmostEt.TrTower

theorem exists_trData_towerAlg : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (F : Finset (integralClosure (O0 p) Ω)),
    ∃ (C : Subalgebra (O0 p) (integralClosure (O0 p) Ω))
      (tr : (integralClosure (O0 p) Ω) → (integralClosure (O0 p) Ω)) (n : ℕ)
      (a b : Fin n → (integralClosure (O0 p) Ω)),
      (↑F : Set (integralClosure (O0 p) Ω)) ⊆ C ∧
        IsTrData (towerAlg T) C tr a b (p : (integralClosure (O0 p) Ω)) := by
  intro p _ Ω _ _ hp2 hclo T F
  classical
  have hpcoe : ((p : integralClosure (O0 p) Ω) : Ω) = p := map_natCast (integralClosure (O0 p) Ω).val p
  obtain ⟨v, hvint, hvinv, hp0, hp1, hS⟩ := GlobalTheory.T.exists_valuation_almostEtale_towerFixer p Ω hp2 hclo T
  obtain ⟨U, -, hUfin, hUfix, hUsep⟩ := hS (F.image Subtype.val)
  obtain ⟨n, a, b, c, hsep, hc⟩ := hUsep (v p) hp1
  haveI := hUfin
  haveI : Fintype (↥(⨅ n, Gn T n) ⧸ U) := Fintype.ofFinite _
  have hvinv' : ∀ (g : ↥(⨅ n, Gn T n)) (x : Ω), v (g • x) = v x := fun g x => hvinv g x
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact (not_lt_zero' hc)
  have hvc : 0 < v c := lt_of_le_of_lt (by positivity) hc

  have hpfix : ∀ (g : ↥(⨅ n, Gn T n)), g • (p : Ω) = p := fun g => by
    change ((g : Gal p Ω)) (p : Ω) = p
    exact map_natCast _ p
  have hd : (p : Ω) / c ∈ Fix Ω U := div_mem (fun g => hpfix g) hsep.c_mem
  have hdv : v ((p : Ω) / c) ≤ 1 := by
    rw [map_div₀]; exact div_le_one_of_le₀ hc.le (by positivity)
  have hsep' : IsSep v U (fun i => a i * ((p : Ω) / c)) b (p : Ω) := by
    have := isSep_mul_right hsep hd hdv (by rw [mul_div_cancel₀ _ hc0]; exact hp1.le)
    rwa [mul_div_cancel₀ _ hc0] at this
  have hsw := isSep_swap hsep'
  have hint : ∀ x : Ω, v x ≤ 1 → x ∈ integralClosure (O0 p) Ω := fun x hx => (hvint x).1 hx
  let a' : Fin n → integralClosure (O0 p) Ω := fun i => ⟨_, hint _ (hsep'.a_le i)⟩
  let b' : Fin n → integralClosure (O0 p) Ω := fun i => ⟨_, hint _ (hsep'.b_le i)⟩
  have htrint : ∀ s : integralClosure (O0 p) Ω, cosetTrace U (s : Ω) ∈ integralClosure (O0 p) Ω :=
    fun s => Subalgebra.sum_mem _ fun q _ => GlobalTheory.K5.Basic.isInt_gal _ s.2
  let tr : integralClosure (O0 p) Ω → integralClosure (O0 p) Ω := fun s => ⟨_, htrint s⟩
  have htr : ∀ s, (tr s : Ω) = cosetTrace U (s : Ω) := fun s => rfl
  have hle : towerAlg T ≤ fixInt U := fun s hs g => towerAlg_fixed T hs (g : ↥(⨅ n, Gn T n))
  refine ⟨fixInt U, tr, n, a', b', ?_, ?_⟩
  · intro s hs
    exact hUfix _ (Finset.mem_image_of_mem _ hs)
  refine
    { le := hle
      e_mem := Subalgebra.natCast_mem _ p
      a_mem := fun i => hsep'.a_mem i
      b_mem := fun i => hsep'.b_mem i
      tr_mem := ?_
      tr_add := ?_
      tr_mul := ?_
      left := ?_
      right := ?_
      sum := ?_ }
  · intro x hx
    apply GlobalTheory.T.mem_towerUnionAdjoin_of_galois_fixed p Ω hclo T
    intro g hg
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).1 ⟨g, hg⟩
  · intro x _ y _
    apply Subtype.ext
    simp only [htr, Subalgebra.coe_add, cosetTrace, smul_add, Finset.sum_add_distrib]
  · intro β hβ x hx
    apply Subtype.ext
    simp only [htr, Subalgebra.coe_mul]
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).2.2 _ (towerAlg_fixed T hβ)
  · intro x hx
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq Ω v _ U n _ _ _ hsep' _ hx
  · intro x hx
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq Ω v _ U n _ _ _ hsw _ hx
  · apply Subtype.ext
    simp only [Subalgebra.coe_mul, hpcoe, AddSubmonoidClass.coe_finsetSum]
    simpa using hsep'.sum_in 1 (one_mem _)

end GlobalTheory.AlmostEt.TrTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma norm_petersson_self (k : ℕ) (h : ℍ → ℂ) (z : ℍ) :
    ‖petersson (k : ℤ) h h z‖ = ‖h z‖ ^ 2 * z.im ^ k := by
  simp only [petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z.im_pos]
  ring

lemma isZeroAtImInfty_of_bound (k : ℕ) (hk : 1 ≤ k) (h : ℍ → ℂ) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖h τ‖ ^ 2 * τ.im ^ k ≤ C) : IsZeroAtImInfty h := by
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hsq : Tendsto (fun τ : ℍ => ‖h τ‖ ^ 2) atImInfty (𝓝 0) := by
    have hlim : Tendsto (fun τ : ℍ => max C 0 * (τ.im)⁻¹) atImInfty (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp him).const_mul (max C 0)
    refine squeeze_zero' (Eventually.of_forall fun τ => by positivity) ?_ hlim
    filter_upwards [him.eventually_ge_atTop 1] with τ hτ
    have hpos : 0 < τ.im := τ.im_pos
    have hpow : τ.im ≤ τ.im ^ k := by
      calc τ.im = τ.im ^ 1 := (pow_one _).symm
        _ ≤ τ.im ^ k := pow_le_pow_right₀ hτ hk
    rw [le_mul_inv_iff₀ hpos]
    calc ‖h τ‖ ^ 2 * τ.im ≤ ‖h τ‖ ^ 2 * τ.im ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ C := hC τ
      _ ≤ max C 0 := le_max_left _ _
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

end GlobalTheory.EisM

theorem GlobalTheory.EisM.cuspForm_of_CF : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ f : CuspForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.modularForm_gammaOne_of_coeffSeq k L N ε a hL hNL hcf.1
  obtain ⟨C, hC⟩ := hcf.2
  have hall : ∀ γ : SL(2, ℤ), IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] γ) := by
    intro γ
    refine isZeroAtImInfty_of_bound k hk _ C fun τ => ?_
    have h1 := congrArg norm (petersson_slash_SL (k : ℤ) (f : ℍ → ℂ) f γ τ)
    rw [norm_petersson_self, norm_petersson_self, hf] at h1
    rw [hf, h1]
    exact hC _
  refine ⟨⟨f.toSlashInvariantForm, f.holo', ?_⟩, hf⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact hall γ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHom
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

variable {Ω : Type} [Field Ω] (ε : Ω →+* ℂ)

theorem exists_isExp_of_mem_ring (a : ring ε.range) : ∃ h : HahnSeries ℚ Ω, IsExp ε a h :=
  GlobalTheory.T.exists_cuspExpansionAtInfinity_of_someLevel Ω ε a (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2)

def expan (a : ring ε.range) : HahnSeries ℚ Ω := Classical.choose (exists_isExp_of_mem_ring ε a)

theorem isExp_expan (a : ring ε.range) : IsExp ε a (expan ε a) :=
  Classical.choose_spec (exists_isExp_of_mem_ring ε a)

theorem expan_eq_of_isExp {a : ring ε.range} {h : HahnSeries ℚ Ω} (ha : IsExp ε a h) : expan ε a = h :=
  (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (isExp_expan ε a) ha

def expanHom : ring ε.range →+* HahnSeries ℚ Ω where
  toFun := expan ε
  map_one' := by
    apply expan_eq_of_isExp
    have h := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.1 1
    have e1 : ((1 : ring ε.range) : ℍ → ℂ) = fun _ => ε 1 := by ext; simp
    rw [e1]; simpa using h
  map_mul' a b := by
    apply expan_eq_of_isExp
    have h := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.2
    simpa using h
  map_zero' := by
    apply expan_eq_of_isExp
    have h := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.1 0
    have e0 : ((0 : ring ε.range) : ℍ → ℂ) = fun _ => ε 0 := by ext; simp
    rw [e0]; simpa using h
  map_add' a b := by
    apply expan_eq_of_isExp
    have h := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).1
    simpa using h

theorem expanHom_injective : Function.Injective (expanHom ε) := by
  intro a b hab
  have hsub := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.1
  have h0 : expan ε a - expan ε b = 0 := sub_eq_zero.mpr hab
  rw [h0] at hsub
  have hmem : ((a - b : ring ε.range) : ℍ → ℂ) ∈ ring ε.range := (a - b).2
  have hin : InR ε.range ((a - b : ring ε.range) : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 hmem
  have hhol := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ε.range _ hin
  push_cast at hhol
  have := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.2.1 _ hhol hsub
  exact Subtype.ext (sub_eq_zero.mp this)

theorem expansion_injective_ringHom :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω,
      Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) :=
  fun _ _ ε => ⟨expanHom ε, expanHom_injective ε, isExp_expan ε⟩

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeToStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_quotient_level_prime_to : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → ∃ (M' : ℕ) (a b : X.K) (c : Ω), 0 < M' ∧ Nat.Coprime q M' ∧ M₀ * l ^ k ∣ M' ∧ Lev X M' a ∧ Lev X M' b ∧ Prim X V a ∧ Prim X V b ∧ c ≠ 0 ∧ f * b = algebraMap Ω X.K c * a := by
  first | exact @GlobalTheory.KZ.ES.Quot.quot_prim | exact GlobalTheory.KZ.ES.Quot.quot_prim | (intros; apply GlobalTheory.KZ.ES.Quot.quot_prim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

open Asymptotics Function

theorem isBigO_qParam_pow_of_qExpansion_coeff_zero {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ) (h : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    have := h i hi
    rw [qExpansion_coeff] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt ha).mp h1
  have ht := qParam_tendsto_atImInfty (h := 1) one_pos
  have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have h3 := (isBigO_refl (fun τ : ℍ => Periodic.qParam 1 τ ^ m) atImInfty).mul h2
  simp only [mul_one] at h3
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually hfg] with τ hτ
  rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
  rw [hτ]; simp

theorem qExpansion_coeff_zero_of_isBigO_qParam_pow {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hlt.ne_top
    rw [← hj] at hlt
    have hjm : j < m := by exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hfg⟩ := ha.analyticOrderAt_eq_natCast.mp hj.symm
    have ht := qParam_tendsto_atImInfty (h := 1) one_pos
    have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty]
        fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j) := by
      have h3 := (isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h
      refine h3.congr' ?_ ?_
      · filter_upwards [ht.eventually hfg] with τ hτ
        rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        rw [hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
      · refine Eventually.of_forall fun τ => ?_
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        simp only
        rw [pow_sub₀ _ hq hjm.le, mul_comm]
    have h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0) := by
      have := ht.pow (m - j)
      rwa [zero_pow (by omega)] at this
    exact hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha] at h1
  intro n hn
  rw [qExpansion_coeff, h1 n hn, mul_zero]

theorem modularFormNorm_isBigO_self_atImInfty {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))
  have hb : ∀ q : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ),
      SlashInvariantForm.quotientFunc (k := k) f q =O[atImInfty] fun _ => (1 : ℂ) := by
    refine Quotient.forall.mpr fun ⟨r, hr⟩ => ?_
    have hc : IsCusp OnePoint.infty 𝒮ℒ := Fact.out
    have := (ModularForm.translate f r⁻¹).bdd_at_cusps' (c := OnePoint.infty)
      (by simpa using hc.of_isFiniteRelIndex_conj hr)
    rw [OnePoint.isBoundedAt_infty_iff] at this
    have h2 : (ModularForm.translate f r⁻¹ : ℍ → ℂ) =O[atImInfty] (1 : ℍ → ℝ) := this
    refine IsBigO.trans h2 ?_
    exact IsBigO.of_bound 1 (by simp)
  have h1 : (∏ q ∈ Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)),
      SlashInvariantForm.quotientFunc (k := k) f q) =O[atImInfty] fun _ => (1 : ℂ) := by
    have := IsBigO.finsetProd (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))) (fun q _ => hb q)
    simpa [Finset.prod_fn] using this
  have h2 := (isBigO_refl (f : ℍ → ℂ) atImInfty).mul h1
  simp only [mul_one] at h2
  refine h2.congr_left fun τ => ?_
  have h3 := congr_fun (Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (k := k) f q)
    (Finset.mem_univ (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)))) τ
  rw [ModularForm.coe_norm]
  have h4 : SlashInvariantForm.quotientFunc (k := k) f (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)) = f := by simp
  rw [h4, Pi.mul_apply] at h3
  convert h3

theorem exists_sturmBound_modularForm_arithmetic {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : ModularForm Γ k, (∀ n < m, (qExpansion 1 f).coeff n = 0) → f = 0 := by
  refine ⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩
  have h1 := qExpansion_coeff_zero_of_isBigO_qParam_pow one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _
    ((modularFormNorm_isBigO_self_atImInfty f).trans (isBigO_qParam_pow_of_qExpansion_coeff_zero hΓ f _ hf))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

theorem sturm_coef_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L →
    ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  intro k L N ε hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.modularForm_gammaOne_of_coeffSeq k L N ε a hL hN ha
  have hc : ∀ n, (qExpansion 1 f).coeff n = a n := by
    intro n
    have := GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane a ha.1 n
    unfold coef at this
    rw [← this, hf]
  have h0 : f = 0 := hm f fun n hn => by rw [hc n]; exact hz n hn
  funext n
  rw [← hc n, h0]
  simp [qExpansion_zero]

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FormsOfCharactersIndependentStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_mf_ch_sum_eq_zero : ∀ (k L N : ℕ) (a : DirichletCharacter ℂ N → ℕ → ℂ), 0 < L → N ∣ L → (∀ ε, MF k L (ch ε) (a ε)) → (∑ ε, a ε) = 0 → ∀ ε, a ε = 0 := by
  first | exact @GlobalTheory.EisM.Indep.forms_of_characters_independent | exact GlobalTheory.EisM.Indep.forms_of_characters_independent | (intros; apply GlobalTheory.EisM.Indep.forms_of_characters_independent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSetStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galB_mem_kummer_invariant_set : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := by
  first | exact @GlobalTheory.KZ.StabGal.galB_mem_B | exact GlobalTheory.KZ.StabGal.galB_mem_B | (intros; apply GlobalTheory.KZ.StabGal.galB_mem_B <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGeStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodSquarefreeLabelTuples_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  first | exact @GlobalTheory.BadShare.goodSet_weight_ge | exact GlobalTheory.BadShare.goodSet_weight_ge | (intros; apply GlobalTheory.BadShare.goodSet_weight_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSetStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_letter_preserves_basis_set : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T : Letter, admitted N l T → ∀ b ∈ X.B N l w, X.op N l T b ∈ X.B N l w := by
  first | exact @GlobalTheory.KZ.B_stable_op | exact GlobalTheory.KZ.B_stable_op | (intros; apply GlobalTheory.KZ.B_stable_op <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOneStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one : ∀ (s : ℝ), 0 < s → IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.stripLow_integrableOn_im_rpow | exact GlobalTheory.EisM.stripLow_integrableOn_im_rpow | (intros; apply GlobalTheory.EisM.stripLow_integrableOn_im_rpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialSpanHeckeLetterStableStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)), p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  first | exact @GlobalTheory.KZ.H3.lam_stable | exact GlobalTheory.KZ.H3.lam_stable | (intros; apply GlobalTheory.KZ.H3.lam_stable <;> assumption)
end

