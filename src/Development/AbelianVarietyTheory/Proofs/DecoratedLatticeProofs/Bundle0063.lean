import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
import Formalism.LocalToGlobal.HermitianForms.Bundle0003
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReduction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AltENsmulLeft
section
open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.TwPerSelfDual

open Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.Th1.H

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}

theorem hv_apply' (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem embH_apply' (emb : ι → E →+* ℂ) (δ : ℂ) (x : HomE E a b) (τ : ι) (i : Fin b) (j : Fin a) :
    embH emb δ x τ i j = δ * emb τ (x (Pi.single j 1) i) := rfl

theorem hv_smul_emb (emb : ι → E →+* ℂ) (δ : ℂ) (sc : ℝ)
    (hst : ∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : HomE E a b) :
    HV sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  rw [hv_apply', hv_apply']
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [embH_apply', LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hst, Complex.conj_conj]
  ring

theorem embH_injective' [Nonempty ι] (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective (embH emb δ : HomE E a b → VV ι a b) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [embH_apply', embH_apply'] at this
  simpa using (emb τ).injective (mul_left_cancel₀ hδ this)

theorem altE_nsmul_left {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (n : ℕ) (v w : V) :
    altE H (n • v) w = altE H v (n • w) := by
  simp only [altE, map_nsmul, LinearMap.smul_apply]

section Mod

variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem npow_smul_mem (L : Submodule (𝓞 E) W) (c n : ℕ) {y : W} (hy : y ∈ L) : ((c : E) ^ n) • y ∈ L := by
  induction n with
  | zero => simpa using hy
  | succ n ih => rw [pow_succ', mul_smul]; exact nat_smul_mem L c ih

theorem zpow_smul_mem (L : Submodule (𝓞 E) W) (c : ℕ) {k : ℤ} (hk : 0 ≤ k) {y : W} (hy : y ∈ L) :
    ((c : E) ^ k) • y ∈ L := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [zpow_natCast]; exact npow_smul_mem L c n hy

end Mod

theorem twO_selfDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ (twist₂ M c e)) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e hδ hst hc he her hSD hSC
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hstk : ∀ k : ℤ, star ((c : E) ^ k) = (c : E) ^ k := fun k => by rw [star_zpow₀, star_natCast]
  have hSD' : dualLat (HV sc) (laV emb δ M) = laV emb δ M := hSD
  have hdualM : ∀ z : HomE E a b, (∀ y ∈ M, ∃ m : ℤ, altE (HV sc) (embH emb δ z) (embH emb δ y) = m) → z ∈ M := by
    intro z hz
    have h1 : embH emb δ z ∈ dualLat (HV sc) (laV emb δ M) := by
      rintro _ ⟨y, hy, rfl⟩
      exact hz y hy
    rw [hSD'] at h1
    obtain ⟨z', hz', e'⟩ := h1
    rwa [← embH_injective' emb hδ e']
  have hcM : ∀ y ∈ M, (c : E) • y ∈ twist₂ M c e := by
    intro y hy
    rw [mem_twO]
    intro Q
    apply le_locP'
    rw [smul_smul, ← zpow_neg, ← zpow_add_one₀ hcE]
    apply zpow_smul_mem M c _ hy
    rcases her Q with h | h | h <;> rw [h] <;> norm_num
  show dualLat (HV sc) (laV emb δ (twist₂ M c e)) = laV emb δ (twist₂ M c e)
  apply le_antisymm
  · intro v hv
    have hcv : c • v ∈ dualLat (HV sc) (laV emb δ M) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [altE_nsmul_left, ← map_nsmul]
      apply hv
      refine ⟨c • y, ?_, rfl⟩
      show c • y ∈ twist₂ M c e
      rw [← Nat.cast_smul_eq_nsmul E]
      exact hcM y hy
    rw [hSD'] at hcv
    obtain ⟨m, hm, hmv⟩ := hcv
    set x : HomE E a b := ((c : E)⁻¹) • m with hxdef
    have hxm : (c : E) • x = m := by rw [hxdef, smul_smul, mul_inv_cancel₀ hcE, one_smul]
    have hxv : embH emb δ x = v := by
      have h1 : c • embH emb δ x = c • v := by
        rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul E, hxm]; exact hmv
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h1
      exact smul_right_injective _ hcC h1
    refine ⟨x, ?_, hxv⟩
    show x ∈ twist₂ M c e
    rw [mem_twO]
    intro Q
    have hc2 : ((c : 𝓞 E) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc.ne')
    obtain ⟨t, ht, hwt⟩ := GlobalTheory.exists_not_mem_dvd_locally_away E (conjPrime₂ Q) _ hc2
    have hT : ∀ y ∈ M, (algebraMap (𝓞 E) E t * ((c : E) ^ e Q)⁻¹) • y ∈ twist₂ M c e := by
      intro y hy
      rw [mem_twO]
      intro Q'
      rw [smul_smul]
      by_cases hQ' : Q' = conjPrime₂ Q
      · subst hQ'
        rw [he Q, zpow_neg, inv_inv]
        have h1 : (c : E) ^ e Q * (algebraMap (𝓞 E) E t * ((c : E) ^ e Q)⁻¹) = algebraMap (𝓞 E) E t := by
          have : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ hcE
          field_simp
        rw [h1, IsScalarTower.algebraMap_smul]
        exact le_locP' M _ (M.smul_mem t hy)
      · obtain ⟨w, hw, z, hz⟩ := hwt Q' hQ'
        have hz' : algebraMap (𝓞 E) E w * algebraMap (𝓞 E) E t = (c : E) ^ 2 * algebraMap (𝓞 E) E z := by
          have := congrArg (algebraMap (𝓞 E) E) hz
          simpa using this
        have hn : (((2 - e Q' - e Q).toNat : ℕ) : ℤ) = 2 - e Q' - e Q :=
          Int.toNat_of_nonneg (by rcases her Q with h | h | h <;> rcases her Q' with h' | h' | h' <;> omega)
        refine loc_of_scal M Q' hw (ρ := (c : 𝓞 E) ^ (2 - e Q' - e Q).toNat * z) ?_ hy
        rw [map_mul, map_pow, map_natCast, ← zpow_natCast, hn, zpow_sub₀ hcE, zpow_sub₀ hcE, zpow_ofNat]
        linear_combination (((c : E) ^ e Q')⁻¹ * ((c : E) ^ e Q)⁻¹) * hz'
    refine ⟨cO E t, fun h => ht ((mem_conjP Q t).2 h), ?_⟩
    rw [← IsScalarTower.algebraMap_smul E (cO E t), smul_smul]
    apply hdualM
    intro y hy
    unfold altE
    rw [hv_smul_emb emb δ sc hst, star_mul', algebraMap_cO, star_star, star_inv₀, hstk, hxv]
    exact hv _ ⟨_, hT y hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (GlobalTheory.T.hermitian_cocycle_integral_of_local E ι a b emb δ d sc M hδ hst hSD hSC x y fun Q =>
      ⟨(c : E) ^ e Q, zpow_ne_zero _ hcE, (mem_twO _ _ _ _).1 hx Q, ?_⟩).1
    rw [hstk]
    have := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [he Q, zpow_neg, inv_inv] at this

end GlobalTheory.TwPerSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardSubspacesContainingRangeQVandermonde
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.RangeKerCount

open GlobalTheory.KerRangeCount Formalism.L2.Col

theorem card_above_range_eq_sum : ∀ (κ : Type) [Field κ] [Finite κ] (U U' : Type) [AddCommGroup U] [Module κ U] [FiniteDimensional κ U] [AddCommGroup U'] [Module κ U'] [FiniteDimensional κ U'] (f : U →ₗ[κ] U') (t e : ℕ), Module.finrank κ U' = Module.finrank κ U + t → e ≤ Module.finrank κ U' → Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} = ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then Nat.card κ ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin (Nat.card κ) t (e - n) else 0) * Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} := by
  intro κ _ _ U U' _ _ _ _ _ _ f t e hU' he
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  rw [Nat.card_eq_fintype_card (α := κ)]
  have hq0 : Fintype.card κ ≠ 0 := Fintype.card_ne_zero
  have hrk := f.finrank_range_add_finrank_ker
  have hin : ∀ n, Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} =
      Formalism.L2.Col.gaussBin (Fintype.card κ) (Module.finrank κ (LinearMap.ker f)) n := by
    intro n
    rw [← card_below (LinearMap.ker f) n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun X => and_comm)
  have hL : Nat.card {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} =
      Formalism.L2.Col.gaussBin (Fintype.card κ) (Module.finrank κ (LinearMap.ker f) + t) e := by
    by_cases hem : e ≤ Module.finrank κ (LinearMap.ker f) + t
    · rw [gaussBin_symm hq0 (Module.finrank κ (LinearMap.ker f) + t) e
        (Module.finrank κ (LinearMap.ker f) + t - e) (by omega)]
      have h := card_above (k := κ) (LinearMap.range f) (Module.finrank κ (LinearMap.ker f) + t - e)
      rw [show Module.finrank κ U' - Module.finrank κ (LinearMap.range f) =
        Module.finrank κ (LinearMap.ker f) + t by omega] at h
      rw [← h]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun X =>
        ⟨fun h => ⟨by omega, h.1⟩, fun h => ⟨h.2, by omega⟩⟩)
    · have : IsEmpty {X : Submodule κ U' // LinearMap.range f ≤ X ∧ Module.finrank κ X + e = Module.finrank κ U'} :=
        ⟨fun X => by have := Submodule.finrank_mono X.2.1; have := X.2.2; omega⟩
      rw [Nat.card_of_isEmpty, gaussBin_eq_zero _ (by omega)]
  set q := Fintype.card κ
  set m := Module.finrank κ (LinearMap.ker f)
  set g : ℕ → ℕ := fun n => (if n ≤ e then q ^ (n * (t - (e - n))) * Formalism.L2.Col.gaussBin q t (e - n) else 0) *
    Formalism.L2.Col.gaussBin q m n with hg
  have hR : ∑ n ∈ Finset.range (Module.finrank κ U + 1), (if n ≤ e then q ^ (n * (t - (e - n))) *
      Formalism.L2.Col.gaussBin q t (e - n) else 0) *
      Nat.card {X : Submodule κ U // X ≤ LinearMap.ker f ∧ Module.finrank κ X = n} =
      ∑ n ∈ Finset.range (Module.finrank κ U + 1), g n :=
    Finset.sum_congr rfl fun n _ => by rw [hin]
  have h2 : ∑ n ∈ Finset.range (e + 1), g n = ∑ n ∈ Finset.range (e + Module.finrank κ U + 1), g n :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      rw [Finset.mem_range] at hn
      simp only [hg]
      rw [if_neg (by omega), zero_mul]
  have h3 : ∑ n ∈ Finset.range (Module.finrank κ U + 1), g n =
      ∑ n ∈ Finset.range (e + Module.finrank κ U + 1), g n :=
    Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => by
      rw [Finset.mem_range] at hn
      simp only [hg]
      rw [gaussBin_eq_zero q (show m < n by omega), mul_zero]
  rw [hL, hR, h3, ← h2, gaussBin_add hq0 m t e, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  simp only [hg]
  rw [if_pos (by omega), show e + 1 - 1 - n = e - n by omega, show e - (e - n) = n by omega]
  ring

end GlobalTheory.RangeKerCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPhiPrV
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.LevelCharOpen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem redM_eq_one (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hX : ∀ i j, Valued.v (X i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) : redM F v X = 1 := by
  ext i j
  have h1 : (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hd : X i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := (hX i j).le
  have hx : X i j ∈ v.adicCompletionIntegers F := by
    have := add_mem hd h1
    rwa [sub_add_cancel] at this
  have h0 : IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hd⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact (hX i j).ne
  have e : (⟨X i j, hx⟩ : v.adicCompletionIntegers F) = ⟨_, hd⟩ + ⟨_, h1⟩ := Subtype.ext (sub_add_cancel _ _).symm
  simp only [redM, dif_pos hx]
  rw [e, map_add, h0, zero_add]
  by_cases hij : i = j
  · subst hij
    have : (⟨_, h1⟩ : v.adicCompletionIntegers F) = 1 := Subtype.ext (Matrix.one_apply_eq i)
    rw [this, map_one, Matrix.one_apply_eq]
  · have : (⟨_, h1⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (Matrix.one_apply_ne hij)
    rw [this, map_zero, Matrix.one_apply_ne hij]

theorem continuous_phi_prV (G : GLoc F E σ gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal) :
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous ((G.phi a v h).comp (prV (E := E) v)) := by
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := FiniteAdeleRing (𝓞 F) F) _ ?_
  have hv : Continuous (Formalism.UG.evalV F v) := RestrictedProduct.continuous_eval v
  refine hv.congr fun r => ?_
  show _ = (G.sp a v h ((1 : E) ⊗ₜ[F] Formalism.UG.evalV F v r)).1
  rw [G.sp_alg]

theorem isOpen_ker_chi {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp}
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (L : GLevH S G H lam) (hgp : ∀ a, gp a ≠ 0) :
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | ∃ hx : x.1 ∈ S.U, S.chi ⟨x.1, hx⟩ = 1} := by
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
  let K : Subgroup (UPts σ J (FiniteAdeleRing (𝓞 F) F)) := (S.chi.ker.map S.U.subtype).subgroupOf _
  have hK : {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | ∃ hx : x.1 ∈ S.U, S.chi ⟨x.1, hx⟩ = 1} = K := by
    ext x
    constructor
    · rintro ⟨hx, h1⟩
      exact ⟨⟨x.1, hx⟩, h1, rfl⟩
    · rintro ⟨y, hy, e⟩
      have e' : y.1 = x.1 := e
      refine ⟨e' ▸ y.2, ?_⟩
      have : (⟨x.1, e' ▸ y.2⟩ : S.U) = y := Subtype.ext e'.symm
      rw [this]
      exact hy
  rw [hK]
  refine Subgroup.isOpen_of_mem_nhds K (g := 1) ?_
  have hfin : ∀ a, {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal}.Finite := fun a => by
    have h0 : Ideal.span {(gp a : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (hgp a)
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have h1 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, x.1 ∈ S.U := S.U_open.mem_nhds S.U.one_mem
  have h2 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ a : Fin 2, ∀ v ∈ {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal},
      ∀ h : (gp a : 𝓞 F) ∈ v.asIdeal, redM F v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1)) = 1 := by
    refine Filter.eventually_all.2 fun a => (Filter.eventually_all_finite (hfin a)).2 fun v h => ?_
    have hc : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) := by
      have c0 : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => (x.1.val).map ((G.phi a v h).comp (prV (E := E) v)) :=
        (Units.continuous_val.comp continuous_subtype_val).matrix_map (continuous_phi_prV G a v h)
      exact ((continuous_const (y := ((L.fr a v h)⁻¹).val)).matrix_mul c0).matrix_mul (continuous_const (y := (L.fr a v h).val))
    have hone : G.mat a v h (L.fr a v h) (bc (prV (E := E) v) (1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)).1) = 1 := by
      simp [GLoc.mat]
    have h3 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ i j,
        Valued.v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1 := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      have c1 : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) =>
          G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j :=
        (hc.matrix_elem i j).sub continuous_const
      have ho : IsOpen {y : v.adicCompletion F | Valued.v y < 1} := by
        simpa using Valued.isOpen_ball (v.adicCompletion F) 1
      refine (ho.preimage c1).mem_nhds ?_
      rw [Set.mem_preimage, Set.mem_setOf_eq, hone, sub_self, map_zero]
      exact zero_lt_one
    exact h3.mono fun x hx _ => redM_eq_one v _ hx
  filter_upwards [h1, h2] with x hx hr
  refine ⟨⟨x.1, hx⟩, ?_, rfl⟩
  classical
  apply Units.ext
  rw [L.chi_eq, Units.val_one]
  refine Finset.prod_eq_one fun a _ => finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [finprod_eq_dif]
  split_ifs with h
  swap
  · rfl
  have : L.red a v h ⟨x.1, hx⟩ = 1 := Subtype.ext (Units.ext ((L.red_eq a v h ⟨x.1, hx⟩).trans (hr a v h h)))
  rw [this, map_one, Units.val_one, inv_one]

end GlobalTheory.LevelCharOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsColSpaceAutToLocalGLMemOpenDense
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem GlobalTheory.denseGL_completion : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M e y V hV hy
  haveI : T2Space k := by
    rw [t2Space_iff_disjoint_nhds]
    intro a b hab
    have hne : valuation k (a - b) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hab)
    let γ : (ValueGroupWithZero k)ˣ := Units.mk0 _ hne
    rw [Filter.disjoint_iff]
    refine ⟨{z | valuation k (z - a) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩,
      {z | valuation k (z - b) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h := Valuation.map_sub_lt _ (show valuation k (z - b) < γ from hz2)
      (show valuation k (z - a) < γ from hz1)
    have e : (z - b) - (z - a) = a - b := by ring
    rw [e, Units.val_mk0] at h
    exact lt_irrefl _ h
  let φ : Matrix A A k → Matrix A A k × (Matrix A A k)ᵐᵒᵖ := fun m => (m, MulOpposite.op m⁻¹)
  have hφ : ∀ g : GL A k, φ g.val = Units.embedProduct _ g := by
    intro g
    refine Prod.ext rfl ?_
    simp [φ, Matrix.coe_units_inv]
  obtain ⟨W, hW, rfl⟩ := (Units.isInducing_embedProduct (M := Matrix A A k)).isOpen_iff.1 hV
  have hdet : y.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hinv : ContinuousAt (fun m : Matrix A A k => m⁻¹) y.val := by
    have h1 : (fun m : Matrix A A k => m⁻¹) = fun m => (m.det)⁻¹ • m.adjugate := by
      funext m; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    exact ContinuousAt.smul ((continuousAt_inv₀ hdet).comp (continuous_id.matrix_det).continuousAt)
      (continuous_id.matrix_adjugate).continuousAt
  have hφc : ContinuousAt φ y.val :=
    ContinuousAt.prodMk continuousAt_id (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hU : φ ⁻¹' W ∩ {m : Matrix A A k | m.det ≠ 0} ∈ nhds y.val := by
    refine Filter.inter_mem (hφc.preimage_mem_nhds (hW.mem_nhds ?_)) ?_
    · rw [hφ]; exact hy
    · exact (isOpen_compl_singleton.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hD : DenseRange (fun m : Matrix A A E => m.map ι) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
  obtain ⟨_, ⟨m', rfl⟩, hm'W, hm'd⟩ := Dense.inter_nhds_nonempty hD hU
  have hm'u : IsUnit m'.det := by
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply hm'd
    show (m'.map ι).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  let n : Matrix (Fin M) (Fin M) E := m'.submatrix e.symm e.symm
  have hn : IsUnit n.det := by
    simpa [n, Matrix.det_submatrix_equiv_self] using hm'u
  refine ⟨Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn), ?_⟩
  show Units.embedProduct _ _ ∈ W
  rw [← hφ, locHom_val, GlobalTheory.SymBridge.toLoc_eq_map_toMatrix']
  have h2 : LinearMap.toMatrix' (Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn)).toLinearMap = n := by
    exact LinearMap.toMatrix'_toLin' n
  rw [h2]
  have h3 : n.submatrix e e = m' := by
    ext i j; simp [n]
  rw [h3]
  exact hm'W
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhereStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_heckeChar_unramified_everywhere : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  first | exact @GlobalTheory.Corev.UnrPow.exists_pow_unrAt | exact GlobalTheory.Corev.UnrPow.exists_pow_unrAt | (intros; apply GlobalTheory.Corev.UnrPow.exists_pow_unrAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormalGroupHeightLeTwoGoodReductionStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_height_le_two_good_reduction : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (l : ℂ_[l]))‖ = 1 := by
  first | exact @GlobalTheory.HeightTwo.height_le_two | exact GlobalTheory.HeightTwo.height_le_two | (intros; apply GlobalTheory.HeightTwo.height_le_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndex
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenVolIndex

theorem measure_toReal_inv_eq_relIndex : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (H L : Subgroup G), H ≤ L → IsOpen (H : Set G) → IsCompact (L : Set G) → μ (L : Set G) = 1 → (μ (H : Set G)).toReal⁻¹ = (H.relIndex L : ℝ) := by
  intro G _ _ _ _ _ μ _ H L hHL hH hL hμL
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hHo : IsOpen ((H.subgroupOf L : Subgroup L) : Set L) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (L ⧸ H.subgroupOf L) := Subgroup.quotient_finite_of_isOpen _ hHo
  haveI : (H.subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have key := GlobalTheory.BaseModule.relIndex_mul_measure' H L hHL hH.measurableSet μ
  rw [hμL] at key
  have htop : μ (H : Set G) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hμL]; exact ENNReal.one_ne_top) (measure_mono hHL)
  have hr : (H.relIndex L : ℝ) * (μ (H : Set G)).toReal = 1 := by
    have := congrArg ENNReal.toReal key
    simpa [ENNReal.toReal_mul] using this
  exact (eq_inv_of_mul_eq_one_left hr).symm

end GlobalTheory.OpenVolIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicConjInfIntegralGLUnipotent
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.UnipLevelTopo

theorem isOpen_inf_isCompact : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (J : Subgroup (GL (A ⊕ Fin c) k)) (g : GL (A ⊕ Fin c) k), IsOpen (J : Set (GL (A ⊕ Fin c) k)) → IsCompact (J : Set (GL (A ⊕ Fin c) k)) → IsOpen ((((Cgrp J g).subgroupOf (N k A c 1)) ⊓ ((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1)) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) := by
  intro k _ _ _ _ A _ _ c J g hJo hJc
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj g hJo hJc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : N k A c 1 → GL (A ⊕ Fin c) k) :=
    (GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := A) (c := c) 1).isClosedEmbedding_subtypeVal
  have eC : (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL (A ⊕ Fin c) k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage, Cgrp, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_sup_right x.2, h⟩⟩
  have eK : (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (KO k (A ⊕ Fin c) : Set (GL (A ⊕ Fin c) k)) := by
    ext x; simp [Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf, eC, eK]
    exact (h1.inter GlobalTheory.SplitFlip.isOpen_KO).preimage continuous_subtype_val
  · rw [eC]; exact hemb.isCompact_preimage h2
  · rw [eK]; exact hemb.isCompact_preimage GlobalTheory.SplitFlip.isCompact_KO

end GlobalTheory.UnipLevelTopo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGL
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenPr

theorem continuous_embX {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {A : Type} [Fintype A] [DecidableEq A] (c : ℕ) :
    Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GL A k => (fromBlocks (x : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_val).matrix_fromBlocks continuous_const continuous_const continuous_const
  · change Continuous fun x : GL A k => (fromBlocks ((x⁻¹ : GL A k) : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_coe_inv).matrix_fromBlocks continuous_const continuous_const continuous_const

theorem isOpen_prX : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (1 : GL (A ⊕ Fin c) k) ∈ O → (∀ z ∈ R k A c 1, z ∈ O → z ∈ Ck) → IsOpen (prX Ck : Set (GL A k)) := by
  intro k _ _ _ _ A _ _ c Ck O hO h1 hCk
  have hc : Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := continuous_embX c
  have hU : IsOpen ((embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O) := hO.preimage hc
  have h1U : (1 : GL A k) ∈ (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O := by
    simp only [Set.mem_preimage, map_one]; exact h1
  have hsub : (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O ⊆ (prX Ck : Set (GL A k)) := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul]
    exact hCk _ (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨x, rfl⟩)) hx
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1U) hsub)

end GlobalTheory.OpenPr
end

