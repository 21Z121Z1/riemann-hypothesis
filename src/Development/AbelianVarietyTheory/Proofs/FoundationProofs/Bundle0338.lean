import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylConjugateOfUnitarySatakeDiagDoubleCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0320
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryIwasawaCellBoundSmallTorusDoubleCoset

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun.Orbit
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (WeylConjU bcParam bcParam_of_weylConj)

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ ϖ' : L}

theorem exists_dosetInd_eq (hU : IsUnramInv ϖ σ q) (hU' : IsUnramInv ϖ' σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    ∃ t' : GU σ n, t'.1.1 = Matrix.diagonal (fun i => ϖ' ^ d i) ∧ dosetInd ℂ (KU σ n) t' = dosetInd ℂ (KU σ n) t := by
  have h0 := GlobalTheory.InertThetaCompare.unif_ne_zero hU
  have h0' := GlobalTheory.InertThetaCompare.unif_ne_zero hU'
  have hv : ∀ a : ℤ, Valued.v (ϖ ^ a) = WithZero.exp (-a) := fun a => by
    simpa using GlobalTheory.InertThetaCompare.val_prod_zpow (ϖ := ϖ) hU.2.2.2.1 (Finset.univ : Finset Unit) fun _ => a
  have hd : ∀ i, d i + d i.rev = 0 := fun i => by
    have h1 := P.fSatake_unit_diag (P.fSatake_borel_of_diag ht) i
    rw [ht, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, hU.2.2.1, ← zpow_add₀ h0] at h1
    have h2 := hv (d i + d i.rev)
    rw [h1, map_one, eq_comm, WithZero.exp_eq_one] at h2
    omega
  obtain ⟨k, hk, hk'⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => (ϖ' / ϖ) ^ d i) fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.1, hU'.2.2.1, ← zpow_add₀ (div_ne_zero h0' h0), hd, zpow_zero]
  have hK : k ∈ KU σ n := P.fSatake_diag_mem_K hk hk' fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.2.1, hU'.2.2.2.1, div_self WithZero.coe_ne_zero, one_zpow]
  refine ⟨t * k, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, ht, hk, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← mul_zpow, mul_div_cancel₀ _ h0]
  · rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem
      (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k, hK, by rw [one_mul]⟩)]

variable [CompleteSpace L] {V : Type} [AddCommGroup V] [Module ℂ V] {α β : Fin (n / 2) → ℂˣ}

theorem satU_of_weylConj (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) (e : WeylConjU α β) :
    SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h (fun i => (β i : ℂ)) :=
  unitarySatakeTransform_weylConjugate_invariant GlobalTheory.T.unitarySatake_weylInvariant hU hh e

theorem weylConj_of_dosetInd (hU : IsUnramInv ϖ σ q)
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) = SatU ϖ q (dosetInd ℂ (KU σ n) t) fun i => (β i : ℂ)) :
    WeylConjU α β := weylConjugate_of_unitarySatake_diagDoubleCosets GlobalTheory.T.unitarySatake_weylInvariant hU h

theorem satU_eq_iff_weylConj (hU : IsUnramInv ϖ σ q) :
    (∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) ↔ WeylConjU α β :=
  ⟨fun h => weylConj_of_dosetInd hU fun _ _ _ _ => h _ (Final.DosetIndMem _ _ _ _),
    fun e _ hh => satU_of_weylConj hU hh e⟩

theorem bcParam_eq_of_satU_eq (hU : IsUnramInv ϖ σ q)
    (h : ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) :
    bcParam n α = bcParam n β := bcParam_of_weylConj ((satU_eq_iff_weylConj hU).1 h)

variable {ρ : Representation ℂ (GU σ n) V} {x : V}

theorem IsSatVecU.unique (hU : IsUnramInv ϖ σ q) (h : IsSatVecU ϖ q ρ x α) (h' : IsSatVecU ϖ q ρ x β) :
    WeylConjU α β :=
  (satU_eq_iff_weylConj hU).1 fun t ht => smul_left_injective ℂ h.1 ((h.2.2 t ht).symm.trans (h'.2.2 t ht))

theorem HasSatU.unique (hU : IsUnramInv ϖ σ q) (h : HasSatU ϖ q ρ α) (h' : HasSatU ϖ q ρ β) : WeylConjU α β := by
  obtain ⟨x, hx⟩ := h.exists_vec
  exact hx.unique hU (h'.2 x hx.2.1 hx.1)

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Place

variable {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun y => by
  obtain ⟨a, ha⟩ := (finAdEquiv F E).surjective (Neutral.B1.finiteSingle E w y)
  refine ⟨_, (finAdEquiv_apply h a).symm.trans ?_⟩
  rw [ha]
  classical exact Pi.mulSingle_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w y

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {V : Type} [AddCommGroup V] [Module ℂ V] {h : w.under (𝓞 F) = v}

theorem IsConjAt.unique {c c' : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
    (hc' : IsConjAt σ h c') : c = c' := RingHom.ext fun y => by
  obtain ⟨z, rfl⟩ := toCompl_surjective h y
  rw [hc, hc']

variable {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {B B' : Multiset ℂˣ}

theorem IsParamVec.unique (hx : IsParamVec σ J L h ρ x B) (hx' : IsParamVec σ J L h ρ x B') : B = B' := by
  by_cases hv : IsSplit (E := E) v
  · exact hx.unique_of_isSplit hv hx'
  obtain ⟨-, c, ϖ, e, α, hU, he, hα, rfl⟩ := hx.resolve_left fun h => hv h.1
  obtain ⟨-, c', ϖ', e', β, hU', he', hβ, rfl⟩ := hx'.resolve_left fun h => hv h.1
  obtain rfl := he.1.unique he'.1
  exact bcParam_of_weylConj (((hα.of_chart he he').of_unif hU hU').unique hU' hβ)

theorem HasParam.unique (hρ : HasParam σ J L h ρ B) (hρ' : HasParam σ J L h ρ B') : B = B' := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact hx.unique (hρ'.isParamVec hx.mem_fixed hx.ne_zero)

theorem IsSysParam.unique {c : List ℤ → ℂ} (hc : IsSysParam σ n h c B) (hc' : IsSysParam σ n h c B') : B = B' := by
  rcases hc with ⟨hv, hB, hc⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, hc⟩ <;>
    rcases hc' with ⟨hv', hB', hc'⟩ | ⟨hw', τ', ϖ', β, hU', hτ', rfl, hc'⟩
  · exact eq_of_satEig_eq (qV_ne_zero w) hB hB' fun j hj => (hc j hj).symm.trans (hc' j hj)
  · exact absurd hv (not_isSplit_of_isInertAt hw')
  · exact absurd hv' (not_isSplit_of_isInertAt hw)
  · obtain rfl := hτ.unique hτ'
    refine bcParam_of_weylConj (weylConj_of_dosetInd hU fun d t hd ht => ?_)
    obtain ⟨t', ht', e⟩ := exists_dosetInd_eq hU hU' ht
    rw [← hc d t hd ht, hc' d t' hd ht', e, satU_indep hU hU' (Final.DosetIndMem _ _ _ _)]

end Place

section Global

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {S : Set (HeightOneSpectrum (𝓞 F))} {V : Type} [AddCommGroup V] [Module ℂ V]
  {Vl : HeightOneSpectrum (𝓞 F) → Type} [∀ v, AddCommGroup (Vl v)] [∀ v, Module ℂ (Vl v)]
  {π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)} {c c' : Fam E} {w : HeightOneSpectrum (𝓞 E)}

theorem HasParamOff.unique (h : HasParamOff σ J L S π c) (h' : HasParamOff σ J L S π c') (hw : w ∉ above E S) :
    c w = c' w := (h _ hw w rfl).unique (h' _ hw w rfl)

theorem IsParamVecOff.unique {ρ : Representation ℂ (GAd σ J) V} {x : V} (h : IsParamVecOff σ J L S ρ x c)
    (h' : IsParamVecOff σ J L S ρ x c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem IsSysParamOff.unique {s : HeightOneSpectrum (𝓞 E) → List ℤ → ℂ} (h : IsSysParamOff σ n S s c)
    (h' : IsSysParamOff σ n S s c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem LSTw_congr (h : ∀ w ∉ above E S, c w = c' w) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (s : ℂ) :
    LSTw S c m s = LSTw S c' m s := eulerProd_congr (fun w hw => by rw [twist, twist, h w hw]) s

end Global

end GlobalTheory.LFun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitaryStatement
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_elementaryDivisors_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ d : List ℤ, GlobalTheory.InertThetaCompare.Good n d ∧ ∃ a ∈ GLint (Fin n) (intL L), ∃ b ∈ GLint (Fin n) (intL L), ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * (b : Matrix (Fin n) (Fin n) L) := by
  first | exact @GlobalTheory.LFun.UnitaryDiv.exists_good_div | exact GlobalTheory.LFun.UnitaryDiv.exists_good_div | (intros; apply GlobalTheory.LFun.UnitaryDiv.exists_good_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddEqOfEven
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatEqui

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem exists_root (D : D7) (u : D.host.E) (hu : u * D.host.conj u = 1) :
    ∃ b : D.host.Eˣ, (b : D.host.E) = u * D.host.conj b := by
  by_cases h : 1 + u = 0
  · have hs : D.host.sqrtMinusD ≠ 0 := by
      intro h0
      have := D.host.sqrtMinusD_sq
      rw [h0] at this
      have hd : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 D.host.hyp.2.1.ne_zero
      exact hd (by linear_combination this)
    refine ⟨Units.mk0 _ hs, ?_⟩
    rw [Units.val_mk0, D.host.conj_sqrtMinusD]
    linear_combination D.host.sqrtMinusD * h
  · refine ⟨Units.mk0 _ h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination -hu

theorem char_value {D : D7} {N : ℕ} (χ : HeckeU D N) (ep : ℤ) (u : D.host.E) (b : D.host.Eˣ)
    (hb : (b : D.host.E) = u * D.host.conj b) (k : D.what₂.Tau → ℤ) (hk : ∀ τ, 2 * k τ = ep * χ.n τ) :
    ((χ.f (Units.map (inc D).toMonoidHom b) ^ ep : ℂˣ) : ℂ) = ∏ τ, embT D τ u ^ (-(k τ)) := by
  rw [Units.val_zpow_eq_zpow_val, eq_inv_of_mul_eq_one_left (χ.aut b), inv_zpow, ← Finset.prod_zpow,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm, ← hk, zpow_mul, zpow_neg]
  congr 2
  have h0 : embT D τ b ≠ 0 := (map_ne_zero _).2 b.ne_zero
  have h1 := congrArg (embT D τ) hb
  rw [map_mul, embT_conj] at h1
  have h2 : (starRingEnd ℂ) (embT D τ b) ≠ 0 := (map_ne_zero _).2 h0
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', pow_two, mul_div_mul_left _ _ h0, div_eq_iff h2]
  exact h1

theorem det_norm {D : D7} {n : ℕ} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : γ * (γ.map D.host.conj).transpose = 1) : γ.det * D.host.conj γ.det = 1 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [← this]
  congr 1
  exact RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ

theorem det_root {D : D7} {n : ℕ} {g : GL (Fin n) (AE D)} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : IsRat D g γ) (b : D.host.Eˣ) (hb : (b : D.host.E) = γ.det * D.host.conj b) :
    Units.map (inc D).toMonoidHom b =
      Matrix.GeneralLinearGroup.det g * sgU D (Units.map (inc D).toMonoidHom b) := by
  ext
  change inc D b = (g : Matrix (Fin n) (Fin n) (AE D)).det * sgA D (inc D b)
  rw [GlobalTheory.NormSum.PtsMem.sgA_inc, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_mul, ← hb]

theorem isRat_one (D : D7) (n : ℕ) : IsRat D ((1 : GA D n) : GL (Fin n) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem moves_one (D : D7) (n : ℕ) : Moves D ((1 : GA D n) : GL (Fin n) (AE D)) (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
  exact h2 ▸ (h1 1).1

theorem exists_factor {D : D7} {n : ℕ} (g : GA D n) (γ : Matrix (Fin n) (Fin n) D.host.E)
    (h : IsRat D (g : GL (Fin n) (AE D)) γ) :
    ∃ (g₁ g₂ : GA D n) (γ₁ γ₂ : Matrix (Fin n) (Fin n) D.host.E), IsRat D (g₁ : GL (Fin n) (AE D)) γ₁ ∧
      IsRat D (g₂ : GL (Fin n) (AE D)) γ₂ ∧ g = g₁ * g₂ ∧ γ = γ₁ * γ₂ ∧ (1 - γ₁).det ≠ 0 ∧ (1 - γ₂).det ≠ 0 := by
  obtain ⟨-, -, hex, hun, -⟩ := GlobalTheory.NormSum.mem_ratG_intG D n
  obtain ⟨z, hz, hz1, hdet⟩ := GlobalTheory.T.exists_normOne_scalar_avoiding_matrix_eigenvalues D n γ
  have hγ := hun g γ h
  obtain ⟨g₁, hg₁⟩ := hex (z • γ) (by
    have : (z • γ).map D.host.conj = D.host.conj z • γ.map D.host.conj := by
      ext i j; simp
    rw [this, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hγ, smul_smul, hz, one_smul])
  obtain ⟨g₂, hg₂⟩ := hex (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) (by
    have : (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)).map D.host.conj = z • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, conj_conj]
    rw [this, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_one, Matrix.mul_one,
      smul_smul, mul_comm, hz, one_smul])
  have e : γ = (z • γ) * (D.host.conj z • (1 : Matrix (Fin n) (Fin n) D.host.E)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hz, one_smul]
  refine ⟨g₁, g₂, _, _, hg₁, hg₂, ?_, e, hdet, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    unfold IsRat at h hg₁ hg₂
    rw [Subgroup.coe_mul, Units.val_mul, h, hg₁, hg₂, ← Matrix.map_mul, ← e]
  · rw [show (1 : Matrix (Fin n) (Fin n) D.host.E) - D.host.conj z • 1 = (1 - D.host.conj z) • 1 by
      rw [sub_smul, one_smul], Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ (sub_ne_zero.2 fun h1 => hz1 ?_)
    rw [← conj_conj D z, ← h1, map_one]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ}

def IsPull (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (a : ℂ) : Prop :=
  ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om g g' F = fun z => a * pull D (tor0 D cc δ) γ γ' F z

theorem IsPull.mul {W : WeilO D cc δ N N' e0} {g₁ g₂ : GA D N} {g₁' g₂' : GA D N'}
    {γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E} {γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E} {a₁ a₂ : ℂ}
    (h₁ : IsPull W g₁ g₁' γ₁ γ₁' a₁) (h₂ : IsPull W g₂ g₂' γ₂ γ₂' a₂) :
    IsPull W (g₁ * g₂) (g₁' * g₂') (γ₁ * γ₂) (γ₁' * γ₂') (a₁ * a₂) := by
  intro F hF
  rw [W.mul _ _ _ _ F hF, h₁ _ (W.maps _ _ F hF), h₂ F hF]
  funext z
  simp only [pull_eq, mulV_mulV, adj_mul, mul_assoc]

theorem isPull_row (hc : Crv D cc δ) (hN : Even N) (hN' : Even N')
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) (a : D.what₂.Tau → ℤ)
    (ha : ∀ τ, 2 * a τ = W.ep' * W.chV'.n τ - (N' : ℤ)) (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (h : IsRat D (g : GL (Fin N) (AE D)) γ) : IsPull W g 1 γ 1 (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
  have key : ∀ (g : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E), IsRat D (g : GL (Fin N) (AE D)) γ →
      (1 - γ).det ≠ 0 → IsPull W g 1 γ 1 (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
    intro g γ h hdet
    obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    have hu := det_norm ((GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 g γ h)
    obtain ⟨b, hb⟩ := exists_root D _ hu
    refine GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum D cc δ hc N N' e0 he (GlobalTheory.T.theta_span_rational_translates_vacuum D cc δ hc N N' e0 he W.nz) W g 1 γ 1 _ h
      (isRat_one D N') ?_
    rw [GlobalTheory.T.weilOperator_vacuum_exact_constant_evenRank D cc δ hc N N' hN hN' e0 he W g 1 _ 1 (Lt g) (stdL D N') (det_root h b hb) (by simp)
      (hLt g).1 (moves_one D N'), GlobalTheory.T.thetaPullback_firstGroup_rationalPoint_eq_smul D cc δ hc N N' hN hN' e0 he g γ (Lt g) h hdet (hLt g).1]
    funext z
    rw [map_one, one_zpow, one_mul, char_value W.chV' W.ep' γ.det b hb (fun τ => a τ + ((N' / 2 : ℕ) : ℤ))
      (fun τ => by have := ha τ; obtain ⟨k, hk⟩ := hN'; omega), Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [neg_add, zpow_add₀ ((map_ne_zero _).2 (left_ne_zero_of_mul_eq_one hu))]
  obtain ⟨g₁, g₂, γ₁, γ₂, h₁, h₂, rfl, rfl, d₁, d₂⟩ := exists_factor g γ h
  have := (key g₁ γ₁ h₁ d₁).mul (key g₂ γ₂ h₂ d₂)
  simpa only [mul_one, ← Finset.prod_mul_distrib, ← mul_zpow, ← map_mul, ← Matrix.det_mul] using this

theorem isPull_col (hc : Crv D cc δ) (hN : Even N) (hN' : Even N')
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) (a : D.what₂.Tau → ℤ)
    (ha : ∀ τ, 2 * a τ = W.ep * W.chV.n τ + (N : ℤ)) (g : GA D N') (γ : Matrix (Fin N') (Fin N') D.host.E)
    (h : IsRat D (g : GL (Fin N') (AE D)) γ) : IsPull W 1 g 1 γ (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
  have key : ∀ (g : GA D N') (γ : Matrix (Fin N') (Fin N') D.host.E), IsRat D (g : GL (Fin N') (AE D)) γ →
      (1 - γ).det ≠ 0 → IsPull W 1 g 1 γ (∏ τ, embT D τ γ.det ^ (-(a τ))) := by
    intro g γ h hdet
    obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N'
    have hu := det_norm ((GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 g γ h)
    obtain ⟨b, hb⟩ := exists_root D _ hu
    refine GlobalTheory.T.om_eq_mul_pull_of_om_eq_on_vacuum D cc δ hc N N' e0 he (GlobalTheory.T.theta_span_rational_translates_vacuum D cc δ hc N N' e0 he W.nz) W 1 g 1 γ _
      (isRat_one D N) h ?_
    rw [GlobalTheory.T.weilOperator_vacuum_exact_constant_evenRank D cc δ hc N N' hN hN' e0 he W 1 g 1 _ (stdL D N) (Lt g) (by simp) (det_root h b hb)
      (moves_one D N) (hLt g).1, GlobalTheory.T.thetaPullback_secondGroup_rationalPoint_eq_det_smul D cc δ hc N N' hN hN' e0 he g γ (Lt g) h hdet (hLt g).1]
    funext z
    rw [map_one, one_zpow, mul_one, char_value W.chV W.ep γ.det b hb (fun τ => a τ - ((N / 2 : ℕ) : ℤ))
      (fun τ => by have := ha τ; obtain ⟨k, hk⟩ := hN; omega), Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [neg_sub', sub_neg_eq_add, zpow_add₀ ((map_ne_zero _).2 (left_ne_zero_of_mul_eq_one hu)), zpow_natCast]
  obtain ⟨g₁, g₂, γ₁, γ₂, h₁, h₂, rfl, rfl, d₁, d₂⟩ := exists_factor g γ h
  have := (key g₁ γ₁ h₁ d₁).mul (key g₂ γ₂ h₂ d₂)
  simpa only [mul_one, ← Finset.prod_mul_distrib, ← mul_zpow, ← map_mul, ← Matrix.det_mul] using this

theorem oddEq_of_even : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ N N' : ℕ, Even N → Even N' → ∀ e0 : VC D N N' → ℂ, oddE0 D cc δ t0 N N' e0 → oddEq D cc δ N N' e0 := by
  intro D cc δ hc t0 _ N N' hN hN' e0 he W γA γA' γ γ' a a' h h' ha' ha
  have := (isPull_row hc hN hN' he.1 W a ha γA γ h).mul (isPull_col hc hN hN' he.1 W a' ha' γA' γ' h')
  rw [mul_one, one_mul, mul_one, one_mul, ← Finset.prod_mul_distrib] at this
  exact this

end GlobalTheory.RatEqui
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupSmoothCharacterStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_smoothCharacterDatum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  first | exact @GlobalTheory.PsType.grp_theta_datum | exact GlobalTheory.PsType.grp_theta_datum | (intros; apply GlobalTheory.PsType.grp_theta_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCosetStatement
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | exact GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | (intros; apply GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryIwasawaCellBoundSmallTorusDoubleCosetStatement
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIwasawaCell_bound_small_torusDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (ε κ : Fin (n / 2) → ℤ) (u k k₁ k₂ : GU σ n), (∀ i, |ε i| ≤ 1) → IsUnipU u → k ∈ KU σ n → k₁ ∈ KU σ n → k₂ ∈ KU σ n → tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * tMat ϖ n (n / 2) ε * ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i| := by
  first | exact @GlobalTheory.LFun.CellBound.cell_bound | exact GlobalTheory.LFun.CellBound.cell_bound | (intros; apply GlobalTheory.LFun.CellBound.cell_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitarySatakeTransformIsLaurentPolynomialStatement
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  first | exact @GlobalTheory.LFun.SatCoef.satU_laurent | exact GlobalTheory.LFun.SatCoef.satU_laurent | (intros; apply GlobalTheory.LFun.SatCoef.satU_laurent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairUnitModulusFactorStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_under_adelic_pair_unit_modulus_factor : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even (N * N') → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∃ c : ℂ, Mod1All c ∧ (W.Om g g' e0 = fun z => c * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D N'), k' ∈ intG D N' → TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p ((g' * k' : GA D N') : GL (Fin N') (AE D)) → ‖lamC lam c‖ = 1 := by
  first | exact @GlobalTheory.ArchFree.weilc.vacuum_under_adelic_pair | exact GlobalTheory.ArchFree.weilc.vacuum_under_adelic_pair | (intros; apply GlobalTheory.ArchFree.weilc.vacuum_under_adelic_pair <;> assumption)
end

