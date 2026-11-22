import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1693

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEisensteinRatioAlgebraicUnit
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.VacUnit

open Formalism.MainNotions.TaylorLogMetric (hYY LocBasis YYl)
open Formalism.MainNotions.StandardLatticesGL3 (OnB LaB pullB KLat)

theorem mem_Qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at h ⊢
  exact h.of_pow hn

theorem norm_int_le {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p]) (c : 𝓞 K) :
    ‖f (c : K)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | (apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one ..)

theorem norm_nat_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

theorem norm_det_le {p : ℕ} [Fact p.Prime] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ_[p]) (h : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _

variable {D : D7} {N N' r : ℕ}

theorem hYY_comb (c : Fin r → D.host.K) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (∑ k, c k • b k) y = ∑ k, c k * hYY D (b k) y := by
  simp only [hYY, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.smul_sum, smul_eq_mul, Finset.sum_mul, smul_mul_assoc]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

theorem exists_coord {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') (j : Fin r) :
    ∃ a : Fin r → D.host.K, (∀ i, ‖f (a i)‖ ≤ 1) ∧ b' j = ∑ i, a i • b i := by
  obtain ⟨s, hs, hY⟩ := hl'.2.1 j
  obtain ⟨t, ht, c, hc⟩ := hl.2.2 _ hY
  have hst : Nat.Coprime (t * s) p := Nat.Coprime.mul_left ht hs
  have h0 : ((t * s : ℕ) : D.host.K) ≠ 0 := by
    intro h
    have h1 := norm_nat_coprime hst
    rw [← map_natCast f, h] at h1
    simp at h1
  refine ⟨fun i => ((t * s : ℕ) : D.host.K)⁻¹ * (c i : D.host.K), fun i => ?_, ?_⟩
  · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, norm_nat_coprime hst, inv_one, one_mul]
    exact norm_int_le f _
  · have h2 : ((t * s : ℕ) : D.host.K) • b' j = ∑ i, (c i : D.host.K) • b i := by
      rw [smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul] at hc
      rw [Nat.cast_smul_eq_nsmul, hc]
      rfl
    simp only [mul_smul]
    rw [← Finset.smul_sum, ← h2, smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem norm_det_eq_one {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b)
    (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') :
    ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ = 1 := by
  choose a ha hab using exists_coord f hl hl'
  choose a' ha' hab' using exists_coord f hl' hl
  have hM : ∀ i j, hYY D (b' j) (b i) = a j i := by
    intro i j
    rw [hab j, hYY_comb]
    simp [hb.1 _ i]
  have hMM : (Matrix.of fun i j => hYY D (b' j) (b i)) * (Matrix.of fun j k => a' k j) = 1 := by
    ext i k
    have h1 := hb.1 k i
    conv_lhs at h1 => rw [hab' k, hYY_comb]
    rw [Matrix.mul_apply, Matrix.one_apply, if_congr (eq_comm (a := i)) rfl rfl, ← h1]
    simp [mul_comm]
  have hd := congrArg (fun A => ‖f (Matrix.det A)‖) hMM
  simp only [Matrix.det_mul, map_mul, norm_mul, Matrix.det_one, map_one, norm_one] at hd
  have h1 : ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa [hM] using ha j i
  have h2 : ‖f (Matrix.of fun j k => a' k j).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa using ha' j i
  refine le_antisymm h1 ?_
  rw [← hd]
  exact mul_le_of_le_one_right (norm_nonneg _) h2

noncomputable def phiK (D : D7) : D.host.K →+* Qbar :=
  (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring fun x => by
    change _ ∈ Qbar
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toRatAlgHom

theorem at_place (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} (hC : Crv D ⊤ δ) (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0)
    {e₁ e₂ : VC D N N' → ℂ} (h₁ : oddE0 D ⊤ δ t0 N N' e₁) (h₂ : oddE0 D ⊤ δ t0 N N' e₂) (hne : e₁ ≠ 0) {κ : ℂ}
    (hκ : e₂ = κ • e₁) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 := by
  have hSD : ∀ n, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h2 ▸ (h1 1).2
  obtain ⟨b, ε, hb, hl, hε, hεn, -, he⟩ := h₁.2.2.2.2 p lam (by simp)
  obtain ⟨b', ε', hb', hl', hε', hεn', -, he'⟩ := h₂.2.2.2.2 p lam (by simp)
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht N N' _ b b' hb hb'
  obtain ⟨μ, hμ, hI3⟩ := hI.mu ⊤ δ hC N N' _ _ (La0 D (tor0 D ⊤ δ) N N') (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inl ⟨_, b', hb', rfl⟩) (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩) _
    (GlobalTheory.UnitaryTheta.pullB_mem D ⊤ δ hC t0 ht N N' _ b hb).1
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have e2 := congrFun hκ z
  rw [he', hpull, Pi.smul_apply, smul_eq_mul] at e2
  rw [he] at e2 hz
  simp only [GlobalTheory.UnitaryTheta.iop_smul, hI3] at e2
  have hz' := right_ne_zero_of_mul hz
  have key : κ * ε = ε' * c * μ := by
    apply mul_right_cancel₀ hz'
    linear_combination -e2
  have hζQ : ζ ∈ Qbar := mem_Qbar_of_pow hm (hζ ▸ one_mem _)
  have hμQ : μ ∈ Qbar := mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)
  set u := phiK D (Matrix.of fun i j => hYY D (b' j) (b i)).det with hu
  have hun : ‖lam u‖ = 1 := norm_det_eq_one (lam.comp (phiK D)) hb hl hl'
  change c ^ 2 = ζ * (u : ℂ) at hc
  have hcQ : c ∈ Qbar := mem_Qbar_of_pow (n := 2) (by norm_num) (hc ▸ mul_mem hζQ u.2)
  rw [lamC, dif_pos hε] at hεn
  rw [lamC, dif_pos hε'] at hεn'
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul hz
  have hκQ : κ ∈ Qbar := by
    rw [eq_div_of_mul_eq hε0 key]
    exact div_mem (mul_mem (mul_mem hε' hcQ) hμQ) hε
  refine ⟨hκQ, ?_⟩
  rw [lamC, dif_pos hκQ]
  have root : ∀ (x : Qbar) (n : ℕ), 0 < n → (x : ℂ) ^ n = 1 → ‖lam x‖ = 1 := by
    intro x n hn hx
    have : x ^ n = 1 := Subtype.ext (by simpa using hx)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  have hcn : ‖lam ⟨c, hcQ⟩‖ = 1 := by
    have : (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u := Subtype.ext (by simpa using hc)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_mul, norm_mul, hun, root ⟨ζ, hζQ⟩ m hm hζ, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  have : (⟨κ, hκQ⟩ : Qbar) * ⟨ε, hε⟩ = ⟨ε', hε'⟩ * ⟨c, hcQ⟩ * ⟨μ, hμQ⟩ := Subtype.ext key
  have h := congrArg (fun y => ‖lam y‖) this
  simpa only [map_mul, norm_mul, hεn, hεn', hcn, root ⟨μ, hμQ⟩ 8 (by norm_num) hμ, mul_one] using h

theorem vac_unit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ},
  oddE0 D ⊤ δ t0 N N' e₁ → oddE0 D ⊤ δ t0 N N' e₂ → e₁ ≠ 0 → ∀ κ : ℂ, e₂ = κ • e₁ →
  κ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam κ‖ = 1 := by
  intro D hI δ t0 hC ht N N' e₁ e₂ h₁ h₂ hne κ hκ
  refine ⟨?_, fun p _ lam => (at_place hI hC ht h₁ h₂ hne hκ p lam).2⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  exact (at_place hI hC ht h₁ h₂ hne hκ 2 (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom).1

end GlobalTheory.VacUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder Matrix

namespace GlobalTheory.OneParamOrbit

theorem eps_true_of_posDef {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) (i : Fin X.rank) : B.ε τ i = true := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hinj : Function.Injective ((B.fr τ)⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_nonsing_inv_iff).mpr (B.fr_unit τ))
  have hJ : ((B.fr τ)⁻¹)ᴴ * gramAt D X τ * (B.fr τ)⁻¹ = Formalism.REAL.Jm (B.ε τ) := by
    rw [← B.fr_gram τ]
    have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B.fr τ)⁻¹)ᴴ * ((B.fr τ)ᴴ * Formalism.REAL.Jm (B.ε τ) * B.fr τ) * (B.fr τ)⁻¹
        = (((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ) * Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (B.ε τ) := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hpos := (hG.conjTranspose_mul_mul_same hinj).diag_pos (i := i)
  rw [hJ] at hpos
  by_contra hne
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply_eq, hne] at hpos
  norm_num at hpos

theorem conj_mem_Kset {D : D7} {X : HSp D} (B : GlobalTheory.ChainFr.Fr X) (τ : D.what₂.Tau)
    (hG : (gramAt D X τ).PosDef) {E : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hE : Eᴴ * gramAt D X τ * E = gramAt D X τ) :
    B.fr τ * E * (B.fr τ)⁻¹ ∈ Formalism.REAL.Kset (B.ε τ) := by
  have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
  have hJ1 : Formalism.REAL.Jm (B.ε τ) = 1 := by
    have : B.ε τ = fun _ => true := funext (eps_true_of_posDef B τ hG)
    rw [this]; simp [Formalism.REAL.Jm]
  have hgram : (B.fr τ)ᴴ * B.fr τ = gramAt D X τ := by
    rw [← B.fr_gram τ, hJ1, Matrix.mul_one]
  refine ⟨?_, by rw [hJ1, Matrix.mul_one, Matrix.one_mul]⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have h1 : ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
  calc (B.fr τ * E * (B.fr τ)⁻¹)ᴴ * (B.fr τ * E * (B.fr τ)⁻¹)
      = ((B.fr τ)⁻¹)ᴴ * (Eᴴ * ((B.fr τ)ᴴ * B.fr τ) * E) * (B.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ((B.fr τ)⁻¹)ᴴ * (B.fr τ)ᴴ * (B.fr τ * (B.fr τ)⁻¹) := by
        rw [hgram, hE, ← hgram]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem orbit_finiteDimensional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep M X),
    GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω → (∀ τ, ∃ a b : ℚ, HasInfExp D χ τ a ∧ HasInfExp D χ' τ b) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D X τ) X.rank 0) →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ algF ψ θ false A B,
      ∃ V : Submodule ℂ (WO M X → ℂ), FiniteDimensional ℂ V ∧ ∀ t : ℝ, ω (1, oneP θ X τ Y t) Φ ∈ V := by
  intro D ψ θ _hψ hθ M X A B χ χ' ω hω hexp hsig τ Y hY Φ hΦ
  have hG : (gramAt D X τ).PosDef := GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hsig τ)
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    by_cases hf0 : f = 0
    · subst hf0
      have h0 : fockF ψ θ false A B 0 P = 0 := by
        have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ (GlobalTheory.Grid.sgn false M) X (frSgn false A).cart B.cart
          A.onb B.onb 0 0 P
        rwa [zero_smul, zero_smul] at this
      refine ⟨⊥, inferInstance, fun t => ?_⟩
      rw [h0, map_zero]; exact zero_mem _
    · obtain ⟨a, b, ha, hb⟩ := hexp τ
      obtain ⟨x, y, -, -, hK⟩ := GlobalTheory.CompactFockAction.compactFockAll D (GlobalTheory.Grid.sgn false M) X
        (frSgn false A) B θ ψ χ χ' (ω.toSgn false) f τ a b hθ hω ha hb hf hf0
      refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (fockF ψ θ false A B f),
        inferInstance, fun t => ?_⟩
      have hu : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (B.fr_unit τ)
      have hE : (NormedSpace.exp (t • Y))ᴴ * gramAt D X τ * NormedSpace.exp (t • Y) = gramAt D X τ :=
        GlobalTheory.SmoothAutCheck.exp_mem_UH (Matrix.isUnit_iff_isUnit_det _ |>.mp hG.isUnit) hY t
      have hk := conj_mem_Kset B τ hG hE
      have hA1 : (frSgn false A).elt θ τ 1 = 1 := by
        have hAu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.fr_unit τ)
        show atTau θ _ τ ((A.fr τ)⁻¹ * 1 * A.fr τ) = 1
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hAu]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ _ τ
      have hBk : B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) = oneP θ X τ Y t := by
        show atTau θ X τ ((B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ) = _
        rw [show (B.fr τ)⁻¹ * (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹) * B.fr τ
            = ((B.fr τ)⁻¹ * B.fr τ) * NormedSpace.exp (t • Y) * ((B.fr τ)⁻¹ * B.fr τ) by
              simp only [Matrix.mul_assoc],
          Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]
        rfl
      have hω1 : ω (1, oneP θ X τ Y t)
          = (ω.toSgn false) ((frSgn false A).elt θ τ 1, B.elt θ τ (B.fr τ * NormedSpace.exp (t • Y) * (B.fr τ)⁻¹)) := by
        rw [hA1, hBk]
        show ω (1, _) = ω ((GlobalTheory.Grid.ofSgn false M) 1, _)
        rw [map_one]
      have key := hK 1 (GlobalTheory.Chain.RealIt.one_mem_Kset _) _ hk P
      have hfock : fockF ψ θ false A B f P = GlobalTheory.ChainFr.ptF ψ θ (frSgn false A) B f P := rfl
      rw [hfock, hω1, key]
      refine Submodule.smul_mem _ _ ⟨_, (MvPolynomial.mem_restrictTotalDegree _ _ _).2
        (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _), rfl⟩
  | zero => exact ⟨⊥, inferInstance, fun t => by rw [map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨V₁, h₁, hV₁⟩ := hx
    obtain ⟨V₂, h₂, hV₂⟩ := hy
    exact ⟨V₁ ⊔ V₂, Submodule.finiteDimensional_sup V₁ V₂, fun t => by
      rw [map_add]; exact add_mem (Submodule.mem_sup_left (hV₁ t)) (Submodule.mem_sup_right (hV₂ t))⟩
  | smul c x _ hx =>
    obtain ⟨V, h, hV⟩ := hx
    exact ⟨V, h, fun t => by rw [map_smul]; exact Submodule.smul_mem _ _ (hV t)⟩

end GlobalTheory.OneParamOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupHodgeTateFirstMapNatural
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.HodgeNat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem theta_xi_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (xi ε) = 0 := by
  have h1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
  have h2 := h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  rw [xi, map_sum]
  simpa [map_pow, WittVector.fontaineTheta_teichmuller, zeta] using h2

theorem ghost_mu_eq_zero [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (n : ℕ) :
    ghost p O n (Sandwich.mu ε) = 0 := by
  induction n with
  | zero =>
    show WittVector.fontaineTheta O p (Sandwich.mu ε) = 0
    rw [Sandwich.mu, map_sub, WittVector.fontaineTheta_teichmuller, map_one, sub_eq_zero]
    exact hε.zeta_zero
  | succ n ih =>
    rw [← ghost_frobenius, Dieudonne.frobenius_mu, ghost_mul, ih, mul_zero]

noncomputable def muPair [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : TDual G where
  toFun t := Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)
  map_add' s t := by
    simp only [epsPairing, map_add, LinearMap.add_apply, mul_add]
  map_smul' a t := by
    simp only [epsPairing, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring

theorem muPair_mem [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (G : PDivGroup p O)
    (χ : G.dual.Tate) : muPair hε G χ ∈ latt G := fun n =>
  ⟨0, fun t => by
    show ghost p O n (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) = 0
    rw [ghost_mul, ghost_mu_eq_zero hε, zero_mul]⟩

end GlobalTheory.PDivLat.HodgeNat

open GlobalTheory.PDivLat.HodgeNat in

theorem GlobalTheory.PDivLat.iota_natural : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G H : PDivGroup p O) (f : G ⟶ H), HasDatum hε G → HasDatum hε H → ∀ (M : Type) [AddCommGroup M] [Module O M] (r : latt G →ₛₗ[WittVector.fontaineTheta O p] M) (M' : Type) [AddCommGroup M'] [Module O M'] (r' : latt H →ₛₗ[WittVector.fontaineTheta O p] M') (u : M' →ₗ[O] M) (ι : G.omega →ₗ[O] M) (ι' : H.omega →ₗ[O] M'), Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = xi ε • n) → (∀ y, u (r' y) = r (lattMap f y)) → (∀ (χ : G.dual.Tate) (y : latt G), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) → ι (dlog G χ) = r y) → (∀ (χ : H.dual.Tate) (y : latt H), (∀ t, y.1 t = Sandwich.mu ε * ofPadic p O (epsPairing hε H t χ)) → ι' (dlog H χ) = r' y) → ∀ w, u (ι' w) = ι (omegaMap G H f w) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H f hG hH M _ _ r M' _ _ r' u ι ι' hrs hrk hu hι hι' w
  obtain ⟨hfree, hfin, -⟩ := GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height p C v O hv ε hε G hG
  haveI : Nontrivial (Ainf p O) := (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv).nontrivial
  obtain ⟨hMfree, -, -⟩ := Dieudonne.free_of_reduction (ReciprocityTheory.PGsh.Ainf.theta_surj p O hv)
    (theta_xi_eq_zero hε) r hrs fun m hm => (hrk m).1 hm
  haveI := hMfree

  have key : ∀ χ : H.dual.Tate, u (ι' (dlog H χ)) = ι (omegaMap G H f (dlog H χ)) := by
    intro χ
    let Y : latt H := ⟨muPair hε H χ, muPair_mem hε H χ⟩
    have h1 : ι' (dlog H χ) = r' Y := hι' χ Y fun t => rfl
    have h2 : ι (dlog G (tateMap H.dual G.dual O (dualHom G H f) χ)) = r (lattMap f Y) := by
      refine hι _ _ fun t => ?_
      show Sandwich.mu ε * ofPadic p O (epsPairing hε H (tateMap G H O f t) χ) = _
      rw [epsPairing, epsPairing, pairing_tateMap]
    rw [h1, hu, ← h2, dlog_tateMap]
  obtain ⟨c, hc, hcw⟩ := GlobalTheory.T.pDivGroup_exists_smul_mem_span_dlog p C v O hv ε hε H hH
  have hspan : ∀ x ∈ Submodule.span O (Set.range (dlog H)),
      u (ι' x) = ι (omegaMap G H f x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨χ, rfl⟩ := hx; exact key χ
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have h := hspan _ (hcw w)
  simp only [map_smul] at h
  have h' : c • (u (ι' w) - ι (omegaMap G H f w)) = 0 := by rw [smul_sub, h, sub_self]
  have tf : ∀ x : M, c • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis O M
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h3 := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
    simpa using (mul_eq_zero.1 h3).resolve_left hc
  exact sub_eq_zero.1 (tf _ h')
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierLeftIsometryL2
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEvaluationL2

theorem partL_lintegral_sq : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL (κ' := κ') A Φ ∈ schA F (κ ⊕ κ')) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ A hmem hA μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C₁, hC₁⟩ := hA μ₁ inferInstance
  refine ⟨C₁, fun Φ hΦ => ?_⟩
  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : ((κ → AF F) × (κ' → AF F)) ≃ₜ+ (κ ⊕ κ' → AF F) :=
    { e.symm with map_add' := fun a b => by funext i; cases i <;> rfl }
  let ν : Measure (κ ⊕ κ' → AF F) := (μ₁.prod μ₂).map eA
  haveI : ν.IsAddHaarMeasure := eA.isAddHaarMeasure_map _
  obtain ⟨c, hμν⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have key : ∀ f : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂μ = c * ∫⁻ y, ∫⁻ x, f (Sum.elim x y) ∂μ₁ ∂μ₂ := by
    intro f hf
    have hmeas : Measurable (⇑eA) := eA.continuous.measurable
    rw [hμν, lintegral_smul_measure]
    simp only [ν]
    rw [lintegral_map hf hmeas, lintegral_prod_symm (fun p => f (eA p)) (hf.comp hmeas).aemeasurable]
    rfl
  have hc1 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hmem Φ hΦ)
  have hc2 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  rw [key _ (hc1.measurable.enorm.pow_const 2), key _ (hc2.measurable.enorm.pow_const 2)]
  have inner : ∀ y, ∫⁻ x, ‖partL (κ' := κ') A Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ =
      C₁ * ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ := by
    intro y
    have h := hC₁ _ (GlobalTheory.DoublingEvLaw.sliceL hΦ y)
    simpa only [partL_apply, Sum.elim_comp_inl, Sum.elim_comp_inr] using h
  have hm : Measurable fun y => ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    Measurable.lintegral_prod_left' (f := fun p : (κ → AF F) × (κ' → AF F) => ‖Φ (eA p)‖ₑ ^ 2)
      ((hc2.comp eA.continuous).measurable.enorm.pow_const 2)
  simp_rw [inner]
  rw [lintegral_const_mul _ hm]
  ring

end GlobalTheory.DoublingEvaluationL2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperOfInfinitelyManyLargeTorsionCounts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.properOfInfinitelyManyLargeTorsionCounts :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G →
      ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ C : ℕ,
      {m : ℕ | (m : k) ≠ 0 ∧ ∃ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) ∧
        m ^ (2 * g) ≤ C * s.card}.Infinite → IsProper G.hom := by
  intro k _ _ G _ hG g hsm C hinf
  obtain ⟨m, ⟨hm0, s, hs, hle⟩, hCm⟩ := hinf.exists_gt C
  have hm1 : 1 ≤ m := by omega
  have hcard : 0 < s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · rw [h, Nat.mul_zero] at hle
      have : 0 < m ^ (2 * g) := Nat.pow_pos hm1
      omega
    · exact h
  have hlt : m ^ (2 * g) < m * s.card :=
    lt_of_le_of_lt hle (Nat.mul_lt_mul_of_pos_right hCm hcard)
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    exact GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k p G hG g hsm m hm0 s hs hlt
  · subst hp0
    haveI : CharZero k := CharP.charP_to_charZero k
    exact GlobalTheory.T.isProper_of_many_torsion_points_charZero k G hG g hsm m s hs hlt
end

