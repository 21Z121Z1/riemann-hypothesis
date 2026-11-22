import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0172
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductIsModularFormCoeffSeqLocallyAlgebr
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZmChar

theorem ch_mul {M : ℕ} (χ : DirichletCharacter ℂ M) (x y : ℤ) : ch χ (x * y) = ch χ x * ch χ y := by
  simp [ch]

theorem ch_add_dvd {M : ℕ} (χ : DirichletCharacter ℂ M) (K : ℕ) (h : M ∣ K) (x : ℤ) : ch χ (x + K) = ch χ x := by
  obtain ⟨t, rfl⟩ := h
  simp [ch, ZMod.natCast_self]

theorem ch_zero {M : ℕ} [Fact (1 < M)] (χ : DirichletCharacter ℂ M) : ch χ 0 = 0 := by
  simp only [ch, Int.cast_zero]
  exact MulChar.map_nonunit χ not_isUnit_zero

theorem inv_apply_neg_one {M : ℕ} (χ : DirichletCharacter ℂ M) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply]
  have : Ring.inverse (-1 : ZMod M) = -1 := by simpa using Ring.inverse_unit (-1 : (ZMod M)ˣ)
  rw [this]

theorem isUnit_of_coprime {M : ℕ} (d : ℤ) (h : IsCoprime d (M : ℤ)) : IsUnit (d : ZMod M) := by
  obtain ⟨a, b, hab⟩ := h
  have := congrArg (Int.cast : ℤ → ZMod M) hab
  push_cast at this
  simp [ZMod.natCast_self] at this
  exact isUnit_iff_exists_inv.2 ⟨a, by rw [mul_comm]; exact this⟩

theorem mul_inv_unit {M : ℕ} (χ : DirichletCharacter ℂ M) (d : ℤ) (h : IsUnit (d : ZMod M)) : ch χ d * ch χ⁻¹ d = 1 := by
  show χ (d : ZMod M) * χ⁻¹ (d : ZMod M) = 1
  rw [← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply h

end GlobalTheory.EisM.ZmChar

namespace GlobalTheory.EisM.ZmChar

theorem cop_dvd {d : ℤ} {A B : ℕ} (h : IsCoprime d (B : ℤ)) (hAB : A ∣ B) : IsCoprime d (A : ℤ) :=
  h.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hAB)

end GlobalTheory.EisM.ZmChar

open GlobalTheory.EisM.ZmChar in

theorem GlobalTheory.zm_char_mf : ∀ (k j N l m : ℕ) (ε : DirichletCharacter ℂ N) (u : ℤ → ℂ) (θ ν : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ (l ^ m)), j + 2 ≤ k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → (∀ x, u (x + N) = u x) → (∀ d x : ℤ, IsCoprime d N → u (x * d) = ch θ⁻¹ d * u x) → ε = θ⁻¹ * ν → ψ (-1) * θ (-1) = (-1) ^ (k - 1 - j) → ψ (-1) * ν (-1) = (-1) ^ (j + 1) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l u (ch ν) (fun x y => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ j)) := by
  intro k j N l m ε u θ ν ψ hjk hN hl hm hlN hu hmul hε hpar1 hpar2
  have hl1 : 1 < l ^ m := Nat.one_lt_pow (by omega) hl.one_lt
  haveI : Fact (1 < l ^ m) := ⟨hl1⟩
  have hlm : 0 < l ^ m := by omega
  have hup : ∀ K : ℕ, N ∣ K → ∀ x, u (x + K) = u x := by
    intro K hK x
    obtain ⟨t, rfl⟩ := hK
    have e : ((N * t : ℕ) : ℤ) = (t : ℤ) * N := by push_cast; ring
    rw [e]
    exact (Function.Periodic.nat_mul (show Function.Periodic u (N : ℤ) from hu) t) x
  obtain ⟨c, hE1⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (k - 1 - j) (N * l ^ m) 1 (fun x => u x * ch ψ x) (fun _ => 1)
    (fun d => ch θ⁻¹ d * ch ψ d) (fun _ => 1) (by omega) (by positivity) one_pos (by simp [ch_zero])
    (fun x => by rw [hup _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) (fun _ => rfl)
    (fun d hd => by
      have hdN : IsCoprime d (N : ℤ) := cop_dvd hd (by simp)
      refine ⟨fun x => ?_, fun x => by ring⟩
      rw [hmul d x hdN, ch_mul]
      ring)
    (by simp only [ch, Int.cast_neg, Int.cast_one, mul_one]; rw [inv_apply_neg_one, mul_comm, hpar1])
  obtain ⟨c', hE2⟩ := GlobalTheory.T.eisenstein_periodic_weights_isModularForm (j + 1) (l ^ m) N (ch ψ⁻¹) (ch ν) (ch ψ⁻¹) (ch ν) (by omega) hlm hN
    (ch_zero _) (ch_add_dvd _ _ dvd_rfl) (ch_add_dvd _ _ dvd_rfl)
    (fun d _ => ⟨fun x => by rw [ch_mul, mul_comm], fun x => by rw [ch_mul, mul_comm]⟩)
    (by simp only [ch, Int.cast_neg, Int.cast_one]; rw [inv_apply_neg_one, hpar2])
  have hD1 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion (k - 1 - j) (N * l ^ m * 1) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self l (by omega)) _) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_right _ _) _),
      ch_add_dvd _ _ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)]) hE1).2
  have hD2 := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion (j + 1) (l ^ m * N) l _ _ (by omega) hl
    (dvd_mul_of_dvd_left (dvd_pow_self l (by omega)) _)
    (fun d => by rw [ch_add_dvd _ _ (dvd_mul_right _ _), ch_add_dvd _ _ (dvd_mul_left _ _)]) hE2).2
  have hD1' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD1
  have hD2' := (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.2.1 (N * l ^ (m + 1)) _ ⟨1, by ring⟩ hD2
  have P := GlobalTheory.EisM.mul_main.2 _ _ _ _ _ _ _ hD1' hD2'
  rw [GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product k l j u (ch ν) (ch ψ) (ch ψ⁻¹) c c' hjk]
  have hk : k - 1 - j + (j + 1) = k := by omega
  rw [hk] at P
  refine (GlobalTheory.EisM.mf_linear _ _ _).2.2.2.1 (ch ε) _ (fun d hd => ?_) P
  have hU := mul_inv_unit ψ d (isUnit_of_coprime d (cop_dvd hd (dvd_mul_of_dvd_right (pow_dvd_pow l (by omega)) _)))
  subst hε
  simp only [ch, MulChar.mul_apply] at hU ⊢
  linear_combination (θ⁻¹ (d : ZMod N) * ν (d : ZMod N)) * hU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
section
set_option autoImplicit false

open Formalism.BasicNotions NumberField

namespace GlobalTheory.WittFracComplex

open Cardinal in

theorem nonempty_ringHom_complex_of_le_continuum (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem charZero_wittVector (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    CharZero (WittVector p k) := by
  obtain ⟨q, hq⟩ := CharP.exists (WittVector p k)
  have h1 : ((q : ℕ) : k) = 0 := by
    have := congrArg (WittVector.constantCoeff : WittVector p k →+* k) (CharP.cast_eq_zero (WittVector p k) q)
    rwa [map_natCast, map_zero] at this
  have h2 : p ∣ q := (CharP.cast_eq_zero_iff k p q).1 h1
  rcases CharP.char_is_prime_or_zero (WittVector p k) q with h | h
  · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
    subst h3
    exact absurd (CharP.cast_eq_zero (WittVector p k) p) (WittVector.p_nonzero p k)
  · subst h
    exact CharP.charP_to_charZero _

open Cardinal in

theorem mk_wittVector_le (p : ℕ) (k : Type) (hk : #k ≤ ℵ₀) : #(WittVector p k) ≤ 𝔠 := by
  have h : Function.Injective (WittVector.coeff : WittVector p k → ℕ → k) :=
    fun x y h => WittVector.ext (fun n => congrFun h n)
  refine (Cardinal.mk_le_of_injective h).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat, ← Cardinal.aleph0_power_aleph0]
  exact Cardinal.power_le_power_right hk

open Cardinal in

theorem nonempty_ringHom_complex : ∀ (p : ℕ) [Fact p.Prime], Nonempty (DV.KW p →+* ℂ) := by
  intro p _
  have hk : #(AlgebraicClosure (ZMod p)) ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (AlgebraicClosure (ZMod p))
    rwa [max_eq_right (Cardinal.lt_aleph0_of_finite _).le] at this
  have := charZero_wittVector p (AlgebraicClosure (ZMod p))
  have : CharZero (DV.KW p) :=
    (RingHom.charZero_iff (IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p))).1 this
  refine nonempty_ringHom_complex_of_le_continuum _ ?_
  rw [Cardinal.mk_fractionRing]
  exact mk_wittVector_le p _ hk

end GlobalTheory.WittFracComplex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PointGlobalSectionsNeBot
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped NNReal

namespace GlobalTheory.PointGeometry

variable (F : Type) [Field F] [NumberField F]

structure AdelicLine where

  inf : InfinitePlace F → ℝ

  fin : HeightOneSpectrum (𝓞 F) → ℝ
  fin_finite : (Function.mulSupport fin).Finite

variable {F}

open Classical in

def AdelicLine.of (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  if h : (Function.mulSupport b).Finite then ⟨a, b, h⟩ else ⟨a, 1, by simp⟩

@[simp] theorem AdelicLine.of_inf (a : InfinitePlace F → ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ) :
    (AdelicLine.of a b).inf = a := by
  unfold AdelicLine.of; split_ifs <;> rfl

theorem AdelicLine.of_fin (a : InfinitePlace F → ℝ) {b : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : (Function.mulSupport b).Finite) : (AdelicLine.of a b).fin = b := by
  unfold AdelicLine.of; rw [dif_pos h]

def AdelicLine.deg (L : AdelicLine F) : ℝ :=
  -((∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log (L.inf v)) + ∑ᶠ w, Real.log (L.fin w)) /
    (Module.finrank ℚ F : ℝ)

def AdelicLine.twist (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    (cf : HeightOneSpectrum (𝓞 F) → ℝ) : AdelicLine F :=
  AdelicLine.of (fun v => Real.exp (-ci v) * L.inf v) (fun w => Real.exp (-cf w) * L.fin w)

theorem AdelicLine.twist_fin (L : AdelicLine F) (ci : InfinitePlace F → ℝ)
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (h : (Function.support cf).Finite) :
    (L.twist ci cf).fin = fun w => Real.exp (-cf w) * L.fin w := by
  refine AdelicLine.of_fin _ ((h.union L.fin_finite).subset fun w hw => ?_)
  by_contra hn
  simp only [Set.mem_union, Function.mem_support, Function.mem_mulSupport, not_or, not_not] at hn
  exact hw (by simp [hn.1, hn.2])

variable [StarRing F]

def latticeNorm (W : HLat F) (ι : W.V →ₗ[F] F) (w : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (⨆ x : W.L, FinitePlace.mk w (ι x))⁻¹

def frameSq (W : HLat F) (ι : W.V →ₗ[F] F) (v : InfinitePlace F) : ℝ≥0 :=
  ∑ k : W.ι, ‖∑ i, (W.X v) i k • v.embedding (ι (W.b i))‖₊ ^ 2

def ofLattice (W : HLat F) (ι : W.V →ₗ[F] F) : AdelicLine F :=
  AdelicLine.of (fun v => (Real.sqrt (frameSq W ι v))⁻¹) (latticeNorm W ι)

variable (F)

def pointGeo : DV.Geo F where
  Var := Unit
  dim _ := 0
  Fn _ := F
  Dv _ := PUnit
  Eff _ _ := True
  eff_zero _ := trivial
  eff_add _ _ _ _ _ := trivial
  H0 _ _ := ⊤
  degreeZeroCohomology_finiteDimensional _ _ := inferInstance
  mul_mem_riemannRochSpace_add _ _ _ _ _ _ _ := Submodule.mem_top
  riemannRoch_mono _ _ _ _ := le_rfl
  KY _ := 0
  Cl _ := Set Unit
  properCl _ Z := Z ≠ Set.univ
  subCl _ Z Z' := Z ⊆ Z'
  supp _ _ := ∅
  inter _ _ := 1
  nef _ _ := True
  big _ _ := True
  bpf _ _ V := ∃ f ∈ V, f ≠ 0
  phiBir _ _ V := ∃ f ∈ V, f ≠ 0
  phiNoContr _ _ _ _ := True
  vanishOn _ _ f Z := Z.Nonempty → f = 0
  hdim _ i _ := if i = 0 then 1 else 0
  pts _ _ := Unit
  ptsMeas _ _ := ⊤
  vol _ _ := @MeasureTheory.Measure.dirac Unit ⊤ ()
  FnC _ _ := ℂ
  cx _ σ := σ
  cx_smul _ σ a f := by simp
  Met _ _ _ := ℝ≥0
  mAdd _ _ _ _ h h' := h * h'
  mPow _ _ _ k h := h ^ k
  fsMet _ _ _ _ _ e := ∑ k, ‖e k‖₊ ^ 2
  pn _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  pnK _ _ _ h f _ := ‖f‖ ^ 2 / (h : ℝ)
  mSmooth _ _ _ h := h ≠ 0
  mPsh _ _ _ _ _ := True
  redZero _ _ _ _ S := S = Set.univ
  agreeOn _ _ _ f g S := S.Nonempty → f = g
  resNorm _ _ _ h _ _ _ g _ := ‖g‖ ^ 2 / (h : ℝ)
  Adl _ := AdelicLine F
  ofW _ _ W ι := ofLattice W ι
  twist _ L ci cf := L.twist ci cf
  arTop _ L := L.deg
  arVol _ L := max L.deg 0
  nefA _ L := 0 ≤ L.deg
  supInf _ L v τ f := v f * L.inf v ^ τ
  supFin _ L w τ f := FinitePlace.mk w f * L.fin w ^ τ
  cutGood _ bd _ _ _ _ _ _ _ := bd = ∅
  cutHt _ L _ _ _ _ _ _ _ := L.deg
  cutOrd _ _ _ _ _ _ _ _ _ _ := 0
  resFull _ _ _ _ _ _ _ _ M ι _ :=
    (M.L.map (ι.restrictScalars (𝓞 F))).FG ∧ M.L.map (ι.restrictScalars (𝓞 F)) ≠ ⊥
  resDeg _ _ _ _ _ _ _ _ M ι L := (AdelicLine.of L.inf (latticeNorm M ι)).deg
  supInf_ofW _ _ W ι v τ f := by
    rw [ciSup_unique]
    change v f * (ofLattice W ι).inf v ^ τ =
      Real.sqrt (‖v.embedding f‖ ^ 2 / ((frameSq W ι v ^ τ : ℝ≥0) : ℝ))
    rw [ofLattice, AdelicLine.of_inf, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      InfinitePlace.norm_embedding_eq, inv_pow, div_eq_mul_inv]
    congr 2
    rw [NNReal.coe_pow, eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity),
      ← mul_pow, Real.mul_self_sqrt (NNReal.coe_nonneg _)]
  supInf_twist _ L ci cf _ v τ f := by
    rw [AdelicLine.twist, AdelicLine.of_inf, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  supFin_twist _ L ci cf h w τ f := by
    rw [AdelicLine.twist_fin L ci h, mul_pow, ← Real.exp_nat_mul, mul_neg]
    ring
  regOn _ _ _ _ _ := True

theorem point_global_sections_ne_bot (Y : (pointGeo F).Var) : (pointGeo F).H0 Y 0 ≠ ⊥ :=
  (top_ne_bot : (⊤ : Submodule F F) ≠ ⊥)

theorem exists_geo : ∀ (F : Type) [Field F] [NumberField F] [StarRing F],
    ∃ G : DV.Geo F, ∃ Y : G.Var, G.H0 Y 0 ≠ ⊥ :=
  fun F _ _ _ => ⟨pointGeo F, (), point_global_sections_ne_bot F _⟩

end GlobalTheory.PointGeometry
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinIntegralTendstoAtZero
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma rpow_le_add_inv_of_mem_Icc {y s : ℝ} (hy : 0 < y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    y ^ s ≤ y + y⁻¹ := by
  rcases le_or_gt 1 y with h | h
  · have : y ^ s ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs1
    rw [Real.rpow_one] at this
    have : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
    linarith
  · have h1 : y ^ s ≤ 1 := Real.rpow_le_one hy.le h.le hs0
    have h2 : 1 ≤ y⁻¹ := by rw [le_inv_comm₀ one_pos hy]; simpa using h.le
    linarith

lemma mod_ofReal_norm {F : ℍ → ℂ} (hF : Mod F) : Mod (fun τ => ((‖F τ‖ : ℝ) : ℂ)) := by
  obtain ⟨C, A, h⟩ := hF
  exact ⟨C, A, fun τ => by simpa using h τ⟩

lemma mod_im_pow (A : ℕ) : Mod (fun τ : ℍ => (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, A, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul]

lemma mod_im_add_inv : Mod (fun τ : ℍ => (((τ.im + τ.im⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, 1, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im + τ.im⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul, pow_one]

theorem rankin_tendsto : ∀ (k j L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Φ : ℤ × ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ), 1 ≤ k → 2 ≤ j → 0 < L → 0 < L' → N ∣ L' → Wt L' ρ → CF k L' (ch ε) h → PolyB b → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Tendsto (fun s : ℝ => pet k ρ (qs h) (fun τ => qs b τ * lat j s L (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (pet k ρ (qs h) (fun τ => qs b τ * lat j 0 L (0, 1) Φ τ))) := by
  intro k j L L' N ε Φ ρ h b hk hj hL hL' hN hρ hh hb hΦ
  obtain ⟨⟨C, A, hC⟩, hmeas, hlim⟩ := GlobalTheory.T.regularizedEisensteinLatticeSum_moderate_measurable_tendsto j L Φ hj hL hΦ
  have hbc : Continuous (qs b) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2
  have hhc : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have him : Continuous (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im
  set G : ℍ → ℂ := fun τ => ((‖qs b τ‖ : ℝ) : ℂ) * ((C : ℂ) * (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) *
    (((τ.im + τ.im⁻¹ : ℝ)) : ℂ) with hG
  have hGc : Continuous G := by
    have h1 : Continuous (fun τ : ℍ => (τ.im ^ A)⁻¹) :=
      (him.pow A).inv₀ (fun τ => (pow_pos τ.im_pos A).ne')
    have h2 : Continuous (fun τ : ℍ => τ.im⁻¹) := him.inv₀ (fun τ => τ.im_pos.ne')
    simp only [hG]
    fun_prop
  have hGmod : Mod G := by
    have M := GlobalTheory.T.hasModerateGrowth_algebra_slash_stable
    exact (M.1 _ _ ((M.1 _ _ (mod_ofReal_norm (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth b hb))
      ((M.1 _ _ (M.2.1 (C : ℂ)) (mod_im_pow A)).2)).2) mod_im_add_inv).2
  have hint := GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L' L' N ε h ρ G hk hL' hN hρ hh hGc.aestronglyMeasurable hGmod
  have hρm : Measurable (fun τ => (ρ τ : ℂ)) := Complex.measurable_ofReal.comp hρ.meas
  simp only [pet]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun τ => ‖(ρ τ : ℂ) * (conj (qs h τ) * G τ * (τ.im : ℂ) ^ k)‖) ?_ ?_ hint.norm ?_
  · refine Filter.Eventually.of_forall (fun s => ?_)
    have hs : Measurable (fun τ : ℍ => (((τ.im ^ s : ℝ)) : ℂ)) :=
      Complex.measurable_ofReal.comp ((him.measurable).pow_const s)
    exact (hρm.mul ((((Complex.continuous_conj.comp hhc).measurable).mul ((hbc.measurable.mul (hmeas s)).mul hs)).mul
      ((Complex.measurable_ofReal.comp him.measurable).pow_const k))).aestronglyMeasurable
  · have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    filter_upwards [hev] with s hs
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have hρ0 := hρ.nonneg τ
    have hl := hC s τ hs.1.le hs.2.le
    have hys := rpow_le_add_inv_of_mem_Icc hy hs.1.le hs.2.le
    have hX : 0 ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := le_trans (norm_nonneg _) hl
    have hys0 : 0 ≤ τ.im ^ s := Real.rpow_nonneg hy.le s
    have key : ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s ≤
        |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹) :=
      mul_le_mul (hl.trans (le_abs_self _)) hys hys0 (abs_nonneg _)
    simp only [hG, norm_mul, Complex.norm_real, Complex.norm_conj, norm_pow, Real.norm_eq_abs,
      norm_norm, abs_norm, Complex.ofReal_mul]
    rw [abs_of_nonneg hy.le, abs_of_nonneg (Real.rpow_nonneg hy.le s),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ τ.im + τ.im⁻¹)]
    have hcomb : |C| * |τ.im ^ A + (τ.im ^ A)⁻¹| = |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| := (abs_mul _ _).symm
    have hP : 0 ≤ |ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k := by positivity
    calc |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) * τ.im ^ k)
        = (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) := by ring
      _ ≤ (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (|C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹)) :=
        mul_le_mul_of_nonneg_left key hP
      _ = |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * (|C| * |τ.im ^ A + (τ.im ^ A)⁻¹|) * (τ.im + τ.im⁻¹)) * τ.im ^ k) := by
        rw [hcomb]; ring
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have h1 : Tendsto (fun s : ℝ => (((τ.im ^ s : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 (((τ.im ^ (0:ℝ) : ℝ)) : ℂ)) := by
      have : ContinuousAt (fun s : ℝ => τ.im ^ s) 0 :=
        Real.continuousAt_const_rpow hy.ne'
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp this.tendsto).mono_left nhdsWithin_le_nhds
    have h2 := ((tendsto_const_nhds (x := (ρ τ : ℂ))).mul
      (((tendsto_const_nhds (x := conj (qs h τ))).mul (((tendsto_const_nhds (x := qs b τ)).mul (hlim τ)).mul h1)).mul
        (tendsto_const_nhds (x := (τ.im : ℂ) ^ k))))
    simpa only [Real.rpow_zero, Complex.ofReal_one, mul_one] using h2

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelInvariantPrincipalCongruence
section
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ

theorem act_sub_int_of_Gamma (x : Fin 2 → ℚ) (M : ℕ) (hM : 0 < M)
    (hx : ∃ a b : ℤ, x 0 = a / M ∧ x 1 = b / M) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M) :
    ∃ n : Fin 2 → ℤ, act x γ = fun i => x i + n i := by
  obtain ⟨a, b, ha, hb⟩ := hx
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have d00 : (M : ℤ) ∣ γ 0 0 - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 0 0) M).mp (by rw [Int.cast_one]; exact h00.symm)
  have d11 : (M : ℤ) ∣ γ 1 1 - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 1 1) M).mp (by rw [Int.cast_one]; exact h11.symm)
  have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  obtain ⟨k00, e00⟩ := d00
  obtain ⟨k11, e11⟩ := d11
  obtain ⟨k01, e01⟩ := d01
  obtain ⟨k10, e10⟩ := d10
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * k00 := by
    rw [show (γ 0 0 : ℤ) = 1 + M * k00 by linarith]; push_cast; ring
  have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * k11 := by
    rw [show (γ 1 1 : ℤ) = 1 + M * k11 by linarith]; push_cast; ring
  have q01 : ((γ 0 1 : ℤ) : ℚ) = M * k01 := by rw [e01]; push_cast; ring
  have q10 : ((γ 1 0 : ℤ) : ℚ) = M * k10 := by rw [e10]; push_cast; ring
  refine ⟨![a * k00 + b * k10, a * k01 + b * k11], ?_⟩
  funext i
  fin_cases i
  · simp only [act, Fin.sum_univ_two]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [q00, q10, ha, hb]; push_cast; field_simp; ring
  · simp only [act, Fin.sum_univ_two]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
    rw [q01, q11, ha, hb]; push_cast; field_simp; ring

theorem siegel_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ)
    (x : Fin 2 → ℚ) (M : ℕ), admitted c x → 0 < M → (∃ a b : ℤ, x 0 = a / M ∧ x 1 = b / M) →
    ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) (siegel T c x) = siegel T c x := by
  intro Ω _ _ _ ε T c x M hx hM hden γ hγ
  rw [GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε T c x γ hx]
  obtain ⟨n, hn⟩ := act_sub_int_of_Gamma x M hM hden γ hγ
  have hs : sgC c (act x γ) = sgC c x := by
    rw [hn]; funext z; exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x n _ hx
  unfold siegel
  rw [hs]

end GlobalTheory.KZ
end

