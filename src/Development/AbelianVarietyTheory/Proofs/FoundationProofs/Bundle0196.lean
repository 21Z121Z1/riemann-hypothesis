import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Formalism.GradedWeylDivisibility.StatementE
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnity
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.FactorsAtL

theorem norm_one_of_pow {R : Type*} [NormedDivisionRing R] {z : R} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    ‖z‖ = 1 := by
  have : ‖z‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn.ne').1 this

theorem char_inv_facts {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N) (l : ℕ) (hl : l.Coprime N) :
    (χ⁻¹ (l : ZMod N)) ^ N.totient = 1 ∧ χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = 1 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hu : IsUnit (l : ZMod N) := (ZMod.isUnit_iff_coprime l N).2 hl
  constructor
  · obtain ⟨v, hv⟩ := hu
    rw [← hv, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  · rw [show χ⁻¹ (l : ZMod N) * χ (l : ZMod N) = (χ⁻¹ * χ) (l : ZMod N) from rfl, MulChar.inv_mul, MulChar.one_apply hu]

theorem norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]

end GlobalTheory.FactorsAtL

namespace GlobalTheory.FactorsAtL

theorem factors_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N)
    (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l →
    α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) →
    α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  intro l _ ι e N χ g α β ζ he hN hlN hP hs hp hα ⟨n, hn, hζ⟩
  have hlp : l.Prime := Fact.out
  have hcop : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hlp).2 hlN
  obtain ⟨hut, huc⟩ := char_inv_facts hN χ l hcop
  have htot : 0 < N.totient := Nat.totient_pos.2 hN
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hinv0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl0
  have hinv1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hnl : ‖ι.symm (l : ℂ)‖ = (l : ℝ)⁻¹ := by rw [map_natCast]; exact norm_natCast_self l
  have hnζ : ‖ι.symm ζ‖ = 1 := norm_one_of_pow hn (by rw [← map_pow, hζ, map_one])
  have hnu : ‖ι.symm (χ⁻¹ (l : ZMod N))‖ = 1 := norm_one_of_pow htot (by rw [← map_pow, hut, map_one])
  refine ⟨?_, ?_, ?_⟩
  · intro hαζ
    have hcα : ‖α‖ = 1 := by rw [hαζ]; exact Complex.norm_eq_one_of_pow_eq_one hζ hn.ne'
    have hcu : ‖χ⁻¹ (l : ZMod N)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hut htot.ne'
    have hβn : ‖β‖ = (l : ℝ) ^ (2 * e) := by
      have h := congrArg norm hp
      rw [norm_mul, norm_mul, hcα, hcu, norm_pow, Complex.norm_natCast, one_mul, one_mul] at h
      exact h
    obtain ⟨_, hrec, _⟩ := GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hP
    obtain ⟨_, ⟨C, hC⟩, _⟩ := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hP.cf
    set u := χ⁻¹ (l : ZMod N) with hu_def
    let c : ℕ → ℂ := fun r => u ^ r * g (l ^ r)
    have hc0 : c 0 = 1 := by simp [c, hP.one]
    have hc1 : c 1 = α + β := by simp [c, hs]
    have hcr : ∀ r, c (r + 2) = (α + β) * c (r + 1) - α * β * c r := by
      intro r
      simp only [c]
      rw [hrec l r hlp hlN, hs, hp, show 2 * e + 1 - 1 = 2 * e by omega]
      have key : u ^ (r + 2) * χ (l : ZMod N) = u ^ (r + 1) := by rw [pow_succ, mul_assoc, huc, mul_one]
      linear_combination (-(l : ℂ) ^ (2 * e) * g (l ^ r)) * key
    set s := Real.sqrt l with hs_def
    have hs2 : s ^ 2 = l := Real.sq_sqrt hl0.le
    have hs1 : 1 < s := by rw [hs_def]; exact Real.lt_sqrt (by norm_num) |>.2 (by simpa using hl1)
    set R := s ^ (2 * e + 1) with hR
    have hR0 : 0 ≤ R := by positivity
    have hbound : ∀ r, ‖c r‖ ≤ Real.sqrt (max C 0) * R ^ r := by
      intro r
      have h1 : ‖c r‖ = ‖g (l ^ r)‖ := by
        simp only [c]; rw [norm_mul, norm_pow, hcu, one_pow, one_mul]
      have hX : ((l ^ r : ℕ) : ℝ) ^ (2 * e + 1) = (R ^ r) ^ 2 := by
        push_cast; rw [hR, ← hs2]; ring
      have h2 : ‖g (l ^ r)‖ ^ 2 ≤ max C 0 * (R ^ r) ^ 2 := by
        rw [← hX]; exact (hC _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      rw [h1, ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (pow_nonneg hR0 r), ← Real.sqrt_mul (le_max_right _ _)]
      exact Real.sqrt_le_sqrt h2
    obtain ⟨_, hβR⟩ := GlobalTheory.T.roots_norm_le_of_bounded_two_step_recurrence α β c (Real.sqrt (max C 0)) R hR0 hc0 hc1 hcr hbound
    rw [hβn, ← hs2, ← pow_mul, hR] at hβR
    have : s ^ (2 * e + 1) < s ^ (2 * (2 * e)) := pow_lt_pow_right₀ hs1 (by omega)
    linarith
  · intro hβζ
    have h := congrArg (fun z => ‖ι.symm z‖) hp
    simp only [map_mul, map_pow, norm_mul, norm_pow] at h
    rw [hα, hnu, hnl, one_mul, one_mul, hβζ, map_mul, norm_mul, hnl, hnζ, mul_one] at h
    have : ((l : ℝ)⁻¹) ^ (2 * e) < ((l : ℝ)⁻¹) ^ 1 := pow_lt_pow_right_of_lt_one₀ hinv0 hinv1 (by omega)
    rw [pow_one] at this
    linarith
  · intro j hj hαj
    rw [hαj, map_mul, map_pow, norm_mul, norm_pow, hnl, hnζ, mul_one] at hα
    have : ((l : ℝ)⁻¹) ^ j < 1 := pow_lt_one₀ hinv0.le hinv1 (by omega)
    linarith

end GlobalTheory.FactorsAtL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTypePrimesOfAdmissible
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
open Formalism.MainNotions.N
open scoped Matrix Pointwise

namespace GlobalTheory.InertiaTypePrimes

section General

variable {Γ R : Type} [Group Γ] [CommRing R] {r : ℕ}

theorem mem_ker_mapRep_iff (J : Ideal R) (ρ : Γ →* GL (Fin r) R) (g : Γ) :
    g ∈ (mapRep (Ideal.Quotient.mk J) ρ).ker ↔
      ∀ a b, (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change (Ideal.Quotient.mk J).mapMatrix ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = 1 ↔ _
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]

theorem isOpen_ker_mapRep [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (ρ : Γ →* GL (Fin r) R)
    (hρ : Continuous fun g => ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)) :
    IsOpen ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) := by
  have : ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) = ⋂ a, ⋂ b,
      (fun g => (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_mapRep_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => hJ.preimage ?_
  exact (hρ.sub continuous_const).matrix_elem a b

theorem pow_sub_one_mem (I : Ideal R) (l m : ℕ) (hl : (l : R) ∈ I) (Y : Matrix (Fin r) (Fin r) R)
    (hY : ∀ a b, (Y - 1) a b ∈ I ^ (m + 1)) (a b : Fin r) : (Y ^ l - 1) a b ∈ I ^ (m + 2) := by
  have h1 : (Ideal.Quotient.mk I).mapMatrix Y = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk I).mapMatrix, ← map_sub]
    ext a b
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem] using Ideal.pow_le_self (Nat.succ_ne_zero m) (hY a b)
  have h2 : (Ideal.Quotient.mk I).mapMatrix (∑ i ∈ Finset.range l, Y ^ i) = 0 := by
    have h0 : ((l : ℕ) : R ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hl
    simp only [map_sum, map_pow, h1, one_pow, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul (R ⧸ I), h0, zero_smul]
  have h3 : ∀ a b, (∑ i ∈ Finset.range l, Y ^ i) a b ∈ I := fun a b => by
    have := congrFun (congrFun h2 a) b
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem] using this
  rw [← mul_geom_sum, Matrix.mul_apply, pow_succ I (m + 1)]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (hY a c) (h3 c b)

def eigenStab (ρ : Γ →* GL (Fin r) R) (χ : Γ →* Rˣ) (x : Fin r → R) : Subgroup Γ where
  carrier := {g | ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) *ᵥ x = ((χ g : Rˣ) : R) • x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hh,
      Matrix.mulVec_smul, hg, smul_smul, mul_comm]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := congrArg (fun y => ((χ g⁻¹ : Rˣ) : R) •
      (((ρ g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) *ᵥ y)) hg
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec, one_smul] at h
    exact h.symm

end General

theorem isWild_of_isWildAt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω) (h : IsWildAt A σ) : IsWild A σ := by
  have h1 : ∀ x : Ω, x ≠ 0 → A.valuation (σ x - x) < A.valuation x := fun x hx => by
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    have h0 : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx)
    rw [e, map_mul]
    exact mul_lt_of_lt_one_left h0 (h x hx)
  have h2 : ∀ x : Ω, A.valuation (σ x) = A.valuation x := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact Valuation.map_eq_of_sub_lt _ (h1 x hx)
  refine ⟨⟨?_, fun x hx => ?_⟩, h1⟩
  · change σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, ← h2, AlgEquiv.smul_def, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · exact (h1 x hx0).trans_le hx

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {r : ℕ} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

end Wild

end GlobalTheory.InertiaTypePrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BlochKatoIntegralScalars

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_of_norm_le_one (K : Loc.FinExt l) (x : K.1) (h : ‖(x : PadicAlgCl l)‖ ≤ 1) :
    x ∈ Loc.OL K :=
  (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1
    (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : Loc.FinExt l) : CompactSpace ↥(Loc.GK K) := by
  haveI := K.2
  have h : IsClosed ((Loc.GK K : Subgroup (Loc.GQ l)) : Set (Loc.GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.1 h.isCompact

theorem exists_pow_mul_mem_OL {X : Type} [TopologicalSpace X] [CompactSpace X] (K : Loc.FinExt l) {m : ℕ}
    (c : X → Fin m → K.1) (hc : Continuous c) :
    ∃ N : ℕ, ∀ g j, (l : K.1) ^ N * c g j ∈ Loc.OL K := by
  have hc' : Continuous fun g (j : Fin m) => ((c g j : K.1) : PadicAlgCl l) :=
    continuous_pi fun j => continuous_subtype_val.comp ((continuous_apply j).comp hc)
  obtain ⟨C, hC⟩ := (isCompact_range hc').isBounded.exists_norm_le
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hl
  refine ⟨N, fun g j => mem_OL_of_norm_le_one K _ ?_⟩
  have h1 : ‖((c g j : K.1) : PadicAlgCl l)‖ ≤ C :=
    (norm_le_pi_norm (fun j : Fin m => ((c g j : K.1) : PadicAlgCl l)) j).trans (hC _ ⟨g, rfl⟩)
  have h2 : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
  have h3 : (((l : K.1) ^ N * c g j : K.1) : PadicAlgCl l) =
      (l : PadicAlgCl l) ^ N * ((c g j : K.1) : PadicAlgCl l) := by
    push_cast
    rfl
  rw [h3, norm_mul, norm_pow, h2, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact h1.trans hN.le

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem mem_crysSpan_of_rational {O' : Type} [CommRing O'] [IsDomain O'] (ι : O₀ →+* O')
    (hι : Function.Injective ι) (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀)
    (c : ↥(Loc.GK Bw.Kw) → Fin m → ↥Bw.LL.1)
    (hc : c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype)))
    (y : ↥Gw → Fin m → FractionRing O')
    (hy : ∀ g a, ∃ n d : O₀, (d ≠ 0 ∧ Bw.toLL d * c (Bw.e g) a = Bw.toLL n) ∧
      algebraMap O' (FractionRing O') (ι d) * y g a = algebraMap O' (FractionRing O') (ι n))
    (z : ↥Gw → Fin m → KmodO O') (hz : ∀ g a, z g a = Submodule.Quotient.mk (y g a)) :
    z ∈ crysSpan Bw P ι T := by
  haveI := compactSpace_GK Bw.Kw
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_OL Bw.LL c hc.1.1
  let f : ↥Gw → Fin m → O₀ := fun g j => Bw.eO.symm ⟨_, hN (Bw.e g) j⟩
  have hf : ∀ g j, Bw.toLL (f g j) = (l : Bw.LL.1) ^ N * c (Bw.e g) j := by
    intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply]
  have hφ : Function.Injective ((algebraMap O' (FractionRing O')).comp ι) :=
    (IsFractionRing.injective O' (FractionRing O')).comp hι
  have hl0 : (l : O₀) ≠ 0 := by
    intro h
    have := congrArg Bw.toLL h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hl1 : (l : FractionRing O') ≠ 0 := by
    intro h
    apply hl0
    apply hφ
    rw [map_natCast, map_zero, h]
  refine Submodule.subset_span ⟨((l : FractionRing O') ^ N)⁻¹, f, ?_, fun g j => ?_⟩
  · have := (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))).smul_mem ((l : Bw.LL.1) ^ N) hc
    unfold IsCrysCocycle
    convert this using 1
    funext g j
    rw [hf, MulEquiv.apply_symm_apply]
    rfl
  · rw [hz]
    congr 1
    obtain ⟨n, d, ⟨hd, h1⟩, h2⟩ := hy g j
    have h3 : d * f g j = (l : O₀) ^ N * n := by
      apply toLL_injective Bw
      rw [map_mul, map_mul, hf, map_pow, map_natCast, ← h1]
      ring
    have h4 := congrArg ((algebraMap O' (FractionRing O')).comp ι) h3
    rw [map_mul, map_mul, map_pow, map_natCast] at h4
    simp only [RingHom.comp_apply] at h4
    have hd' : algebraMap O' (FractionRing O') (ι d) ≠ 0 := fun h =>
      hd (hφ (by rw [map_zero]; exact h))
    rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hl1)]
    apply mul_left_cancel₀ hd'
    rw [h4, ← h2]
    ring

end Local

theorem Trep_eq_actDiv (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ)
    (g : GE D) (hg : ψ g = 1) (x : Fin D.R.r → KmodO (D.ntw.Ok i k)) :
    Gen.Trep i s k ψ g x = actDiv (Formalism.MainNotions.N.mapRep (toOk D i k) (latT D i s)) g x := by
  funext a
  have h : ∀ b, ((Formalism.MainNotions.N.mapRep (toOk D i k) (latT D i s) g : GL _ _) : Matrix _ _ _) a b =
      Gen.phiK D.ntw i k (Gen.Tmat i s g a b) := by
    intro b
    rw [← Gen.Tgl_coe]
    rfl
  simp only [actDiv, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, h]
  simp only [Gen.Trep, twRep, MonoidHom.coe_mk, OneHom.coe_mk, hg, inv_one, one_mul, LinearMap.smul_apply,
    Pi.smul_apply, matAct, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum, smul_smul, Gen.Tmat,
    Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.map_apply]
  rfl

theorem mem_of_mk_mem_span {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R G M) (S : Submodule R (G → M)) (hB : ∀ x : M, (fun g => ρ g x - x) ∈ S)
    (A : Set (ReciprocityTheory.Gal.H1 ρ))
    (hA : ∀ x ∈ A, ∃ w : ReciprocityTheory.Gal.Z1 ρ, (w : G → M) ∈ S ∧ x = Submodule.Quotient.mk w)
    (w : ReciprocityTheory.Gal.Z1 ρ) (hw : Submodule.Quotient.mk w ∈ Submodule.span R A) : (w : G → M) ∈ S := by
  have hB' : (ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype ≤ S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype := by
    intro w hw
    obtain ⟨x, hx⟩ := (mem_coboundaries1 ρ _).1 hw
    have : (ReciprocityTheory.Gal.Z1 ρ).subtype w = fun g => ρ g x - x := funext hx
    rw [Submodule.mem_comap, this]
    exact hB x
  have hle : Submodule.span R A ≤ (S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map (Submodule.mkQ _) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hA x hx
    exact ⟨w, hw, rfl⟩
  have h2 : w ∈ ((S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map
      (Submodule.mkQ ((ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype))).comap (Submodule.mkQ _) :=
    hle hw
  rw [Submodule.comap_map_mkQ, sup_eq_right.2 hB'] at h2
  exact h2

theorem mem_bkAt_of_mem_bk : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (ψ : GE D →* (D.ntw.Ok i k)ˣ) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)), (∀ σ ∈ decAt D v, ψ σ = 1) → ∀ z : ReciprocityTheory.Gal.Z1 (Gen.Trep i s k ψ), ReciprocityTheory.Gal.resH1 (Gen.Trep i s k ψ) (decAt D v).subtype continuous_subtype_val (Submodule.Quotient.mk z) ∈ Gen.bk (bk0 D) i s k ψ v → (z : GE D → Fin D.R.r → KmodO (D.ntw.Ok i k)) ∈ bkAt (D.ntwbr i v hv) (D.loc (D.ntw.l i)) (toOk D i k) (latT D i s) := by
  intro D i s k ψ v hv hψ z hz
  replace hz := ((Gen.bk.eq_1 (bk0 D) i s k ψ v).trans (dif_pos hv)).le hz
  refine mem_of_mk_mem_span ((Gen.Trep i s k ψ).comp (decAt D v).subtype)
    (crysSpan (D.ntwbr i v hv) (D.loc (D.ntw.l i)) (toOk D i k) (latT D i s) ⊔
      cobOn ((Formalism.MainNotions.N.mapRep (toOk D i k) (latT D i s)).comp (decAt D v).subtype) ⊤) ?_ _ ?_
    (restrictCocycles1 (Gen.Trep i s k ψ) (decAt D v).subtype continuous_subtype_val z) hz
  · intro x
    refine Submodule.mem_sup_right ⟨x, fun g _ => ?_⟩
    exact congrArg (· - x) (Trep_eq_actDiv D i s k ψ g (hψ g g.2) x)
  · rintro x ⟨w, c, y, hc, hy, hw, hx⟩
    refine ⟨w, Submodule.mem_sup_left ?_, hx⟩
    exact mem_crysSpan_of_rational (D.ntwbr i v hv) (D.loc (D.ntw.l i))
      (toOk D i k) ((D.ntw.Ok_inj i k).comp (D.ntw.O_inj i)) (latT D i s) c hc y hy _ hw

end GlobalTheory.BlochKatoIntegralScalars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFiniteStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerBettiModule_free_finite : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → Module.Free ℤ_[l] (X.B N l w) ∧ Module.Finite ℤ_[l] (X.B N l w) := by
  first | exact @GlobalTheory.KZ.B_free_finite | exact GlobalTheory.KZ.B_free_finite | (intros; apply GlobalTheory.KZ.B_free_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRelatedPairFstEqZeroOfTrivialStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerRelatedPair_fst_eq_zero_of_trivial : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E], CharZero E → ∀ (y : E ⊗[ℤ_[l]] X.Fn l) (G : ℂ → MvPolynomial (Fin 2) E), (y, G) ∈ H3.abelian₂ X l E → G ∈ Triv E w (Gam N l) → y = 0 := by
  first | exact @GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv | exact GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv | (intros; apply GlobalTheory.KZ.H3.LamInj.fst_eq_zero_of_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowerTriIntegral
section
open MvPolynomial

namespace GlobalTheory.WeylInt

open Formalism.GradedWeylDivisibility

theorem lowerTri_of_interlaced {r n : ℕ} {m : Fin r × Fin n →₀ ℕ} (h : Interlaced m) : LowerTri m := by
  have key : ∀ (k : ℕ) (hk : k < n) (a : Fin r), a.val < k → m (a, ⟨k, hk⟩) = 0 := by
    intro k
    induction k with
    | zero => intro hk a ha; omega
    | succ k ih =>
      intro hk a ha
      have h1 := h ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl a
      have h2 : (∑ b : Fin r with b < a, m (b, ⟨k, by omega⟩)) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ih _ b ?_
        have : b.val < a.val := (Finset.mem_filter.mp hb).2
        omega
      rw [h2] at h1
      have h3 : m (a, ⟨k + 1, hk⟩) ≤ ∑ b : Fin r with b ≤ a, m (b, ⟨k + 1, hk⟩) :=
        Finset.single_le_sum (f := fun b : Fin r => m (b, ⟨k + 1, hk⟩)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)
      omega
  intro a s has
  exact key s.val s.2 a has

theorem intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = MvPolynomial.map (Int.castRingHom ℚ) P := rfl

theorem intQ_bidet {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    intQ r n (bideterminant ℤ sz hsz I) = bideterminant ℚ sz hsz I := by
  rw [intQ_apply]
  simp only [bideterminant, initMinor, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  ext1 i j
  simp

theorem lowerTriIntegral : Formalism.GradedWeylDivisibility.LowerTriIntegral := by
  intro r n ν
  suffices key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl ℚ r n ν,
      (colLex r n).toSyn ((colLex r n).degree f) = d →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e f = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, f = intQ r n Q' by
    intro f hf hint
    exact key _ f hf rfl hint
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro f hf hd hz
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    set m := (colLex r n).degree f with hm
    have hint : Interlaced m := leadInterlaced ℚ r n ν f hf hf0
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
      colSums ℚ r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
    obtain ⟨K, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
    obtain ⟨hdeg, hlc⟩ := column_lex_bideterminant ℚ r n K sz hsz I hmono
    have hmem : bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν := by
      have := bidetMem ℚ r n K sz hsz I
      rwa [hshape] at this
    obtain ⟨z, hzm⟩ := hz m (lowerTri_of_interlaced hint)
    have hlcf : (colLex r n).leadingCoeff f = (z : ℚ) := hzm
    set f' := f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I with hf'
    have hf'mem : f' ∈ dualWeyl ℚ r n ν := Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hmem)
    have hb : (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = intQ r n (z • bideterminant ℤ sz hsz I) := by
      rw [map_smul, intQ_bidet, hlcf, Int.cast_smul_eq_zsmul]
    have hdecomp : f = f' + intQ r n (z • bideterminant ℤ sz hsz I) := by
      rw [hf', ← hb]; abel
    have hQ : ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, f' = intQ r n Q' := by
      by_cases h0 : f' = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant ℚ sz hsz I) (hdeg.trans hexp) hlc h0
      refine ih _ (hd ▸ hlt) f' hf'mem rfl fun e he => ?_
      obtain ⟨w, hw⟩ := hz e he
      refine ⟨w - coeff e (z • bideterminant ℤ sz hsz I), ?_⟩
      rw [hf', hb, coeff_sub, hw, intQ_apply, coeff_map]
      simp only [Int.cast_sub, eq_intCast]
    obtain ⟨Q', hQ'⟩ := hQ
    exact ⟨Q' + z • bideterminant ℤ sz hsz I, by rw [map_add, ← hQ']; exact hdecomp⟩

end GlobalTheory.WeylInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddWeightModularCuspDimensionLowerBoundStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddWeight_modular_cusp_dimension_lower_bound : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k → FiniteDimensional ℂ (ModularForm Γ (k : ℤ)) ∧ FiniteDimensional ℂ (CuspForm Γ (k : ℤ)) ∧ (k - 1) * Γ.index ≤ 12 * (Module.finrank ℂ (ModularForm Γ (k : ℤ)) + Module.finrank ℂ (CuspForm Γ (k : ℤ))) := by
  first | exact @GlobalTheory.OddFrame.dim_lower_bound | exact GlobalTheory.OddFrame.dim_lower_bound | (intros; apply GlobalTheory.OddFrame.dim_lower_bound <;> assumption)
end

