import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0050
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatch
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial

theorem exists_linear_factors_indexed {ι : Type} [DecidableEq ι] (F : Finset ι) :
    ∀ P : ℂ[X], P.Monic → P.natDegree = F.card → ∃ r : ι → ℂ, P = ∏ a ∈ F, (X - C (r a)) := by
  induction F using Finset.induction_on with
  | empty =>
    intro P hm hd
    refine ⟨fun _ => 0, ?_⟩
    simpa using eq_one_of_monic_natDegree_zero hm (by simpa using hd)
  | insert a F ha ih =>
    intro P hm hd
    rw [Finset.card_insert_of_notMem ha] at hd
    have hdeg : P.degree ≠ 0 := by
      intro h
      have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr h.le
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hdeg
    obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hz
    have hmQ : Q.Monic := by
      have h := hm
      rw [hQ] at h
      exact (monic_X_sub_C z).of_mul_monic_left h
    have hdQ : Q.natDegree = F.card := by
      have h := congrArg natDegree hQ
      rw [(monic_X_sub_C z).natDegree_mul hmQ, natDegree_X_sub_C] at h
      omega
    obtain ⟨r, hr⟩ := ih Q hmQ hdQ
    refine ⟨Function.update r a z, ?_⟩
    rw [Finset.prod_insert ha, Function.update_self, hQ, hr]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [Function.update_of_ne (fun h : b = a => ha (h ▸ hb))]

theorem exists_perm_of_monic_factors (n M : ℕ) (lev : Fin n → ℕ) (χ : Fin n → ℂ) (P : Fin M → ℂ[X]) (s : Fin M → ℂ)
    (hlev : ∀ a, lev a < M)
    (hP : ∀ i, (P i).Monic ∧ (P i).natDegree = (univ.filter fun a => lev a = (i : ℕ)).card)
    (hcap : ∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin M,
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
        (P i).nextCoeff + ((univ.filter fun a => lev a = (i : ℕ)).card : ℂ) * s i := by
  choose r hr using fun i => exists_linear_factors_indexed _ (P i) (hP i).1 (hP i).2
  let lv : Fin n → Fin M := fun a => ⟨lev a, hlev a⟩
  let g : Fin n → ℂ := fun a => s (lv a) - r (lv a) a
  have hfil : ∀ i : Fin M, (univ.filter fun a => lev a = (i : ℕ)) = univ.filter fun a => lv a = i := by
    intro i
    ext a
    simp [lv, Fin.ext_iff]
  have hg : ∀ i : Fin M, ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)), g a = s i - r i a := by
    intro i a ha
    have : lv a = i := by
      rw [hfil] at ha
      exact (Finset.mem_filter.mp ha).2
    simp only [g, this]
  have hpoly : ∀ Y, Formalism.QuantumDeterminants.capP g Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    rw [← hcap Y]
    unfold Formalism.QuantumDeterminants.capP
    rw [← Finset.prod_fiberwise univ lv]
    refine Finset.prod_congr rfl fun i _ => ?_
    conv_rhs => rw [hr i, eval_prod]
    rw [hfil i]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [← hfil i] at ha
    rw [hg i a ha]
    simp only [eval_sub, eval_X, eval_C]
    ring
  obtain ⟨σ, hσ⟩ := GlobalTheory.CompanionTheory.CharOfLowK.exists_perm_of_capelliPolynomial_eq g χ hpoly
  refine ⟨σ, fun i => ?_⟩
  have h1 : ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (s i - r i a) :=
    Finset.sum_congr rfl fun a ha => by rw [← hσ a, hg i a ha]
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  conv_rhs => rw [hr i, prod_X_sub_C_nextCoeff]
  ring

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CenterActionCommutesLeviDifference
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem ev_fa {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (Y : ℂ) :
    ev E (fa n Y) = qdet E (Y + ((n : ℂ) - 1) / 2) := by
  unfold fa
  rw [map_qdet]
  congr 1
  funext p q
  simp [ev]

theorem evL_fb {n M : ℕ} (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n)
    (hlev : ∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ))
    {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (Y : ℂ) :
    evL lev E (fb d h Y) = (List.ofFn fun i : Fin M =>
      qdet (fun p q : Fin (d i) => E (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩))
        (Y + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2)).prod := by
  unfold fb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp]
  rw [map_qdet, shift, add_sub_assoc]
  congr 1
  funext p q
  simp [evL, hlev]

theorem span_apply_sum {n : ℕ} (lev : Fin n → ℕ) (hm : Monotone lev) {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (r : Fin n → Fin n → Prop) (hr : ∀ p q, r p q → lev p < lev q)
    {y : Module.End ℂ V}
    (hy : y ∈ Submodule.span ℂ {y : Module.End ℂ V | ∃ (p q : Fin n) (w : Module.End ℂ V), r p q ∧ y = E p q * w})
    (x : V) : ∃ w : Pos n → V, y x = ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, hpq, rfl⟩ := hy
    have hl := hr p q hpq
    have hlt : p < q := by
      by_contra hc
      exact absurd (hm (not_lt.mp hc)) (not_le.mpr hl)
    classical
    refine ⟨Pi.single (⟨(p, q), hlt⟩ : Pos n) (w x), ?_⟩
    rw [Finset.sum_eq_single (⟨(p, q), hlt⟩ : Pos n)]
    · simp [inU, hl]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [LinearMap.add_apply, hu, hv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  | smul c a _ ha =>
    obtain ⟨u, hu⟩ := ha
    refine ⟨c • u, ?_⟩
    rw [LinearMap.smul_apply, hu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

theorem co_hyp : ∀ (n M : ℕ) (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n) (Y : ℂ), Monotone lev →
    (∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      (∀ i : Pos n, inU lev i → Commute (E i.1.1 i.1.2) (ev E (fa n Y))) ∧
      ∀ x : V, ∃ w : Pos n → V, ev E (fa n Y) x - evL lev E (fb d h Y) x =
        ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  intro n M lev d h Y hm hlev V _ _ E hE
  rw [ev_fa, evL_fb lev d h hlev]
  refine ⟨fun i _ => (Formalism.REAL.qDetCentral (Module.End ℂ V) n E hE _ i.1.1 i.1.2).symm, fun x => ?_⟩
  have hlevb : ∀ p : Fin n, lev p = ((blk (stdBlocks d h) p : Fin M) : ℕ) := by
    intro p
    have := hlev ((stdBlocks d h).symm p).1 ((stdBlocks d h).symm p).2
    simpa [blk] using this
  have hc := GlobalTheory.CapHC.qdet_blocks_congr (Module.End ℂ V) d h E hE Y
  obtain ⟨w, hw⟩ := span_apply_sum lev hm E (fun p q => blk (stdBlocks d h) p < blk (stdBlocks d h) q)
    (fun p q hpq => by rw [hlevb p, hlevb q]; exact hpq) hc x
  exact ⟨w, by rw [← hw, LinearMap.sub_apply]⟩

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CuspidalTwistInjectiveImports
section

end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteTypeAlgebraCommonEigencharacter
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem exists_character_of_smul_ne_zero :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R] (W : Type) [AddCommGroup W]
      [Module ℂ W] [Module R W] [IsScalarTower ℂ R W] (t : W), t ≠ 0 →
      ∃ φ : R →ₐ[ℂ] ℂ, ∀ (r : R) (c : ℂ), r • t = c • t → φ r = c := by
  intro R _ _ _ W _ _ _ _ t ht
  let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R W t)
  have hmemJ : ∀ x : R, x ∈ J ↔ x • t = 0 := fun x => by
    simp [J, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ J := h ▸ Submodule.mem_top
    exact ht (by simpa using (hmemJ 1).1 h1)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℂ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ m) (Ideal.Quotient.mkₐ_surjective ℂ m)
  haveI : Module.Finite ℂ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (R ⧸ m)
  have bij : Function.Bijective (algebraMap ℂ (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] R ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ (R ⧸ m)) bij
  refine ⟨(e.symm : (R ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m), fun r c h => ?_⟩
  have hmem : r - algebraMap ℂ R c ∈ J := by
    rw [hmemJ, sub_smul, algebraMap_smul, h, sub_self]
  have hq : Ideal.Quotient.mkₐ ℂ m r = algebraMap ℂ (R ⧸ m) c := by
    have h0 : Ideal.Quotient.mk m (r - algebraMap ℂ R c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (hJm hmem)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have he : e c = algebraMap ℂ (R ⧸ m) c := rfl
  show e.symm (Ideal.Quotient.mkₐ ℂ m r) = c
  rw [hq, ← he, AlgEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.RgCOBlock
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
section
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.GradFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def pM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def qM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

theorem J_mul (h : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  obtain ⟨hg, hH, -, -⟩ := h
  have h0 : Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0 := hg
  rw [hH] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem A4 (h : A * A * A = A) : A * A * A * A = A * A := by rw [h]

theorem pM_idem (h : A * A * A = A) : pM A * pM A = pM A := by
  have h4 := A4 h
  unfold pM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, ← mul_assoc, h4, h]
  module

theorem pM_mul_qM (h : A * A * A = A) : pM A * qM A = 0 := by
  have h4 := A4 h
  unfold pM qM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add, add_mul, mul_sub, ← mul_assoc, h4, h]
  module

theorem J_mul_pM (h : IsGrad ε A) : Formalism.REAL.Jm ε * pM A = qM A * Formalism.REAL.Jm ε := by
  have hJ := J_mul h
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← mul_assoc, hJ, neg_mul, mul_assoc, hJ, mul_neg, neg_neg, mul_assoc]
  unfold pM qM
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, h2, hJ, sub_neg_eq_add]

theorem trace_qM (h : IsGrad ε A) : Matrix.trace (qM A) = Matrix.trace (pM A) := by
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
    rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
  rw [this, Matrix.trace_mul_comm, ← mul_assoc, hJJ, one_mul]

theorem pM_conjTranspose (h : Aᴴ = A) : (pM A)ᴴ = pM A := by
  unfold pM
  simp [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, h]

theorem isProj (h : A * A * A = A) : LinearMap.IsProj (Vm A) (Matrix.toLin' (pM A)) := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  change Matrix.toLin' (pM A) (Matrix.toLin' (pM A) y) = Matrix.toLin' (pM A) y
  rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, pM_idem h]

theorem trace_pM (h : A * A * A = A) : Matrix.trace (pM A) = (rk A : ℂ) := by
  have := (isProj h).trace
  rw [Matrix.trace_toLin'_eq] at this
  exact this

theorem one_le_rk (h : IsGrad ε A) : 1 ≤ rk A := by
  obtain ⟨-, -, h3, hA⟩ := id h
  by_contra hc
  have h0 : rk A = 0 := by omega
  have hb : Vm A = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hP : pM A = 0 := by
    have : Matrix.toLin' (pM A) = 0 := LinearMap.range_eq_bot.mp hb
    simpa using this
  have hQ : qM A = 0 := by
    have hJJ := Formalism.REAL.Jm_mul_self ε
    have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
      rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
    rw [this, hP]; simp
  apply hA
  have : A = qM A - pM A := by unfold pM qM; module
  rw [this, hP, hQ, sub_zero]

theorem isotropic (h : IsGrad ε A) {x y : Fin n → ℂ} (hx : x ∈ Vm A) (hy : y ∈ Vm A) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  obtain ⟨-, hH, h3, -⟩ := id h
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  change star (pM A *ᵥ u) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (pM A *ᵥ v)) = 0
  have hz : pM A * (Formalism.REAL.Jm ε * pM A) = 0 := by
    rw [J_mul_pM h, ← mul_assoc, pM_mul_qM h3, zero_mul]
  rw [star_mulVec, pM_conjTranspose hH, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, hz]
  simp

theorem flagFacts : FlagFacts := by
  intro n ε A h
  obtain ⟨-, -, h3, -⟩ := id h
  refine ⟨one_le_rk h, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [W]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h0 : W A 0 = ⊥ := rfl
    have h1 : W A 1 = Vm A := rfl
    change Module.finrank ℂ (W A 1) = Module.finrank ℂ (W A 0) + rk A
    rw [h0, h1, finrank_bot, zero_add]
    rfl
  · intro x hx y hy
    exact isotropic h hx hy
  · have hj : (Matrix.trace ((1 / 2 : ℂ) • (A * A + A))).re = (rk A : ℝ) := by
      change (Matrix.trace (qM A)).re = _
      rw [trace_qM h, trace_pM h3]
      simp
    unfold rhoA
    simp only [hj]

end GlobalTheory.CompanionTheory.GradFlag
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotient
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.QuotAction

theorem descends (C : Type) [AddCommGroup C] [Module ℂ C] (L : Type) (l : L → Module.End ℂ C)
    (Z B : Submodule ℂ C) (hZ : ∀ k, ∀ z ∈ Z, l k z ∈ Z) (hB : ∀ k, ∀ z ∈ B, l k z ∈ B) :
    ∃ ρ : FreeAlgebra ℂ L →ₐ[ℂ] Module.End ℂ (Z ⧸ B.comap Z.subtype),
      ∀ (y : FreeAlgebra ℂ L) (z : Z), ∃ hz : FreeAlgebra.lift ℂ l y (z : C) ∈ Z,
        ρ y (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk ⟨FreeAlgebra.lift ℂ l y (z : C), hz⟩ := by
  let lZ : L → Module.End ℂ Z := fun k => (l k).restrict (hZ k)
  have hBl : ∀ k, B.comap Z.subtype ≤ (B.comap Z.subtype).comap (lZ k) := by
    intro k z hz
    show Z.subtype (lZ k z) ∈ B
    exact hB k z hz
  let lQ : L → Module.End ℂ (Z ⧸ B.comap Z.subtype) :=
    fun k => (B.comap Z.subtype).mapQ (B.comap Z.subtype) (lZ k) (hBl k)
  have hP : ∀ (y : FreeAlgebra ℂ L) (z : Z),
      FreeAlgebra.lift ℂ l y (z : C) = ((FreeAlgebra.lift ℂ lZ y z : Z) : C) := by
    intro y
    induction y using FreeAlgebra.induction
    · intro z; simp
    · intro z; rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]; rfl
    · rename_i a b ha hb
      intro z; simp only [map_mul, Module.End.mul_apply, hb, ha]
    · rename_i a b ha hb
      intro z; simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  have hQ : ∀ (y : FreeAlgebra ℂ L) (z : Z),
      FreeAlgebra.lift ℂ lQ y (Submodule.Quotient.mk z) = Submodule.Quotient.mk (FreeAlgebra.lift ℂ lZ y z) := by
    intro y
    induction y using FreeAlgebra.induction
    · intro z; simp
    · intro z; rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]; rfl
    · rename_i a b ha hb
      intro z; simp only [map_mul, Module.End.mul_apply, hb, ha]
    · rename_i a b ha hb
      intro z; simp only [map_add, LinearMap.add_apply, Submodule.Quotient.mk_add, ha, hb]
  refine ⟨FreeAlgebra.lift ℂ lQ, fun y z => ⟨by rw [hP y z]; exact (FreeAlgebra.lift ℂ lZ y z).2, ?_⟩⟩
  rw [hQ y z]
  congr 1
  exact Subtype.ext (hP y z).symm

end GlobalTheory.CompanionTheory.RgCOBlock.QuotAction
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionPreservesSupportDegree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp

open Finset
open CompanionTheory.D.LK (Pos Cn ann cre lift sg)
open CompanionTheory.RgExh.U

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_ann_ne (i k : Pos n) (x : Cn n V) (A : Finset (Pos n))
    (h : (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0) :
    k ∈ A ∧ i ∉ A.erase k ∧ x (insert i (A.erase k)) ≠ 0 := by
  change (if k ∈ A then sg k A • (if i ∈ A.erase k then 0 else
    sg i (A.erase k) • x (insert i (A.erase k))) else 0) ≠ 0 at h
  by_cases hk : k ∈ A
  · by_cases hi : i ∈ A.erase k
    · rw [if_pos hk, if_pos hi, smul_zero] at h
      exact absurd rfl h
    · refine ⟨hk, hi, fun hx => ?_⟩
      rw [if_pos hk, if_neg hi, hx, smul_zero, smul_zero] at h
      exact h rfl
  · rw [if_neg hk] at h
    exact absurd rfl h

theorem lF_ne (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cn n V) (A : Finset (Pos n))
    (h : lF E p q x A ≠ 0) :
    x A ≠ 0 ∨ ∃ i k : Pos n, adC p q i k ≠ 0 ∧ (cre k * ann i : Module.End ℂ (Cn n V)) x A ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, hall⟩ := hcon
  apply h
  change ((lift n (E p q) + adL p q : Module.End ℂ (Cn n V)) x) A = 0
  rw [LinearMap.add_apply, Pi.add_apply, CompanionTheory.D.LK.lift_apply, h0, map_zero, zero_add]
  unfold adL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply]
  by_cases hc : adC p q i k = 0
  · rw [hc, zero_smul]
  · rw [hall i k hc, smul_zero]

theorem inU_of_adC {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {i k : Pos n}
    (h : adC p q i k ≠ 0) (hi : inU lev i) : inU lev k := by
  unfold adC at h
  unfold inU at hi ⊢
  by_cases h1 : q = (i : Fin n × Fin n).1 ∧ (k : Fin n × Fin n) = (p, (i : Fin n × Fin n).2)
  · rw [h1.2]
    show lev p < lev (i : Fin n × Fin n).2
    rw [hpq, h1.1]
    exact hi
  · by_cases h2 : (i : Fin n × Fin n).2 = p ∧ (k : Fin n × Fin n) = ((i : Fin n × Fin n).1, q)
    · rw [h2.2]
      show lev (i : Fin n × Fin n).1 < lev q
      rw [← hpq, ← h2.1]
      exact hi
    · rw [if_neg h1, if_neg h2, sub_zero] at h
      exact absurd rfl h

theorem lF_suppIn_deg (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (_hlev : Monotone lev) (x : Cn n V)
    (hx : SuppIn (inU lev) x) (p q : Fin n) (hpq : lev p = lev q) :
    SuppIn (inU lev) (lF E p q x) ∧ ∀ j, Deg j x → Deg j (lF E p q x) := by
  unfold SuppIn at hx ⊢
  unfold Deg
  constructor
  · intro A hA l hl
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hx A h0 l hl
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hsupp := hx _ hx'
      by_cases hlk : l = k
      · subst hlk
        exact inU_of_adC hpq hc (hsupp i (Finset.mem_insert_self _ _))
      · exact hsupp l (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hlk, hl⟩))
  · intro j hj A hA
    rcases lF_ne E p q x A hA with h0 | ⟨i, k, hc, hne⟩
    · exact hj A h0
    · obtain ⟨hk, hi, hx'⟩ := cre_ann_ne i k x A hne
      have hcard := hj _ hx'
      rw [Finset.card_insert_of_notMem hi, Finset.card_erase_of_mem hk] at hcard
      have hpos : 0 < A.card := Finset.card_pos.2 ⟨k, hk⟩
      omega

end GlobalTheory.CompanionTheory.RgCOBlock.LeviSupp
end
end

