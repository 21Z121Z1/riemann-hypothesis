import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInert
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.UnitInert

section Local

variable {O : Type} [CommRing O] [IsNoetherianRing O] {r : ℕ}

theorem exists_unitary_conj (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] {σ : O →+* O}
    (hσ : ∀ a, σ (σ a) = a) (hI : ∀ x ∈ I, σ x ∈ I) (hω : ∃ ω, IsUnit (ω - σ ω))
    {g h : Matrix (Fin r) (Fin r) O} (hg : cT σ g * g = 1) (hh : cT σ h * h = 1)
    (hs : g.charpoly.Separable) (e : h.charpoly = g.charpoly) :
    ∃ u : GL (Fin r) O, cT σ u.1 * u.1 = 1 ∧ g * u = u * h := by
  have hjac := IsAdicComplete.le_jacobson_bot I
  obtain ⟨v, hv⟩ := GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := g) hs
  obtain ⟨w, hw⟩ := GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := h) (show h.charpoly.Separable by rwa [e])
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have hy : g * (a * b⁻¹ : GL (Fin r) O) = (a * b⁻¹ : GL (Fin r) O) * h := by
    have h1 := GlobalTheory.Orb.mul_krylov_eq g v
    have h2 := GlobalTheory.Orb.mul_krylov_eq h w
    rw [← ha] at h1
    rw [← hb, e] at h2
    rw [Units.val_mul, ← mul_assoc, h1, Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, h2,
      Units.inv_mul_cancel_left]
  generalize a * b⁻¹ = y at hy
  set s : Matrix (Fin r) (Fin r) O → Matrix (Fin r) (Fin r) O := cT σ with hsdef
  have hm : ∀ a b, s (a * b) = s b * s a := fun a b => cT_mul σ a b
  have hadd : ∀ a b, s (a + b) = s a + s b := fun a b => Matrix.ext fun i j => by simp [s, cT]
  have hss : ∀ a, s (s a) = a := fun a => Matrix.ext fun i j => by simp [s, cT, hσ]
  have hsc : ∀ c : O, s (algebraMap O _ c) = algebraMap O _ (σ c) := fun c => by
    ext i j
    simp only [s, cT, transpose_apply, map_apply, algebraMap_matrix_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h1 : s 1 = 1 := by simpa using hsc 1
  change s g * g = 1 at hg
  change s h * h = 1 at hh
  let C := Subalgebra.centralizer O ({h} : Set (Matrix (Fin r) (Fin r) O))
  have hC : ∀ {a}, a ∈ C ↔ a * h = h * a := by simp [C, Subalgebra.mem_centralizer_iff, eq_comm]
  let _ : CommRing C :=
    { (inferInstance : Ring C) with
      mul_comm := fun a b => Subtype.ext (by
        obtain ⟨p, hp⟩ := GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 a.2)
        obtain ⟨q, hq⟩ := GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 b.2)
        rw [C.coe_mul, C.coe_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]) }
  have : Module.Finite O (Matrix (Fin r) (Fin r) O) := inferInstanceAs (Module.Finite O (Fin r → Fin r → O))
  have : Module.Finite O C := Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite I C
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite I C
  have hsC : ∀ a ∈ C, s a ∈ C := fun a ha => hC.2 (by
    have h2 := congrArg s (hC.1 ha)
    rw [hm, hm] at h2
    calc s a * h = h * (s h * s a) * h := by rw [← mul_assoc, mul_eq_one_comm.1 hh, one_mul]
      _ = h * s a := by rw [h2, mul_assoc, mul_assoc, hh, mul_one])
  let t : C →+* C :=
    { toFun := fun a => ⟨s a, hsC _ a.2⟩
      map_one' := Subtype.ext h1
      map_mul' := fun a b => by rw [mul_comm a b]; exact Subtype.ext (hm _ _)
      map_zero' := Subtype.ext (by simpa using hsc 0)
      map_add' := fun a b => Subtype.ext (hadd _ _) }
  have hιR : ∀ c, t (algebraMap O C c) = algebraMap O C (σ c) := fun c => Subtype.ext (hsc c)
  have hl : s y * y ∈ C := hC.2 (by
    have h2 : s h * (s y * y) * h = s y * y := by
      rw [← mul_assoc, ← hm, mul_assoc, ← hy, hm, mul_assoc, ← mul_assoc (s g), hg, one_mul]
    conv_rhs => rw [← h2, ← mul_assoc, ← mul_assoc, mul_eq_one_comm.1 hh, one_mul])
  have hlu : (s y * y) * ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) = 1 := by
    rw [mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.inv_mul, h1]
  have hl' : ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) ∈ C := hC.2 (by
    have h2 := mul_eq_one_comm.1 hlu
    exact (Commute.units_inv_left (u := ⟨_, _, hlu, h2⟩) (hC.1 hl)).eq)
  obtain ⟨ω, hω⟩ := hω
  obtain ⟨z, hz⟩ := GlobalTheory.HenselianNorm.exists_norm_eq C (I.map (algebraMap O C)) t (fun a => Subtype.ext (hss _))
    (fun x hx => (show I.map (algebraMap O C) ≤ (I.map (algebraMap O C)).comap t from Ideal.map_le_iff_le_comap.2
      fun c hc => by
        rw [Ideal.mem_comap, Ideal.mem_comap, hιR]
        exact Ideal.mem_map_of_mem _ (hI c hc)) hx)
    ⟨algebraMap O C ω, by rw [hιR, ← map_sub]; exact hω.map _⟩ ⟨_, hl'⟩ (Subtype.ext (by
      change s _ = _
      rw [hm, hss])) (IsUnit.of_mul_eq_one_right ⟨_, hl⟩ (Subtype.ext hlu))
  have hz' : z.1 * s z.1 = (y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O) := congrArg Subtype.val hz
  have h3 : (y * z.1) * s (y * z.1) = 1 := by
    rw [hm, mul_assoc, ← mul_assoc z.1, hz', mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.mul_inv, h1]
  refine ⟨⟨_, _, h3, mul_eq_one_comm.1 h3⟩, mul_eq_one_comm.1 h3, ?_⟩
  change g * (y * z.1) = y * z.1 * h
  rw [← mul_assoc, hy, mul_assoc, mul_assoc, hC.1 z.2]

end Local

end GlobalTheory.BCT.UnitInert

namespace GlobalTheory.BCT.UnitInert

variable {E : Type} [Field E] [NumberField E]

theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

theorem eventually_lift (p : E[X]) : ∀ᶠ w : Pl E in cofinite, ∃ q : (w.adicCompletionIntegers E)[X],
    q.map (algebraMap _ (w.adicCompletion E)) = atPl w p := by
  have h : ∀ᶠ w : Pl E in cofinite, ∀ i ∈ p.support,
      algebraMap E (w.adicCompletion E) (p.coeff i) ∈ w.adicCompletionIntegers E := by
    rw [eventually_all_finset]
    exact fun i _ => eventually_int _
  filter_upwards [h] with w hw
  refine (Polynomial.mem_lifts _).1 ((Polynomial.lifts_iff_coeff_lifts _).2 fun i => ?_)
  rw [coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hw i hi⟩, rfl⟩
  · rw [notMem_support_iff.1 hi, map_zero]
    exact ⟨0, map_zero _⟩

theorem eventually_separable (P : E[X]) (hP : P.Separable) : ∀ᶠ w : Pl E in cofinite,
    ∀ q : (w.adicCompletionIntegers E)[X], q.map (algebraMap _ (w.adicCompletion E)) = atPl w P → q.Separable := by
  obtain ⟨u, v, huv⟩ := hP
  filter_upwards [eventually_lift u, eventually_lift v] with w ⟨u', hu⟩ ⟨v', hv⟩ q hq
  refine ⟨u', v', Polynomial.map_injective (algebraMap _ (w.adicCompletion E)) Subtype.val_injective ?_⟩
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, hq, hu, hv,
    Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, huv,
    Polynomial.map_one, Polynomial.map_one]

theorem conj_of_charpoly_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w →
      γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ hU n _ P hP
  filter_upwards [eventually_separable P hP.2.2.1] with w hsep hw γ γ' hγK hγ'K hγ hγ'
  let O := w.adicCompletionIntegers E
  let ι := algebraMap O (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) O, GeneralLinearGroup.map ι y' = γ.1 := (Subgroup.mem_subgroupOf.1 hγK)
  obtain ⟨z', hz'⟩ : ∃ z' : GL (Fin n) O, GeneralLinearGroup.map ι z' = γ'.1 := (Subgroup.mem_subgroupOf.1 hγ'K)
  obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
  have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
  let c : O →+* O := (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
  have hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι) := fun M => by
    ext i j; rfl
  have hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1 := fun x => by
    rw [UL, if_neg hw]
    change cT (cj w) x.val * 1 * x.val = 1 ↔ _
    rw [mul_one]
  have hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι := fun x => by
    ext i j; rfl
  have hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1 := fun x hx => by
    refine Matrix.map_injective hι ?_
    show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι
    rw [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]
    exact (hUL _).1 hx
  have hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly := fun x =>
    (Matrix.charpoly_map _ _).symm
  have e1 : y'.val.charpoly.map ι = atPl w P := by rw [hch, hy', hγ]
  have e2 : z'.val.charpoly.map ι = atPl w P := by rw [hch, hz', hγ']
  obtain ⟨u, hu, hcu⟩ := exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc
    (fun x hx => by
      rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
      exact (hv _).trans_lt hx)
    ⟨⟨x₀, hx₀⟩, by
      rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
      change ¬ Valued.v (x₀ - cj w x₀) < 1
      rw [Valuation.map_sub_swap, hx₁]
      exact lt_irrefl _⟩
    (hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1)
    (Polynomial.map_injective ι hι (e2.trans e1.symm))
  let g : GLw n w := GeneralLinearGroup.map ι u
  have hg : g ∈ UL n w := by
    rw [hUL]
    have := congrArg (fun M => M.map ι) hu
    simp only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this
    exact this
  have key : γ.1 * g = g * γ'.1 := by
    rw [← hy', ← hz', ← map_mul, ← map_mul]
    congr 1
    exact Units.ext hcu
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  change γ'.1 = g⁻¹ * γ.1 * g
  rw [mul_assoc, key, inv_mul_cancel_left]

end GlobalTheory.BCT.UnitInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSoluti
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.TransportBack

open Matrix

theorem map_mul_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k p : Type*} [Fintype k]
    (X : Matrix m k R) (Y : Matrix k p R) : (X * Y).map f = X.map f * Y.map f := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem map_mulVec_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*} [Fintype k]
    (X : Matrix m k R) (a : k → R) : X.map f *ᵥ (fun i => f (a i)) = fun i => f ((X *ᵥ a) i) := by
  ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem map_add_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*}
    (X Y : Matrix m k R) : (X + Y).map f = X.map f + Y.map f := by
  ext i j; simp

theorem map_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (1 : Matrix n n R).map ι = ι 1 • (1 : Matrix n n S) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_neg_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (-1 : Matrix n n R).map ι = -(ι 1 • (1 : Matrix n n S)) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem assoc_a {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (D : Matrix d e R) :
    A * B * C * D = A * (B * (C * D)) := by simp only [Matrix.mul_assoc]

theorem assoc_b {R : Type*} [CommRing R] {a b c d : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (P₁ Y Q₁ P₂ : Matrix d d R) :
    A * B * C * (P₁ * Y * Q₁) * P₂ = A * (B * (C * (P₁ * (Y * (Q₁ * P₂))))) := by
  simp only [Matrix.mul_assoc]

theorem smul_mid_of {R : Type*} [CommRing R] {a b d : Type*} [Fintype b] [DecidableEq b]
    (s : R) (A : Matrix a b R) (B : Matrix b b R) (C : Matrix b d R) (h : s • B = s • 1) :
    s • (A * B * C) = s • (A * C) := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem smul_last_of {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (s : R) (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (Z : Matrix d e R) (h : s • Z = 0) :
    s • (A * B * C * Z) = 0 := by
  rw [← Matrix.mul_smul, h, Matrix.mul_zero]

end GlobalTheory.TransportBack

namespace GlobalTheory.TransportBack
open Matrix

theorem transport_back : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl F) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* AE F E)
    (P Q : Matrix (Fin n) (Fin n) (AE F E)) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ n X v O _ c ι P Q JL hAe he hc hPQ hQP heP heQ hJ hlat M G ZL hM hMG hZL hN
  have heι : ∀ x, ι 1 * ι x = ι x := fun x => by rw [← map_mul, one_mul]
  have hιe : ∀ x, ι x * ι 1 = ι x := fun x => by rw [← map_mul, mul_one]
  have hee : ι 1 * ι 1 = ι 1 := heι 1
  have hce : cA σ (ι 1) = ι 1 := by rw [hc, map_one]
  have hmapE : ∀ {m k : Type} (Y : Matrix m k O), ι 1 • Y.map ι = Y.map ι := by
    intro m k Y; ext i j; simp [heι]
  have hePY : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n) k (AE F E)), ι 1 • (P * Y) = P * Y := by
    intro k _ Y; rw [← Matrix.smul_mul, heP]
  have hZP : P * ZL.map ι * Q * P = P * ZL.map ι := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_smul, Matrix.mul_one, hePY]
  have hvec : ∀ a : Fin n → O, Q *ᵥ (P *ᵥ fun i => ι (a i)) = fun i => ι (a i) := by
    intro a; rw [Matrix.mulVec_mulVec, hQP, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp [heι]

  have hAtZ : At (evFin F v) (P * ZL.map ι * Q) := by
    intro u hu
    have hu' : u • Q = 0 := by rw [← heQ, ← smul_assoc, hAe u hu, zero_smul]
    rw [← Matrix.mul_smul, hu', Matrix.mul_zero]

  have hlatZ : ∀ z ∈ GlobalTheory.InertSph.latAt X v, (P * ZL.map ι * Q) *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
    intro z hz
    obtain ⟨a, rfl⟩ := (hlat z).1 hz
    refine (hlat _).2 ⟨ZL *ᵥ a, ?_⟩
    rw [Matrix.mulVec_mulVec, hZP, ← Matrix.mulVec_mulVec, map_mulVec_gen]

  have hPcQc : P.map (cA σ) * Q.map (cA σ) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [← map_mul_gen, hPQ]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h, hce]
  have h1 : Pᵀ * incM F X.J = JL.map ι * Q.map (cA σ) := by
    calc Pᵀ * incM F X.J = ι 1 • (Pᵀ * incM F X.J) := by
            rw [← Matrix.smul_mul, ← Matrix.transpose_smul, heP]
      _ = Pᵀ * incM F X.J * (P.map (cA σ) * Q.map (cA σ)) := by
            rw [hPcQc, Matrix.mul_smul, Matrix.mul_one]
      _ = JL.map ι * Q.map (cA σ) := by rw [← Matrix.mul_assoc, hJ]
  have hPc : ι 1 • P.map (cA σ) = P.map (cA σ) := by
    conv_rhs => rw [← heP]
    ext i j; simp [hce]
  have h2 : incM F X.J * P.map (cA σ) = Qᵀ * JL.map ι := by
    calc incM F X.J * P.map (cA σ) = ι 1 • (incM F X.J * P.map (cA σ)) := by
            rw [← Matrix.mul_smul, hPc]
      _ = (P * Q)ᵀ * incM F X.J * P.map (cA σ) := by
            rw [hPQ, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.smul_mul,
              Matrix.one_mul]
      _ = Qᵀ * JL.map ι := by
            rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, hJ]
  have hmapc : (ZL.map ι).map (cA σ) = (ZL.map c).map ι := by
    rw [Matrix.map_map, Matrix.map_map]; congr 1; funext x; exact hc x
  have hJZ : (P * ZL.map ι * Q)ᵀ * incM F X.J + incM F X.J * (P * ZL.map ι * Q).map (cA σ) = 0 := by
    have hz0 : (ZLᵀ * JL + JL * ZL.map c).map ι = 0 := by rw [hZL]; ext i j; simp
    rw [map_add_gen, map_mul_gen, map_mul_gen, Matrix.transpose_map] at hz0
    rw [map_mul_gen, map_mul_gen, hmapc, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc (incM F X.J), h2]
    calc _ = Qᵀ * ((ZL.map ι)ᵀ * JL.map ι + JL.map ι * (ZL.map c).map ι) * Q.map (cA σ) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hz0]; simp

  set N := ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL with hNdef
  set K := (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * ZL.map ι * Q) with hK
  have hNab : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (-(ι 1 • 1)) := by
    rw [Matrix.fromRows_map, map_one_eq, map_neg_one_eq]
  have hDel : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (ι 1 • 1) := by
    rw [Matrix.fromRows_map, map_one_eq]
  have hanti : GlobalTheory.DblVac.antiCols (F := F) (E := E) n * P = Matrix.fromBlocks P 0 0 P * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι := by
    rw [hNab, GlobalTheory.DblVac.antiCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hdiag : ∀ Y : Matrix (Fin n) (Fin n) (AE F E), (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * Y) = Matrix.fromBlocks P 0 0 P * ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDel, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hantiT : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * (Matrix.fromBlocks P 0 0 P * Y) = P * (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι)ᵀ * Y) := by
    intro k _ Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNab, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_fromRows,
      Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols]
    simp [Matrix.mul_smul, heP]
  have hMG' : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), M * (Matrix.fromBlocks P 0 0 P * Y) = Matrix.fromBlocks P 0 0 P * (G.map ι * Y) := by
    intro k _ Y; rw [← Matrix.mul_assoc, hMG, Matrix.mul_assoc]
  have hQPι : ZL.map ι * (Q * P) = ZL.map ι := by rw [hQP, Matrix.mul_smul, Matrix.mul_one, hmapE]
  have hKP : K * P = P * N.map ι := by
    rw [hK, Matrix.add_mul]
    refine (congrArg₂ (· + ·) (assoc_a _ _ _ _) (assoc_b _ _ _ _ _ _ _)).trans ?_
    rw [hanti, hQPι, hdiag, hMG', hMG', hantiT, hantiT, hNdef]
    simp only [map_add_gen, map_mul_gen, Matrix.transpose_map, Matrix.mul_add, Matrix.mul_assoc]

  have hN1 : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hN
  have h2inv : algebraMap F (AE F E) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (AE F E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hMe : ι 1 • (M - 1) = M - 1 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    apply he
    intro u hu
    have := congrFun (congrFun (hM u hu) i) j
    simpa using this
  have hM1 : (1 - ι 1) • M = (1 - ι 1) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [sub_smul, one_smul, sub_smul, one_smul, ← sub_eq_zero,
      show M - ι 1 • M - (1 - ι 1 • 1) = (M - 1) - (ι 1 • M - ι 1 • 1) by abel, ← smul_sub, hMe, sub_self]
  have hZe : (1 - ι 1) • (P * ZL.map ι * Q) = 0 := by
    rw [sub_smul, one_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, heP, sub_self]
  have hAA : (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.antiCols n = (2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows]
    refine (Matrix.fromCols_mul_fromRows _ _ _ _).trans ?_
    simp [two_smul]
  have hKe : (1 - ι 1) • K = (1 - ι 1) • ((2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hK, smul_add]
    refine (congrArg₂ (· + ·) (smul_mid_of _ _ _ _ hM1) (smul_last_of _ _ _ _ _ hZe)).trans ?_
    rw [add_zero]
    exact congrArg _ hAA
  set R := (algebraMap F (AE F E) 2⁻¹ * (1 - ι 1)) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + P * N⁻¹.map ι * Q with hR
  have hKR : K * R = 1 := by
    have hsec : K * (P * N⁻¹.map ι * Q) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKP, Matrix.mul_assoc P, ← map_mul_gen, hN1, map_one_eq,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPQ, smul_smul, hee]
    rw [hR, Matrix.mul_add, hsec, Matrix.mul_smul, Matrix.mul_one, mul_smul, hKe, smul_smul, smul_smul, ← add_smul,
      show algebraMap F (AE F E) 2⁻¹ * (1 - ι 1) * 2 + ι 1 = (1 - ι 1) * (algebraMap F (AE F E) 2⁻¹ * 2) + ι 1 by ring,
      h2inv, mul_one, sub_add_cancel, one_smul]
  have hPz : ∀ w : Fin n → AE F E, (1 - ι 1) • (P *ᵥ w) = 0 := by
    intro w; rw [← Matrix.smul_mulVec, sub_smul, one_smul, heP, sub_self, Matrix.zero_mulVec]
  refine ⟨P * ZL.map ι * Q, hAtZ, hlatZ, hJZ, Matrix.isUnit_det_of_right_inverse hKR, ?_⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (hlat z).1 hz
  rw [Matrix.inv_eq_right_inv hKR]
  refine (hlat _).2 ⟨N⁻¹ *ᵥ a, ?_⟩
  rw [hR, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mul_smul, hPz, smul_zero, zero_add,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvec, map_mulVec_gen]

end GlobalTheory.TransportBack
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparableStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_GL_of_charpoly_eq_of_separable : ∀ (K : Type) [Field K] (n : ℕ) (a b : GL (Fin n) K), a.val.charpoly = b.val.charpoly → a.val.charpoly.Separable → ∃ h : GL (Fin n) K, b = h⁻¹ * a * h := by
  first | exact @GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable | exact GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable | (intros; apply GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfin
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RatPt

open GlobalTheory.BCT.TrKer GlobalTheory.BCT.FinPart

theorem coord_pInf_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (e : E) :
    coord v.embedding (pInf E (algebraMap E (Ad E) e)) = v.embedding e := by
  have hv : (InfinitePlace.mk v.embedding) = v := InfinitePlace.mk_embedding v
  have h : (InfinitePlace.mk v.embedding).embedding = v.embedding := by rw [hv]
  simp only [coord, h, if_true, Pi.evalRingHom_apply]
  rw [pInf_algebraMap, hv]

theorem ratGL_mem_UA {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : UE E n) :
    ratGL E n γ.1 ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  change cT (conjAd E) (ratGL E n γ.1).val * 1 * (ratGL E n γ.1).val = 1
  have hc : cT (conjAd E) (ratGL E n γ.1).val =
      (algebraMap E (Ad E)).mapMatrix (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val) := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact conjAd_algebraMap _
  have hr : (ratGL E n γ.1).val = (algebraMap E (Ad E)).mapMatrix γ.1.val := rfl
  rw [hc, hr, mul_one, ← map_mul, ← map_one (algebraMap E (Ad E)).mapMatrix, ← hγ, mul_one]

theorem ratPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), ∃ r ∈ ratU E n, splitFin E n r = finPt γ ∧ ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ.1 := by
  intro E _ _ _ n γ
  refine ⟨⟨ratGL E n γ.1, ratGL_mem_UA γ⟩, ⟨γ.1, rfl⟩, ?_, ?_⟩
  · set r : UA E n := ⟨ratGL E n γ.1, ratGL_mem_UA γ⟩
    have hpr : GeneralLinearGroup.map (pFin E) (ratGL E n γ.1) = ratF E n γ.1 := by
      apply Units.ext
      ext i j
      rfl
    have hi : (finPt γ).1⁻¹ * r ∈ infU E n := by
      rw [infU, MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_mul, map_inv, map_inv]
      change (pU (finPt γ))⁻¹ * GeneralLinearGroup.map (pFin E) (ratGL E n γ.1) = 1
      rw [pU_finPt, hpr, inv_mul_cancel]
    have he : r = (finPt γ).1 * (⟨_, hi⟩ : infU E n).1 := by
      simp only [mul_inv_cancel_left]
    rw [he, splitFin_mul]
  · intro v
    apply Units.ext
    ext i j
    change coord v.embedding (pInf E (algebraMap E (Ad E) (γ.1.val i j))) = v.embedding (γ.1.val i j)
    exact coord_pInf_algebraMap v _

end GlobalTheory.BCT.RatPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEliminationFormGeneralLinearFormsConeStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eliminationForm_generalLinearForms_cone : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime → (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) → ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K) (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 → (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  first | exact @GlobalTheory.HSShort.exists_elim_form_of_field | exact GlobalTheory.HSShort.exists_elim_form_of_field | (intros; apply GlobalTheory.HSShort.exists_elim_form_of_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormFiniteFibresBirationalLinearSystemStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_finite_fibres_birational_linearSystem : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin S.N) F), g.IsHomogeneous d ∧ g ∉ S.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (y : Fin S.N → K), {x : S.Pt K | aeval (S.coords x.1) g ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y}.Finite := by
  first | exact @GlobalTheory.BirFiniteFibre.exists_form_finite_fibres | exact GlobalTheory.BirFiniteFibre.exists_form_finite_fibres | (intros; apply GlobalTheory.BirFiniteFibre.exists_form_finite_fibres <;> assumption)
end

