import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalDomainLiftCyclotomicAway
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor.CycLift

theorem charZero_witt (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 ((CharP.cast_eq_zero_iff K p l).1 h2)
    subst h4
    exact WittVector.p_nonzero p K h1
  · subst h
    exact CharP.charP_to_charZero _

theorem isPrimitiveRoot_zetaAway {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zetaAway n) n :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn)
    Subtype.val_injective

theorem hom_ext {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] (f g : cycAway n →+* R)
    (h : f (zetaAway n) = g (zetaAway n)) : f = g := by
  have hinv : ∀ hx : (n : ℂ)⁻¹ ∈ cycAway n, f ⟨(n : ℂ)⁻¹, hx⟩ = g ⟨(n : ℂ)⁻¹, hx⟩ := by
    intro hx
    have hu : (⟨(n : ℂ)⁻¹, hx⟩ : cycAway n) * (n : cycAway n) = 1 :=
      Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])
    have hf := congrArg f hu
    have hg := congrArg g hu
    rw [map_mul, map_natCast, map_one] at hf hg
    calc f ⟨(n : ℂ)⁻¹, hx⟩ = f ⟨(n : ℂ)⁻¹, hx⟩ * ((n : R) * g ⟨(n : ℂ)⁻¹, hx⟩) := by
          rw [_root_.mul_comm (n : R), hg, _root_.mul_one]
      _ = g ⟨(n : ℂ)⁻¹, hx⟩ := by rw [← _root_.mul_assoc, hf, _root_.one_mul]
  ext ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · exact hinv _
  | zero => exact (map_zero f).trans (map_zero g).symm
  | one => exact (map_one f).trans (map_one g).symm
  | add x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | neg x hx ih =>
    change f (-⟨x, hx⟩) = g (-⟨x, hx⟩)
    rw [map_neg, map_neg, ih]
  | mul x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

end GlobalTheory.SiegelTor.CycLift

namespace GlobalTheory.SiegelTor.CycLift

theorem exists_hom {n : ℕ} (hn : n ≠ 0) {F : Type} [Field F] [CharZero F] {y : F} (hy : IsPrimitiveRoot y n) :
    ∃ f : cycAway n →+* F, Function.Injective f ∧ f (zetaAway n) = y := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  set z : ℂ := ((zetaAway n : cycAway n) : ℂ) with hzdef
  have hz : IsPrimitiveRoot z n := (isPrimitiveRoot_zetaAway hn).map_of_injective (f := (cycAway n).subtype) Subtype.val_injective
  have hint : IsIntegral ℚ z := (hz.isIntegral hpos).tower_top
  let pb := IntermediateField.adjoin.powerBasis hint
  have hgen : pb.gen = IntermediateField.AdjoinSimple.gen ℚ z := rfl
  have hroot : Polynomial.aeval y (minpoly ℚ pb.gen) = 0 := by
    have hmp : minpoly ℚ pb.gen = minpoly ℚ z := by
      exact IntermediateField.minpoly_gen ℚ z
    rw [hmp, ← Polynomial.cyclotomic_eq_minpoly_rat hz hpos, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hy.isRoot_cyclotomic hpos
  let ψ := pb.lift y hroot
  have hle : cycAway n ≤ (IntermediateField.adjoin ℚ {z}).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ z
    · show _ ∈ IntermediateField.adjoin ℚ {z}
      exact inv_mem (IntermediateField.natCast_mem _ n)
  refine ⟨(ψ : IntermediateField.adjoin ℚ {z} →+* F).comp (Subring.inclusion hle), ?_, ?_⟩
  · exact ((ψ : IntermediateField.adjoin ℚ {z} →+* F).injective).comp (Subring.inclusion_injective hle)
  · change ψ pb.gen = y
    exact PowerBasis.lift_gen _ _ _

end GlobalTheory.SiegelTor.CycLift

namespace GlobalTheory.SiegelTor.CycLift

theorem exists_complete_domain_lift : ∀ (n : ℕ), 3 ≤ n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K),
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsNoetherianRing V) (βV : cycAway n →+* V)
      (π : V →+* K), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Function.Injective βV ∧ Function.Surjective π ∧
        π.comp βV = β := by
  intro n hn3 K _ _ β
  have hn : n ≠ 0 := by omega
  have hβζ := isPrimitiveRoot_map hn β
  have hnK : (n : K) ≠ 0 := by simpa using ((isUnit_natCast hn).map β).ne_zero
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    haveI := charZero_witt p K
    have hinj := IsFractionRing.injective (WittVector p K) (FractionRing (WittVector p K))
    haveI : CharZero (FractionRing (WittVector p K)) := charZero_of_injective_algebraMap hinj
    have hc : ∀ a : K, (WittVector.constantCoeff : WittVector p K →+* K) (WittVector.teichmuller p a) = a :=
      fun a => by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    set t : WittVector p K := WittVector.teichmuller p (β (zetaAway n)) with ht_def
    have ht : IsPrimitiveRoot t n := by
      refine ⟨?_, fun l hl => hβζ.dvd_of_pow_eq_one l ?_⟩
      · rw [ht_def, ← map_pow, hβζ.pow_eq_one, map_one]
      · have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) hl
        rwa [map_pow, map_one, hc] at this
    obtain ⟨f, hf, hfζ⟩ := exists_hom hn (ht.map_of_injective hinj)
    have hnW : IsUnit (n : WittVector p K) :=
      WittVector.isUnit_of_coeff_zero_ne_zero _ (by rw [← WittVector.constantCoeff_apply, map_natCast]; exact hnK)
    have hmem : ∀ x, f x ∈ (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range := by
      rintro ⟨x, hx⟩
      induction hx using Subring.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx'
        · exact ⟨t, hfζ.symm⟩
        · subst hx'
          refine ⟨↑hnW.unit⁻¹, ?_⟩
          apply mul_right_cancel₀ (Nat.cast_ne_zero.2 hn : (n : FractionRing (WittVector p K)) ≠ 0)
          have e1 : algebraMap (WittVector p K) (FractionRing (WittVector p K)) ↑hnW.unit⁻¹ * n = 1 := by
            rw [← map_natCast (algebraMap (WittVector p K) (FractionRing (WittVector p K))) n, ← map_mul,
              hnW.val_inv_mul, map_one]
          have hu : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) * (n : cycAway n) = 1 :=
            Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])
          have e2 := congrArg f hu
          rw [map_mul, map_natCast, map_one] at e2
          exact e1.trans e2.symm
      | zero => show f 0 ∈ _; rw [map_zero]; exact zero_mem _
      | one => show f 1 ∈ _; rw [map_one]; exact one_mem _
      | add x y hx hy ihx ihy =>
        show f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _; rw [map_add]; exact add_mem ihx ihy
      | neg x hx ih => show f (-⟨x, hx⟩) ∈ _; rw [map_neg]; exact neg_mem ih
      | mul x y hx hy ihx ihy =>
        show f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _; rw [map_mul]; exact mul_mem ihx ihy
    let e : WittVector p K ≃+* (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range :=
      RingEquiv.ofBijective (algebraMap (WittVector p K) (FractionRing (WittVector p K))).rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
    let βV : cycAway n →+* WittVector p K := e.symm.toRingHom.comp (f.codRestrict _ hmem)
    have hβV : ∀ x, algebraMap (WittVector p K) (FractionRing (WittVector p K)) (βV x) = f x := fun x =>
      congrArg Subtype.val (e.apply_symm_apply (f.codRestrict _ hmem x))
    refine ⟨WittVector p K, inferInstance, inferInstance, inferInstance, inferInstance, βV, WittVector.constantCoeff,
      ?_, ?_, ?_, ?_⟩
    · rw [(WittVector.irreducible p).maximalIdeal_eq]
      exact WittVector.isAdicCompleteIdealSpanP
    · exact fun a b h => hf (by rw [← hβV, ← hβV, h])
    · exact fun a => ⟨WittVector.teichmuller p a, hc a⟩
    · refine hom_ext hn _ _ ?_
      have h1 : βV (zetaAway n) = t := hinj (by rw [hβV, hfζ])
      show WittVector.constantCoeff (βV (zetaAway n)) = β (zetaAway n)
      rw [h1, hc]
  · subst hp0
    haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, hf, hfζ⟩ := exists_hom hn hβζ
    have hβ : β = f := hom_ext hn _ _ hfζ.symm
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, β, RingHom.id K, ?_, hβ ▸ hf,
      fun x => ⟨x, rfl⟩, RingHom.id_comp β⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance

end GlobalTheory.SiegelTor.CycLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectio
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.Proj

variable {p q r : ℕ}

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem det_Jpq_ne (p q : ℕ) : (Formalism.UG.Jpq p q).det ≠ 0 := by
  rw [Jpq_eq_diagonal, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rcases i with i | i <;> simp

theorem star_det_mul_det (u : UpqT p q) : star (UpqT.mat u).det * (UpqT.mat u).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqExpChart.mat_unitary u)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := det_Jpq_ne p q
  apply mul_left_cancel₀ hJ
  linear_combination h

theorem det_mat_ne (u : UpqT p q) : (UpqT.mat u).det ≠ 0 := by
  intro h
  have := star_det_mul_det u
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem dg_unitary (a₀ : Fin p ⊕ Fin q) (z : ℂ) (hz : star z * z = 1) :
    (dg a₀ z)ᴴ * Formalism.UG.Jpq p q * dg a₀ z = Formalism.UG.Jpq p q := by
  rw [Jpq_eq_diagonal, dg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = a₀
  · subst h
    simp only [Pi.star_apply, Function.update_self]
    linear_combination (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i) * hz
  · simp [Function.update_of_ne h]

theorem det_sMat (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : (sMat a₀ u).det = 1 := by
  rw [sMat, Matrix.det_mul, det_dg, mul_inv_cancel₀ (det_mat_ne u)]

theorem sMat_unitary (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) :
    (sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u = Formalism.UG.Jpq p q := by
  have hz : star (UpqT.mat u).det⁻¹ * (UpqT.mat u).det⁻¹ = 1 := by
    rw [star_inv₀, ← mul_inv, star_det_mul_det, inv_one]
  have h1 := GlobalTheory.UpqExpChart.mat_unitary u
  have h2 := dg_unitary a₀ _ hz
  calc _ = (dg a₀ (UpqT.mat u).det⁻¹)ᴴ * ((UpqT.mat u)ᴴ * Formalism.UG.Jpq p q * UpqT.mat u) *
        dg a₀ (UpqT.mat u).det⁻¹ := by
        simp only [sMat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem continuous_sMat (a₀ : Fin p ⊕ Fin q) : Continuous (sMat a₀ : UpqT p q → _) := by
  unfold sMat dg
  refine GlobalTheory.UpqExpChart.continuous_mat.matrix_mul (Continuous.matrix_diagonal ?_)
  exact continuous_const.update a₀
    (GlobalTheory.UpqExpChart.continuous_mat.matrix_det.inv₀ det_mat_ne)

theorem sMat_mul (a₀ : Fin p ⊕ Fin q) (u v : UpqT p q) (hu : (UpqT.mat u).det = 1) :
    sMat a₀ (u * v) = UpqT.mat u * sMat a₀ v := by
  have h : UpqT.mat (u * v) = UpqT.mat u * UpqT.mat v := rfl
  rw [sMat, sMat, h, Matrix.det_mul, hu, one_mul, Matrix.mul_assoc]

theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) (A : Matrix ι (Fin r) ℂ)
    (B : Matrix (Fin r) ι ℂ) (hAB : A * B = 1) (S : Matrix ι ι ℂ) : (B * S * A).det = S.det := by
  have h1 : (B * S * A).submatrix e e = B.submatrix e id * S * A.submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  have h2 : A.submatrix id e * B.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, hAB]
    rfl
  rw [← Matrix.det_submatrix_equiv_self e, h1, Matrix.det_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

def gl (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (u : UpqT p q) : GL (Fin r) ℂ where
  val := B * sMat a₀ u * A
  inv := B * (sMat a₀ u).adjugate * A
  val_inv := by
    calc _ = B * (sMat a₀ u * (A * B) * (sMat a₀ u).adjugate) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.mul_adjugate, det_sMat, one_smul, Matrix.mul_one, hBA]
  inv_val := by
    calc _ = B * ((sMat a₀ u).adjugate * (A * B) * sMat a₀ u) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.adjugate_mul, det_sMat, one_smul, Matrix.mul_one, hBA]

section
variable (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1)

theorem gl_val (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = B * sMat a₀ u * A := rfl

theorem continuous_gl : Continuous (gl a₀ A B hAB hBA) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_const.matrix_mul (continuous_sMat a₀)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul (continuous_sMat a₀).matrix_adjugate).matrix_mul continuous_const

theorem mul_gl (u : UpqT p q) :
    A * (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = sMat a₀ u * A := by
  rw [gl_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul]

theorem gl_keeps (H : Matrix (Fin r) (Fin r) ℂ) (hH : Aᴴ * Formalism.UG.Jpq p q * A = -Hᵀ) (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ)ᵀ * H *
      (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = H := by
  have hm := mul_gl a₀ A B hAB hBA u
  generalize (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = g at hm ⊢
  have h : gᴴ * (-Hᵀ) * g = -Hᵀ := by
    calc _ = (A * g)ᴴ * Formalism.UG.Jpq p q * (A * g) := by
          rw [← hH]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Aᴴ * ((sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u) * A := by
          rw [hm]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [sMat_unitary, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h'
  exact h'

end

theorem exists_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)), IsIdent p q Ψ G x σ A e → ∃ π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G, Continuous π ∧ IsProj p q Ψ G σ A a₀ π ∧ (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ hI
  let B : ∀ ρ, Matrix (Fin r) (Fin (p ρ) ⊕ Fin (q ρ)) ℂ := fun ρ => mat x (σ ρ) * (permM (e ρ))ᵀ
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ => by
    simp only [B]
    rw [← Matrix.mul_assoc, (hI ρ).2, permM_mul_transpose]
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv (e ρ)).1 (hAB ρ)
  let F : (∀ ρ, UpqT (p ρ) (q ρ)) → κ → GL (Fin r) ℂ :=
    fun b ρ => gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ)
  have hF : ∀ b ρ, F b (σ.symm (σ ρ)) = gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ) := fun b ρ => by
    rw [Equiv.symm_apply_apply]
  have hmem : ∀ b, (fun τ => F b (σ.symm τ)) ∈ realSU Ψ G := fun b => by
    rw [DensOne.mem_realSU_iff]
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    simp only [hF]
    exact ⟨gl_keeps _ _ _ _ _ _ (hI ρ).1 _, by rw [gl_val, det_conj (e ρ) _ _ (hAB ρ), det_sMat]⟩
  refine ⟨fun b => ⟨_, hmem b⟩, ?_, ?_, ?_⟩
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    exact (continuous_gl _ _ _ _ _).comp (continuous_apply _)
  · intro b ρ
    simp only [hF]
    exact mul_gl _ _ _ _ _ _
  · intro s b₀ hs b
    refine Subtype.ext (funext fun τ => ?_)
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    apply Units.ext
    change ((F (b₀ * b) (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (s.1 (σ ρ) : GL (Fin r) ℂ) * ((F b (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    have h1 : ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B ρ * UpqT.mat (b₀ ρ) * A ρ := by
      rw [Matrix.mul_assoc, hs ρ, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
    have h2 : (UpqT.mat (b₀ ρ)).det = 1 := by
      rw [← det_conj (e ρ) _ _ (hAB ρ), ← h1]
      exact (((DensOne.mem_realSU_iff Ψ G _).1 s.2) (σ ρ)).2
    rw [hF, hF, gl_val, gl_val, h1, Pi.mul_apply, sMat_mul _ _ _ h2]
    calc _ = B ρ * UpqT.mat (b₀ ρ) * (A ρ * B ρ) * sMat (a₀ ρ) (b ρ) * A ρ := by
          rw [hAB]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CovTop.VolUp.Proj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCosetRepresentatives
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovTop.VolUp.Reps

theorem isKM_one_of_three {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : Gal(E/F)) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (k : Matrix (Fin n) (Fin n) (RA F E))
    (h : IsKM c G L 3 k) : IsKM c G L 1 k := by
  refine ⟨h.1, fun x hx => ?_, h.2.2⟩
  obtain ⟨y, hy, e⟩ := h.2.1 x hx
  exact ⟨3 • y, nsmul_mem hy 3, by rw [e, one_smul]⟩

theorem exists_reps : ∀ (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))), IsOpen {h : GA D V | finE V h ∈ K₀} → (∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ K₀) → ∃ (J : Type) (_ : Countable J) (g : J → GA D V), (∀ j, g j ∈ GfC V) ∧ (∀ i j, UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 3 ((finHom V (g i)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g j)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → i = j) ∧ ∀ h : GA D V, ∃ j, ∃ γ ∈ GQ V, finE V ((g j)⁻¹ * γ * h) ∈ K₀ := by
  intro D V Λ K₀ hKo hK1
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := (GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V).2.1
  let H : Subgroup (GA D V) := K₀.comap (finE V)
  have hHo : IsOpen (H : Set (GA D V)) := hKo
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  let jm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* GA D V :=
    (e0.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj0 : ∀ k, e0 (jm k) = (1, k) := fun k => e0.apply_symm_apply _
  have hfin : ∀ h : GA D V, finE V (jm (e0 h).2) = finE V h := by
    intro h
    have h1 : finHom V (jm (e0 h).2) = finHom V h := by
      refine Units.ext ?_
      have a1 := (he0 (jm (e0 h).2)).1
      have a2 := (he0 h).1
      rw [hj0] at a1
      exact a1.symm.trans a2
    rw [finE_eq, finE_eq, h1]
  have hinf : ∀ k, jm k ∈ GfC V := by
    intro k
    have a1 := (he0 (jm k)).2
    rw [hj0] at a1
    exact Units.ext a1.symm
  have hmk : ∀ h : GA D V, DoubleCoset.mk (GQ V) H (jm (e0 h).2) = DoubleCoset.mk (GQ V) H h := by
    intro h
    refine (DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, (jm (e0 h).2)⁻¹ * h, ?_, by group⟩
    show finE V ((jm (e0 h).2)⁻¹ * h) ∈ K₀
    rw [map_mul, map_inv, hfin, inv_mul_cancel]
    exact one_mem _
  let g : DoubleCoset.Quotient (GQ V : Set (GA D V)) (H : Set (GA D V)) → GA D V :=
    fun q => jm (e0 (Quotient.out q)).2
  have hgj : ∀ q, DoubleCoset.mk (GQ V) H (g q) = q := fun q => (hmk _).trans (Quotient.out_eq' q)
  have hJc : Countable (DoubleCoset.Quotient (GQ V : Set (GA D V)) (H : Set (GA D V))) := by
    obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense (GA D V)
    haveI := hs.to_subtype
    have hsurj : Function.Surjective (fun x : s => DoubleCoset.mk (GQ V) H (x : GA D V)) := by
      intro q
      have hU : IsOpen ((fun x => Quotient.out q * x) '' (H : Set (GA D V))) := isOpenMap_mul_left _ _ hHo
      obtain ⟨x, hxs, ⟨k, hk, rfl⟩⟩ := hd.exists_mem_open hU ⟨_, 1, one_mem _, mul_one _⟩
      refine ⟨⟨_, hxs⟩, ?_⟩
      refine ((DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, k⁻¹, inv_mem hk, by group⟩).trans (Quotient.out_eq' q)
    exact hsurj.countable
  refine ⟨_, hJc, g, fun j => hinf _, fun i j hE => ?_, fun h => ?_⟩
  · obtain ⟨γ, hγ, κ, hκ, he⟩ := hE
    obtain ⟨γ₀, hγ₀, hγf⟩ := GlobalTheory.RepsInj.gq_of_isUA D V γ hγ
    have hx : ((finHom V ((γ₀ * g i)⁻¹ * g j)).1 : Matrix (Fin V.rank) (Fin V.rank)
        (RA (maximalRealSubfield D.host.E) D.host.E)) = κ := by
      have h1 : ((finHom V (γ₀ * g i)).1 : Matrix (Fin V.rank) (Fin V.rank)
          (RA (maximalRealSubfield D.host.E) D.host.E)) * κ = (finHom V (g j)).1 := by
        rw [map_mul, Units.val_mul, hγf, he]
      rw [map_mul, map_inv, Units.val_mul, ← h1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have hxH : finE V ((γ₀ * g i)⁻¹ * g j) ∈ K₀ := by
      have h3 := isKM_one_of_three _ _ _ _ hκ
      rw [← hx] at h3
      exact hK1 _ h3
    have e : DoubleCoset.mk (GQ V) H (g i) = DoubleCoset.mk (GQ V) H (g j) :=
      (DoubleCoset.eq _ _ _ _).2 ⟨γ₀, hγ₀, (γ₀ * g i)⁻¹ * g j, hxH, by group⟩
    exact (hgj i).symm.trans (e.trans (hgj j))
  · obtain ⟨γ, hγ, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 (hgj (DoubleCoset.mk (GQ V) H h))
    refine ⟨DoubleCoset.mk (GQ V) H h, γ⁻¹, inv_mem hγ, ?_⟩
    generalize g (DoubleCoset.mk (GQ V) H h) = x at e ⊢
    subst e
    have e2 : x⁻¹ * γ⁻¹ * (γ * x * k) = k := by group
    rw [e2]
    exact hk

end GlobalTheory.CovTop.VolUp.Reps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDimSuccGeneratingSectionsInfiniteField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.GenCut

theorem isEmpty_of_topologicalKrullDim_lt_zero (T : Type) [TopologicalSpace T]
    (h : topologicalKrullDim T < ((0 : ℕ) : WithBot ℕ∞)) : IsEmpty T := by
  by_contra hT
  rw [not_isEmpty_iff] at hT
  obtain ⟨x⟩ := hT
  haveI : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim T := Order.krullDim_nonneg
  exact absurd h (not_lt.mpr (by simpa using h0))

theorem exists_sections_cover_closed (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X) (hL : L.IsLB)
    (n : ℕ) (u : Fin n → L.Sec) (hu : ⨆ i, nonzeroLocus (u i) = ⊤) (e : ℕ) :
    ∀ Z : Set X, IsClosed Z → topologicalKrullDim Z < (e : ℕ) →
      ∃ s : Fin e → L.Sec, ∀ x ∈ Z, ∃ i, x ∈ nonzeroLocus (s i) := by
  induction e with
  | zero =>
    intro Z _ h
    have := isEmpty_of_topologicalKrullDim_lt_zero Z h
    exact ⟨Fin.elim0, fun x hx => (this.false ⟨x, hx⟩).elim⟩
  | succ e ih =>
    intro Z hZ h
    obtain ⟨S, hS, hdim⟩ := GlobalTheory.T.exists_finite_topologicalKrullDim_diff_open_lt X Z hZ
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_sec_nonzero_on_finite_of_generated' k X p L hL n u hu S hS
    have hU : IsOpen ((nonzeroLocus t : X.Opens) : Set X) := (nonzeroLocus t).isOpen
    obtain ⟨s, hs⟩ := ih (Z \ ((nonzeroLocus t : X.Opens) : Set X)) (hZ.sdiff hU)
      (hdim _ hU (fun x hx => ht x hx) e h)
    refine ⟨Fin.cons t s, fun x hx => ?_⟩
    by_cases hxt : x ∈ nonzeroLocus t
    · exact ⟨0, by simpa using hxt⟩
    · obtain ⟨i, hi⟩ := hs x ⟨hx, hxt⟩
      exact ⟨i.succ, by simpa using hi⟩

theorem exists_generating_sections_of_dim_le :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ d : ℕ, topologicalKrullDim X ≤ d → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ s : Fin (d + 1) → L.Sec, ⨆ i, nonzeroLocus (s i) = ⊤ := by
  intro k _ _ X _ p L hL d hd n u hu
  have h1 : topologicalKrullDim (Set.univ : Set X) ≤ topologicalKrullDim X :=
    topologicalKrullDim_subspace_le X _
  have h2 : ((d : ℕ) : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self d
  obtain ⟨s, hs⟩ := exists_sections_cover_closed k X p L hL n u hu (d + 1) Set.univ isClosed_univ
    (lt_of_le_of_lt (h1.trans hd) h2)
  refine ⟨s, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, hi⟩ := hs x (Set.mem_univ x)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end GlobalTheory.GenCut
end

