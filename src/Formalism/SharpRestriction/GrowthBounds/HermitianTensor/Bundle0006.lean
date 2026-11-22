import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.GrowthOfBasic
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0004
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0003

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.PbSmithLam
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem pb_nabla_one {O K : Type} [CommRing O] [Field K] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    nablaLTw O K m lam 1 = intO O (m + 1) (nuOf lam) := by
  ext F
  rw [Formalism.GradedWeylDivisibility.nablaLTwMem O K m lam 1 (by simp) F, Matrix.det_one, one_zpow, one_smul, tn_rowAct_one]
  exact Iff.rfl

theorem pb_finrank (K : Type) [Field K] (n : ℕ) (nu : Fin n → ℕ) (hnu : Antitone nu) :
    (Module.finrank K (dualWeyl K n n nu) : ℚ) = weylDim n (fun i => (nu i : ℤ)) := by
  rw [Formalism.L2.G.Model.weyl_dualWeyl K n nu hnu]
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rfl

theorem pb_smith_lam {p n' : ℕ} (R : RS p n') (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] R.Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
        B (rowAct R.Kf g P) Q = B P (rowAct R.Kf g.transpose Q)) ∧
      (∀ P ∈ intO R.O (m + 1) (nuOf lam), ∀ Q ∈ intO R.O (m + 1) (nuOf lam), B P Q ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (x x' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim (m + 1) (fun j => (nuOf lam j : ℤ)) ∧ (∀ b, ka b ≤ Formalism.L2.G.Model.expN p m lam) ∧
        (∀ b, x b ∈ intO R.O (m + 1) (nuOf lam)) ∧ (∀ a', x' a' ∈ intO R.O (m + 1) (nuOf lam)) ∧
        ∀ a' b, B (x b) (x' a') = if a' = b then (p : R.Kf) ^ ka b else 0 := by
  classical
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨B0, ha, hb, hc, hd⟩ :=
    Formalism.L2.G.Model.formCore p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m lam hlam
  obtain ⟨Bs, -, hB1, hB3, hB2⟩ := la_basis hinj m lam 1 (by rw [Matrix.det_one]; exact isUnit_one)
  rw [pb_nabla_one] at hB1
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) := (sSIdxFinite _ _ _).fintype
  let e : Fin (Fintype.card ↥(ssIdx (m + 1) (m + 1) (nuOf lam))) ≃ ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) :=
    (Fintype.equivFin _).symm
  have hrange : Set.range (Bs ∘ e) = Set.range Bs := e.surjective.range_comp Bs
  have hli : LinearIndependent R.Kf (Bs ∘ e) := hB3.comp e e.injective
  have hsK : Submodule.span R.Kf (Set.range (Bs ∘ e)) = dualWeyl R.Kf (m + 1) (m + 1) (nuOf lam) := by rw [hrange, hB2]
  have hsO : Submodule.span R.O (Set.range (Bs ∘ e)) = intO R.O (m + 1) (nuOf lam) := by rw [hrange, hB1]
  have hpc : algebraMap R.O R.Kf (p : R.O) = (p : R.Kf) := map_natCast _ p
  obtain ⟨x, x', ka, hka, hx, hx', hdiag⟩ := pb_abs (O := R.O) (K := R.Kf) R.w (p : R.O) R.std.2.1 R.std.1.w_sq
    (Formalism.L2.G.Model.expN p m lam) _ (Bs ∘ e) hli B0
    (by rw [hsK]; exact hb)
    (by rw [hsK, hsO]; exact hc)
    (by rw [hsO, hpc]; exact hd)
  rw [hsO] at hx hx'
  rw [hpc] at hdiag
  refine ⟨((p : R.Kf) ^ Formalism.L2.G.Model.expN p m lam) • B0, ?_, ?_, _, x, x', ka, ?_, hka, hx, hx', ?_⟩
  · intro g P Q
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, ha]
  · intro P hP Q hQ
    have h := hd Q hQ P hP
    rw [map_smul] at h
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    exact h
  · rw [← pb_finrank R.Kf (m + 1) (nuOf lam) (nuOf_anti lam hlam), ← hsK, finrank_span_eq_card hli, Fintype.card_fin]
  · intro a' b
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact hdiag a' b

theorem smithP : SmithP := by
  intro p n' R m ν hνA hν0
  have hlam : Antitone (fun j => ((ν j : ℕ) : ℤ)) := fun i j h => by
    show ((ν j : ℕ) : ℤ) ≤ ((ν i : ℕ) : ℤ)
    exact_mod_cast hνA h
  have hnu : nuOf (fun j => ((ν j : ℕ) : ℤ)) = ν := by
    funext t
    simp only [nuOf, hν0]
    simp
  have hexp : Formalism.L2.G.Model.expN p m (fun j => ((ν j : ℕ) : ℤ)) ≤ N0 (m + 1) * deF p (m + 1) (ν 0) := by
    unfold Formalism.L2.G.Model.expN
    split_ifs
    · exact Nat.zero_le _
    · have : ellWt (fun j : Fin (m + 1) => ((ν j : ℕ) : ℤ)) = ν 0 := by
        unfold ellWt
        have hl : lastIdx (m + 1) = Fin.last m := Fin.ext (by simp [lastIdx])
        rw [hl]
        show (((ν 0 : ℕ) : ℤ) - ((ν (Fin.last m) : ℕ) : ℤ)).toNat = ν 0
        rw [hν0]
        simp
      rw [this]
  obtain ⟨B, h1, h2, nb, x, x', ka, h3, h4, h5, h6, h7⟩ := pb_smith_lam R m _ hlam
  rw [hnu] at h2 h3 h5 h6
  exact ⟨B, h1, h2, nb, x, x', ka, h3, fun b => (h4 b).trans hexp, h5, h6, h7⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.PdAevalScale
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

variable (A : Type) [CommRing A] (r : ℕ)

def pdW : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) := fun i j => if i = j.rev then 1 else 0

def pdZ : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) := fun i j => (genY A r).adjugate j.rev i

theorem mul_pdW_apply_eq_apply_rev (M : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A)) (i j : Fin r) :
    (M * pdW A r) i j = M i j.rev := by
  simp [pdW, Matrix.mul_apply]

theorem pdZ_eq : pdZ A r = (genY A r).adjugate.transpose * pdW A r := by
  ext i j
  rw [mul_pdW_apply_eq_apply_rev]
  rfl

theorem pdW_transpose : (pdW A r).transpose = pdW A r := by
  ext i j
  simp only [Matrix.transpose_apply, pdW]
  by_cases h : i = j.rev
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [h', Fin.rev_rev]

theorem pdW_sq : pdW A r * pdW A r = 1 := by
  ext i j
  rw [mul_pdW_apply_eq_apply_rev]
  simp [pdW, Matrix.one_apply]

theorem pdW_det_sq : (pdW A r).det * (pdW A r).det = 1 := by
  rw [← Matrix.det_mul, pdW_sq, Matrix.det_one]

theorem cofY_mapMatrix : (cofY A r).mapMatrix (genY A r) = pdZ A r := by
  ext i j
  simp [cofY, genY, pdZ, AlgHom.mapMatrix_apply, aeval_X]

theorem detY_eq : detY A r = (genY A r).det := rfl

theorem pd_cof_det : cofY A r (detY A r) = (pdW A r).det * detY A r ^ (r - 1) := by
  rw [detY_eq]
  have h1 : cofY A r (genY A r).det = ((cofY A r).mapMatrix (genY A r)).det :=
    RingHom.map_det (cofY A r).toRingHom (genY A r)
  rw [h1, cofY_mapMatrix, pdZ_eq, Matrix.det_mul, Matrix.det_transpose, Matrix.det_adjugate,
    Fintype.card_fin]
  ring

theorem pd_ZZ : (genY A r).det • (cofY A r).mapMatrix (pdZ A r) =
    ((pdW A r).det * (genY A r).det ^ (r - 1)) • genY A r := by
  have hWW := pdW_sq A r
  have hWT := pdW_transpose A r
  have hadjW : (pdW A r).adjugate = (pdW A r).det • pdW A r := by
    calc (pdW A r).adjugate = (pdW A r).adjugate * (pdW A r * pdW A r) := by
          rw [hWW, Matrix.mul_one]
      _ = ((pdW A r).adjugate * pdW A r) * pdW A r := by rw [Matrix.mul_assoc]
      _ = (pdW A r).det • pdW A r := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hmapW : (pdW A r).map (cofY A r) = pdW A r := by
    ext i j
    simp only [Matrix.map_apply, pdW]
    split_ifs <;> simp
  have hmap : (cofY A r).mapMatrix (pdZ A r) = (pdZ A r).adjugate.transpose * pdW A r := by
    conv_lhs => rw [pdZ_eq]
    rw [AlgHom.mapMatrix_apply, Matrix.map_mul, hmapW, Matrix.transpose_map]
    have h1 : (genY A r).adjugate.map (cofY A r) = ((genY A r).map (cofY A r)).adjugate :=
      RingHom.map_adjugate (cofY A r).toRingHom (genY A r)
    rw [h1, ← AlgHom.mapMatrix_apply, cofY_mapMatrix]
  rw [hmap]
  rcases Nat.lt_or_ge r 2 with hr | hr
  · interval_cases r
    · ext i
      exact Fin.elim0 i
    · ext i j
      fin_cases i
      fin_cases j
      simp [pdZ, pdW, genY, Matrix.adjugate_fin_one, Matrix.det_fin_one, Matrix.mul_apply]
  · have hadjadj : (genY A r).adjugate.adjugate = (genY A r).det ^ (r - 2) • genY A r := by
      rw [Matrix.adjugate_adjugate _ (by rw [Fintype.card_fin]; omega), Fintype.card_fin]
    have hZ : (pdZ A r).adjugate =
        ((pdW A r).det * (genY A r).det ^ (r - 2)) • (pdW A r * (genY A r).transpose) := by
      rw [pdZ_eq, Matrix.adjugate_mul_distrib, hadjW, ← Matrix.adjugate_transpose, hadjadj,
        Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hZ, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hWT,
      Matrix.smul_mul, Matrix.mul_assoc, hWW, Matrix.mul_one, smul_smul]
    congr 1
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
    ring

theorem pd_aeval_scale {σ B : Type} [Fintype σ] [CommRing B] [Algebra A B] (c : B) (z : σ → B) (d : ℕ)
    (g : MvPolynomial σ A) (hg : g.IsHomogeneous d) : aeval (fun i => c * z i) g = c ^ d * aeval z g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.1 hs)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hd
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [show ∑ i ∈ s.support, s i = d from by rw [← hd]; rfl]
  ring

theorem pd_cofcof (d : ℕ) (g : MvPolynomial (Fin r × Fin r) A) (hg : g.IsHomogeneous d) :
    detY A r ^ d * cofY A r (cofY A r g) = ((pdW A r).det * detY A r ^ (r - 1)) ^ d * g := by
  have hcomp : cofY A r (cofY A r g) = aeval (fun v => cofY A r (pdZ A r v.1 v.2)) g := by
    rw [← AlgHom.comp_apply]
    unfold cofY
    rw [MvPolynomial.comp_aeval]
    rfl
  have hz : (fun v : Fin r × Fin r => detY A r * cofY A r (pdZ A r v.1 v.2)) =
      fun v => ((pdW A r).det * detY A r ^ (r - 1)) * X v := by
    funext v
    have h1 := congrFun (congrFun (pd_ZZ A r) v.1) v.2
    simp only [Matrix.smul_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, genY,
      Matrix.of_apply] at h1
    rw [detY_eq]
    exact h1
  rw [hcomp, ← pd_aeval_scale A (detY A r) _ d g hg, hz, pd_aeval_scale A _ X d g hg,
    aeval_X_left_apply]

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TaIntOfRename
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def ta_covR (A : Type) [CommRing A] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A))

theorem ta_covR_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (i : Fin (m + 1)) :
    map φ (ta_covR A m i) = ta_covR B m i := by
  unfold ta_covR
  rw [map_mul, map_pow, map_neg, map_one]
  congr 1
  exact (RingHom.map_det (map φ) (Matrix.of fun a b : Fin m =>
    (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A))).trans (by
      congr 1
      ext a b
      simp)

theorem ta_covR_eq (K : Type) [Field K] (m : ℕ) : ta_covR K m = covY K m := rfl

theorem ta_aeval_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (β : MvPolynomial (Fin (m + 1)) A) :
    map φ (aeval (ta_covR A m) β) = aeval (ta_covR B m) (map φ β) := by
  induction β using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X, ta_covR_map]

section Int

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

def ta_Int (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K] {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∃ β : MvPolynomial σ O, map (algebraMap O K) β = F

theorem ta_Int_coeff {σ : Type} {F : MvPolynomial σ K} (h : ta_Int O F) (u : σ →₀ ℕ) :
    coeff u F ∈ Set.range (algebraMap O K) := by
  obtain ⟨β, rfl⟩ := h
  exact ⟨coeff u β, (coeff_map _ _ _).symm⟩

theorem ta_Int_of_coeff {σ : Type} {F : MvPolynomial σ K} (h : ∀ u, coeff u F ∈ Set.range (algebraMap O K)) :
    ta_Int O F := by
  classical
  choose c hc using h
  refine ⟨∑ u ∈ F.support, monomial u (c u), ?_⟩
  simp only [map_sum, map_monomial, hc]
  exact F.support_sum_monomial_coeff

theorem ta_Int_add {σ : Type} {F G : MvPolynomial σ K} (h1 : ta_Int O F) (h2 : ta_Int O G) : ta_Int O (F + G) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨a + b, map_add _ _ _⟩

theorem ta_Int_mul {σ : Type} {F G : MvPolynomial σ K} (h1 : ta_Int O F) (h2 : ta_Int O G) : ta_Int O (F * G) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨a * b, map_mul _ _ _⟩

theorem ta_Int_smul {σ : Type} {F : MvPolynomial σ K} (c : O) (h : ta_Int O F) : ta_Int O (algebraMap O K c • F) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨C c * a, by rw [map_mul, map_C, smul_eq_C_mul]⟩

theorem ta_Int_rename {σ τ : Type} (e : σ → τ) {F : MvPolynomial σ K} (h : ta_Int O F) : ta_Int O (rename e F) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨rename e a, map_rename _ _ _⟩

theorem ta_Int_of_rename {σ τ : Type} (e : σ → τ) (he : Function.Injective e) {F : MvPolynomial σ K}
    (h : ta_Int O (rename e F)) : ta_Int O F := by
  refine ta_Int_of_coeff fun u => ?_
  rw [← coeff_rename_mapDomain e he]
  exact ta_Int_coeff h _

theorem ta_Int_prodX {k : ℕ} (a : Fin k → ℕ) : ta_Int O (∏ i, X i ^ a i : MvPolynomial (Fin k) K) :=
  ⟨∏ i, X i ^ a i, by simp [map_prod]⟩

theorem ta_Int_aeval (m : ℕ) {b : MvPolynomial (Fin (m + 1)) K} (h : ta_Int O b) : ta_Int O (aeval (covY K m) b) := by
  obtain ⟨β, rfl⟩ := h
  exact ⟨aeval (ta_covR O m) β, by rw [ta_aeval_map, ta_covR_eq]⟩

end Int

section Sat

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem ta_exists_pow (w : O) (hw : Irreducible w) {σ : Type} (b : MvPolynomial σ K) :
    ∃ n : ℕ, ta_Int O ((algebraMap O K w ^ n) • b) := by
  classical
  obtain ⟨⟨s, hs⟩, hsI⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (b.support.image fun u => coeff u b)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hw
  refine ⟨n, ta_Int_of_coeff fun u => ?_⟩
  rw [coeff_smul, smul_eq_mul]
  by_cases hu : u ∈ b.support
  · obtain ⟨r, hr⟩ := hsI _ (Finset.mem_image_of_mem _ hu)
    refine ⟨(↑v⁻¹ : O) * r, ?_⟩
    have hr' : algebraMap O K r = algebraMap O K s * coeff u b := by
      rw [hr]
      exact Algebra.smul_def _ _
    rw [map_mul, hr', hv, map_mul, map_pow, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · rw [mem_support_iff, not_not] at hu
    exact ⟨0, by rw [hu, mul_zero, map_zero]⟩

theorem ta_sat (w : O) (hw : Irreducible w) (m : ℕ) (hm : 1 ≤ m) (b : MvPolynomial (Fin (m + 1)) K)
    (h : ta_Int O (aeval (covY K m) b)) : ta_Int O b := by
  classical
  have hw0 : w ≠ 0 := hw.ne_zero
  have hinjOK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hW0 : algebraMap O K w ≠ 0 := fun h0 => hw0 (hinjOK (by rw [h0, map_zero]))
  obtain ⟨γ, hγ⟩ := h
  haveI hmax : (Ideal.span {w}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hw
  letI : Field (O ⧸ Ideal.span {w}) := Ideal.Quotient.field _
  have hind : Function.Injective (aeval (R := O ⧸ Ideal.span {w}) (covY (O ⧸ Ideal.span {w}) m)) := by
    have := Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_alg_independent (O ⧸ Ideal.span {w}) m hm
    rw [covY_eq] at this
    exact this
  have step : ∀ n : ℕ, ta_Int O (algebraMap O K w ^ (n + 1) • b) → ta_Int O (algebraMap O K w ^ n • b) := by
    intro n hn
    obtain ⟨β, hβ⟩ := hn
    have e1 : map (algebraMap O K) (aeval (ta_covR O m) β) = map (algebraMap O K) (C (w ^ (n + 1)) * γ) := by
      rw [ta_aeval_map, ta_covR_eq, hβ, map_smul, map_mul, map_C, hγ, smul_eq_C_mul]
      simp only [map_pow]
    have e2 := map_injective _ hinjOK e1
    have e3 : aeval (R := O ⧸ Ideal.span {w}) (covY (O ⧸ Ideal.span {w}) m)
        (map (Ideal.Quotient.mk (Ideal.span {w})) β) = 0 := by
      rw [← ta_covR_eq, ← ta_aeval_map, e2, map_mul, map_C, map_pow,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w), zero_pow (Nat.succ_ne_zero n),
        C_0, zero_mul]
    have e4 : map (Ideal.Quotient.mk (Ideal.span {w})) β = 0 := hind (by rw [e3, map_zero])
    apply ta_Int_of_coeff
    intro u
    have hu : coeff u β ∈ Ideal.span {w} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := congrArg (coeff u) e4
      rwa [coeff_map, coeff_zero] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hu
    refine ⟨c, ?_⟩
    have e5 := congrArg (coeff u) hβ
    rw [coeff_map, ← hc, map_mul, coeff_smul, smul_eq_mul] at e5
    rw [coeff_smul, smul_eq_mul]
    apply mul_right_cancel₀ hW0
    rw [e5]
    ring
  obtain ⟨n, hn⟩ := ta_exists_pow w hw b
  induction n with
  | zero => simpa using hn
  | succ n ih => exact ih (step n hn)

end Sat

section Act

variable {K : Type} [Field K] {m : ℕ}

theorem ta_Psi_gl_alt (g' : GL (Fin (m + 1)) K) (a : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (glAct g' (rename Sum.inl a)) =
      blockEmb K true (rowAct K (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (rename (fun i => (i, (0 : Fin (m + 1)))) a)) := by
  have key : (PsiXY K m).comp ((Formalism.CountingSumsFrames.glAct g').comp (rename Sum.inl)) =
      (blockEmb K true).comp ((rowAct K (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).comp
        (rename fun i => (i, (0 : Fin (m + 1))))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [PsiXY, Formalism.CountingSumsFrames.glAct, blockEmb, rowAct, algebraMap_eq]
  exact DFunLike.congr_fun key a

theorem ta_Psi_gl_y (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) K)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g⁻¹) (b : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (glAct g' (rename Sum.inr b)) =
      blockEmb K false (aeval (fun i => C g.det * rowAct K g⁻¹ (covY K m i)) b) := by
  have hinv : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
  have hd0 : g.det ≠ 0 := hg.ne_zero
  have key : (PsiXY K m).comp ((Formalism.CountingSumsFrames.glAct g').comp (rename Sum.inr)) =
      (blockEmb K false).comp (aeval fun i => C g.det * rowAct K g⁻¹ (covY K m i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    have h5 := Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_cofactor_transform K m g⁻¹ i hinv
    rw [covY_eq] at h5
    have hgg : ((g'⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g := by
      rw [Matrix.coe_units_inv, hg', Matrix.nonsing_inv_nonsing_inv g hg]
    simp only [AlgHom.comp_apply, rename_X, aeval_X, Formalism.CountingSumsFrames.glAct, Sum.elim_inr, map_sum, map_mul, hgg]
    rw [h5, ← map_mul, ← mul_assoc, ← C_mul, Matrix.nonsing_inv_nonsing_inv g hg, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv', mul_inv_cancel₀ hd0, C_1, one_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    unfold PsiXY blockEmb
    rw [aeval_C, aeval_X, Sum.elim_inr, rename_C, algebraMap_eq]
  exact DFunLike.congr_fun key b

theorem ta_aeval_scale {τ : Type} {k Q : ℕ} (d : K) (z : Fin k → MvPolynomial τ K) (b : MvPolynomial (Fin k) K)
    (hb : b.IsHomogeneous Q) : aeval (fun i => C d * z i) b = d ^ Q • aeval z b := by
  classical
  conv_lhs => rw [b.as_sum]
  conv_rhs => rw [b.as_sum]
  simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hdeg := hb (mem_support_iff.mp hu)
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [smul_eq_C_mul, ← map_pow]
  have hQ : ∑ i ∈ u.support, u i = Q := by
    rw [← hdeg]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hQ]
  ring

theorem ta_aeval_rowAct (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (b : MvPolynomial (Fin (m + 1)) K) :
    aeval (fun i => rowAct K h (covY K m i)) b = rowAct K h (aeval (covY K m) b) := by
  exact (DFunLike.congr_fun (comp_aeval (covY K m) (rowAct K h)) b).symm

theorem ta_Psi_gl (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) K)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g⁻¹) (Q : ℕ) (a b : MvPolynomial (Fin (m + 1)) K)
    (hb : b.IsHomogeneous Q) :
    PsiXY K m (glAct g' (rename Sum.inl a * rename Sum.inr b)) =
      blockEmb K true (rowAct K g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a)) *
        blockEmb K false (g.det ^ Q • rowAct K g⁻¹ (aeval (covY K m) b)) := by
  rw [map_mul, map_mul, ta_Psi_gl_alt, ta_Psi_gl_y g hg g' hg', hg', ta_aeval_scale g.det _ b hb, ta_aeval_rowAct]

end Act

end Formalism.MainNotions.flipOneThree.Pf

end
end

