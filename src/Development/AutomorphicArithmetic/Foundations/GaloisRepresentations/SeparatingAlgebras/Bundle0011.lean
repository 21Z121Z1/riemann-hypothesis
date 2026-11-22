import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0050
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBound
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

section CoefLeLemmas

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type}

private lemma coefLe_sum {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ s, CoefLe ι R (f a)) : CoefLe ι R (∑ a ∈ s, f a) := by
  intro m
  rw [MvPolynomial.coeff_sum, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR (fun a ha => h a ha m)

private lemma coefLe_mul {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) {p q : MvPolynomial σ ℂ}
    (hp : CoefLe ι R p) (hq : CoefLe ι S q) : CoefLe ι (R * S) (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hR hS) ?_
  intro x _
  rw [map_mul, norm_mul]
  exact mul_le_mul (hp _) (hq _) (norm_nonneg _) hR

private lemma coefLe_one : CoefLe ι 1 (1 : MvPolynomial σ ℂ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

private lemma coefLe_pow {R : ℝ} (hR : 0 ≤ R) {p : MvPolynomial σ ℂ} (hp : CoefLe ι R p) (k : ℕ) :
    CoefLe ι (R ^ k) (p ^ k) := by
  induction k with
  | zero => simpa using coefLe_one ι
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact coefLe_mul ι (pow_nonneg hR _) hR ih hp

private lemma coefLe_prod {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (h : ∀ a ∈ s, CoefLe ι (r a) (f a)) :
    CoefLe ι (∏ a ∈ s, r a) (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefLe_one ι
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coefLe_mul ι (hr a) (Finset.prod_nonneg fun b _ => hr b) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

private lemma coefLe_C_mul_X {c : ℂ} {R : ℝ} (hR : 1 ≤ R) (hc : ‖ι.symm c‖ ≤ R) (v : σ) :
    CoefLe ι R (MvPolynomial.C c * MvPolynomial.X v) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs
  · simpa using hc
  · simpa using zero_le_one.trans hR

private lemma coefLe_monomial_image {τ : Type} {y : σ → MvPolynomial τ ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hy : ∀ v, CoefLe ι R (y v)) (m : σ →₀ ℕ) :
    CoefLe ι (R ^ (m.sum fun _ e => e)) (m.prod fun v e => y v ^ e) := by
  have h := coefLe_prod ι m.support (fun v => y v ^ m v) (fun v => R ^ m v)
    (fun _ => pow_nonneg hR _) (fun v _ => coefLe_pow ι hR (hy v) (m v))
  rwa [Finset.prod_pow_eq_pow_sum] at h

end CoefLeLemmas

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.blockBound_pf :
    UpperTheory.Gal.Gen.BlockBound := by
  intro l _ ι T n A R hR hA D x hx h1
  classical
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  set y : T × Fin n × Fin n → MvPolynomial (T × Fin n × Fin n) ℂ :=
    fun v => ∑ b : Fin n, MvPolynomial.C (A v.1 v.2.1 b) * MvPolynomial.X (v.1, (b, v.2.2)) with hydef
  have hy : ∀ v, CoefLe ι R (y v) := fun v =>
    coefLe_sum ι _ _ hR0 fun b _ => coefLe_C_mul_X ι hR (hA _ _ _) _
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ A x =
      ∑ m ∈ x.support, MvPolynomial.C (MvPolynomial.coeff m x) * (m.prod fun v e => y v ^ e) := by
    conv_lhs => rw [x.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_monomial]
    rfl
  rw [e]
  refine coefLe_sum ι _ _ (pow_nonneg hR0 _) fun m hm k => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, norm_mul]
  have hdeg : (m.sum fun _ e => e) ≤ D := (MvPolynomial.le_totalDegree hm).trans hx
  calc _ ≤ 1 * R ^ (m.sum fun _ e => e) :=
        mul_le_mul (h1 m) (coefLe_monomial_image ι hR0 hy m k) (norm_nonneg _) zero_le_one
    _ ≤ R ^ D := by
        rw [one_mul]
        exact pow_le_pow_right₀ hR hdeg
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DenomBdd
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound

open GlobalTheory.CongW (IntMat)

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private lemma natCast_int (u : HeightOneSpectrum (𝓞 E)) (l : ℕ) :
    (l : u.adicCompletion E) ∈ u.adicCompletionIntegers E :=
  _root_.natCast_mem (u.adicCompletionIntegers E) l

private lemma v_lt_one (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) :
    Valued.v (l : u.adicCompletion E) < 1 := by
  have h := (u.valuation_lt_one_iff_mem (K := E) ((l : ℕ) : 𝓞 E)).2 hu
  have h2 := u.valuedAdicCompletion_eq_valuation (K := E) ((l : ℕ) : 𝓞 E)
  rw [← h2] at h
  simpa using h

private lemma exists_pow_int (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (y : u.adicCompletion E) : ∃ d : ℕ, (l : u.adicCompletion E) ^ d * y ∈ u.adicCompletionIntegers E := by
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  obtain ⟨d, hd⟩ := exists_pow_lt₀ (v_lt_one u hu) (Units.mk0 _ (inv_ne_zero hv))
  refine ⟨d, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow]
  have h0 : (0 : _) < Valued.v y := zero_lt_iff.2 hv
  have := mul_le_mul_left (le_of_lt hd) (Valued.v y)
  simpa [hv] using this

private lemma intMat_mono (u : HeightOneSpectrum (𝓞 E)) (l : ℕ) (m : Matrix (Fin a) (Fin a) (u.adicCompletion E))
    {d e : ℕ} (hde : d ≤ e) (h : IntMat u ((l : u.adicCompletion E) ^ d • m)) :
    IntMat u ((l : u.adicCompletion E) ^ e • m) := by
  intro i j
  have h1 := h i j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1 ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  rw [pow_add, mul_comm (_ ^ d), mul_assoc]
  exact mul_mem (pow_mem (natCast_int u l) k) h1

private lemma exists_intMat (u : HeightOneSpectrum (𝓞 E)) {l : ℕ} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (m : Matrix (Fin a) (Fin a) (u.adicCompletion E)) :
    ∃ d : ℕ, IntMat u ((l : u.adicCompletion E) ^ d • m) := by
  choose D hD using fun p : Fin a × Fin a => exists_pow_int u hu (m p.1 p.2)
  refine ⟨Finset.univ.sup D, fun i j => ?_⟩
  have hle : D (i, j) ≤ Finset.univ.sup D := Finset.le_sup (Finset.mem_univ _)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hk, pow_add, mul_comm (_ ^ D (i, j)), mul_assoc]
  exact mul_mem (pow_mem (natCast_int u l) k) (hD (i, j))

private lemma isOpen_intMat {X : Type*} [TopologicalSpace X] (u : HeightOneSpectrum (𝓞 E)) (c : u.adicCompletion E)
    (f : X → Matrix (Fin a) (Fin a) (u.adicCompletion E)) (hf : Continuous f) :
    IsOpen {x | IntMat u (c • f x)} := by
  have e : {x | IntMat u (c • f x)} = ⋂ i, ⋂ j, {x | c * f x i j ∈ u.adicCompletionIntegers E} := by
    ext x
    simp [IntMat]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  have hc : Continuous fun x => c * f x i j :=
    continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hf))
  exact (GroundTheory.Global.isOpen_adicCompletionIntegers u).preimage hc

end

end UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound

open GlobalTheory.CongW (IntMat) in
open UpperTheory.Gal.Gen.IntegralMatrixDenominatorBound in
theorem UpperTheory.Gal.Gen.denomBdd_pf :
    UpperTheory.Gal.Gen.DenomBdd := by
  intro E _ _ _ l hl n Z hZ
  have hl0 : ((l : ℕ) : 𝓞 E) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  have hS : {u : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)}) ?_).subset ?_
    · simpa using hl0
    · intro u hu
      exact Ideal.dvd_span_singleton.2 hu
  have hopen : ∀ d : ℕ, IsOpen {g : UA E n | DenomLe l d g} := by
    intro d
    have e : {g : UA E n | DenomLe l d g} = ⋂ u ∈ {u : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ u.asIdeal},
        ({g : UA E n | IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E)))} ∩
        {g : UA E n | IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E)))}) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, DenomLe]
    rw [e]
    refine hS.isOpen_biInter fun u _ => ?_
    exact (isOpen_intMat u _ _ (Units.continuous_val.comp (GlobalTheory.BCT.GlobLev.continuous_cLoc u))).inter
      (isOpen_intMat u _ _ (Units.continuous_coe_inv.comp (GlobalTheory.BCT.GlobLev.continuous_cLoc u)))
  have hmono : ∀ {d e : ℕ}, d ≤ e → ∀ g : UA E n, DenomLe l d g → DenomLe l e g :=
    fun hde g h u hu => ⟨intMat_mono u l _ hde (h u hu).1, intMat_mono u l _ hde (h u hu).2⟩
  have hcover : ∀ g : UA E n, ∃ d : ℕ, DenomLe l d g := by
    intro g
    have h1 : ∀ u : HeightOneSpectrum (𝓞 E), ∃ d : ℕ, ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))) := by
      intro u
      by_cases hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal
      · obtain ⟨d₁, h₁⟩ := exists_intMat u hu ((cLoc u g : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))
        obtain ⟨d₂, h₂⟩ := exists_intMat u hu (((cLoc u g)⁻¹ : GL (Fin n) (u.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (u.adicCompletion E))
        exact ⟨max d₁ d₂, fun _ => ⟨intMat_mono u l _ (le_max_left _ _) h₁, intMat_mono u l _ (le_max_right _ _) h₂⟩⟩
      · exact ⟨0, fun h => absurd h hu⟩
    choose D hD using h1
    refine ⟨hS.toFinset.sup D, fun u hu => ?_⟩
    have hle : D u ≤ hS.toFinset.sup D := Finset.le_sup (hS.mem_toFinset.2 hu)
    exact ⟨intMat_mono u l _ hle (hD u hu).1, intMat_mono u l _ hle (hD u hu).2⟩
  obtain ⟨d, hd⟩ := hZ.elim_directed_cover (fun d : ℕ => {g : UA E n | DenomLe l d g}) hopen
    (fun g _ => Set.mem_iUnion.2 (hcover g))
    (directed_of_isDirected_le fun _ _ hde g hg => hmono hde g hg)
  exact ⟨d, fun g hg => hd hg⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DetBound
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private lemma norm_det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 1 ≤ R) (h : ∀ i j, ‖ι.symm (M i j)‖ ≤ R) : ‖ι.symm M.det‖ ≤ R ^ n :=
  _root_.UpperTheory.Reformulated.B.Qh59.norm_det_le ι M R hR h

theorem UpperTheory.Gal.Gen.detBound_pf :
    UpperTheory.Gal.Gen.DetBound := by
  intro l _ ι T _ n lam A R hR h
  have hR0 : (0 : ℝ) ≤ R := zero_le_one.trans hR
  rw [Formalism.L2.DIV.detTw_eq, map_prod, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have h1 := norm_det_le ι ((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).1
  have h2 := norm_det_le ι (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).2
  have hinv : (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det =
      (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [pow_mul]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (lam τ).detShift
  · rw [hk, zpow_natCast, map_pow, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 k
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow, ← hinv, map_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 k
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DiscAHomog
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private noncomputable def discA (a n : ℕ) : MvPolynomial (Fin a) ℤ :=
  ∏ p ∈ (Finset.univ : Finset (Fin a)).offDiag, ∏ c ∈ Finset.Icc 1 n,
    (MvPolynomial.X p.1 ^ c - MvPolynomial.X p.2 ^ c)

private noncomputable def discB (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  ∏ q ∈ (Finset.univ : Finset (Fin a × Fin a × Fin a)).filter
      (fun q => ¬ (q.1 = q.2.1 ∧ q.2.2 = q.2.1)),
    (MvPolynomial.X q.1 * MvPolynomial.X q.2.2 - MvPolynomial.X q.2.1 ^ 2)

private theorem discA_symm (a n : ℕ) : (discA a n).IsSymmetric := by
  intro σ
  simp only [discA, map_prod, map_sub, map_pow, MvPolynomial.rename_X]
  refine Finset.prod_equiv (σ.prodCongr σ) ?_ ?_
  · rintro ⟨i, j⟩
    simp [Finset.mem_offDiag]
  · intro p _
    rfl

private theorem discB_symm (a : ℕ) : (discB a).IsSymmetric := by
  intro σ
  simp only [discB, map_prod, map_sub, map_mul, map_pow, MvPolynomial.rename_X]
  refine Finset.prod_equiv (σ.prodCongr (σ.prodCongr σ)) ?_ ?_
  · rintro ⟨i, j, k⟩
    simp
  · intro p _
    rfl

private theorem discA_homog (a n : ℕ) : ∃ d, (discA a n).IsHomogeneous d := by
  refine ⟨_, MvPolynomial.IsHomogeneous.prod _ _ (fun _ => ∑ c ∈ Finset.Icc 1 n, c) fun p _ =>
    MvPolynomial.IsHomogeneous.prod _ _ (fun c => c) fun c _ => ?_⟩
  exact (MvPolynomial.isHomogeneous_X_pow _ _).sub (MvPolynomial.isHomogeneous_X_pow _ _)

private theorem discB_homog (a : ℕ) : ∃ d, (discB a).IsHomogeneous d := by
  refine ⟨_, MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 2) fun q _ => ?_⟩
  exact ((MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)).sub
    (MvPolynomial.isHomogeneous_X_pow _ _)

private theorem discA_ne (a n : ℕ) : discA a n ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun p hp => Finset.prod_ne_zero_iff.2 fun c hc h => ?_
  have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.1 hp).2.2
  have hc0 : c ≠ 0 := by
    have := (Finset.mem_Icc.1 hc).1
    omega
  have := congrArg (MvPolynomial.eval (Pi.single p.1 (1 : ℤ))) h
  simp [Pi.single_eq_of_ne hne.symm, hc0] at this

private theorem discB_ne (a : ℕ) : discB a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun q hq h => ?_
  have hq' : ¬ (q.1 = q.2.1 ∧ q.2.2 = q.2.1) := (Finset.mem_filter.1 hq).2
  have hz : (Pi.single q.2.1 (1 : ℤ) : Fin a → ℤ) q.1 * (Pi.single q.2.1 (1 : ℤ) : Fin a → ℤ) q.2.2 = 0 := by
    by_cases h1 : q.1 = q.2.1
    · have h2 : q.2.2 ≠ q.2.1 := fun h2 => hq' ⟨h1, h2⟩
      rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul]
  have := congrArg (MvPolynomial.eval (Pi.single q.2.1 (1 : ℤ))) h
  simp only [map_sub, map_mul, map_pow, MvPolynomial.eval_X, map_zero, hz, Pi.single_eq_same] at this
  norm_num at this

theorem UpperTheory.Gal.Gen.discEx2_pf :
    UpperTheory.Gal.Gen.DiscEx2 := by
  intro a n
  have hne : discA a n * discB a ≠ 0 := mul_ne_zero (discA_ne a n) (discB_ne a)
  obtain ⟨d₁, h₁⟩ := discA_homog a n
  obtain ⟨d₂, h₂⟩ := discB_homog a
  have hh := h₁.mul h₂
  refine ⟨discA a n * discB a, ?_, ?_, hne, ?_⟩
  · intro σ
    rw [map_mul, discA_symm a n σ, discB_symm a σ]
  · rw [hh.totalDegree hne]
    exact hh
  · intro k _ z hz
    rw [map_mul] at hz
    have hA := left_ne_zero_of_mul hz
    have hB := right_ne_zero_of_mul hz
    simp only [discA, discB, map_prod, map_sub, map_mul, map_pow, MvPolynomial.aeval_X] at hA hB
    refine ⟨fun i j hij c hc1 hcn => ?_, fun i j k' hq => ?_⟩
    · have h1 := Finset.prod_ne_zero_iff.1 hA (i, j)
        (Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩)
      exact sub_ne_zero.1 (Finset.prod_ne_zero_iff.1 h1 c (Finset.mem_Icc.2 ⟨hc1, hcn⟩))
    · exact sub_ne_zero.1 (Finset.prod_ne_zero_iff.1 hB (i, j, k')
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.FrameW
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem cAll_fin' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {c : UA E n}
    (hc : c ∈ finU E n) : cAll c = 1 := by
  funext v
  have : cInf c = 1 := hc
  simp [cAll, cEmb, this]

theorem UpperTheory.Gal.Gen.frameW_pf :
    UpperTheory.Gal.Gen.Kappa → UpperTheory.Gal.Gen.DenomBdd → UpperTheory.Gal.Gen.RhoBound → UpperTheory.Gal.Gen.LatFacts → UpperTheory.Gal.Gen.LevelEx → UpperTheory.Gal.Gen.FrameW := by
  intro hK hD hR hL hE E _ _ _ l _ ι a W J t ht
  classical
  have hlp : l.Prime := Fact.out
  obtain ⟨κ, hκr, hκi, hκd⟩ := hK E l ι a
  let ρ := Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W
  let M : UA E a → (InfinitePlace E → GL (Fin a) ℂ) := fun g => (cAll g)⁻¹ * κ g
  let b : UA E a → {x : W.Sp // CoefLe ι 1 x.1} → W.Sp := fun g x => ρ (M g) x.1
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlp.one_lt.le
  have hpow : ∀ d : ℕ, (1 : ℝ) ≤ (l : ℝ) ^ d := fun d => one_le_pow₀ hl1
  have hgrow : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c) x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c) _ (hpow d) (fun τ i j => hκd c d hc τ i j) x hx
  have hgrowInv : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c)⁻¹ x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c)⁻¹ _ (hpow d) (fun τ i j => by
      have h := hκd c d hc τ i j
      simp only [Pi.inv_apply, inv_inv]
      exact ⟨h.2, h.1⟩) x hx
  have hval : ∀ f : algForms W, ∀ γ ∈ ratU E a, ∀ s x, x ∈ infU E a → ∀ c : finU E a,
      (∀ v g, f.1 v (g * (c : UA E a)) = f.1 v g) → ∀ v,
      f.1 (ρ (M (γ * s * x * c)) v) (γ * s * x * c) = f.1 (ρ (M s) (ρ (κ (c : UA E a)) v)) s := by
    intro f γ hγ s x hx c hf v
    have hM : cAll x * M (γ * s * x * c) = M s * κ (c : UA E a) := by
      simp only [M, map_mul, hκr γ hγ, hκi x hx, cAll_fin' c.2, mul_one]
      group
    have hA : ∀ v, f.1 v (γ * s * x * c) = f.1 v (s * c * x) := by
      intro v
      rw [mul_assoc γ s, mul_assoc γ, (f.2.1 v).left γ hγ, mul_assoc s x, ← fin_mul_inf c.2 hx, ← mul_assoc]
    have hB : ∀ v, f.1 v (s * c * x) = f.1 (W.rep ⟨x, hx⟩ v) (s * c) := by
      intro v
      rw [f.2.2 ⟨x, hx⟩ v]
      rfl
    have e3 : W.rep ⟨x, hx⟩ (ρ (M (γ * s * x * c)) v) = ρ (M s) (ρ (κ (c : UA E a)) v) := by
      change ρ (cAll x) (ρ (M _) v) = _
      rw [← Module.End.mul_apply, ← map_mul, hM, map_mul, Module.End.mul_apply]
    rw [hA, hB, hf, e3]
  refine ⟨{x : W.Sp // CoefLe ι 1 x.1}, b, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨C, hC, hfC⟩ := hE E a W f
    obtain ⟨d, hd⟩ := hD E l hlp a C hC.compact
    let C₃ : Subgroup (finU E a) := C.subgroupOf (finU E a)
    have hC₃o : IsOpen (C₃ : Set (finU E a)) := by
      obtain ⟨N, hNo, hN1, hNC⟩ := hC.isOpen
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
        (Filter.mem_of_superset ((hNo.preimage continuous_subtype_val).mem_nhds hN1) ?_)
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, x.2⟩)
    obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a C₃ hC₃o
    let φ : UA E a → (W.Sp →ₗ[ℂ] ℂ) := fun s => (LinearMap.proj s) ∘ₗ f.1 ∘ₗ (ρ (M s))
    have hφ : ∀ s, ∃ m : ℝ, 0 ≤ m ∧ ∀ (R : ℝ) (x : W.Sp), CoefLe ι R x.1 → ‖ι.symm (φ s x)‖ ≤ m * R :=
      fun s => (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).1 (φ s)
    choose m hm0 hm using hφ
    refine ⟨(∑ s ∈ S, m s) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at), fun g i => ?_⟩
    obtain ⟨γ, hγ, s, hs, y, hy, c, hc, rfl⟩ := hS g
    have hcC : (c : UA E a) ∈ C := Subgroup.mem_subgroupOf.1 hc
    have e := hval f γ hγ s y hy c (fun v g => hfC _ hcC v g) i.1
    have hb : f.1 (b (γ * s * y * c) i) (γ * s * y * c) = φ s (ρ (κ (c : UA E a)) i.1) := e
    rw [hb]
    refine (hm s _ _ (hgrow _ d (hd _ hcC) i.1 i.2)).trans ?_
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => hm0 q) hs) (by positivity)
  · intro f h0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    funext g
    obtain ⟨c, hc0, hc⟩ := (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).2 (ρ (M g)⁻¹ v)
    have h1 := h0 g ⟨c • ρ (M g)⁻¹ v, hc⟩
    have h2 : b g ⟨c • ρ (M g)⁻¹ v, hc⟩ = c • v := by
      change ρ (M g) (c • ρ (M g)⁻¹ v) = c • v
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h2, map_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  · intro F R hF j g i
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hF g i)
    have e : opOf (RU E a) (t j) (F (b g i)) g = ∑ h ∈ (t j).support, t j h * F (b g i) (g * h) := by
      simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]
    rw [e, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun h hh => ?_
    obtain ⟨hfin, d, hd, hn⟩ := ht j h hh
    have hMh : M g = M (g * h) * (κ h)⁻¹ := by
      simp only [M, map_mul, cAll_fin' hfin, mul_one]
      group
    set y : W.Sp := ρ (κ h)⁻¹ i.1 with hy
    have hyc := hgrowInv h d hd i.1 i.2
    have hx : CoefLe ι 1 ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) := by
      intro q
      have hq := hyc q
      have e1 : MvPolynomial.coeff q ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) =
          t j h * MvPolynomial.coeff q (y : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) := by
        simp [MvPolynomial.coeff_smul]
      rw [e1, map_mul, norm_mul]
      have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
      calc _ ≤ ((l : ℝ)⁻¹) ^ (a * d * GlobalTheory.CongW.wtSize W.at) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at) :=
            mul_le_mul hn hq (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [← pow_mul, inv_pow, show d * (a * GlobalTheory.CongW.wtSize W.at) = a * d * GlobalTheory.CongW.wtSize W.at by ring]
            exact inv_mul_cancel₀ (by positivity)
    have hb : t j h * F (b g i) (g * h) = F (b (g * h) ⟨t j h • y, hx⟩) (g * h) := by
      have : b g i = ρ (M (g * h)) y := by
        change ρ (M g) i.1 = _
        rw [hMh, map_mul, Module.End.mul_apply]
      change _ = F (ρ (M (g * h)) (t j h • y)) (g * h)
      rw [this, map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hb]
    exact hF _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.KerOpen
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.kerOpen_pf :
    UpperTheory.Gal.Gen.PowNhds → UpperTheory.Gal.Gen.KerOpen := by
  intro hP E _ _ w a J hJ A _ _ θ
  have hN : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hV := hP E w a (Nat.card A) hN (J : Set (GL (Fin a) (w.adicCompletion E)))
    (hJ.mem_nhds J.one_mem)
  refine ⟨interior ((fun x => x ^ Nat.card A) '' (J : Set (GL (Fin a) (w.adicCompletion E)))),
    isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := interior_subset hx
  have hx' : x = (⟨y, hy⟩ : J) ^ Nat.card A := Subtype.ext (by simpa using hxy.symm)
  rw [hx', map_pow, pow_card_eq_one']
end

