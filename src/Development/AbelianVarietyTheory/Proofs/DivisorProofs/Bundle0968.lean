import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLower
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.SDown

theorem pderiv_aeval_sum {σ δ : Type} [Fintype σ] [DecidableEq σ] (f : σ → MvPolynomial δ ℂ) (i : δ)
    (G : MvPolynomial σ ℂ) : pderiv i (aeval f G) = ∑ u, pderiv i (f u) * aeval f (pderiv u G) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, aeval_X, hp, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]; simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem derivation_finset_prod {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι]
    (D : Derivation R A A) (f : ι → A) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha,
      Function.update_self]
    have h1 : ∏ j ∈ s, Function.update f a (D (f a)) j = ∏ j ∈ s, f j := by
      refine Finset.prod_congr rfl fun j hj => ?_
      exact Function.update_of_ne (by rintro rfl; exact ha hj) _ _
    have h2 : ∀ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j =
        f a * ∏ j ∈ s, Function.update f i (D (f i)) j := by
      intro i hi
      rw [Finset.prod_insert ha, Function.update_of_ne (by rintro rfl; exact ha hi)]
    rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
    ring

theorem derivation_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j => D (M i j)).det := by
  have key : ∀ B : Matrix n n A, B.det = ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, B i (σ i) := by
    intro B
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [key, map_sum]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivation_finset_prod, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.smul_def]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp [Matrix.updateRow_self]
  · rw [Function.update_of_ne hj, Matrix.updateRow_ne hj]

theorem derivation_sum_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} (s : Finset ι)
    (D : ι → Derivation R A A) (x : A) : (∑ t ∈ s, D t) x = ∑ t ∈ s, D t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

variable {P Q S : ℕ}

theorem pderiv_u_mS (a : Fin P) (c : Fin S) (a0 : Fin P) (b0 : Fin Q) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (mS P Q S a0 b0) =
      if a0 = a then X (Sum.inr b0, Sum.inr c) else 0 := by
  classical
  simp [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pderiv_t_mS (b : Fin Q) (c : Fin S) (a0 : Fin P) (b0 : Fin Q) :
    pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (mS P Q S a0 b0) =
      if b0 = b then X (Sum.inl a0, Sum.inr c) else 0 := by
  classical
  simp [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pderiv_u_detS (h : Q ≤ S) (a : Fin P) (c : Fin S) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (detS P Q S h) = 0 := by
  classical
  rw [detS, derivation_det]
  refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
  simp [pderiv_X, Pi.single_apply]

theorem sum_X_pderiv_detS (h : Q ≤ S) (b b' : Fin Q) :
    ∑ c : Fin S, X ((Sum.inr b', Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b, Sum.inr c) (detS P Q S h) =
      if b' = b then detS P Q S h else 0 := by
  classical
  let Dd : Derivation ℂ (Pol P Q 0 S) (Pol P Q 0 S) :=
    ∑ c : Fin S, (X (Sum.inr b', Sum.inr c) : Pol P Q 0 S) • pderiv (Sum.inr b, Sum.inr c)
  have hD : ∀ p, Dd p = ∑ c : Fin S, X ((Sum.inr b', Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b, Sum.inr c) p := by
    intro p; simp only [Dd, derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]
  rw [← hD, detS, derivation_det]
  have hrow : ∀ i j : Fin Q, Dd ((Matrix.of fun b c : Fin Q => (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)) i j) =
      if i = b then X (Sum.inr b', Sum.inr (Fin.castLE h j)) else 0 := by
    intro i j
    rw [hD]
    by_cases hi : i = b
    · subst hi; simp [pderiv_X, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [pderiv_X, Pi.single_apply, hi]
  simp_rw [hrow]
  rw [Finset.sum_eq_single b]
  · simp only [if_true]
    split_ifs with hb
    · subst hb
      congr 1
      ext i j
      by_cases hi : i = b' <;> simp [Matrix.updateRow_apply, hi]
    · refine Matrix.det_zero_of_row_eq hb ?_
      ext j
      simp [Matrix.updateRow_apply, Ne.symm hb]
  · intro i _ hi
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    simp [hi]
  · simp

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair.SDown

variable {P Q S : ℕ}

theorem pderiv_u_aeval (a : Fin P) (c : Fin S) (H : Mdl P Q) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) H) =
      ∑ b0 : Fin Q, X (Sum.inr b0, Sum.inr c) * aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a, b0) H) := by
  classical
  rw [pderiv_aeval_sum, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [pderiv_u_mS]
  · intro a0 _ ha0; simp [pderiv_u_mS, ha0]
  · simp

theorem pderiv_t_aeval (b : Fin Q) (c : Fin S) (H : Mdl P Q) :
    pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) H) =
      ∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) * aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a0, b) H) := by
  classical
  rw [pderiv_aeval_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  rw [Finset.sum_eq_single b]
  · simp [pderiv_t_mS]
  · intro b0 _ hb0; simp [pderiv_t_mS, hb0]
  · simp

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair.SDown

variable {P Q S : ℕ}

theorem rhs_eq (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G) =
      (∑ a0 : Fin P, ∑ b0 : Fin Q, mS P Q S a0 b0 *
          aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a0, b) (pderiv (a, b0) G)) +
        ((S + k' : ℕ) : ℂ) • aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a, b) G)) *
        detS P Q S h ^ k' := by
  simp [embS, opS, mulM, derM, LinearMap.sum_apply, map_sum, Module.End.mul_apply]

theorem key (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin S, pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (pderiv (Sum.inl a, Sum.inr c) (embS P Q S h k' G)) =
      embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G) := by
  classical
  rw [rhs_eq]
  set m : Fin P × Fin Q → Pol P Q 0 S := fun ab => mS P Q S ab.1 ab.2 with hm
  set D := detS P Q S h with hDdef
  have hE : embS P Q S h k' G = aeval m G * D ^ k' := by simp [embS, hm, hDdef]
  have step1 : ∀ c : Fin S, pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (embS P Q S h k' G) =
      ∑ b0 : Fin Q, X (Sum.inr b0, Sum.inr c) * aeval m (pderiv (a, b0) G) * D ^ k' := by
    intro c
    rw [hE, Derivation.leibniz, Derivation.leibniz_pow, hDdef, pderiv_u_detS, hm, pderiv_u_aeval]
    simp only [mul_zero, smul_zero, zero_add, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    ring
  have step2 : ∀ (c : Fin S) (b0 : Fin Q),
      pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (X (Sum.inr b0, Sum.inr c) * aeval m (pderiv (a, b0) G) * D ^ k') =
        (if b0 = b then aeval m (pderiv (a, b) G) * D ^ k' else 0) +
        X (Sum.inr b0, Sum.inr c) * (∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) *
            aeval m (pderiv (a0, b) (pderiv (a, b0) G))) * D ^ k' +
        aeval m (pderiv (a, b0) G) * ((k' : Pol P Q 0 S) * D ^ (k' - 1)) *
          (X (Sum.inr b0, Sum.inr c) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D) := by
    intro c b0
    rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hm, pderiv_t_aeval, pderiv_X, Pi.single_apply]
    simp only [smul_eq_mul, nsmul_eq_mul, Prod.mk.injEq, Sum.inr.injEq, and_true]
    by_cases hb : b0 = b
    · subst hb
      simp only [if_true]
      ring
    · simp only [hb, if_false]
      ring
  have hT1 : ∑ c : Fin S, ∑ b0 : Fin Q, X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * (∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) *
      aeval m (pderiv (a0, b) (pderiv (a, b0) G))) * D ^ k' =
      ∑ a0 : Fin P, ∑ b0 : Fin Q, mS P Q S a0 b0 * aeval m (pderiv (a0, b) (pderiv (a, b0) G)) * D ^ k' := by
    simp only [mS, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a0 _ => Finset.sum_congr rfl fun c _ => by ring
  have hT3 : ∑ c : Fin S, ∑ b0 : Fin Q, aeval m (pderiv (a, b0) G) * ((k' : Pol P Q 0 S) * D ^ (k' - 1)) *
      (X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D) =
      (k' : Pol P Q 0 S) * aeval m (pderiv (a, b) G) * D ^ k' := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have e : ∀ b0 : Fin Q, ∑ c : Fin S, X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D =
        if b0 = b then D else 0 := fun b0 => by rw [hDdef]; exact sum_X_pderiv_detS h b b0
    simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases k' with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; ring
  have hT0 : ∑ c : Fin S, ∑ b0 : Fin Q, (if b0 = b then aeval m (pderiv (a, b) G) * D ^ k' else 0) =
      (S : Pol P Q 0 S) * aeval m (pderiv (a, b) G) * D ^ k' := by
    simp [Finset.sum_ite_eq', mul_assoc]
  simp_rw [step1, map_sum, step2, Finset.sum_add_distrib]
  rw [hT0, hT1, hT3, Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul, add_mul, Finset.sum_mul]
  simp only [Finset.sum_mul]
  push_cast
  ring

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair

theorem fockAct1_Eab_inr_inl_embS_pair : ∀ (P Q S : ℕ) (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q)
    (f : Pol P Q 0 S), GlobalTheory.DefLift.BilFischer.pair (fockAct1 P Q 0 S (Eab (Sum.inr b) (Sum.inl a)) f)
      (embS P Q S h k' G) = GlobalTheory.DefLift.BilFischer.pair f (embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G)) := by
  intro P Q S h k' a b G f
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  have hterm : ∀ c : Fin S, omE ((Sum.inr b : Ix P Q), (Sum.inr c : Ix 0 S)) (Sum.inl a, Sum.inr c) f =
      (f * X (Sum.inr b, Sum.inr c)) * X (Sum.inl a, Sum.inr c) := by
    intro c
    simp [omE, raiB, lowB, linePos]
    ring
  simp only [hterm, map_sum, LinearMap.sum_apply, GlobalTheory.DefLift.BilFischer.pair_mul_X]
  rw [← map_sum]
  exact congrArg _ (SDown.key h k' a b G)

end GlobalTheory.CharPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSchemeSpecialFibreNonempty
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.FlatDVRFibre

theorem mem_basicOpen_unif_iff {O : Type} [CommRing O] {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O)) (ϖ : O) (z : Z) :
    z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ↔ ϖ ∉ (f z).asIdeal := by
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

theorem genericPoint_mem_and_exists_not_mem :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)), Flat f → Nonempty (specialFibre f) →
  genericPoint Z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ∧ ∃ z : Z, z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) := by
  intro O _ _ _ ϖ hϖ Z _ f hf hne
  refine ⟨?_, ?_⟩
  · rw [mem_basicOpen_unif_iff]
    let e : Spec (.of O) := (⊥ : PrimeSpectrum O)
    have hη : e ⤳ f (genericPoint Z) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum O))
    obtain ⟨x', hx', hx''⟩ := Flat.generalizingMap f hη
    have hxe : x' = genericPoint Z :=
      (hx'.antisymm (genericPoint_specializes x')).eq
    rw [← hxe, hx'']
    change ϖ ∉ (⊥ : Ideal O)
    simpa using hϖ.ne_zero
  · obtain ⟨p⟩ := hne
    refine ⟨specialι f p, ?_⟩
    rw [mem_basicOpen_unif_iff, not_not]
    have h1 : f (specialι f p) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
        (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) p) := by
      let p' : ↑(pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) := p
      change f (pullback.fst f _ p') = _
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [h1]
    set q := pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) p
    change ϖ ∈ Ideal.comap (IsLocalRing.residue O) q.asIdeal
    haveI := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [hq, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
    exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

end GlobalTheory.FlatDVRFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerRightCommutesEmbedding
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair

variable {P Q R : ℕ}

theorem pderiv_detR_wLetter (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (vars_rename g _ hv)
  simp [g] at hx

theorem wPolarize_aeval_mR (b b' : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c)
        (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (∑ a, X (a, b') * pderiv (a, b) G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p n hp =>
    have key : ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (mR P Q R n.1 n.2)
        = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2)
            (∑ a, X (a, b') * pderiv (a, b) (X n : Mdl P Q)) := by
      obtain ⟨a, b''⟩ := n
      by_cases hb : b'' = b
      · subst hb
        simp [mR, pderiv_X, Pi.single_apply, mul_comm]
      · simp [mR, pderiv_X, Pi.single_apply, hb]
    have e1 : ∀ (A B : Pol P Q R 0), ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (A * B) =
        (∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) A) * B +
          A * ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.mul_sum]
      exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)
        (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)
    have e2 : ∀ (A B : Mdl P Q), ∑ a, X (a, b') * pderiv (a, b) (A * B) =
        (∑ a, X (a, b') * pderiv (a, b) A) * B + A * ∑ a, X (a, b') * pderiv (a, b) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
    rw [map_mul, aeval_X, e1, hp, key, e2, map_add, map_mul, map_mul, aeval_X]

theorem fockAct1_inr_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (b b' : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inr b')) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inr b') G) := by
  intro P Q R h k b b' G
  have hD : ∀ c : Fin R, pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := fun c => by
    simp [Derivation.leibniz_pow, pderiv_detR_wLetter]
  have hw := wPolarize_aeval_mR (R := R) b b' G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    GlobalTheory.CompactHarm.omE_nn (Sum.inr b, Sum.inl _) (Sum.inr b', Sum.inl _) rfl rfl]
  simp only [embR, opR, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, pderiv_mul, hD,
    mul_zero, add_zero, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg, map_smul, Prod.mk.injEq, Sum.inr.injEq, and_true]
  have e : ∀ x : Fin P, (mulM x b') ((derM x b) G) = X (x, b') * pderiv (x, b) G := fun _ => rfl
  simp only [e, ← hw, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_mul, mul_assoc]
  rw [sub_right_inj]
  split_ifs
  · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    ring
  · simp

end GlobalTheory.CharPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockInvariantSubspaceEquivariantProjection
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair GlobalTheory.FockAlg

namespace GlobalTheory.FockProj

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem inner_homog_eq (hι : IsFockIP ι) {n : ℕ} {h : MvPolynomial σ ℂ} (hh : h.IsHomogeneous n)
    (g : MvPolynomial σ ℂ) :
    inner ℂ (ι h) (ι g) = inner ℂ (ι h) (ι (homogeneousComponent n g)) := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [map_sum, inner_sum]
  by_cases hn : n ∈ Finset.range (g.totalDegree + 1)
  · rw [Finset.sum_eq_single_of_mem n hn]
    intro m _ hmn
    exact GlobalTheory.FockAdj.inner_eq_zero_of_isHomogeneous hι (Ne.symm hmn) hh
      (homogeneousComponent_isHomogeneous m g)
  · have hlt : g.totalDegree < n := by simp at hn; omega
    rw [homogeneousComponent_eq_zero n g hlt, map_zero, inner_zero_right]
    refine Finset.sum_eq_zero fun m hm => ?_
    have : m ≠ n := by simp at hm; omega
    exact GlobalTheory.FockAdj.inner_eq_zero_of_isHomogeneous hι (Ne.symm this) hh
      (homogeneousComponent_isHomogeneous m g)

theorem isCompl_orth [Finite σ] (hι : IsFockIP ι) (hinj : Function.Injective ι)
    (W : Submodule ℂ (MvPolynomial σ ℂ)) (hW : ∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) :
    IsCompl W ((W.map ι)ᗮ.comap ι) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxC
    have h0 : inner ℂ (ι x) (ι x) = 0 :=
      (Submodule.mem_orthogonal _ _).1 (Submodule.mem_comap.1 hxC) (ι x) (Submodule.mem_map_of_mem hx)
    rw [inner_self_eq_zero] at h0
    exact hinj (by rw [h0, map_zero])
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro f
    rw [← sum_homogeneousComponent f]
    refine Submodule.sum_mem _ fun n _ => ?_
    set h := homogeneousComponent n f
    have hh : h.IsHomogeneous n := homogeneousComponent_isHomogeneous n f
    let Wn : Submodule ℂ (MvPolynomial σ ℂ) := W ⊓ homogeneousSubmodule σ ℂ n
    haveI : FiniteDimensional ℂ (homogeneousSubmodule σ ℂ n) :=
      Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ ℂ n)
    haveI : FiniteDimensional ℂ Wn := Submodule.finiteDimensional_of_le inf_le_right
    let K : Submodule ℂ H := Wn.map ι
    haveI : FiniteDimensional ℂ K := inferInstance
    obtain ⟨w, hwWn, hwk⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem (ι h))
    have hwn : w.IsHomogeneous n := (mem_homogeneousSubmodule n w).1 hwWn.2
    refine Submodule.mem_sup.2 ⟨w, hwWn.1, h - w, ?_, add_sub_cancel _ _⟩
    rw [Submodule.mem_comap, Submodule.mem_orthogonal]
    rintro v ⟨w', hw', rfl⟩
    rw [inner_eq_zero_symm, inner_homog_eq hι (hh.sub hwn), map_sub, hwk]
    refine Submodule.starProjection_inner_eq_zero (K := K) _ _ ?_
    exact Submodule.mem_map_of_mem ⟨hW w' hw' n, homogeneousComponent_mem n w'⟩

theorem exists_equivariant_proj : ∀ (p q r s : ℕ) (W : Submodule ℂ (Pol p q r s)),
    (∀ Z, ∀ f ∈ W, fockAct1 p q r s Z f ∈ W) → (∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) →
    ∃ π : Pol p q r s →ₗ[ℂ] Pol p q r s, (∀ f, π f ∈ W) ∧ (∀ f ∈ W, π f = f) ∧
      ∀ Z f, π (fockAct1 p q r s Z f) = fockAct1 p q r s Z (π f) := by
  intro p q r s W hst hgr
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln p q r s)
  set C : Submodule ℂ (Pol p q r s) := (W.map ι)ᗮ.comap ι with hCdef
  have hc : IsCompl W C := isCompl_orth hι hinj W hgr
  have hCst : ∀ Z, ∀ u ∈ C, fockAct1 p q r s Z u ∈ C := by
    intro Z u hu
    rw [hCdef, Submodule.mem_comap, Submodule.mem_orthogonal] at hu ⊢
    rintro v ⟨w, hw, rfl⟩
    rw [inner_eq_zero_symm,
      (GlobalTheory.FockAdj.fock_adjoints p q r s _ ι hι).2.1 Z u w, inner_eq_zero_symm]
    exact hu _ (Submodule.mem_map_of_mem (hst _ w hw))
  let π : Pol p q r s →ₗ[ℂ] Pol p q r s := W.subtype ∘ₗ W.linearProjOfIsCompl C hc
  have hmem : ∀ f, π f ∈ W := fun f => (W.linearProjOfIsCompl C hc f).2
  have hπW : ∀ f ∈ W, π f = f := fun f hf =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨f, hf⟩)
  have hπC : ∀ u ∈ C, π u = 0 := fun u hu => by
    have h0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 hu
    exact (congrArg Subtype.val h0).trans rfl
  have hsub : ∀ f, f - π f ∈ C := fun f => by
    have key : W.linearProjOfIsCompl C hc (π f) = W.linearProjOfIsCompl C hc f :=
      Submodule.linearProjOfIsCompl_apply_left hc (W.linearProjOfIsCompl C hc f)
    have h1 := (W.linearProjOfIsCompl C hc).map_sub f (π f)
    rw [key, sub_self] at h1
    exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).1 h1
  refine ⟨π, hmem, hπW, fun Z f => ?_⟩
  have hf : f = π f + (f - π f) := (add_sub_cancel _ _).symm
  conv_lhs => rw [hf]
  rw [map_add, map_add, hπW _ (hst Z _ (hmem f)), hπC _ (hCst Z _ (hsub f)), add_zero]

end GlobalTheory.FockProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (negSp S) T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (k : FVar D T.rank S.rank →₀ ℕ) (x : WO S T), pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) x = starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) x) := by
  first | exact @GlobalTheory.FockConj.pureTensorO_negSp_monomial | exact GlobalTheory.FockConj.pureTensorO_negSp_monomial | (intros; apply GlobalTheory.FockConj.pureTensorO_negSp_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobQIterateSelf
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem frobQ_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ x : Qr p r, (⇑(frobQ p r))^[r] x = x := by
  intro p _ r hr x
  have h : (⇑(frobQ p r) : Qr p r → Qr p r) = ⇑(GlobalTheory.LKLoc.frobR p (Q0 p) r) := rfl
  rw [h]
  exact GlobalTheory.LKLoc.frobR_iterate_self p (Q0 p) (by infer_instance) r hr x

end GlobalTheory.LKRes
end

