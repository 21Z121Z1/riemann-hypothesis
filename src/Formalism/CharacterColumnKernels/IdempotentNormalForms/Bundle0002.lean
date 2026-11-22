import Formalism.CharacterColumnKernels.Bundle0001
import Formalism.CharacterColumnKernels.Bundle0002
import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0001
import Formalism.CharacterColumnKernels.StatementX
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelLengthBound
section
open Finset

namespace Formalism.NG

private lemma padicValInt_eq_emultiplicity (l : ℕ) [hl : Fact l.Prime] {z : ℤ} (hz : z ≠ 0) :
    (padicValInt l z : ℕ∞) = emultiplicity (l : ℤ) z := by
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  rw [show padicValInt l z = padicValNat l z.natAbs from rfl, padicValNat_eq_emultiplicity hz',
    ← Int.natCast_emultiplicity, Int.natCast_natAbs]
  rcases abs_choice z with h | h
  · rw [h]
  · rw [h, emultiplicity_neg]

private lemma padicValInt_pow_sub_one_eq_add (l : ℕ) [hl : Fact l.Prime] (s₀ : ℕ) (hs : 1 ≤ s₀) (hs2 : l = 2 → 2 ≤ s₀)
    (x : ℤ) (hx1 : (l : ℤ) ^ s₀ ∣ x - 1) (hx2 : ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1)
    (n : ℕ) (hn0 : n ≠ 0) :
    x ^ n - 1 ≠ 0 ∧ padicValInt l (x ^ n - 1) = s₀ + padicValNat l n := by
  have hlp := hl.out
  have hE1 : emultiplicity (l : ℤ) (x - 1) = s₀ := emultiplicity_eq_coe.mpr ⟨hx1, hx2⟩
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h hdvd; simpa using this
    exact (Nat.prime_iff_prime_int.mp hlp).not_dvd_one h1
  have hE : emultiplicity (l : ℤ) (x ^ n - 1) = (s₀ : ℕ∞) + emultiplicity l n := by
    rcases hlp.eq_two_or_odd' with h2 | hodd
    · subst h2
      have h4 : (4 : ℤ) ∣ x - 1 := by
        have := (pow_dvd_pow ((2 : ℕ) : ℤ) (hs2 rfl)).trans hx1
        norm_num at this
        exact this
      push_cast at hlx hE1 ⊢
      have := Int.two_pow_sub_pow' n h4 hlx
      rw [one_pow] at this
      have hc := Int.natCast_emultiplicity 2 n
      push_cast at hc
      rw [this, hE1, hc]
    · have := Int.emultiplicity_pow_sub_pow hlp hodd (y := 1) hdvd hlx n
      rw [one_pow] at this
      rw [this, hE1]
  have hfin : emultiplicity (l : ℤ) (x ^ n - 1) = ((s₀ + padicValNat l n : ℕ) : ℕ∞) := by
    rw [hE, ← padicValNat_eq_emultiplicity hn0]
    norm_cast
  have hne : x ^ n - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hfin
    exact ENat.top_ne_coe _ hfin
  refine ⟨hne, ?_⟩
  have := padicValInt_eq_emultiplicity l hne
  rw [hfin] at this
  exact_mod_cast this

theorem character_column_kernel_length_bound : characterColumnKernelLengthBound := by
  intro l hl s₀ hs hs2 x hx1 hx2 a b hab
  have hlp := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨hne, hv⟩ := padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (b - a) (by omega)
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x ^ a := by
    intro h
    have h' : (l : ℤ) ∣ x := hlp.dvd_of_dvd_pow h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h' hdvd; simpa using this
    exact hlp.not_dvd_one h1
  have hxa : x ^ a ≠ 0 := fun h ↦ hlx (h ▸ dvd_zero _)
  have e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_of_le hab.le, mul_one]
  rw [e, padicValInt.mul hxa hne, padicValInt.eq_zero_of_not_dvd hlx, zero_add, hv]

private lemma prod_univ_erase_zero_eq_prod_succ {M : Type*} [CommMonoid M] (t : ℕ) (f : Fin (t + 1) → M) :
    ∏ i ∈ univ.erase (0 : Fin (t + 1)), f i = ∏ i : Fin t, f i.succ := by
  rw [Fin.univ_succ, Finset.erase_cons, Finset.prod_map]
  rfl

theorem idempotentNormalForms_fact : characterColumnKernelBlockBound := by
  intro l hl s₀ hs hs2 x hx1 hx2 u hu w t
  have hlp := Nat.prime_iff_prime_int.mp hl.out
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h hdvd; simpa using this
    exact hlp.not_dvd_one h1
  have hux : ¬ (l : ℤ) ∣ u * x ^ w := by
    intro h
    rcases hlp.dvd_or_dvd h with h | h
    · exact hu h
    · exact hlx (hlp.dvd_of_dvd_pow h)
  have hux0 : u * x ^ w ≠ 0 := fun h ↦ hux (h ▸ dvd_zero _)
  have hneg : ∀ z : ℤ, padicValInt l (-z) = padicValInt l z := fun z ↦ by simp [padicValInt]
  have hg : ∀ i : ℕ, u * x ^ w - u * x ^ (w + (i + 1)) ≠ 0 ∧
      padicValInt l (u * x ^ w - u * x ^ (w + (i + 1))) = s₀ + padicValNat l (i + 1) := by
    intro i
    obtain ⟨hne, hv⟩ := padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (i + 1) (by omega)
    have e : u * x ^ w - u * x ^ (w + (i + 1)) = -((u * x ^ w) * (x ^ (i + 1) - 1)) := by ring
    have hm : (u * x ^ w) * (x ^ (i + 1) - 1) ≠ 0 := mul_ne_zero hux0 hne
    refine ⟨by rw [e]; exact neg_ne_zero.mpr hm, ?_⟩
    rw [e, hneg, padicValInt.mul hux0 hne, padicValInt.eq_zero_of_not_dvd hux, zero_add, hv]
  have key : ∀ t : ℕ, (∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1)))) ≠ 0 ∧
      padicValInt l (∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1)))) =
        t * s₀ + padicValNat l t.factorial := by
    intro t
    induction t with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ]
      refine ⟨mul_ne_zero ih.1 (hg k).1, ?_⟩
      rw [padicValInt.mul ih.1 (hg k).1, ih.2, (hg k).2, Nat.factorial_succ,
        padicValNat.mul (by omega) (Nat.factorial_ne_zero k)]
      ring
  have hd : delta (fun i : Fin (t + 1) ↦ u * x ^ (w + (i : ℕ))) =
      ∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1))) := by
    rw [delta, prod_univ_erase_zero_eq_prod_succ]
    simp only [Fin.val_zero, Fin.val_succ, add_zero]
    exact Fin.prod_univ_eq_prod_range (fun i ↦ u * x ^ w - u * x ^ (w + (i + 1))) t
  rw [hd, (key t).2]

end Formalism.NG
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.GenRelMapApply
section
open Finset

noncomputable section

namespace Formalism.NG

section GenKey

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma gen_relMap_apply {a b : Type*} [Fintype a] [Fintype b] (X : Matrix a b O) (v : b → KO O) (i : a) :
    relMap O (KO O) X v i = ∑ j, X i j • v j := rfl

lemma gen_relMap_mul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (X : Matrix a b O) (Y : Matrix b c O) :
    relMap O (KO O) (X * Y) = relMap O (KO O) X ∘ₗ relMap O (KO O) Y := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, gen_relMap_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

lemma gen_relMap_one {a : Type*} [Fintype a] [DecidableEq a] (v : a → KO O) :
    relMap O (KO O) (1 : Matrix a a O) v = v := by
  funext i
  simp [gen_relMap_apply, Matrix.one_apply, ite_smul]

lemma gen_key {M G : Type} [Fintype M] [DecidableEq M] [Fintype G] [DecidableEq G]
    (A : Matrix M G O) : ∃ (n : ℕ) (U : Matrix M M O) (f : Fin n ↪ M) (e : Fin n ↪ G),
      (∃ C0 : Matrix G M O, IsUnit (Matrix.of fun p q => (C0 * U) (e p) (f q)).det) ∧
      ∀ C' : Matrix G M O, IsUnit (Matrix.of fun p q => (C' * U) (e p) (f q)).det →
        LinearMap.ker (relMap O (KO O) (C' * A)) = LinearMap.ker (relMap O (KO O) A) := by
  classical
  obtain ⟨n, snf⟩ := (LinearMap.range (Matrix.mulVecLin A)).smithNormalForm (Pi.basisFun O M)
  set U : Matrix M M O := (Pi.basisFun O M).toMatrix snf.bM with hUdef
  set W : Matrix M M O := snf.bM.toMatrix (Pi.basisFun O M) with hWdef
  have hWU : W * U = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUW : U * W = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hn : n ≤ Fintype.card G := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    have h2 := LinearMap.finrank_range_le (Matrix.mulVecLin A)
    rw [h1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    exact h2
  let e : Fin n ↪ G := (Fin.castLEEmb hn).trans (Fintype.equivFin G).symm.toEmbedding
  refine ⟨n, U, snf.f, e, ?_, ?_⟩
  · refine ⟨Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0, ?_⟩
    have hZ : (Matrix.of fun p q =>
        ((Matrix.of fun i l => ∑ p, if e p = i then W (snf.f p) l else 0) * U) (e p) (snf.f q)) = 1 := by
      ext p q
      simp only [Matrix.of_apply, Matrix.mul_apply, e.injective.eq_iff, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [← Matrix.mul_apply, hWU]
      simp [Matrix.one_apply, snf.f.injective.eq_iff]
    rw [hZ, Matrix.det_one]
    exact isUnit_one
  · intro C' hC
    set Y : Matrix M G O := W * A with hYdef
    have hAY : A = U * Y := by rw [hYdef, ← Matrix.mul_assoc, hUW, Matrix.one_mul]
    have hY : ∀ k, k ∉ Set.range snf.f → ∀ j, Y k j = 0 := by
      intro k hk j
      have hmem : (fun l => A l j) ∈ LinearMap.range (Matrix.mulVecLin A) :=
        ⟨Pi.single j 1, by
          funext l
          simp⟩
      have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem⟩ hk
      rw [← Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O M)] at h0
      simpa [hYdef, Matrix.mulVec, dotProduct, Matrix.mul_apply] using h0
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      set y := relMap O (KO O) Y v with hydef
      have hy0 : ∀ k, k ∉ Set.range snf.f → y k = 0 := by
        intro k hk
        simp [hydef, gen_relMap_apply, hY k hk]
      have hv' : relMap O (KO O) (C' * U) y = 0 := by
        rw [hydef, ← LinearMap.comp_apply, ← gen_relMap_mul, Matrix.mul_assoc, ← hAY]
        exact hv
      set Z : Matrix (Fin n) (Fin n) O := Matrix.of fun p q => (C' * U) (e p) (snf.f q) with hZdef
      have hz : relMap O (KO O) Z (y ∘ snf.f) = 0 := by
        funext p
        have := congrFun hv' (e p)
        rw [gen_relMap_apply, Pi.zero_apply] at this
        rw [gen_relMap_apply, Pi.zero_apply]
        exact (Fintype.sum_of_injective snf.f snf.f.injective _ _
          (fun k hk => by simp [hy0 k hk]) (fun q => rfl)).trans this
      have hyf : y ∘ snf.f = 0 := by
        rw [← gen_relMap_one (y ∘ snf.f), ← Matrix.nonsing_inv_mul Z hC, gen_relMap_mul,
          LinearMap.comp_apply, hz, map_zero]
      have hy : y = 0 := by
        funext k
        by_cases hk : k ∈ Set.range snf.f
        · obtain ⟨q, rfl⟩ := hk
          exact congrFun hyf q
        · exact hy0 k hk
      rw [hAY, gen_relMap_mul, LinearMap.comp_apply, ← hydef, hy, map_zero]
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [gen_relMap_mul, LinearMap.comp_apply, hv, map_zero]

end GenKey

lemma gen_bigMat_mul {R O : Type*} [Ring R] [CommRing O] [Algebra O R] {m g d : Type*}
    [Fintype m] [Fintype d] [DecidableEq d] (ρ : R →ₐ[O] Matrix d d O) (C : Matrix g m R) (P : Matrix m g R) :
    bigMat (⇑ρ) (C * P) = bigRect (⇑ρ) C * bigRect (⇑ρ) P := by
  ext p q
  simp only [bigMat, bigRect, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

theorem generic : StatGeneric := by
  intro R O _ _ _ _ _ _ m g s _ _ _ _ d _ _ ρ hρ P
  classical
  have hk := fun w => gen_key (O := O) (bigRect (ρ w) P)
  choose n U f e hC0 hgood using hk
  choose C0 hC0 using hC0
  let res := IsLocalRing.residue O
  let r : ∀ w, d w → d w → R := fun w a b => Function.surjInv (hρ w) (Matrix.single a b 1)
  let c : (Σ w : s, g × m × d w × d w) → Matrix g m R := fun j =>
    Matrix.single j.2.1 j.2.2.1 (r j.1 j.2.2.2.1 j.2.2.2.2)
  let L : ∀ w, Matrix (g × d w) (m × d w) (MvPolynomial (Σ w : s, g × m × d w × d w)
      (IsLocalRing.ResidueField O)) := fun w p q =>
    ∑ j, MvPolynomial.X j * MvPolynomial.C (res (ρ w (c j p.1 q.1) p.2 q.2))
  let Q : s → MvPolynomial (Σ w : s, g × m × d w × d w) (IsLocalRing.ResidueField O) := fun w =>
    (Matrix.of fun p q => ∑ l, L w (e w p) l * MvPolynomial.C (res (U w l (f w q)))).det
  have hevalQ : ∀ w (t : (Σ w : s, g × m × d w × d w) → O),
      MvPolynomial.eval (fun j => res (t j)) (Q w) =
        res (Matrix.of fun p q => (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    intro w t
    simp only [Q]
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q
    simp [L, Matrix.mul_apply, bigRect, Matrix.sum_apply, map_sum]

  have hsum : ∀ w (φ : g × m × d w × d w → O),
      bigRect (ρ w) (∑ j : (Σ w : s, g × m × d w × d w),
        (Pi.single (M := fun w => g × m × d w × d w → O) w φ j.1 j.2) • c j) =
        fun p q => φ (p.1, q.1, p.2, q.2) := by
    intro w φ
    funext p q
    simp only [bigRect, Matrix.sum_apply, Matrix.smul_apply, map_sum, map_smul]
    rw [Fintype.sum_sigma]
    rw [Fintype.sum_eq_single w (fun x hx => by simp [Pi.single_eq_of_ne hx])]
    simp only [Pi.single_eq_same]
    rw [Fintype.sum_eq_single (p.1, q.1, p.2, q.2)]
    · simp [c, r, Function.surjInv_eq (hρ w)]
    · rintro ⟨i', k', a', b'⟩ hy
      simp only [c, r, Matrix.single_apply]
      split_ifs with h1
      · obtain ⟨rfl, rfl⟩ := h1
        rw [Function.surjInv_eq (hρ w), Matrix.single_apply, if_neg, smul_zero]
        rintro ⟨rfl, rfl⟩
        exact hy rfl
      · simp
  have hQne : ∀ w, Q w ≠ 0 := by
    intro w hQ
    set t0 : (Σ w : s, g × m × d w × d w) → O := fun j =>
      Pi.single (M := fun w => g × m × d w × d w → O) w
        (fun x => C0 w (x.1, x.2.2.1) (x.2.1, x.2.2.2)) j.1 j.2 with ht0
    have h1 := hevalQ w t0
    rw [hQ, map_zero] at h1
    have h2 : bigRect (ρ w) (∑ j, t0 j • c j) = C0 w := by
      rw [ht0, hsum]
    rw [h2] at h1
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hC0 w) h1.symm
  have hprod : (∏ w, Q w) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun w _ => hQne w)
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x (∏ w, Q w) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hprod (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  rw [map_prod] at hx
  have hxw : ∀ w, MvPolynomial.eval x (Q w) ≠ 0 := fun w =>
    (Finset.prod_ne_zero_iff.1 hx) w (Finset.mem_univ w)
  let t : (Σ w : s, g × m × d w × d w) → O := fun j =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) (x j)
  have htx : (fun j => res (t j)) = x := funext fun j => Function.surjInv_eq _ _
  refine ⟨∑ j, t j • c j, fun w => ?_⟩
  have hu : IsUnit (Matrix.of fun p q =>
      (bigRect (ρ w) (∑ j, t j • c j) * U w) (e w p) (f w q)).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hevalQ w t, htx]
    exact hxw w
  show Module.length O (LinearMap.ker (relMap O (KO O) (bigMat (ρ w) (_ * P)))) = _
  rw [gen_bigMat_mul, hgood w _ hu]

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.LenCokerOfDetNeZero
section
open Finset Module IsDiscreteValuationRing Matrix

noncomputable section

namespace Formalism.NG

section HomQuotAux

variable {R O M NN : Type*} [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
  [SMulCommClass R O M] [AddCommGroup NN] [Module R NN] {g : Type} [Fintype g]

def evalGens (n : g → NN) : (NN →ₗ[R] M) →ₗ[O] (g → M) where
  toFun φ j := φ (n j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalGens_mem (Θ : Matrix g g R) (n : g → NN) (hrel : ∀ i, ∑ j, Θ i j • n j = 0)
    (φ : NN →ₗ[R] M) : (fun j => φ (n j)) ∈ LinearMap.ker (relMap O M Θ) := by
  classical
  rw [LinearMap.mem_ker]
  funext i
  rw [relMap_apply', Pi.zero_apply]
  simp_rw [← LinearMap.map_smul]
  rw [← map_sum, hrel i, map_zero]

theorem evalGens_inj (n : g → NN) (hspan : Submodule.span R (Set.range n) = ⊤) :
    Function.Injective (fun (φ : NN →ₗ[R] M) (j : g) => φ (n j)) := by
  intro φ ψ h
  exact LinearMap.ext_on_range hspan fun j => congrFun h j

end HomQuotAux

theorem homQuot : StatHomQuot := by
  intro R O M NN _ _ _ _ _ _ _ _ g _ _ Θ n hspan hrel
  refine ⟨evalGens_mem Θ n hrel, evalGens_inj n hspan, ?_⟩
  exact Module.length_le_of_injective
    (LinearMap.codRestrict (LinearMap.ker (relMap O M Θ)) (evalGens (O := O) (M := M) n)
      (evalGens_mem Θ n hrel))
    fun φ ψ h => evalGens_inj n hspan (congrArg Subtype.val h)

section KerHomAux

variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {g d : Type} [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O)

def uncurryEquiv : (g → LatQ O d ρ) ≃ₗ[O] (g × d → KO O) where
  toFun v p := v p.1 p.2
  invFun w j b := w (j, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [SMulCommClass R O (LatQ O d ρ)]

theorem uncurry_relMap (Θ : Matrix g g R) (v : g → LatQ O d ρ) :
    uncurryEquiv ρ (relMap O (LatQ O d ρ) Θ v) = matQ O (bigMat ρ Θ) (uncurryEquiv ρ v) := by
  funext p
  obtain ⟨i, a⟩ := p
  show (∑ j, Θ i j • v j : LatQ O d ρ) a = ∑ q : g × d, ρ (Θ i q.1) a q.2 • v q.1 q.2
  rw [Fintype.sum_prod_type]
  have hsum : (∑ j, Θ i j • v j : LatQ O d ρ) a = ∑ j, ((Θ i j • v j : LatQ O d ρ) : d → KO O) a :=
    Finset.sum_apply (M := fun _ : d => KO O) a univ (fun j => (Θ i j • v j : LatQ O d ρ))
  rw [hsum]
  rfl

theorem ker_map_uncurry (Θ : Matrix g g R) :
    (LinearMap.ker (relMap O (LatQ O d ρ) Θ)).map (uncurryEquiv (g := g) ρ).toLinearMap =
      LinearMap.ker (matQ O (bigMat ρ Θ)) := by
  ext w
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker,
    ← (uncurryEquiv (g := g) ρ).map_eq_zero_iff, uncurry_relMap, LinearEquiv.apply_symm_apply]

end KerHomAux

theorem kerHomBlock : StatKerHomBlock := by
  intro R O _ _ _ _ g d _ _ _ _ ρ _ Θ
  obtain ⟨e⟩ := homCoker R O (LatQ O d ρ) g g Θ
  rw [e.length_eq, ← ker_map_uncurry ρ Θ]
  exact (Submodule.equivMapOfInjective _ (uncurryEquiv (g := g) ρ).injective _).length_eq.symm

section LenCokerAux

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem lenCoker_of_det_ne_zero (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) = addVal O A.det := by
  have hinj : Function.Injective (Matrix.mulVecLin A) :=
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  let N := LinearMap.range (Matrix.mulVecLin A)
  let e : (ι → O) ≃ₗ[O] N := LinearEquiv.ofInjective _ hinj
  have h1 := IdempotentNormalFormsLenFacts.length_quot_eq_addVal_det N e
  have h2 : N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N) = Matrix.mulVecLin A := LinearMap.ext fun x => rfl
  have h3 : LinearMap.det (Matrix.mulVecLin A) = A.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  rw [h1, h2, h3]

def dotLin (u : ι → O) : (ι → O) →ₗ[O] O where
  toFun x := u ⬝ᵥ x
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

theorem lenCoker_of_det_eq_zero (A : Matrix ι ι O) (hd : A.det = 0) :
    Module.length O ((ι → O) ⧸ LinearMap.range (Matrix.mulVecLin A)) = ⊤ := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun i => addVal O (w i))
    ⟨j, Finset.mem_univ _⟩
  have hwi0 : w i0 ≠ 0 := by
    intro h
    have := hi0 j (Finset.mem_univ _)
    rw [h, addVal_zero, top_le_iff, addVal_eq_top_iff] at this
    exact hj this
  choose w' hw' using fun i => (addVal_le_iff_dvd (a := w i0) (b := w i)).mp
    (hi0 i (Finset.mem_univ _))
  have hw'i0 : w' i0 = 1 := by
    have := hw' i0
    exact (mul_left_cancel₀ hwi0 (this.symm.trans (mul_one _).symm))
  have hw'A : w' ᵥ* A = 0 := by
    have : w = w i0 • w' := funext fun i => by simp [hw' i]
    rw [this, Matrix.smul_vecMul] at hw
    exact (smul_eq_zero.mp hw).resolve_left hwi0
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  rw [ENat.eq_top_iff_forall_ge]
  intro k
  let I : Ideal O := Ideal.span ({ϖ ^ k} : Set O)
  let f : (ι → O) →ₗ[O] (O ⧸ I) := I.mkQ ∘ₗ dotLin w'
  have hle : LinearMap.range (Matrix.mulVecLin A) ≤ LinearMap.ker f := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    show I.mkQ (w' ⬝ᵥ (A *ᵥ z)) = 0
    rw [Matrix.dotProduct_mulVec, hw'A, zero_dotProduct, map_zero]
  let F := (LinearMap.range (Matrix.mulVecLin A)).liftQ f hle
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨c, rfl⟩ := I.mkQ_surjective y
    refine ⟨Submodule.Quotient.mk (Pi.single i0 c), ?_⟩
    show I.mkQ (w' ⬝ᵥ Pi.single i0 c) = I.mkQ c
    rw [dotProduct_single, hw'i0, one_mul]
  have h := Module.length_le_of_surjective F hF
  rw [IdempotentNormalFormsLenFacts.length_quot_span, hϖ.addVal_pow] at h
  simpa using h

end LenCokerAux

theorem lenCoker : StatLenCoker := by
  intro O _ _ _ ι _ _ A
  by_cases hd : A.det = 0
  · rw [lenCoker_of_det_eq_zero A hd, hd, addVal_zero]
  · exact lenCoker_of_det_ne_zero A hd

end Formalism.NG
end
end

