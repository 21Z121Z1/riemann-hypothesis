import Formalism.SubspaceCounting.Bundle0002
import Formalism.SubspaceCounting.SubspaceCountingProofs.LengthLayers
import Formalism.SubspaceCounting.SubspaceCountingProofs.Bundle0001

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.AllButLESmith
section
noncomputable section

open scoped BigOperators
open Module

namespace Formalism.G0

namespace AllButLESmithP

variable {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup M] [Module O M] [Fintype ι]

theorem pow_succ_dvd_of_not_dvd {π : O} (hπ : Irreducible π) {a : O} {E : ℕ}
    (h : ¬ a ∣ π ^ E) : π ^ (E + 1) ∣ a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  by_contra hc
  apply h
  have hk : k ≤ E := by
    by_contra hk
    apply hc
    rw [hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow π (not_le.mp hk)) _
  rw [hu]
  exact (Units.mul_left_dvd).mpr (pow_dvd_pow π hk)

variable {P : Submodule O M} {n : ℕ}

theorem down (snf : Basis.SmithNormalForm P ι n) (π : O) (g E : ℕ) (S : Finset ι)
    (hS : ∀ j, j ∉ S → ∃ i, snf.f i = j ∧ snf.a i ∣ π ^ E) (hcard : S.card ≤ g) :
    AllButLE π ⊤ P g E := by
  classical
  refine ⟨S.image snf.bM, by simp, Finset.card_image_le.trans hcard, ?_⟩
  intro x _
  rw [← snf.bM.sum_repr x, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : j ∈ S
  · apply Submodule.mem_sup_right
    rw [smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hj)))
  · obtain ⟨i, rfl, t, ht⟩ := hS j hj
    apply Submodule.mem_sup_left
    have : π ^ E • (snf.bM.repr x (snf.f i) • snf.bM (snf.f i)) =
        (snf.bM.repr x (snf.f i) * t) • (snf.bN i : M) := by
      rw [snf.snf i, smul_smul, smul_smul, ht]
      congr 1
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (snf.bN i).2

theorem up (snf : Basis.SmithNormalForm P ι n) (π : O) (hπ : Irreducible π) (g E : ℕ)
    (S : Finset ι) (hS : ∀ i, snf.f i ∈ S → ¬ snf.a i ∣ π ^ E)
    (h : AllButLE π ⊤ P g E) : S.card ≤ g := by
  classical
  obtain ⟨C, -, hCg, hC⟩ := h
  let K : Ideal O := Ideal.span {π ^ (E + 1)}
  let φ : M →ₗ[O] (↥S → O ⧸ K) :=
    LinearMap.pi (fun j : ↥S => K.mkQ ∘ₗ snf.bM.coord (j : ι))
  have hφb : ∀ i, φ (snf.bN i : M) = 0 := by
    intro i
    funext j
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Basis.coord_apply, snf.snf i,
      map_smul, Basis.repr_self, Pi.zero_apply]
    rw [Finsupp.single_apply]
    split_ifs with hij
    · rw [← map_smul, smul_eq_mul, mul_one, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Ideal.mem_span_singleton]
      have hmem : snf.f i ∈ S := by rw [hij]; exact j.2
      exact pow_succ_dvd_of_not_dvd hπ (hS i hmem)
    · simp
  have hφP : ∀ p ∈ P, φ p = 0 := by
    intro p hp
    have hsum := snf.bN.sum_repr ⟨p, hp⟩
    have hp' : p = ∑ i, snf.bN.repr ⟨p, hp⟩ i • (snf.bN i : M) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hp', map_sum]
    simp only [map_smul, hφb, smul_zero, Finset.sum_const_zero]
  have hsurj : Function.Surjective φ := by
    intro t
    choose r hr using fun j => K.mkQ_surjective (t j)
    refine ⟨snf.bM.equivFun.symm (fun k => if hk : k ∈ S then r ⟨k, hk⟩ else 0), ?_⟩
    funext j
    have hrep : snf.bM.repr (snf.bM.equivFun.symm
        (fun k => if hk : k ∈ S then r ⟨k, hk⟩ else 0)) (j : ι) = r j := by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      simp
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Basis.coord_apply, hrep, hr]
  have hmemC : ∀ x : M, π ^ E • φ x ∈ Submodule.span O ((C.image φ : Finset _) : Set _) := by
    intro x
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp (hC x Submodule.mem_top)
    rw [← map_smul, ← hpw, map_add, hφP p hp, zero_add, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hw
  have hkill : ∀ w : ↥S → O ⧸ K, π ^ (E + 1) • w = 0 := by
    intro w
    funext j
    obtain ⟨r, hr⟩ := K.mkQ_surjective (w j)
    rw [Pi.smul_apply, Pi.zero_apply, ← hr, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _

  have hker : Ideal.span {π} ≤ LinearMap.ker ((π ^ E) • K.mkQ) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show (π ^ E) • K.mkQ π = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      ← pow_succ]
    exact Ideal.mem_span_singleton_self _
  let g0 : (O ⧸ Ideal.span {π}) →ₗ[O] (O ⧸ K) := (Ideal.span {π}).liftQ ((π ^ E) • K.mkQ) hker
  have hg0 : Function.Injective g0 := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.ker_liftQ_eq_bot
    intro r hr
    rw [LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mem_span_singleton, pow_succ] at hr
    rw [Ideal.mem_span_singleton]
    exact (mul_dvd_mul_iff_left (pow_ne_zero E hπ.ne_zero)).mp hr
  let ι' : (↥S → O ⧸ Ideal.span {π}) →ₗ[O] (↥S → O ⧸ K) :=
    LinearMap.pi (fun j : ↥S => g0 ∘ₗ LinearMap.proj j)
  have hinj : Function.Injective ι' := by
    intro u v huv
    funext j
    exact hg0 (congrFun huv j)
  have hV : LinearMap.range ι' ≤ Submodule.span O ((C.image φ : Finset _) : Set _) := by
    rintro _ ⟨u, rfl⟩
    choose r hr using fun j => (Ideal.span {π} : Submodule O O).mkQ_surjective (u j)
    obtain ⟨x, hx⟩ := hsurj (fun j => K.mkQ (r j))
    have : ι' u = π ^ E • φ x := by
      funext j
      rw [hx]
      simp only [ι', LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← hr,
        Pi.smul_apply, g0]
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply]
    rw [this]
    exact hmemC x
  have hs : ∀ v ∈ LinearMap.range ι', π ^ 1 • v ∈ (⊥ : Submodule O (↥S → O ⧸ K)) := by
    rintro _ ⟨u, rfl⟩
    rw [Submodule.mem_bot]
    obtain ⟨r, hr⟩ : ∃ w, ι' u = π ^ E • w := by
      choose r hr using fun j => (Ideal.span {π} : Submodule O O).mkQ_surjective (u j)
      refine ⟨fun j => K.mkQ (r j), ?_⟩
      funext j
      simp only [ι', LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← hr,
        Pi.smul_apply, g0]
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply]
    rw [hr, smul_smul, ← pow_add, add_comm]
    exact hkill r
  have hlay := LengthLayersP.layer π hπ (⊥ : Submodule O (↥S → O ⧸ K)) (LinearMap.range ι')
    bot_le (C.image φ) g 1 (Finset.card_image_le.trans hCg) hV hs
  rw [Module.length_bot, zero_add, ← (LinearEquiv.ofInjective ι' hinj).length_eq,
    Module.length_pi_of_fintype] at hlay
  simp only [LengthLayersP.length_residue π hπ, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one] at hlay
  exact_mod_cast hlay

theorem key (snf : Basis.SmithNormalForm P ι n) (π : O) (hπ : Irreducible π) (g E : ℕ)
    (B : Finset (Fin n)) (hB : ∀ i, i ∈ B ↔ ¬ snf.a i ∣ π ^ E) :
    AllButLE π ⊤ P g E ↔ B.card + (Fintype.card ι - n) ≤ g := by
  classical
  let S : Finset ι := B.map snf.f ∪ (Finset.univ.map snf.f)ᶜ
  have hcard : S.card = B.card + (Fintype.card ι - n) := by
    rw [Finset.card_union_of_disjoint, Finset.card_map, Finset.card_compl, Finset.card_map,
      Finset.card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_compl] at hj'
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hj
    exact hj' (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  have hin : ∀ i, snf.f i ∈ S → ¬ snf.a i ∣ π ^ E := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨i', hi', he⟩ := Finset.mem_map.mp h
      rw [snf.f.injective he] at hi'
      exact (hB i).mp hi'
    · exact absurd (Finset.mem_map_of_mem _ (Finset.mem_univ i)) (Finset.mem_compl.mp h)
  have hout : ∀ j, j ∉ S → ∃ i, snf.f i = j ∧ snf.a i ∣ π ^ E := by
    intro j hj
    have h1 : j ∈ Finset.univ.map snf.f := by
      by_contra h
      exact hj (Finset.mem_union_right _ (Finset.mem_compl.mpr h))
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp h1
    refine ⟨i, rfl, ?_⟩
    by_contra h
    exact hj (Finset.mem_union_left _ (Finset.mem_map_of_mem _ ((hB i).mpr h)))
  rw [← hcard]
  exact ⟨up snf π hπ g E S hin, down snf π g E S hout⟩

end AllButLESmithP

theorem all_but_le_smith : AllButLESmith := by
  unfold AllButLESmith
  intro O M ι _ _ _ _ _ _ π hπ P n snf g E
  exact AllButLESmithP.key snf π hπ g E _ (fun i => by simp)

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.ChoiceOfTops
section
noncomputable section

namespace Formalism.G0

namespace ChoiceOfTopsP

lemma not_good {n : ℕ} {T : Finset ℕ} {L₂ K r N₁ G : ℕ} (h : ¬ GoodOrbit n T L₂ K r N₁ G) :
    ¬ CondA n T L₂ K ∨ (¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ∨ ¬ CondC n T G ∨ T.card < N₁ := by
  unfold GoodOrbit at h
  by_cases hN : N₁ ≤ T.card
  · tauto
  · right; right; right; omega

lemma term_le (p a b c d : Prop) {_ : Decidable p} {_ : Decidable a} {_ : Decidable b}
    {_ : Decidable c} {_ : Decidable d} (w : ℝ) (hw : 0 ≤ w) (h : p → a ∨ b ∨ c ∨ d) :
    (if p then w else 0) ≤
      (if a then w else 0) + (if b then w else 0) + (if c then w else 0) + (if d then w else 0) := by
  by_cases hp : p
  · rcases h hp with h' | h' | h' | h' <;>
      split_ifs <;> linarith
  · split_ifs <;> linarith

lemma probNotGood_le (n : ℕ) (δ : ℝ) (L₂ K r N₁ G : ℕ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    probNotGood n δ L₂ K r N₁ G ≤
      condProb n δ (fun T => ¬ CondA n T L₂ K) +
      condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) +
      condProb n δ (fun T => ¬ CondC n T G) +
      condProb n δ (fun T => T.card < N₁) := by
  classical
  unfold probNotGood condProb
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T _
  have hw : 0 ≤ δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) :=
    mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)
  refine term_le _ _ _ _ _ _ hw ?_
  rintro ⟨h0T, hg⟩
  rcases not_good hg with h | h | h | h
  · exact Or.inl ⟨h0T, h⟩
  · exact Or.inr (Or.inl ⟨h0T, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h0T, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h0T, h⟩))

end ChoiceOfTopsP

theorem choiceOfTops_of (ha : TopsChoicePartA) (hb : TopsChoiceSecondBound) (hc : TopsChoiceThirdBound) (hn : SmallCardCondProbBound) : ChoiceOfTops := by
  intro n δ L₂ K r N₁ G hn2 hev hδ hL hLδ hr hN
  have hL' : (1 : ℝ) ≤ L₂ := by exact_mod_cast hL
  have hδ1 : δ ≤ 1 := by nlinarith
  have h := ChoiceOfTopsP.probNotGood_le n δ L₂ K r N₁ G hδ hδ1
  have h1 := ha n δ L₂ K hn2 hδ hL hLδ
  have h2 := hb n δ L₂ r N₁ hn2 hev hδ hL hLδ hr hN
  have h3 := hc n δ G hn2 hδ hδ1
  have h4 := hn n δ N₁ hn2 hδ hδ1
  linarith

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.DetQuotVal
section
noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP

variable {K ι : Type} [Field K] [DecidableEq ι]

lemma det_msMat {L : Type} [Field L] {r : ℕ} (hr : 1 ≤ r) (g : GL (Fin r) L) :
    (msMat g).det = Polynomial.X := by
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_last hr]
  have h1 : (g.1.map Polynomial.C).det * ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, Units.mul_inv]
    simp
  calc (g.1.map Polynomial.C).det * Polynomial.X * ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det
      = Polynomial.X * ((g.1.map Polynomial.C).det *
          ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det) := by ring
    _ = Polynomial.X := by rw [h1, mul_one]

lemma substS_det_all {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hv : ∀ l, vec (A l) = true) (hS : ∀ l, A l ∈ S)
    (g : GL (Fin r) L) :
    substS (K := K) vec S g (detLetters A) =
      MvPolynomial.C Polynomial.X * Matrix.det (Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) := by
  have h1 : substS (K := K) vec S g (detLetters A) =
      Matrix.det ((Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) *
        ((msMat g).map MvPolynomial.C).transpose) := by
    have := substS_det (K := K) vec S g A (RingHom.id _)
    simp only [RingHom.id_apply] at this
    rw [this]
    congr 1
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, substS_X]
    simp only [hS l, hv l, if_true, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hC := RingHom.map_det (MvPolynomial.C : Polynomial L →+* MvPolynomial (ι × Fin r) (Polynomial L)) (msMat g)
  rw [RingHom.mapMatrix_apply] at hC
  rw [h1, Matrix.det_mul, Matrix.det_transpose, ← hC, det_msMat hr, mul_comm]

lemma not_dvd_detX {L : Type} [Field L] {r : ℕ} (A : Fin r → ι) (hA : Function.Injective A) :
    ¬ (MvPolynomial.C Polynomial.X : MvPolynomial (ι × Fin r) (Polynomial L)) ∣
      Matrix.det (Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) := by
  intro h
  let v : ι × Fin r → L := fun p => ∑ l, if p.1 = A l ∧ p.2 = l then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v) h
  rw [MvPolynomial.eval₂Hom_C, RingHom.map_det, RingHom.mapMatrix_apply] at h2
  have hM : (Matrix.of fun (l b : Fin r) =>
      (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))).map
        (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v) = 1 := by
    refine Matrix.ext fun l b => ?_
    simp only [Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval₂Hom_X', Matrix.one_apply, v]
    rw [Finset.sum_eq_single l]
    · by_cases e : b = l
      · subst e; simp
      · simp [e, Ne.symm e]
    · intro k _ hk
      have : A l ≠ A k := fun x => hk (hA x).symm
      simp [this]
    · simp
  rw [hM, Matrix.det_one] at h2
  simp at h2

lemma msMat_eval_zero_mul_eq_mul_diagonal {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) :
    (msMat g).map (Polynomial.evalRingHom (0 : L)) * g.1 =
      g.1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) := by
  unfold msMat
  rw [Matrix.map_mul, Matrix.map_mul]
  have e1 : (g.1.map Polynomial.C).map (Polynomial.evalRingHom (0 : L)) = g.1 := by
    ext i j; simp
  have e2 : ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).map (Polynomial.evalRingHom (0 : L)) =
      (g⁻¹ : GL (Fin r) L).1 := by
    ext i j; simp
  have e3 : (Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1)).map
      (Polynomial.evalRingHom (0 : L)) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) := by
    ext i j
    by_cases h : i = j
    · subst h; by_cases h' : i.val + 1 = r <;> simp [h']
    · simp [h]
  rw [e1, e2, e3, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

lemma not_dvd_substS_det {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r)
    (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A)
    (hv : ∀ l, vec (A l) = true) (hS : ¬ ∀ l, A l ∈ S) (g : GL (Fin r) L) :
    ¬ MvPolynomial.C Polynomial.X ∣ substS (K := K) vec S g (detLetters A) := by
  intro h
  obtain ⟨l₀, hl₀⟩ := not_forall.mp hS
  let last : Fin r := ⟨r - 1, by omega⟩
  let τ : Equiv.Perm (Fin r) := Equiv.swap l₀ last
  let v : ι × Fin r → L := fun p => ∑ l, if p.1 = A l then g.1 p.2 (τ l) else 0
  have hvA : ∀ l b, v (A l, b) = g.1 b (τ l) := by
    intro l b
    simp only [v]
    rw [Finset.sum_eq_single l]
    · simp
    · intro k _ hk
      have : A l ≠ A k := fun x => hk (hA x).symm
      simp [this]
    · simp
  let φ := MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v
  have h2 := map_dvd φ h
  rw [show φ (MvPolynomial.C Polynomial.X) = 0 by simp [φ], substS_det, zero_dvd_iff] at h2
  have hM : (Matrix.of fun l a => φ (substS (K := K) vec S g (MvPolynomial.X (A l, a)))) =
      (g.1.transpose).submatrix τ id := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.transpose_apply, substS_X]
    by_cases hl : A l ∈ S
    · simp only [hl, hv l, if_true, map_sum, map_mul, φ, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', hvA]
      have := congrFun (congrFun (msMat_eval_zero_mul_eq_mul_diagonal g) a) (τ l)
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
      simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at this
      simp only [Polynomial.coe_evalRingHom]
      rw [this]
      have hne : (τ l).val + 1 ≠ r := by
        intro e
        have h' : τ l = last := by ext; simp [last]; omega
        have hll : l = l₀ := by
          have := congrArg τ h'
          rw [Equiv.swap_apply_self] at this
          simpa [τ] using this
        exact hl₀ (hll ▸ hl)
      simp [hne]
    · simp only [hl, if_false, φ, MvPolynomial.eval₂Hom_X', hvA]
  rw [hM, Matrix.det_permute, Matrix.det_transpose] at h2
  have hu := Matrix.isUnits_det_units g
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with e | e <;> simp [e, hu.ne_zero] at h2

lemma sum_cov {r : ℕ} (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι)
    (hv : ∀ l, vec (A l) = true) (d : ι → ℕ) (m' : ℕ) :
    ∑ i ∈ S.filter (fun i => vec i = false), (d i + m' * (if i ∈ Set.range A then 1 else 0)) =
      ∑ i ∈ S.filter (fun i => vec i = false), d i := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cov_zero vec S A hv, mul_zero, add_zero]

end Formalism.G0.DetQuotValP

open Formalism.G0.DetQuotValP in
theorem Formalism.G0.det_quotient_valuation : Formalism.G0.DetQuotVal := by
  intro K ι _ _ _ r vec S' A d H m' th hA hv _ hle hval L _ _ g
  have h := hval L g
  rw [sum_cov vec S' A hv d m'] at h
  set c := ∑ i ∈ S'.filter (fun i => vec i = false), d i
  simp only [map_mul, map_pow] at h ⊢
  set p : MvPolynomial (ι × Fin r) (Polynomial L) := MvPolynomial.C Polynomial.X with hpdef
  have hp : Prime p := (MvPolynomial.prime_C_iff _).mpr Polynomial.prime_X
  have hnd : ∀ (U : MvPolynomial (ι × Fin r) (Polynomial L)), ¬ p ∣ U → ∀ n, p ^ n ∣ U ^ m' *
      substS (K := K) vec S' g H → p ^ n ∣ substS (K := K) vec S' g H := by
    intro U hU n hn
    exact hp.pow_dvd_of_dvd_mul_left n (fun e => hU (hp.dvd_of_dvd_pow e)) hn
  by_cases hall : 1 ≤ r ∧ ∀ l, A l ∈ S'
  · rw [substS_det_all hall.1 vec S' A hv hall.2 g, mul_pow, mul_assoc] at h
    rw [show th + c = m' + (th - m' + c) by omega, pow_add] at h
    have h' := (mul_dvd_mul_iff_left (pow_ne_zero m' hp.ne_zero)).mp h
    exact hnd _ (not_dvd_detX A hA) _ h'
  · have hnot : ¬ p ∣ substS (K := K) vec S' g (detLetters A) := by
      by_cases hr : 1 ≤ r
      · exact not_dvd_substS_det hr vec S' A hA hv (fun x => hall ⟨hr, x⟩) g
      · have hr0 : r = 0 := by omega
        subst hr0
        have : detLetters (K := K) A = 1 := Matrix.det_fin_zero
        rw [this, map_one]
        exact hp.not_dvd_one
    exact (pow_dvd_pow p (by omega)).trans (hnd _ hnot _ h)
end
end

