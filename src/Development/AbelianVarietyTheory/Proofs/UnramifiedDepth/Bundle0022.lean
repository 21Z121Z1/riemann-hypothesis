import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.DualLattices.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coords : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (ι : Type) [Fintype ι] (e : ι → I → C) (z : I → ι → C) (al : I → ℕ → I → C), (∀ j x, e j x = ∑ b, z b j * S.tan b x) → (∀ c b, al c 0 b = if c = b then 1 else 0) → (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) → (∀ c, MvPowerSeries.constantCoeff (linPull e (t c)) = 0) ∧ (∀ (b : I) (μ : ι →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) = MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b j) * (MvPowerSeries.X j : MvPowerSeries ι C))) ∧ ∀ (κ : J) (μ : ι →₀ ℕ), MvPowerSeries.coeff μ (linPull e (S.ze t κ)) = -∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.be c s κ * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) := by
  intro C _ V d I J _ _ G S t ht ι _ e z al he hal0 hal
  obtain ⟨f, hf⟩ : ∃ f : I → MvPowerSeries ι C,
      f = fun x => ∑ j, e j x • (MvPowerSeries.X j : MvPowerSeries ι C) := ⟨_, rfl⟩
  have hlp : ∀ F : MvPowerSeries I C, linPull e F = MvPowerSeries.subst f F := by
    intro F; subst hf; rfl
  have hf0 : ∀ x, MvPowerSeries.constantCoeff (f x) = 0 := by
    intro x
    simp [hf, map_sum, MvPowerSeries.smul_eq_C_mul]
  have hsub : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero hf0
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hal' : ∀ c s x, S.al c s x = ∑ b', al c s b' * S.tan b' x := by
    intro c s x
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [hal0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact S.cur_zero_inl c x
    · rw [hal c s x hs]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [show S.al b' 0 x = S.tan b' x from S.cur_zero_inl b' x]
  simp only [hlp]
  refine ⟨fun c => MvPowerSeries.constantCoeff_subst_eq_zero hsub hf0 (ht.1 c), fun b μ => ?_,
    fun κ μ => ?_⟩
  · set P : I → ℕ → C := fun c s =>
      MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) with hP
    set Y : I → C := fun b' => ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s with hY
    set Zf : I → C := fun b' =>
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b' j) *
        (MvPowerSeries.X j : MvPowerSeries ι C)) with hZ
    have hx : ∀ x, ∑ b', (Y b' - Zf b') * S.tan b' x = 0 := by
      intro x
      have h := GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries C I ι I V.l hl (fun c s => S.al c s x) t (MvPowerSeries.X x) f hf0 ht.1
        (fun μ' => by rw [MvPowerSeries.coeff_X, ht.2 x μ']) μ
      rw [MvPowerSeries.subst_X hsub] at h
      have eL : MvPowerSeries.coeff μ (f x) = ∑ b', Zf b' * S.tan b' x := by
        simp only [hf, hZ, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_C_mul, he,
          Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have eR : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.al c s x *
          MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) =
          ∑ b', Y b' * S.tan b' x := by
        calc _ = ∑ s ∈ Finset.range (μ.degree + 1), ∑ b', ∑ c,
              al c s b' * P c s * S.tan b' x := by
              refine Finset.sum_congr rfl fun s _ => ?_
              simp only [hP, hal', Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
              ring
          _ = ∑ b', ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s * S.tan b' x :=
              Finset.sum_comm
          _ = _ := by simp only [hY, Finset.sum_mul]
      rw [eL, eR] at h
      simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
    have hv : Matrix.vecMul (fun b' => Y b' - Zf b') (Matrix.of S.tan) = 0 := by
      funext x
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact hx x
    have h0 := congrFun (Matrix.eq_zero_of_vecMul_eq_zero S.U_det_ne hv) b
    exact sub_eq_zero.mp h0
  · have hF : ∀ μ' : I →₀ ℕ, MvPowerSeries.coeff μ' (S.ze t κ) =
        ∑ s ∈ Finset.range (μ'.degree + 1), ∑ c, (-S.be c s κ) *
          MvPowerSeries.coeff μ' (t c ^ V.l ^ s) := by
      intro μ'
      show -(∑ s ∈ Finset.Icc 1 μ'.degree, ∑ c : I,
        S.be c s κ * MvPowerSeries.coeff μ' (t c ^ V.l ^ s)) = _
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_subset
      · intro s hs
        simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢
        omega
      · intro s hs hns
        have hs0 : s = 0 := by
          simp only [Finset.mem_Icc, Finset.mem_range] at hs hns
          omega
        subst hs0
        simp [show ∀ c, S.be c 0 κ = 0 from fun c => S.be_zero c κ]
    rw [GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries C I ι I V.l hl (fun c s => -S.be c s κ) t (S.ze t κ) f hf0 ht.1 hF μ]
    simp only [neg_mul, Finset.sum_neg_distrib]

end GlobalTheory.MainTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GroupLawPowerSeries
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChLaw

private lemma nil_of_mem_span {S : Type} [CommRing S] {s : Set S} (hs : ∀ a ∈ s, IsNilpotent a)
    {c : S} (hc : c ∈ Ideal.span s) : IsNilpotent c := by
  have h : Ideal.span s ≤ nilradical S := Ideal.span_le.2 fun a ha => mem_nilradical.2 (hs a ha)
  exact mem_nilradical.1 (h hc)

theorem groupLaw_powerSeries :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∃ F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
      (∀ k, fAdd F a b k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ x S a * x S b = x S (fAdd F a b)) := by
  classical
  intro _ h2 R₀ _ G _ _ g x ⟨h0, hnat, hinj, hsur⟩
  have hex : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∃ c : Fin g → S,
        (∀ k, c k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ (∀ k, IsNilpotent (c k)) ∧
        x S a * x S b = x S c := by
    intro S _ _ a b ha hb
    set I : Ideal S := Ideal.span (Set.range a ∪ Set.range b) with hI
    have hnil : ∀ c ∈ I, IsNilpotent c := fun c hc =>
      nil_of_mem_span (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [ha i, hb i]) hc
    have hker : ∀ c, c ∈ RingHom.ker (Ideal.Quotient.mkₐ R₀ I) ↔ c ∈ I := fun c => by
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    have hz : spMap (Ideal.Quotient.mkₐ R₀ I) ≫ (x S a * x S b) = 1 := by
      have ea : (fun i => Ideal.Quotient.mkₐ R₀ I (a i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
      have eb : (fun i => Ideal.Quotient.mkₐ R₀ I (b i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
      rw [MonObj.comp_mul, hnat _ _ _ a ha, hnat _ _ _ b hb, ea, eb, h0, _root_.mul_one]
    obtain ⟨c, hc, hzc⟩ := hsur S (S ⧸ I) (Ideal.Quotient.mkₐ R₀ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I) (fun c hc => hnil c ((hker c).1 hc)) _ hz
    exact ⟨c, fun k => (hker _).1 (hc k), fun k => hnil _ ((hker _).1 (hc k)), hzc⟩
  choose cc hc1 hc2 hc3 using hex
  have hF : ∀ k : Fin g, ∃ f : MvPowerSeries (Fin g ⊕ Fin g) R₀,
      ∀ (S : Type) [CommRing S] [Algebra R₀ S] (u : Fin g ⊕ Fin g → S)
        (hu : ∀ i, IsNilpotent (u i)),
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k =
          nEval f u := by
    intro k
    obtain ⟨f, hf⟩ := h2 (R₀ := R₀) (κ := Fin g ⊕ Fin g)
      (fun S _ _ u => if hu : ∀ i, IsNilpotent (u i) then
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k
        else 0) (by
        intro S _ _ S' _ _ φ u hu
        have hu' : ∀ i, IsNilpotent (φ (u i)) := fun i => (hu i).map φ
        simp only [dif_pos hu, dif_pos hu']
        have := hinj S'
          (fun j => φ (cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i))
            (fun _ => hu _) (fun _ => hu _) j))
          (cc S' (fun i => φ (u (Sum.inl i))) (fun i => φ (u (Sum.inr i)))
            (fun _ => hu' _) (fun _ => hu' _))
          (fun j => (hc2 _ _ _ _ _ j).map φ) (hc2 _ _ _ _ _) (by
            rw [← hnat _ _ φ _ (hc2 _ _ _ _ _), ← hc3, ← hc3, MonObj.comp_mul,
              hnat _ _ φ _ (fun _ => hu _), hnat _ _ φ _ (fun _ => hu _)])
        exact congrFun this k)
    refine ⟨f, fun S _ _ u hu => ?_⟩
    have := hf S u hu
    simpa only [dif_pos hu] using this
  choose F hF using hF
  refine ⟨F, fun S _ _ a b ha hb => ?_⟩
  have e : fAdd F a b = cc S a b ha hb := by
    funext k
    have hu : ∀ i, IsNilpotent (Sum.elim a b i) := by
      rintro (i | i); exacts [ha i, hb i]
    exact (hF k S (Sum.elim a b) hu).symm
  rw [e]
  exact ⟨hc1 S a b ha hb, hc3 S a b ha hb⟩

end GlobalTheory.ChLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilCoord

section Alg

variable {R : Type} [CommRing R] {n : ℕ} {B : Type} [CommRing B] [Algebra R B]

theorem ext_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (φ₁ φ₂ : B →ₐ[R] A)
    (h : ∀ b, IsNilpotent (φ₁ b - φ₂ b))
    (hs : ∀ j : Fin n, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := φ₁.comp π
  have hρ2 : φ₂.comp π = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  obtain ⟨s, hsg⟩ := (inferInstance : Algebra.FiniteType (MvPolynomial (Fin n) R) B).out
  let J : Ideal A := Ideal.span ((fun b => φ₁ b - φ₂ b) '' (s : Set B))
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (s.finite_toSet.image _)), Ideal.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact h b
  have : ψ₁ = ψ₂ := by
    apply Algebra.FormallyUnramified.lift_unique J hJ
    apply AlgHom.ext_of_adjoin_eq_top hsg
    intro b hb
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨b, hb, rfl⟩
  ext x
  exact AlgHom.congr_fun this x

theorem exists_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (e : B →ₐ[R] A) (a : Fin n → A)
    (ha : ∀ j, IsNilpotent (a j)) :
    ∃ φ : B →ₐ[R] A, (∀ b, IsNilpotent (φ b - e b)) ∧
      ∀ j, φ (π (MvPolynomial.X j)) = e (π (MvPolynomial.X j)) + a j := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A :=
    MvPolynomial.aeval (fun j => e (π (MvPolynomial.X j)) + a j)
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (Set.finite_range _)), Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact ha b
  let mk : A →ₐ[MvPolynomial (Fin n) R] A ⧸ J := Ideal.Quotient.mkₐ _ J
  have hf₀ : ((Ideal.Quotient.mkₐ R J).comp e).comp π = (Ideal.Quotient.mkₐ R J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin n) R] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ R J).comp e).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (mk : A →+* A ⧸ J)) := by
    have : RingHom.ker (mk : A →+* A ⧸ J) = J := Ideal.mk_ker
    rw [this]
    exact hJ
  let φ' := Algebra.FormallySmooth.liftOfSurjective f₀ mk hmk hker
  have hφ' : mk.comp φ' = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective f₀ mk hmk hker
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  refine ⟨{ φ'.toRingHom with commutes' := fun r => ?_ }, fun b => ?_, fun j => ?_⟩
  · show φ' (algebraMap R B r) = _
    rw [← π.commutes, hc, ρ.commutes]
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (e b) := AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    obtain ⟨N, hN⟩ := hJ
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow e1 N
    rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  · show φ' (π _) = _
    rw [hc]
    exact MvPolynomial.aeval_X _ j

end Alg

theorem exists_etale_chart {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    [IsLocalRing R₀] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (C : Chart G) (π : MvPolynomial (Fin g) R₀ →ₐ[R₀] Γ(G.left, C.U)), π.toRingHom.Etale := by
  let e0 : Spec (CommRingCat.of R₀) ⟶ G.left := (η[G]).left
  obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (e0 (IsLocalRing.closedPoint R₀))
  have hsp : ∀ p : PrimeSpectrum R₀, p ⤳ IsLocalRing.closedPoint R₀ := fun p =>
    (PrimeSpectrum.le_iff_specializes _ _).mp
      (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum R₀).isPrime.ne_top)
  have hw : e0 ≫ G.hom = 𝟙 _ := Over.w (η[G])
  have hU' : U = ⊤ := by
    rw [eq_top_iff]
    intro p _
    refine (hsp p).mem_open U.isOpen ?_
    have h1 : (e0 ≫ G.hom) (IsLocalRing.closedPoint R₀) ∈ U := by
      exact (Scheme.Hom.comp_apply e0 G.hom (IsLocalRing.closedPoint R₀)).symm ▸ e hx
    rw [hw] at h1
    exact h1
  subst hU'
  let C : Chart G := ⟨V, hV, fun p _ => (hsp p).mem_open (e0 ⁻¹ᵁ V).isOpen hx⟩
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g (alg0 C) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv h
  obtain ⟨π, hπ1, hπ2⟩ := h2.exists_etale_mvPolynomial
  clear_value C
  exact ⟨C, { π with commutes' := fun r => RingHom.congr_fun hπ1 r }, hπ2⟩

theorem nilpotent_coordinates :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G),
      (∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) := by
  intro R₀ _ G _ _ _ g hG
  classical
  obtain ⟨C, π, hπ⟩ := exists_etale_chart G g hG
  have key : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      ∃ φ : Γ(G.left, C.U) →ₐ[R₀] S, (∀ i, IsNilpotent (a i)) →
        (∀ b, IsNilpotent (φ b - algebraMap R₀ S (eps C b))) ∧
        ∀ j, φ (π (MvPolynomial.X j)) = algebraMap R₀ S (eps C (π (MvPolynomial.X j))) + a j := by
    intro S _ _ a
    by_cases ha : ∀ i, IsNilpotent (a i)
    · obtain ⟨φ, h⟩ := exists_of_nil π hπ ((Algebra.ofId R₀ S).comp (eps C)) a ha
      exact ⟨φ, fun _ => h⟩
    · exact ⟨(Algebra.ofId R₀ S).comp (eps C), fun h => absurd h ha⟩
  choose F hF using key
  have uniq : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S) (φ : Γ(G.left, C.U) →ₐ[R₀] S),
      (∀ i, IsNilpotent (a i)) → (∀ b, IsNilpotent (φ b - algebraMap R₀ S (eps C b))) →
      (∀ j, φ (π (MvPolynomial.X j)) = algebraMap R₀ S (eps C (π (MvPolynomial.X j))) + a j) →
      φ = F S a := by
    intro S _ _ a φ ha h1 h2
    refine ext_of_nil π hπ _ _ (fun b => ?_) (fun j => ?_)
    · have := (Commute.all _ _).isNilpotent_sub (h1 b) ((hF S a ha).1 b)
      rwa [sub_sub_sub_cancel_right] at this
    · rw [h2, (hF S a ha).2]
  refine ⟨fun S _ _ a => pt C (F S a), ?_, ?_, ?_, ?_⟩
  · intro S _ _
    show pt C (F S 0) = 1
    rw [← uniq S 0 ((Algebra.ofId R₀ S).comp (eps C)) (fun _ => IsNilpotent.zero)
      (fun b => by simp [Algebra.ofId_apply]) (fun j => by simp [Algebra.ofId_apply]), pt_eps]
  · intro S _ _ S' _ _ φ a ha
    show spMap φ ≫ pt C (F S a) = pt C (F S' _)
    rw [spMap_pt]
    congr 1
    refine uniq S' _ _ (fun i => (ha i).map φ) (fun b => ?_) (fun j => ?_)
    · have := ((hF S a ha).1 b).map φ
      rwa [map_sub, AlgHom.commutes] at this
    · rw [AlgHom.comp_apply, (hF S a ha).2, map_add, AlgHom.commutes]
  · intro S _ _ a b ha hb h
    have h1 : F S a = F S b := pt_injective C h
    funext j
    have h2 := (hF S a ha).2 j
    rw [h1, (hF S b hb).2 j] at h2
    exact (add_left_cancel h2).symm
  · intro S _ _ S' _ _ ρ hρ hn z hz
    rw [← pt_eps C S'] at hz
    obtain ⟨φ, rfl⟩ := exists_pt C z (le_preimage_of_nil C ρ hρ hn z _ hz)
    rw [spMap_pt] at hz
    have h1 := pt_injective C hz
    have h2 : ∀ b, φ b - algebraMap R₀ S (eps C b) ∈ RingHom.ker ρ := by
      intro b
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]
      exact AlgHom.congr_fun h1 b
    refine ⟨fun j => φ (π (MvPolynomial.X j)) - algebraMap R₀ S (eps C (π (MvPolynomial.X j))),
      fun j => h2 _, ?_⟩
    show pt C φ = pt C (F S _)
    congr 1
    exact uniq S _ φ (fun j => hn _ (h2 _)) (fun b => hn _ (h2 b)) (fun j => by rw [add_sub_cancel])

end GlobalTheory.NilCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsEqTangent
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory.CotPoints

private lemma comp_assoc' {R₀ : Type} [CommRing R₀] {A B C D : LAlg R₀} (h : LHom C D)
    (g : LHom B C) (f : LHom A B) : (h.comp g).comp f = h.comp (g.comp f) := rfl

private lemma coords_bijective {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : ℕ} (b : Module.Basis (Fin g) R M) :
    Function.Bijective (fun m : Fin g → N => ∑ k, b k ⊗ₜ[R] m k) := by
  classical
  have h : (fun m : Fin g → N => ∑ k, b k ⊗ₜ[R] m k) =
      (TensorProduct.equivFinsuppOfBasisLeft (N := N) b).symm ∘ Finsupp.equivFunOnFinite.symm := by
    funext m
    simp only [Function.comp, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp
  rw [h]
  exact (LinearEquiv.bijective _).comp (Equiv.bijective _)

private lemma coords_nsmul {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : ℕ} (b : Module.Basis (Fin g) R M) (n : ℕ)
    (m : Fin g → N) : n • ∑ k, b k ⊗ₜ[R] m k = ∑ k, b k ⊗ₜ[R] (n • m k) := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => (map_nsmul (TensorProduct.mk R M N (b k)) n (m k)).symm

section

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)

private lemma ptMap_spec (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t ∧
      ∀ j (φ' : LHom (D.fin.AAx j) Tw.O), φ'.comp (D.fin.sO j) = LHom.id Tw.O →
        B.map φ' (D.fin.y j) = ptOf B D.L.τ t → j = D.ptIdx t ∧ HEq φ' (D.ptMap t) :=
  Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))

private lemma ptOf_zero : ptOf B D.L.τ (0 : Nb p g) = 0 := by
  simp [ptOf]

end

theorem points_eq_tangent :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ (S : LAlg R₀) (s : LHom Tw.O S) (π : LHom S Tw.O) (hπ : π.SqZero), π.comp s = LHom.id Tw.O →
    (∀ m : Fin g → π.ker, (∀ k, p • m k = 0) → ∃! φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s ∧ π.comp φ = (D.ptMap 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) ∧
    (∀ φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s → π.comp φ = (D.ptMap 0) → ∃! m : Fin g → π.ker, (∀ k, p • m k = 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k))) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D S s π hπ hs
  obtain ⟨-, h2, h3⟩ := ptMap_spec D 0
  rw [ptOf_zero D] at h2 h3
  refine ⟨fun m hm => ?_, fun φ hφ hπφ => ?_⟩
  · have hz : p • B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k) = 0 := by
      rw [← map_nsmul, coords_nsmul]
      simp [hm]
    obtain ⟨i, φ, e1, e2, e3⟩ := D.fin.univ S s _ hz
    have h4 := h3 i (π.comp φ) (by rw [comp_assoc', e1, hs])
      (by rw [B.map_comp, e2]; exact (B.tg_ker π hπ _).2 ⟨_, rfl⟩)
    obtain ⟨hi, hφ⟩ := h4
    subst hi
    refine ⟨φ, ⟨e1, eq_of_heq hφ, e2⟩, fun φ' h' => ?_⟩
    exact eq_of_heq (e3 _ φ' h'.1 h'.2.2).2
  · have h0 : B.map π (B.map φ (D.fin.y (D.ptIdx 0))) = 0 := by
      rw [← B.map_comp, hπφ, h2]
    obtain ⟨v, hv⟩ := (B.tg_ker π hπ _).1 h0
    have hb := coords_bijective (N := π.ker) D.ch.gb
    obtain ⟨m, hm⟩ := hb.2 v
    have hm' : ∑ k, D.ch.gb k ⊗ₜ[R₀] m k = v := hm
    have hp : p • v = 0 := by
      apply B.tg_inj π hπ
      rw [map_nsmul, hv, ← map_nsmul, D.fin.y_p, map_zero, map_zero]
    refine ⟨m, ⟨fun k => ?_, by rw [hm', hv]⟩, fun m' h' => ?_⟩
    · have : (fun k => p • m k) = (0 : Fin g → π.ker) := by
        apply hb.1
        show ∑ k, D.ch.gb k ⊗ₜ[R₀] (p • m k) = ∑ k, D.ch.gb k ⊗ₜ[R₀] (0 : Fin g → π.ker) k
        rw [← coords_nsmul, hm', hp]
        simp
      exact congrFun this k
    · apply hb.1
      apply B.tg_inj π hπ
      show B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m' k) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)
      rw [← h'.2, hm', hv]

end GlobalTheory.CotPoints
end

