import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsStdOfInjective
section
set_option autoImplicit false

noncomputable section

open DividedPowers TensorProduct

namespace GlobalTheory.PDA.Model

variable {B : Type} [CommRing B] {J : Ideal B}

theorem repr_mul_succ (Q : PDPoly B) (p : Q.P) (n : ℕ) : Q.e.repr (p * Q.e (n + 1)) 0 = 0 := by
  have : (Q.e.coord 0) ∘ₗ LinearMap.mulRight B (Q.e (n + 1)) = 0 := by
    refine Q.e.ext fun m ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
      LinearMap.zero_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
    rw [Finsupp.single_eq_of_ne (by omega), smul_zero]
  exact LinearMap.congr_fun this p

theorem mem_ext_iff (Q : PDPoly B) (p : Q.P) : p ∈ Q.ext J ↔ Q.e.repr p 0 ∈ J := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    have h1 : ∀ q, Q.e.repr (q * a) 0 ∈ J := by
      refine Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 ∈ J) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨j, hj, rfl⟩ q
        rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact J.mul_mem_right _ hj
      · simp
      · intro x y _ _ hx hy q; rw [mul_add, map_add]; exact add_mem (hx q) (hy q)
      · intro r x _ hx q; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    have h2 : ∀ q, Q.e.repr (q * b) 0 = 0 := by
      refine Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 = 0) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩ q; exact repr_mul_succ Q q j
      · simp
      · intro x y _ _ hx hy q; rw [mul_add, map_add, Finsupp.add_apply, hx, hy, add_zero]
      · intro r x _ hx q; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    have h1' := h1 1
    have h2' := h2 1
    rw [one_mul] at h1' h2'
    rw [map_add, Finsupp.add_apply, h2', add_zero]; exact h1'
  · intro h
    rw [← Q.e.linearCombination_repr p, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Ideal.sum_mem _ fun n _ ↦ ?_
    rw [Algebra.smul_def]
    rcases n with _ | n
    · exact Ideal.mul_mem_right _ _ (Q.algebraMap_mem_ext h)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Q.e_succ_mem_aug n))

theorem comap_ext (Q : PDPoly B) : (Q.ext J).comap (algebraMap B Q.P) = J := by
  ext a
  rw [Ideal.mem_comap, mem_ext_iff, Algebra.algebraMap_eq_smul_one, ← Q.e_zero]
  simp

theorem isStd_unique {Q : PDPoly B} {δ : DividedPowers J} {η η' : DividedPowers (Q.ext J)}
    (h : Q.IsStd δ η) (h' : Q.IsStd δ η') : η = η' := by
  refine dpow_eq_from_gens η' η (S := algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1))
    (by rw [Ideal.span_union]; rfl) ?_
  rintro n _ (⟨j, hj, rfl⟩ | ⟨k, rfl⟩)
  · rw [h.dp.dpow_comp j hj, h'.dp.dpow_comp j hj]
  · beta_reduce
    conv_lhs => rw [← h'.var]
    conv_rhs => rw [← h.var]
    rw [η.dpow_comp (by omega) (Q.e_one_mem_ext J), η'.dpow_comp (by omega) (Q.e_one_mem_ext J), h.var, h'.var]

theorem exists_isStd_of_injective (K : Type) [CommRing K] [Algebra ℚ K] [Algebra B K]
    (hK : Function.Injective (algebraMap B K)) (Q : PDPoly B) (δ : DividedPowers J) :
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  classical
  haveI : Module.Free B Q.P := Module.Free.of_basis Q.e
  let f : Q.P →+* K ⊗[B] Q.P := (Algebra.TensorProduct.includeRight (R := B) (A := K) (B := Q.P)).toRingHom
  have hf : Function.Injective f := Algebra.TensorProduct.includeRight_injective hK
  letI : Algebra ℚ (K ⊗[B] Q.P) := ((algebraMap K (K ⊗[B] Q.P)).comp (algebraMap ℚ K)).toAlgebra
  have keyC : ∀ (n : ℕ) (x y : K ⊗[B] Q.P), (n.factorial : K ⊗[B] Q.P) * x = n.factorial * y → x = y :=
    fun n x y h ↦ (IsUnit.natCast_factorial_of_algebra (A := K ⊗[B] Q.P) ℚ n).mul_left_cancel h
  have key : ∀ (n : ℕ) (x y : Q.P), (n.factorial : Q.P) * x = n.factorial * y → x = y :=
    fun n x y h ↦ hf (keyC n _ _ (by simpa using congrArg f h))
  let κ : DividedPowers ((Q.ext J).map f) := RatAlgebra.dividedPowers _
  have hmem : ∀ (n : ℕ) {x : Q.P} (_ : x ∈ Q.ext J), ∃ (y : Q.P) (_ : n ≠ 0 → y ∈ Q.ext J),
      f y = κ.dpow n (f x) := by
    intro n x hx
    have hs : Q.ext J = Ideal.span (algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1)) := by
      rw [Ideal.span_union]; rfl
    have hx' := hx
    rw [hs] at hx'
    revert n
    refine Submodule.span_induction (p := fun x _ ↦ ∀ n, ∃ (y : Q.P) (_ : n ≠ 0 → y ∈ Q.ext J),
      f y = κ.dpow n (f x)) ?_ ?_ ?_ ?_ hx'
    · rintro _ (⟨j, hj, rfl⟩ | ⟨k, rfl⟩) n
      · refine ⟨algebraMap B Q.P (δ.dpow n j), fun hn ↦ Q.algebraMap_mem_ext (δ.dpow_mem hn hj), keyC n _ _ ?_⟩
        rw [factorial_mul_dpow_eq_pow _ (Ideal.mem_map_of_mem f (Q.algebraMap_mem_ext hj)), ← map_pow, ← map_pow,
          ← factorial_mul_dpow_eq_pow δ hj, map_mul, map_natCast, map_mul, map_natCast]
      · refine ⟨(Nat.uniformBell n (k + 1) : Q.P) * Q.e (n * (k + 1)), fun hn ↦ ?_, ?_⟩
        · obtain ⟨m, hm⟩ : ∃ m, n * (k + 1) = m + 1 := Nat.exists_eq_succ_of_ne_zero (by positivity)
          rw [hm]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Q.e_succ_mem_aug m))
        · have he : ∀ m, f (Q.e m) = κ.dpow m (f (Q.e 1)) := fun m ↦ keyC m _ _ (by
            rw [factorial_mul_dpow_eq_pow _ (Ideal.mem_map_of_mem f (Q.e_one_mem_ext J)), ← map_pow, Q.e_one_pow,
              map_mul, map_natCast])
          beta_reduce
          rw [map_mul, map_natCast, he, he (k + 1),
            κ.dpow_comp (by omega) (Ideal.mem_map_of_mem f (Q.e_one_mem_ext J))]
    · intro n
      rcases n with _ | n
      · exact ⟨1, by simp, by rw [map_one, map_zero, κ.dpow_zero (zero_mem _)]⟩
      · exact ⟨0, fun _ ↦ zero_mem _, by rw [map_zero, κ.dpow_eval_zero (by omega)]⟩
    · intro x y hx hy ihx ihy n
      replace hx : x ∈ Q.ext J := hs.ge hx
      replace hy : y ∈ Q.ext J := hs.ge hy
      choose u hu hu' using ihx
      choose v hv hv' using ihy
      refine ⟨∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, u k.1 * v k.2, fun hn ↦ Ideal.sum_mem _ fun k hk ↦ ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
        by_cases h0 : k.1 = 0
        · exact Ideal.mul_mem_left _ _ (hv _ (by omega))
        · exact Ideal.mul_mem_right _ _ (hu _ h0)
      · rw [map_add, κ.dpow_add (Ideal.mem_map_of_mem f hx) (Ideal.mem_map_of_mem f hy), map_sum]
        simp only [map_mul, hu', hv']
    · intro a x hx ih n
      replace hx : x ∈ Q.ext J := hs.ge hx
      obtain ⟨y, hy, hy'⟩ := ih n
      refine ⟨a ^ n * y, fun hn ↦ Ideal.mul_mem_left _ _ (hy hn), ?_⟩
      rw [smul_eq_mul, map_mul, map_mul, κ.dpow_mul (Ideal.mem_map_of_mem f hx), hy', map_pow]
  refine ⟨DividedPowers.ofInjective _ _ f hf κ rfl hmem, ⟨le_sup_left, fun {n} a ha ↦ key n _ _ ?_⟩,
    fun n ↦ key n _ _ ?_⟩
  · rw [factorial_mul_dpow_eq_pow _ (Q.algebraMap_mem_ext ha), ← map_pow,
      ← factorial_mul_dpow_eq_pow δ ha, map_mul, map_natCast]
  · rw [factorial_mul_dpow_eq_pow _ (Q.e_one_mem_ext J), Q.e_one_pow]

theorem exists_isStd_int : ∃ η : DividedPowers ((stdPoly ℤ).ext ⊥), (stdPoly ℤ).IsStd (dividedPowersBot ℤ) η :=
  exists_isStd_of_injective ℚ (algebraMap ℤ ℚ).injective_int _ _

theorem exists_isStd_padic (p : ℕ) [Fact p.Prime] :
    ∃ η : DividedPowers ((stdPoly ℤ_[p]).ext (Ideal.span {(p : ℤ_[p])})),
      (stdPoly ℤ_[p]).IsStd (PadicInt.dividedPowers p) η :=
  exists_isStd_of_injective ℚ_[p] (IsFractionRing.injective ℤ_[p] ℚ_[p]) _ _

def gam (n : ℕ) (x : ZMod 4) : ZMod 4 :=
  if x = 0 ∨ x = 2 then (if n = 0 then 1 else if n = 1 ∨ n = 4 then x else 0) else 0

theorem mem_two (x : ZMod 4) : x ∈ Ideal.span {(2 : ZMod 4)} ↔ x = 0 ∨ x = 2 := by
  rw [Ideal.mem_span_singleton']; revert x; decide

theorem gam_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (x y : ZMod 4) : gam m x * gam n y = 0 := by
  unfold gam
  simp only [hm, hn, if_false]
  by_cases h1 : m = 1 ∨ m = 4 <;> by_cases h2 : n = 1 ∨ n = 4 <;> simp only [h1, h2] <;> revert x y <;> decide

theorem gam_isPreDP_and_ne_dpow : IsPreDP (Ideal.span {(2 : ZMod 4)}) gam ∧
    ∀ δ : DividedPowers (Ideal.span {(2 : ZMod 4)}), δ.dpow ≠ gam := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun δ h ↦ ?_⟩
  · intro n x hx; rw [mem_two] at hx; simp only [gam, hx, if_false]
  · intro x hx; rw [mem_two] at hx; simp [gam, hx]
  · intro x hx; rw [mem_two] at hx; simp [gam, hx]
  · intro n hn x hx; rw [mem_two] at hx ⊢; simp only [gam, hx, hn, if_true, if_false]; split_ifs <;> simp [hx]
  · intro n x hx y hy
    rw [mem_two] at hx hy
    rcases n with _ | n
    · simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      revert x y; decide
    · rw [Finset.Nat.sum_antidiagonal_succ]
      rcases n with _ | n
      · simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
        revert x y; decide
      · rw [Finset.Nat.sum_antidiagonal_succ', Finset.sum_eq_zero fun k _ ↦ gam_mul _ _ (by omega) (by omega) _ _]
        simp only [gam, add_zero]
        by_cases h : n + 1 + 1 = 1 ∨ n + 1 + 1 = 4 <;> simp only [h] <;> simp <;> revert x y <;> decide
  · intro n a x hx
    rw [mem_two] at hx
    by_cases h0 : n = 0
    · subst h0; revert a x; decide
    by_cases h1 : n = 1
    · subst h1; revert a x; decide
    by_cases h4 : n = 4
    · subst h4; revert a x; decide
    simp [gam, h0, h1, h4]
  · intro m n x hx
    rw [mem_two] at hx
    by_cases hm : m = 0
    · subst hm; simp [gam, hx]
    by_cases hn : n = 0
    · subst hn; simp [gam, hx]
    rw [gam_mul m n hm hn]
    by_cases h4 : m + n = 4
    · have : m = 1 ∧ n = 3 ∨ m = 2 ∧ n = 2 ∨ m = 3 ∧ n = 1 := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert x <;> decide
    · have h1 : m + n ≠ 1 := by omega
      have h0 : m + n ≠ 0 := by omega
      simp only [gam, h0, h1, h4]; simp
  · have := δ.dpow_comp (m := 2) (n := 2) (x := 2) (by omega) ((mem_two 2).2 (Or.inr rfl))
    rw [h] at this
    have hb : Nat.uniformBell 2 2 = 3 := by
      have := Nat.uniformBell_mul_eq 2 (n := 2) (by omega)
      simp [Nat.factorial] at this; omega
    rw [hb] at this
    revert this; decide

end GlobalTheory.PDA.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.LiftSys

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {X₀ : Scheme.{0}}

structure Sys (I : Ideal R) (π : R →+* R₀) (s₀ : X₀ ⟶ Sp R₀) : Type 1 where

  F : AffOp X₀ ⥤ CommAlgCat.{0} R

  p : ∀ U : AffOp X₀, F.obj U →+* Sec s₀ U.unop.1
  semi : ∀ U, SemiHom π (p U)
  nat : ∀ {U V : AffOp X₀} (a : U ⟶ V) (b : F.obj U), p V (mp F a b) = mp (OAff s₀) a (p U b)
  surj : ∀ U, Function.Surjective (p U)
  ker : ∀ U b, p U b = 0 ↔ b ∈ I.map (algebraMap R (F.obj U))
  smooth : ∀ U, Algebra.Smooth R (F.obj U)

theorem map_sq (hI : I ^ 2 = 0) (B : Type) [CommRing B] [Algebra R B] : I.map (algebraMap R B) ^ 2 = 0 := by
  rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]

theorem surjective_spMap_sqZero {B B₀ : Type} [CommRing B] [CommRing B₀] (p : B →+* B₀) (hp : Function.Surjective p)
    {J : Ideal B} (hJ : J ^ 2 = 0) (hk : ∀ b, p b = 0 → b ∈ J) : Surjective (spMap p) :=
  ⟨(PrimeSpectrum.isHomeomorph_comap p (fun x ↦ ⟨1, one_pos, by simpa using hp x⟩) fun b hb ↦
    ⟨2, by simpa [hJ] using Ideal.pow_mem_pow (hk b hb) 2⟩).surjective⟩

theorem surjective_of_isPullback_sqZero (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) {s₀ : X₀ ⟶ Sp R₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}
    (h : IsPullback i s₀ s (spMap π)) : Surjective i :=
  MorphismProperty.of_isPullback (P := @Surjective) h.flip
    (surjective_spMap_sqZero π hπ hI fun _ hb ↦ hk ▸ RingHom.mem_ker.2 hb)

variable {π : R →+* R₀} {s₀ : X₀ ⟶ Sp R₀}

abbrev Cr (hI : I ^ 2 = 0) (π : R →+* R₀) (s₀ : X₀ ⟶ Sp R₀) : Type 1 := Cris.H1 (divided₂ hI) (s₀ ≫ spMap π)

namespace Sys

variable (S S' : Sys I π s₀) (hI : I ^ 2 = 0)

@[reducible] def thickObj (U : AffOp X₀) : Thick (divided₂ hI) (s₀ ≫ spMap π) where
  B := S.F.obj U
  J := I.map (algebraMap R (S.F.obj U))
  δ := divided₂ (map_sq hI _)
  nil := isDPNilpotent_squareZero _
  dp := isDPMorphism_sqDP hI _ _ fun _ ha ↦ Ideal.mem_map_of_mem _ ha
  B₀ := Sec s₀ U.unop.1
  π := S.p U
  surj := S.surj U
  ker := S.ker U
  x := affPt s₀ U.unop
  w := by
    rw [← Category.assoc, affPt_w, ← Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun r ↦ ((S.semi U).map_algebraMap r).symm)

def thickHom {U V : AffOp X₀} (a : U ⟶ V) (α : S.F.obj U →ₐ[R] S'.F.obj V)
    (h : ∀ b, S'.p V (α b) = mp (OAff s₀) a (S.p U b)) : S.thickObj hI U ⟶ S'.thickObj hI V where
  φ := α
  φ₀ := (Sec.res s₀ (leOfHom a.unop) : Sec s₀ U.unop.1 →+* Sec s₀ V.unop.1)
  comm b := (h b).symm
  dp := isDPMorphism_sqDP (map_sq hI _) (map_sq hI _) _ fun b hb ↦ (S'.ker V _).1 (by
    have : S.p U b = 0 := (S.ker U b).2 hb
    exact (h b).trans (by rw [this, map_zero]))
  pt := affPt_res s₀ (leOfHom a.unop)

def thick : AffOp X₀ ⥤ Thick (divided₂ hI) (s₀ ≫ spMap π) where
  obj := S.thickObj hI
  map a := S.thickHom S hI a (mp S.F a) (S.nat a)
  map_id U := Thick.hom_ext (mp_id S.F U)
  map_comp a b := Thick.hom_ext (mp_comp S.F a b)

def coef : CoefMap (RingHom.id R) (O (divided₂ hI) (s₀ ≫ spMap π)) S.F where
  G := S.thick hI
  α U := RingHom.id (S.F.obj U)
  naturality _ _ := rfl
  smul _ _ _ := rfl

def r : Cr hI π s₀ →ₗ[R] CatCoh.H1 S.F := (S.coef hI).pull1

def K : Submodule R (Cr hI π s₀) := LinearMap.ker (S.r hI)

def redO : CoefMap π S.F (OAff s₀) where
  G := 𝟭 _
  α := S.p
  naturality a b := S.nat a b
  smul U := S.semi U

def IsIdealValuedLiftSystemCochain (g : C0 S.F) : Prop := ∀ U, g U ∈ I.map (algebraMap R (S.F.obj U))

def IsIdealValuedLiftSystemCocycle (z : Z1 S.F) : Prop := ∀ (U V : AffOp X₀) (a : U ⟶ V), z.1 U V a ∈ I.map (algebraMap R (S.F.obj V))

structure Presents {X : Scheme.{0}} (s : X ⟶ Sp R) (i : X₀ ⟶ X) where

  y : ∀ U : AffOp X₀, Sp (S.F.obj U) ⟶ X
  isOpen : ∀ U, IsOpenImmersion (y U)
  base : ∀ U, y U ≫ s = spMap (algebraMap R (S.F.obj U))
  nat : ∀ ⦃U V : AffOp X₀⦄ (a : U ⟶ V), spMap (mp S.F a : S.F.obj U →+* S.F.obj V) ≫ y U = y V
  red : ∀ U, spMap (S.p U) ≫ y U = affPt s₀ U.unop ≫ i

  cover : ∀ x : X, ∃ U, x ∈ Set.range (y U).base

theorem cover_of_surjective {X : Scheme.{0}} {i : X₀ ⟶ X} (hi : Surjective i) (y : ∀ U : AffOp X₀, Sp (S.F.obj U) ⟶ X)
    (red : ∀ U, spMap (S.p U) ≫ y U = affPt s₀ U.unop ≫ i) (x : X) : ∃ U, x ∈ Set.range (y U).base := by
  obtain ⟨x₀, rfl⟩ := hi.surj x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X₀.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  have hx' : x₀ ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hx
  obtain ⟨q, rfl⟩ := hx'
  refine ⟨Opposite.op ⟨U, hU⟩, spMap (S.p (Opposite.op ⟨U, hU⟩)) q, ?_⟩
  have := congrArg (fun f : Sp (Sec s₀ U) ⟶ X ↦ f q) (red (Opposite.op ⟨U, hU⟩))
  exact this

def Presents.ofSurjective {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (hi : Surjective i)
    (y : ∀ U : AffOp X₀, Sp (S.F.obj U) ⟶ X) (isOpen : ∀ U, IsOpenImmersion (y U))
    (base : ∀ U, y U ≫ s = spMap (algebraMap R (S.F.obj U)))
    (nat : ∀ ⦃U V : AffOp X₀⦄ (a : U ⟶ V), spMap (mp S.F a : S.F.obj U →+* S.F.obj V) ≫ y U = y V)
    (red : ∀ U, spMap (S.p U) ≫ y U = affPt s₀ U.unop ≫ i) : S.Presents s i :=
  ⟨y, isOpen, base, nat, red, S.cover_of_surjective hi y red⟩

include hI in

theorem surjective_spMap_p (U : AffOp X₀) : Surjective (spMap (S.p U)) :=
  surjective_spMap_sqZero (S.p U) (S.surj U) (map_sq hI _) fun b hb ↦ (S.ker U b).1 hb

include hI in

theorem Presents.surjective {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (P : S.Presents s i) : Surjective i := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, q, rfl⟩ := P.cover x
  obtain ⟨q₀, rfl⟩ := (S.surjective_spMap_p hI U).surj q
  refine ⟨affPt s₀ U.unop q₀, ?_⟩
  have := congrArg (fun f : Sp (Sec s₀ U.unop.1) ⟶ X ↦ f q₀) (P.red U)
  simpa only [Scheme.Hom.comp_apply] using this.symm

structure LocIso where

  φ : ∀ U : AffOp X₀, S.F.obj U ≃ₐ[R] S'.F.obj U
  red : ∀ U b, S'.p U (φ U b) = S.p U b

def Full : Prop := ∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ c ∈ I • (⊤ : Submodule R (Cr hI π s₀)), S.r hI c = H1.mk _ z

end Sys

structure IsTheta (I : Ideal R) {B B₀ B' : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B']
    [Algebra R B'] (p : B →+* B₀) (α β : B →ₐ[R] B') (θ : Ω[B₀⁄R₀] →+ B') : Prop where
  smul : ∀ b w, θ (p b • w) = α b * θ w
  der : ∀ b, θ (D R₀ B₀ (p b)) = α b - β b
  mem : ∀ w, θ w ∈ I.map (algebraMap R B')

theorem isTheta_zero (I : Ideal R) {B B₀ B' : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    [CommRing B'] [Algebra R B'] (p : B →+* B₀) (α : B →ₐ[R] B') : IsTheta (R₀ := R₀) I p α α 0 :=
  ⟨fun _ _ ↦ by simp, fun _ ↦ by simp, fun _ ↦ by simp⟩

def Sys.LocIso.IsDefect {S S' : Sys I π s₀} (Φ : S.LocIso S')
    (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V) : Prop :=
  ∀ (U V : AffOp X₀) (a : U ⟶ V), IsTheta I (S.p U) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))
    ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (θ U V a)

def Sys.LocIso.refl (S : Sys I π s₀) : S.LocIso S := ⟨fun _ ↦ AlgEquiv.refl, fun _ _ ↦ rfl⟩

theorem redMor (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (s₀ : X₀ ⟶ Sp R₀) :
    IsMor (divided₂ hI) (s₀ ≫ spMap π) (dp0 R₀) s₀ π (𝟙 X₀) where
  dp := by
    have z : ∀ a ∈ I, π a = 0 := fun a ha ↦ RingHom.mem_ker.1 (hk ▸ ha)
    refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ z a ha, fun n hn a ha ↦ ?_⟩
    rw [z a ha, z _ ((divided₂ hI).dpow_mem hn ha), dpow_eval_zero _ hn]
  w := Category.id_comp _

def rho (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (s₀ : X₀ ⟶ Sp R₀) : Cr hI π s₀ →ₛₗ[π] FirstDeRham s₀ :=
  (redMor hI hk s₀).pull1

def FormOf (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (c : Cr hI π s₀) (w : GlobForm s₀) : Prop :=
  ∃ f : Form s₀, Form.cl s₀ f = rho hI hk s₀ c ∧ (cmpForm s₀ f).1 = w

def evForm (s₀ : X₀ ⟶ Sp R₀) (U : AffOp X₀) : GlobForm s₀ →ₗ[R₀] Ω[Sec s₀ U.unop.1⁄R₀] where
  toFun w := w.1 U
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Const (s₀ : X₀ ⟶ Sp R₀) : Prop :=
  ∀ g : C0 (OAff s₀), d0 _ g = 0 → ∃ r : R₀, ∀ U, g U = algebraMap R₀ (Sec s₀ U.unop.1) r

def Par (s₀ : X₀ ⟶ Sp R₀) : Prop := ∀ U : AffOp X₀, IsBaseChange (Sec s₀ U.unop.1) (evForm s₀ U)

structure Good (s₀ : X₀ ⟶ Sp R₀) : Prop where
  const : Const s₀
  par : Par s₀
  proj : Module.Projective R₀ (GlobForm s₀)
  surj : ∀ w : GlobForm s₀, ∃ f : Form s₀, (cmpForm s₀ f).1 = w
  inj : ∀ f : Form s₀, Form.cl s₀ f = 0 ↔ cmpForm s₀ f = 0

def RhoBC (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (s₀ : X₀ ⟶ Sp R₀) : Prop :=
  Function.Surjective (rho hI hk s₀) ∧ ∀ c, rho hI hk s₀ c = 0 ↔ c ∈ I • (⊤ : Submodule R (Cr hI π s₀))

section Self

variable {X : Scheme.{0}} (s : X ⟶ Sp R)

theorem smooth_sec_affine [Smooth s] (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  haveI : IsOpenImmersion (affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h : Smooth (affPt s U ≫ s) := inferInstance
  rw [affPt_w] at h
  exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)

def Sys.self [Smooth s] : Sys (⊥ : Ideal R) (RingHom.id R) s where
  F := OAff s
  p _ := RingHom.id _
  semi _ := fun _ _ ↦ rfl
  nat _ _ := rfl
  surj _ := Function.surjective_id
  ker U b := by simp [Ideal.map_bot]
  smooth U := smooth_sec_affine s U.unop

def Sys.selfPresents [Smooth s] : (Sys.self s).Presents s (𝟙 X) :=
  Sys.Presents.ofSurjective _ inferInstance (fun U ↦ affPt s U.unop)
    (fun U ↦ IsAffineOpen.isOpenImmersion_fromSpec U.unop.2) (fun U ↦ affPt_w s U.unop)
    (fun _ _ a ↦ affPt_res s (leOfHom a.unop)) fun U ↦ by
      change spMap (RingHom.id _) ≫ affPt s U.unop = affPt s U.unop ≫ 𝟙 X
      rw [Category.comp_id, Cris.spMap_id, Category.id_comp]

example [Smooth s] : (Sys.LocIso.refl (Sys.self s)).IsDefect (fun _ _ _ ↦ 0) := fun _ _ _ ↦ isTheta_zero _ _ _

example [Smooth s] {Y : Scheme.{0}} (t : Y ⟶ Sp R) (i : X ⟶ Y) (hi : ¬ Surjective i) :
    IsEmpty ((Sys.self s).Presents t i) :=
  ⟨fun P ↦ hi (P.surjective _ (by simp))⟩

end Self

end GlobalTheory.LiftSys
end
end

