import Mathlib
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.DualLattices.Bundle0029
import ReciprocityTheory.DualLattices.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothNilLift

theorem exists_lift_of_nil {R A W K : Type} [CommRing R] [CommRing A] [CommRing W] [CommRing K]
    [Algebra R A] [Algebra R W] [Algebra R K] [Algebra.Smooth R A] (ρ : W →ₐ[R] K)
    (hρ : Function.Surjective ρ) (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (φ : A →ₐ[R] K) :
    ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  choose w hw using fun i : Fin n => hρ (φ (f (MvPolynomial.X i)))
  let g : MvPolynomial (Fin n) R →ₐ[R] W := MvPolynomial.aeval w
  have hg : ρ.comp g = φ.comp f := by
    ext i
    simp [g, hw]
  have hg' : ∀ p, ρ (g p) = φ (f p) := fun p => AlgHom.congr_fun hg p
  let J : Ideal W := (RingHom.ker f.toRingHom).map g.toRingHom
  have hJ : J ≤ RingHom.ker ρ := by
    refine Ideal.map_le_iff_le_comap.mpr fun p hp => ?_
    have hp' : f p = 0 := hp
    change ρ (g p) = 0
    rw [hg', hp', map_zero]
  have hJfg : J.FG := hker.map _
  have hJn : IsNilpotent J :=
    (Ideal.FG.isNilpotent_iff_le_nilradical hJfg).mpr fun a ha => hn a (hJ ha)
  let g₀ : (MvPolynomial (Fin n) R ⧸ RingHom.ker f) →ₐ[R] W ⧸ J :=
    Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp g) fun p hp =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.toRingHom hp)
  let E := Ideal.quotientKerAlgEquivOfSurjective hf
  let ψ₀ : A →ₐ[R] W ⧸ J := g₀.comp E.symm.toAlgHom
  have hψ₀ : ∀ p, ψ₀ (f p) = Ideal.Quotient.mk J (g p) := by
    intro p
    have h1 : E.symm (f p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change g₀ (E.symm (f p)) = _
    rw [h1]
    rfl
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_lift J hJn ψ₀
  refine ⟨ψ, AlgHom.ext fun a => ?_⟩
  obtain ⟨p, rfl⟩ := hf a
  have h2 : Ideal.Quotient.mk J (ψ (f p)) = Ideal.Quotient.mk J (g p) :=
    (AlgHom.congr_fun hψ (f p)).trans (hψ₀ p)
  have h3 : ρ (ψ (f p) - g p) = 0 := hJ (Ideal.Quotient.eq.mp h2)
  rw [map_sub, sub_eq_zero] at h3
  change ρ (ψ (f p)) = _
  rw [h3, hg']

theorem exists_point_lift {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀)))
    [Smooth X.hom] {W K : Type} [CommRing W] [CommRing K] [Algebra R₀ W] [Algebra R₀ K]
    [IsLocalRing K] (ρ : W →ₐ[R₀] K) (hρ : Function.Surjective ρ)
    (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (z : sp (R₀ := R₀) K ⟶ X) :
    ∃ y : sp (R₀ := R₀) W ⟶ X, spMap ρ ≫ y = z := by
  let x : Spec (CommRingCat.of K) ⟶ X.left := z.left
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint K))) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum K) ⤳ IsLocalRing.closedPoint K :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum K).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hmem
  let a0 : R₀ →+* Γ(X.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ X.hom.appLE ⊤ U le_top).hom
  letI : Algebra R₀ Γ(X.left, U) := a0.toAlgebra
  have hover : hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom a0) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of R₀))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, CommRingCat.ofHom_hom, Spec.map_comp]
  haveI : Algebra.Smooth R₀ Γ(X.left, U) := by
    have h1 : RingHom.Smooth (X.hom.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Smooth) X.hom inferInstance
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R₀))⟩ ⟨U, hU⟩ le_top
    have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom :=
      RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv.bijective
    exact h2.comp h1
  let φ := x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hφx : Spec.map φ ≫ hU.fromSpec = x := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
      (isAffineOpen_top (Spec (CommRingCat.of K))) hx
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  have hφ : φ.hom.comp a0 = algebraMap R₀ K := by
    have e : Spec.map (CommRingCat.ofHom (φ.hom.comp a0)) =
        Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := by
      calc Spec.map (CommRingCat.ofHom (φ.hom.comp a0))
          = Spec.map φ ≫ Spec.map (CommRingCat.ofHom a0) := by
            rw [← Spec.map_comp]; rfl
        _ = Spec.map φ ≫ hU.fromSpec ≫ X.hom := by rw [hover]
        _ = x ≫ X.hom := by rw [← Category.assoc, hφx]
        _ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := Over.w z
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let φ' : Γ(X.left, U) →ₐ[R₀] K := ⟨φ.hom, fun r => RingHom.congr_fun hφ r⟩
  obtain ⟨ψ, hψ⟩ := exists_lift_of_nil ρ hρ hn φ'
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec) ?_, ?_⟩
  · simp only [sp, Over.mk_hom]
    rw [Category.assoc, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec = x
    rw [← hφx, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact AlgHom.congr_fun hψ a

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    Smooth G.hom → ∀ (K W : LAlg R₀) (ρW : LHom W K), IsNilOver ρW → SM B K W ρW) := by
  intro R₀ _ G _ _ B e hb _ hnat hsm K W ρW hρ
  refine ⟨hρ, fun x => ?_⟩
  obtain ⟨y, hy⟩ := exists_point_lift G ρW.1 hρ.1 hρ.2 (e K x)
  obtain ⟨y', rfl⟩ := (hb W).2 y
  exact ⟨y', (hb K).1 (by rw [hnat, hy])⟩

end GlobalTheory.SmoothNilLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfNaturalOnNilpotent
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private noncomputable abbrev serNatI (R₀ κ : Type) [CommRing R₀] (N : ℕ) : Ideal (MvPolynomial κ R₀) :=
  Ideal.span (Set.range fun j : κ => (MvPolynomial.X j : MvPolynomial κ R₀) ^ N)

private lemma serNat_coeff {R₀ κ : Type} [CommRing R₀] [DecidableEq κ] {N : ℕ}
    {q : MvPolynomial κ R₀} (hq : q ∈ serNatI R₀ κ N) :
    ∀ m : κ →₀ ℕ, (∀ j, m j < N) → MvPolynomial.coeff m q = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨j, rfl⟩ m hm
    simp only [MvPolynomial.coeff_X_pow]
    rw [if_neg]
    rintro rfl
    simpa using hm j
  · intro m _; simp
  · intro x y _ _ hx hy m hm
    rw [MvPolynomial.coeff_add, hx m hm, hy m hm, add_zero]
  · intro r x _ hx m hm
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2, mul_zero]
    intro j
    have : p.1 + p.2 = m := by simpa using hp
    have h2 := hm j
    rw [← this, Finsupp.add_apply] at h2
    omega

private lemma serNat_nil {R₀ κ : Type} [CommRing R₀] (N : ℕ) (j : κ) :
    (Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)) ^ N = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩

private lemma serNat_aeval {R₀ κ : Type} [CommRing R₀] [Fintype κ] [DecidableEq κ]
    {S : Type} [CommRing S] [Algebra R₀ S] {N : ℕ} {a : κ → S} (ha : ∀ i, a i ^ N = 0)
    (q : MvPolynomial κ R₀) :
    MvPolynomial.aeval a q = ∑ e : κ → Fin N, algebraMap R₀ S (MvPolynomial.coeff
      (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) q) * ∏ i, a i ^ (e i : ℕ) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | monomial m r =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    by_cases hm : ∀ j, m j < N
    · rw [Finset.sum_eq_single (fun j => (⟨m j, hm j⟩ : Fin N))]
      · rw [MvPolynomial.coeff_monomial, if_pos]
        ext j; simp
      · intro e _ he
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply he
        funext j
        apply Fin.ext
        simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · push Not at hm
        obtain ⟨j, hj⟩ := hm
        rw [Finset.prod_eq_zero (f := fun i => a i ^ m i) (Finset.mem_univ j)
          (pow_eq_zero_of_le hj (ha j)), mul_zero]
      · intro e _
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply hm
        intro j
        simp [h]

theorem exists_series_of_natural_on_nilpotent :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) := by
  intro hE R₀ _ κ _ _ c hc
  choose p hp using fun N : ℕ => Ideal.Quotient.mk_surjective (I := serNatI R₀ κ N)
    (c (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N)
      (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)))
  have key : ∀ (N : ℕ) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, a i ^ N = 0) →
      c S a = MvPolynomial.aeval a (p N) := by
    intro N S _ _ a ha
    let φ : (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ (serNatI R₀ κ N) (MvPolynomial.aeval a) (by
        intro x hx
        have : serNatI R₀ κ N ≤ RingHom.ker (MvPolynomial.aeval (R := R₀) a) := by
          refine Ideal.span_le.2 ?_
          rintro _ ⟨j, rfl⟩
          simp [RingHom.mem_ker, ha j]
        exact this hx)
    have hφ : ∀ x, φ (Ideal.Quotient.mk (serNatI R₀ κ N) x) = MvPolynomial.aeval a x :=
      fun x => rfl
    have h := hc _ S φ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => ⟨N, serNat_nil N j⟩)
    rw [← hp N, hφ] at h
    simp only [hφ, MvPolynomial.aeval_X] at h
    exact h.symm
  have compat : ∀ N M : ℕ, N ≤ M → ∀ m : κ →₀ ℕ, (∀ j, m j < N) →
      MvPolynomial.coeff m (p M) = MvPolynomial.coeff m (p N) := by
    intro N M h m hm
    have h1 := key M _ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => pow_eq_zero_of_le h (serNat_nil N j))
    have h2 : MvPolynomial.aeval (R := R₀)
        (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
        = Ideal.Quotient.mkₐ R₀ (serNatI R₀ κ N) := by
      ext j; simp
    rw [← hp N, h2, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h1
    have h3 := serNat_coeff h1 m hm
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
    exact h3.symm
  refine ⟨fun m => MvPolynomial.coeff m (p (Finset.univ.sup m + 1)), ?_⟩
  intro S _ _ a ha
  choose n hn using ha
  have hN : ∀ i, a i ^ (Finset.univ.sup n) = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  generalize Finset.univ.sup n = N at hN
  refine Eq.trans ?_ ((hE _ S a).1 N hN).symm
  rw [key N S a hN, serNat_aeval hN]
  unfold tEval
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 2
  set m : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ) with hm
  change _ = MvPolynomial.coeff m (p (Finset.univ.sup m + 1))
  rw [← compat N (max N (Finset.univ.sup m + 1)) (le_max_left _ _) m (fun j => by simp [hm]),
    compat _ _ (le_max_right _ _) m
      (fun j => Nat.lt_succ_of_le (Finset.le_sup (f := m) (Finset.mem_univ j)))]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FAddNsmulFEqEvalPolyFrob
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private def btPolySub (p : ℕ) (g : ℕ) (W : Type) [CommRing W] :
    Subalgebra W (MvPolynomial (Fin g) W) where
  carrier := {q | ∀ m : Fin g →₀ ℕ, (∃ i, ¬ p ∣ m i) →
    MvPolynomial.coeff m q ∈ Ideal.span {(p : W)}}
  add_mem' := by
    intro a b ha hb m hm
    rw [MvPolynomial.coeff_add]
    exact Ideal.add_mem _ (ha m hm) (hb m hm)
  mul_mem' := by
    intro a b ha hb m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h1 : p ∣ x.1 i
    · refine Ideal.mul_mem_left _ _ (hb _ ⟨i, fun h2 => hi ?_⟩)
      rw [← hx', Finsupp.add_apply]
      exact dvd_add h1 h2
    · exact Ideal.mul_mem_right _ _ (ha _ ⟨i, h1⟩)
  algebraMap_mem' := by
    intro r m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C, if_neg]
    · exact Ideal.zero_mem _
    · rintro rfl
      exact hi (by simp)

private lemma btPoly_map_tEval {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (f : MvPowerSeries ι R₀) {S S' : Type} [CommRing S] [Algebra R₀ S] [CommRing S']
    [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : ι → S) :
    φ (tEval N f a) = tEval N f (fun i => φ (a i)) := by
  simp [tEval, map_sum, map_prod]

private lemma btPoly_unif {ι S : Type} [Fintype ι] [CommRing S] (a : ι → S)
    (h : ∀ i, IsNilpotent (a i)) : ∃ M, ∀ M' ≥ M, ∀ i, a i ^ M' = 0 := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun M' hM i => ?_⟩
  exact pow_eq_zero_of_le ((Finset.le_sup (Finset.mem_univ i)).trans hM) (hn i)

private lemma btPoly_nil {R₀ : Type} [CommRing R₀]
    (H : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S]
      [Algebra R₀ S] (a : ι → S), (∀ i, IsNilpotent (a i)) →
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))
    {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S]
    (a : Fin g → S) (ha : ∀ i, IsNilpotent (a i)) (n : ℕ) :
    ∀ k, IsNilpotent (nsmulF ch.F a n k) := by
  have h0 : ∀ k, algebraMap R₀ S (MvPowerSeries.coeff 0 (ch.F k)) = 0 := by
    intro k
    have h1 := congrFun (ch.F_unit S 0 (fun _ => IsNilpotent.zero)) k
    have h2 := H (ch.F k) S (Sum.elim (0 : Fin g → S) (0 : Fin g → S))
      (by rintro (i | i) <;> exact IsNilpotent.zero)
    have h3 : Ideal.span (Set.range (Sum.elim (0 : Fin g → S) (0 : Fin g → S))) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i | i, rfl⟩ <;> rfl
    rw [h3, Ideal.mem_bot] at h2
    change nEval _ _ = 0 at h1
    rw [h1] at h2
    simpa using h2
  induction n with
  | zero => intro k; exact IsNilpotent.zero
  | succ n ih =>
    intro k
    have hn : ∀ i, IsNilpotent (Sum.elim (nsmulF ch.F a n) a i) := by
      rintro (i | i)
      · exact ih i
      · exact ha i
    have h2 := H (ch.F k) S _ hn
    rw [h0, sub_zero] at h2
    have h3 : Ideal.span (Set.range (Sum.elim (nsmulF ch.F a n) a)) ≤ nilradical S := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hn i
    exact h3 h2

theorem fAdd_nsmulF_eq_eval_poly_frob :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} (K : LAlg R₀) (ch : FormalChartAtZero B K g), PSerFrobStatement p K ch) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (W : Type) [CommRing W] [Algebra R₀ W] (c : Fin g → W),
    (∀ i, IsNilpotent (c i)) → ∀ N : ℕ, ∃ Γ : Fin g → MvPolynomial (Fin g) W,
      (∀ k m, (∃ i, ¬ p ∣ m i) → MvPolynomial.coeff m (Γ k) ∈ Ideal.span {(p : W)}) ∧
      ∀ y : Fin g → W, (∀ i, y i ^ N = 0) → fAdd ch.F c (nsmulF ch.F y p) = fun k => MvPolynomial.eval y (Γ k)) := by
  intro H1 H2 R₀ _ p _ g B K ch W _ _ c hc N
  obtain ⟨G, hG, hGe⟩ := H2 p K ch N
  let I : Ideal (MvPolynomial (Fin g) R₀) := Ideal.span (Set.range fun j => MvPolynomial.X j ^ N)
  let x : Fin g → MvPolynomial (Fin g) R₀ ⧸ I := fun j => Ideal.Quotient.mk I (MvPolynomial.X j)
  have hx : ∀ j, x j ^ N = 0 := fun j => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hae : (MvPolynomial.aeval x : MvPolynomial (Fin g) R₀ →ₐ[R₀] _) = Ideal.Quotient.mkₐ R₀ I := by
    ext j; simp [x]
  have hnil : ∀ k, IsNilpotent (Ideal.Quotient.mk I (G k)) := fun k => by
    have := btPoly_nil (fun f S _ _ a ha => ((H1 f S a).2 ha).2) ch _ x (fun i => ⟨N, hx i⟩) p k
    rw [hGe _ x hx, hae] at this
    exact this
  obtain ⟨M₁, hM₁⟩ := btPoly_unif _ hnil
  obtain ⟨M₂, hM₂⟩ := btPoly_unif _ hc
  let z : Fin g ⊕ Fin g → MvPolynomial (Fin g) W :=
    Sum.elim (fun i => MvPolynomial.C (c i)) (fun i => MvPolynomial.map (algebraMap R₀ W) (G i))
  refine ⟨fun k => tEval (max M₁ M₂) (ch.F k) z, fun k => ?_, fun y hy => ?_⟩
  · change tEval (max M₁ M₂) (ch.F k) z ∈ btPolySub p g W
    unfold tEval
    refine Subalgebra.sum_mem _ fun e _ => Subalgebra.mul_mem _ ?_
      (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · rw [IsScalarTower.algebraMap_apply R₀ W]
      exact Subalgebra.algebraMap_mem _ _
    · rcases i with i | i
      · exact Subalgebra.algebraMap_mem (btPolySub p g W) (c i)
      · intro m hm
        obtain ⟨r, hr⟩ := hG i m hm
        change MvPolynomial.coeff m (MvPolynomial.map (algebraMap R₀ W) (G i)) ∈ _
        rw [MvPolynomial.coeff_map, hr, map_mul, map_natCast]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · funext k
    have hI : ∀ q ∈ I, MvPolynomial.aeval y q = (0 : W) := by
      intro q hq
      have : I ≤ RingHom.ker (MvPolynomial.aeval y : MvPolynomial (Fin g) R₀ →ₐ[R₀] W) := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        simp [RingHom.mem_ker, hy j]
      exact this hq
    have e1 := btPoly_map_tEval (max M₁ M₂) (ch.F k)
      ((MvPolynomial.aeval y : MvPolynomial (Fin g) W →ₐ[W] W).restrictScalars R₀) z
    have e2 : (fun i => ((MvPolynomial.aeval y : MvPolynomial (Fin g) W →ₐ[W] W).restrictScalars R₀)
        (z i)) = Sum.elim c (fun k => MvPolynomial.aeval y (G k)) := by
      funext i
      rcases i with i | i
      · simp [z]
      · simp only [z, AlgHom.coe_restrictScalars', Sum.elim_inr]
        exact MvPolynomial.aeval_map_algebraMap W y (G i)
    rw [e2] at e1
    rw [hGe W y hy]
    change nEval _ _ = _
    rw [(H1 (ch.F k) W _).1 (max M₁ M₂), ← e1]
    · simp [MvPolynomial.coe_aeval_eq_eval]
    · rintro (i | i)
      · exact hM₂ _ (le_max_right _ _) i
      · have := hM₁ _ (le_max_left M₁ M₂) i
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at this
        have := hI _ this
        rwa [map_pow] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TeichmullerQuot
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WittQuot

private lemma wS_mul (p : ℕ) [hp : Fact p.Prime] (n : ℕ) : (p : MvPolynomial (Fin n) ℤ) * wS p n =
    (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p := by
  set q : MvPolynomial (Fin n) ℤ := (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p with hq
  have hd : MvPolynomial.C (p : ℤ) ∣ q := by
    rw [MvPolynomial.C_dvd_iff_zmod, hq]
    simp only [map_sub, map_sum, map_pow, MvPolynomial.map_X]
    rw [sum_pow_char, sub_self]
  rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hd
  conv_rhs => rw [q.as_sum]
  change _ * ∑ m ∈ q.support, MvPolynomial.monomial m (q.coeff m / (p : ℤ)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← map_natCast (MvPolynomial.C : ℤ →+* _), MvPolynomial.C_mul_monomial,
    Int.mul_ediv_cancel' (hd m)]

private lemma teich_decomp (p : ℕ) [Fact p.Prime] {K : Type} [CommRing K] [CharP K p]
    [PerfectRing K p] (x : WittVector p K) :
    ∃ y : WittVector p K, x = WittVector.teichmuller p (x.coeff 0) + p * y := by
  have hmem : x - WittVector.teichmuller p (x.coeff 0) ∈
      Ideal.span {(p : WittVector p K) ^ 1} := by
    rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero,
      ← WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [WittVector.teichmuller_coeff_zero]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨w, ?_⟩
  rw [pow_one] at hw
  rw [mul_comm, hw]; abel

theorem teichmuller_quot :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (ϖ : PreTilt O p), ϖ.untilt = (p : O) →
    ∀ (W : Type) [CommRing W] (pr : Ainf.A p O →+* W), Function.Surjective pr →
    RingHom.ker pr = Ideal.span {(p : Ainf.A p O) ^ 2, WittVector.teichmuller p ϖ} →
    (∀ w : W, ∃ c : PreTilt O p, ∃ c' : W, w = pr (WittVector.teichmuller p c) + p * c') ∧
    (∀ (n : ℕ) (a : Fin n → PreTilt O p), ∑ j, pr (WittVector.teichmuller p (a j)) = pr (WittVector.teichmuller p (∑ j, a j)) +
      p * pr (WittVector.teichmuller p (MvPolynomial.eval₂ (Int.castRingHom (PreTilt O p)) (fun j => (frobeniusEquiv (PreTilt O p) p).symm (a j)) (wS p n)))) ∧
    (∀ c : PreTilt O p, WittVector.fontaineTheta O p (WittVector.teichmuller p c) ∈ Ideal.span {(p : O)} → pr (WittVector.teichmuller p c) = 0)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε ϖ hϖ W _ pr hpr hker
  have hp2 : pr ((p : Ainf.A p O) ^ 2) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span (by simp)
  have hϖ0 : pr (WittVector.teichmuller p ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span (by simp)
  refine ⟨fun w => ?_, fun n a => ?_, fun c hc => ?_⟩
  · obtain ⟨x, rfl⟩ := hpr w
    obtain ⟨y, hy⟩ := teich_decomp p x
    refine ⟨x.coeff 0, pr y, ?_⟩
    conv_lhs => rw [hy]
    rw [map_add, map_mul, map_natCast]
  · obtain ⟨w, hw⟩ := ((teichSum p (Fin n) Finset.univ).2 (PreTilt O p) a (wS p n) (wS_mul p n)).1
    have h := congrArg pr hw
    rw [map_sum, map_add, map_add, map_mul, map_mul, hp2, zero_mul, add_zero, map_natCast] at h
    rw [h, MvPolynomial.aeval_def]
    rfl
  · have hK := ((a0 p C v O hv).2.2.1 ϖ hϖ).2.2
    have hm : WittVector.teichmuller p c ∈
        Ideal.span {(p : WittVector p (PreTilt O p)), WittVector.teichmuller p ϖ} := by
      rw [← hK, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hc
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hm
    have h := congrArg (WittVector.constantCoeff (p := p) (R := PreTilt O p)) hxy
    rw [map_add, map_mul, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero, zero_add] at h
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
    rw [← h, map_mul, map_mul, hϖ0, mul_zero]

end GlobalTheory.WittQuot
end

