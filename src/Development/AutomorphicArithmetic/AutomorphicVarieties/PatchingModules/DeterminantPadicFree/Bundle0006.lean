import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanDesc
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem sd_map_ev {F F' : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ}
    {Z : Matrix (Fin n) (Fin n) F} (hZ : Z ∈ Ev F F n a) : Z.map f ∈ Ev F' F' n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  have h0 : Z i j = 0 := (hZ i j).2 e
  rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]

private theorem sd_up {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F)
    (hY : Y ∈ Submodule.span F (Set.range r)) :
    Y.map f ∈ Submodule.span F' (Set.range fun i => (r i).map f) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin n) (Fin n) F).map f = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have : (y + z).map f = y.map f + z.map f := by ext i j; simp
    rw [this]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (c • y).map f = f c • y.map f := by ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hy

private theorem sd_down {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n : ℕ}
    (r : ι → Matrix (Fin n) (Fin n) F) (p : F' →+ F) (hp : ∀ (c : F') (x : F), p (c * f x) = p c * x)
    (Y : Matrix (Fin n) (Fin n) F')
    (hY : Y ∈ Submodule.span F' (Set.range fun i => (r i).map f)) :
    ∀ c : F', (c • Y).map p ∈ Submodule.span F (Set.range r) := by
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    intro c
    have : (c • (r i).map f).map p = p c • r i := by
      ext s t; simp [hp]
    show (c • (r i).map f).map p ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero =>
    intro c
    have : (c • (0 : Matrix (Fin n) (Fin n) F')).map p = 0 := by ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    intro c
    have : (c • (y + z)).map p = (c • y).map p + (c • z).map p := by ext i j; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ (hy c) (hz c)
  | smul d y _ hy =>
    intro c
    rw [smul_smul]; exact hy _

theorem UpperTheory.V.Pa.Det.spanDesc :
    ∀ {F F' ι : Type} [Field F] [Field F'] (f : F →+* F') {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) F), (∀ i, r i ∈ Ev F F n a) → (Submodule.span F (Set.range r) = Ev F F n a ↔ Submodule.span F' (Set.range fun i => (r i).map f) = Ev F' F' n a) := by
  intro F F' ι _ _ f n a r hr
  constructor
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact sd_map_ev f (hr i)
    · intro Z hZ
      have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
      rw [hZ']
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
      · have h1 : (single i j 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a :=
          fun p q => ⟨fun _ => trivial, fun e' => by
            rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
            rintro ⟨rfl, rfl⟩
            exact e' e⟩
        rw [← h] at h1
        have h2 := Submodule.smul_mem _ (Z i j) (sd_up f r _ h1)
        convert h2 using 1
        ext p q
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
        split_ifs <;> simp
      · have : Z i j = 0 := (hZ i j).2 e
        simp [this]
  · intro h
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hr i
    · intro Z hZ
      letI : Algebra F F' := f.toAlgebra
      obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F F')
        (LinearMap.ker_eq_bot.2 f.injective)
      have hp1 : ∀ x : F, p (f x) = x := fun x => LinearMap.congr_fun hp x
      have hp2 : ∀ (c : F') (x : F), p.toAddMonoidHom (c * f x) = p.toAddMonoidHom c * x := by
        intro c x
        have h3 : c * f x = x • c := by rw [mul_comm]; rfl
        show p (c * f x) = p c * x
        rw [h3, map_smul, smul_eq_mul, mul_comm]
      have h1 := sd_map_ev f hZ
      rw [← h] at h1
      have h2 := sd_down f r p.toAddMonoidHom hp2 _ h1 1
      convert h2 using 1
      ext s t
      simp [hp1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SpanInt
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image {A F M N : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M) (y : N)
    (hy : y ∈ Submodule.span F (φ '' T)) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A T, d • y = φ w :=
  _root_.UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image φ T y hy

theorem UpperTheory.V.Pa.Det.spanInt :
    ∀ {K ι : Type} [Field K] {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) (PowerSeries K)) (S : Set ι), Submodule.span (FractionRing (PowerSeries K)) ((fun i => (r i).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) '' S) = Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a → ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ, (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) (r '' S) := by
  intro K ι _ n a r S h Z hZ
  let φ : Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[PowerSeries K]
      Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K)) :=
    (Algebra.linearMap (PowerSeries K) (FractionRing (PowerSeries K))).mapMatrix
  have hφ : ∀ Y, φ Y = Y.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) := fun _ => rfl
  have hinj : Function.Injective φ :=
    Matrix.map_injective (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hmem : φ Z ∈ Submodule.span (FractionRing (PowerSeries K)) (φ '' (r '' S)) := by
    rw [Set.image_image]
    simp only [hφ]
    rw [h]
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
    have : Z i j = 0 := (Submodule.mem_bot _).1 ((hZ i j).2 hij)
    simp [this]
  obtain ⟨d, hd, w, hw, e⟩ := UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image φ _ _ hmem
  rw [← map_smul] at e
  have e' := hinj e
  obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd
    (PowerSeries.X_irreducible (R := K))
  refine ⟨s, ?_⟩
  have : (PowerSeries.X : PowerSeries K) ^ s • Z = (↑u⁻¹ : PowerSeries K) • w := by
    rw [← e', smul_smul, Units.inv_mul_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ hw
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SplitEx
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_injective_roots_in_integral_closure {A L : Type} [CommRing A] [Field L] [Algebra A L] {n : ℕ} (p : Polynomial A)
    (hm : p.Monic) (hn : (p.map (algebraMap A L)).natDegree = n) (hsep : (p.map (algebraMap A L)).Separable)
    (hs : (p.map (algebraMap A L)).Splits) :
    ∃ al : Fin n → integralClosure A L, Function.Injective al ∧
      p.map (algebraMap A (integralClosure A L)) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
  classical
  set pL := p.map (algebraMap A L) with hpL
  have hmL : pL.Monic := hm.map _
  have hroots : pL = (pL.roots.map fun x => Polynomial.X - Polynomial.C x).prod :=
    hs.eq_prod_roots_of_monic hmL
  have hnd : pL.roots.Nodup := Polynomial.nodup_roots hsep
  set s := pL.roots.toFinset with hsdef
  have hcard : s.card = n := by
    rw [hsdef, Multiset.toFinset_card_of_nodup hnd, ← hs.natDegree_eq_card_roots, hn]
  have hint : ∀ x ∈ s, x ∈ integralClosure A L := by
    intro x hx
    rw [hsdef, Multiset.mem_toFinset, Polynomial.mem_roots hmL.ne_zero, Polynomial.IsRoot,
      hpL, Polynomial.eval_map] at hx
    exact ⟨p, hm, hx⟩
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hcard)).symm
  refine ⟨fun b => ⟨(e b : L), hint _ (e b).2⟩, ?_, ?_⟩
  · intro b b' h
    have h2 := congrArg Subtype.val h
    exact e.injective (Subtype.ext h2)
  · apply Polynomial.map_injective (integralClosure A L).val.toRingHom Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod]
    have h1 : ((integralClosure A L).val.toRingHom).comp (algebraMap A (integralClosure A L)) =
        algebraMap A L := by
      ext a
      rfl
    rw [h1]
    change pL = _
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hroots]
    have h3 : ∏ b : Fin n, (Polynomial.X - Polynomial.C ((e b : L))) =
        ∏ x ∈ s, (Polynomial.X - Polynomial.C x) := by
      rw [Equiv.prod_comp e (fun x : s => Polynomial.X - Polynomial.C (x : L))]
      exact Finset.prod_coe_sort s (fun x => Polynomial.X - Polynomial.C x)
    convert h3.symm using 1
    · rw [Finset.prod_eq_multiset_prod, hsdef, Multiset.toFinset_val, hnd.dedup]
    · rfl

theorem UpperTheory.V.Pa.Det.splitEx :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] {q n : ℕ} (P : Fin q → Polynomial (PowerSeries K)), (∀ a, (P a).Monic ∧ (P a).natDegree = n ∧ ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).Separable) → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A') (al : Fin q → Fin n → A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ a, Function.Injective (al a) ∧ (P a).map j = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ K _ _ _ q n P hP
  classical
  have hQ0 : (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => ((hP a).1.map _).ne_zero
  haveI hsepE : Algebra.IsSeparable (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) := by
    rw [← IntermediateField.isSeparable_top,
      ← (isSplittingField_iff_intermediateField.mp
        (inferInstance : Polynomial.IsSplittingField (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).2,
      IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x hx
    have h0 := Polynomial.aeval_eq_zero_of_mem_rootSet hx
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨a, _, ha⟩ := h0
    exact (hP a).2.2.of_dvd (minpoly.dvd (FractionRing (PowerSeries K)) x ha)
  haveI hcA : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hfinA : Finite (IsLocalRing.ResidueField (PowerSeries K)) :=
    Finite.of_equiv K (PowerSeries.residueFieldOfPowerSeries).symm.toEquiv
  set_option synthInstance.maxHeartbeats 400000 in
  obtain ⟨hfin, _, _, hdvr, hcB, hloc, hres⟩ :=
    UpperTheory.V.AlgebraTools.integralClosure_complete_dvr (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))
  have hinjAE : Function.Injective (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
    rw [IsScalarTower.algebraMap_eq (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))]
    exact (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).injective.comp (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hj : Function.Injective (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) := by
    intro x y h
    apply hinjAE
    exact congrArg Subtype.val h
  haveI hcharA : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C (R := K)).injective l
  haveI hcharB : CharP ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) l := charP_of_injective_ringHom hj l
  have hal : ∀ a, ∃ al : Fin n → ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), Function.Injective al ∧
      (P a).map (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
    intro a
    have hdeg : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).natDegree = n := by
      rw [(hP a).1.natDegree_map]
      exact (hP a).2.1
    have hmapE : (P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) =
        ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).map (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hsepa : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Separable := by
      rw [hmapE]
      exact (hP a).2.2.map
    have hspl : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Splits := by
      rw [hmapE]
      refine Polynomial.Splits.of_dvd (Polynomial.SplittingField.splits (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))
        (Polynomial.map_ne_zero hQ0) ?_
      exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ a))
    exact exists_injective_roots_in_integral_closure (P a) (hP a).1 hdeg hsepa hspl
  choose al hal1 hal2 using hal
  exact ⟨↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), inferInstance, inferInstance, hdvr, ⟨hcB, hres hfinA, hcharB⟩, algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), al,
    hj, hloc, RingHom.finite_algebraMap.mpr hfin, fun a => ⟨hal1 a, hal2 a⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SubMulAddEpM
section
noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.Det

section Ep

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_ep' {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem sum_eta {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

private theorem epM_mul_epM (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z' = 0 := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta]

private theorem epM_add (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (fun j => Z j + Z' j) = DD.epM Z + DD.epM Z' := by
  ext a b <;> simp [DD.epM]

private theorem epM_zero : DD.epM (fun _ : Fin g => (0 : Matrix (Fin n) (Fin n) X)) = 0 := by
  ext a b <;> simp [DD.epM]

private theorem mul_epM (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    M.map (algebraMap A (DD X g)) * DD.epM Z = DD.epM fun j => M.map (algebraMap A X) * Z j := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

private theorem epM_mul (M : Matrix (Fin n) (Fin n) A) (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * M.map (algebraMap A (DD X g)) = DD.epM fun j => Z j * M.map (algebraMap A X) := by
  ext a b <;> simp [Matrix.mul_apply, DD.epM, sum_a, sum_ep, sum_ep', sum_eta, alg_eq]

private theorem add_mul_sub_epM (Z : Fin g → Matrix (Fin n) (Fin n) X) : (1 + DD.epM Z) * (1 - DD.epM Z) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, epM_mul_epM]; abel

private theorem sub_mul_add_epM (Z : Fin g → Matrix (Fin n) (Fin n) X) : (1 - DD.epM Z) * (1 + DD.epM Z) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, epM_mul_epM]; abel

end Ep

section Rho

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X] [Algebra x.A X]

private theorem ρX_one : x.ρX X 1 = 1 := by
  simp [NP.ρX, mat]

private theorem ρX_mul (g h : F.G₀) : x.ρX X (g * h) = x.ρX X g * x.ρX X h := by
  simp [NP.ρX, mat, Matrix.map_mul]

private theorem w_wi (v : F.Vl) : x.wX X v * x.wiX X v = 1 := by
  rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp

private theorem wi_w (v : F.Vl) : x.wiX X v * x.wX X v = 1 := by
  rw [NP.wX, NP.wiX, ← Matrix.map_mul]; simp

variable {x} (k : Kap x)

private theorem coc (j) (g h : F.G₀) : k.κ j (g * h) = k.κ j g + mat x.ρ g * k.κ j h * mat x.ρ g⁻¹ := by
  have := (k.mem j).2.2.1 g h
  simpa [NP.ρX] using this

private theorem κ_one (j) : k.κ j 1 = 0 := by
  have := coc k j 1 1
  simpa [mat] using this

private theorem ρ1_one : k.ρ1 X 1 = 1 := by
  simp [Kap.ρ1, κ_one, ρX_one, epM_zero]

private theorem ρ1_mul (g h : F.G₀) : k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h := by
  have e : (DD.epM fun j => (k.κ j (g * h)).map (algebraMap x.A X)) =
      (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) +
        x.ρX (DD X k.g) g * (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) * x.ρX (DD X k.g) g⁻¹ := by
    rw [NP.ρX, NP.ρX, mul_epM, epM_mul, ← epM_add]
    congr 1
    funext j
    rw [coc, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul]
  have i : x.ρX (DD X k.g) g⁻¹ * x.ρX (DD X k.g) g = 1 := by rw [← ρX_mul, inv_mul_cancel, ρX_one]
  have z : (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * x.ρX (DD X k.g) g *
      (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) = 0 := by
    rw [NP.ρX, epM_mul, epM_mul_epM]
  simp only [Kap.ρ1]
  rw [e, ρX_mul]
  generalize (DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) = P at *
  generalize (DD.epM fun j => (k.κ j h).map (algebraMap x.A X)) = Q at *
  generalize x.ρX (DD X k.g) g⁻¹ = s at *
  generalize x.ρX (DD X k.g) g = r at *
  generalize x.ρX (DD X k.g) h = r' at *
  calc (1 + (P + r * Q * s)) * (r * r') = r * r' + P * r * r' + r * Q * (s * r) * r' := by noncomm_ring
    _ = r * r' + P * r * r' + r * Q * r' + P * r * Q * r' := by rw [i, z]; noncomm_ring
    _ = _ := by noncomm_ring

end Rho

end UpperTheory.V.Pa.Det

open IsLocalRing UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.rho1Hom :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], k.ρ1 X 1 = 1 ∧ (∀ g h, k.ρ1 X (g * h) = k.ρ1 X g * k.ρ1 X h) ∧ (∀ g, k.ρ1 X g⁻¹ = x.ρX (DD X k.g) g⁻¹ * (1 - DD.epM fun j => (k.κ j g).map (algebraMap x.A X))) ∧ ∀ v, k.w1 X v * k.wi1 X v = 1 ∧ k.wi1 X v * k.w1 X v = 1 := by
  intro l _ F n x k X _ _
  refine ⟨ρ1_one X k, ρ1_mul X k, fun g => ?_, fun v => ⟨?_, ?_⟩⟩
  · have h1 : k.ρ1 X g * k.ρ1 X g⁻¹ = 1 := by rw [← ρ1_mul, mul_inv_cancel, ρ1_one]
    have h2 : x.ρX (DD X k.g) g⁻¹ * (1 - DD.epM fun j => (k.κ j g).map (algebraMap x.A X)) * k.ρ1 X g = 1 := by
      rw [Kap.ρ1, mul_assoc, ← mul_assoc (1 - _), sub_mul_add_epM, one_mul, ← ρX_mul, inv_mul_cancel, ρX_one]
    exact (left_inv_eq_right_inv h2 h1).symm
  · rw [Kap.w1, Kap.wi1, mul_assoc, ← mul_assoc (x.wX _ v), w_wi, one_mul, sub_mul_add_epM]
  · rw [Kap.w1, Kap.wi1, mul_assoc, ← mul_assoc (1 + _), add_mul_sub_epM, one_mul, wi_w]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TypeIDisc
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

open UpperTheory.V.CA in
private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one, h] at h1
  have h2 := (d_toDet (GDet.ofRep ρ) (MonoidAlgebra.single g 1)).2.2.1
  rw [d_toDet_ofRep.1, (d_ofRep _ _ _).2.2.1 hn] at h2
  have h3 : GDet.repAlg ρ K (MonoidAlgebra.single g 1) = ρ g := by
    ext i j; simp [GDet.repAlg]
  rw [h3] at h2
  exact h1.symm.trans h2.symm

private theorem span_top {n : ℕ} {A L : Type} [CommRing A] [Field L] [Algebra A L] (t : A)
    (ht : algebraMap A L t ≠ 0) (S : Set (Matrix (Fin n) (Fin n) A))
    (hS : ∀ Z, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A S) :
    Submodule.span L ((algebraMap A L).mapMatrix '' S) = ⊤ := by
  have h1 : ∀ Z ∈ Submodule.span A S, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have : (algebraMap A L).mapMatrix (c • y) = algebraMap A L c • (algebraMap A L).mapMatrix y := by
        ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ hy
  have h2 : ∀ Z : Matrix (Fin n) (Fin n) A, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z
    obtain ⟨s, hs⟩ := hS Z
    have h := h1 _ hs
    have e : (algebraMap A L).mapMatrix (t ^ s • Z) = algebraMap A L t ^ s • (algebraMap A L).mapMatrix Z := by
      ext i j; simp
    rw [e] at h
    exact (Submodule.smul_mem_iff _ (pow_ne_zero s ht)).1 h
  rw [eq_top_iff]
  intro Z _
  rw [Matrix.matrix_eq_sum_single Z]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (Z i j) = Z i j • (algebraMap A L).mapMatrix (Matrix.single i j (1 : A)) := by
    ext a b
    by_cases h : i = a ∧ j = b <;> simp [Matrix.single_apply, h]
  rw [e]
  exact Submodule.smul_mem _ _ (h2 _)

theorem UpperTheory.V.Pa.Det.typeIDisc :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {R : Type} [CommRing R] (D : GDet n R F.G₀) (f : R →+* x.A), x.a = n → D.map f = GDet.ofRep (mat x.ρ) → ∀ q : Ideal R, q ≤ RingHom.ker f → DiscSt D q := by
  intro l _ F n x R _ D f ha hD q hq
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  have ht : algebraMap x.A (FractionRing x.A) x.t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective x.A (FractionRing x.A))).2 PowerSeries.X_ne_zero
  have hsp := span_top (L := FractionRing x.A) x.t ht (mat x.ρ '' (F.G' : Set F.G₀)) fun Z =>
    x.span Z fun i j => ⟨fun _ => Submodule.mem_top, fun h => (h (by simp [ha])).elim⟩
  obtain ⟨y, hy, hdet⟩ := (UpperTheory.V.CA.g_gram _ _ _).1 hsp
  have hy' : ∀ a, ∃ g, (algebraMap x.A (FractionRing x.A)).mapMatrix (mat x.ρ g) = y a := fun a => by
    obtain ⟨_, ⟨g, -, rfl⟩, h⟩ := hy a
    exact ⟨g, h⟩
  choose g hg using hy'
  refine ⟨fun i => g (finProdFinEquiv.symm i), fun i => g (finProdFinEquiv.symm i), fun hm => hdet ?_⟩
  have h0 := congrArg (algebraMap x.A (FractionRing x.A)) (RingHom.mem_ker.1 (hq hm))
  rw [map_zero, ← RingHom.comp_apply, RingHom.map_det] at h0
  rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← h0]
  congr 1
  ext a b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, tr_of_map hn D f _ hD,
    Matrix.submatrix_apply, Matrix.of_apply, ← hg, ← hg, ← map_mul, ← map_mul, RingHom.mapMatrix_apply]
  exact (AddMonoidHom.map_trace (algebraMap x.A (FractionRing x.A)) _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ZlUniq
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem zlUniq_val (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hl : (l : R) = 0) (a : ℤ_[l]) : f a = ((PadicInt.toZMod a).val : R) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
    (PadicInt.maximalIdeal_eq_span_p (p := l) ▸ PadicInt.sub_zmodRepr_mem a)
  rw [PadicInt.val_toZMod_eq_zmodRepr]
  have h := congrArg f hc
  rw [map_mul, map_natCast, hl, mul_zero, map_sub, map_natCast, eq_comm, sub_eq_zero] at h
  exact h

theorem UpperTheory.V.Pa.Det.zlUniq :
    ∀ (l : ℕ) [Fact l.Prime], (∀ {K : Type} [Field K] [Finite K] (_ : ℤ_[l] →+* K), CharP K l) ∧ ∀ {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R), (l : R) = 0 → f = f' ∧ ∀ a, f a = ((PadicInt.toZMod a).val : R) := by
  intro l _
  refine ⟨fun {K} _ _ f => ?_, fun {R} _ f f' hl => ⟨?_, zlUniq_val l f hl⟩⟩
  · obtain ⟨p, hchar⟩ := CharP.exists K
    have hp : p.Prime := CharP.char_is_prime K p
    have hpl : p = l := by
      by_contra hne
      have hunit : IsUnit (p : ℤ_[l]) := by
        by_contra hnu
        have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
          rw [Int.cast_natCast]
          exact PadicInt.mem_nonunits.mp hnu
        rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
        exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
      have h := hunit.map f
      rw [map_natCast, CharP.cast_eq_zero] at h
      exact not_isUnit_zero h
    subst hpl
    exact hchar
  · ext a
    rw [zlUniq_val l f hl, zlUniq_val l f' hl]
end

