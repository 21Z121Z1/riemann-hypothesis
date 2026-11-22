import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.ExistsIsRegularOfListEqMaximalIdeal
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Nakayama
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0074
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Data.Finset.NoncommProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

private theorem chiS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y) = (D.chiS S y).map (f : S →+* T) := by
  have h := D.nat (Polynomial S) (Polynomial T) (Polynomial.mapAlgHom f) (Polynomial.X ⊗ₜ 1 -
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y)
  refine Eq.trans ?_ h
  unfold Det.chiS
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y with
    | zero => simp
    | tmul s x => simp
    | add a b ha hb => simp only [map_add, ha, hb]

private theorem F_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    Polynomial.aeval (Algebra.TensorProduct.map f (AlgHom.id A E) y)
      (D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y)) =
      Algebra.TensorProduct.map f (AlgHom.id A E) (Polynomial.aeval y (D.chiS S y)) := by
  rw [chiS_map]
  generalize D.chiS S y = p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
  | monomial k a =>
    simp [Polynomial.aeval_monomial, Algebra.TensorProduct.algebraMap_apply]

private theorem expand {ι : Type} (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S)
    (N : Set E) (w : MvPolynomial ι A ⊗[A] E)
    (h : ∀ α, TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) ∈ N) :
    Algebra.TensorProduct.map f (AlgHom.id A E) w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) := by
  classical
  have hw : ∃ s : Finset (ι →₀ ℕ), ∀ t, s ⊆ t → w = ∑ α ∈ t, (MvPolynomial.monomial α (1 : A)) ⊗ₜ[A]
      TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) := by
    clear h
    induction w with
    | zero => exact ⟨∅, by simp⟩
    | add a b ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s ∪ s', fun t ht => ?_⟩
      simp only [map_add, tmul_add, Finset.sum_add_distrib]
      rw [← hs t (Finset.subset_union_left.trans ht), ← hs' t (Finset.subset_union_right.trans ht)]
    | tmul p z =>
      refine ⟨p.support, fun t ht => ?_⟩
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, MvPolynomial.lcoeff_apply, ← smul_tmul,
        ← sum_tmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      congr 1
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_subset ht fun α _ hα => ?_
      rw [MvPolynomial.notMem_support_iff.1 hα, map_zero]
  obtain ⟨s, hs⟩ := hw
  rw [hs s le_rfl, map_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [Algebra.TensorProduct.map_tmul, ← mul_one (f _), ← smul_eq_mul, ← smul_tmul']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h α, rfl⟩)

private theorem part1 (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    Polynomial.aeval y (D.chiS S y) ∈
      Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) := by
  obtain ⟨k, s, x, rfl⟩ := TensorProduct.exists_sum_tmul_eq y
  have : ∑ j, s j ⊗ₜ[A] x j =
      Algebra.TensorProduct.map (MvPolynomial.aeval s) (AlgHom.id A E) (Det.gen (A := A) x) := by
    simp [Det.gen, map_sum]
  rw [this, F_map]
  exact expand S _ _ _ fun α => TwoSidedIdeal.subset_span ⟨k, x, α, rfl⟩

private theorem rT_mem (P S : Type) [CommRing P] [Algebra A P] [CommRing S] [Algebra A S] (g : P →ₗ[A] S)
    (N : Set E) (w : P ⊗[A] E) (h : w ∈ Submodule.span P ((fun z : E => (1 : P) ⊗ₜ[A] z) '' N)) :
    g.rTensor E w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) := by
  suffices H : ∀ p : P, g.rTensor E (p • w) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) by
    simpa using H 1
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    intro p
    rw [smul_tmul', LinearMap.rTensor_tmul, ← mul_one (g _), ← smul_eq_mul, ← smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hz, rfl⟩)
  | zero => intro p; simp
  | add x y _ _ hx hy => intro p; rw [smul_add, map_add]; exact add_mem (hx p) (hy p)
  | smul a x _ hx => intro p; rw [smul_smul]; exact hx _

private theorem chElt_bc (S : Type) [CommRing S] [Algebra A S] {k : ℕ} (x : Fin k → S ⊗[A] E) (α : Fin k →₀ ℕ) :
    (D.baseChange S).chElt x α = ((MvPolynomial.lcoeff S α).restrictScalars A).rTensor E
      (Polynomial.aeval (Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen x))
        (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen x)))) := by
  unfold Det.chElt
  generalize Det.gen (A := S) x = y
  have h1 : (D.baseChange S).chiS (MvPolynomial (Fin k) S) y =
      D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y) := by
    unfold Det.chiS
    rw [(d_bc D S).1]
    congr 1
    rw [map_sub]
    congr 1
    · rw [Algebra.TensorProduct.one_def, Det.cancel_tmul]; simp
    · induction y with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul s y =>
        induction y with
        | zero => simp
        | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
        | tmul b z => simp [Det.cancel_tmul]
  rw [h1, Polynomial.aeval_algHom_apply]
  generalize Polynomial.aeval y (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y)) = w
  induction w with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s y =>
    induction y with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | tmul b z =>
      rw [Det.cancel_tmul, mul_comm]
      simp [smul_tmul', MvPolynomial.coeff_C_mul, mul_comm b]

private theorem chElt_one (S : Type) [CommRing S] [Algebra A S] {k : ℕ} (x : Fin k → E) (α : Fin k →₀ ℕ) :
    (D.baseChange S).chElt (fun i => (1 : S) ⊗ₜ[A] x i) α = (1 : S) ⊗ₜ[A] D.chElt x α := by
  rw [chElt_bc]
  have : Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen fun i => (1 : S) ⊗ₜ[A] x i) =
      Algebra.TensorProduct.map (MvPolynomial.mapAlgHom (Algebra.ofId A S)) (AlgHom.id A E)
        (Det.gen (A := A) x) := by
    simp [Det.gen, map_sum, Det.cancel_tmul]
  rw [this, F_map]
  unfold Det.chElt
  generalize Polynomial.aeval (Det.gen (A := A) x) (D.chiS (MvPolynomial (Fin k) A) (Det.gen x)) = w
  induction w with
  | zero => simp
  | add a b ha hb => simp only [map_add, tmul_add, ha, hb]
  | tmul s y =>
    simp [MvPolynomial.coeff_map, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_tmul]

private theorem span_mul (S : Type) [CommRing S] [Algebra A S] (I : TwoSidedIdeal E) (w : S ⊗[A] E)
    (h : w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E))) (u : S ⊗[A] E) :
    u * w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) ∧
    w * u ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    induction u with
    | zero => simp
    | add a b ha hb => rw [add_mul, mul_add]; exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
    | tmul s e =>
      have key : ∀ t ∈ I, s ⊗ₜ[A] t ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) := by
        intro t ht
        rw [← mul_one s, ← smul_eq_mul, ← smul_tmul']
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ht, rfl⟩)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact ⟨key _ (I.mul_mem_left _ _ hz), key _ (I.mul_mem_right _ _ hz)⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, mul_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    rw [mul_smul_comm, smul_mul_assoc]
    exact ⟨Submodule.smul_mem _ _ hx.1, Submodule.smul_mem _ _ hx.2⟩

private theorem part2 (S : Type) [CommRing S] [Algebra A S] :
    ((D.baseChange S).CH : Set (S ⊗[A] E)) =
      Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) := by
  ext w
  simp only [SetLike.mem_coe]
  constructor
  · intro h
    unfold Det.CH at h
    induction h using TwoSidedIdeal.span_induction with
    | mem x hx =>
      obtain ⟨k, x, α, rfl⟩ := hx
      rw [chElt_bc]
      exact rT_mem _ _ _ _ _ (part1 D _ _)
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | left_absorb a x _ hx => exact (span_mul S _ _ hx a).1
    | right_absorb b x _ hx => exact (span_mul S _ _ hx b).2
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      change z ∈ TwoSidedIdeal.span _ at hz
      induction hz using TwoSidedIdeal.span_induction with
      | mem x hx =>
        obtain ⟨k, x, α, rfl⟩ := hx
        exact TwoSidedIdeal.subset_span ⟨k, _, α, (chElt_one D S x α).symm⟩
      | zero => simp
      | add x y _ _ hx hy => simp only [tmul_add]; exact add_mem hx hy
      | neg x _ hx => simp only [tmul_neg]; exact neg_mem hx
      | left_absorb a x _ hx =>
        have := TwoSidedIdeal.mul_mem_left _ ((1 : S) ⊗ₜ[A] a) _ hx
        simpa using this
      | right_absorb b x _ hx =>
        have := TwoSidedIdeal.mul_mem_right _ _ ((1 : S) ⊗ₜ[A] b) hx
        simpa using this
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx

end

theorem UpperTheory.V.CA.d_chS :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (S : Type) [CommRing S] [Algebra A S], (∀ y : S ⊗[A] E, Polynomial.aeval y (D.chiS S y) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E))) ∧ ((D.baseChange S).CH : Set (S ⊗[A] E)) = Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) ∧ (D.IsCH → (D.baseChange S).IsCH ∧ ∀ x : E, Polynomial.aeval x (D.chi x) = 0) := by
  intro n A E _ _ _ D S _ _
  refine ⟨part1 D S, part2 D S, fun h => ?_⟩
  have hb : ∀ (T : Type) [CommRing T] [Algebra A T],
      Submodule.span T ((fun z : E => (1 : T) ⊗ₜ[A] z) '' (D.CH : Set E)) = ⊥ := by
    intro T _ _
    rw [Submodule.span_eq_bot]
    rintro _ ⟨z, hz, rfl⟩
    rw [show D.CH = ⊥ from h] at hz
    have : z = 0 := by simpa using hz
    simp [this]
  refine ⟨?_, fun x => ?_⟩
  · refine eq_bot_iff.2 fun w hw => ?_
    have : w ∈ ((D.baseChange S).CH : Set (S ⊗[A] E)) := hw
    rw [part2, hb] at this
    simpa using this
  · have h1 := part1 D A (1 ⊗ₜ x)
    rw [hb, Submodule.mem_bot] at h1
    have h2 : D.chiS A (1 ⊗ₜ x) = D.chi x := by simp [Det.chiS, Det.chi]
    rw [h2] at h1
    have h3 := congrArg (Algebra.TensorProduct.lid A E) h1
    rw [← Polynomial.aeval_algHom_apply] at h3
    simpa using h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cm_of_regular (A : Type) [CommRing A] [IsRegularLocalRing A] : ReciprocityTheory.CA.IsCM A := by
  obtain ⟨xs, hspan, hlen, hreg⟩ :=
    PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal A
  refine ⟨inferInstance, xs.length, hlen.symm, xs, rfl, fun r hr => ?_, hreg⟩
  rw [← hspan]
  exact Ideal.subset_span hr

theorem UpperTheory.V.CA.cl_cm :
    (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (d : ℕ), IsCM (MvPowerSeries (Fin d) O) ∧ ringKrullDim (MvPowerSeries (Fin d) O) = (d + 1 : ℕ)) ∧ ∀ (k : Type) [Field k] (d : ℕ), IsCM (MvPowerSeries (Fin d) k) ∧ ringKrullDim (MvPowerSeries (Fin d) k) = d := by
  refine ⟨fun O _ _ _ _ d => ⟨?_, ?_⟩, fun k _ d => ⟨?_, ?_⟩⟩
  · haveI : IsRegularLocalRing (MvPowerSeries (Fin d) O) :=
      GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O (Fin d)
    exact cm_of_regular _
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
    push_cast
    rfl
  · haveI : IsRegularLocalRing (MvPowerSeries (Fin d) k) :=
      GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin d)
    exact cm_of_regular _
  · rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplUniq
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cu_uniq {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (F G : R →+* T)
    (e : F.comp (algebraMap C R) = G.comp (algebraMap C R))
    (hF : maximalIdeal R ≤ J.comap F) (hG : maximalIdeal R ≤ J.comap G) : F = G := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' J
  intro n r
  obtain ⟨c, hc⟩ := h.dense n r
  have h1 : F (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow F n (Ideal.pow_right_mono hF n hc)
  have h2 : G (r - algebraMap C R c) ∈ J ^ n :=
    Ideal.le_comap_pow G n (Ideal.pow_right_mono hG n hc)
  have h3 : F (algebraMap C R c) = G (algebraMap C R c) := RingHom.congr_fun e c
  rw [Ideal.Quotient.eq]
  have := sub_mem h1 h2
  rw [map_sub, map_sub, h3] at this
  simpa using this

private theorem cu_ex {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T)
    (hf : x ≤ J.comap f) :
    ∃ F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F :=
  _root_.UpperTheory.Reformulated.B.LevelOfCongruence.cu_ex h J f hf

private theorem cu_le {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x ≤ (maximalIdeal R).comap (algebraMap C R) := by
  have := h.comap_pow 1
  rw [pow_one, pow_one] at this
  exact this.ge

private theorem cu_map {C R : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R] {x : Ideal C}
    (h : IsCplAt x R) : x.map (algebraMap C R) = maximalIdeal R := by
  haveI := h.noeth
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 (cu_le h)) ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (IsNoetherian.noetherian _)
    (maximalIdeal_le_jacobson _) fun r hr => ?_
  obtain ⟨c, hc⟩ := h.dense 2 r
  have h1 : algebraMap C R c ∈ maximalIdeal R := by
    have := sub_mem hr (Ideal.pow_le_self two_ne_zero hc)
    simpa using this
  have h2 : c ∈ x := by
    have := h.comap_pow 1
    rw [pow_one, pow_one] at this
    rw [← this]; exact h1
  have h3 : r = algebraMap C R c + (r - algebraMap C R c) := by ring
  rw [h3]
  refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h2) ?_
  rw [smul_eq_mul, ← pow_two]
  exact hc

private theorem cu_equiv {C R S : Type} [CommRing C] [CommRing R] [Algebra C R] [IsLocalRing R]
    [CommRing S] [Algebra C S] [IsLocalRing S] {x : Ideal C}
    (h : IsCplAt x R) (h' : IsCplAt x S) : Nonempty (R ≃ₐ[C] S) := by
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨F, hF1, hF2⟩ := cu_ex h (maximalIdeal S) (algebraMap C S) (cu_le h')
  obtain ⟨G, hG1, hG2⟩ := cu_ex h' (maximalIdeal R) (algebraMap C R) (cu_le h)
  have e1 : G.comp F = RingHom.id R :=
    cu_uniq h (maximalIdeal R) _ _ (by rw [RingHom.comp_assoc, hF1, hG1, RingHom.id_comp])
      (fun r hr => hG2 (hF2 hr)) (fun r hr => hr)
  have e2 : F.comp G = RingHom.id S :=
    cu_uniq h' (maximalIdeal S) _ _ (by rw [RingHom.comp_assoc, hG1, hF1, RingHom.id_comp])
      (fun r hr => hF2 (hG2 hr)) (fun r hr => hr)
  exact ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom F G e2 e1) fun c => RingHom.congr_fun hF1 c⟩

theorem UpperTheory.V.CA.cpl_uniq :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ (T : Type) [CommRing T] (J : Ideal T) [IsAdicComplete J T] (f : C →+* T), x ≤ J.comap f → ∃! F : R →+* T, F.comp (algebraMap C R) = f ∧ maximalIdeal R ≤ J.comap F) ∧ Nonempty (R ≃ₐ[C] Cpl x) ∧ x.map (algebraMap C R) = maximalIdeal R := by
  intro C R _ _ _ _ _ x _ h
  refine ⟨fun T _ J _ f hf => ?_, ?_, cu_map h⟩
  · obtain ⟨F, hF⟩ := cu_ex h J f hf
    exact ⟨F, hF, fun G hG => cu_uniq h J G F (hG.1.trans hF.1.symm) hG.2 hF.2⟩
  · obtain ⟨_, h'⟩ := cpl_is C x
    exact cu_equiv h h'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DProd
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, Ring (E i)]
  [∀ i, Algebra A (E i)]

private theorem UpperTheory.V.CA.prod_piRight_apply (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)) (i : ι) :
    Algebra.TensorProduct.piRight A S S E y i =
      Algebra.TensorProduct.map (AlgHom.id S S) (Pi.evalAlgHom A E i) y := by
  induction y with
  | zero => simp
  | tmul s y => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

private theorem UpperTheory.V.CA.prod_piRight_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T]
    (f : S →ₐ[A] T) (y : S ⊗[A] (∀ i, E i)) (i : ι) :
    Algebra.TensorProduct.piRight A T T E (Algebra.TensorProduct.map f (AlgHom.id A _) y) i =
      Algebra.TensorProduct.map f (AlgHom.id A _) (Algebra.TensorProduct.piRight A S S E y i) := by
  induction y with
  | zero => simp
  | tmul s y => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

private theorem UpperTheory.V.CA.prod_single_smul (S : Type) [CommRing S] [Algebra A S] (b : S) (i : ι) :
    (Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i (b • (1 : S ⊗[A] E i))) =
      1 + (b - 1) ⊗ₜ[A] (Pi.single i 1 : ∀ i, E i) := by
  rw [AlgEquiv.symm_apply_eq]
  funext j
  rw [map_add, map_one, Pi.add_apply, Pi.one_apply, Algebra.TensorProduct.piRight_tmul]
  by_cases h : j = i
  · subst h
    simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      ← TensorProduct.add_tmul, add_sub_cancel]
  · simp [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h]

private noncomputable def UpperTheory.V.CA.prodFactor (D : Det n A (∀ i, E i)) (i : ι) (r : ℕ)
    (hr : D.D A[X] (1 + X ⊗ₜ (Pi.single i 1 : ∀ i, E i)) = (1 + X) ^ r) : Det r A (E i) where
  D S _ _ := (D.D S).comp ((Algebra.TensorProduct.piRight A S S E).symm.toAlgHom.toMonoidHom.comp
    (MonoidHom.mulSingle (fun j => S ⊗[A] E j) i))
  nat S T _ _ _ _ f x := by
    change D.D T ((Algebra.TensorProduct.piRight A T T E).symm (Pi.mulSingle i _)) =
      f (D.D S ((Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i x)))
    rw [← D.nat]
    congr 1
    rw [AlgEquiv.symm_apply_eq]
    funext j
    rw [prod_piRight_map, AlgEquiv.apply_symm_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  homog S _ _ b x := by
    have h1 : b • x = (b • (1 : S ⊗[A] E i)) * x := by rw [smul_mul_assoc, one_mul]
    rw [h1, map_mul]
    congr 1
    change D.D S ((Algebra.TensorProduct.piRight A S S E).symm (Pi.mulSingle i _)) = _
    rw [prod_single_smul]
    have h2 := D.nat A[X] S (Polynomial.aeval (b - 1)) (1 + X ⊗ₜ (Pi.single i 1 : ∀ i, E i))
    rw [hr] at h2
    simpa using h2

end

theorem UpperTheory.V.CA.d_prod :
    ∀ {n : ℕ} {A ι : Type} [CommRing A] [IsLocalRing A] [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, Ring (E i)] [∀ i, Algebra A (E i)] (D : Det n A (∀ i, E i)), ∃ (m : ι → ℕ) (Ds : ∀ i, Det (m i) A (E i)), ∑ i, m i = n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)), D.D S y = ∏ i, ((Ds i).pull (Pi.evalAlgHom A E i)).D S y := by
  intro n A ι _ _ _ _ E _ _ D
  have hid : ∀ i, IsIdempotentElem (Pi.single i 1 : ∀ i, E i) := by
    intro i
    show _ * _ = _
    rw [← Pi.single_mul, one_mul]
  choose r hrle hr using fun i => d_idem_rank D (Pi.single i 1 : ∀ i, E i) (hid i)
  have hpull : ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)) (i : ι),
      ((prodFactor E D i (r i) (hr i)).pull (Pi.evalAlgHom A E i)).D S y
        = D.D S ((Algebra.TensorProduct.piRight A S S E).symm
            (Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i))) := by
    intro S _ _ y i
    rw [prod_piRight_apply]
    rfl
  have hprod : ∀ (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] (∀ i, E i)),
      D.D S y = ∏ i, ((prodFactor E D i (r i) (hr i)).pull (Pi.evalAlgHom A E i)).D S y := by
    intro S _ _ y
    simp only [hpull]
    let g : (∀ j, S ⊗[A] E j) →* S :=
      (D.D S).comp (Algebra.TensorProduct.piRight A S S E).symm.toAlgHom.toMonoidHom
    have hg : ∀ x, g x = D.D S ((Algebra.TensorProduct.piRight A S S E).symm x) := fun x => rfl
    calc D.D S y = g (Algebra.TensorProduct.piRight A S S E y) := by
          rw [hg, AlgEquiv.symm_apply_apply]
      _ = g (Finset.univ.noncommProd
            (fun i => Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i))
            fun i _ j _ _ => Pi.mulSingle_apply_commute _ i j) := by
          rw [Finset.noncommProd_mulSingle]
      _ = ∏ i, g (Pi.mulSingle i (Algebra.TensorProduct.piRight A S S E y i)) :=
          (Finset.map_noncommProd _ _ _ g).trans (Finset.noncommProd_eq_prod _ _)
      _ = _ := by simp only [hg]
  refine ⟨r, fun i => prodFactor E D i (r i) (hr i), ?_, hprod⟩
  have h := hprod A[X] ((X : A[X]) • 1)
  simp only [Det.homog, map_one, mul_one] at h
  rw [Finset.prod_pow_eq_pow_sum] at h
  have h' := congrArg Polynomial.natDegree h
  simpa [Polynomial.natDegree_X_pow] using h'.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UPoly
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem aeval_mul_homog {n : ℕ} {A G S : Type} [CommRing A] [CommRing S] [Algebra A S]
    {P : MvPolynomial G A} (hP : P.IsHomogeneous n) (b : S) (x : G → S) :
    MvPolynomial.aeval (fun g => b * x g) P = b ^ n * MvPolynomial.aeval x P :=
  _root_.UpperTheory.Reformulated.B.Qk4.aeval_mul_homog hP b x

theorem UpperTheory.V.CA.u_poly :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [Fintype G] [DecidableEq G] (P : MvPolynomial G A), P.IsHomogeneous n → MvPolynomial.eval (Pi.single 1 1) P = 1 → MvPolynomial.aeval (fun g : G => ∑ a : G, (MvPolynomial.X (Sum.inl a) * MvPolynomial.X (Sum.inr (a⁻¹ * g)) : MvPolynomial (G ⊕ G) A)) P = MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr P → ∃ D : GDet n A G, ∀ (S : Type) [CommRing S] [Algebra A S] (y : MonoidAlgebra S G), D.D S y = MvPolynomial.aeval (fun g => y.coeff g) P := by
  intro n A G _ _ _ _ P hP h1 hm
  refine ⟨⟨fun S _ _ => ⟨⟨fun y => MvPolynomial.aeval (fun g => y.coeff g) P, ?_⟩, ?_⟩, ?_, ?_⟩, fun S _ _ y => rfl⟩
  · have h : (fun g => (1 : MonoidAlgebra S G).coeff g) =
        fun g => Algebra.ofId A S ((Pi.single 1 1 : G → A) g) := by
      funext g
      by_cases hg : g = 1
      · subst hg; simp [MonoidAlgebra.one_def]
      · simp [MonoidAlgebra.one_def, hg, Ne.symm hg]
    rw [h, ← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval, h1, map_one]
  · intro x y
    have h := congrArg (MvPolynomial.aeval (R := A) (Sum.elim (fun g => x.coeff g) (fun g => y.coeff g))) hm
    rw [map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename, MvPolynomial.comp_aeval_apply] at h
    refine Eq.trans ?_ h
    change MvPolynomial.aeval _ P = _
    congr 2
    funext g
    simp only [map_sum, map_mul, MvPolynomial.aeval_X, Sum.elim_inl, Sum.elim_inr]
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
    simp
  · intro S T _ _ _ _ f x
    change MvPolynomial.aeval _ P = f (MvPolynomial.aeval _ P)
    rw [MvPolynomial.comp_aeval_apply]
    congr 2
  · intro S _ _ b x
    change MvPolynomial.aeval _ P = b ^ n * (MvPolynomial.aeval _ P)
    rw [← aeval_mul_homog hP]
    congr 2
end

