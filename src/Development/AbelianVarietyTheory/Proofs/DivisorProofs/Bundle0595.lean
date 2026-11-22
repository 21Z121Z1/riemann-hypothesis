import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionComponentsPreimageOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem sectionComponents_preimage_of_isPullback :
    ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X)
      (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ →
      e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e →
      q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} =
        {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by
  intro X S X' S' f f' p q e e' hf hq he he' hee
  ext x'
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hfq : f (q x') = p (f' x') := by
    rw [← Scheme.Hom.comp_apply, hq.w, Scheme.Hom.comp_apply]
  rw [hfq]

  have hY := IsPullback.of_hasPullback f (S.fromSpecResidueField (p (f' x')))
  have hY' := IsPullback.of_hasPullback f' (S'.fromSpecResidueField (f' x'))
  have hsq : S'.fromSpecResidueField (f' x') ≫ p =
      Spec.map (p.residueFieldMap (f' x')) ≫ S.fromSpecResidueField (p (f' x')) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField p (f' x')).symm

  let eY : Spec (S.residueField (p (f' x'))) ⟶ pullback f (S.fromSpecResidueField (p (f' x'))) :=
    pullback.lift (S.fromSpecResidueField (p (f' x')) ≫ e) (𝟙 _) (by simp [he])
  let eY' : Spec (S'.residueField (f' x')) ⟶ pullback f' (S'.fromSpecResidueField (f' x')) :=
    pullback.lift (S'.fromSpecResidueField (f' x') ≫ e') (𝟙 _) (by simp [he'])

  let r : pullback f' (S'.fromSpecResidueField (f' x')) ⟶
      pullback f (S.fromSpecResidueField (p (f' x'))) :=
    pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _ ≫ Spec.map (p.residueFieldMap (f' x')))
      (by simp only [Category.assoc]; rw [hq.w, ← Category.assoc, pullback.condition, Category.assoc, hsq])
  have hbig := hY'.paste_horiz hq
  have hr : IsPullback r (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (p.residueFieldMap (f' x'))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hY
    have h1 : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
    rw [h1, ← hsq]
    exact hbig
  have hsec : eY ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hsec' : eY' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hcomm : eY' ≫ r = Spec.map (p.residueFieldMap (f' x')) ≫ eY := by
    apply pullback.hom_ext
    · simp only [r, eY, eY', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [hee, reassoc_of% hsq]
    · simp only [r, eY, eY', Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]
  have hsm : Smooth (pullback.snd f (S.fromSpecResidueField (p (f' x')))) := inferInstance
  have key := GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt (S.residueField (p (f' x'))) (S'.residueField (f' x')) _ _
    (pullback.snd _ _) (pullback.snd _ _) (Spec.map (p.residueFieldMap (f' x'))) r eY eY'
    hsm hr hsec hsec' hcomm

  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f') (g := S'.fromSpecResidueField (f' x')) x' (IsLocalRing.closedPoint _)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have hy₀ : pullback.fst f (S.fromSpecResidueField (p (f' x'))) (eY (IsLocalRing.closedPoint _)) =
      e (p (f' x')) := by
    have h1 : eY ≫ pullback.fst _ _ = S.fromSpecResidueField (p (f' x')) ≫ e := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply eY (pullback.fst _ _) _).symm.trans ?_
    rw [h1]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg e (Scheme.fromSpecResidueField_apply _ _))
  have hy₀' : pullback.fst f' (S'.fromSpecResidueField (f' x')) (eY' (IsLocalRing.closedPoint _)) =
      e' (f' x') := by
    have h1 : eY' ≫ pullback.fst _ _ = S'.fromSpecResidueField (f' x') ≫ e' := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply eY' (pullback.fst _ _) _).symm.trans ?_
    rw [h1]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg e' (Scheme.fromSpecResidueField_apply _ _))
  have hqx : pullback.fst f (S.fromSpecResidueField (p (f' x'))) (r y') = q x' := by
    have h1 : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply r (pullback.fst _ _) _).symm.trans ?_
    rw [h1, Scheme.Hom.comp_apply, hy'1]
  have A := GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X S f e (p (f' x')) _ (pullback.snd _ _) (pullback.fst _ _) _ hY hy₀ (r y')
  have B := GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X' S' f' e' (f' x') _ (pullback.snd _ _) (pullback.fst _ _) _ hY' hy₀' y'
  rw [hqx] at A
  rw [hy'1] at B
  rw [A, B, ← key]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNumBlockSetsMulGammaTwoSidedBounds
section
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem numBlockSetsOfTotalSize_zero {r : ℕ} (b : Fin r → ℕ) : splitDoublingNBlock b 0 = 1 := by
  unfold splitDoublingNBlock
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext J
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (h1 hx)
    have : i ∈ Finset.univ.filter fun i => b i ∈ J := by simp [hx]
    rw [h2] at this
    simp at this
  · rintro rfl
    simp

theorem numBlockSetsOfTotalSize_le_choose {r : ℕ} (b : Fin r → ℕ) (j : ℕ) : splitDoublingNBlock b j ≤ r.choose j := by
  unfold splitDoublingNBlock
  have h : r.choose j = (Finset.powersetCard j (Finset.univ : Finset (Fin r))).card := by simp
  rw [h]
  refine Finset.card_le_card_of_injOn (fun J => Finset.univ.filter fun i => b i ∈ J) ?_ ?_
  · intro J hJ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hJ
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hJ.2⟩
  · intro J hJ K hK hJK
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hJ hK
    have key : ∀ i, b i ∈ J ↔ b i ∈ K := fun i => by
      have := Finset.ext_iff.1 hJK i
      simpa using this
    ext x
    constructor
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hJ.1 hx)
      exact (key i).1 hx
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hK.1 hx)
      exact (key i).2 hx

theorem gam_le_pow (q l : ℕ) : gam q l ≤ q ^ l := by
  unfold gam
  split_ifs with h
  · simp [h]
  · exact Nat.sub_le _ _

theorem gam_cast {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) :
    (gam q k : ℝ) = (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold gam
  rw [if_neg (by omega), Nat.add_sub_cancel, Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  field_simp
  ring

theorem one_add_pow_le_two_mul {x : ℝ} (hx : 0 ≤ x) {r : ℕ} (h : (r : ℝ) * x ≤ 1) :
    (1 + x) ^ r ≤ 1 + 2 * (r * x) := by
  have h0 : 0 ≤ (r : ℝ) * x := by positivity
  have h1 : (1 + x) ^ r ≤ Real.exp x ^ r :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) r
  rw [← Real.exp_nat_mul] at h1
  have h2 := Real.abs_exp_sub_one_le (x := r * x) (by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg h0] at h2
  linarith [(abs_le.1 h2).2]

theorem sum_choose_mul_pow_le {x : ℝ} (hx : 0 ≤ x) (r k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j ≤ (1 + x) ^ r := by
  have h1 : ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j
      ≤ ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun _ _ _ => by positivity)
  have h2 : ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * x ^ j
      = ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (by simpa using hj)]
    simp
  rw [add_comm 1 x, add_pow]
  refine h1.trans (le_of_eq ?_)
  rw [← h2]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

theorem sum_numBlockSets_mul_gamma_two_sided_bounds : ∀ (r k q : ℕ) (b : Fin r → ℕ), 1 ≤ k → 1 ≤ r → r ≤ q → 2 ≤ q → (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) ≤ ((∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam q (k - j) : ℕ) : ℝ) ∧ ((∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam q (k - j) : ℕ) : ℝ) ≤ (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ)) := by
  intro r k q b hk hr hrq hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hg := gam_cast (q := q) (k := k) (by omega) hk
  rw [Finset.sum_range_succ', numBlockSetsOfTotalSize_zero, one_mul, Nat.sub_zero]
  push_cast
  rw [hg]
  constructor
  · have : 0 ≤ ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith
  · have hx : (0 : ℝ) ≤ 1 / q := by positivity
    have h1 := sum_choose_mul_pow_le hx r k
    have h2 := one_add_pow_le_two_mul hx (r := r) (by
      rw [mul_one_div, div_le_one hq0]; exact_mod_cast hrq)
    rw [Finset.sum_range_succ'] at h1
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h1
    have h3 : ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ)
        ≤ (q : ℝ) ^ k * ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j + 1 ≤ k := by simpa using hj
      have e : (q : ℝ) ^ k * ((r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1))
          = (r.choose (j + 1) : ℝ) * (q : ℝ) ^ (k - (j + 1)) := by
        conv_lhs => rw [← Nat.sub_add_cancel hj', pow_add]
        rw [one_div_pow]
        field_simp
      rw [e]
      exact_mod_cast Nat.mul_le_mul (numBlockSetsOfTotalSize_le_choose b _) (gam_le_pow _ _)
    have h4 : ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1)
        ≤ 2 * (r * (1 / (q : ℝ))) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (pow_nonneg hq0.le k)
    have e : (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ))
        = (q : ℝ) ^ k * (2 * (r * (1 / (q : ℝ)))) + (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) := by ring
    rw [e]
    linarith

end GlobalTheory.FinGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCocycleSimplicialLevelsCup
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_cocycle_simplicial_levels_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  first | (exact @GlobalTheory.PBFg.graded_bijective) | (exact GlobalTheory.PBFg.graded_bijective) | (intros; apply GlobalTheory.PBFg.graded_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCoverStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDual_regularForms_finiteCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  first | (exact @GlobalTheory.PD.twistedDual_omB) | (exact GlobalTheory.PD.twistedDual_omB) | (intros; apply GlobalTheory.PD.twistedDual_omB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WpQTrivRight
section
noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

namespace GlobalTheory.SympQ

variable {O : Type} [CommRing O] (N : NumD O)

def trivHom (k : ℕ) : Multiplicative N.X →* N.QT k where
  toFun z := N.qTriv k z.toAdd
  map_one' := Subtype.ext (Prod.ext (by simp [NumD.qTriv]) (by simp [NumD.qTriv, N.io_zero]))
  map_mul' a b := Subtype.ext (Prod.ext (by simp [NumD.qTriv, smul_add]) (by simp [NumD.qTriv, N.io_add]))

abbrev Qq (k : ℕ) : Type := N.QT k ⧸ (trivHom N k).range

theorem qEq_iff_mk_eq {k : ℕ} (p p' : N.QT k) : N.QEq p p' ↔ (QuotientGroup.mk p : Qq N k) = QuotientGroup.mk p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [trivHom]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    change N.qTriv k z.toAdd = p⁻¹ * p' at hz
    rw [hz, mul_inv_cancel_left]

def pushRep (M n : ℕ) : N.QT M →* N.QT n :=
  if h : n ∣ M then
    { toFun := fun p => ⟨(p.1.1, p.1.2 ^ (M / n)), by
        rw [NumD.mem_QT, ← pow_mul, Nat.div_mul_cancel h]
        exact p.2⟩
      map_one' := Subtype.ext (Prod.ext rfl (by simp))
      map_mul' := fun p q => Subtype.ext (Prod.ext rfl (by simp [mul_pow])) }
  else 1

theorem pushRep_fst {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.1 = p.1.1 := by
  simp [pushRep, h]

theorem pushRep_snd {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.2 = p.1.2 ^ (M / n) := by
  simp [pushRep, h]

theorem pushRep_triv (M n : ℕ) : (trivHom N M).range ≤ (trivHom N n).range.comap (pushRep N M n) := by
  rintro _ ⟨z, rfl⟩
  by_cases h : n ∣ M
  · refine ⟨Multiplicative.ofAdd ((M / n) • z.toAdd), Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_fst N h, smul_smul, Nat.mul_div_cancel' h]
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_snd N h, N.io_nsmul]
  · simp [pushRep, h]

def pushQ (M n : ℕ) : Qq N M →* Qq N n := QuotientGroup.map _ _ (pushRep N M n) (pushRep_triv N M n)

theorem pushQ_mk (M n : ℕ) (p : N.QT M) :
    pushQ N M n (QuotientGroup.mk p) = QuotientGroup.mk (pushRep N M n p) := rfl

theorem wp_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.wp p (N.qTriv k z) = 1 := by
  rw [← inv_inj, ← NumD.wp_swap, WpPairing.wp_qTriv, inv_one]

theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (hp : N.QEq p p') (hq : N.QEq q q') : N.wp p q = N.wp p' q' := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff _ _).1 hp
  obtain ⟨w, rfl⟩ := (N.qEq_iff _ _).1 hq
  rw [WpPairing.wp_mul_left, WpPairing.wp_mul_right, WpPairing.wp_mul_right, WpPairing.wp_qTriv,
    WpPairing.wp_qTriv, wp_qTriv_right]
  simp

def wpQ (k : ℕ) (x y : Qq N k) : Oˣ :=
  Quotient.liftOn₂' x y (fun p q => N.wp p q) fun p q p' q' hp hq =>
    wp_congr N ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hp)) ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hq))

theorem wpQ_mk (k : ℕ) (p q : N.QT k) : wpQ N k (QuotientGroup.mk p) (QuotientGroup.mk q) = N.wp p q := rfl

end GlobalTheory.SympQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XiMuAssociatedOfPrimitiveRootsStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xi_mu_associated_of_primitive_roots : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ ε' : PreTilt O p, IsPrimitiveRoot (root ε').untilt p → Associated (xi ε) (xi ε') ∧ Associated (mu ε) (mu ε') := by
  first | exact @GlobalTheory.DetInv.xi_mu_associated | exact GlobalTheory.DetInv.xi_mu_associated | (intros; apply GlobalTheory.DetInv.xi_mu_associated <;> assumption)
end

