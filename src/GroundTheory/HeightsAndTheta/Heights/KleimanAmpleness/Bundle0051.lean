import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanishLoc
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Compare

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem coe_d_sub (F : SubSystem S x E) {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥(F.sub I)) i)
    (J : Cech.Idx (support x) (i + 1)) :
    ((Cech.d (fun I : Chart x => ↥(F.sub I)) F.res i t J : F.sub J.1) : E) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • (t (Cech.face J j) : E) := by
  rw [Cech.d_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul_of_tower]
  rfl

variable (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

def liftTilde (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    LocMod S N M.coneSubE I.1 :=
  Classical.choose (exists_locConeE_eq M c I hI y.2)

theorem liftTilde_mem (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    liftTilde M c I hI y ∈ degLoc M.coneGradedE c I :=
  (Classical.choose_spec (exists_locConeE_eq M c I hI y.2)).1

theorem locConeE_liftTilde (I : StdCell N) (hI : I.1 ⊆ support x) (y : M.tilde c ⟨I.1, I.2.1, hI⟩) :
    locConeE M I.1 hI (liftTilde M c I hI y) = singleE S x E c y :=
  (Classical.choose_spec (exists_locConeE_eq M c I hI y.2)).2

def liftCochain {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    Cech.Cochain (locSys S N M.coneSubE) i := fun J =>
  if hJ : J.1.1 ⊆ support x then liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) else 0

theorem liftCochain_of {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i)
    (J : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) (hJ : J.1.1 ⊆ support x) :
    liftCochain M c t J = liftTilde M c J.1 hJ (t ⟨⟨J.1.1, J.1.2.1, hJ⟩, J.2⟩) :=
  dif_pos hJ

theorem liftCochain_mem {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) i) :
    liftCochain M c t ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) i := by
  intro J _
  by_cases hJ : J.1.1 ⊆ support x
  · rw [liftCochain_of M c t J hJ]
    exact liftTilde_mem M c _ hJ _
  · change (if hJ : J.1.1 ⊆ support x then _ else 0) ∈ _
    rw [dif_neg hJ]
    exact zero_mem _

theorem locConeE_d {i : ℕ} (z : Cech.Cochain (locSys S N M.coneSubE) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) (hK : K.1.1 ⊆ support x) :
    locConeE M K.1.1 hK (Cech.d (locSys S N M.coneSubE) locResS i z K) =
      ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
        ((Cech.face_subset K j).trans hK) (z (Cech.face K j)) := by
  rw [Cech.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  exact locConeE_locRes M (Cech.face_subset K j) hK _

theorem d_liftCochain {i : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) (i + 1))
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res (i + 1) t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS (i + 1) (liftCochain M c t) = 0 := by
  funext K
  change _ = 0
  by_cases hK : K.1.1 ⊆ support x
  · apply locConeE_injective M K.1.1 hK
    rw [locConeE_d M (liftCochain M c t) K hK, map_zero]
    have h0 := coe_d_sub (M.tildeSys c) t ⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩
    rw [ht] at h0
    calc ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
          ((Cech.face_subset K j).trans hK) (liftCochain M c t (Cech.face K j))
        = ∑ j : K.1.1, Cech.sgn K.1.1 j • singleE S x E c
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (i + 1 + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (i + 1 + 1)) j) : E)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · haveI := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _

theorem tildeSys_H_subsingleton (k : ℕ) (h : Subsingleton (cohom M.coneGradedE (k + 1) c)) :
    Subsingleton ((M.tildeSys c).H (k + 1)) := by
  unfold cohom Cech.Hdeg at h
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff'] at h
  unfold SubSystem.H Cech.H
  refine Submodule.Quotient.subsingleton_iff.mpr (Submodule.eq_top_iff'.mpr ?_)
  rintro ⟨t, ht⟩
  rw [Submodule.mem_comap]
  change t ∈ LinearMap.range (Cech.d _ (M.tildeSys c).res k)
  have hz : liftCochain M c t ∈
      Cech.cocyDeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) locResS (k + 1) :=
    ⟨d_liftCochain M c t (LinearMap.mem_ker.mp ht), liftCochain_mem M c t⟩
  have hb := h ⟨_, hz⟩
  rw [Submodule.mem_comap] at hb
  change liftCochain M c t ∈ (Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) k).map
    (Cech.d (locSys S N M.coneSubE) locResS k) at hb
  obtain ⟨y, hy, hyz⟩ := hb
  have hu : ∀ I : Cech.Idx (support x) k, coeffE S x E c (locConeE M I.1.1 I.1.2.2
      (y ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩)) ∈ (M.tildeSys c).sub I.1 := fun I => by
    obtain ⟨v, hv, hyv⟩ := locConeE_degLoc M c _ I.1.2.2
      (hy ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ (Set.mem_univ _))
    rw [hyv, coeffE_singleE_same]
    exact hv
  refine ⟨fun I => ⟨_, hu I⟩, ?_⟩
  funext J
  apply Subtype.ext
  rw [coe_d_sub]
  have e1 := locConeE_liftTilde M c ⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩ J.1.2.2 (t J)
  have e2 := congrFun hyz ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩
  rw [liftCochain_of M c t _ J.1.2.2] at e2
  rw [← coeffE_singleE_same (S := S) (x := x) c (t J : E), ← e1, ← e2]
  refine Eq.trans ?_ (congrArg (coeffE S x E c)
    (locConeE_d M y ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩ J.1.2.2)).symm
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

end Compare

theorem TildeVanish.proof (h : SerreVanish.Statement.{u, v}) : TildeVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M
  obtain ⟨c₀, hc₀⟩ := h S N M.coneSubE M.coneGradedE M.coneSubE_finite
  refine ⟨c₀, fun i hi c hc => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact tildeSys_H_subsingleton M c k (hc₀ (k + 1) hi c hc)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def segreJoin {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    (Σ k, Sum.elim (fun _ : Unit => ∀ k, ι k) ι k) → Ω :=
  IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (NumbersDVR.segreVec y)) y

def SegreBase.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S (segreJoin y) (Sum.inl ()) ∧
      (∀ β : K → ℤ, secOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) = secOver S y β) ∧
      ∀ (β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
        GeneratesOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) η ↔ GeneratesOver S y β η

theorem SegreBase.hyps (F : Type) [Field F] : ∀ k, ∃ i, IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1 ⟨k, i⟩ ≠ 0 :=
  fun _ => ⟨0, IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero F 1 _⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TrdegEqOfLeOfIsAlgebraic
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)

section Trdeg

variable {F : Type} [Field F] {B : Type} [CommRing B] [IsDomain B] [Algebra F B]

theorem trdeg_eq_of_le_of_isAlgebraic {S T : Subalgebra F B} (hST : S ≤ T)
    (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg F S = Algebra.trdeg F T := by
  let _ : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  have _ : IsScalarTower F S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : FaithfulSMul F S :=
    (faithfulSMul_iff_algebraMap_injective F S).2 (algebraMap F S).injective
  have _ : FaithfulSMul S T :=
    (faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)
  let f : T →ₐ[S] B := { T.val.toRingHom with commutes' := fun _ => rfl }
  have _ : Algebra.IsAlgebraic S T :=
    ⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩
  have h := trdeg_add_eq F S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

theorem isAlgebraic_of_mem_adjoin (S : Subalgebra F B) {s : Set B} (hs : ∀ b ∈ s, IsAlgebraic S b)
    {b : B} (hb : b ∈ Algebra.adjoin F s) : IsAlgebraic S b := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r => exact isAlgebraic_algebraMap (⟨algebraMap F B r, S.algebraMap_mem r⟩ : S)
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

theorem trdeg_eq_of_isAlgebraic_both {S T : Subalgebra F B} (h₁ : ∀ t ∈ T, IsAlgebraic S t)
    (h₂ : ∀ s ∈ S, IsAlgebraic T s) : Algebra.trdeg F S = Algebra.trdeg F T := by
  have hS : ∀ b ∈ S ⊔ T, IsAlgebraic S b := fun b hb =>
    isAlgebraic_of_mem_adjoin S (fun b (hb : b ∈ (S : Set B) ∪ T) =>
      Or.elim hb (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : S)) (h₁ b))
      (by rwa [Algebra.sup_def] at hb)
  have hT : ∀ b ∈ S ⊔ T, IsAlgebraic T b := fun b hb =>
    isAlgebraic_of_mem_adjoin T (fun b (hb : b ∈ (S : Set B) ∪ T) =>
      Or.elim hb (h₂ b) (fun h => isAlgebraic_algebraMap (⟨b, h⟩ : T)))
      (by rwa [Algebra.sup_def] at hb)
  rw [trdeg_eq_of_le_of_isAlgebraic le_sup_left hS, trdeg_eq_of_le_of_isAlgebraic le_sup_right hT]

end Trdeg

section LocalRings

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem isAlgebraic_of_mem_locIn (A : Subalgebra F Ω) (p : Ideal A) [p.IsPrime] {u : Ω}
    (hu : u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p) : IsAlgebraic A u := by
  unfold IndefiniteRowSideFullHecke.Kleiman2.locIn at hu
  induction hu using Subring.closure_induction with
  | mem u hu =>
    obtain ⟨a, b, hb, rfl⟩ := hu
    have hb0 : (b : Ω) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)
    refine IsAlgebraic.of_mul (y := (b : Ω)) (mem_nonZeroDivisors_of_ne_zero hb0)
      (isAlgebraic_algebraMap b) ?_
    have e : (b : Ω) * ((a : Ω) / b) = algebraMap A Ω a := by
      rw [mul_div_cancel₀ _ hb0]; rfl
    rw [e]
    exact isAlgebraic_algebraMap a
  | zero => exact isAlgebraic_zero
  | one => exact isAlgebraic_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | mul x y _ _ hx hy => exact hx.mul hy

theorem le_locIn (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨⟨a, ha⟩, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h), by simp⟩

theorem exists_trdeg_chartRing_eq {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (h : IndefiniteRowSideFullHecke.Kleiman2.SameModel F y y') (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ c' : ∀ k, ι' k, (∀ k, y' ⟨k, c' k⟩ ≠ 0) ∧
      Algebra.trdeg F (chartRingOver F y c) = Algebra.trdeg F (chartRingOver F y' c') := by
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F y :=
    ⟨c, hc, ⊥, Ideal.isPrime_bot, rfl⟩
  unfold IndefiniteRowSideFullHecke.Kleiman2.SameModel at h
  rw [h] at hz
  obtain ⟨c', hc', p', hp', hzeq⟩ := hz
  refine ⟨c', hc', trdeg_eq_of_isAlgebraic_both (fun t ht => ?_) (fun s hs => ?_)⟩
  · have ht' : t ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y c) ⊥ := by
      rw [hzeq]; exact le_locIn _ p' ht
    exact isAlgebraic_of_mem_locIn _ ⊥ ht'
  · have hs' : s ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver F y' c') p' := by
      rw [← hzeq]; exact le_locIn _ ⊥ hs
    exact isAlgebraic_of_mem_locIn _ p' hs'

end LocalRings

section Cone

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
variable {K : Type} {ι : K → Type}

def chartConeMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    MvPolynomial K (chartRingOver F y c) →ₐ[F] MvPolynomial K Ω :=
  ((aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars
    F).comp (MvPolynomial.mapAlgHom (chartRingOver F y c).val)

theorem chartConeMap_C (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : chartRingOver F y c) :
    chartConeMap y c (MvPolynomial.C a) = MvPolynomial.C (a : Ω) := by
  simp [chartConeMap]

theorem chartConeMap_X (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    chartConeMap (F := F) y c (X k) = MvPolynomial.C (y ⟨k, c k⟩) * X k := by
  simp [chartConeMap]

theorem mConeMapOver_X (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mConeMapOver F y (X p) = MvPolynomial.C (y p) * X p.1 := by
  simp [mConeMapOver]

theorem chartConeMap_injective (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (chartConeMap (F := F) y c) := by
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k
  let ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => MvPolynomial.C (y ⟨k, c k⟩)⁻¹ * X k
  have hinv : ψ'.comp ψ = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]
  have hψ : Function.Injective ψ := Function.LeftInverse.injective (g := ψ') fun p => by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  exact hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)

theorem trdeg_quotient_mIdealOver [Fintype K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) =
      Algebra.trdeg F (chartRingOver F y c) + Fintype.card K := by
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ chartRingOver F y c := fun p =>
    Algebra.subset_adjoin ⟨p, rfl⟩

  let ρ : MvPolynomial (Σ k, ι k) F →ₐ[F] MvPolynomial K (chartRingOver F y c) :=
    aeval fun p => MvPolynomial.C (⟨_, hu p⟩ : (chartRingOver F y c)) * X p.1
  have hfac : mConeMapOver F y = (chartConeMap (F := F) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [mConeMapOver_X, AlgHom.comp_apply]
    rw [aeval_X, map_mul, chartConeMap_C, chartConeMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mConeMapOver F y).range
  have hle : R ≤ (chartConeMap (F := F) y c).range := by
    show (mConeMapOver F y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hUR : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ∈ R := fun k =>
    ⟨X ⟨k, c k⟩, mConeMapOver_X y _⟩
  have hU0 : ∀ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ≠ 0 := fun k =>
    mul_ne_zero (MvPolynomial.C_ne_zero.2 (hc k)) (MvPolynomial.X_ne_zero k)

  have halgC : ∀ w ∈ (chartRingOver F y c), IsAlgebraic R (MvPolynomial.C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      refine IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1)
        (mem_nonZeroDivisors_of_ne_zero (hU0 p.1)) (isAlgebraic_algebraMap (⟨_, hUR p.1⟩ : R)) ?_
      have e : (MvPolynomial.C (y ⟨p.1, c p.1⟩) * X p.1 : MvPolynomial K Ω) *
          MvPolynomial.C (y p / y ⟨p.1, c p.1⟩) = mConeMapOver F y (X p) := by
        rw [mConeMapOver_X, mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hc p.1)]
      rw [e]
      exact isAlgebraic_algebraMap (⟨_, AlgHom.mem_range_self _ _⟩ : R)
    | algebraMap r =>
      exact isAlgebraic_algebraMap (⟨algebraMap F _ r, R.algebraMap_mem r⟩ : R)
    | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy
  have halg : ∀ t ∈ (chartConeMap (F := F) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (chartConeMap (F := F) y c q)
    induction q using MvPolynomial.induction_on with
    | C a => rw [chartConeMap_C]; exact halgC a a.2
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, chartConeMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hUR k⟩ : R))
  have h1 : Algebra.trdeg F (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = Algebra.trdeg F R :=
    (Ideal.quotientKerEquivRange (mConeMapOver F y)).trdeg_eq
  have h2 : Algebra.trdeg F (chartConeMap (F := F) y c).range =
      Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) :=
    (AlgEquiv.ofInjective (chartConeMap (F := F) y c) (chartConeMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul F (chartRingOver F y c) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F (chartRingOver F y c)).injective
  have _ : FaithfulSMul (chartRingOver F y c) (MvPolynomial K (chartRingOver F y c)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective K _)
  have h3 : Algebra.trdeg F (MvPolynomial K (chartRingOver F y c)) =
      Algebra.trdeg F (chartRingOver F y c) + Fintype.card K := by
    rw [← trdeg_add_eq F (chartRingOver F y c) (A := MvPolynomial K (chartRingOver F y c)),
      MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [h1, trdeg_eq_of_le_of_isAlgebraic hle halg, h2, h3]

end Cone

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

