import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartSecOverOfMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

variable (S : Type) [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]
  [Algebra S Ω]

def chartSecOver (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) : Set Ω :=
  {t | ∃ n : ℕ, Kleiman.xProd I ^ n * t ∈
    secOver S y (δ + ((n * I.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)}

def ChartSecMul.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ (γ β : K → ℤ)
      (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)),
      (Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
          (chartSecOver S y k₀ e γ I * chartSecOver S y k₀ e β I) : Set Ω) =
        chartSecOver S y k₀ e (γ + β) I

theorem mem_chartSecOver_of_mem (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (δ : K → ℤ)
    (I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {t : Ω} (ht : t ∈ secOver S y δ) :
    t ∈ chartSecOver S y k₀ e δ I :=
  ⟨0, by simpa using ht⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneBlockPnPt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelCurvesLift.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ P : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) F), NumbersDVR.IsMultiProjPrime P →
        mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ P →
          ∃ W : Ideal (NumbersDVR.MRing ι F), NumbersDVR.IsMultiProjPrime W ∧ mIdealOver F y ≤ W ∧
            baseComap F k₀ e W = P

theorem ModelCurvesLift.oneBlock_pnPt (F : Type) [Field F] :
    IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1) () ∘ (Equiv.refl (Fin (1 + 1))).symm) =
      IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1 := by
  funext ⟨⟨⟩, i⟩
  rfl

theorem ModelCurvesLift.hyps (F : Type) [Field F] :
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1) () ∧
      NumbersDVR.IsMultiProjPrime (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock
        (IndefiniteRowSideFullHecke.Kleiman2.blockVec (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 1) () ∘ (Equiv.refl (Fin (1 + 1))).symm))) := by
  refine ⟨IndefiniteRowSideFullHecke.Kleiman2.isModelWithBase_pnPt F 1, ?_⟩
  rw [ModelCurvesLift.oneBlock_pnPt, IndefiniteRowSideFullHecke.Kleiman2.mIdealOver_pnPt]
  exact NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OnePt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable def onePt (k : Type) [Field k] : Fin (0 + 1) → RatFunc k := fun _ => 1

def GenericHypGap.Statement : Prop :=
  ∀ (k : Type) [Field k],
    Kleiman.IsDomination k (onePt k) (Kleiman.lineX k) ∧
    (∀ (i : Fin (0 + 1)) (hi : onePt k i ≠ 0), ∀ b ∈ Kleiman.domRing k (onePt k) (Kleiman.lineX k) i,
      ∃ s : k, algebraMap k (RatFunc k) s ≠ 0 ∧
        algebraMap k (RatFunc k) s * b ∈ Kleiman.chartRing k (onePt k) (Kleiman.singleChart hi)) ∧
    ¬ IndefiniteRowSideFullHecke.Kleiman2.SameModel k (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (Kleiman.lineX k)) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (onePt k))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointDegreePos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {k : Type u} [Field k] {N : ℕ}

theorem oneBlock_homogeneousComponent (f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    oneBlock (S := k) (N := N) (homogeneousComponent n f) =
      homogeneousComponent n (oneBlock (S := k) (N := N) f) := by
  classical
  have ho : ∀ g, oneBlock (S := k) (N := N) g = rename (HilbertPositive.blockEquiv N) g := fun _ => rfl
  ext d
  set d' := Finsupp.mapDomain (HilbertPositive.blockEquiv N).symm d with hd'
  have hd : d = Finsupp.mapDomain (HilbertPositive.blockEquiv N) d' := by
    rw [hd', ← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hdeg : d.degree = d'.degree := by
    rw [hd, Finsupp.degree_mapDomain]
  rw [ho, ho, coeff_homogeneousComponent, hd,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective,
    coeff_rename_mapDomain _ (HilbertPositive.blockEquiv N).injective, coeff_homogeneousComponent, ← hd, hdeg]

theorem isMultiProjPrime_comap_oneBlock {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {pp : Ideal (Poly k N)} (h : IsSubvar x pp 0) :
    NumbersDVR.IsMultiProjPrime (pp.comap (oneBlock (S := k) (N := N)).toRingHom) ∧
      FieldNumbers.relDim (pp.comap (oneBlock (S := k) (N := N)).toRingHom) =
        ((0 : ℕ) : WithBot (WithTop ℤ)) := by
  have := h.isPrime
  let e : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (HilbertPositive.blockEquiv N)).toRingEquiv
  have hc : pp.comap (oneBlock (S := k) (N := N)).toRingHom = pp.comap e.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  refine ⟨⟨Ideal.comap_isPrime _ _, ?_, ?_⟩, ?_⟩
  · intro f hf b
    have heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) b f =
        homogeneousComponent (b ()) f := by
      ext d
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent,
        HilbertPositive.weight_blockWeight_one d]
      congr 1
      apply propext
      constructor
      · intro h; rw [← h]
      · intro h; funext u; exact h
    rw [heq]
    change oneBlock (S := k) (N := N) _ ∈ pp
    change oneBlock (S := k) (N := N) f ∈ pp at hf
    rw [oneBlock_homogeneousComponent]
    exact h.homog _ hf _
  · intro u
    obtain ⟨i, hi⟩ := h.relevant
    refine ⟨i, ?_⟩
    change oneBlock (S := k) (N := N) (X _) ∉ pp
    rw [oneBlock, rename_X]
    exact hi
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit, hc]
    have hm : pp = (pp.comap e.toRingHom).map e.toRingHom := by
      rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective]
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e hm), h.dim]

end

theorem PointDegreePos.proof : PointDegreePos.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp h
  obtain ⟨hP, hrel⟩ := isMultiProjPrime_comap_oneBlock h
  have := hP.isPrime
  obtain ⟨hfd, -⟩ := FieldNumbers.IntNumBase.full k Unit (fun _ => Fin (N + 1)) _ hP hrel
  unfold FieldNumbers.resDeg
  rw [dif_pos hP.isPrime]
  exact Module.finrank_pos

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PReindexDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

theorem coneMap_rename {F : Type} [Field F] {κ : Type} {Ω : Type} [Field Ω] [Algebra F Ω] (x' : κ → Ω) {N : ℕ}
    (e : κ ≃ Fin (N + 1)) (p : NumbersDVR.MRing (fun _ : Unit => κ) F) :
    uniqueAlgEquiv Ω Unit (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p) =
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename (fun v : Σ _ : Unit, κ => e v.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.oneBlock]

theorem ReindexDim.proof : ReindexDim.Statement := by
  intro F _ κ _ Ω _ _ x' N e
  let σ : (Σ _ : Unit, κ) ≃ Fin (N + 1) :=
    { toFun := fun v => e v.2, invFun := fun i => ⟨(), e.symm i⟩, left_inv := fun _ => by simp,
      right_inv := fun _ => by simp }
  let f : NumbersDVR.MRing (fun _ : Unit => κ) F ≃+* Kleiman.Poly F N := (renameEquiv F σ).toRingEquiv
  have hc : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') =
      (Kleiman.primeOf (S := F) (x' ∘ e.symm)).comap f.toRingHom := by
    ext p
    change mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p = 0 ↔
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename σ p) = 0
    rw [← (uniqueAlgEquiv Ω Unit).injective.eq_iff, map_zero]
    exact Iff.of_eq (congrArg (· = 0) (coneMap_rename x' e p))
  have h : Kleiman.primeOf (S := F) (x' ∘ e.symm) = (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFiniteE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section ReadOnCharts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

def chartVal {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) : E :=
  coeffE S x E c (locConeE M I.1.1 I.1.2.2 (y ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩))

theorem chartVal_zero {n : ℕ} (I : Cech.Idx (support x) n) :
    chartVal M c (0 : Cech.Cochain (locSys S N M.coneSubE) n) I = 0 := by
  unfold chartVal
  rw [Pi.zero_apply, map_zero, map_zero]

theorem chartVal_add {n : ℕ} (y y' : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) :
    chartVal M c (y + y') I = chartVal M c y I + chartVal M c y' I := by
  unfold chartVal
  rw [Pi.add_apply, map_add, map_add]

theorem chartVal_smul {n : ℕ} (a : S) (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (I : Cech.Idx (support x) n) : chartVal M c (a • y) I = a • chartVal M c y I := by
  unfold chartVal
  rw [Pi.smul_apply, LinearMap.map_smul_of_tower, map_smul]

theorem chartVal_mem {n : ℕ} {y : Cech.Cochain (locSys S N M.coneSubE) n}
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (I : Cech.Idx (support x) n) :
    chartVal M c y I ∈ (M.tildeSys c).sub I.1 := by
  obtain ⟨v, hv, hyv⟩ := locConeE_degLoc M c _ I.1.2.2
    (hy ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ (Set.mem_univ _))
  unfold chartVal
  rw [hyv, coeffE_singleE_same]
  exact hv

theorem chartVal_d {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (J : Cech.Idx (support x) (n + 1)) :
    chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • chartVal M c y (Cech.face J j) := by
  refine (congrArg (coeffE S x E c)
    (locConeE_d M y ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩ J.1.2.2)).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

def toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) :
    Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n :=
  fun I => ⟨chartVal M c y I, chartVal_mem M c hy I⟩

theorem coe_d_toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (J : Cech.Idx (support x) (n + 1)) :
    ((Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n (toTildeC M c y hy) J : _) : E) =
      chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J := by
  rw [coe_d_sub, chartVal_d]
  rfl

def toTildeCocy (n : ℕ) :
    Cech.cocyDeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) locResS n →ₗ[S]
      LinearMap.ker (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n) where
  toFun y := ⟨toTildeC M c y.1 y.2.2, LinearMap.mem_ker.mpr (funext fun J => Subtype.ext (by
    rw [coe_d_toTildeC, LinearMap.mem_ker.mp y.2.1, chartVal_zero]
    rfl))⟩
  map_add' y y' := Subtype.ext (funext fun I => Subtype.ext (chartVal_add M c y.1 y'.1 I))
  map_smul' a y := Subtype.ext (funext fun I => Subtype.ext (chartVal_smul M c a y.1 I))

def toTildeH (n : ℕ) : cohom M.coneGradedE n c →ₗ[S] (M.tildeSys c).H n :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (toTildeCocy M c n)) (by
    intro y hy
    rw [Submodule.mem_comap] at hy
    refine LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
    cases n with
    | zero =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) 0) ∈ (⊥ : Submodule S _) at hy
      rw [Submodule.mem_bot] at hy
      change toTildeC M c y.1 y.2.2 ∈ (⊥ : Submodule S _)
      rw [Submodule.mem_bot]
      funext I
      apply Subtype.ext
      change chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) 0) I = 0
      rw [hy, chartVal_zero]
    | succ k =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) ∈
        (Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) k).map
          (Cech.d (locSys S N M.coneSubE) locResS k) at hy
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      change toTildeC M c y.1 y.2.2 ∈
        LinearMap.range (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res k)
      refine ⟨toTildeC M c z hz, funext fun J => Subtype.ext ?_⟩
      rw [coe_d_toTildeC]
      change _ = chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) J
      rw [← hzy])

theorem d_liftCochain_any {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS n (liftCochain M c t) = 0 := by
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
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · have := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _

theorem chartVal_liftCochain {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (I : Cech.Idx (support x) n) : chartVal M c (liftCochain M c t) I = (t I : E) := by
  have e1 := liftCochain_of M c t ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ I.1.2.2
  have e2 := locConeE_liftTilde M c ⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩ I.1.2.2 (t I)
  unfold chartVal
  rw [e1]
  exact (congrArg (coeffE S x E c) e2).trans (coeffE_singleE_same _ _)

theorem toTildeH_surjective (n : ℕ) : Function.Surjective (toTildeH M c n) := by
  intro q
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨Submodule.Quotient.mk ⟨liftCochain M c t.1,
    d_liftCochain_any M c t.1 (LinearMap.mem_ker.mp t.2), liftCochain_mem M c t.1⟩, ?_⟩
  change Submodule.Quotient.mk (toTildeCocy M c n _) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (funext fun I => Subtype.ext (chartVal_liftCochain M c t.1 I))

end ReadOnCharts

theorem TildeFiniteE.proof (h : SerreFinite.Statement.{u, v}) : TildeFiniteE.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M i c
  have : Module.Finite S (cohom M.coneGradedE i c) :=
    h S N M.coneSubE M.coneGradedE M.coneSubE_finite i c
  exact Module.Finite.of_surjective (toTildeH M c i) (toTildeH_surjective M c i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SecsTwistSysPtX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

def BundleRealises {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} {x : Fin (N + 1) → Ω}
    (Q : Kleiman.LineBundle S x) (β : K → ℤ) : Prop :=
  ∀ c : ℤ, (Q.toSubSystem.twist (Kleiman.twistSys S x c)).secs =
    secOver S y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem realises_graph (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s) :
    BundleRealises (graphVec x s) baseBlock Q (graphDeg n) :=
  fun c => twist_secs_eq_secOver Q n s hgen c

end Graph

section Point

variable (k : Type) [Field k]

end Point

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section Objects

variable {K : Type} [Fintype K] (ι : K → Type)

abbrev segreIdx : Unit ⊕ K → Type := Sum.elim (fun _ : Unit => ∀ k, ι k) ι

variable (R : Type*) [CommRing R]

def segreIncl : MRing ι R →ₐ[R] MRing (segreIdx ι) R :=
  rename fun v => (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k)

variable {ι R}

def segreY (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  X (⟨Sum.inl (), c⟩ : Σ k, segreIdx ι k)

def segreMon (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  ∏ k, X (⟨Sum.inr k, c k⟩ : Σ k, segreIdx ι k)

variable (ι R)

def segreRels : Set (MRing (segreIdx ι) R) :=
  {g | ∃ c d : ∀ k, ι k, g = segreY c * segreMon d - segreY d * segreMon c}

def segreLiftVal (W : Ideal (MRing ι R)) : (Σ k, segreIdx ι k) → Polynomial (MRing ι R ⧸ W)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩))
  | ⟨Sum.inr k, i⟩ => Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩))

def segreLiftMap (W : Ideal (MRing ι R)) :
    MRing (segreIdx ι) R →ₐ[R] Polynomial (MRing ι R ⧸ W) :=
  aeval (segreLiftVal ι R W)

def segreLift (W : Ideal (MRing ι R)) : Ideal (MRing (segreIdx ι) R) :=
  RingHom.ker (segreLiftMap ι R W)

end Objects

section Examples

example (W : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :
    segreY (R := ℚ) (fun _ => (0 : Fin 2)) * segreMon (fun _ => 1) -
        segreY (fun _ => 1) * segreMon (fun _ => 0) ∈ segreLift _ ℚ W := by
  simp only [segreLift, RingHom.mem_ker, segreY, segreMon, map_sub, map_mul, map_prod,
    segreLiftMap, aeval_X, segreLiftVal]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  ring

example : (X ⟨Sum.inr (), (0 : Fin 2)⟩ : MRing (segreIdx (fun _ : Unit => Fin 2)) ℚ) ∉
    segreLift _ ℚ ⊥ := by
  simp only [segreLift, RingHom.mem_ker, segreLiftMap, aeval_X, segreLiftVal]
  rw [Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact X_ne_zero _

end Examples

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

