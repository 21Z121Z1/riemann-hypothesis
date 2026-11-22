import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockGroupUnipotentDoubleCosetCellBlockDia
section
open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.Cut.Block

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

variable {F : Type} [NormedField F] {m : ℕ}

open Matrix Topology in
variable {F : Type} [NormedField F] {m : ℕ} in
theorem _root_.GlobalTheory.JSW.Cut.Block.mir_inv (a : GL (Fin m) F) (y : Fin m → F) :
    (_root_.GlobalTheory.JSW.KirFin.mir a y)⁻¹ =
      _root_.GlobalTheory.JSW.KirFin.mir a⁻¹ (-((a⁻¹).val *ᵥ y)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [_root_.GlobalTheory.JSW.KirFin.mir_mul]
  simp [mulVec_neg, mulVec_mulVec, ← _root_.GlobalTheory.JSW.KirFin.mir_one]

theorem mir_left_inj {g h : GL (Fin m) F} {x y : Fin m → F} (e : mir g x = mir h y) : g = h := by
  ext i j
  have := congrArg (fun p : GL (Fin (m + 1)) F => p.val i.castSucc j.castSucc) e
  simpa using this

def blocks (U : Subgroup (GL (Fin (m + 1)) F)) : Subgroup (GL (Fin m) F) where
  carrier := {a | ∃ y, mir a y ∈ U}
  one_mem' := ⟨0, by rw [mir_one]; exact U.one_mem⟩
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨a.val *ᵥ z + y, by rw [← mir_mul]; exact U.mul_mem hy hz⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨_, by rw [← mir_inv]; exact U.inv_mem hy⟩

theorem exists_blocks_cell_cor_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  intro F _ m U hUc hUo
  refine ⟨blocks U, isCompact_blocks hUc, ?_, fun b hb => ⟨0, hb⟩, fun h₀ h => ?_⟩
  · exact Subgroup.isOpen_mono (H₁ := U.comap cor) (fun b hb => ⟨0, hb⟩) (hUo.preimage continuous_cor)
  constructor
  · rintro ⟨n, hn, u, hu, e⟩
    obtain ⟨n', x, rfl⟩ := exists_mir (lr_of_mem hn)
    have hlu : lr u = lr 1 := by
      have h1 : lr (cor h) = lr (1 * u) := by
        rw [e]
        refine lr_mul_congr ?_ u
        rw [lr_mul_congr (lr_of_mem hn) _, one_mul]
        exact lr_mir h₀ 0
      rw [one_mul] at h1
      rw [← h1]
      exact lr_mir h 0
    obtain ⟨a, y, rfl⟩ := exists_mir hlu
    refine ⟨n', mir_mem_iff.1 hn, a, ⟨y, hu⟩, ?_⟩
    change mir h 0 = mir n' x * mir h₀ 0 * mir a y at e
    rw [mir_mul, mir_mul] at e
    exact mir_left_inj e
  · rintro ⟨n', hn', a, ⟨y, hy⟩, rfl⟩
    refine ⟨mir n' (-((n' * h₀).val *ᵥ y)), mir_mem_iff.2 hn', mir a y, hy, ?_⟩
    change mir (n' * h₀ * a) 0 = mir n' _ * mir h₀ 0 * mir a y
    rw [mir_mul, mir_mul, mulVec_zero, zero_add, add_neg_cancel]

end GlobalTheory.JSW.Cut.Block
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleCorrectionSquareZeroIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

namespace CocCorr

variable {R : Type} [CommRing R] {I : Ideal R}

theorem mul_eq_zero_of_mem (hI : I ^ 2 = ⊥) {S : Type} [CommRing S] [Algebra R S] {x y : S}
    (hx : x ∈ I.map (algebraMap R S)) (hy : y ∈ I.map (algebraMap R S)) : x * y = 0 := by
  have h : I.map (algebraMap R S) ^ 2 = ⊥ := by rw [← Ideal.map_pow, hI, Ideal.map_bot]
  have := Ideal.mul_mem_mul hx hy
  rw [← pow_two, h] at this
  exact (Submodule.mem_bot _).1 this

theorem map_mem {S S' : Type} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S'] (φ : S →+* S')
    (hφ : ∀ r : R, φ (algebraMap R S r) = algebraMap R S' r) {x : S}
    (hx : x ∈ I.map (algebraMap R S)) : φ x ∈ I.map (algebraMap R S') := by
  have h := Ideal.mem_map_of_mem φ hx
  rwa [Ideal.map_map, show φ.comp (algebraMap R S) = algebraMap R S' from RingHom.ext hφ] at h

end CocCorr

open CocCorr in
theorem cocycle_of_sqZero : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), PrimI I n₀ n₁ n₂ → ∀ (u : C1 F) (v : C0 F'), (∀ t t' a, IsUnit (u t t' a)) → In2 I F (mdef F u) → (∀ t, IsUnit (v t)) → MulRel I n₀ n₁ n₂ u v → ∃ u' : C1 F, In1 I F (u' - u) ∧ mdef F u' = 0 := by
  intro R _ I hI D T _ _ F F' n₀ n₁ n₂ hP u v hu hm hv hrel

  have hmpI : ∀ {t t' : D} (b : t ⟶ t') {x : F.obj t}, x ∈ I.map (algebraMap R (F.obj t)) →
      mp F b x ∈ I.map (algebraMap R (F.obj t')) := fun b x hx ↦
    map_mem (mp F b).toRingHom (fun r ↦ (mp F b).commutes r) hx
  have hmpI' : ∀ {t t' : T} (b : t ⟶ t') {x : F'.obj t}, x ∈ I.map (algebraMap R (F'.obj t)) →
      mp F' b x ∈ I.map (algebraMap R (F'.obj t')) := fun b x hx ↦
    map_mem (mp F' b).toRingHom (fun r ↦ (mp F' b).commutes r) hx
  have hαI : ∀ (n : CoefMap (RingHom.id R) F F') (t : T) {x : F.obj (n.G.obj t)},
      x ∈ I.map (algebraMap R (F.obj (n.G.obj t))) → n.α t x ∈ I.map (algebraMap R (F'.obj t)) := by
    intro n t x hx
    refine map_mem (n.α t) (fun r ↦ ?_) hx
    rw [Algebra.algebraMap_eq_smul_one, n.smul, map_one, RingHom.id_apply, Algebra.algebraMap_eq_smul_one]

  let z : C2 F := fun t t' t'' a b ↦ mdef F u t t' t'' a b * Ring.inverse (u t t'' (a ≫ b))
  have hzI : In2 I F z := fun t t' t'' a b ↦ Ideal.mul_mem_right _ _ (hm t t' t'' a b)
  have hz_eq : ∀ {t t' t'' : D} (a : t ⟶ t') (b : t' ⟶ t''),
      mp F b (u t t' a) * u t' t'' b = u t t'' (a ≫ b) + u t t'' (a ≫ b) * z t t' t'' a b := by
    intro t t' t'' a b
    have h1 := Ring.mul_inverse_cancel _ (hu t t'' (a ≫ b))
    simp only [z, mdef]
    linear_combination (-(mp F b (u t t' a) * u t' t'' b - u t t'' (a ≫ b))) * h1

  have hz2 : z ∈ Z2 F := by
    intro t t' t'' t''' a b c
    have e1 := congrArg (mp F c) (hz_eq a b)
    simp only [map_mul, map_add, ← mp_comp] at e1
    have e2 := hz_eq (a ≫ b) c
    have e3 := hz_eq a (b ≫ c)
    have e4 := hz_eq b c
    rw [Category.assoc] at e2
    have p1 := mul_eq_zero_of_mem hI (hmpI c (hzI _ _ _ a b)) (hzI _ _ _ (a ≫ b) c)
    have p2 := mul_eq_zero_of_mem hI (hzI _ _ _ a (b ≫ c)) (hzI _ _ _ b c)
    have hU : u t t''' (a ≫ b ≫ c) * (mp F c (z t t' t'' a b) + z t t'' t''' (a ≫ b) c
        - z t t' t''' a (b ≫ c) - z t' t'' t''' b c) = 0 := by
      linear_combination (-(u t'' t''' c)) * e1 - (1 + mp F c (z t t' t'' a b)) * e2
        + (1 + z t' t'' t''' b c) * e3 + mp F (b ≫ c) (u t t' a) * e4
        - u t t''' (a ≫ b ≫ c) * p1 + u t t''' (a ≫ b ≫ c) * p2
    have := ((hu _ _ _).mul_right_eq_zero).1 hU
    linear_combination this

  let U : CoefMap (RingHom.id R) F F' → C1 F' := fun n t t' a ↦ n.α t' (u _ _ (n.G.map a))
  let W : C1 F' := fun t t' a ↦ U n₁ t t' a * U n₂ t t' a * mp F' a (v t)
  let f : C1 F' := fun t t' a ↦ (U n₀ t t' a * v t' - W t t' a) * Ring.inverse (W t t' a)
  have hUu : ∀ n t t' a, IsUnit (U n t t' a) := fun n t t' a ↦ (hu _ _ _).map (n.α t')
  have hWu : ∀ t t' a, IsUnit (W t t' a) := fun t t' a ↦
    ((hUu n₁ t t' a).mul (hUu n₂ t t' a)).mul ((hv t).map (mp F' a))
  have hfI : In1 I F' f := fun t t' a ↦ Ideal.mul_mem_right _ _ (hrel t t' a)
  have hf_eq : ∀ {t t' : T} (a : t ⟶ t'), U n₀ t t' a * v t' =
      U n₁ t t' a * U n₂ t t' a * mp F' a (v t) + U n₁ t t' a * U n₂ t t' a * mp F' a (v t) * f t t' a := by
    intro t t' a
    have h1 := Ring.mul_inverse_cancel _ (hWu t t' a)
    simp only [f]
    linear_combination (-(U n₀ t t' a * v t' - W t t' a)) * h1
  have hUeq : ∀ (n : CoefMap (RingHom.id R) F F') {t t' t'' : T} (a : t ⟶ t') (b : t' ⟶ t''),
      mp F' b (U n t t' a) * U n t' t'' b = U n t t'' (a ≫ b) +
        U n t t'' (a ≫ b) * n.α t'' (z _ _ _ (n.G.map a) (n.G.map b)) := by
    intro n t t' t'' a b
    have h := congrArg (n.α t'') (hz_eq (n.G.map a) (n.G.map b))
    simp only [map_mul, map_add, n.naturality, ← Functor.map_comp] at h
    exact h
  have hd : d1 F' f = (n₀.pullbackTwoCocycle ⟨z, hz2⟩).1 - (n₁.pullbackTwoCocycle ⟨z, hz2⟩).1 - (n₂.pullbackTwoCocycle ⟨z, hz2⟩).1 := by
    funext t t' t'' a b
    simp only [d1_apply, Pi.sub_apply, CoefMap.pullCocycleTwo_apply]
    have ra := congrArg (mp F' b) (hf_eq a)
    simp only [map_mul, map_add, ← mp_comp] at ra
    have rb := hf_eq b
    have rab := hf_eq (a ≫ b)
    have h0 := hUeq n₀ a b
    have h1 := hUeq n₁ a b
    have h2 := hUeq n₂ a b
    set a0 := mp F' b (U n₀ t t' a)
    set a1 := mp F' b (U n₁ t t' a)
    set a2 := mp F' b (U n₂ t t' a)
    set b0 := U n₀ t' t'' b
    set b1 := U n₁ t' t'' b
    set b2 := U n₂ t' t'' b
    set c0 := U n₀ t t'' (a ≫ b)
    set c1 := U n₁ t t'' (a ≫ b)
    set c2 := U n₂ t t'' (a ≫ b)
    set V := mp F' (a ≫ b) (v t)
    set V' := mp F' b (v t')
    set V'' := v t''
    set F1 := mp F' b (f t t' a)
    set F2 := f t' t'' b
    set F3 := f t t'' (a ≫ b)
    set Z0 := n₀.α t'' (z _ _ _ (n₀.G.map a) (n₀.G.map b))
    set Z1 := n₁.α t'' (z _ _ _ (n₁.G.map a) (n₁.G.map b))
    set Z2' := n₂.α t'' (z _ _ _ (n₂.G.map a) (n₂.G.map b))
    have indexFFirst : F1 ∈ I.map (algebraMap R (F'.obj t'')) := hmpI' b (hfI _ _ a)
    have indexFSecond : F2 ∈ I.map (algebraMap R (F'.obj t'')) := hfI _ _ b
    have indexFThird : F3 ∈ I.map (algebraMap R (F'.obj t'')) := hfI _ _ (a ≫ b)
    have iZ0 : Z0 ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₀ t'' (hzI _ _ _ _ _)
    have iZ1 : Z1 ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₁ t'' (hzI _ _ _ _ _)
    have iZ2 : Z2' ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₂ t'' (hzI _ _ _ _ _)
    have hT : c1 * c2 * V * V' * ((1 + Z1) * (1 + Z2') * (1 + F1) * (1 + F2) - (1 + F3) * (1 + Z0)) = 0 := by
      linear_combination (-(a1 * a2 * V * (1 + F1))) * rb - b0 * V'' * ra
        - V * V' * (1 + F1) * (1 + F2) * (c1 * (1 + Z1) * h2 + a2 * b2 * h1) + (1 + Z0) * V' * rab + V' * V'' * h0
    have hK : IsUnit (c1 * c2 * V * V') :=
      (((hUu n₁ _ _ _).mul (hUu n₂ _ _ _)).mul ((hv t).map _)).mul ((hv t').map _)
    have hX := (hK.mul_right_eq_zero).1 hT
    linear_combination hX - (1 + F1 + F2 + F1 * F2) * mul_eq_zero_of_mem hI iZ1 iZ2
      - (1 + F2) * mul_eq_zero_of_mem hI iZ1 indexFFirst - mul_eq_zero_of_mem hI iZ1 indexFSecond
      - (1 + F2) * mul_eq_zero_of_mem hI iZ2 indexFFirst - mul_eq_zero_of_mem hI iZ2 indexFSecond
      - mul_eq_zero_of_mem hI indexFFirst indexFSecond + mul_eq_zero_of_mem hI indexFThird iZ0

  obtain ⟨f₀, hf₀I, hf₀⟩ := hP ⟨z, hz2⟩ f hzI hfI hd
  refine ⟨fun t t' a ↦ u t t' a * (1 - f₀ t t' a), fun t t' a ↦ ?_, ?_⟩
  · simp only [Pi.sub_apply]
    rw [show u t t' a * (1 - f₀ t t' a) - u t t' a = -(u t t' a * f₀ t t' a) by ring]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (hf₀I t t' a))
  · funext t t' t'' a b
    simp only [mdef, Pi.zero_apply, map_mul, map_sub, map_one]
    have e := hz_eq a b
    have ed := congrFun (congrFun (congrFun (congrFun (congrFun hf₀ t) t') t'') a) b
    rw [d1_apply] at ed
    have iF := hmpI b (hf₀I t t' a)
    have iG := hf₀I t' t'' b
    have iz := hzI t t' t'' a b
    linear_combination (1 - mp F b (f₀ t t' a)) * (1 - f₀ t' t'' b) * e - u t t'' (a ≫ b) * ed
      + u t t'' (a ≫ b) * (1 + z t t' t'' a b) * mul_eq_zero_of_mem hI iF iG
      - u t t'' (a ≫ b) * mul_eq_zero_of_mem hI iz iF - u t t'' (a ≫ b) * mul_eq_zero_of_mem hI iz iG

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdAllAway
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.InertRank

theorem exists_dvd_all {A ι : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    (a : ι → A) (s : Finset ι) (h : ∃ i ∈ s, a i ≠ 0) :
    ∃ j ∈ s, a j ≠ 0 ∧ ∀ i ∈ s, a j ∣ a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at h
  | insert k s _ ih =>
    by_cases hs : ∃ i ∈ s, a i ≠ 0
    · obtain ⟨j, hj, hj0, hdvd⟩ := ih hs
      rcases ValuationRing.dvd_total (a j) (a k) with hjk | hkj
      · refine ⟨j, Finset.mem_insert_of_mem hj, hj0, fun i hi => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hjk
        · exact hdvd i hi
      · refine ⟨k, Finset.mem_insert_self _ _, fun h0 => hj0 ?_, fun i hi => ?_⟩
        · rw [h0] at hkj
          exact zero_dvd_iff.1 hkj
        · rcases Finset.mem_insert.1 hi with rfl | hi
          · exact dvd_rfl
          · exact hkj.trans (hdvd i hi)
    · push_neg at hs
      obtain ⟨i, hi, hi0⟩ := h
      have hk : a k ≠ 0 := by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hi0
        · exact absurd (hs i hi) hi0
      refine ⟨k, Finset.mem_insert_self _ _, hk, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact dvd_rfl
      · rw [hs i hi]
        exact dvd_zero _

theorem exists_dvd_all_away {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Fintype ι]
    (P : HeightOneSpectrum R) (a : ι → R) (h : ∃ i, a i ≠ 0) :
    ∃ j, a j ≠ 0 ∧ ∀ i, ∃ r s : R, s ∉ P.asIdeal ∧ s * a i = a j * r := by
  let A := Localization.AtPrime P.asIdeal
  have hinj : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A (Ideal.primeCompl_le_nonZeroDivisors P.asIdeal)
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot A
  obtain ⟨i0, hi0⟩ := h
  obtain ⟨j, -, hj0, hdvd⟩ := exists_dvd_all (fun i => algebraMap R A (a i)) Finset.univ
    ⟨i0, Finset.mem_univ _, fun h0 => hi0 (hinj (by simpa using h0))⟩
  refine ⟨j, fun h0 => hj0 (by simp [h0]), fun i => ?_⟩
  obtain ⟨c, hc⟩ := hdvd i (Finset.mem_univ _)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl c
  refine ⟨r, (s : R), s.2, hinj ?_⟩
  have hs := IsLocalization.mk'_spec A r s
  simp only at hc
  rw [map_mul, map_mul, hc, ← hs]
  ring

theorem exists_dep_away {E : Type} [Field E] [NumberField E] {n : ℕ} {ι : Type} [Fintype ι]
    (P : HeightOneSpectrum (𝓞 E)) (v : ι → Fin n → E) (hcard : n < Fintype.card ι) :
    ∃ b : ι → 𝓞 E, ∑ i, b i • v i = 0 ∧ ∃ j, b j ∉ P.asIdeal := by
  classical
  have hdep : ¬ LinearIndependent (𝓞 E) v := by
    intro hli
    have := (LinearIndependent.iff_fractionRing (𝓞 E) E).1 hli |>.fintype_card_le_finrank
    simp at this
    omega
  obtain ⟨a, ha, hne⟩ := Fintype.not_linearIndependent_iff.1 hdep
  obtain ⟨j, hj0, hall⟩ := exists_dvd_all_away P a hne
  choose r s hs hrs using hall
  refine ⟨fun i => (∏ k ∈ Finset.univ.erase i, s k) * r i, ?_, j, ?_⟩
  · have hcoef : ∀ i, a j * ((∏ k ∈ Finset.univ.erase i, s k) * r i) = (∏ k, s k) * a i := by
      intro i
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)]
      linear_combination (-(∏ k ∈ Finset.univ.erase i, s k)) * hrs i
    have h1 : a j • ∑ i, ((∏ k ∈ Finset.univ.erase i, s k) * r i) • v i = 0 := by
      rw [Finset.smul_sum]
      simp_rw [smul_smul, hcoef, mul_smul]
      rw [← Finset.smul_sum, ha, smul_zero]
    have hj0' : algebraMap (𝓞 E) E (a j) ≠ 0 := by simpa using hj0
    have h2 : algebraMap (𝓞 E) E (a j) • ∑ i, ((∏ k ∈ Finset.univ.erase i, s k) * r i) • v i = 0 := by
      rw [algebraMap_smul]; exact h1
    exact (smul_eq_zero.1 h2).resolve_left hj0'
  · have hsj : r j = s j := by
      have : a j * r j = a j * s j := by rw [← hrs j, mul_comm]
      exact mul_left_cancel₀ hj0 this
    beta_reduce
    rw [hsj, mul_comm, Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j)]
    intro hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hmem
    exact hs k hk

theorem coeff_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {P : Ideal (𝓞 E)} {y : List ℕ}
    (hy : ∀ a ∈ y, 0 < a) (A B : Submodule (𝓞 E) (Formalism.L2.Col.Sp E n))
    (e : (A ⧸ (B ⊓ A).comap A.subtype) ≃ₗ[𝓞 E] Formalism.L2.Col.inType P y)
    (x : Fin y.length → A)
    (hx : ∀ i, e (Submodule.Quotient.mk (x i)) = Pi.single i 1)
    (b : Fin y.length → 𝓞 E) (hz : (∑ i, b i • (x i : Formalism.L2.Col.Sp E n)) ∈ B)
    (i : Fin y.length) : b i ∈ P := by
  classical
  have hq : (Submodule.Quotient.mk (∑ k, b k • x k) : A ⧸ (B ⊓ A).comap A.subtype) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    refine ⟨?_, (∑ k, b k • x k).2⟩
    simpa using hz
  have he : (∑ k, b k • (Pi.single k 1 : Formalism.L2.Col.inType P y)) = 0 := by
    have := congrArg e hq
    rw [map_zero] at this
    rw [← this, ← Submodule.mkQ_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, Submodule.mkQ_apply, hx]
  have hi := congrFun he i
  rw [Finset.sum_apply, Finset.sum_eq_single i
    (fun k _ hk => by rw [Pi.smul_apply, Pi.single_eq_of_ne hk.symm, smul_zero]) (by simp),
    Pi.smul_apply, Pi.single_eq_same] at hi
  have hi' : (Ideal.Quotient.mk (P ^ y.get i)) (b i) = 0 := by
    simpa [Algebra.smul_def] using hi
  have hmem := Ideal.Quotient.eq_zero_iff_mem.1 hi'
  have hpos : 0 < y.get i := hy _ (List.get_mem y i)
  exact Ideal.pow_le_self hpos.ne' hmem

theorem two_mul_length_le {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (P : HeightOneSpectrum (𝓞 E)) (y : List ℕ)
    (d e : Col.DecoSet E n ST SG) (hy : ∀ a ∈ y, 0 < a) (he : e ∈ d.inertSet P.asIdeal y) :
    2 * y.length ≤ n := by
  classical
  obtain ⟨⟨⟨e1⟩, ⟨e2⟩⟩, -, -⟩ := he
  by_contra hlt
  have lift : ∀ {A B : Submodule (𝓞 E) (Formalism.L2.Col.Sp E n)}
      (f : (A ⧸ (B ⊓ A).comap A.subtype) ≃ₗ[𝓞 E] Formalism.L2.Col.inType P.asIdeal y),
      ∃ x : Fin y.length → A, ∀ i, f (Submodule.Quotient.mk (x i)) = Pi.single i 1 := by
    intro A B f
    have : ∀ i, ∃ a : A, f (Submodule.Quotient.mk a) = Pi.single i 1 := fun i => by
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (f.symm (Pi.single i 1))
      exact ⟨a, by rw [ha, LinearEquiv.apply_symm_apply]⟩
    choose x hx using this
    exact ⟨x, hx⟩
  obtain ⟨x, hx⟩ := lift e1
  obtain ⟨x', hx'⟩ := lift e2
  obtain ⟨b, hb, j, hj⟩ := exists_dep_away (ι := Fin y.length ⊕ Fin y.length) P
    (Sum.elim (fun i => (x i : Formalism.L2.Col.Sp E n)) (fun i => (x' i : Formalism.L2.Col.Sp E n)))
    (by simp; omega)
  rw [Fintype.sum_sum_type] at hb
  simp only [Sum.elim_inl, Sum.elim_inr] at hb
  have h1 : (∑ i, b (Sum.inl i) • (x i : Formalism.L2.Col.Sp E n)) ∈ e.1.N := by
    rw [eq_neg_of_add_eq_zero_left hb]
    exact neg_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (x' i).2)
  have h2 : (∑ i, b (Sum.inr i) • (x' i : Formalism.L2.Col.Sp E n)) ∈ d.1.N := by
    rw [eq_neg_of_add_eq_zero_right hb]
    exact neg_mem (sum_mem fun i _ => Submodule.smul_mem _ _ (x i).2)
  rcases j with j | j
  · exact hj (coeff_mem hy _ _ e1 x hx (fun i => b (Sum.inl i)) h1 j)
  · exact hj (coeff_mem hy _ _ e2 x' hx' (fun i => b (Sum.inr i)) h2 j)

end GlobalTheory.InertRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFrameOffFiniteZeroSet
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem exists_etale_frame_of_finite_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → (∃ H : La, ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (A.zeroSet s).Finite → ∃ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y := by
  intro n Y _ _ _ _ _ _ ι La _ A hn hH E L s hs hS
  obtain ⟨H, hH⟩ := hH
  obtain ⟨T, hTf, hTd, hTm⟩ := GlobalTheory.T.exists_finite_disjoint_meeting_every_component n Y ι La A hn _ hS
  obtain ⟨k1, hk1⟩ := GlobalTheory.T.exists_sections_coords_nonvanishing_at_finset n Y ι La A H hH hTf.toFinset (A.kap + E)
  obtain ⟨k2, hk2⟩ := GlobalTheory.T.exists_pos_add_nsmul_of_levi_pos n Y ι La A H ((2 * n + 4) • A.kap + E + L) hH
  obtain ⟨t0, t, a, ht0, ht, ha, hT⟩ := hk1 (max k1 k2) (le_max_left _ _)
  obtain ⟨J, hJ, hJeq⟩ := GlobalTheory.T.exists_jacobian_section_canonical_weight n Y ι La A (A.kap + (max k1 k2) • H) t0 t ht0 ht
  obtain ⟨s', hs', hs'T, C, hC, hs'C⟩ := GlobalTheory.T.exists_linComb_sections_ne_zero_on_finset n Y ι La A L n s hTf.toFinset hs (by
    intro P hP hPS
    exact Set.disjoint_left.mp hTd (hTf.mem_toFinset.mp hP) hPS)
  obtain ⟨hmul, hopen, hfrac⟩ := GlobalTheory.T.atlasSections_mul_div_nonvanishing_isOpen n Y ι La A
  have ha' : A.IsSec ((A.kap + (max k1 k2) • H) + (A.kap + E)) a := by
    have e : (A.kap + (max k1 k2) • H) + (A.kap + E) = A.kap + ((A.kap + E) + (max k1 k2) • H) := by
      abel
    rw [e]; exact ha
  obtain ⟨h1, h1n⟩ := hmul _ _ _ _ ht0 hJ
  obtain ⟨h2, h2n⟩ := hmul _ _ _ _ h1 ha'
  obtain ⟨h3, h3n⟩ := hmul _ _ _ _ h2 hs'
  have hdec : ∀ y, t0 (A.pick y) y * J (A.pick y) y * a (A.pick y) y * s' (A.pick y) y ≠ 0 →
      t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y ∧ a (A.pick y) y ≠ 0 := by
    intro y hy
    have hJ0 : J (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    have ht00 : t0 (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    have ha0 : a (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    refine ⟨ht00, ?_, ha0⟩
    rw [hJeq (A.pick y) y (A.mem_pick y) ht00] at hJ0
    exact right_ne_zero_of_mul hJ0
  have hopen' := hopen _ _ h3
  obtain ⟨M, hM⟩ := (isCompact_range (ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_nsq A h2)).bddAbove
  refine ⟨_, fun i y => t0 i y * J i y * a i y * s' i y, A.zmap t0 t, fun i y => a i y / t0 i y,
    h3, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (A.kap + (max k1 k2) • H) + (A.kap + (2 * n) • (A.kap + (max k1 k2) • H)) +
        ((A.kap + (max k1 k2) • H) + (A.kap + E)) + L
        = ((2 * n + 4) • A.kap + E + L) + ((2 * n + 2) * max k1 k2) • H := by
      module
    rw [e]
    apply hk2
    calc k2 ≤ max k1 k2 := le_max_right _ _
      _ ≤ (2 * n + 2) * max k1 k2 := Nat.le_mul_of_pos_left _ (by omega)
  · exact GlobalTheory.T.isEtaleCoordinates_section_quotients n Y ι La A _ t0 t _ ht0 ht hopen' (fun y hy => ⟨(hdec y hy).1, (hdec y hy).2.1⟩)
  · exact hfrac _ _ a t0 _ ha' ht0 (fun y hy => ⟨(hdec y hy).2.2, (hdec y hy).1⟩)
  · refine GlobalTheory.T.dense_nonvanishingSet_of_ne_zero_on_components n Y ι La A _ _ T h3 hTm ?_
    intro P hP
    obtain ⟨ht0P, hcP, haP⟩ := hT P (hTf.mem_toFinset.mpr hP)
    have hsP := hs'T P (hTf.mem_toFinset.mpr hP)
    have hJP : J (A.pick P) P ≠ 0 := by
      rw [hJeq (A.pick P) P (A.mem_pick P) ht0P]
      exact mul_ne_zero (pow_ne_zero _ ht0P) hcP
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ht0P hJP) haP) hsP
  · refine ⟨max M 1 * C, by positivity, fun y => ?_⟩
    rw [h3n y, mul_assoc]
    exact mul_le_mul ((hM ⟨y, rfl⟩).trans (le_max_left _ _)) (hs'C y)
      (ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_nonneg A _ _ _) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrder
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_finset_cover_units : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  classical
  intro E _ _ c hc
  let U : Subgroup (Af E)ˣ := (PicFin.intR E).toSubmonoid.units
  have h1 : ((hatOUnits c).subgroupOf U).FiniteIndex := PicFin.finiteIndex_units hc
  have h2 : Finite (U ⧸ (hatOUnits c).subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (U ⧸ (hatOUnits c).subgroupOf U)
  refine ⟨Finset.univ.image fun q : U ⧸ (hatOUnits c).subgroupOf U => (q.out : U).1, fun y hy => ?_⟩
  have hyU : y ∈ U := (Submonoid.mem_units_iff _ _).2
    ⟨fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hy v).le,
     fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (by rw [inv_coord, map_inv₀, hy v, inv_one])⟩
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨y, hyU⟩)), ?_⟩
  have h3 := (QuotientGroup.eq (s := (hatOUnits c).subgroupOf U)).1
    (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hyU⟩ : U ⧸ (hatOUnits c).subgroupOf U))
  exact Subgroup.mem_subgroupOf.1 h3

end GlobalTheory.CMVal.Euler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalVectorIsotropicNondegeneratePlanesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z)) = 0) := by
  first | exact @GlobalTheory.PlaneNorm.exists_rational_middle_vector | exact GlobalTheory.PlaneNorm.exists_rational_middle_vector | (intros; apply GlobalTheory.PlaneNorm.exists_rational_middle_vector <;> assumption)
end

