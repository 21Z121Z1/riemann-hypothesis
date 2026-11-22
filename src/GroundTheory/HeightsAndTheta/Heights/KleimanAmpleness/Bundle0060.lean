import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoeNeZeroOfNotMem
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PModelGenericPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

namespace ModelGenericPoint

variable {O : Type} [CommRing O] {K : Type} {ι : K → Type} (P : Ideal (NumbersDVR.MRing ι O))

def genPt : (Σ k, ι k) → FractionRing (NumbersDVR.MRing ι O ⧸ P) :=
  fun p => algebraMap (NumbersDVR.MRing ι O ⧸ P) _ (Ideal.Quotient.mk P (X p))

theorem aeval_genPt (g : NumbersDVR.MRing ι O) :
    aeval (genPt P) g = algebraMap (NumbersDVR.MRing ι O ⧸ P)
      (FractionRing (NumbersDVR.MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) := by
  have h : (aeval (genPt P) : NumbersDVR.MRing ι O →ₐ[O] FractionRing (NumbersDVR.MRing ι O ⧸ P)) =
      (IsScalarTower.toAlgHom O (NumbersDVR.MRing ι O ⧸ P)
        (FractionRing (NumbersDVR.MRing ι O ⧸ P))).comp (Ideal.Quotient.mkₐ O P) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPt]
  rw [h]
  rfl

theorem aeval_genPt_eq_zero (g : NumbersDVR.MRing ι O) : aeval (genPt P) g = 0 ↔ g ∈ P := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

theorem genPt_ne_zero (p : Σ k, ι k) : genPt P p ≠ 0 ↔ (X p : NumbersDVR.MRing ι O) ∉ P := by
  rw [Ne, ← aeval_genPt_eq_zero, aeval_X]

theorem mIdealOver_genPt [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [P.IsPrime]
    (hP : NumbersDVR.IsMultiHomogIdeal P) : mIdealOver O (genPt P) = P := by
  ext f
  constructor
  · intro hf
    have hc : ∀ b : K → ℕ, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P := by
      intro b
      rw [← aeval_genPt_eq_zero, ← coeff_mConeMapOver, RingHom.mem_ker.mp hf, coeff_zero]
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    exact Ideal.sum_mem _ fun b _ => hc b
  · intro hf
    refine RingHom.mem_ker.mpr ?_
    ext m
    rw [coeff_zero]
    have h := coeff_mConeMapOver (S := O) (genPt P) (⇑m) f
    rw [Finsupp.equivFunOnFinite_symm_coe] at h
    rw [h, aeval_genPt_eq_zero]
    exact hP f hf _

theorem algebraMap_injective (h : P.comap (C : O →+* NumbersDVR.MRing ι O) = ⊥) :
    Function.Injective (algebraMap O (FractionRing (NumbersDVR.MRing ι O ⧸ P))) := by
  have h0 : Function.Injective (algebraMap O (NumbersDVR.MRing ι O ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hc' : Ideal.Quotient.mk P (C c) = 0 := by
      exact hc
    have hmem : c ∈ P.comap (C : O →+* NumbersDVR.MRing ι O) :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hc')
    rw [h] at hmem
    exact hmem
  rw [IsScalarTower.algebraMap_eq O (NumbersDVR.MRing ι O ⧸ P)]
  exact (IsFractionRing.injective (NumbersDVR.MRing ι O ⧸ P)
    (FractionRing (NumbersDVR.MRing ι O ⧸ P))).comp h0

end ModelGenericPoint

open ModelGenericPoint in

theorem ModelGenericPoint.proof : ModelGenericPoint.Statement := by
  intro O _ _ _ K _ _ ι _ P d hP
  have := hP.multiProj.isPrime
  have hinj := algebraMap_injective P hP.noTorsion
  let alg : Algebra (FractionRing O) (FractionRing (NumbersDVR.MRing ι O ⧸ P)) :=
    (IsFractionRing.lift hinj).toAlgebra
  refine ⟨FractionRing (NumbersDVR.MRing ι O ⧸ P), inferInstance, inferInstance, alg, ?_, genPt P,
    mIdealOver_genPt P hP.multiProj.multiHomog, fun k => ?_⟩
  · exact IsScalarTower.of_algebraMap_eq fun c => (IsFractionRing.lift_algebraMap hinj c).symm
  · obtain ⟨i, hi⟩ := hP.multiProj.relevant k
    exact ⟨i, (genPt_ne_zero P _).mpr hi⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinRestrictionSame
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts SameModel modVec resImage ResField)

theorem coe_subringCongr {R : Type*} [Ring R] {s t : Subring R} (h : s = t) (x : s) :
    ((RingEquiv.subringCongr h x : t) : R) = x :=
  rfl

theorem coe_subringCongr_symm {R : Type*} [Ring R] {s t : Subring R} (h : s = t) (x : t) :
    (((RingEquiv.subringCongr h).symm x : s) : R) = x :=
  rfl

section Transport

variable {S : Type*} [CommRing S] {L L' : Type*} [Field L] [Field L'] [Algebra S L] [Algebra S L']

theorem locIn_map (φ : L ≃ₐ[S] L') (A : Subalgebra S L) (B : Subalgebra S L') (e : A ≃ₐ[S] B)
    (he : ∀ a, (e a : L') = φ a) (p : Ideal A) (P : Ideal B) (hpP : ∀ a, a ∈ p ↔ e a ∈ P) :
    (locIn A p).map (φ : L →+* L') = locIn B P := by
  unfold locIn
  rw [RingHom.map_closure]
  congr 1
  ext u
  constructor
  · rintro ⟨_, ⟨a, b, hb, rfl⟩, rfl⟩
    exact ⟨e a, e b, fun h => hb ((hpP b).mpr h), by simp [he, map_div₀]⟩
  · rintro ⟨a', b', hb', rfl⟩
    refine ⟨(e.symm a' : L) / e.symm b', ⟨e.symm a', e.symm b', fun h => hb' ?_, rfl⟩, ?_⟩
    · simpa using (hpP (e.symm b')).mp h
    · simp only [RingHom.coe_coe, map_div₀, ← he, AlgEquiv.apply_symm_apply]

theorem chartRingOver_comp {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k) :
    chartRingOver S (fun q => φ (v q)) c = (chartRingOver S v c).map (φ : L →ₐ[S] L') := by
  unfold chartRingOver
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  congr 1
  ext u
  simp [map_div₀]

noncomputable def chartEquiv {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k) :
    chartRingOver S v c ≃ₐ[S] chartRingOver S (fun q => φ (v q)) c :=
  (φ.subalgebraMap (chartRingOver S v c)).trans (Subalgebra.equivOfEq _ _ (chartRingOver_comp φ v c).symm)

theorem chartEquiv_coe {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) (c : ∀ k, ι k)
    (a : chartRingOver S v c) : (chartEquiv φ v c a : L') = φ a :=
  rfl

theorem modelPts_comp {K : Type} {ι : K → Type} (φ : L ≃ₐ[S] L') (v : (Σ k, ι k) → L) :
    modelPts S (fun q => φ (v q)) = Subring.map (φ : L →+* L') '' modelPts S v := by
  ext z
  constructor
  · rintro ⟨c, hc, P, hP, rfl⟩
    have hc' : ∀ k, v ⟨k, c k⟩ ≠ 0 := fun k h => hc k (by simp [h])
    refine ⟨_, ⟨c, hc', P.comap (chartEquiv φ v c : chartRingOver S v c →+* _), inferInstance, rfl⟩, ?_⟩
    exact locIn_map φ _ _ (chartEquiv φ v c) (chartEquiv_coe φ v c) _ P (fun a => Iff.rfl)
  · rintro ⟨_, ⟨c, hc, p, hp, rfl⟩, rfl⟩
    have hc' : ∀ k, φ (v ⟨k, c k⟩) ≠ 0 := fun k => by simpa using hc k
    refine ⟨c, hc', p.comap ((chartEquiv φ v c).symm : _ →+* chartRingOver S v c), inferInstance, ?_⟩
    exact locIn_map φ _ _ (chartEquiv φ v c) (chartEquiv_coe φ v c) p _
      (fun a => by rw [Ideal.mem_comap, RingHom.coe_coe, AlgEquiv.symm_apply_apply])

theorem exists_algEquiv_of_ker_eq {R : Type*} [CommRing R] (r : R →+* L) (r' : R →+* L')
    (hr : Function.Surjective r) (hr' : Function.Surjective r') (hker : RingHom.ker r = RingHom.ker r')
    (hS : ∀ s : S, ∃ u, r u = algebraMap S L s ∧ r' u = algebraMap S L' s) :
    ∃ φ : L ≃ₐ[S] L', ∀ u, φ (r u) = r' u := by
  let φ₀ : L ≃+* L' := (RingHom.quotientKerEquivOfSurjective hr).symm.trans
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hr'))
  have hφ₀ : ∀ u, φ₀ (r u) = r' u := fun u => by
    simp only [φ₀, RingEquiv.trans_apply, RingHom.quotientKerEquivOfSurjective_symm_apply,
      Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  refine ⟨AlgEquiv.ofRingEquiv (f := φ₀) fun s => ?_, fun u => hφ₀ u⟩
  obtain ⟨u, hu, hu'⟩ := hS s
  rw [← hu, hφ₀, hu']

theorem map_closure_of_image (φ : L ≃ₐ[S] L') {X : Set L} {Y : Set L'} (h : φ '' X = Y) :
    (Subring.closure X).map (φ : L →+* L') = Subring.closure Y := by
  rw [RingHom.map_closure, RingHom.coe_coe, h]

end Transport

theorem exists_resEquiv {S : Type} [CommRing S] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω)
    (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]
    (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime]
    (hloc : locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p) :
    ∃ φ : ResField S y c p ≃ₐ[S] ResField S y' c' p',
      ∀ u, φ (resMap y c p u) = resMap y' c' p' (RingEquiv.subringCongr hloc.symm u) := by
  let e := RingEquiv.subringCongr hloc.symm
  refine exists_algEquiv_of_ker_eq (resMap y c p) ((resMap y' c' p').comp e.toRingHom)
    (resMap_surjective y c p) ((resMap_surjective y' c' p').comp e.surjective) ?_ ?_
  · ext u
    rw [RingHom.mem_ker, RingHom.mem_ker]
    show resMap y c p u = 0 ↔ resMap y' c' p' (e u) = 0
    rw [resMap_eq_zero_iff, resMap_eq_zero_iff, isUnit_map_iff]
  · intro s
    have hs : algebraMap S Ω s ∈ locIn (chartRingOver S y c) p :=
      (mem_locIn_chart_iff y c p).mpr ⟨algebraMap S _ s, 1, Ideal.one_notMem p, by simp⟩
    exact ⟨⟨_, hs⟩, resMap_algebraMap y c p s hs, resMap_algebraMap y' c' p' s _⟩

theorem image_resImage {S : Type} [CommRing S] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω)
    (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime]
    (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime]
    (hloc : locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p)
    (φ : ResField S y c p ≃ₐ[S] ResField S y' c' p')
    (hφ : ∀ u, φ (resMap y c p u) = resMap y' c' p' (RingEquiv.subringCongr hloc.symm u))
    (z : Subring Ω) (hz : z ≤ locIn (chartRingOver S y c) p) :
    φ '' resImage S y c p z = resImage S y' c' p' z := by
  have hz' : z ≤ locIn (chartRingOver S y' c') p' := hloc.symm ▸ hz
  rw [resImage_eq y c p z hz, resImage_eq y' c' p' z hz']
  ext v
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨RingEquiv.subringCongr hloc.symm u, ?_, hφ u⟩
    rw [coe_subringCongr]
    exact hu
  · rintro ⟨u', hu', rfl⟩
    refine ⟨resMap y c p ((RingEquiv.subringCongr hloc.symm).symm u'), ⟨_, ?_, rfl⟩, ?_⟩
    · rw [coe_subringCongr_symm]
      exact hu'
    · rw [hφ, RingEquiv.apply_symm_apply]

theorem sameModel_modVec (h : RestrictionPointsAll.Statement) {S : Type} [CommRing S] {K : Type} {ι : K → Type}
    {K' : Type} {ι' : K' → Type} {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω)
    (hyy' : modelPts S y = modelPts S y')
    (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime] (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime] (hc' : ∀ k, y' ⟨k, c' k⟩ ≠ 0)
    (hloc : locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p)
    (φ : ResField S y c p ≃ₐ[S] ResField S y' c' p')
    (himg : ∀ z ≤ locIn (chartRingOver S y c) p, φ '' resImage S y c p z = resImage S y' c' p' z) :
    modelPts S (fun q => φ (modVec S y c p q)) = modelPts S (modVec S y' c' p') := by
  rw [modelPts_comp φ (modVec S y c p), h S K ι Ω y c p hc, h S K' ι' Ω y' c' p' hc', hloc, ← hyy']
  ext z'
  constructor
  · rintro ⟨_, ⟨z, hz, hzO, rfl⟩, rfl⟩
    exact ⟨z, hz, hzO, map_closure_of_image φ (himg z hzO)⟩
  · rintro ⟨z, hz, hzO, rfl⟩
    exact ⟨_, ⟨z, hz, hzO, rfl⟩, map_closure_of_image φ (himg z hzO)⟩

theorem RestrictionSame.proof (h : RestrictionPointsAll.Statement) : RestrictionSame.Statement := by
  intro S _ K _ ι K' ι' Ω _ _ y y' hyy' c p _ hc c' p' _ hc' hloc
  obtain ⟨φ, hφ⟩ := exists_resEquiv y y' c p c' p' hloc
  have himg := image_resImage y y' c p c' p' hloc φ hφ
  exact ⟨φ, fun z _ hz => himg z hz, sameModel_modVec h y y' hyy' c p hc c' p' hc' hloc φ himg⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenPrimeOfEqFinrank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter

noncomputable section

universe u w

section Lemmas

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_twistSys {n : ℕ} (b : Fin n → ℤ) (l : List (Fin n)) (a : ℤ) :
    l.foldl (fun F i => F.twist (twistSys S x (b i))) (twistSys S x a) =
      twistSys S x (a + (l.map b).sum) := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, twistSys_twist_eq_add, ih, List.map_cons, List.sum_cons, add_assoc]

theorem tensorSub_twistSys {n : ℕ} (b : Fin n → ℤ) (T : Finset (Fin n)) :
    tensorSub (fun i => twistSys S x (b i)) T = twistSys S x (∑ i ∈ T, b i) := by
  classical
  rw [tensorSub, foldl_twist_twistSys, zero_add,
    ← List.sum_toFinset b ((List.nodup_finRange n).filter _)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp

theorem interSum_twistSys (pp : Ideal (Poly S N)) {n : ℕ} (b : Fin n → ℤ) (c : ℕ) :
    interSum pp (fun i => twistSys S x (b i)) c =
      ∑ T : Finset (Fin n), (-1) ^ (n - T.card) * restrLen pp (twistSys S x (∑ i ∈ T, b i + c)) := by
  unfold interSum
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [tensorSub_twistSys, twistSys_twist_eq_add]

end Lemmas

section Differences

variable {K : Type*}

theorem foldr_diffStep_eq {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) (l : List (Fin n))
    (hl : l.Nodup) (m : K → ℤ) :
    (l.map bs).foldr NumbersDVR.diffStep h m =
      ∑ T ∈ l.toFinset.powerset, (-1) ^ T.card * h (m - ∑ i ∈ T, bs i) := by
  classical
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
    have ha' : a ∉ l.toFinset := fun h' => ha (List.mem_toFinset.mp h')
    rw [List.map_cons, List.foldr_cons, List.toFinset_cons, Finset.sum_powerset_insert ha']
    change (l.map bs).foldr NumbersDVR.diffStep h m - (l.map bs).foldr NumbersDVR.diffStep h (m - bs a) = _
    rw [ih hl' m, ih hl' (m - bs a), sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have hat : a ∉ t := fun h' => ha' (Finset.mem_powerset.mp ht h')
    rw [Finset.card_insert_of_notMem hat, Finset.sum_insert hat, pow_succ, sub_sub]
    ring

theorem mixedDiff_eq_sum {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    NumbersDVR.mixedDiff bs h m = ∑ T : Finset (Fin n), (-1) ^ T.card * h (m - ∑ i ∈ T, bs i) := by
  classical
  rw [NumbersDVR.mixedDiff, List.ofFn_eq_map, foldr_diffStep_eq bs h _ (List.nodup_finRange n),
    List.toFinset_finRange, Finset.powerset_univ]

end Differences

section Point

variable {k : Type u} [Field k] {K' : Type w} [Field K'] [Algebra k K'] {N : ℕ}

theorem restrLen_primeOf_eq_finrank (y : Fin (N + 1) → K') {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y K') : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := k) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := k) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := k) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := k) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule k F.secs) rfl).length_eq, Module.length_eq_rank]
  rfl

end Point

theorem NumEq.proof (hRL : RestrLenRestrict.Statement.{0, 0}) : NumEq.Statement := by
  intro k _ N Ω _ _ x pp e b hsub
  classical

  obtain ⟨j, hjp⟩ := hsub.relevant
  have hj : x j ≠ 0 := fun h0 => hjp (hsub.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.full k Ω N x pp hsub.isPrime hsub.homog hsub.le j hj hjp
  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  let y : Fin (N + 1) → Ip.ResidueField := fun i => ψ (ratio hj i)
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    change ψ (ratio hj i) = 0
    rw [h0, map_zero]
  have hpy : primeOf (S := k) y = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) y := hpy ▸ hsub.le
  have hsubW : IsSubvar y pp e := ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩
  have hyj : y j ≠ 0 := fun h0 => hjp (hpy ▸ (mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0))
  have hy0 : y ≠ 0 := fun h => hyj (congrFun h j)

  set I := pp.comap (oneBlock (S := k) (N := N)) with hI_def
  have hI : I = primeOfOne (S := k) y := by rw [primeOfOne, hpy]
  have hIp : NumbersDVR.IsMultiProjPrime I := hI ▸ isMultiProjPrime_primeOfOne y hy0
  have hIdim : FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, hI, HilbertPositive.ringKrullDim_primeOfOne, hpy,
      hsub.dim]
    simp
  let H : ℤ → ℤ := fun m => NumbersDVR.hilbFn I (fun _ : Unit => m)
  let R : ℤ → ℤ := fun m => restrLen pp (twistSys k x m)

  have hY : ∀ᶠ n : ℕ in atTop, restrLen pp (twistSys k y (n : ℤ)) = H n := by
    filter_upwards [TwistSections.full k _ N y hy0] with n hn
    rw [← hpy, restrLen_primeOf_eq_finrank y hyj, hn, HilbertPositive.finrank_piece_eq_hilbFn, ← hI]

  obtain ⟨r₀, hr₀⟩ := RestrictTwist.full.1 k Ω N x _ y hxy hxy' 0
  have hXY := hRL k Ω N x _ y hxy hxy' pp e hsubW (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have hRH : ∀ᶠ n : ℕ in atTop, R n = H n := by
    filter_upwards [hY, hXY] with n h1 h2
    have e1 : (twistBundle k y 0).toSubSystem = twistSys k y 0 := rfl
    have e2 : (twistBundle k x 0).toSubSystem = twistSys k x 0 := rfl
    rw [e1, e2, twistSys_zero_twist, twistSys_zero_twist] at h2
    rw [← h1, h2]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hRH
  have hRH' : ∀ m : ℤ, (n₀ : ℤ) ≤ m → R m = H m := by
    intro m hm
    have h := hn₀ m.toNat (by omega)
    rwa [Int.toNat_of_nonneg (by omega)] at h

  let bs : Fin e → Unit → ℤ := fun i _ => b i
  have hMD := (FieldNumbers.MixedDiffConst.full k Unit (fun _ => Fin (N + 1)) I hIp.multiHomog hIp.relevant e
    hIdim).1 bs
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hMD
  set B : ℤ := ∑ i, b i with hB
  have hev : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => twistSys k x (b i)) c = NumbersDVR.intNum k I bs := by
    filter_upwards [eventually_ge_atTop (m₀ () - B).toNat,
      eventually_all.mpr fun T : Finset (Fin e) => eventually_ge_atTop ((n₀ : ℤ) - ∑ i ∈ T, b i).toNat]
      with c hc1 hc2
    rw [interSum_twistSys, ← hm₀ (fun _ => (c : ℤ) + B) (fun u => by cases u; change m₀ () ≤ (c : ℤ) + B; omega),
      mixedDiff_eq_sum]
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hsum : (∑ i ∈ Tᶜ, bs i) = fun _ : Unit => ∑ i ∈ Tᶜ, b i := by
      funext u
      rw [Finset.sum_apply]
    have hc : (n₀ : ℤ) ≤ ∑ i ∈ T, b i + c := by have := hc2 T; omega
    have hsplit := Finset.sum_add_sum_compl T b
    have hcard : Tᶜ.card = e - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    rw [show restrLen pp (twistSys k x (∑ i ∈ T, b i + c)) = H (∑ i ∈ T, b i + c) from hRH' _ hc, hsum, hcard]
    change (-1) ^ (e - T.card) * H (∑ i ∈ T, b i + c) =
      (-1) ^ (e - T.card) * NumbersDVR.hilbFn I ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i)
    have hfun : ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i) =
        fun _ : Unit => ∑ i ∈ T, b i + c := by
      funext u
      simp only [Pi.sub_apply]
      omega
    rw [hfun]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hev.mono fun c h => h.symm)).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XNotMemMIdealOver
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

def SectionRatio.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W →
      mIdealOver k (graphVec x s) ≤ W → ∀ j b : Fin m,
        (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W →
        ∃ (d : ℕ) (f g : Kleiman.Poly k N), f.IsHomogeneous d ∧ g.IsHomogeneous d ∧
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g ∉ W ∧
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g * X ⟨Sum.inr (), b⟩ -
            rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f * X ⟨Sum.inr (), j⟩ ∈ W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

