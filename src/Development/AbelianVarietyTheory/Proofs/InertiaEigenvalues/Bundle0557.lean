import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0412
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCompletedLocalizationPrism
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem locAway_φ_mem {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) :
    ∀ x ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f),
      D.φ x ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f) := by
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    exact Submonoid.subset_closure ⟨m + 1, by simp only [Function.iterate_succ_apply']⟩
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

theorem locAway_iterate_sub_mem {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) (m : ℕ) :
    D.φ^[m] f - f ^ (l ^ m) ∈ Ideal.span {(l : A)} := by
  rw [← Ideal.Quotient.eq]
  induction m with
  | zero => simp
  | succ m ih =>
    have hl0 : ((l : A ⧸ Ideal.span {(l : A)})) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : A)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    rw [Function.iterate_succ_apply', D.φ_eq, map_add, map_mul, map_pow, ih, map_natCast, hl0, zero_mul,
      add_zero, map_pow, map_pow, ← pow_mul, pow_succ]

theorem locAway_dvd_mod {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) (J : Ideal A)
    (hl : (l : A) ∈ J) (n : ℕ) :
    ∀ s ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f), ∃ (k : ℕ) (t : A), f ^ k - s * t ∈ J ^ n := by
  intro s hs
  induction hs using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    have h1 : f ^ (l ^ m) - D.φ^[m] f ∈ J := by
      rw [← neg_sub, neg_mem_iff]
      exact (Ideal.span_le.2 (Set.singleton_subset_iff.2 hl)) (locAway_iterate_sub_mem D f m)
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow (f ^ (l ^ m)) (f ^ (l ^ m) - D.φ^[m] f) n
    refine ⟨l ^ m * n, t, ?_⟩
    have e : f ^ (l ^ m * n) - D.φ^[m] f * t = (f ^ (l ^ m) - D.φ^[m] f) ^ n := by
      rw [pow_mul]
      have e2 : f ^ l ^ m - (f ^ l ^ m - D.φ^[m] f) = D.φ^[m] f := by ring
      rw [e2] at ht
      linear_combination ht
    rw [e]; exact Ideal.pow_mem_pow h1 n
  | one => exact ⟨0, 1, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k1, t1, h1⟩ := hx
    obtain ⟨k2, t2, h2⟩ := hy
    refine ⟨k1 + k2, t1 * t2, ?_⟩
    have e : f ^ (k1 + k2) - x * y * (t1 * t2) = f ^ k1 * (f ^ k2 - y * t2) + y * t2 * (f ^ k1 - x * t1) := by
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)

theorem locAway_units {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} (g : Hom B C) (f : B.A)
    (hu : IsUnit (g.f f)) :
    ∀ s ∈ Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f), IsUnit (g.f s) := by
  intro s hs
  induction hs using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      show IsUnit (g.f (B.D.φ^[m + 1] f))
      change IsUnit (g.f (B.D.φ^[m] f)) at ih
      rw [Function.iterate_succ_apply', g.f_φ]
      exact ih.map C.D.φ
  | one => rw [map_one]; exact isUnit_one
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem GenAway₂ : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A),
    GenAway B f d → Nonempty (LocP B f d) := by
  intro l _ R _ B f d hg
  set M := Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f) with hM
  have hfM : f ∈ M := Submonoid.subset_closure ⟨0, rfl⟩
  obtain ⟨DL, hDL⟩ := GlobalTheory.T.exists_deltaRingStructure_localization l B.A B.D M (locAway_φ_mem B.D f)
  obtain ⟨hIL, hdnz, N, hN⟩ := GlobalTheory.T.prismLocalization_span_nonZeroDivisor_bounded_torsion l R B f d hg M hfM
  set J : Ideal (Localization M) := Ideal.span {(l : Localization M)} ⊔
    Ideal.span {algebraMap B.A (Localization M) d} with hJdef
  have hJ : (JJ B).map (algebraMap B.A (Localization M)) = J := by
    rw [JJ, Ideal.map_sup, hIL, Ideal.map_span, Set.image_singleton, map_natCast]
  have hJfg : J.FG := Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)
  obtain ⟨Q, _, i, hi⟩ := GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ J hJfg
  have hlJ : (l : Localization M) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  obtain ⟨DQ, hDQ⟩ := GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q i J hi hlJ DL
  obtain ⟨hqnz, hqN⟩ := GlobalTheory.T.adic_completion_regular_and_torsion_bounded l _ Q i (algebraMap B.A (Localization M) d) N hdnz hN hi
  set g : B.A →+* Q := i.comp (algebraMap B.A (Localization M)) with hgdef
  have hgδ : ∀ x, g (B.D.δ x) = DQ.δ (g x) := fun x => by
    simp only [hgdef, RingHom.comp_apply]; rw [hDL x, hDQ]
  have hIg : B.I.map g = Ideal.span {g d} := by
    rw [hgdef, ← Ideal.map_map, hIL, Ideal.map_span, Set.image_singleton]; rfl
  have hIle : B.I ≤ (Ideal.span {g d}).comap g := Ideal.map_le_iff_le_comap.1 hIg.le
  have hJi : J.map i = Ideal.span {(l : Q)} ⊔ Ideal.span {g d} := by
    rw [hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      map_natCast]; rfl
  have hcomp : IsAdicComplete (Ideal.span {(l : Q)} ⊔ Ideal.span {g d}) Q := by
    have := hi.complete; rwa [hJi] at this
  have hgφ : g.comp B.D.φ = DQ.φ.comp g := RingHom.ext fun x => Delta.map_φ_of_map_δ B.D DQ g hgδ x
  have hlmem : (l : Q) ∈ Ideal.span {g d} ⊔ (Ideal.span {g d}).map DQ.φ := by
    have h := Ideal.mem_map_of_mem g B.l_mem
    have hgm : (B.I.map B.D.φ).map g = (B.I.map g).map DQ.φ := by
      rw [Ideal.map_map, Ideal.map_map, hgφ]
    rwa [map_natCast, Ideal.map_sup, hgm, hIg] at h
  have hbdd : ∃ n : ℕ, ∀ x : Q ⧸ Ideal.span {g d}, (∃ m : ℕ, (l : Q ⧸ Ideal.span {g d}) ^ m * x = 0) →
      (l : Q ⧸ Ideal.span {g d}) ^ n * x = 0 := by
    refine ⟨N, fun x ⟨m, hm⟩ => ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm ⊢
    exact hqN y m hm
  let Qo : Obj l R :=
    { A := Q
      D := DQ
      I := Ideal.span {g d}
      inv := invertible_span_singleton hqnz
      complete := hcomp
      l_mem := hlmem
      bdd := hbdd
      str := (Ideal.quotientMap (Ideal.span {g d}) g hIle).comp B.str }
  let inl : Hom B Qo :=
    { f := g
      f_δ := hgδ
      f_I := fun x hx => hIle hx
      f_str := fun r x h => by
        show _ = Ideal.quotientMap (Ideal.span {g d}) g hIle (B.str r)
        rw [← h, Ideal.quotientMap_mk] }
  have hlu : ∀ s : M, IsUnit (g s) := fun s => (IsLocalization.map_units (Localization M) s).map i
  have hJn : ∀ n : ℕ, ((JJ B) ^ n).map g = (J ^ n).map i := fun n => by
    rw [hgdef, ← Ideal.map_map, Ideal.map_pow, hJ]
  have hlJB : (l : B.A) ∈ JJ B := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  refine ⟨{ Q := Qo, inl := inl, unit := ?_, I_eq := rfl, univ := ?_, surj := ?_, ker := ?_ }⟩
  · exact hlu ⟨f, hfM⟩
  · intro C gC hu
    have hMu : ∀ s : M, IsUnit (gC.f s) := fun s => locAway_units gC f hu s s.2
    set lift : Localization M →+* C.A := IsLocalization.lift hMu with hliftdef
    have hla : ∀ x, lift (algebraMap B.A (Localization M) x) = gC.f x := IsLocalization.lift_eq hMu
    have hδl : IsδMap DL C.D lift := by
      have e : (W2.map lift).comp (deltaSectionToWittLengthTwo DL) = (deltaSectionToWittLengthTwo C.D).comp lift := by
        apply IsLocalization.ringHom_ext M
        refine RingHom.ext fun x => W2.ext rfl ?_
        change lift (DL.δ (algebraMap B.A (Localization M) x)) =
          C.D.δ (lift (algebraMap B.A (Localization M) x))
        rw [← hDL x, hla, hla, gC.f_δ]
      intro x; exact congrArg W2.snd (RingHom.congr_fun e x)
    have hJle : J.map lift ≤ JJ C := by
      rw [hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        map_natCast, hla]
      exact sup_le_sup_left (Ideal.span_le.2 (Set.singleton_subset_iff.2 (gC.f_I d hg.1))) _
    haveI := C.complete
    have hhaus : IsHausdorff (JJ C) C.A := inferInstance
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C.A i J (JJ C) hi C.complete lift hJle
    have hhi : ∀ y, h (i y) = lift y := fun y => RingHom.congr_fun hh y
    have hδh : IsδMap DQ C.D h := by
      refine GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C.A DQ C.D (J.map i) (JJ C) h ?_ ?_ hhaus ?_
      · rw [← map_natCast i]; exact Ideal.mem_map_of_mem i hlJ
      · rw [Ideal.map_map, hh]; exact hJle
      · intro x n
        obtain ⟨y, hy⟩ := hi.surj x n
        refine ⟨i y, mem_δLocus.2 ?_, by rwa [← Ideal.map_pow]⟩
        rw [← hDQ y, hhi, hhi, hδl]
    have hgC : h.comp g = gC.f := by rw [hgdef, ← RingHom.comp_assoc, hh, IsLocalization.lift_comp]
    have hIC : ∀ x ∈ Ideal.span {g d}, h x ∈ C.I := fun x hx =>
      (Ideal.span_le (I := C.I.comap h)).2 (Set.singleton_subset_iff.2 (by
        show h (g d) ∈ C.I
        rw [← RingHom.comp_apply h g, hgC]; exact gC.f_I d hg.1)) hx
    let H : Hom Qo C :=
      { f := h
        f_δ := hδh
        f_I := hIC
        f_str := fun r x hx => by
          obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (B.str r)
          change Ideal.Quotient.mk _ x = Ideal.quotientMap _ g hIle (B.str r) at hx
          rw [← hb, Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
          rw [← gC.f_str r b hb, Ideal.Quotient.eq, ← hgC, RingHom.comp_apply, ← map_sub]
          exact hIC _ hx }
    refine ⟨H, Hom.ext' hgC, fun y hy => Hom.ext' ?_⟩
    have hy' : y.f.comp g = gC.f := congrArg Hom.f hy
    have hyi : y.f.comp i = h.comp i := IsLocalization.ringHom_ext M (hy'.trans hgC.symm)
    exact GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap _ Q C.A i J (JJ C) hi hhaus y.f h (by rw [hyi, hh]; exact hJle) hyi
  · intro x n
    obtain ⟨y, hy⟩ := hi.surj x n
    obtain ⟨⟨b0, s⟩, hbs⟩ := IsLocalization.mk'_surjective M y
    dsimp only at hbs
    subst hbs
    obtain ⟨k, t, hkt⟩ := locAway_dvd_mod B.D f (JJ B) hlJB n s s.2
    refine ⟨k, b0 * t, ?_⟩
    change g f ^ k * x - g (b0 * t) ∈ ((JJ B) ^ n).map g
    have hs : i (IsLocalization.mk' (Localization M) b0 s) * g s = g b0 := by
      rw [hgdef, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    have e : g f ^ k * x - g (b0 * t) = g f ^ k * (x - i (IsLocalization.mk' (Localization M) b0 s)) +
        i (IsLocalization.mk' (Localization M) b0 s) * g (f ^ k - s * t) := by
      rw [map_sub, map_mul, map_mul, map_pow]; linear_combination (g t) * hs
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem g hkt))
    rw [hJn]; exact hy
  · intro b n hb
    change g b ∈ ((JJ B) ^ n).map g at hb
    rw [hJn] at hb
    have h1 := hi.ker _ n hb
    rw [← hJ, ← Ideal.map_pow] at h1
    obtain ⟨⟨⟨j, hj⟩, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff M (Localization M)).1 h1
    rw [← map_mul] at hjs
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 hjs
    have hcs : ((c : B.A) * (s : B.A)) * b ∈ JJ B ^ n := by
      have e : ((c : B.A) * (s : B.A)) * b = (c : B.A) * j := by rw [← hc]; ring
      rw [e]; exact Ideal.mul_mem_left _ _ hj
    obtain ⟨k, t, hkt⟩ := locAway_dvd_mod B.D f (JJ B) hlJB n ((c : B.A) * (s : B.A)) (M.mul_mem c.2 s.2)
    refine ⟨k, ?_⟩
    have e : f ^ k * b = (f ^ k - ((c : B.A) * (s : B.A)) * t) * b + t * (((c : B.A) * (s : B.A)) * b) := by ring
    rw [e]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hkt) (Ideal.mul_mem_left _ _ hcs)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperModCommutator
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

private lemma commutator_le_of_forall_commutator_mem {G : Type*} [Group G] (C : Subgroup G)
    (hC : ∀ σ τ : G, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ C :=
  Subgroup.commutator_le.2 fun a _ b _ => by
    rw [commutatorElement_def]
    exact hC a b

theorem pow_mem_upper_mod_commutator : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p e : ℕ) (v : ℝ) (C : Subgroup (L ≃ₐ[F] L)), (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F L v, ∃ τ ∈ upperRamificationGroup F L (min (2 * v) (v + e)), τ⁻¹ * σ ^ p ∈ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p e v C hC hv hpe σ hσ

  let H : Subgroup (L ≃ₐ[F] L) := ⁅(⊤ : Subgroup (L ≃ₐ[F] L)), ⊤⁆
  let Q : IntermediateField F L := IntermediateField.fixedField H
  haveI : IsGalois F Q := IsGalois.of_fixedField_normal_subgroup H
  have hker : (AlgEquiv.restrictNormalHom Q).ker = H := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_fixedField H
  have hab : ∀ s t : Q ≃ₐ[F] Q, s * t = t * s := by
    intro s t
    obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := L) s
    obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := L) t
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ (AlgEquiv.restrictNormalHom Q).ker := by
      rw [hker]
      have h := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rwa [commutatorElement_def] at h
    rw [MonoidHom.mem_ker] at hmem
    simp only [map_mul, map_inv] at hmem
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
    exact hmem
  have hσQ : AlgEquiv.restrictNormalHom Q σ ∈ upperRamificationGroup F Q v := by
    rw [← GroundTheory.LocalField.map_upperRamificationGroup Q v]
    exact Subgroup.mem_map_of_mem _ hσ
  have hpow := GlobalTheory.T.pow_mem_upperRamificationGroup_of_comm' F Q p e v hab hv hpe _ hσQ
  rw [← map_pow, ← GroundTheory.LocalField.map_upperRamificationGroup Q] at hpow
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 hpow
  refine ⟨τ, hτ, commutator_le_of_forall_commutator_mem C hC ?_⟩
  have hk : τ⁻¹ * σ ^ p ∈ (AlgEquiv.restrictNormalHom Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτσ, inv_mul_cancel]
  rw [hker] at hk
  exact hk

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCrystalChangeOfBasisConstantCoeffEqOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.CrysDiag.eps_constantCoeff_eq_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (κ₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, κ₀ τ (δ.f y) = PowerSeries.constantCoeff (κ τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)).map PowerSeries.constantCoeff = 1 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  intro E jA hR hM oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ hκ Q _ c y hy τ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.crystal_basis_transport_free_over_prism l a e O K t ϖ ι P T I E jA hR hM oE hoE b hb
  have key : ∀ j, ∑ i, ∑ q, δ.f (y i j q) • (oE (c i j q)).u S₀ (E.tr (δ.comp p₀) (b i)) =
      ∑ i, ∑ _q : Unit, (if i = j then (1 : S₀.A) else 0) • (oE 1).u S₀ (E.tr (δ.comp p₀) (b i)) := by
    intro j
    have hfix : ∀ i, (oE 1).u S₀ (E.tr (δ.comp p₀) (b i)) = E.tr (δ.comp p₀) (b i) := fun i => by
      rw [(oE 1).u_tr, h1]
    simp only [hfix, ite_smul, one_smul, zero_smul, Finset.sum_const, Finset.card_univ, Fintype.card_unit]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    conv_rhs => rw [hδ, E.tr_comp, hy j]
    simp only [E.tr_comp, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => ?_
    rw [(oE (c i j q)).u_tr]
    exact ((E.tr δ).map_smulₛₗ _ _).symm
  have hC : ∀ w : Wq l a, (toAc t K (PowerSeries.C w) τ : K⟦X⟧) = PowerSeries.C (algebraMap O K (emb t τ w)) := by
    intro w
    ext n
    rw [coeff_toAc, PowerSeries.coeff_C, PowerSeries.coeff_C]
    split_ifs <;> simp
  have hψ : ∀ z : ℤ_[l], κ₀ τ ((δ.comp p₀).f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) =
      algebraMap O K⟦X⟧ (algebraMap ℤ_[l] O z) := by
    intro z
    change κ₀ τ (δ.f (p₀.f _)) = _
    rw [hκ₀, hκ, PowerSeries.algebraMap_apply, frobS_C, PowerSeries.constantCoeff_C, hC,
      AlgEquiv.commutes, AlgHom.commutes, PowerSeries.algebraMap_apply]
  refine Matrix.ext fun i j => ?_
  have hij := h2 S₀ (δ.comp p₀) Q Unit (fun i q => c i j q) (fun i q => δ.f (y i j q)) (fun _ _ => 1)
    (fun i _ => if i = j then (1 : S₀.A) else 0) (by simpa only [one_smul] using key j) K⟦X⟧ (κ₀ τ) hψ i
  simp only [hκ₀, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, apply_ite (κ₀ τ),
    map_one, map_zero] at hij
  rw [Matrix.map_apply, Matrix.of_apply, map_sum, Matrix.one_apply, ← hij]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
    PowerSeries.constantCoeff_C, PowerSeries.algebraMap_apply]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mk_one_eq_zero_iff_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (x : M) :
    LocalizedModule.mk x (1 : Submonoid.powers t) = 0 ↔ ∃ r : ℕ, t ^ r • x = 0 := by
  rw [← LocalizedModule.zero_mk (1 : Submonoid.powers t), LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, r, rfl⟩, h⟩
    exact ⟨r, by simpa [Submonoid.smul_def] using h⟩
  · rintro ⟨r, h⟩
    exact ⟨⟨t ^ r, r, rfl⟩, by simpa [Submonoid.smul_def] using h⟩

theorem exists_eq_mk_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A)
    (z : LocalizedModule (Submonoid.powers t) M) :
    ∃ (n : M) (k : ℕ), IsFrac t z n k := by
  induction z using LocalizedModule.induction_on with
  | _ n s =>
    obtain ⟨_, k, rfl⟩ := s
    exact ⟨n, k, rfl⟩

theorem mk_one_eq_pow_smul_of_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A)
    (z : LocalizedModule (Submonoid.powers t) M) (m : M) (k : ℕ) (h : IsFrac t z m k) :
    LocalizedModule.mk m (1 : Submonoid.powers t) = t ^ k • z := by
  rw [h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

theorem exists_pow_smul_eq_zero_of_sum {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    (t c : A) (m : M) (k : ℕ) (v : ι → A) (w : ι → M) (z : ι → LocalizedModule (Submonoid.powers t) M)
    (Z : LocalizedModule (Submonoid.powers t) M) (hm : IsFrac t Z m k) (hZ : Z = ∑ j, v j • z j)
    (hw : ∀ j, LocalizedModule.mk (w j) (1 : Submonoid.powers t) = c • z j) :
    ∃ r : ℕ, t ^ r • (c • m - t ^ k • ∑ j, v j • w j) = 0 := by
  rw [← mk_one_eq_zero_iff_pow_smul]
  have h1 := mk_one_eq_pow_smul_of_isFrac t Z m k hm
  have hlin : ∀ x : M, LocalizedModule.mk x (1 : Submonoid.powers t) =
      LocalizedModule.mkLinearMap (Submonoid.powers t) M x := fun _ => rfl
  rw [hlin, map_sub, map_smul, map_smul, map_sum]
  simp only [map_smul, ← hlin, hw, h1, hZ, Finset.smul_sum, smul_smul]
  rw [sub_eq_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← LocalizedModule.smul'_mk, hw, smul_smul, smul_smul]
  congr 1
  ring

theorem mk_tr_eq_smul_Φ_tr {l : ℕ} {R : Type} [CommRing R] (M : FCrys l R) {P P' : Obj l R} (f : Hom P P')
    (d : ↥P.I) (d' : ↥P'.I) (x mx : M.M P) (k : ℕ) (hreg : IsSMulRegular (M.M P') (f.f d))
    (h : IsFrac (d : P.A) (M.Φ P d x) mx k) :
    LocalizedModule.mk (M.tr f mx) (1 : Submonoid.powers (d' : P'.A)) = f.f d ^ k • M.Φ P' d' (M.tr f x) := by
  obtain ⟨n, s, hn⟩ := exists_eq_mk_pow (d' : P'.A) (M.Φ P' d' (M.tr f x))
  obtain ⟨r, hr⟩ := M.Φ_nat f d d' x mx k n s h hn
  rw [mul_pow, mul_smul] at hr
  have hr' := (hreg.pow r).right_eq_zero_of_smul hr
  rw [smul_sub, sub_eq_zero] at hr'
  rw [hn, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨⟨(d' : P'.A) ^ r, r, rfl⟩, ?_⟩
  simpa [Submonoid.smul_def] using hr'

theorem frob_tr_basis (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ) (A : Matrix (Fin d) (Fin d) bk.S)
    (hA : ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j))
      (∑ i, bk.toP (A i j) • e i) a)
    (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (t : ↥Q.I) (y : Fin d → Q.A) (m : M.M Q) (k : ℕ)
    (hm : IsFrac (t : Q.A) (M.Φ Q t (∑ j, y j • M.tr g (e j))) m k) :
    ∃ r : ℕ, (t : Q.A) ^ r • (BK.hf g bk.E ^ a • m - (t : Q.A) ^ k •
      ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i)) = 0 := by
  have hreg : IsSMulRegular (M.M Q) (BK.hf g bk.E) := by
    haveI := M.proj Q
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2

  have key : ∀ j : Fin d, LocalizedModule.mk (M.tr g (∑ i, bk.toP (A i j) • e i)) (1 : Submonoid.powers (t : Q.A)) =
      BK.hf g bk.E ^ a • M.Φ Q t (M.tr g (e j)) := fun j =>
    mk_tr_eq_smul_Φ_tr M g ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ t (e j) _ a hreg (hA j)
  have hsum : ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i) =
      ∑ j, Q.D.φ (y j) • M.tr g (∑ i, bk.toP (A i j) • e i) := by
    simp only [map_sum, LinearMap.map_smulₛₗ, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]; rfl
  have hΦ : M.Φ Q t (∑ j, y j • M.tr g (e j)) = ∑ j, Q.D.φ (y j) • M.Φ Q t (M.tr g (e j)) := by
    simp only [map_sum, LinearMap.map_smulₛₗ, RingHom.comp_apply, algebraMap_smul]
  rw [hsum]
  exact exists_pow_smul_eq_zero_of_sum (t : Q.A) (BK.hf g bk.E ^ a) m k (fun j => Q.D.φ (y j))
    (fun j => M.tr g (∑ i, bk.toP (A i j) • e i)) (fun j => M.Φ Q t (M.tr g (e j))) _ hm hΦ key

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.JointSix

theorem psiAt_psiW {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) :
    BlochKatoReduction.Gen.psiAt (C.sd w) (KillingConditions.psiW C w) = GlobalTheory.PtCore.psiG D C w := by
  unfold KillingConditions.psiW GlobalTheory.PtCore.psiG
  cases h : C.sd w
  · ext g
    simp [BlochKatoReduction.Gen.psiAt]
  · simp [BlochKatoReduction.Gen.psiAt]

theorem main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GlobalTheory.PtCore.PtFam D r ρ → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C →
    GlobalTheory.PtCore.GoodPtRow D → GlobalTheory.PtCore.ResAbsIrr D → KillingConditions.SignatureChoiceCondition ρ C := by
  intro hC D C r ρ hF hT hTr hS hG hR i _
  have hsel := GlobalTheory.PtSel.selCore hC D C hT hTr hG hR hS ρ
    (fun i π hπ => hF.pt i π (Formalism.L2.zgoodSub D i hπ))
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, h1, h2, h3, h4, -⟩ := hsel i π hπ
    refine ⟨s, h1, ?_⟩
    rw [h2, psiAt_psiW]
    exact ⟨h3, h4⟩
  · rw [Rat.cast_sum, ← hT.Q_eq i]
    exact Finset.sum_le_sum fun v hv => GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue D C hT i v hv

example : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C → GlobalTheory.PtCore.GoodPtRow D → GlobalTheory.PtCore.ResAbsIrr D → KillingConditions.SignatureChoiceCondition ρ C := main

end GlobalTheory.JointSix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.StrictAdm

theorem strict_adm : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm11 D := by
  intro D l _ K LL T₀ T₁ T₂ ι π hses hc
  obtain ⟨hi, hs, -, hk, -⟩ := hses
  have hT := D.locT l
  have hsq₀ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hi hc
  have hsq₂ := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2 hs hc).1
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K LL T₁.V T₁.ρ hc).1
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, hk x]
  have he := GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ
    ι.f π.f ι.equiv π.equiv hi hs hrk hdr
  exact ⟨hsq₀, hsq₂, fun τ a => (he.2.2 τ a).2.1⟩

end GlobalTheory.Per.StrictAdm
end

