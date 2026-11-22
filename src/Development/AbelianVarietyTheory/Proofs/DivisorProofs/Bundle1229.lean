import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactOfComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixFrameAtPrimitiveRootFactor

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDimStableIsSumOfKTypes
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS
open scoped InnerProductSpace Matrix

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sumTypes_conjT_mem {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : gᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hg
  refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hu), ?_⟩
  have h := congrArg Matrix.conjTranspose hc
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at h
  exact h.symm

theorem sumTypes_mul_conjT {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g * gᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hg.1

theorem sumTypes_inner {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) (r v : H) :
    ⟪r, σ g v⟫_ℂ = ⟪σ gᴴ r, v⟫_ℂ := by
  have hK := Formalism.REAL.kFacts n ε
  have hgU : g ∈ UJset ε := hK.1 g hg
  have hgU' : gᴴ ∈ UJset ε := hK.1 _ (sumTypes_conjT_mem hg)
  let f : H →ₗᵢ[ℂ] H := { (σ g : H →ₗ[ℂ] H) with norm_map' := hσ.2.1 g hgU }
  have e : σ g (σ gᴴ r) = r := by
    have h1 := hσ.1.2 g hgU gᴴ hgU'
    rw [sumTypes_mul_conjT hg, hσ.1.1] at h1
    have := congrArg (fun T : H →L[ℂ] H => T r) h1
    simpa using this.symm
  calc ⟪r, σ g v⟫_ℂ = ⟪f (σ gᴴ r), f v⟫_ℂ := by
        show ⟪r, σ g v⟫_ℂ = ⟪σ g (σ gᴴ r), σ g v⟫_ℂ
        rw [e]
    _ = ⟪σ gᴴ r, v⟫_ℂ := f.inner_map_map _ _

theorem finDimStable_isSumOfKTypes : SumTypes := by
  intro n ε H _ _ σ hσ S hSfd hSK
  set R : Submodule ℂ H := sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} with hR
  have hRS : R ≤ S := sSup_le fun S' hS' => hS'.1
  have : FiniteDimensional ℂ R := Submodule.finiteDimensional_of_le hRS
  have hRK : Formalism.MainNotions.S.IsKStableOn ε σ R := by
    intro g hg v hv
    have hle : R ≤ Submodule.comap (σ g : H →ₗ[ℂ] H) R := sSup_le fun S' hS' x hx => by
      obtain ⟨μ, hμ⟩ := hS'.2
      exact Submodule.mem_sSup_of_mem hS' (hμ.2.1 g hg x hx)
    exact hle hv
  have hRoK : Formalism.MainNotions.S.IsKStableOn ε σ Rᗮ := by
    intro g hg v hv r hr
    rw [sumTypes_inner hσ hg]
    exact hv _ (hRK _ (sumTypes_conjT_mem hg) r hr)
  set T : Submodule ℂ H := S ⊓ Rᗮ
  have hT : T = ⊥ := by
    by_contra h0
    have : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨μ, S', hS'T, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ T inferInstance
      (fun g hg v hv => Submodule.mem_inf.2 ⟨hSK g hg v (Submodule.mem_inf.1 hv).1, hRoK g hg v (Submodule.mem_inf.1 hv).2⟩) h0
    obtain ⟨v, hv, hv0, -⟩ := hS'.2.2.2.1
    have hvR : v ∈ R := Submodule.mem_sSup_of_mem (show S' ∈ {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} from ⟨hS'T.trans inf_le_left, μ, hS'⟩) hv
    have hvRo : v ∈ Rᗮ := (hS'T hv).2
    exact hv0 (inner_self_eq_zero.1 (hvRo v hvR))
  intro v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := R.exists_add_mem_mem_orthogonal v
  have hzS : z ∈ S := by
    have := sub_mem hv (hRS hy)
    simpa using this
  have hz0 : z ∈ T := ⟨hzS, hz⟩
  rw [hT, Submodule.mem_bot] at hz0
  rw [hz0, add_zero]
  exact hy

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eq_of_toSub_eq {G : Type} [Group G] {H : Subgroup G} {g h : G} (hg : g ∈ H) (hh : h ∈ H)
    (e : toSub H g = toSub H h) : g = h := by
  unfold toSub at e
  rw [dif_pos hg, dif_pos hh] at e
  exact congrArg Subtype.val e

theorem under_conjSrc (w : Pl E) :
    (conjSrc (GlobalTheory.SplitPts.conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
    (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))

theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  by_contra h
  exact hw ⟨_, h, under_conjSrc w⟩

theorem ext_cj (w : Pl E) (a : Af E) : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
    Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      f (pLoc E v a) = cj w (pLoc E w a) := by
  rintro v rfl f hf h
  have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
  have hcj : cj v = hex.choose := by unfold cj; rw [dif_pos hex]
  rw [hcj]
  exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
    (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _

theorem cLoc_mem_UL {w : Pl E} (hw : ¬ IsSplitAt w) (x : UA E n) : cLoc w x ∈ UL n w := by
  have hUL : UL n w = UJ (cj w) 1 := by unfold UL; rw [if_neg hw]
  rw [hUL]
  show cT (cj w) (cLoc w x).val * 1 * (cLoc w x).val = 1
  have hc := GlobalTheory.SplitPts.comp_eq x w
  have e : (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) =
      (cLoc w x).val.map (cj w) := by
    refine Matrix.ext fun i j => ?_
    exact ext_cj w (pFin E (x.1.val i j)) _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec _ w).1
      (conjLoc_spec _ w).2.1
  rw [e] at hc
  rw [Matrix.mul_one]
  exact hc

theorem cLoc_conj_eq (w : Pl E) (x y : UA E n) (h : cLoc w x = cLoc w y) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y := by
  have hx := GlobalTheory.SplitPts.comp_eq x w
  have hy := GlobalTheory.SplitPts.comp_eq y w
  rw [h] at hx
  have e : ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ =
      ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ := by
    have h1 := mul_eq_one_comm.1 hx
    have h2 := mul_eq_one_comm.1 hy
    calc _ = ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ *
            ((cLoc w y).val * ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map
              (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ) := by rw [← Matrix.mul_assoc, hy, Matrix.one_mul]
      _ = _ := by rw [h1, Matrix.mul_one]
  refine Units.ext (Matrix.ext fun i j => (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective ?_)
  have := congrFun (congrFun e j) i
  simpa using this

end GlobalTheory.LocInj

open GlobalTheory.LocInj in
theorem GlobalTheory.BCT.finU_eq_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ S : Set (Pl E), IsSection S → ∀ x y : finU E n,
      (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  intro E _ _ _ _ n S hS x y hxy

  have hS' : ∀ w ∈ S, cLoc w (x : UA E n) = cLoc w (y : UA E n) := by
    intro w hw
    by_cases hsp : IsSplitAt w
    · have hUL : ∀ g, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hsp]; trivial
      exact eq_of_toSub_eq (hUL _) (hUL _) (hxy w hw)
    · exact eq_of_toSub_eq (cLoc_mem_UL hsp _) (cLoc_mem_UL hsp _) (hxy w hw)

  have hall : ∀ u : Pl E, cLoc u (x : UA E n) = cLoc u (y : UA E n) := by
    intro u
    obtain ⟨s, ⟨hsS, hsu⟩, -⟩ := hS u
    by_cases hus : u = s
    · subst hus; exact hS' u hsS
    · have hsp : IsSplitAt s := ⟨u, hus, hsu.symm⟩
      obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
      rcases hover u hsu.symm with h | h
      · exact absurd h hus
      · subst h; exact cLoc_conj_eq s _ _ (hS' s hsS)
  have hxi : cInf (x : UA E n) = 1 := MonoidHom.mem_ker.1 x.2
  have hyi : cInf (y : UA E n) = 1 := MonoidHom.mem_ker.1 y.2
  refine Subtype.ext (Subtype.ext (ga_ext (hxi.trans hyi.symm) ?_))
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
  exact congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUn
section
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocMem

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjSrc_eq_of_not_split (w : Pl E) (hw : ¬ IsSplitAt w) :
    conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
  set c : E ≃+* E := (IsCMField.complexConj E).toRingEquiv
  set u := conjSrc c w with hu
  have h : GlobalTheory.Mem.Chr.ConjPl c u w := conjPl_conjSrc c w
  by_contra hne
  apply hw
  refine ⟨u, hne, ?_⟩
  apply HeightOneSpectrum.ext
  ext y
  change algebraMap _ _ y ∈ u.asIdeal ↔ algebraMap _ _ y ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have hfix : c ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) =
      ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) := by
    change IsCMField.complexConj E _ = _
    rw [IsCMField.complexConj_eq_self_iff]
    exact ((y : maximalRealSubfield E)).2
  rw [← h, hfix]

theorem eq_cj_of_ext (w u : Pl E) (hu : u = w) (f : u.adicCompletion E →+* w.adicCompletion E) (hf : Continuous f)
    (hext : ∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) (b : Af E) :
    f (pLoc E u b) = cj w (pLoc E w b) := by
  subst hu
  have hex : ∃ s : u.adicCompletion E →+* u.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, hext⟩
  have hcj : cj u = hex.choose := by
    unfold cj
    rw [dif_pos hex]
  have hfs : (f : u.adicCompletion E → u.adicCompletion E) = hex.choose :=
    (HeightOneSpectrum.denseRange_algebraMap E u).equalizer hf hex.choose_spec.1
      (funext fun k => by simp only [Function.comp_apply, hext, hex.choose_spec.2])
  rw [hcj, ← hfs]

theorem cj_pLoc_pFin (w : Pl E) (hw : ¬ IsSplitAt w) (a : Ad E) :
    cj w (pLoc E w (pFin E a)) = pLoc E w (pFin E (conjAd E a)) := by
  change _ = pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E a))
  rw [pLoc_conjFin]
  exact (eq_cj_of_ext w _ (conjSrc_eq_of_not_split w hw) _ (conjLoc_spec _ w).1
    (fun k => (conjLoc_spec _ w).2.1 k) (pFin E a)).symm

end GlobalTheory.BCT.LocMem

open GlobalTheory.BCT.LocMem in

theorem GlobalTheory.BCT.cLoc_mem_UL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ (w : Pl E) (x : finU E n), cLoc w (x : UA E n) ∈ UL n w := by
  intro E _ _ _ _ n w x
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  have hx : cT (conjAd E) ((x : UA E n) : GA E n).val * 1 * ((x : UA E n) : GA E n).val = 1 := (x : UA E n).2
  set φ : Ad E →+* w.adicCompletion E := (pLoc E w).comp (pFin E)
  have hval : (cLoc w (x : UA E n)).val = φ.mapMatrix ((x : UA E n) : GA E n).val := rfl
  have hcT : cT (cj w) (φ.mapMatrix ((x : UA E n) : GA E n).val) =
      φ.mapMatrix (cT (conjAd E) ((x : UA E n) : GA E n).val) := by
    refine Matrix.ext fun i j => ?_
    exact cj_pLoc_pFin w hs _
  change cT (cj w) (cLoc w (x : UA E n)).val * 1 * (cLoc w (x : UA E n)).val = 1
  rw [hval, hcT, ← map_one φ.mapMatrix, ← map_mul, ← map_mul, hx]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodEqFinprodMemFibresOfSection
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_eq_finprod_mem_fibres_of_section :
    ∀ {α γ M : Type} [CommMonoid M] (p : α → γ) (S : Set α) (f : α → M),
      (∀ x, ∃! s, s ∈ S ∧ p s = p x) → (Function.mulSupport f).Finite →
        ∏ᶠ x, f x = ∏ᶠ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x := by
  intro α γ M _ p S f hS hf
  choose g hg using fun x => (hS x).exists
  have key : ∀ s ∈ S, ∀ x, p x = p s ↔ g x = s := by
    intro s hs x
    constructor
    · intro h
      exact (hS x).unique (hg x) ⟨hs, h.symm⟩
    · rintro rfl
      exact (hg x).2.symm
  set T := hf.toFinset with hT
  have hin : ∀ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x = ∏ x ∈ T with g x = s, f x := by
    intro s hs
    apply finprod_mem_eq_prod_of_subset
    · rintro x ⟨hx1, hx2⟩
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hT, Set.Finite.mem_toFinset]
      exact ⟨hx2, (key s hs x).1 hx1⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact (key s hs x).2 hx.2
  rw [finprod_mem_congr rfl hin, finprod_eq_prod_of_mulSupport_subset f (s := T) (by simp [hT])]
  rw [finprod_mem_eq_prod_of_subset (t := T.image g)]
  · exact (Finset.prod_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem g hi) f).symm
  · rintro s ⟨_, hs⟩
    rw [Function.mem_mulSupport] at hs
    obtain ⟨u, hu, _⟩ := Finset.exists_ne_one_of_prod_ne_one hs
    rw [Finset.mem_filter] at hu
    rw [Finset.coe_image]
    exact ⟨u, hu.1, hu.2⟩
  · intro s hs
    rw [Finset.coe_image] at hs
    obtain ⟨u, _, rfl⟩ := hs
    exact (hg u).1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramified
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.UnitLemma

theorem UQ.norm_of_fixed_unit {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (w w' : E) (hs : star w = w) (h1 : ‖w‖ ≤ 1)
    (h1' : ‖w'‖ ≤ 1) (hww : w * w' = 1) : ∃ v : E, v * star v = w := by
  obtain ⟨ζ, -, hζ⟩ := GlobalTheory.NormUnits.exists_far_unit F E
  obtain ⟨a, ha⟩ := GlobalTheory.NormUnits.fixed_mem_range F E ζ hζ w hs
  have hprod : ‖w‖ * ‖w'‖ = 1 := by rw [← norm_mul, hww, norm_one]
  have hwn : ‖w‖ = 1 := by
    refine le_antisymm h1 ?_
    by_contra h
    push_neg at h
    have : ‖w‖ * ‖w'‖ < 1 :=
      calc ‖w‖ * ‖w'‖ ≤ ‖w‖ * 1 := by gcongr
        _ < 1 := by simpa using h
    linarith
  have han : ‖a‖ = 1 := by rw [← norm_algebraMap' E a, ha, hwn]
  obtain ⟨v, hv⟩ := GlobalTheory.NormUnits.norm_onto_units F E a han
  exact ⟨v, by rw [hv, ha]⟩

theorem UQ.unit_fixed_is_norm : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  intro K t ht hct
  obtain ⟨F, nF, nE, hE, nA, st, hU, hst, hball⟩ := K.exists_unram
  have hmul : ∀ x y : K.E, @HMul.hMul K.E K.E K.E (@instHMul K.E nE.toMul) x y = x * y := by
    intro x y; rw [← hE]
  have hone : @OfNat.ofNat K.E 1 (@One.toOfNat1 K.E nE.toOne) = 1 := by rw [← hE]
  obtain ⟨u, rfl⟩ := ht
  have hww : algebraMap K.O K.E u * algebraMap K.O K.E (u⁻¹ : K.Oˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨v, hv⟩ := @UQ.norm_of_fixed_unit F K.E nF nE nA st hU (algebraMap K.O K.E u)
    (algebraMap K.O K.E (u⁻¹ : K.Oˣ)) (by rw [hst]; exact hct) ((hball _).2 ⟨u, rfl⟩) ((hball _).2 ⟨_, rfl⟩)
    (by rw [hmul, hone]; exact hww)
  refine ⟨v, ?_⟩
  rw [← hst, ← hmul]; exact hv

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlacesStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_unit_eq_norm_almost_all_places : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  first | (exact @GlobalTheory.LocNorm.unit_fixed_is_norm) | (exact GlobalTheory.LocNorm.unit_fixed_is_norm) | (intros; apply GlobalTheory.LocNorm.unit_fixed_is_norm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCellStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_point_in_some_cell : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)) (x : Part a l), ∃ w : ι → Equiv.Perm (Fin N), x ∈ Set.range (cell a l w) := by
  first | exact @GlobalTheory.FlagZ.exists_mem_range_cell | exact GlobalTheory.FlagZ.exists_mem_range_cell | (intros; apply GlobalTheory.FlagZ.exists_mem_range_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSubalgebraMvPolynomialEvalOfFlatAeval
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

theorem flat_polyMap_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  intro K κ' _ _ _ _ A m v h
  have h1 : (Algebra.TensorProduct.map (AlgHom.id ℂ κ')
      (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A)).toRingHom.Flat :=
    RingHom.Flat.tensorProductMap (f := AlgHom.id ℂ κ') (RingHom.Flat.id κ') h
  let e1 := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm.toRingEquiv
  let e2 := ((Algebra.TensorProduct.comm ℂ κ' A).trans (tensEquiv (κ' := κ') A)).toRingEquiv
  have h2 := ((RingHom.Flat.of_bijective (f := e1.toRingHom) e1.bijective).comp h1).comp
    (RingHom.Flat.of_bijective (f := e2.toRingHom) e2.bijective)
  convert h2 using 1
  refine MvPolynomial.ringHom_ext (fun b => Subtype.ext ?_) (fun i => Subtype.ext ?_)
  · have : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm (MvPolynomial.C b)
        = b ⊗ₜ 1 := by
      rw [AlgEquiv.symm_apply_eq]; simp [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
    simp [e1, e2, tensMap, this]
  · simp [e1, e2, tensMap]

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdFreeTopFormEqZeroOfIsPrimeOfStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrd_freeTopForm_eq_zero_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd (dForm cL (fun i => (x i : L))) = 0 := by
  first | exact @GlobalTheory.formOrd_dForm_of_isPrimeOf | exact GlobalTheory.formOrd_dForm_of_isPrimeOf | (intros; apply GlobalTheory.formOrd_dForm_of_isPrimeOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdKaehlerWedgeUniformiserResidueIndependent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_cons_of_ord_eq_one : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  F.formOrd (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  intro K _ cK F m π y hπ hy hP hB
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by rw [hπ]; norm_num)
  have hirr : Irreducible (⟨π, hπm⟩ : F.ring) := by
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible F.ring
    have hne : (⟨π, hπm⟩ : F.ring) ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne ht
    have e : π = ((u : F.ring) : K) * (t : K) ^ n := by
      simpa using congrArg Subtype.val hu
    have hu0 : ((u : F.ring) : K) ≠ 0 := (u.isUnit.map F.ring.subtype).ne_zero
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have h1 : F.ord π = n := by
      rw [e, F.ord_mul hu0 (pow_ne_zero _ ht0), F.ord_eq_zero u.isUnit, F.ord_pow,
        F.ord_irreducible ht]
      simp
    obtain rfl : n = 1 := by
      rw [hπ] at h1
      exact_mod_cast h1.symm
    rw [hu, pow_one]
    exact (irreducible_units_mul u).2 ht
  refine formOrd_dForm_uniformiser_cons cK m F ⟨π, hπm⟩ (fun i => ⟨y i, hy i⟩) hirr ?_ ⟨_, hB⟩
  intro P hP0
  obtain ⟨h0, hi⟩ := hP P hP0
  have e : ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) =
      MvPolynomial.eval₂ cK y P :=
    MvPolynomial.eval₂_comp_left F.ring.subtype F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P
  refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : F.ring) (Subtype.ext ?_)
  change ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) * _ = 1
  rw [e]
  exact mul_inv_cancel₀ h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixCofactorEqQPowFrameStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusMatrix_cofactor_eq_q_pow_frame : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n h : ℕ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h : ℤ)) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → ∀ i, ∃ Q : Mx (PowerSeries ↥(OL LL)) n n, (N.P i).map (inc l ↥(OL LL)) * Q = (q l ↥(OL LL) ^ h) • (1 : Mx (PowerSeries ↥(OL LL)) n n) := by
  first | exact @GlobalTheory.WachPlace.FrameHeight.frame_height | exact GlobalTheory.WachPlace.FrameHeight.frame_height | (intros; apply GlobalTheory.WachPlace.FrameHeight.frame_height <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixFrameAtPrimitiveRootFactorStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusMatrix_frame_at_primitiveRoot_factor : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n : ℕ) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin n → ℤ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (u c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ (fun i => Finset.univ.val.map (U i)) → (∀ i a, 0 ≤ U i a) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → (((HW l).W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → u = 1 + (l : ℤ_[l]) * c → IsPrimitiveRoot ζ l → IsExpAt (OL LL).val.toRingHom ζ jj → ∀ i, ∃ G H : (Mx (PowerSeries ↥LL.1) n n)ˣ, (N.P i).map (fun y => jj (inc l ↥(OL LL) y)) = (G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat) * (H : Mx (PowerSeries ↥LL.1) n n) ∧ ((1 + (X : PowerSeries ↥(OL LL)) • N.D i).map (fun y => jj (inc l ↥(OL LL) y))) * ((G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat)).map (rescale ((OL LL).val.toRingHom (algebraMap ℤ_[l] ↥(OL LL) u))) = (G : Mx (PowerSeries ↥LL.1) n n) * Matrix.diagonal (fun a => (X : PowerSeries ↥LL.1) ^ (U i a).toNat) := by
  first | exact @GlobalTheory.WachRoots.frame_at_root | exact GlobalTheory.WachRoots.frame_at_root | (intros; apply GlobalTheory.WachRoots.frame_at_root <;> assumption)
end

