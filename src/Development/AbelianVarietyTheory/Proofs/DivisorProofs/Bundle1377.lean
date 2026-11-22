import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1108

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicUnitRootsBoundedDenominatorNumberFiel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem monic_roots_norm_one_coeff_denom_finite : ∀ (E : Type) [Field E] [NumberField E] (n d : ℕ), d ≠ 0 → {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k}.Finite := by
  intro E _ _ n d hd
  set T := {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k} with hT
  set B : ℝ := max 1 1 ^ n * (n.choose (n / 2) : ℝ) with hB
  set S : Set E := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ) * B} with hS
  have hSf : S.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ ((d : ℝ) * B)
  let F : E[X] → (Fin (n+1) → E) := fun P k => (d : E) * P.coeff k
  have hpi : (Set.pi Set.univ (fun _ : Fin (n+1) => S)).Finite := Set.Finite.pi (fun _ => hSf)
  have himg : F '' T ⊆ Set.pi Set.univ (fun _ : Fin (n+1) => S) := by
    rintro _ ⟨P, ⟨hm, hn, hr, hc⟩, rfl⟩ k _
    obtain ⟨a, ha⟩ := hc k
    refine ⟨?_, fun φ => ?_⟩
    · show IsIntegral ℤ ((d : E) * P.coeff k)
      rw [← ha]; exact a.isIntegral_coe
    · have hbd := Polynomial.coeff_bdd_of_roots_le (B := 1) (d := n) φ hm (IsAlgClosed.splits _) hn.le
        (fun z hz => (hr φ z hz).le) k
      rw [Polynomial.coeff_map] at hbd
      show ‖φ ((d : E) * P.coeff k)‖ ≤ (d : ℝ) * B
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg d)
  have hinj : Set.InjOn F T := by
    rintro P ⟨-, hP, -⟩ Q ⟨-, hQ, -⟩ hPQ
    ext k
    by_cases hk : k < n + 1
    · have := congrFun hPQ ⟨k, hk⟩
      simp only [F] at this
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hd) this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  exact Set.Finite.of_finite_image (hpi.subset himg) hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsSupportDefiniteUnitaryTestFu
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.SuppFin

theorem cLoc_eventually_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n), ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w n := GlobalTheory.T.definiteUnitaryLocalComponent_mem_integralGL_cofinite

theorem factor_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU E n, (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w n) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := GlobalTheory.T.localTestFactor_ne_zero_of_globalProduct_ne_zero

theorem cLoc_mem_UL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UA E n), cLoc w y ∈ UL n w := by
  intro E _ _ _ hU n w y
  by_cases hs : IsSplitAt w
  · unfold UL
    rw [if_pos hs]
    exact Subgroup.mem_top _
  · obtain ⟨-, -, hloc, -⟩ := (GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs
    have hu := GlobalTheory.DefU.ClassFin.cT_pFin y
    unfold UL
    rw [if_neg hs]
    change cT (cj w) (cLoc w y).val * 1 * (cLoc w y).val = 1
    rw [mul_one]
    have key : cT (cj w) ((GeneralLinearGroup.map (pFin E) (y : GA E n)).val.map (pLoc E w)) =
        (cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (GeneralLinearGroup.map (pFin E) (y : GA E n)).val).map (pLoc E w) := by
      refine Matrix.ext fun i j => ?_
      simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
      exact (hloc _).symm
    calc cT (cj w) (cLoc w y).val * (cLoc w y).val =
        (cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (GeneralLinearGroup.map (pFin E) (y : GA E n)).val *
          (GeneralLinearGroup.map (pFin E) (y : GA E n)).val).map (pLoc E w) := by
          rw [Matrix.map_mul, ← key]
          rfl
      _ = 1 := by rw [hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem compact_val_bounded : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))), IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j, Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := GlobalTheory.T.gl_adicCompletion_entries_bounded_of_isCompact

theorem valuation_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : E), w.valuation E (IsCMField.complexConj E a) = (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E a := by
  intro E _ _ _ w a
  obtain ⟨-, h1, h2⟩ := conjLoc_spec (GlobalTheory.SplitPts.conjE E) w
  have hv : ∀ (v : Pl E) (b : E), Valued.v (algebraMap E (v.adicCompletion E) b) = v.valuation E b :=
    fun v b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v b
  have e := h2 (algebraMap E _ a)
  rw [h1] at e
  rw [← hv, ← hv]
  exact e

theorem section_conjSrc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → (∀ w, w ∉ S → conjSrc (GlobalTheory.SplitPts.conjE E) w ∈ S) ∧ Function.Injective (conjSrc (GlobalTheory.SplitPts.conjE E)) := by
  intro E _ _ _ S hS
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
    by_cases hs : IsSplitAt w
    · rcases (GlobalTheory.SplitPts.over_split hs).2.2 u hu with rfl | h
      · exact absurd huS hw
      · rwa [← h]
    · exfalso
      exact hs ⟨u, fun h => hw (h ▸ huS), hu⟩
  · intro a b hab
    have ha := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) a
    have hb := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) b
    rw [hab] at ha
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at ha hb
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have hy : IsIntegral ℤ ((GlobalTheory.SplitPts.conjE E) (x : E)) :=
      x.isIntegral_coe.map (RingHom.toIntAlgHom (GlobalTheory.SplitPts.conjE E).toRingHom)
    exact (ha x ⟨_, hy⟩ rfl).trans (hb x ⟨_, hy⟩ rfl).symm

theorem unitary_norm_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ (γ.1.val i j)‖ ≤ 1 := GlobalTheory.T.norm_complexEmbedding_entry_definiteUnitaryRational_le_one

theorem finite_of_local_bounds : ∀ (E : Type) [Field E] [NumberField E] (X : Set E), (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) → (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) → (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := GlobalTheory.T.finite_of_valuation_bounded_norm_le_one

theorem cLoc_finPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (γ : UE E n), cLoc w (finPt γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  intro E _ _ _ n w γ
  have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [mul_one] at h
  have hc : cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (ratF E n γ.1).val * (ratF E n γ.1).val = 1 := by
    have e : (ratF E n γ.1).val = γ.1.val.map (algebraMap E (Af E)) := rfl
    rw [e]
    calc cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (γ.1.val.map (algebraMap E (Af E))) * γ.1.val.map (algebraMap E (Af E))
        = (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * γ.1.val).map (algebraMap E (Af E)) := by
          rw [Matrix.map_mul]
          congr 1
          refine Matrix.ext fun i j => ?_
          simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
          exact conjFin_algebraMap (E := E) _ _
      _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero (algebraMap E (Af E))) (map_one (algebraMap E (Af E)))
  have hUA := GlobalTheory.DefU.ClassFin.finGL_mem_UA _ hc
  have hfin : (⟨_, hUA⟩ : UA E n) ∈ finU E n := (MonoidHom.mem_ker).2 (Units.ext (by
    have := pInf_finGL (E := E) (ratF E n γ.1)
    exact congrArg Units.val this))
  have e0 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, hUA⟩ := dif_pos hUA
  have e1 : (finPt γ).1 = ⟨finGL E n (ratF E n γ.1), hUA⟩ := by
    unfold finPt
    rw [e0]
    exact congrArg Subtype.val (dif_pos hfin)
  rw [e1]
  have h2 := GlobalTheory.CuspRep.pFin_finGL (E := E) (a := n) (ratF E n γ.1)
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  exact congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) h2

end GlobalTheory.BCT.SuppFin

namespace GlobalTheory.BCT.SuppFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem val_le_one_of_KGL {w : Pl E} {h : GL (Fin n) (w.adicCompletion E)} (hh : h ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    Valued.v (h.val i j) ≤ 1 := by
  obtain ⟨k, rfl⟩ := hh
  exact (k.val i j).2

theorem conj_entry (γ : UE E n) (i j : Fin n) : IsCMField.complexConj E (γ.1.val i j) = (γ.1⁻¹).val j i := by
  have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [mul_one] at h
  rw [Units.inv_eq_of_mul_eq_one_left h]
  rfl

theorem finite_of_bounds (S : Set (Pl E)) (hS : IsSection S) (Γs : Set (UE E n))
    (hb : ∀ w ∈ S, ∃ N : ℤ, ∀ γ ∈ Γs, ∀ i j, w.valuation E (γ.1.val i j) ≤ WithZero.exp N ∧
      w.valuation E ((γ.1⁻¹).val i j) ≤ WithZero.exp N)
    (hc : ∀ᶠ w in cofinite, w ∈ S → ∀ γ ∈ Γs, ∀ i j, w.valuation E (γ.1.val i j) ≤ 1 ∧
      w.valuation E ((γ.1⁻¹).val i j) ≤ 1) : Γs.Finite := by
  classical
  set X : Set E := {a | ∃ γ ∈ Γs, ∃ i j, a = γ.1.val i j ∨ a = (γ.1⁻¹).val i j} with hXdef
  have hcc : ∀ a : E, IsCMField.complexConj E (IsCMField.complexConj E a) = a := IsCMField.complexConj_apply_apply E
  have hXc : ∀ a ∈ X, IsCMField.complexConj E a ∈ X := by
    rintro a ⟨γ, hγ, i, j, rfl | rfl⟩
    · exact ⟨γ, hγ, j, i, Or.inr (conj_entry γ i j)⟩
    · refine ⟨γ, hγ, j, i, Or.inl ?_⟩
      rw [← conj_entry γ j i, hcc]
  obtain ⟨hsec, hinj⟩ := section_conjSrc E S hS
  have hval : ∀ (w : Pl E) (a : E), w.valuation E a =
      (conjSrc (GlobalTheory.SplitPts.conjE E) w).valuation E (IsCMField.complexConj E a) := by
    intro w a
    rw [← valuation_conj, hcc]
  have hall : ∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨N, hN⟩ := hb w hw
      refine ⟨N, ?_⟩
      rintro a ⟨γ, hγ, i, j, rfl | rfl⟩
      exacts [(hN γ hγ i j).1, (hN γ hγ i j).2]
    · obtain ⟨N, hN⟩ := hb _ (hsec w hw)
      refine ⟨N, fun a ha => ?_⟩
      rw [hval]
      obtain ⟨γ, hγ, i, j, h | h⟩ := hXc a ha <;> rw [h]
      exacts [(hN γ hγ i j).1, (hN γ hγ i j).2]
  have hcof : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1 := by
    have h2 := hinj.tendsto_cofinite.eventually hc
    filter_upwards [hc, h2] with w h1 h2 a ha
    by_cases hw : w ∈ S
    · obtain ⟨γ, hγ, i, j, rfl | rfl⟩ := ha
      exacts [(h1 hw γ hγ i j).1, (h1 hw γ hγ i j).2]
    · rw [hval]
      obtain ⟨γ, hγ, i, j, h | h⟩ := hXc a ha <;> rw [h]
      exacts [(h2 (hsec w hw) γ hγ i j).1, (h2 (hsec w hw) γ hγ i j).2]
  have hinf : ∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1 := by
    rintro a ⟨γ, hγ, i, j, rfl | rfl⟩ τ
    · exact unitary_norm_le_one E n γ τ i j
    · exact unitary_norm_le_one E n γ⁻¹ τ i j
  have hX := finite_of_local_bounds E X hall hcof hinf
  have hM : (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => X).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hX
  refine (hM.preimage (f := fun γ : UE E n => (γ.1.val : Fin n → Fin n → E)) ?_).subset ?_
  · intro a _ b _ h
    exact Subtype.ext (Units.ext h)
  · intro γ hγ i _ j _
    exact ⟨γ, hγ, i, j, Or.inl rfl⟩

end GlobalTheory.BCT.SuppFin

open GlobalTheory.BCT.SuppFin in

theorem GlobalTheory.BCT.SuppFin.suppFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU E n, {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite := by
  intro E _ _ _ hU n hn S hS K' hK' f hf x
  classical
  set Γs : Set (UE E n) := {γ | globFn S f (x⁻¹ * finPt γ * x) ≠ 0} with hΓs
  have hUL : ∀ (w : Pl E) (z : UA E n), cLoc w z ∈ UL n w := fun w z => cLoc_mem_UL E hU n w z
  have hnz : ∀ γ ∈ Γs, ∀ w ∈ S, f w (toSub _ (cLoc w (x⁻¹ * finPt γ * x).1)) ≠ 0 :=
    fun γ hγ w hw => factor_ne_zero E n S K' f hf (x⁻¹ * finPt γ * x) (cLoc_eventually_KGL E n _) hγ w hw
  have hpt : ∀ (w : Pl E) (γ : UE E n), GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 =
      cLoc w x.1 * cLoc w (x⁻¹ * finPt γ * x).1 * (cLoc w x.1)⁻¹ := by
    intro w γ
    rw [← cLoc_finPt E n w γ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
    group
  have hv : ∀ (w : Pl E) (a : E), Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
    fun w a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
  have hent : ∀ (w : Pl E) (γ : UE E n) (i j : Fin n),
      (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val i j = algebraMap E _ (γ.1.val i j) ∧
      ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)⁻¹).val i j =
        algebraMap E _ ((γ.1⁻¹).val i j) := by
    intro w γ i j
    rw [← map_inv]
    exact ⟨rfl, rfl⟩
  refine finite_of_bounds S hS Γs ?_ ?_
  · intro w hw
    set c := cLoc w x.1 with hcdef
    set D : Set (GL (Fin n) (w.adicCompletion E)) :=
      (fun h => c * h * c⁻¹) '' ((UL n w).subtype '' tsupport (f w)) with hDdef
    have hD : IsCompact D :=
      (((hf.1 w).1.image continuous_subtype_val).image ((continuous_const.mul continuous_id).mul continuous_const))
    obtain ⟨N, hN⟩ := compact_val_bounded E w n D hD
    refine ⟨N, fun γ hγ i j => ?_⟩
    have hmem : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ D := by
      rw [hpt]
      refine ⟨_, ⟨⟨_, hUL w _⟩, subset_tsupport _ ?_, rfl⟩, rfl⟩
      have h0 := hnz γ hγ w hw
      rwa [toSub, dif_pos (hUL w _)] at h0
    obtain ⟨h1, h2⟩ := hN _ hmem i j
    rw [(hent w γ i j).1, hv] at h1
    rw [(hent w γ i j).2, hv] at h2
    exact ⟨h1, h2⟩
  · filter_upwards [hf.2, cLoc_eventually_KGL E n x.1] with w hfw hxw hw γ hγ i j
    have h0 := hnz γ hγ w hw
    rw [hfw, toSub, dif_pos (hUL w _)] at h0
    have hy : cLoc w (x⁻¹ * finPt γ * x).1 ∈ GlobalTheory.LFun.KGL w n :=
      Subgroup.mem_subgroupOf.1 (Set.indicator_apply_ne_zero.1 h0).1
    have hg : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ GlobalTheory.LFun.KGL w n := by
      rw [hpt]
      exact mul_mem (mul_mem hxw hy) (inv_mem hxw)
    have h1 := val_le_one_of_KGL hg i j
    have h2 := val_le_one_of_KGL (inv_mem hg) i j
    rw [(hent w γ i j).1, hv] at h1
    rw [(hent w γ i j).2, hv] at h2
    exact ⟨h1, h2⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDiscreteSeriesCharacterEqWeylCharacterStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_discreteSeriesCharacter_eq_weylCharacter : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℤ) (α : Fin n → ℂ) (ι : Type) [Finite ι]
    (y : ι → Equiv.Perm (Fin n)) (θ : ι → Fin n → ℝ), Odd n → Function.Injective α →
    Function.Bijective (fun p : compactWeyl ε × ι => (y p.2)⁻¹ * p.1.1) →
    (∀ q a, Complex.exp (θ q a * Complex.I) = α ((y q)⁻¹ a)) →
    ∑ᶠ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) = glChar (hiWt lam) α := by
  first | exact @GlobalTheory.dsChar_finsum_eq_glChar | exact GlobalTheory.dsChar_finsum_eq_glChar | (intros; apply GlobalTheory.dsChar_finsum_eq_glChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogFinitePlaceEqNegLogAbsNormStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_log_finitePlace_eq_neg_log_abs_norm' : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∑ᶠ q : FinitePlace F, Real.log (q δ) = -Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm | exact GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm | (intros; apply GlobalTheory.ProdFormula.finsum_log_finitePlace_eq_neg_log_abs_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndexStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_log_gaussAbs_le_fractionalIdeal_index : ∀ (F : Type) [Field F] [NumberField F] (τ : Type) (g : MvPolynomial τ F), g ≠ 0 → ∀ (I : Submodule (𝓞 F) F) (δ : F), δ ≠ 0 → 1 ≤ I → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (∀ m, coeff m g / δ ∈ I) → ∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g) ≤ Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup) + ∑ᶠ q : FinitePlace F, Real.log (q δ) := by
  first | exact @GlobalTheory.GaussFrac.finsum_log_gaussAbs_le | exact GlobalTheory.GaussFrac.finsum_log_gaussAbs_le | (intros; apply GlobalTheory.GaussFrac.finsum_log_gaussAbs_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetVacuumEqConstMulPeriodScaledJetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockJet_vacuum_eq_const_mul_periodScaledJet : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  first | exact @GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq | exact GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq | (intros; apply GlobalTheory.FunObj.TopJet.fockIn_vacuum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift.PolRangePf

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_eq' (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add' (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq', MultilinearMap.map_update_add]

theorem atPl_smul' (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq', MultilinearMap.map_update_smul]

theorem atPl_zero' (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq', MultilinearMap.map_update_zero]

theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

end Tensor

theorem heisOp_zero {P Q R S : ℕ} : heisOp (P := P) (Q := Q) (R := R) (S := S) 0 = 0 := by
  simp [heisOp]

theorem Jm_transpose' (p q : ℕ) : (Jm p q)ᵀ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem exists_at_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (z : InfinitePlace F → ℂ) : ∃ a : AE F E, At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := GlobalTheory.T.exists_archimedean_adele_CM_prescribed_embedding_values hcm τ z

theorem exists_mat_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => exists_at_piInf hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem mulX_mem_span {P Q R S : ℕ} (l : Ln P Q R S) :
    LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
      Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := GlobalTheory.T.fockVariableMultiplication_mem_span_heisenbergOperators l

theorem tens_top {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ))
    (h1 : PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N)
    (hN : ∀ w l, ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) : N = ⊤ := GlobalTheory.T.piTensorMvPolynomial_submodule_eq_top_of_one_mul_X N h1 hN

theorem tens_top_heis {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}
    (N : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S))
    (h1 : PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ∈ N)
    (hN : ∀ w c, ∀ T ∈ N, atPl w (heisOp (P := P) (Q := Q) (R := R) (S := S) c) T ∈ N) : N = ⊤ := by
  refine tens_top N h1 fun w l T hT => ?_
  let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) :=
    { carrier := {L | ∀ T ∈ N, atPl w L T ∈ N}
      add_mem' := fun {a b} ha hb T hT => by
        rw [atPl_add', LinearMap.add_apply]; exact N.add_mem (ha T hT) (hb T hT)
      zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem
      smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }
  have hK : Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) ≤ K :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)
  exact hK (mulX_mem_span l) T hT

theorem heisOp_twist_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := GlobalTheory.T.fockHeisenbergOperator_I_signatureConj_apply_one c

theorem sumPl_twist_one {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S))) (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))
      = Complex.I • sumPl (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S))) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl_tprod, heisOp_twist_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _

theorem polRange_of (hL : ActsLaws) (_hD : DerEx) (hV : VacLine) : PolRange := by
  intro F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  have uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂ := fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have der : ∀ u, At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix P Q) (Ix R S) ℂ) (e : ℂ),
      A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm R S * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • ((A w * Jm P Q) * c * (Jm R S * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm P Q * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm R S)) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPl_twist_one, map_smul]
  have gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h => by
    unfold Model.Pol
    exact Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := by
    intro u hu f hf f₁ h1
    unfold Model.Pol at hf ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    have htop : (M.Pol ψ τ).comap Φ = ⊤ := by
      refine tens_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_
      obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
        (fun w' => A w' * Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w' * (C w')ᵀ)
      have hs : sumPl (fun w' => heisOp (Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w')) T =
          atPl w (heisOp c) T := by
        rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]
        · simp
        · intro b _ hb; simp [Function.update_of_ne hb, heisOp_zero, atPl_zero']
        · simp
      have := pol_der u hu _ hT _ (der u hu _ hu' T)
      rwa [hs] at this
    have : T ∈ (M.Pol ψ τ).comap Φ := htop ▸ Submodule.mem_top
    exact this
  · unfold Model.Pol
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
    · obtain ⟨ε, hε⟩ := hf₀
      obtain ⟨z, hz⟩ := hV F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      exact ⟨z • PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)), by rw [map_smul, hz]⟩
    · obtain ⟨T, rfl⟩ := hf
      exact ⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩

end GlobalTheory.RealLift.PolRangePf
end
end

