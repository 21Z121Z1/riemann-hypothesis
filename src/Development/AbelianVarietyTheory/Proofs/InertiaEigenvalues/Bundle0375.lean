import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimplificationCharpoly

private theorem charpoly_eq_of_filtration_graded_eq {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (G : ℕ → Submodule k V)
      (f g : Module.End k V), Monotone G → G 0 = ⊥ → G n = ⊤ → (∀ i, ∀ x ∈ G i, f x ∈ G i) →
      (∀ i, ∀ x ∈ G (i + 1), g x - f x ∈ G i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  induction n with
  | zero =>
    intro V _ _ _ G f g _ h0 hn _ _
    have hV : ∀ x : V, x = 0 := by
      intro x
      have hx : x ∈ G 0 := by rw [hn]; exact Submodule.mem_top
      rw [h0] at hx
      exact (Submodule.mem_bot k).mp hx
    have hfg : f = g := by
      ext x
      rw [hV x, map_zero, map_zero]
    rw [hfg]
  | succ n ih =>
    intro V _ _ _ G f g hmono h0 hn hf hd

    have hg : ∀ i, ∀ x ∈ G i, g x ∈ G i := by
      intro i x hx
      cases i with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx, map_zero]
        exact Submodule.zero_mem _
      | succ j =>
        have e : g x = f x + (g x - f x) := by abel
        rw [e]
        exact Submodule.add_mem _ (hf _ x hx) (hmono (Nat.le_succ j) (hd j x hx))
    set A := G n with hA
    rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A f (hf n),
      GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A g (hg n)]
    congr 1
    ·
      refine ih (fun i => (G i).comap A.subtype) (f.restrict (hf n)) (g.restrict (hg n))
        (fun i j hij => Submodule.comap_mono (hmono hij)) ?_ ?_ ?_ ?_
      · rw [h0, Submodule.comap_bot, Submodule.ker_subtype]
      · exact Submodule.comap_subtype_self A
      · intro i x hx
        exact hf i x hx
      · intro i x hx
        exact hd i x hx
    ·
      congr 1
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.mapQ_apply]
      rw [Submodule.Quotient.eq]
      have hx : x ∈ G (n + 1) := by rw [hn]; exact Submodule.mem_top
      have := hd n x hx
      rw [← neg_mem_iff, neg_sub] at this
      exact this

theorem charpoly_eq_of_filtration {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (F : ℕ → Submodule k V)
      (f g : Module.End k V), F 0 = ⊥ → F n = ⊤ → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
      (∀ i, ∀ x ∈ F (i + 1), g x - f x ∈ F i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  intro V _ _ _ F f g h0 hn hf hd

  refine charpoly_eq_of_filtration_graded_eq n (fun i => partialSups F i) f g (partialSups F).monotone ?_ ?_ ?_ ?_
  · simp only [partialSups_zero, h0]
  · exact eq_top_iff.mpr (hn ▸ le_partialSups F n)
  · intro i
    have hle : partialSups F i ≤ (partialSups F i).comap f := by
      refine partialSups_le F i _ (fun j hj x hx => ?_)
      exact le_partialSups_of_le F hj (hf j x hx)
    exact fun x hx => hle hx
  · intro i
    have hle : partialSups F (i + 1) ≤ (partialSups F i).comap (g - f) := by
      refine partialSups_le F (i + 1) _ (fun j hj x hx => ?_)
      cases j with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx]
        exact Submodule.zero_mem _
      | succ m =>
        exact le_partialSups_of_le F (Nat.succ_le_succ_iff.mp hj) (hd m x hx)
    exact fun x hx => hle hx

theorem charpoly_eq : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V),
    GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ →
      ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  intro k Γ _ _ W _ _ _ V _ _ _ s ρ hss g
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf at hss
  obtain ⟨-, m, Ws, e, hst, hint, hρ⟩ := hss
  have hsj : ∀ j, ∀ x ∈ Ws j, s g x ∈ Ws j := by
    intro j x hx
    have h := hst j
    unfold Stable at h
    exact h g x hx

  let H : ℕ → Submodule k W := fun i => ⨆ (j : Fin m) (_ : (j : ℕ) < i), Ws j
  have hH : ∀ i, ∀ x ∈ H i, s g x ∈ H i := by
    intro i
    have hle : H i ≤ (H i).comap (s g) :=
      iSup₂_le fun j hj x hx =>
        (le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j hj) (hsj j x hx)
    exact fun x hx => hle hx
  rw [← e.charpoly_conj (s g)]
  refine charpoly_eq_of_filtration m (fun i => (H i).map (e : W →ₗ[k] V)) (e.conj (s g)) (ρ g)
    ?_ ?_ ?_ ?_
  · have h0 : H 0 = ⊥ := by simp [H]
    simp only [h0, Submodule.map_bot]
  · have hm : H m = ⊤ := by
      rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
      exact iSup_le fun j => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < m) => Ws j) j j.isLt
    simp only [hm, Submodule.map_top, LinearEquiv.range]
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx ⊢
    simpa [LinearEquiv.conj_apply] using hH i _ hx
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx
    have hle : H (i + 1) ≤ ((H i).map (e : W →ₗ[k] V)).comap
        ((ρ g - e.conj (s g)) ∘ₗ (e : W →ₗ[k] V)) := by
      refine iSup₂_le fun j hj v hv => ?_
      have hsub : (⨆ j' ∈ Set.Iio j, Ws j') ≤ H i :=
        iSup₂_le fun j' hj' => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j'
          (lt_of_lt_of_le (Fin.lt_def.mp (Set.mem_Iio.mp hj')) (Nat.lt_succ_iff.mp hj))
      have h1 := Submodule.map_mono (f := (e : W →ₗ[k] V)) hsub (hρ j g v hv)
      simpa [LinearEquiv.conj_apply] using h1
    have h2 := hle hx
    simpa using h2

end GlobalTheory.SemisimplificationCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivatives
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.DegDer

variable {g : ℕ} [Fact g.Prime]

theorem tl_one {a n : ℕ} (h : a ≤ n) : tl a (1 : Mt g n) = (1 : Mt g a) := by
  ext i j
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]

theorem br_one {a b n : ℕ} (h : a + b ≤ n) : br a b (1 : Mt g n) = (1 : Mt g b) := by
  ext i j
  have hi : a + (i : ℕ) < n := by omega
  have hj : a + (j : ℕ) < n := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
  simp

theorem toG_one {n : ℕ} : toG (1 : Mt g n) = 1 := by
  unfold toG
  rw [dif_pos isUnit_one]
  ext : 1
  simp

theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 = ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ *
      ((Fintype.card (Gn g (a + b)) : ℂ) * (α 1 * β 1)) := by
  unfold hc hcT
  rw [← GlobalTheory.GLm.ParBasic.card_par]
  congr 1
  simp only [mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true,
    tl_one (Nat.le_add_right a b), br_one (le_refl (a + b)), toG_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

theorem blockDiagonalWithIdentityGL_one (k : ℕ) : diag1 (1 : Gn g k) (k + 1) = 1 := by
  unfold diag1
  have : (fun i j : Fin (k + 1) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN ((1 : Gn g k) : Mt g k) i j
      else (1 : Mt g (k + 1)) i j) = (1 : Mt g (k + 1)) := by
    ext i j
    split_ifs with h
    · simp only [Units.val_one, entN, h, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
    · rfl
  rw [this, toG_one]

theorem prod_pow_add (a b : ℕ) :
    (∏ i : Fin (a + b), (g : ℂ) ^ (i : ℕ)) =
      (∏ i : Fin a, (g : ℂ) ^ (i : ℕ)) * (∏ i : Fin b, (g : ℂ) ^ (i : ℕ)) * (g : ℂ) ^ (a * b) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.coe_castAdd, Fin.coe_natAdd, pow_add, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  ring

theorem prod_Icc_add (f : ℕ → ℂ) (a b : ℕ) :
    (∏ i ∈ Finset.Icc 1 (a + b), f i) = (∏ i ∈ Finset.Icc 1 a, f i) * ∏ i ∈ Finset.Ico (a + 1) (a + b + 1), f i := by
  have e : ∀ n, Finset.Icc 1 n = Finset.Ico 1 (n + 1) := fun n => by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e, e, Finset.prod_Ico_consecutive _ (by omega) (by omega)]

theorem card_Gn_factors_ne_zero (n : ℕ) :
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) ≠ 0 ∧ (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) ≠ 0 := by
  have h : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [GlobalTheory.GLq.GGDeg.card_Gn] at h
  exact mul_ne_zero_iff.mp h

theorem one_eq_sum_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (χ : Gn g n → ℂ),
    0 < n → IsClass χ → χ 1 = ∑ m ∈ Finset.range n, der ψ m χ 1 * ∏ i ∈ Finset.Ico (m + 1) n, ((g : ℂ) ^ i - 1) := by
  intro g _ ψ hψ n χ hn hχ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have h1 : χ 1 = χ (diag1 (1 : Gn g k) (k + 1)) := by rw [blockDiagonalWithIdentityGL_one]
  rw [h1, GlobalTheory.GLm.mirClass_diag1_eq_sum g ψ hψ k χ hM 1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
  obtain ⟨b, rfl⟩ : ∃ b, k = i + b := ⟨k - i, by omega⟩
  have hkb : i + b - i = b := by omega
  rw [hkb, hc_one, (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ b).1]
  push_cast
  rw [GlobalTheory.GLq.GGDeg.card_Gn i, GlobalTheory.GLq.GGDeg.card_Gn b, GlobalTheory.GLq.GGDeg.card_Gn (i + b), prod_pow_add,
    prod_Icc_add]
  obtain ⟨hPi, hQi⟩ := card_Gn_factors_ne_zero (g := g) i
  obtain ⟨hPb, hQb⟩ := card_Gn_factors_ne_zero (g := g) b
  have hg : (g : ℂ) ^ (i * b) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero)
  field_simp

end GlobalTheory.GLq.DegDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedDiscGaugeCompletion_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), IsUltrametricDist (Disc l u ρ) ∧ (∀ y : Disc l u ρ, ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l) ∧ (∀ (N : Type) [NormedAddCommGroup N], (∀ z : N, l • z = 0 → z = 0) → ∀ F G : Disc l u ρ →+ N, Continuous F → Continuous G → (∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) → F = G) ∧ ∀ (A' A'' : Type) [CommRing A'] [CommRing A''] (u' : A') (u'' : A'') (ρ' ρ'' : ℝ≥0) (f : A →+* A') (f' : A' →+* A'') (F : Disc l u ρ →+* Disc l u' ρ') (F' : Disc l u' ρ' →+* Disc l u'' ρ''), IsDiscMap f F → IsDiscMap f' F' → IsDiscMap (f'.comp f) (F'.comp F) := by
  first | exact @GlobalTheory.BSP.DiscBasic.disc_basic | exact GlobalTheory.BSP.DiscBasic.disc_basic | (intros; apply GlobalTheory.BSP.DiscBasic.disc_basic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscTopologicalBasisExpansionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedDisc_topologicalBasis_expansion : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap s j → ∀ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), ((∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖)) → ∀ y, Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0) ∧ HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y := by
  first | exact @GlobalTheory.BSP.DiscExpand.disc_expand | exact GlobalTheory.BSP.DiscExpand.disc_expand | (intros; apply GlobalTheory.BSP.DiscExpand.disc_expand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingNumericalInequalityTheoremB
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

theorem closing_numerical_inequality :
    ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := by
  intro CA C b l S η Rw Tb Vd f r t m p hC hp ht hf hm hl hS hη hb hL hRw hTb hVd
  have hK : 0 ≤ max CA 0 := le_max_right _ _
  have hpR : (260 : ℝ) * (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) ≤ (p : ℝ) := by exact_mod_cast hp
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hmR : (m : ℝ) ≤ r := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hl0 : 0 < l := by linarith

  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogl : 1 ≤ Real.log l := by
    have := Real.log_le_log (by norm_num) hl
    linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith

  have hlam : Real.logb l (2 * b) ≤ 2 * Real.log b := by
    rw [Real.logb, div_le_iff₀ (by linarith), Real.log_mul (by norm_num) hb.ne']
    nlinarith
  set L := Real.log b with hLdef
  set lam := Real.logb l (2 * b) with hlamdef
  have hx : 0 ≤ b / l := div_nonneg hb.le hl0.le
  set x := b / l with hxdef
  have h4x : 4 * b / l = 4 * x := by rw [hxdef]; ring
  rw [h4x] at hRw

  have hinner : 3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)
      ≤ 13 * ((r : ℝ) * (x + S + t + η + L) + m * b) := by
    nlinarith [mul_nonneg hr0 hx, mul_nonneg hr0 hS, mul_nonneg hr0 (sub_nonneg.2 htR),
      mul_nonneg hr0 hη, mul_nonneg hr0 (sub_nonneg.2 hlam), mul_nonneg hr0 (by linarith : (0:ℝ) ≤ L),
      mul_nonneg hm0 hb.le]
  have hB : 0 ≤ (r : ℝ) * (x + S + t + η + L) + m * b := by
    have : 0 ≤ x + S + t + η + L := by linarith
    exact add_nonneg (mul_nonneg hr0 this) (mul_nonneg hm0 hb.le)
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hmain : max CA 0 * (3 * (f : ℝ) * r * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1))
      ≤ C * f * ((r : ℝ) * (x + S + t + η + L) + m * b) := by
    have e : 3 * (f : ℝ) * r * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)
        = f * (3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)) := by ring
    rw [e]
    calc max CA 0 * (f * (3 * (r : ℝ) * (4 * x + 2 * S + 2 * lam + 1 + η + t) + 6 * (m : ℝ) * (2 * b + 1)))
        ≤ max CA 0 * (f * (13 * ((r : ℝ) * (x + S + t + η + L) + m * b))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hf0) hK
      _ = (13 * max CA 0) * (f * ((r : ℝ) * (x + S + t + η + L) + m * b)) := by ring
      _ ≤ C * (f * ((r : ℝ) * (x + S + t + η + L) + m * b)) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg hf0 hB)
      _ = C * f * ((r : ℝ) * (x + S + t + η + L) + m * b) := by ring

  set Q : ℝ := (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) with hQ
  have hQe : Q = (f : ℝ) ^ 2 * ((t : ℝ) ^ 2 * ((r : ℝ) + t)) := by rw [hQ]; ring
  have ht2 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (t : ℝ) * t := mul_le_mul htR htR zero_le_one (by linarith)
      _ = (t : ℝ) ^ 2 := by ring
  have hf2 : (f : ℝ) ≤ (f : ℝ) ^ 2 := by
    calc (f : ℝ) = f * 1 := by ring
      _ ≤ (f : ℝ) * f := mul_le_mul_of_nonneg_left hfR hf0
      _ = (f : ℝ) ^ 2 := by ring
  have hrt : (1 : ℝ) ≤ (r : ℝ) + t := by linarith
  have hT1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 * ((r : ℝ) + t) := one_le_mul_of_one_le_of_one_le ht2 hrt
  have hfQ : (f : ℝ) ≤ Q := by
    rw [hQe]
    exact hf2.trans (le_mul_of_one_le_right (sq_nonneg _) hT1)
  have hVQ : 4 * ((r : ℝ) + t) * t ≤ 4 * Q := by
    have h1 : ((r : ℝ) + t) * t ≤ (t : ℝ) ^ 2 * ((r : ℝ) + t) := by
      have : ((r : ℝ) + t) * t = ((r : ℝ) + t) * t * 1 := by ring
      calc ((r : ℝ) + t) * t ≤ ((r : ℝ) + t) * (t * t) :=
            mul_le_mul_of_nonneg_left (by
              calc (t : ℝ) = t * 1 := by ring
                _ ≤ (t : ℝ) * t := mul_le_mul_of_nonneg_left htR (by linarith)) (by linarith)
        _ = (t : ℝ) ^ 2 * ((r : ℝ) + t) := by ring
    have hf1 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := hfR.trans hf2
    have h2 : (t : ℝ) ^ 2 * ((r : ℝ) + t) ≤ Q := by
      rw [hQe]; exact le_mul_of_one_le_left (by linarith) hf1
    linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hQL : Q ≤ Q * L := le_mul_of_one_le_right hQ0 hL.le
  have hTbQ : Tb ≤ 240 * Q * L := by
    have : 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * L = 240 * Q * L := by rw [hQ]; ring
    linarith
  have hpL : 260 * Q * L ≤ (p : ℝ) * L := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : 260 * Q = (260 : ℝ) * (f : ℝ) ^ 2 * (t : ℝ) ^ 2 * ((r : ℝ) + t) := by rw [hQ]; ring
    linarith
  have hQL0 : 0 ≤ Q * L := mul_nonneg hQ0 (by linarith)
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryModIffForallTraceFormCoboundaryStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundaryMod_iff_forall_traceForm_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL))),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l]))),
    L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) →
    ∀ (z : ↥(GK K) × ↥(GK K) → LL),
    (CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x))) := by
  first | exact @GlobalTheory.cobO_iff_forall_lam | exact GlobalTheory.cobO_iff_forall_lam | (intros; apply GlobalTheory.cobO_iff_forall_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffProdOneSubCMulX
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem coeff_prod_one_sub_C_mul_X (c : ℂ) (α : Multiset ℂ) (k : ℕ) :
    ((α.map fun a => (1 : Polynomial ℂ) - Polynomial.C (c * a) * Polynomial.X).prod).coeff k
      = (-1 : ℂ) ^ k * c ^ k * α.esymm k := by
  induction α using Multiset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp [Multiset.esymm]
    | succ k => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul, one_mul, mul_assoc, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul]
    cases k with
    | zero => rw [ih]; simp [Multiset.esymm]
    | succ k =>
      have h : (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      rw [Polynomial.coeff_X_mul, ih, ih, h]
      ring

theorem normalised_esymm_eq_coeff :
    ∀ (r : ℕ) (q : ℝ), 0 < q → ∀ (α : Multiset ℂ), Multiset.card α = r → ∀ k, k ≤ r → (-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (((k : ℂ) * ((r : ℂ) - k)) / 2) * α.esymm k) = ((α.map fun a => (1 : Polynomial ℂ) - Polynomial.C ((q : ℂ) ^ (((r : ℂ) - 1) / 2) * a) * Polynomial.X).prod).coeff k := by
  intro r q hq α _ k _
  rw [coeff_prod_one_sub_C_mul_X]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    rw [← Nat.choose_two_right, Nat.cast_choose_two]
  have h : (q : ℂ) ^ (k * (k - 1) / 2) * (q : ℂ) ^ (((k : ℂ) * ((r : ℂ) - k)) / 2)
      = ((q : ℂ) ^ (((r : ℂ) - 1) / 2)) ^ k := by
    rw [← Complex.cpow_natCast (q : ℂ) (k * (k - 1) / 2), ← Complex.cpow_add _ _ hq0, hk,
      ← Complex.cpow_nat_mul]
    congr 1
    ring
  rw [← h]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroMapPowNullFactsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_zero_map_pow_null_facts : ∀ (S A ι : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (tb : TopBasis s I ι), (∀ x, (∀ i, tb.c i x = 0) → x = 0) ∧ (∀ (n : ℕ) x, x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n) ∧ (IsHausdorff I S → ∀ a : ι → S, (∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) → ∃ x, ∀ i, tb.c i x = a i) := by
  first | exact @GlobalTheory.BSP.TopBasis.coeff_facts | exact GlobalTheory.BSP.TopBasis.coeff_facts | (intros; apply GlobalTheory.BSP.TopBasis.coeff_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutatorMemOfCoboundaryDetectsQuotientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutator_mem_of_coboundary_detects_quotient : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → Detects p r A B → ∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B := by
  first | exact @GlobalTheory.PMon.Ram.commutator_mem_of_detects | exact GlobalTheory.PMon.Ram.commutator_mem_of_detects | (intros; apply GlobalTheory.PMon.Ram.commutator_mem_of_detects <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonCocyclesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_cocycles_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (a a' : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (Φ' : Matrix (Fin a') (Fin a') A) Z Z' (γ σ : Bool → GE N), Univ bkP i s κ Q Φ Z → Univ bkP i s κ Q' Φ' Z' → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (γ b) = 0) → SelC bkP i s κ Y Q f) → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] b m, repOn (Tgl i s) κ Y (σ b) m = m) → ∃ E : Matrix (Fin a) (Fin a') A, what₂ E ⊔ (what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) = ⊤ ∧ (∀ b, (Φ * E) b ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) ∧ ∀ j : Bool × Fin D.R.r, Z' (σ j.1) j.2 - Matrix.vecMul (Z (σ j.1) j.2) E ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) := by
  first | exact @GlobalTheory.NewPrime.comparison_cocycles | exact GlobalTheory.NewPrime.comparison_cocycles | (intros; apply GlobalTheory.NewPrime.comparison_cocycles <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMapIntertwinesGroupAlgebraActionStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonMap_intertwines_groupAlgebra_action : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D → ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)), D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) → S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
  first | exact @GlobalTheory.PendOf.CenKey.phi_onMt | exact GlobalTheory.PendOf.CenKey.phi_onMt | (intros; apply GlobalTheory.PendOf.CenKey.phi_onMt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocksStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_blockTriangular_diagonal_blocks : SubQuot := by
  first | exact @GlobalTheory.PMon.subQuot | exact GlobalTheory.PMon.subQuot | (intros; apply GlobalTheory.PMon.subQuot <;> assumption)
end

