import Mathlib
import Formalism.HermitianLattices.Bundle0002
import Formalism.HermitianLattices.HermitianLatticesProofs.ThetaSummable
import Formalism.HermitianLattices.Bundle0001
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0002
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0001
import Lemmata.GeneralBFactSecondRest.Imports

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite
section
open Module Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section AutFiniteSec

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

lemma autFinite_short (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L] (R : ℚ) :
    Set.Finite {v : V | v ∈ L ∧ Algebra.trace ℚ K (h v v) ≤ R} := by
  have hs := thetaSummable_main h hpos L 0 Complex.I (by simp)
  have hnorm : ∀ x : L, ‖Complex.exp (Real.pi * Complex.I * Complex.I *
      ((Algebra.trace ℚ K (h (0 + (x : V)) (0 + (x : V))) : ℚ) : ℂ))‖ =
        Real.exp (-Real.pi * ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ)) := by
    intro x
    rw [Complex.norm_exp, zero_add]
    congr 1
    have e : (Real.pi : ℂ) * Complex.I * Complex.I = -(Real.pi : ℂ) := by
      rw [mul_assoc, Complex.I_mul_I]
      ring
    rw [e]
    simp
  have hev := (tendsto_zero_iff_norm_tendsto_zero.1 hs.tendsto_cofinite_zero).eventually
    (gt_mem_nhds (Real.exp_pos (-Real.pi * (R : ℝ))))
  rw [Filter.eventually_cofinite] at hev
  refine (hev.image Subtype.val).subset ?_
  rintro v ⟨hvL, hvR⟩
  refine ⟨⟨v, hvL⟩, ?_, rfl⟩
  show ¬ (‖Complex.exp (Real.pi * Complex.I * Complex.I *
      ((Algebra.trace ℚ K (h (0 + v) (0 + v)) : ℚ) : ℂ))‖ < Real.exp (-Real.pi * (R : ℝ)))
  rw [not_lt, hnorm ⟨v, hvL⟩]
  apply Real.exp_le_exp.2
  have hR : ((Algebra.trace ℚ K (h v v) : ℚ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hvR
  nlinarith [Real.pi_pos]

end AutFiniteSec

theorem autFinite : AutFinite := by
  intro K V _ _ _ _ _ _ _ _ h _ hpos L hL
  obtain ⟨S, hS⟩ := Submodule.IsLattice.fg (A := K) (M := L)
  set R : ℚ := ∑ s ∈ S, Algebra.trace ℚ K (h s s) with hR
  have hSL : ∀ s ∈ S, s ∈ L := fun s hs => hS ▸ Submodule.subset_span hs
  have hsR : ∀ s ∈ S, Algebra.trace ℚ K (h s s) ≤ R := fun s hs =>
    Finset.single_le_sum (f := fun s => Algebra.trace ℚ K (h s s))
      (fun x _ => thetaSummable_nonneg h hpos x) hs
  have hT := autFinite_short h hpos L R
  have hspan : Submodule.span K (S : Set V) = ⊤ := by
    rw [eq_top_iff, ← Submodule.IsLattice.span_eq_top (A := K) (M := L), Submodule.span_le]
    intro x hx
    rw [← hS] at hx
    exact Submodule.span_le_restrictScalars (NumberField.RingOfIntegers K) K (S : Set V) hx
  let Φ : (V ≃ₗ[K] V) → (S → V) := fun g s => g s
  apply Set.Finite.of_finite_image (f := Φ)
  · refine (Set.Finite.pi (t := fun _ : S => {v : V | v ∈ L ∧ Algebra.trace ℚ K (h v v) ≤ R})
      (fun _ => hT)).subset ?_
    rintro _ ⟨g, ⟨hg, hgL⟩, rfl⟩ s _
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    refine ⟨?_, ?_⟩
    · have hm : g s ∈ Formalism.HermitianLatticesTheory.gmap g L := Submodule.mem_map_of_mem (hSL s s.2)
      rwa [hgL] at hm
    · show Algebra.trace ℚ K (h (g s) (g s)) ≤ R
      rw [hg']
      exact hsR s s.2
  · intro g₁ _ g₂ _ hg
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hspan
    intro x hx
    exact congrFun hg ⟨x, hx⟩

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.GenusScale
section
open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem genusScale_span (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (s : Set V)
    (hs : ∀ a ∈ s, ∀ b ∈ s, c * h a b ∈ (1 : Submodule R K)) :
    ∀ x ∈ Submodule.span R s, ∀ y ∈ Submodule.span R s, c * h x y ∈ (1 : Submodule R K) := by
  have key : ∀ a ∈ s, ∀ y ∈ Submodule.span R s, c * h a y ∈ (1 : Submodule R K) := by
    intro a ha y hy
    induction hy using Submodule.span_induction with
    | mem b hb => exact hs a ha b hb
    | zero => simp
    | add u w _ _ hu hw =>
        rw [map_add, mul_add]
        exact add_mem hu hw
    | smul r u _ hu =>
        rw [genusBasic_hsmul_right, mul_left_comm]
        exact genusBasic_mem_one_mul _ hu r
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem a ha => exact key a ha y hy
  | zero => simp
  | add u w _ _ hu hw =>
      rw [map_add, LinearMap.add_apply, mul_add]
      exact add_mem hu hw
  | smul r u _ hu =>
      rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
      exact genusBasic_mem_one_mul _ hu _

theorem genusScale_transfer (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : ∀ x ∈ L, ∀ y ∈ L, c * h x y ∈ (1 : Submodule R K)) :
    ∀ x ∈ M, ∀ y ∈ M, c * h x y ∈ (1 : Submodule R K) := by
  intro x hx y hy
  refine genusBasic_lg (K := K) (1 : Submodule R K) (c * h x y) ?_
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hxM : x ∈ loc (K := K) p M := locBasic_le_locS (hcompl (K := K) p) M hx
  have hyM : y ∈ loc (K := K) p M := locBasic_le_locS (hcompl (K := K) p) M hy
  rw [← hgL, isomAct_mem_gmap] at hxM hyM
  obtain ⟨s, hsS, hsx⟩ := locBasic_mem_locS.mp hxM
  obtain ⟨t, htS, hty⟩ := locBasic_mem_locS.mp hyM
  have hg' : ∀ u v : V, h (g u) (g v) = h u v := hg
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg' (g.symm x) (g.symm y)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    exact e.symm
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  refine locBasic_mem_locS.mpr ⟨locBasic_sigma hinj hstar s * t,
    (hcompl (K := K) p).mul_mem (genusBasic_sigma_mem hinj hstar p s hsS) htS, ?_⟩
  have e : (locBasic_sigma hinj hstar s * t) • (c * h x y) =
      c * (algebraMap R K (locBasic_sigma hinj hstar s) * (algebraMap R K t * h x y)) := by
    rw [Algebra.smul_def, map_mul]
    ring
  rw [e]
  exact h1

end SlopeTestRemainingChoices

private theorem exists_nat_pos_mul_mem_one {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ n : ℕ, 0 < n ∧ (n : K) * z ∈ (1 : Submodule (𝓞 K) K) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsIntegral.isIntegral (R := ℚ) z).isAlgebraic
  obtain ⟨y, hy0, hy⟩ := hz.exists_integral_multiple
  have hw : IsIntegral ℤ ((y.natAbs : K) * z) := by
    rcases Int.natAbs_eq y with e | e
    · rw [← Int.cast_natCast, ← e, ← zsmul_eq_mul]
      exact hy
    · have e' : (y.natAbs : ℤ) = -y := by linarith
      rw [← Int.cast_natCast, e', Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hy.neg
  exact ⟨y.natAbs, Int.natAbs_pos.mpr hy0, Submodule.mem_one.mpr ⟨⟨_, hw⟩, rfl⟩⟩

theorem genusScale : GenusScale := by
  intro K V _ _ _ _ _ _ _ _ h _ L hL
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro r
    have hr : IsIntegral ℤ (algebraMap (𝓞 K) K r) := NumberField.RingOfIntegers.isIntegral_coe r
    exact ⟨⟨star (algebraMap (𝓞 K) K r), hr.map (starRingEnd K).toIntAlgHom⟩, rfl⟩
  obtain ⟨s, hs⟩ := hL.fg
  choose n hn0 hn using exists_nat_pos_mul_mem_one (K := K)
  refine ⟨∏ q ∈ s ×ˢ s, n (h q.1 q.2), Finset.prod_pos (fun q _ => hn0 _), ?_⟩
  have hLd : ∀ x ∈ L, ∀ y ∈ L,
      ((∏ q ∈ s ×ˢ s, n (h q.1 q.2) : ℕ) : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← hs]
    refine genusScale_span hinj hstar h _ _ ?_
    intro a ha b hb
    have hmem : (a, b) ∈ s ×ˢ s := Finset.mem_product.mpr ⟨ha, hb⟩
    obtain ⟨k, hk⟩ : n (h a b) ∣ ∏ q ∈ s ×ˢ s, n (h q.1 q.2) :=
      Finset.dvd_prod_of_mem (fun q : V × V => n (h q.1 q.2)) hmem
    rw [hk, Nat.cast_mul, mul_comm ((n (h a b) : ℕ) : K), mul_assoc]
    have hm := genusBasic_mem_one_mul _ (hn (h a b)) (k : 𝓞 K)
    rwa [map_natCast] at hm
  intro M hM x hx y hy
  have hM' : Submodule.IsLattice K M ∧ SameGenus h L M := hM
  exact genusScale_transfer hinj hstar h _ L M hM'.2 hLd x hx y hy

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.MajLattice
section
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajLatticeAux

variable {K : Type*} [Field K] [NumberField K]

theorem majLattice_common (t : Finset K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ t, IsIntegral ℤ ((d : K) * a) := by
  first | exact UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common .. | (apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› t | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K

end MajLatticeAux

section MajLatticeMain

variable {K V ι : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

def majLattice_u (z : ι → mixedSpace K) (v : InfinitePlace K) : ι → ℂ :=
  fun i => (z i).2 ⟨v, IsTotallyComplex.isComplex v⟩

def majLattice_Traw (X : InfinitePlace K → Matrix ι ι ℂ) :
    (ι → mixedSpace K) →ₗ[ℝ] (InfinitePlace K × ι × Fin 2 → ℝ) where
  toFun z p := if p.2.2 = 0 then (((X p.1)⁻¹ *ᵥ majLattice_u z p.1) p.2.1).re
    else (((X p.1)⁻¹ *ᵥ majLattice_u z p.1) p.2.1).im
  map_add' z z' := by
    funext p
    have : majLattice_u (z + z') p.1 = majLattice_u z p.1 + majLattice_u z' p.1 := rfl
    simp only [this, Matrix.mulVec_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' r z := by
    funext p
    have : majLattice_u (r • z) p.1 = r • majLattice_u z p.1 := rfl
    simp only [this, Matrix.mulVec_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

def majLattice_alt (X : InfinitePlace K → Matrix ι ι ℂ) :
    (ι → mixedSpace K) →ₗ[ℝ] EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    majLattice_Traw X

theorem majLattice_realize_eq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    realize b X x = majLattice_alt X (fun i => mixedEmbedding K (b.repr x i)) := by
  rfl

theorem majLattice_T_injective (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) : Function.Injective (majLattice_alt X) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hu : ∀ v, majLattice_u z v = 0 := by
    intro v
    have hw : (X v)⁻¹ *ᵥ majLattice_u z v = 0 := by
      funext i
      have h0 := congrArg (fun w => w (v, i, 0)) hz
      have h1 := congrArg (fun w => w (v, i, 1)) hz
      simp [majLattice_alt, majLattice_Traw] at h0 h1
      exact Complex.ext h0 h1
    have := congrArg (fun w => X v *ᵥ w) hw
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v)] using this
  funext i
  refine Prod.ext (funext fun w => absurd w.2
    (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _))) (funext fun w => ?_)
  simpa [majLattice_u] using congrFun (hu w.1) i

theorem majLattice_finrank :
    finrank ℝ (ι → mixedSpace K) =
      finrank ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) := by
  have hc : nrComplexPlaces K = Fintype.card (InfinitePlace K) := by
    classical
    rw [nrComplexPlaces]
    convert Fintype.card_congr (Equiv.subtypeUnivEquiv (IsTotallyComplex.isComplex (K := K)))
  rw [finrank_euclideanSpace, Module.finrank_pi_fintype]
  simp only [mixedEmbedding.finrank, IsTotallyComplex.finrank, hc, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
  ring

def majLattice_B (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    Basis (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ
      (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :=
  (Pi.basis fun _ : ι => latticeBasis K).map
    (LinearMap.linearEquivOfInjective (majLattice_alt X) (majLattice_T_injective X hX)
      majLattice_finrank)

theorem majLattice_mem_span (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : ∀ i, IsIntegral ℤ (b.repr x i)) :
    realize b X x ∈ Submodule.span ℤ (Set.range (majLattice_B X hX)) := by
  refine ((majLattice_B X hX).mem_span_iff_repr_mem ℤ _).mpr fun k => ?_
  have hr : (majLattice_B X hX).repr (realize b X x) k =
      (latticeBasis K).repr (mixedEmbedding K (b.repr x k.1)) k.2 := by
    rw [majLattice_realize_eq, show majLattice_alt X (fun i => mixedEmbedding K (b.repr x i)) =
      LinearMap.linearEquivOfInjective (majLattice_alt X) (majLattice_T_injective X hX)
        majLattice_finrank (fun i => mixedEmbedding K (b.repr x i)) from rfl]
    simp only [majLattice_B, Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Pi.basis_repr]
  rw [hr]
  have hmem : mixedEmbedding K (b.repr x k.1) ∈
      Submodule.span ℤ (Set.range (latticeBasis K)) := by
    rw [mem_span_latticeBasis]
    exact LinearMap.mem_range.mpr ⟨⟨_, hx k.1⟩, rfl⟩
  exact ((latticeBasis K).mem_span_iff_repr_mem ℤ _).mp hmem k.2

theorem majLattice_B_apply (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (k : Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 K)) :
    majLattice_B X hX k = realize b X (integralBasis K k.2 • b k.1) := by
  rw [majLattice_realize_eq]
  have : (fun i => mixedEmbedding K (b.repr (integralBasis K k.2 • b k.1) i)) =
      Pi.single k.1 (latticeBasis K k.2) := by
    funext i
    rcases eq_or_ne i k.1 with rfl | h
    · simp [Algebra.smul_def]
    · simp [h]
  rw [this]
  simp [majLattice_B]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem majLattice_exists_c (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ L := by
  first | exact Bl.general_b_fact_second_rest.goal1 .. | (apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL y | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V | exact @Bl.general_b_fact_second_rest.goal1 K

theorem majLattice_exists_d (b : Basis ι K V) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((d : K) * b.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd, ht⟩ := majLattice_common (s.biUnion fun g => Finset.univ.image fun i => b.repr g i)
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    exact ht _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro i
    simp only [map_add, Finsupp.add_apply, mul_add]
    exact (hx i).add (hy i)
  | smul r x _ hx =>
    intro i
    have : b.repr (r • x) i = algebraMap (𝓞 K) K r * b.repr x i := by
      rw [← algebraMap_smul K r x, map_smul]; rfl
    rw [this, mul_left_comm]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx i)

theorem majLattice_mem_zmap (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    w ∈ zmap (realize b X) L ↔ ∃ x ∈ L, realize b X x = w := Iff.rfl

end MajLatticeMain

theorem majLattice : MajLattice := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX L hL
  obtain ⟨d, hd, hdL⟩ := majLattice_exists_d b L hL.fg
  have hd' : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
  constructor
  · have hmaps : Set.MapsTo (fun w => (d : ℝ) • w)
        (zmap (realize b X) L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))
        (Submodule.span ℤ (Set.range (majLattice_B X hX)) :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := (majLattice_mem_zmap b X L w).mp hw
      have h1 : (d : ℝ) • realize b X x = realize b X (d • x) := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      simp only [h1]
      apply majLattice_mem_span
      intro i
      have h2 : b.repr (d • x) i = (d : K) * b.repr x i := by
        rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
      rw [h2]
      exact hdL x hx i
    have : DiscreteTopology (Submodule.span ℤ (Set.range (majLattice_B X hX)) :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) :=
      inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (majLattice_B X hX))))
    refine DiscreteTopology.of_continuous_injective
      ((continuous_const_smul (d : ℝ)).restrict hmaps) ?_
    intro p q hpq
    apply Subtype.ext
    have := congrArg Subtype.val hpq
    exact smul_right_injective _ hd' this
  · rw [eq_top_iff, ← (majLattice_B X hX).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hc, hcL⟩ := majLattice_exists_c L hL.span_eq_top (b k.1)
    have hc' : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have hmem : (c : ℝ) • majLattice_B X hX k ∈ zmap (realize b X) L := by
      refine (majLattice_mem_zmap b X L _).mpr
        ⟨(RingOfIntegers.basis K k.2) • (c • b k.1), L.smul_mem _ hcL, ?_⟩
      rw [majLattice_B_apply b, integralBasis_apply, algebraMap_smul, smul_comm, map_zsmul,
        Int.cast_smul_eq_zsmul]
    have := Submodule.smul_mem (Submodule.span ℝ
      (zmap (realize b X) L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))
      (c : ℝ)⁻¹ (Submodule.subset_span hmem)
    rwa [inv_smul_smul₀ hc'] at this

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.OpBound
section
open NumberField Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section OpBoundAux

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem opBound_cnorm_nonneg (u : ι → ℂ) : 0 ≤ cnorm u := Real.sqrt_nonneg _

theorem opBound_cnorm_sq (u : ι → ℂ) : cnorm u ^ 2 = ∑ i, ‖u i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)

theorem opBound_normSq (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (z : V) :
    ‖realize b X z‖ ^ 2 = ∑ v, cnorm (fcoord b X v z) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, opBound_cnorm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  show ‖realizeRaw b X z (v, i, 0)‖ ^ 2 + ‖realizeRaw b X z (v, i, 1)‖ ^ 2 = _
  simp only [realizeRaw, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (by decide : (1 : Fin 2) ≠ 0),
    if_true, Real.norm_eq_abs, sq_abs, Complex.sq_norm,
    Complex.normSq_apply]
  ring

theorem opBound_vecAt_sub (b : Module.Basis ι K V) (v : InfinitePlace K) (x y : V) :
    vecAt b v (x - y) = vecAt b v x - vecAt b v y := by
  funext i; simp [vecAt, map_sub]

theorem opBound_vecAt_map (b : Module.Basis ι K V) (v : InfinitePlace K) (g : V →ₗ[K] V) (y : V) :
    vecAt b v (g y) = matAt b v g *ᵥ vecAt b v y := by
  funext i
  simp only [vecAt, matAt]
  rw [← LinearMap.toMatrix_mulVec_repr b b g y, RingHom.map_mulVec]
  rfl

theorem opBound_fcoord (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (g : V →ₗ[K] V) (y : V) :
    fcoord b X v (g y - y) = (X v)⁻¹ *ᵥ ((matAt b v g - 1) *ᵥ vecAt b v y) := by
  rw [fcoord, opBound_vecAt_sub, opBound_vecAt_map, Matrix.sub_mulVec, Matrix.one_mulVec]

end OpBoundAux

theorem opBound : OpBound := by
  intro K V ι _ _ _ _ _ _ _ b X g δ hδ hO y
  have hb : ∀ v, cnorm (fcoord b X v (g y - y)) ≤ δ * cnorm (fcoord b X v y) := by
    intro v
    rw [opBound_fcoord]
    exact hO v (vecAt b v y)
  have hsq : ‖realize b X (g y - y)‖ ^ 2 ≤ (δ * ‖realize b X y‖) ^ 2 := by
    rw [mul_pow, opBound_normSq, opBound_normSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    calc cnorm (fcoord b X v (g y - y)) ^ 2 ≤ (δ * cnorm (fcoord b X v y)) ^ 2 :=
          pow_le_pow_left₀ (opBound_cnorm_nonneg _) (hb v) 2
      _ = δ ^ 2 * cnorm (fcoord b X v y) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end Formalism.HermitianLatticesTheory
end
end

