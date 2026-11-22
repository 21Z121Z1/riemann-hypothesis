import Formalism.CharacterColumnKernels.Bundle0001
import Lemmata.SecondBlockLemmaA.Imports
import Lemmata.AddValuationProducts.AddValProd

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.CongMem
section
namespace Formalism.NG

theorem points : StatPoints := by
  intro O B Ω _ _ _ _ _ _ _ _ _ _ hinj b hb
  by_contra hb0
  have hnil : b ∉ sInf (minimalPrimes B) := by
    rw [minimalPrimes, Ideal.sInf_minimalPrimes]
    intro h
    have h' : b ∈ nilradical B := h
    rw [nilradical_eq_zero] at h'
    exact hb0 h'
  obtain ⟨P, hP, hbP⟩ : ∃ P ∈ minimalPrimes B, b ∉ P := by
    rw [Ideal.mem_sInf] at hnil
    push Not at hnil
    exact hnil
  have hPprime : P.IsPrime := hP.1.1
  have hcomap : P.comap (algebraMap O B) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_bot]
    by_contra ha0
    have hnzd : algebraMap O B a ∈ nonZeroDivisors B := by
      rw [mem_nonZeroDivisors_iff_right]
      intro x hx
      have hs : a • x = 0 := by rw [Algebra.smul_def, mul_comm, hx]
      exact (smul_eq_zero.mp hs).resolve_left ha0
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha hnzd
  have : IsDomain (B ⧸ P) := Ideal.Quotient.isDomain P
  have hinjS : Function.Injective (algebraMap O (B ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : algebraMap O B a ∈ P := by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem] at ha
      exact ha
    have : a ∈ P.comap (algebraMap O B) := ha'
    rw [hcomap] at this
    exact (Ideal.mem_bot).mp this
  have : Module.IsTorsionFree O (B ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjS
  have : Module.IsTorsionFree O Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  let L : (B ⧸ P) →ₐ[O] Ω := IsAlgClosed.lift
  have hker : RingHom.ker (L : (B ⧸ P) →+* Ω) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := O)
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap O Ω a = 0 := by
      rw [← L.commutes a]; exact ha
    rw [Ideal.mem_bot]
    exact hinj (by rw [this, map_zero])
  have hφ := hb (L.comp (Ideal.Quotient.mkₐ O P))
  have hmem : Ideal.Quotient.mk P b ∈ RingHom.ker (L : (B ⧸ P) →+* Ω) := by
    rw [RingHom.mem_ker]
    exact hφ
  rw [hker, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hbP hmem

end Formalism.NG
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.DetTri
section
open Finset

noncomputable section

namespace Formalism.NG

theorem detTri : StatDetTri := by
  unfold StatDetTri bigMat
  intro R O _ g d _ _ _ _ α _ ρ b hb Θ
  have hM : Matrix.BlockTriangular (fun p q : g × d => ρ (Θ p.1 q.1) p.2 q.2) (fun p => b p.2) := by
    intro i j hij
    exact hb (Θ i.1 j.1) hij
  rw [hM.det]
  rcases isEmpty_or_nonempty g with hg | ⟨⟨g0⟩⟩
  · haveI := hg
    rw [Finset.univ_eq_empty, Finset.image_empty, Finset.prod_empty]
    symm
    apply Finset.prod_eq_one
    intro k _
    exact Matrix.det_isEmpty
  · have himg : (univ : Finset (g × d)).image (fun p => b p.2) = (univ : Finset d).image b := by
      ext k
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
      constructor
      · rintro ⟨_, i, hi⟩
        exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨g0, i, hi⟩
    rw [himg]
    apply Finset.prod_congr rfl
    intro k _
    let e : g × {i : d // b i = k} ≃ {p : g × d // b p.2 = k} :=
      { toFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
        invFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc _ = Matrix.det ((Matrix.toSquareBlock _ (fun p : g × d => b p.2) k).submatrix e e) :=
          (Matrix.det_submatrix_equiv_self e _).symm
      _ = _ := congrArg Matrix.det (Matrix.ext fun x y => rfl)

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
section
open Module IsDiscreteValuationRing Matrix

noncomputable section

namespace Formalism.NG

namespace IdempotentNormalFormsLenFacts

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma length_quot_span (a : O) :
    Module.length O (O ⧸ Ideal.span ({a} : Set O)) = addVal O a :=
  Ring.ord_eq_addVal a

lemma addVal_prod {ι : Type*} (s : Finset ι) (a : ι → O) :
    addVal O (∏ i ∈ s, a i) = ∑ i ∈ s, addVal O (a i) := by
  first | exact Bl.SecondBlockLemmaA.goal1 .. | (apply Bl.SecondBlockLemmaA.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaA.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaA.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaA.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaA.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι s a | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι s | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› ι | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O ‹_› | exact @Bl.SecondBlockLemmaA.goal1 O

lemma length_quot_eq_addVal_det {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Submodule O (ι → O)) (e : (ι → O) ≃ₗ[O] N) :
    Module.length O ((ι → O) ⧸ N) =
      addVal O (LinearMap.det (N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N))) := by
  first | exact Bl.AddValuationProducts.goal1 .. | (apply Bl.AddValuationProducts.goal1 <;> assumption) | (intros; apply Bl.AddValuationProducts.goal1 <;> assumption) | (apply @Bl.AddValuationProducts.goal1 <;> assumption) | (intros; apply @Bl.AddValuationProducts.goal1 <;> assumption) | (apply @Bl.AddValuationProducts.goal1 <;> first | assumption | infer_instance) | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› N e | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› N | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› ι | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› ‹_› | exact @Bl.AddValuationProducts.goal1 O ‹_› | exact @Bl.AddValuationProducts.goal1 O

lemma mk_eq_zero_iff (y : FractionRing O) :
    (Submodule.Quotient.mk y : KO O) = 0 ↔ ∃ x : O, algebraMap O (FractionRing O) x = y := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]

lemma matQ_mk {ι : Type*} [Fintype ι] (A : Matrix ι ι O) (y : ι → FractionRing O) :
    matQ O A (fun i => (Submodule.Quotient.mk (y i) : KO O)) =
      fun i => (Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O)) *ᵥ y) i) : KO O) := by
  ext i
  show ∑ j, A i j • (Submodule.mkQ (1 : Submodule O (FractionRing O)) (y j)) =
    Submodule.mkQ (1 : Submodule O (FractionRing O))
      ((A.map (algebraMap O (FractionRing O)) *ᵥ y) i)
  rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.map_apply, Algebra.smul_def]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev AK (A : Matrix ι ι O) : Matrix ι ι (FractionRing O) := A.map (algebraMap O (FractionRing O))

lemma isUnit_det_AK (A : Matrix ι ι O) (hd : A.det ≠ 0) : IsUnit (AK A).det := by
  rw [isUnit_iff_ne_zero, AK, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h => hd (IsFractionRing.injective O (FractionRing O) (by rw [h, map_zero]))

def phi (A : Matrix ι ι O) : (ι → O) →ₗ[O] (ι → KO O) where
  toFun x i := Submodule.Quotient.mk (((AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j))) i)
  map_add' x y := by
    ext i
    have : (fun j => algebraMap O (FractionRing O) (x j + y j)) =
        (fun j => algebraMap O (FractionRing O) (x j)) +
          (fun j => algebraMap O (FractionRing O) (y j)) := by
      ext j; simp
    simp only [Pi.add_apply]
    rw [this, Matrix.mulVec_add, Pi.add_apply, Submodule.Quotient.mk_add]
  map_smul' r x := by
    ext i
    have : (fun j => algebraMap O (FractionRing O) (r • x j)) =
        algebraMap O (FractionRing O) r • (fun j => algebraMap O (FractionRing O) (x j)) := by
      ext j; simp
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [this, Matrix.mulVec_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    simp [Algebra.smul_def]

lemma phi_apply (A : Matrix ι ι O) (x : ι → O) :
    phi A x = fun i => (Submodule.Quotient.mk
      (((AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j))) i) : KO O) := rfl

lemma map_mulVec_fun (A : Matrix ι ι O) (z : ι → O) :
    (fun i => algebraMap O (FractionRing O) ((A *ᵥ z) i)) =
      AK A *ᵥ (fun j => algebraMap O (FractionRing O) (z j)) := by
  ext i
  exact RingHom.map_mulVec _ A z i

lemma range_phi (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    LinearMap.range (phi A) = LinearMap.ker (matQ O A) := by
  have hu := isUnit_det_AK A hd
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, phi_apply, matQ_mk, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨x i, rfl⟩
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    choose y hy using fun i => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (v i)
    have hv' : v = fun i => (Submodule.Quotient.mk (y i) : KO O) := funext fun i => (hy i).symm
    rw [hv', matQ_mk] at hv
    choose x hx using fun i => (mk_eq_zero_iff _).mp (congrFun hv i)
    refine ⟨x, ?_⟩
    have hx' : (fun j => algebraMap O (FractionRing O) (x j)) = AK A *ᵥ y := funext hx
    rw [phi_apply, hx', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, hv']

lemma ker_phi (A : Matrix ι ι O) (hd : A.det ≠ 0) :
    LinearMap.ker (phi A) = LinearMap.range (Matrix.mulVecLin A) := by
  have hu := isUnit_det_AK A hd
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_range, phi_apply]
  constructor
  · intro h
    choose z hz using fun i => (mk_eq_zero_iff _).mp (congrFun h i)
    refine ⟨z, ?_⟩
    have hz' : (fun j => algebraMap O (FractionRing O) (z j)) =
        (AK A)⁻¹ *ᵥ (fun j => algebraMap O (FractionRing O) (x j)) := funext hz
    funext i
    apply IsFractionRing.injective O (FractionRing O)
    rw [Matrix.mulVecLin_apply]
    have := congrFun (map_mulVec_fun A z) i
    rw [this, hz', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVecLin_apply, map_mulVec_fun, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨z i, rfl⟩

lemma length_ker_of_det_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι O)
    (hd : A.det ≠ 0) :
    Module.length O (LinearMap.ker (matQ O A)) = addVal O A.det := by
  have hinj : Function.Injective (Matrix.mulVecLin A) :=
    Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  let N := LinearMap.range (Matrix.mulVecLin A)
  let e : (ι → O) ≃ₗ[O] N := LinearEquiv.ofInjective _ hinj
  have h1 := length_quot_eq_addVal_det N e
  have h2 : N.subtype ∘ₗ (e : (ι → O) →ₗ[O] N) = Matrix.mulVecLin A := LinearMap.ext fun x => rfl
  have h3 : LinearMap.det (Matrix.mulVecLin A) = A.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  rw [← (LinearEquiv.ofEq _ _ (range_phi A hd)).length_eq,
    ← (LinearMap.quotKerEquivRange (phi A)).length_eq,
    (Submodule.quotEquivOfEq _ _ (ker_phi A hd)).length_eq, h1, h2, h3]

lemma length_ker_of_det_eq_zero (A : Matrix ι ι O) (hd : A.det = 0) :
    Module.length O (LinearMap.ker (matQ O A)) = ⊤ := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun i => addVal O (w i))
    ⟨j, Finset.mem_univ _⟩
  have hwi0 : w i0 ≠ 0 := by
    intro h
    have := hi0 j (Finset.mem_univ _)
    rw [h, addVal_zero, top_le_iff, addVal_eq_top_iff] at this
    exact hj this
  choose w' hw' using fun i => (addVal_le_iff_dvd (a := w i0) (b := w i)).mp
    (hi0 i (Finset.mem_univ _))
  have hw'i0 : w' i0 = 1 := by
    have := hw' i0
    exact (mul_left_cancel₀ hwi0 (this.symm.trans (mul_one _).symm))
  have hAw' : A *ᵥ w' = 0 := by
    have : w = w i0 • w' := funext fun i => by simp [hw' i]
    rw [this, Matrix.mulVec_smul] at hw
    exact (smul_eq_zero.mp hw).resolve_left hwi0
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  rw [ENat.eq_top_iff_forall_ge]
  intro k
  let c : FractionRing O := (algebraMap O (FractionRing O) (ϖ ^ k))⁻¹
  have hc : algebraMap O (FractionRing O) (ϖ ^ k) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O (FractionRing O))]
    exact fun h => pow_ne_zero k hϖ0 (IsFractionRing.injective O (FractionRing O) h)
  have hc1 : algebraMap O (FractionRing O) (ϖ ^ k) * c = 1 := mul_inv_cancel₀ hc
  let v : ι → KO O := fun i => Submodule.Quotient.mk (c * algebraMap O (FractionRing O) (w' i))
  have hv : v ∈ LinearMap.ker (matQ O A) := by
    rw [LinearMap.mem_ker]
    have : (fun i => c * algebraMap O (FractionRing O) (w' i)) =
        c • (fun i => algebraMap O (FractionRing O) (w' i)) := by
      ext i; simp
    show matQ O A (fun i => (Submodule.Quotient.mk (c * algebraMap O (FractionRing O) (w' i)) : KO O)) = 0
    rw [matQ_mk, this, Matrix.mulVec_smul, ← map_mulVec_fun, hAw']
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨0, by simp⟩
  let χ : O →ₗ[O] (ι → KO O) := LinearMap.toSpanSingleton O _ v
  have hker : LinearMap.ker χ = Ideal.span ({ϖ ^ k} : Set O) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton]
    constructor
    · intro h
      have h0 := congrFun h i0
      simp only [v, Pi.smul_apply, Pi.zero_apply, hw'i0, map_one, mul_one,
        ← Submodule.Quotient.mk_smul] at h0
      obtain ⟨z, hz⟩ := (mk_eq_zero_iff _).mp h0
      refine ⟨z, ?_⟩
      apply IsFractionRing.injective O (FractionRing O)
      rw [Algebra.smul_def] at hz
      rw [map_mul, hz, mul_left_comm, hc1, mul_one]
    · rintro ⟨z, rfl⟩
      ext i
      simp only [v, Pi.smul_apply, Pi.zero_apply, ← Submodule.Quotient.mk_smul]
      refine (mk_eq_zero_iff _).mpr ⟨z * w' i, ?_⟩
      rw [Algebra.smul_def, map_mul, map_mul,
        show algebraMap O (FractionRing O) (ϖ ^ k) * algebraMap O (FractionRing O) z *
          (c * algebraMap O (FractionRing O) (w' i)) =
          (algebraMap O (FractionRing O) (ϖ ^ k) * c) *
          (algebraMap O (FractionRing O) z * algebraMap O (FractionRing O) (w' i)) by ring,
        hc1, one_mul]
  have hrange : LinearMap.range χ ≤ LinearMap.ker (matQ O A) := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.smul_mem _ x hv
  have hle := Module.length_le_of_injective (Submodule.inclusion hrange)
    (Submodule.inclusion_injective hrange)
  rw [← (LinearMap.quotKerEquivRange χ).length_eq,
    (Submodule.quotEquivOfEq _ _ hker).length_eq, length_quot_span, hϖ.addVal_pow] at hle
  simpa using hle

end IdempotentNormalFormsLenFacts

open IdempotentNormalFormsLenFacts

theorem lenKer : StatLenKer := by
  intro O _ _ _ ι _ _ A
  by_cases hd : A.det = 0
  · rw [length_ker_of_det_eq_zero A hd, hd, addVal_zero]
  · exact length_ker_of_det_ne_zero A hd

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.ProdEraseZero
section
open Finset

namespace Formalism.NG

private lemma vInt_eq_emult (l : ℕ) [hl : Fact l.Prime] {z : ℤ} (hz : z ≠ 0) :
    (padicValInt l z : ℕ∞) = emultiplicity (l : ℤ) z := by
  rw [padicValInt.of_ne_one_ne_zero hl.out.ne_one hz]
  exact (FiniteMultiplicity.emultiplicity_eq_multiplicity
    (Int.finiteMultiplicity_iff.mpr ⟨by simpa using hl.out.ne_one, hz⟩)).symm

theorem powSubPow : StatPowSubPow := by
  intro l hl hl2 x hx1 hx2 a b hab
  have hp : l.Prime := hl.out
  have hodd : Odd l := hp.odd_of_ne_two hl2
  have hpi : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by
      have := dvd_sub h hx1
      simpa using this
    exact hpi.not_dvd_one h1
  have hx1ne : x - 1 ≠ 0 := by
    intro h; exact hx2 (by rw [h]; exact dvd_zero _)
  have hv1 : padicValInt l (x - 1) = 1 := by
    have h1 := (padicValInt_dvd_iff (p := l) 1 (x - 1)).mp (by simpa using hx1)
    have h2 : ¬ (2 ≤ padicValInt l (x - 1)) := fun h =>
      hx2 ((padicValInt_dvd_iff (p := l) 2 (x - 1)).mpr (Or.inr h))
    rcases h1 with h1 | h1
    · exact absurd h1 hx1ne
    · omega
  set n := b - a with hn
  have hn0 : n ≠ 0 := by omega
  have hlte := Int.emultiplicity_pow_sub_pow hp hodd (x := x) (y := 1) (by simpa using hx1) hx n
  rw [one_pow] at hlte
  rw [← vInt_eq_emult l hx1ne, hv1, ← padicValNat_eq_emultiplicity_of_ne_one hp.ne_one hn0] at hlte
  have hne : x ^ n - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hlte
    have h' : ((1 + padicValNat l n : ℕ) : ℕ∞) = ⊤ := by push_cast; exact hlte.symm
    exact ENat.natCast_ne_top _ h'
  have hv : padicValInt l (x ^ n - 1) = 1 + padicValNat l n := by
    rw [← vInt_eq_emult l hne] at hlte
    exact_mod_cast hlte
  have hxa : x ^ a ≠ 0 := pow_ne_zero _ (fun h => hx (by rw [h]; exact dvd_zero _))
  have hfac : x ^ b - x ^ a = x ^ a * (x ^ n - 1) := by
    have : b = a + n := by omega
    rw [this, pow_add]; ring
  rw [hfac, padicValInt.mul hxa hne, hv,
    padicValInt.eq_zero_of_not_dvd (fun h => hx (hpi.dvd_of_dvd_pow h))]
  ring

private lemma prod_erase_zero {M : Type*} [CommMonoid M] (t : ℕ) (f : Fin (t + 1) → M) :
    ∏ i ∈ univ.erase (0 : Fin (t + 1)), f i = ∏ i : Fin t, f i.succ := by
  rw [Fin.univ_succ, Finset.erase_cons, Finset.prod_map]
  rfl

theorem deltaVal : StatDeltaVal := by
  intro l hl hl2 u hu w t
  have hp : l.Prime := hl.out
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hp.two_le
  have hnot : ¬ (l : ℤ) ^ 2 ∣ (1 + (l : ℤ)) - 1 := by
    rw [show (1 + (l : ℤ)) - 1 = (l : ℤ) by ring]
    intro h
    have := Int.le_of_dvd (by omega) h
    nlinarith
  have hF : ∀ i : ℕ, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) ≠ 0 ∧
      padicValInt l (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) =
        1 + padicValNat l (i + 1) := by
    intro i
    have hrw : u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)) =
        (-u) * ((1 + (l : ℤ)) ^ (w + (i + 1)) - (1 + (l : ℤ)) ^ w) := by ring
    have hps := powSubPow l hl2 (1 + (l : ℤ)) (by simp) hnot w (w + (i + 1)) (by omega)
    rw [Nat.add_sub_cancel_left] at hps
    have hne : (1 + (l : ℤ)) ^ (w + (i + 1)) - (1 + (l : ℤ)) ^ w ≠ 0 := by
      intro h; rw [h, padicValInt.zero] at hps; omega
    have hu0 : -u ≠ 0 := by
      intro h; exact hu (by rw [neg_eq_zero.mp h]; exact dvd_zero _)
    rw [hrw]
    refine ⟨mul_ne_zero hu0 hne, ?_⟩
    rw [padicValInt.mul hu0 hne, hps, padicValInt.eq_zero_of_not_dvd (by rwa [dvd_neg])]
    ring
  have hclaim : ∀ s : ℕ,
      (∏ i ∈ range s, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)))) ≠ 0 ∧
      padicValInt l (∏ i ∈ range s, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)))) =
        s + padicValNat l s.factorial := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [prod_range_succ]
      refine ⟨mul_ne_zero ih.1 (hF s).1, ?_⟩
      rw [padicValInt.mul ih.1 (hF s).1, ih.2, (hF s).2, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero s) (Nat.factorial_ne_zero s)]
      ring
  unfold delta
  rw [prod_erase_zero]
  simp only [Fin.val_succ, Fin.val_zero, add_zero]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) t]
  exact (hclaim t).2

theorem deltaValLe : StatDeltaValLe := by
  intro l hl hl2 u hu w t
  rw [deltaVal l hl2 u hu w t]
  have := padicValNat_factorial_le (p := l) t
  omega

end Formalism.NG
end

