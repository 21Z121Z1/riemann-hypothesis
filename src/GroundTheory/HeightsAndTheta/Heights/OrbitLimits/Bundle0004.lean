import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeImageZLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.mixedEmbedding

theorem LatticeImageZLattice.exists_int_mul_integral {F : Type} [Field F] [NumberField F]
    (L : AddSubgroup F) (hfg : L.FG) : ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ L, IsIntegral ℤ (N • x) := by
  obtain ⟨S, hS⟩ := hfg
  have halg : ∀ s : F, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • s) := fun s =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple
  choose y hy0 hyint using halg
  refine ⟨∏ s ∈ S, y s, Finset.prod_ne_zero_iff.mpr fun s _ => hy0 s, ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem y hs
    rw [hc, mul_comm, mul_smul]
    exact (hyint s).zsmul c
  | zero => simpa using isIntegral_zero
  | add a b _ _ ha hb => simpa [smul_add] using ha.add hb
  | neg a _ ha => simpa [smul_neg] using ha.neg

open scoped Classical in

theorem LatticeImageZLattice.proof : LatticeImageZLattice.Statement := by
  intro F _ _ L hfg hfull
  obtain ⟨N, hN0, hLint⟩ := LatticeImageZLattice.exists_int_mul_integral L hfg

  let e : mixedSpace F →ₗ[ℝ] mixedSpace F := (N : ℝ) • LinearMap.id
  have he₁ : Continuous e := continuous_const_smul (N : ℝ)
  have he₂ : Function.Injective e := fun a b h =>
    smul_right_injective (mixedSpace F) (Int.cast_ne_zero.mpr hN0 : (N : ℝ) ≠ 0) h
  have hdisc : DiscreteTopology (ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e) :=
    ZLattice.comap_discreteTopology ℝ _ he₁ he₂
  have hle : (latticeImage F L : Set (mixedSpace F)) ⊆
      ZLattice.comap ℝ (mixedEmbedding.integerLattice F) e := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage L z).mp hz
    show e (mixedEmbedding F x) ∈ mixedEmbedding.integerLattice F
    refine ⟨⟨N • x, hLint x hx⟩, ?_⟩
    change mixedEmbedding F (N • x) = (N : ℝ) • mixedEmbedding F x
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have : DiscreteTopology (latticeImage F L) := DiscreteTopology.of_subset hdisc hle
  refine ⟨this, ⟨?_⟩⟩

  rw [eq_top_iff, ← (latticeBasis F).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨n, hn, hnL⟩ := hfull (integralBasis F i)
  have hmem : mixedEmbedding F ((n : F) * integralBasis F i) ∈ latticeImage F L :=
    (mem_latticeImage L _).mpr ⟨_, hnL, rfl⟩
  have hb : latticeBasis F i = (n : ℝ)⁻¹ • mixedEmbedding F ((n : F) * integralBasis F i) := by
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul, latticeBasis_apply]
  rw [hb]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNumberFieldBoxCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory

namespace NumberFieldBoxCount

theorem inf_full {F : Type*} [Field F] {L B : AddSubgroup F}
    (hL : ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) (hB : ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ B) :
    ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L ⊓ B := by
  intro x
  obtain ⟨n, hn, hnx⟩ := hL x
  obtain ⟨m, hm, hmx⟩ := hB x
  refine ⟨m * n, Nat.mul_pos hm hn, ?_, ?_⟩
  · have h := L.nsmul_mem hnx m
    rw [nsmul_eq_mul, ← mul_assoc] at h
    simpa using h
  · have h := B.nsmul_mem hmx n
    rw [nsmul_eq_mul, ← mul_assoc] at h
    simpa [mul_comm] using h

theorem fg_of_le {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} (hK : K.FG) (hHK : H ≤ K) : H.FG := by
  obtain ⟨S, hS⟩ := hK
  have hK' : (AddSubgroup.toIntSubmodule K).FG := ⟨S, by rw [← AddSubgroup.toIntSubmodule_closure, hS]⟩
  obtain ⟨T, hT⟩ := hK'.of_le (S := AddSubgroup.toIntSubmodule H) hHK
  exact ⟨T, AddSubgroup.toIntSubmodule.injective (by rw [AddSubgroup.toIntSubmodule_closure, hT])⟩

theorem forall_le_iff {F : Type*} [Field F] [NumberField F] (ρ : (F →+* ℂ) → ℝ)
    (hρc : ∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) (x : F) :
    (∀ σ : F →+* ℂ, ‖σ x‖ ≤ ρ σ) ↔ ∀ w : InfinitePlace F, normAtPlace w (mixedEmbedding F x) ≤ ρ w.embedding := by
  refine ⟨fun h w => ?_, fun h σ => ?_⟩
  · rw [normAtPlace_apply, ← norm_embedding_eq]
    exact h _
  · have h' := h (InfinitePlace.mk σ)
    rw [normAtPlace_apply, InfinitePlace.apply] at h'
    rcases embedding_mk_eq σ with e | e
    · rwa [e] at h'
    · rwa [e, hρc] at h'

theorem card_eq {F : Type*} [Field F] [NumberField F] (ρ : (F →+* ℂ) → ℝ)
    (hρc : ∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) (L : AddSubgroup F) :
    Nat.card {x : L // ∀ σ : F →+* ℂ, ‖σ (x : F)‖ ≤ ρ σ} =
      {y : mixedSpace F | y ∈ latticeImage F L ∧ ∀ w, normAtPlace w y ≤ ρ w.embedding}.ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_eq_of_bijective (fun x => ⟨mixedEmbedding F x.1,
    (mem_latticeImage _ _).2 ⟨x.1, x.1.2, rfl⟩, (forall_le_iff ρ hρc _).1 x.2⟩) ⟨?_, ?_⟩
  · intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (mixedEmbedding_injective F h'))
  · rintro ⟨y, hy, hyb⟩
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage _ _).1 hy
    exact ⟨⟨⟨x, hx⟩, (forall_le_iff ρ hρc x).2 hyb⟩, rfl⟩

theorem relIndex_latticeImage {F : Type*} [Field F] [NumberField F] (H K : AddSubgroup F) :
    (latticeImage F H).toAddSubgroup.relIndex (latticeImage F K).toAddSubgroup = H.relIndex K := by
  simp only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (mixedEmbedding_injective F)

open scoped Classical in

theorem proof (h1 : LatticeImageZLattice.Statement) (h2 : CovolumeRelIndex.Statement)
    (h4 : EmbeddingSumPlaces.Statement) (h5 : MixedBoxCount.Statement) : NumberFieldBoxCount.Statement := by
  intro F _ _ B hB hBf
  obtain ⟨_, _⟩ := h1 F B hB hBf
  refine ⟨Module.finrank ℚ F * Real.log 2 + Real.log (ZLattice.covolume (latticeImage F B)) -
    Real.log (convexBodyLTFactor F : ℝ), ?_⟩
  intro L hL hLf ρ hρ hρc
  obtain ⟨_, _⟩ := h1 F L hL hLf
  obtain ⟨_, _⟩ := h1 F (L ⊓ B) (fg_of_le hL inf_le_left) (inf_full hLf hBf)
  have mono : ∀ {H K : AddSubgroup F}, H ≤ K → latticeImage F H ≤ latticeImage F K := by
    intro H K hHK
    refine (Submodule.toAddSubgroup_le _ _).1 ?_
    simp only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.map_mono hHK
  have cL := h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F L) (mono inf_le_left)
  have cB := h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F B) (mono inf_le_right)
  rw [relIndex_latticeImage, AddSubgroup.inf_relIndex_left] at cL
  rw [relIndex_latticeImage, AddSubgroup.inf_relIndex_right] at cB
  have p0 := ZLattice.covolume_pos (latticeImage F (L ⊓ B)) volume
  have pL := ZLattice.covolume_pos (latticeImage F L) volume
  have pB := ZLattice.covolume_pos (latticeImage F B) volume
  have r1 : (0 : ℝ) < B.relIndex L := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have r2 : (0 : ℝ) < L.relIndex B := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have hgen : genIndex L B = ZLattice.covolume (latticeImage F B) / ZLattice.covolume (latticeImage F L) := by
    rw [genIndex, div_eq_div_iff r2.ne' pL.ne']
    linarith
  obtain ⟨-, hcount⟩ := h5 F (latticeImage F L) (fun w => ρ w.embedding) (fun w => hρ _)
  have hsum := h4 F (fun σ => Real.log (ρ σ)) (fun σ => by simp only [hρc])
  rw [card_eq ρ hρc L, hsum, hgen, Real.log_div pB.ne' pL.ne']
  linarith

end NumberFieldBoxCount

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushMultComplex
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def DivPushMultComplex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I W : Ideal (MRing ι))
    (Wa : Ideal (MRingOver ℂ ι)),
    W ∈ I.minimalPrimes → IsHorizontal W →
    Wa ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes →
    multAt I W = multAt (I.map (MvPolynomial.map (Int.castRingHom ℂ))) Wa

theorem DivPushMultComplex.hyps_inhabited :
    (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∈ (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).minimalPrimes ∧
      IsHorizontal (Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))) ∧
      (Ideal.span {X ⟨(), 0⟩} : Ideal (MRingOver ℂ (PBlk 2))) ∈
        ((Ideal.span {Xc 2 0} : Ideal (MRing (PBlk 2))).map
          (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes := by
  have hprime : (Ideal.span {(Xc 2 0 : MRing (PBlk 2))}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  have hprimeC : (Ideal.span {(X ⟨(), 0⟩ : MRingOver ℂ (PBlk 2))}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  refine ⟨?_, ?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  · rw [IsHorizontal, eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hc
    obtain ⟨q, hq⟩ := hc
    have h := congrArg constantCoeff hq
    simpa using h
  · rw [Ideal.map_span, Set.image_singleton, Xc, map_X, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsFnDegRelDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

def FnDegRelDeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hκv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (i' : ∀ k', ι' k'),
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsChart P' i' →
      haveI := hP'.isPrime
      ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg v P' i' = relDeg ⟨κ, hκv.1⟩ P'

section Inhabitants

def firstFactor : (Σ _ : Unit, Fin 2) → (Σ _ : Fin 2, Fin 2) := fun p => ⟨0, p.2⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMulSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

def LocalGen {Ω : Type} [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (m : Ideal B) (f : Ω) : Prop :=
  (∃ b : B, b ∉ m ∧ (b : Ω) * f ∈ X) ∧ ∀ z ∈ X, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * f

def LocalGenFamily.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (η : Type) [Fintype η] (f : η → Ω),
    Module.Finite ℤ B → (∀ b ∈ B, ∀ z ∈ X, b * z ∈ X) → (∀ i, f i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * f i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B X m (f i)) →
      X ≠ ⊥ ∧ ∃ (ι : Type) (_ : Fintype ι) (a : ι → Ω), (∀ j, a j ∈ X) ∧
        (∀ j, ∃ c ∈ B, c ≠ 0 ∧ c * a j ∈ B) ∧
        ∀ m : Ideal B, m.IsMaximal → ∃ j, ∀ z ∈ X, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * a j

def LocallyPrincipalCoprimeField.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (B : Subring Ω) (M : AddSubgroup Ω) (ι : Type) [Fintype ι]
    (a : ι → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : Ω, x ∈ M ↔ ∃ y ∈ I, (β : Ω) * x = δ * y

def InvertibleProductRep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω)
    (β δ β' δ' : B) (I J : Ideal B),
    β ≠ 0 → δ ≠ 0 → β' ≠ 0 → δ' ≠ 0 →
    (∀ x : Ω, x ∈ M ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) →
    (∀ x : Ω, x ∈ N ↔ ∃ y ∈ J, (β' : Ω) * x = δ' * y) →
    (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      LocalGen B M m (g i) ∧ LocalGen B N m (h i) ∧ LocalGen B P m (g i * h i)) →
      ∀ x : Ω, x ∈ P ↔ ∃ y ∈ I * J, ((β * β' : B) : Ω) * x = (δ * δ' : B) * y

def InvertibleIndexCharP.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (η : Type) [Fintype η] (f : η → Ω),
    ringChar Ω ≠ 0 → Module.Finite ℤ B → (∀ b ∈ B, ∀ z ∈ X, b * z ∈ X) → (∀ i, f i ≠ 0) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B X m (f i)) →
      genIndex X B.toAddSubgroup = 1

end GroundTheory.Heights₂.Heights.Targets
end

