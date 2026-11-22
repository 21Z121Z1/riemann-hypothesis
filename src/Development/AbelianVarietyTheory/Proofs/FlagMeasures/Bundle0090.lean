import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.ColumnDimensionRational
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0088
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0078
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorUnitaryGroupLocal
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CapelliLocality

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma exp_inUH (H K Y : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hY : Yᴴ * H = -(H * Y)) : inUH H (NormedSpace.exp Y) := by
  have h1 : Yᴴ = H * (-Y) * K := by
    calc Yᴴ = Yᴴ * H * K := by rw [Matrix.mul_assoc, hHK, Matrix.mul_one]
      _ = H * (-Y) * K := by rw [hY, Matrix.mul_neg]
  unfold inUH
  rw [← Matrix.exp_conjTranspose, h1, ioh_exp_conj H K (-Y) hKH hHK]
  have h2 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  calc H * NormedSpace.exp (-Y) * K * H * NormedSpace.exp Y
      = H * (NormedSpace.exp (-Y) * (K * H) * NormedSpace.exp Y) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hKH, Matrix.mul_one, h2, Matrix.mul_one]

lemma inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  unfold inUH at *
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha, hb]

lemma rdV_congr (H K X : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hX : Xᴴ * H = -(H * X)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUH H g) :
    RdV X F₁ g = RdV X F₂ g := by
  unfold RdV
  congr 1
  funext t
  refine hF _ (inUH_mul hg (exp_inUH H K _ hKH hHK ?_))
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hX, smul_neg]
  simp

lemma hpart1_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart1 H Z)ᴴ * H = -(H * hpart1 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  unfold hpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [← smul_neg, neg_sub]
  simp

lemma hpart2_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart2 H Z)ᴴ * H = -(H * hpart2 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  unfold hpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [hs, neg_smul, add_comm]

lemma foldr_congr (H : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) (l : List (ℂ × Fin n × Fin n)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) :
    ∀ x, inUH H x →
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ x =
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ x := by
  induction l with
  | nil => simpa using hF
  | cons p l ih =>
    intro x hx
    simp only [List.map_cons, List.foldr_cons]
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ = G₁ at ih ⊢
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ = G₂ at ih ⊢
    unfold Formalism.QuantumDeterminants.Top EabH
    rw [ih x hx, rdV_congr H H⁻¹ _ hKH hHK (hpart1_mem H _ hKH hHK hH) ih hx,
      rdV_congr H H⁻¹ _ hKH hHK (hpart2_mem H _ hKH hHK hH) ih hx]

theorem capelliH_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  intro n ε E _ _ H P Q F₁ F₂ u g hQP hPQ hH hF hg
  have hinv := ioh_Hinv ε H P Q hQP hPQ hH
  have hc : Pᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one]
  have hHK : H * H⁻¹ = 1 := by
    rw [hinv]
    calc H * (Q * Jm ε * Qᴴ) = Pᴴ * (Jm ε * ((P * Q) * (Jm ε * Qᴴ))) := by
          rw [hH]; simp only [Matrix.mul_assoc]
      _ = Pᴴ * Qᴴ := by
          rw [hPQ, Matrix.one_mul, ← Matrix.mul_assoc (Jm ε), Jm_mul_self, Matrix.one_mul]
      _ = 1 := hc
  have hKH : H⁻¹ * H = 1 := mul_eq_one_comm.mp hHK
  have hJ : (Jm ε)ᴴ = Jm ε := by
    unfold Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : ε i <;> simp [h]
  have hHh : Hᴴ = H := by
    rw [hH]
    simp only [Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  unfold capelliH qdetOp qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 : (List.ofFn fun k : Fin n => Formalism.QuantumDeterminants.Top (E := E) (EabH H) (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)) =
        (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), σ k, k)).map
          fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2 := by
    rw [List.map_ofFn]; rfl
  rw [e1]
  exact foldr_congr H hKH hHK hHh _ hF g hg

end GlobalTheory.CapelliLocality

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqNcardPrimesOver
section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColCmp

namespace GlobalTheory.SplitResidue

theorem card_eq_ncard_primesOver (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    Nat.card {w : HeightOneSpectrum (𝓞 E) // (g : 𝓞 E) ∈ w.asIdeal} =
      (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hne : (Ideal.span {(g : ℤ)}) ≠ ⊥ := by simpa using hg.ne_zero
  haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1.asIdeal, w.1.isPrime, ?_⟩) ⟨?_, ?_⟩)
  · haveI := w.1.isPrime
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using w.2
  · intro a b h
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro ⟨P, hP, hPl⟩
    refine ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_⟩, rfl⟩
    simpa using (Ideal.mem_of_liesOver P (Ideal.span {(g : ℤ)}) (g : ℤ)).1
      (Ideal.mem_span_singleton_self _)

theorem residue_and_unramified : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), g.Prime →
    FlagUnipotentStabilizers.SplitsCompletely E g →
    ∀ w : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ w.asIdeal →
      Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod g) ∧ (g : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro E _ _ g hg h w hw
  haveI := w.isPrime
  haveI := Fact.mk hg
  have h' := (card_eq_ncard_primesOver E hg).symm.trans h
  obtain ⟨h1, h2⟩ := GlobalTheory.LocSplit.split_prime hg h' w.asIdeal hw
  refine ⟨?_, h1⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero hg, ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  refine ⟨(RingEquiv.ofBijective (ZMod.castHom (dvd_refl g) (𝓞 E ⧸ w.asIdeal))
    ⟨ZMod.castHom_injective _, fun y => ?_⟩).symm⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨m, hm⟩ := h2 x
  refine ⟨(m : ZMod g), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk w.asIdeal), eq_comm, Ideal.Quotient.eq]
  exact hm

end GlobalTheory.SplitResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdPlace

theorem term_orbit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (ha : S.a = 0)
    {d d₁ : S.Datum} {Λ Λ₁ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (hT₁ : S.IsTerm d₁ Λ₁)
    (hM : S.M d Λ = S.M d₁ Λ₁) : ∃ h ∈ S.H0, h • Λ₁ = Λ := by
  have : IsArtinianRing E := by
    have := L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
    exact IsArtinianRing.of_finite F E
  obtain ⟨u₀, hu₀, hE, hui, hup⟩ := GlobalTheory.T.frameLattice_unimodular_generators_exponent_zero L r k S d Λ hT ha
  obtain ⟨b₀, hbW, hΛ, hbi, hbp⟩ := GlobalTheory.T.hermitianTerm_splits_unimodular_complement L r k S d Λ hT ha
  obtain ⟨c₀, hcW, hΛ₁, hci, hcp⟩ := GlobalTheory.T.hermitianTerm_splits_unimodular_complement L r k S d₁ Λ₁ hT₁ ha
  obtain ⟨u, huo, hus⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm u₀ hui hup
  obtain ⟨b, hbo, hbs⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm b₀ hbi hbp
  obtain ⟨c, hco, hcs⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm c₀ hci hcp
  have hsp : ∀ (w : Fin (k - 1) → S.V) (w₀ : Fin (k - 1) → S.V), (∀ i, w₀ i ∈ S.W0) →
      Submodule.span L.O (Set.range w) = Submodule.span L.O (Set.range w₀) → ∀ i, w i ∈ S.W0 := by
    intro w w₀ h0 he i
    have h1 : w i ∈ Submodule.span L.O (Set.range w₀) := by
      rw [← he]; exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : Submodule.span L.O (Set.range w₀) ≤ S.W0.restrictScalars L.O :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
    exact h2 h1
  have hbW' := hsp b b₀ hbW hbs
  have hcW' := hsp c c₀ hcW hcs
  have huME : ∀ i, u i ∈ S.ME := by
    intro i
    have h1 : u i ∈ Submodule.span L.O (Set.range u₀) := by
      rw [← hus]; exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : Submodule.span L.O (Set.range u₀) ≤ S.ME.restrictScalars L.O :=
      Submodule.span_le.2 (by
        rintro _ ⟨j, rfl⟩
        rw [← hE]; exact Submodule.subset_span ⟨j, rfl⟩)
    exact h2 h1
  have horth : ∀ {w : S.V}, w ∈ S.W0 → ∀ i, hf L S.Hm w (u i) = 0 := fun hw i => hw _ (huME i)
  have horth' : ∀ {w : S.V}, w ∈ S.W0 → ∀ i, hf L S.Hm (u i) w = 0 := fun hw i => by
    rw [GlobalTheory.FrameBasic.hf_conj L S.herm.1, horth hw i, map_zero]

  let x : Fin (2 * (r + 1) + (k - 1)) → S.V := Fin.append u c
  let y : Fin (2 * (r + 1) + (k - 1)) → S.V := Fin.append u b
  have gx : ∀ i j, hf L S.Hm (x i) (x j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [x, huo, Fin.ext_iff]
    · simp [x, horth' (hcW' j), Fin.ext_iff]; omega
    · simp [x, horth (hcW' i), Fin.ext_iff]; omega
    · simp [x, hco, Fin.ext_iff]
  have gy : ∀ i j, hf L S.Hm (y i) (y j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [y, huo, Fin.ext_iff]
    · simp [y, horth' (hbW' j), Fin.ext_iff]; omega
    · simp [y, horth (hbW' i), Fin.ext_iff]; omega
    · simp [y, hbo, Fin.ext_iff]
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.HermTuple.witt_tuples L S.Hm S.herm _ x y
    (fun i j => by rw [gx, gy]) (by
      have : (Matrix.of fun i j => hf L S.Hm (x i) (x j)) = 1 := by
        ext i j; simp [gx, Matrix.one_apply]
      rw [this]; simp)
  have hgu : ∀ i, g (u i) = u i := fun i => by
    have := hgx (Fin.castAdd _ i)
    simpa [x, y] using this
  have hgc : ∀ i, g (c i) = b i := fun i => by
    have := hgx (Fin.natAdd _ i)
    simpa [x, y] using this
  have hfix : ∀ v ∈ S.ME, g v = v := by
    intro v hv
    rw [← hE] at hv
    let K : Submodule E S.V := LinearMap.eqLocus (g : S.V →ₗ[E] S.V) LinearMap.id
    have h1 : Submodule.span L.O (Set.range u) ≤ K.restrictScalars L.O :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hgu i)
    have h2 : Submodule.span E (Set.range u₀) ≤ K :=
      Submodule.span_le.2 (by
        rintro _ ⟨j, rfl⟩
        apply h1
        rw [hus]
        exact Submodule.subset_span ⟨j, rfl⟩)
    exact h2 hv
  have hH0 : g ∈ S.H0 :=
    ⟨hg, GlobalTheory.HL.FrameStab.mem_unipOn' bot_le g fun v hv => by rw [hfix v hv, sub_self]; exact Submodule.zero_mem _⟩
  have hsm : ∀ s : Set S.V, g • Submodule.span L.O s = Submodule.span L.O (g '' s) := fun s => by
    rw [Submodule.pointwise_smul_def, Submodule.map_span]; rfl
  have e1 : g • S.M d Λ = S.M d Λ := by
    rw [hu₀, ← hus, hsm, ← Set.range_comp]
    congr 2
    funext i
    exact hgu i
  have e2 : g • Submodule.span L.O (Set.range c) = Submodule.span L.O (Set.range b) := by
    rw [hsm, ← Set.range_comp]
    congr 2
    funext i
    exact hgc i
  refine ⟨g, hH0, ?_⟩
  have e3 : ∀ A B : Submodule L.O S.V, g • (A ⊔ B) = g • A ⊔ g • B := fun A B => by
    simp only [Submodule.pointwise_smul_def, Submodule.map_sup]
  rw [hΛ₁, ← hM, ← hcs, e3, e1, e2, hbs, ← hΛ]

theorem good_place {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k) (hG : Good S) :
    S.Hp = 1 ∧ S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 ∧ ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 ∧
      S.om d₀ (coordLat S) = 1 ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d₀ = S.complementReferenceCompactSubgroup ∧
      (∀ Λ, S.IsTerm d₀ Λ → ∃ h ∈ S.St, Λ = h • coordLat S) ∧
      (∀ Λ, S.IsTerm d₀ Λ → S.Fr d₀ Λ = S.frameCls S.f S.f' → Λ = coordLat S) ∧
      ∀ d Λ, S.IsTerm d Λ → ∃ h ∈ S.H0, d = h • d₀ := by
  obtain ⟨hvG, hvD⟩ := GlobalTheory.T.goodPlace_gramInvariant_minors_valuation_zero L r k S hG
  have hvth : S.vth = 0 := by simp [Frames.vth, hG.gg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hvG]
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.framesCoordinateLattice_isTerm_trivialWitnesses L r k S hG
  have hT₀ : S.IsTerm d₀ (coordLat S) := ⟨(1, 1), hd₀⟩
  obtain ⟨hom, hM₀, hFr₀, -, -⟩ := GlobalTheory.HL.WitIndep.witness_independence L r k S d₀ _ _ _ hd₀
  have hFr₁ : S.Fr d₀ (coordLat S) = S.frameCls S.f S.f' := hFr₀
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  obtain ⟨-, -, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hG.gg hG.D_unit
  have hint : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ h =>
    (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1
  have hdd : ∀ d d' Λ, S.IsTerm d Λ → S.IsTerm d' Λ → d' = d := fun d d' Λ h h' =>
    (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.2 d' h'
  have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S
  have hcom := GlobalTheory.HL.ComplAct.main L r k S
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  refine ⟨(GlobalTheory.HL.GoodPlace.equality L r k S hk hG.gg hvG hvD).2.1, GlobalTheory.T.stabilizer_framesCoordinateLattice_goodPlace L r k S hG ha d₀ hd₀, d₀, hd₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hom]
    have h1 : ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V),
        (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → S.psiOf g gs 1 = 1 := by
      intro g gs hd
      have : ∀ j, S.coef g gs 1 j = 0 := fun j => by
        have := hd j.succ j
        rw [if_neg (by simp [Fin.ext_iff])] at this
        exact this
      simp [Frames.psiOf, this]
    have e1 : S.psi 1 = 1 := h1 _ _ S.dual
    have e2 : S.psi' 1 = 1 := h1 _ _ S.dual'
    simp [e1, e2]
  · ext h
    simp only [Subgroup.mem_inf, Frames.complementReferenceCompactSubgroup, MulAction.mem_stabilizer_iff]
    refine and_congr_right fun hh => ⟨fun e => ?_, fun e => ?_⟩
    · have h1 := hcom d₀ _ hT₀ h hh
      rw [e] at h1
      have := (huniq d₀ _ hT₀).2 _ h1.1 h1.2.2.2.2.2
      exact this
    · have h1 := hcom d₀ _ hT₀ h hh
      have e' : h • coordLat S = coordLat S := e
      rw [e'] at h1
      exact hdd _ _ _ hT₀ h1.1
  · intro Λ hΛ
    obtain ⟨h, hh, e⟩ := hall _ (hint _ _ hΛ)
    refine ⟨h, hh, ?_⟩
    have h2 := hact d₀ _ hT₀ h hh
    exact (huniq d₀ _ h2.1).2 _ hΛ (by rw [h2.2.2.2.2.1, hFr₁, e])
  · intro Λ hΛ e
    exact (huniq d₀ _ hT₀).2 _ hΛ (by rw [e, hFr₁])
  · intro d Λ hΛ
    obtain ⟨s, hs, e⟩ := hall _ (hint _ _ hΛ)
    have hsi := S.St.inv_mem hs
    have h2 := hact d _ hΛ _ hsi
    have hT₂ := h2.1
    have hFr₂ : S.Fr d (s⁻¹ • Λ) = S.Fr d₀ (coordLat S) := by
      rw [h2.2.2.2.2.1, e, hFr₁, smul_smul, inv_mul_cancel, one_smul]
    have hM₂ : S.M d (s⁻¹ • Λ) = S.M d₀ (coordLat S) := by
      have h3 : (S.fr d (s⁻¹ • Λ), S.fr' d (s⁻¹ • Λ)) ∈ S.Fr d₀ (coordLat S) := by
        rw [← hFr₂]; exact (hcls _ _).1
      exact ((hcls _ _).2.1 _ h3).2
    obtain ⟨h, hh, e₁⟩ := term_orbit L r k S ha hT₂ hT₀ hM₂
    refine ⟨h, hh, ?_⟩
    have h4 := (hcom d₀ _ hT₀ h hh).1
    rw [e₁] at h4
    exact hdd _ _ _ h4 hT₂

theorem coordinate_lattice_standard : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → {p | ¬ ((G.S p).gg = false ∧ (G.S p).Hp = 1 ∧ (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = (G.S p).K0 ∧ ∃ d₀, (G.S p).IsTermW d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) 1 1 ∧ (G.S p).om d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = 1 ∧ (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV d₀ = (G.S p).complementReferenceCompactSubgroup ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → ∃ h ∈ (G.S p).St, Λ = h • (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → (G.S p).Fr d₀ Λ = (G.S p).frameCls (G.S p).f (G.S p).f' → Λ = (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ ∀ d Λ, (G.S p).IsTerm d Λ → ∃ h ∈ (G.S p).H0, d = h • d₀)}.Finite := by
  intro F E _ _ _ _ _ sig A r k G hk
  refine (GlobalTheory.T.globalHermitianFrames_good_almost_all_places A r k G).subset fun p hp hg => hp ?_
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  exact ⟨hg.gg, good_place (A.L p) r k (G.S p) hk hg⟩

end GlobalTheory.HL.StdPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle
section
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Matrix

namespace GlobalTheory.SA.TransvG

section Det

variable {K : Type} [CommRing K]

theorem det_fromBlocks_swap {n : Type} [Fintype n] [DecidableEq n] (P A B D : Matrix n n K) :
    (fromBlocks P A B D).det = (fromBlocks (-A) P (-D) B).det := by
  have h : fromBlocks (-A) P (-D) B = fromBlocks P A B D * (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 *
      fromBlocks 1 1 0 1 : Matrix (n ⊕ n) (n ⊕ n) K) := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [det_mul]

theorem det_updateRow_last {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det = (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h : (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp
  simp [Fin.castSucc_ne_last, h, ← two_mul]

theorem det_fromBlocks_single {n : Type} [Fintype n] [DecidableEq n] (l : n) (X Y : Matrix n n K) (t s : K) :
    (fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y).det =
      X.det * Y.det - t * s * ((X.updateRow l (Pi.single l 1)).det * (Y.updateRow l (Pi.single l 1)).det) := by
  have e1 : fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y =
      (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y (Sum.inl l) +
          t • Pi.single (Sum.inr l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e2 : (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (Pi.single (Sum.inr l) 1) =
      (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y (Sum.inr l) +
          s • Pi.single (Sum.inl l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e3 : (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1) =
      (fromBlocks (X.updateRow l (Pi.single l 1)) 0 0 (Y.updateRow l (Pi.single l 1))).submatrix
        (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb, @eq_comm _ l b]
  have e4 : (X.updateRow l 0).det = 0 := det_eq_zero_of_row_eq_zero l fun j => by simp
  rw [e1, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₁₂, e2,
    det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₂₁, e3, det_permute,
    det_fromBlocks_zero₂₁, Equiv.Perm.sign_swap (by simp), e4]
  simp
  ring

theorem det_fromBlocks_last {r : ℕ} (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) A B
      (diagonal fun a => if a = Fin.last r then -T' else 0)).det =
      (-1) ^ (r + 1) * (A.det * B.det - T * T' *
        ((A.submatrix Fin.castSucc Fin.castSucc).det * (B.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have h : (-diagonal fun a => if a = Fin.last r then -T' else 0) =
      diagonal fun a => if a = Fin.last r then T' else 0 := by
    ext a b
    simp only [Matrix.neg_apply, diagonal_apply]
    split_ifs <;> simp
  have h2 : (-A).submatrix Fin.castSucc Fin.castSucc = -A.submatrix Fin.castSucc Fin.castSucc := rfl
  rw [det_fromBlocks_swap, h, det_fromBlocks_single, det_updateRow_last, det_updateRow_last, h2, det_neg, det_neg]
  simp only [Fintype.card_fin]
  ring

end Det

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem B_e_e (F : FlagD H r) (a b : Fin (r + 1)) :
    H.B (F.e a) (F.e b) = diagonal (fun a => if a = Fin.last r then -F.T else 0) a b := by
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · simp [F.zz]
  · rename_i b
    simp [B_eq_zero_comm.1 (F.zperp b), diagonal_apply, (Fin.castSucc_ne_last b).symm]
  · rename_i a
    simp [F.zperp a, diagonal_apply, Fin.castSucc_ne_last]
  · rename_i a b
    simp [F.iso a b, diagonal_apply, Fin.castSucc_ne_last]

theorem gram_eq_fromBlocks (F F' : FlagD H r) :
    Gram F F' = fromBlocks (diagonal fun a => if a = Fin.last r then -F.T else 0) (Zhat F F') (Zhat F F')ᴴ
      (diagonal fun a => if a = Fin.last r then -F'.T else 0) := by
  ext (a | a) (b | b)
  · exact B_e_e F a b
  · rfl
  · exact (H.herm _ _).symm
  · exact B_e_e F' a b

theorem det_gram (F F' : FlagD H r) : (Gram F F').det = (-1) ^ (r + 1) * Gval F F' := by
  rw [gram_eq_fromBlocks, det_fromBlocks_last, ← conjTranspose_submatrix, det_conjTranspose, det_conjTranspose]
  rfl

theorem gram_det_statement : LemmaG := fun _ _ _ _ _ _ _ _ F F' => det_gram F F'

theorem isTransv_iff_gval : ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), IsTransv F F' ↔ Gval F F' ≠ 0 := by
  intro K V _ _ _ _ _ H r F F'
  rw [isTransv_iff_gram, det_gram]
  simp

end GlobalTheory.SA.TransvG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ M', IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsUnimodular h M → IsMaxLat h M ∧ badP h M = ∅ ∧ lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), IsOrthoLattice h M n → Submodule.IsLattice K M ∧ IsUnimodular h M ∧ Module.finrank K V = n) := by
  first | exact @GlobalTheory.Mass.MaxExists.main | exact GlobalTheory.Mass.MaxExists.main | (intros; apply GlobalTheory.Mass.MaxExists.main <;> assumption)
end

