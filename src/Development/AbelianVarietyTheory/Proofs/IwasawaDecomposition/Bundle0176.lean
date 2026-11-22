import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0064
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.Cong

open GlobalTheory.LastSteps

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h : IsUnit (redP P (1 : E)) := by
    rw [GlobalTheory.TopStep.reduction_one₂]
    exact isUnit_one
  have h1 : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, GlobalTheory.TopStep.reduction_one₂, Units.val_one])
  unfold LocE.unitV
  rw [dif_pos h, h1, map_one, Units.val_one]

omit [StarRing E] in
theorem unitV_det_delta (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} {A : Fin t → Fin t → E}
    (hA : ∀ s s', A s s' = if s = s' then 1 else 0) : LocE.unitV χ (Matrix.det (Matrix.of fun s s' => A s s')) = 1 := by
  have : (Matrix.of fun s s' => A s s') = 1 := by
    ext s s'
    rw [Matrix.of_apply, hA, Matrix.one_apply]
  rw [this, Matrix.det_one, unitV_one]

omit [NumberField E] [StarRing E] in

theorem entB_id (q : ℕ) {k₀ c n : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) :
    LocE.entB q k₀ c n c n ex ex (LinearMap.id : HomE E (n + c) (n + c)) p p' = if p = p' then 1 else 0 := by
  have h1 : LocE.fIdx k₀ c n p < n + c := by
    unfold LocE.fIdx
    split_ifs <;> omega
  have h2 : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p' ↔ p = p' := by
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    unfold LocE.fIdx at h
    split_ifs at h <;> omega
  unfold LocE.entB Loc.atN
  rw [dif_pos h1, LinearMap.id_apply]
  unfold Loc.eN
  by_cases h : p = p'
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (h2.1 h')), zero_mul]

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

omit [StarRing E] in
theorem blocks_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i)
      (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => unitV_det_delta _ fun s s' => ?_
  have h1 : ∀ s : Fin t, r + i * t + s.1 < r + j * t := fun s => by
    have := Finset.mem_range.1 hi
    have := s.2
    nlinarith
  rw [hM _ _ (h1 s) (h1 s')]
  simp [Fin.ext_iff]

omit [StarRing E] in
theorem int_delta {N : ℕ} {M : ℕ → ℕ → E} (hM : ∀ p p', p < N → p' < N → M p p' = if p = p' then 1 else 0)
    (p p' : ℕ) (h : p < N) (h' : p' < N) : IntAt P (M p p') := by
  rw [hM _ _ h h']
  split_ifs
  · exact GlobalTheory.TopStep.intAt_one
  · exact GlobalTheory.TopStep.intAt_zero

omit [StarRing E] in
theorem lamGv_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, GlobalTheory.TopStep.reduction_zero, AddChar.map_zero_eq_one]
  intro i hi
  have := Finset.mem_range.1 hi
  rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

omit [StarRing E] in
theorem lamGvS_delta {k₀ r t j : ℕ} (hk : k₀ ≤ r) {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, GlobalTheory.TopStep.reduction_zero,
    AddChar.map_zero_eq_one]
  all_goals
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

theorem lamQB_cong (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {y : HomE E (n + c) (n + c)}
    (hy : y ∈ homS (LocE.lamY P (qOf P) n c 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.lamQB ξ kj n (LinearMap.id + (qOf P : E) • y) = 1 := by
  unfold LocE.lamQB
  have hl : ∀ s : Fin (n - kj), kj + s.1 < n + c := fun s => by
    have := s.2
    omega
  have e : (fun s t : Fin (n - kj) => Loc.atN ((LinearMap.id + (qOf P : E) • y : HomE E (n + c) (n + c))
      (Loc.eN E (n + c) (kj + t.1))) (kj + s.1)) =
      fun s t : Fin (n - kj) => (if s = t then 1 else 0) + (qOf P : E) * y (Pi.single ⟨_, hl t⟩ 1) ⟨_, hl s⟩ := by
    funext s t
    unfold Loc.atN
    rw [dif_pos (hl s), eN_eq (hl t)]
    simp [Pi.single_apply, Fin.ext_iff]
  rw [e, unitV_congr ξ (redP_det_add_q (A := fun s t => if s = t then 1 else 0) (fun s t => ?_) fun s t => ?_),
    unitV_det_delta ξ fun _ _ => rfl, inv_one]
  · split_ifs
    · exact GlobalTheory.TopStep.intAt_one
    · exact GlobalTheory.TopStep.intAt_zero
  · simpa [LocE.scE] using mem_homS_sclLat.1 hy ⟨_, hl s⟩ ⟨_, hl t⟩

end Loc

theorem lamRow_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hj y hy
  have hN : R.N j + cOf R j = R.r + j * R.t := by
    unfold Ranks.N cOf Ranks.r
    rw [mul_add, mul_one]
    omega
  have hk : R.k ≤ R.N j := Nat.le_add_right _ _
  have hr : R.k ≤ R.r := by
    unfold Ranks.r
    omega
  unfold lamYat at hy
  unfold lamRow
  by_cases hP : P ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    have hZ := entB_int R.k (x := y) hy
    have hM : ∀ p p', p < R.r + j * R.t → p' < R.r + j * R.t →
        LocE.entB (qOf P) R.k (cOf R j) (R.N j) (cOf R j) (R.N j) (fun i => i + 1) (fun i => i + 1)
          (LinearMap.id : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) p p' = if p = p' then 1 else 0 :=
      fun p p' h h' => entB_id _ hk _ (hN ▸ h) (hN ▸ h')
    split_ifs
    · unfold LocE.lamGBS
      rw [entB_add_smul, lamGvS_congr _ _ (int_delta hM) hZ, lamGvS_delta _ _ hr hM]
    · unfold LocE.lamGB
      rw [entB_add_smul, lamGv_congr _ _ (int_delta hM) hZ, lamGv_delta _ _ hM]
  · rw [if_neg hP] at hy ⊢
    exact lamQB_cong _ _ _ _ hy

end GlobalTheory.Mem.Col2.IdxEx.Cong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCompletelyOverIntermediateOfSplitsOverRat
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SplitTower

theorem splits_completely_of_intermediate :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  intro K L _ _ _ _ _ p hp hcount 𝔭 hp𝔭
  rw [GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭]
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  have hPmax : P.IsMaximal := by
    exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI := hPmax
  haveI : Fintype (P.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite P (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 L)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have h1 : (P.primesOver (𝓞 L)).ncard = ∑ _q : P.primesOver (𝓞 L), 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have hall : ∀ Q ∈ P.primesOver (𝓞 L), Q.ramificationIdx ℤ * Q.inertiaDeg ℤ = 1 := by
    rw [← hsum, h1, Finset.sum_eq_sum_iff_of_le] at hcount
    · intro Q hQ
      exact (hcount ⟨Q, hQ⟩ (Finset.mem_univ _)).symm
    · rintro ⟨Q, hQ, _⟩ -
      exact Nat.mul_pos (Ideal.ramificationIdx_pos Q _) (Ideal.inertiaDeg_pos Q _)
  intro Q hQ
  obtain ⟨hQp, hQ𝔭⟩ := hQ
  haveI := 𝔭.isPrime
  haveI h𝔭P : 𝔭.asIdeal.LiesOver P := by
    refine ⟨hPmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_⟩
    rw [hPdef, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hp𝔭
  haveI : Q.LiesOver P := Ideal.LiesOver.trans Q 𝔭.asIdeal P
  have h := hall Q ⟨hQp, inferInstance⟩
  rw [Ideal.ramificationIdx_tower 𝔭.asIdeal Q, Ideal.inertiaDeg_tower 𝔭.asIdeal Q] at h
  refine Nat.eq_one_of_dvd_one ?_
  rw [← h]
  exact ⟨𝔭.asIdeal.ramificationIdx ℤ * 𝔭.asIdeal.inertiaDeg ℤ, by ring⟩

end GlobalTheory.SplitTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjectiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_kummer_inertia_surjective : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y := by
  first | exact @GlobalTheory.TameKummerInertia.tame_kummer_surj | exact GlobalTheory.TameKummerInertia.tame_kummer_surj | (intros; apply GlobalTheory.TameKummerInertia.tame_kummer_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingCharArgMulLeftUnipotent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent

theorem chArg_left : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  intro F _ n' c' n c hc hc' r hr xj t
  obtain ⟨-, -, h3⟩ := (GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
  generalize Loc.xx1 xj t = x at h3
  have e : Loc.n1Arg r = ∑ i ∈ Finset.range c, Loc.atN (r (Loc.eN F (n + c) (n + (i + 1)))) (n + i) := by
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    rw [Finset.sum_range_succ, GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_zero (F := F) (N := n + (d + 1)) (i := n + (d + 1)) (by omega),
      map_zero]
    have z : Loc.atN (0 : Fin (n + (d + 1)) → F) (n + d) = 0 := by
      unfold Loc.atN
      split_ifs <;> rfl
    rw [z, add_zero]
    rfl
  rw [e]
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have b3 := atN_of_R1cond hr.1 (h3 (i + 1))
  have b4 : Loc.atN (Loc.eN F (n + c) (n + (i + 1))) (n + i) = 0 := GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.atN_eN_succ _ _
  simp only [map_sub, atN_sub, b4] at b3
  change Loc.atN (r (x (Loc.eN F (n' + c') (n' + (i + 1))))) (n + i) =
    Loc.atN (x (Loc.eN F (n' + c') (n' + (i + 1)))) (n + i) + _
  linear_combination b3

end GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInTrans
section
open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.Mem.UnramTower

theorem unramIn_trans : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N], (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn L 𝔭) → (∀ P : HeightOneSpectrum (𝓞 L), GlobalTheory.NT.UnramIn N P) → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn N 𝔭 := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ hL hN 𝔭 σ hσ
  obtain ⟨Q, hQ, hQo, hσ⟩ := hσ
  have hσ' : ∀ x : 𝓞 N, σ • x - x ∈ Q := fun x => hσ x
  have hPo : (Q.under (𝓞 L)).LiesOver 𝔭.asIdeal := inferInstance
  have hP : (Q.under (𝓞 L)).IsPrime := inferInstance
  have h1 : σ.restrictNormal L = 1 := by
    refine hL 𝔭 _ ⟨Q.under (𝓞 L), hP, hPo, ?_⟩
    intro x
    have hx := hσ' (algebraMap (𝓞 L) (𝓞 N) x)
    have e : algebraMap (𝓞 L) (𝓞 N) ((σ.restrictNormal L) • x) = σ • algebraMap (𝓞 L) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact AlgEquiv.restrictNormal_commutes σ L (x : L)
    show (σ.restrictNormal L) • x - x ∈ Ideal.comap (algebraMap (𝓞 L) (𝓞 N)) Q
    rw [Ideal.mem_comap, map_sub, e]
    exact hx
  have hfix : ∀ y : L, σ (algebraMap L N y) = algebraMap L N y := by
    intro y
    rw [← AlgEquiv.restrictNormal_commutes σ L y, h1]
    rfl
  let τ : N ≃ₐ[L] N := { σ.toRingEquiv with commutes' := hfix }
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨Q.under (𝓞 L), hP, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have h2 : τ = 1 := by
    refine hN P τ ⟨Q, hQ, ⟨rfl⟩, ?_⟩
    intro x
    exact hσ' x
  ext y
  exact DFunLike.congr_fun h2 y

end GlobalTheory.Mem.UnramTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Mem.LatGood

theorem map_mulVec_injective {K m k : Type} [Field K] [Fintype m] [Fintype k] (φ : K →+* ℂ) (B : Matrix m k K)
    (h : Function.Injective B.mulVec) : Function.Injective (B.map φ).mulVec := by
  classical
  have hk : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) hk
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' B) = 1 := by
    rw [hg]; exact LinearMap.toMatrix'_id
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1
  have h2 : (LinearMap.toMatrix' g).map φ * B.map φ = 1 := by
    rw [← Matrix.map_mul, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  intro x y hxy
  have := congrArg ((LinearMap.toMatrix' g).map φ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, h2] using this

section Datum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

def valMat (c : C.Cl) : Matrix C.ιV (Fin C.dim) K :=
  Matrix.of fun i a => C.bV.repr ((C.basis a : C.Cl → C.V) c) i

theorem pair_eq (x y : C.V) :
    C.pair x y = ∑ i, ∑ j, star (C.bV.repr x i) * C.gramV i j * C.bV.repr y j := by
  conv_lhs => rw [← C.bV.sum_repr x, ← C.bV.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, CSD.gramV, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_map (hb : C.HasRatBasis) (φ : K →+* ℂ) :
    C.H.map φ = ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ • (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ) := by
  ext a b
  simp only [Matrix.map_apply, CSD.H, Matrix.of_apply, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pair_eq, Matrix.mul_apply, Matrix.conjTranspose_apply, valMat]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C.basis_rat hb a c i φ]
  rfl

theorem exists_val_ne (φ : K →+* ℂ) (x : Fin C.dim → ℂ) (hx : x ≠ 0) :
    ∃ c, ((valMat C c).map φ) *ᵥ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let B : Matrix (C.Cl × C.ιV) (Fin C.dim) K := Matrix.of fun p a => valMat C p.1 p.2 a
  have hB : Function.Injective B.mulVec := by
    intro u v huv
    apply C.I_injective
    funext c
    apply C.bV.repr.injective
    ext i
    have h1 := congrFun huv (c, i)
    simp only [Matrix.mulVec, dotProduct, B, valMat, Matrix.of_apply] at h1
    simp only [CSD.I_eq_sum, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finsupp.smul_apply, smul_eq_mul]
    simpa only [mul_comm] using h1
  apply hx
  apply map_mulVec_injective φ B hB
  rw [Matrix.mulVec_zero]
  funext p
  exact congrFun (hcon p.1) p.2

theorem gram_posDef (hb : C.HasRatBasis) (φ : K →+* ℂ) (hp : (C.gramV.map φ).PosDef) : (C.H.map φ).PosDef := by
  have hw : ∀ c, (0 : ℂ) < ((C.wt c : ℕ) : ℂ)⁻¹ := fun c => inv_pos.mpr (by exact_mod_cast C.wt_pos c)
  rw [gram_map C hb φ]
  have hpsd : (∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ •
      (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ)).PosSemidef :=
    Matrix.posSemidef_sum _ fun c _ => (hp.posSemidef.conjTranspose_mul_mul_same _).smul (hw c).le
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_
  have e : ∀ c, star x ⬝ᵥ (((C.wt c : ℕ) : ℂ)⁻¹ •
      (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ)) *ᵥ x =
      ((C.wt c : ℕ) : ℂ)⁻¹ * (star (((valMat C c).map φ) *ᵥ x) ⬝ᵥ (C.gramV.map φ) *ᵥ (((valMat C c).map φ) *ᵥ x)) := by
    intro c
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp only [e]
  obtain ⟨c, hc⟩ := exists_val_ne C φ x hx
  exact Finset.sum_pos' (fun c _ => mul_nonneg (hw c).le (hp.posSemidef.dotProduct_mulVec_nonneg _))
    ⟨c, Finset.mem_univ c, mul_pos (hw c) (hp.dotProduct_mulVec_pos hc)⟩

omit [StarRing K] in

theorem exists_smul_mem {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem ..)

theorem values_isLattice (M : C.Cl → Submodule (𝓞 K) C.V) (hM : ∀ c, Submodule.IsLattice K (M c))
    (L : Submodule (𝓞 K) C.Forms) (hL : ∀ x, x ∈ L ↔ ∀ c, x.1 c ∈ M c) :
    L.FG ∧ Submodule.span K (L : Set C.Forms) = ⊤ := by
  classical
  constructor
  · apply Submodule.fg_of_fg_map_injective (C.Forms.subtype.restrictScalars (𝓞 K)) Subtype.val_injective
    refine Submodule.FG.of_le (Submodule.fg_pi fun c => (hM c).fg) ?_
    rintro _ ⟨x, hx, rfl⟩ c _
    exact (hL x).1 hx c
  · rw [eq_top_iff]
    intro x _
    have h : ∀ c, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x.1 c ∈ M c := fun c =>
      exists_smul_mem (by rw [(hM c).span_eq_top]; trivial)
    choose d hd hdM using h
    have hx : (∏ c, d c) • x ∈ L := by
      rw [hL]
      intro c
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      show ((∏ c' ∈ Finset.univ.erase c, d c') * d c) • x.1 c ∈ M c
      rw [mul_smul]
      exact (M c).smul_mem _ (hdM c)
    have hd0 : (∏ c, d c) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd c
    have hd' : algebraMap (𝓞 K) K (∏ c, d c) ≠ 0 := by simpa only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff] using hd0
    have : x = (algebraMap (𝓞 K) K (∏ c, d c))⁻¹ • ((∏ c, d c) • x) := by
      rw [← algebraMap_smul K (∏ c, d c) x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

end Datum

theorem root_mem_cmMax {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) {u : K} {m : ℕ} (hm : m ≠ 0) (hu : u ^ m = 1) : u ∈ cmMax K := by
  have key : ∀ φ : K →+* ℂ, φ u⁻¹ = starRingEnd ℂ (φ u) := by
    intro φ
    have h1 : (φ u) ^ m = 1 := by rw [← map_pow, hu, map_one]
    rw [map_inv₀]
    exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hm)
  have hs : star u = u⁻¹ := σ.injective (by rw [hσ, key])
  intro φ
  rw [hs, key]

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem rho_rat (hF : FOk emb σ) (hS : S.Ok) (b : S.β) (g : S.G b) (i j : VVIdx lam) :
    (bVV K lam).repr (S.rho emb lam b g (bVV K lam j)) i ∈ cmMax K := by
  have he : ∀ τ x, emb τ x ∈ cmMax K := fun τ x φ => by
    rw [← hF.emb_star]
    exact hF.conjE (φ.comp (emb τ)) x
  have h1 := (GlobalTheory.coefAction_repr_mem_subfield emb (cmMax K) lam he (S.gam b g) i j).2
  obtain ⟨m, hm, hu⟩ := hS.root b g
  have h2 : ((S.chr b g : Kˣ) : K) ∈ cmMax K :=
    root_mem_cmMax σ hF.sig_star hm.ne' (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one])
  have e : S.rho emb lam b g (bVV K lam j) = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) (bVV K lam j) := rfl
  rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem h2 h1

theorem hasRatBasis (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) : (S.csd emb lam h).HasRatBasis :=
  GlobalTheory.FormsDescent.hasRatBasis_of_act _ fun c γ i j => rho_rat S emb σ lam hF hS c.1 γ.1 i j

theorem gramV_posDef (h : (S.fam emb lam).Ok) (φ : K →+* ℂ) : ((S.csd emb lam h).gramV.map φ).PosDef := by
  have h1 := pairingPositive_holds K ι n lam (gramKd emb (1 : Matrix (Fin n) (Fin n) E)) φ fun τ => by
    have : gramKd emb (1 : Matrix (Fin n) (Fin n) E) τ = 1 := by
      simp [gramKd]
    rw [this, map_one']
    exact Matrix.PosDef.one
  exact h1

theorem step_gram_posDef (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) (φ : K →+* ℂ) :
    ((S.csd emb lam h).H.map φ).PosDef :=
  gram_posDef _ (hasRatBasis S emb σ lam hF hS h) φ (gramV_posDef S emb lam h φ)

omit [StarRing E] [StarRing K] in
theorem delAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (delAtr emb lam L) :=
  (GlobalTheory.TransLattice.nabDelLattice K ι n lam _ fun τ =>
    GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL)).2

end Step

theorem lawGood : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF hS h
  exact ⟨fun v => (frameOfSpec _ _ (step_gram_posDef S emb σ lam hF hS h v.embedding)).1,
    values_isLattice (S.csd emb lam h) (fun c => delAtr emb lam (S.Lsh c.1 (S.rep c)))
      (fun c => delAtr_isLattice emb lam _ (hS.lsh_lat c.1 _)) _ fun _ => Iff.rfl⟩

end GlobalTheory.Mem.LatGood
end
end

