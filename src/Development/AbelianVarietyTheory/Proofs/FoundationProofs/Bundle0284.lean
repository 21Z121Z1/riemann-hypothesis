import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0281
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTransvectionVectorsNeighbour
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPairSpherical
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Inhab

theorem om_vac {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ}
    {e0 : VC D a d → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (W : WeilO D cc δ a d e0)
    (h1 : ∀ u, IntU D u → W.chV.f u = 1) (h2 : ∀ u, IntU D u → W.chV'.f u = 1)
    (k : GA D a) (hk : k ∈ intG D a) (k' : GA D d) (hk' : k' ∈ intG D d) : W.Om k k' e0 = e0 := by
  obtain ⟨x, x', hx, hx', h⟩ := (VacInt.vacuum_eigen D (GlobalTheory.InducedType.induced_type D).1 cc δ hc a d e0 he W).2.1 k hk k' hk'
  rw [h, h1 x' hx', h2 x hx]
  simp

end GlobalTheory.NormSum.Inhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCoeffConj
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_coeff_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω),
    ∃ σ : GlobalTheory.FN.ring ε.range ≃+* GlobalTheory.FN.ring ε.range, ∀ (a : GlobalTheory.FN.ring ε.range) (h h' : HahnSeries ℚ Ω),
      IsExp ε a h → IsExp ε (σ a : GlobalTheory.FN.ring ε.range) h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s
  obtain ⟨e, he_inj, he⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1
  have key : ∀ t : Ω ≃+* Ω, ∃ c : ring ε.range → ring ε.range, ∀ a,
      (∀ r, (e (c a)).coeff r = t ((e a).coeff r)) ∧
      ∀ h h' : HahnSeries ℚ Ω, IsExp ε a h → IsExp ε (c a : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
    intro t
    have hex : ∀ a : ring ε.range, ∃ b : ring ε.range, ∀ h h' : HahnSeries ℚ Ω,
        IsExp ε a h → IsExp ε (b : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
      intro a
      obtain ⟨f', hf', hp⟩ := GlobalTheory.T.exists_galoisConjugate_modularFunction_someLevel Ω ε t a ((hmem a).1 a.2)
      exact ⟨⟨f', (hmem f').2 hf'⟩, hp⟩
    choose c hc using hex
    exact ⟨c, fun a => ⟨hc a (e a) (e (c a)) (he a) (he (c a)), hc a⟩⟩
  have mapc : ∀ t : Ω ≃+* Ω, ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω, ∀ h r, (Φ h).coeff r = t (h.coeff r) := by
    intro t
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω t.toRingHom 1 (fun _ => 1) one_pos rfl (by simp)
    exact ⟨Φ, fun h r => by simpa using hΦ h r⟩
  obtain ⟨c, hc⟩ := key s
  obtain ⟨d, hd⟩ := key s.symm
  obtain ⟨Φ, hΦ⟩ := mapc s
  have ec : ∀ a, e (c a) = Φ (e a) := fun a => by
    ext r
    rw [(hc a).1, hΦ]
  refine ⟨{ toFun := c, invFun := d, left_inv := ?_, right_inv := ?_, map_add' := ?_, map_mul' := ?_ },
    fun a h h' => (hc a).2 h h'⟩
  · intro a
    apply he_inj
    ext r
    rw [(hd _).1, (hc a).1]
    simp
  · intro a
    apply he_inj
    ext r
    rw [(hc _).1, (hd a).1]
    simp
  · intro a b
    apply he_inj
    simp only [map_mul, ec]
  · intro a b
    apply he_inj
    simp only [map_add, ec]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitCharacterUnitaryGroupStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_character_unitary_group : ∀ (D : D7) (N₀ : ℕ) (χ : HeckeU D N₀) (N : ℕ), ∃ c : GA D N →* ℂˣ, (∀ k : GA D N, SuppInert D (k : GL (Fin N) (AE D)) → c k = 1) ∧ ∀ (g : GA D N) (x : (AE D)ˣ), (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) → x = Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) * sgU D x → c g = χ.f x := by
  first | exact @GlobalTheory.SplitCharacter.exists_split_character | exact GlobalTheory.SplitCharacter.exists_split_character | (intros; apply GlobalTheory.SplitCharacter.exists_split_character <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsThetaLatticeCorrespondenceWeilOperator
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.WeilCorr

open GlobalTheory.NormSum.MovedTheta

theorem exists_close_two {R E : Type} [CommRing R] (ι : E → R) (O : Subring R) (I : AddSubgroup R)
    (hA : ∀ (y : R) (m : ℕ), 0 < m → ∃ e : E, ∃ t ∈ I, ι e - y = (m : R) * t)
    (hO : ∀ y : R, ∃ n : ℕ, 0 < n ∧ (n : R) * y ∈ O) (hI : ∀ s ∈ O, ∀ t ∈ I, s * t ∈ I)
    {a b : ℕ} (X : Matrix (Fin a) (Fin b) R) (P P' : Matrix (Fin a) (Fin a) R) (Q Q' : Matrix (Fin b) (Fin b) R)
    (m : ℕ) (hm : 0 < m) :
    ∃ z : Matrix (Fin a) (Fin b) E, (∀ i j, ∃ y ∈ I, (z.map ι - X) i j = (m : R) * y) ∧
      (∀ i j, (P * z.map ι * Q - P * X * Q) i j ∈ I) ∧ ∀ i j, (P' * z.map ι * Q' - P' * X * Q') i j ∈ I := by
  obtain ⟨n₁, hn₁, hP⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO P
  obtain ⟨n₂, hn₂, hQ⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO Q
  obtain ⟨n₃, hn₃, hP'⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO P'
  obtain ⟨n₄, hn₄, hQ'⟩ := GlobalTheory.WeilEquiv.exists_common_den O hO Q'
  choose e t ht he using fun i j => hA (X i j) (m * n₁ * n₂ * n₃ * n₄) (by positivity)
  have key : ∀ (P : Matrix (Fin a) (Fin a) R) (Q : Matrix (Fin b) (Fin b) R) (n n' c : ℕ),
      (∀ i j, (n : R) * P i j ∈ O) → (∀ i j, (n' : R) * Q i j ∈ O) → m * n₁ * n₂ * n₃ * n₄ = c * n * n' →
      ∀ i j, (P * (Matrix.of e).map ι * Q - P * X * Q) i j ∈ I := by
    intro P Q n n' c hP hQ hc i j
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul, he, hc]
    refine sum_mem fun l _ => sum_mem fun r _ => ?_
    have : P i r * (((c * n * n' : ℕ) : R) * t r l) * Q l j =
        ((c : R) * ((n : R) * P i r) * ((n' : R) * Q l j)) * t r l := by
      push_cast; ring
    rw [this]
    exact hI _ (O.mul_mem (O.mul_mem (natCast_mem O _) (hP i r)) (hQ l j)) _ (ht r l)
  refine ⟨Matrix.of e, fun i j => ⟨((n₁ * n₂ * n₃ * n₄ : ℕ) : R) * t i j, hI _ (natCast_mem O _) _ (ht i j), ?_⟩,
    key P Q n₁ n₂ (m * n₃ * n₄) hP hQ (by ring), key P' Q' n₃ n₄ (m * n₁ * n₂) hP' hQ' (by ring)⟩
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, he]
  push_cast; ring

section Entries

variable {R : Type} [CommRing R] {I : AddSubgroup R} {a b : ℕ} {A B A' B' : Matrix (Fin a) (Fin b) R}

theorem entries_of_sub (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, B i j ∈ I) (i : Fin a) (j : Fin b) : A i j ∈ I := by
  have := add_mem (h i j) (h' i j)
  rwa [Matrix.sub_apply, sub_add_cancel] at this

theorem entries_trans (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, (B - A') i j ∈ I) (i : Fin a) (j : Fin b) :
    (A - A') i j ∈ I := by
  have := add_mem (h i j) (h' i j)
  rwa [Matrix.sub_apply, Matrix.sub_apply, sub_add_sub_cancel] at this

theorem entries_iff (h : ∀ i j, (A - B) i j ∈ I) (h' : ∀ i j, (A' - B') i j ∈ I) :
    (∀ i j, (B - B') i j ∈ I) ↔ ∀ i j, (A - A') i j ∈ I := by
  refine forall₂_congr fun i j => ?_
  have h1 := sub_mem (h i j) (h' i j)
  simp only [Matrix.sub_apply] at h1 ⊢
  constructor
  · intro h2
    convert add_mem h1 h2 using 1
    ring
  · intro h2
    convert sub_mem h2 h1 using 1
    ring

end Entries

variable {D : D7} {N N' : ℕ}

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) :
    Function.Injective (pt D (tor0 D cc δ) δ : Matrix (Fin N') (Fin N) D.host.E → VC D N N') := by
  intro z w h
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
  simp only [pt, embV, tor0, Pi.smul_apply, smul_eq_mul] at h1
  exact (embT D _).injective (mul_left_cancel₀ hδ h1)

theorem pt_sub (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z - w) = pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ w := by
  rw [sub_eq_add_neg, pt_add, pt_neg, ← sub_eq_add_neg]

theorem mv_sub (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z - w) = mv g g' z - mv g g' w := by
  rw [sub_eq_add_neg, mv_add, mv_neg, ← sub_eq_add_neg]

theorem pt_mem_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) {h : GA D N} {h' : GA D N'}
    {L : Lat D N} {L' : Lat D N'} (hL : Moves D (h : GL (Fin N) (AE D)) L) (hL' : Moves D (h' : GL (Fin N') (AE D)) L')
    (u : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ u ∈ La D (tor0 D cc δ) L L' ↔
      ∀ i j, mv (h : GL (Fin N) (AE D)) (h' : GL (Fin N') (AE D)) u i j ∈ IhE D cc := by
  have hD := (GlobalTheory.InducedType.induced_type D).1
  constructor
  · intro hu
    obtain ⟨z, hz, hz'⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' h h' L L' hL hL' _ hu
    rw [pt_injective cc hδ hz]
    exact hz'
  · exact GlobalTheory.NormSum.pt_mem_La_of_adelic D hD cc δ hcc N N' h h' L L' hL hL' u

theorem move_fwd (g h : GL (Fin N) (AE D)) (g' h' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (((g' * h')⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) *
      ((g' : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
        ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) *
      ((g * h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = mv h h' z := by
  simp only [mv, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)),
    ← Matrix.mul_assoc ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)),
    Units.inv_mul, Units.inv_mul, Matrix.one_mul, Matrix.one_mul]

theorem move_bwd (g h : GL (Fin N) (AE D)) (g' h' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    ((h'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * mv g g' z *
      (h : Matrix (Fin N) (Fin N) (AE D)) = mv (g * h) (g' * h') z := by
  simp only [mv, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem approx_fwd {cc : Ideal (𝓞 D.host.K)} (hcc : cc ≠ ⊥) (g h k : GL (Fin N) (AE D)) (g' h' k' : GL (Fin N') (AE D))
    (z : Matrix (Fin N') (Fin N) D.host.E) (m : ℕ) (hm : 0 < m) :
    ∃ z' : Matrix (Fin N') (Fin N) D.host.E, CloseTo D cc m g g' z z' ∧
      (∀ i j, (mv (g * h) (g' * h') z' - mv h h' z) i j ∈ IhE D cc) ∧
      ∀ i j, (mv (g * k) (g' * k') z' - mv k k' z) i j ∈ IhE D cc := by
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  rw [← move_fwd g h g' h' z, ← move_fwd g k g' k' z]
  exact exists_close_two (inc D) (OhE D) (IhE D cc) hA hO hI _ _ _ _ _ m hm

theorem approx_bwd {cc : Ideal (𝓞 D.host.K)} (hcc : cc ≠ ⊥) (g h k : GL (Fin N) (AE D)) (g' h' k' : GL (Fin N') (AE D))
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ z : Matrix (Fin N') (Fin N) D.host.E,
      (∀ i j, (mv h h' z - mv (g * h) (g' * h') y) i j ∈ IhE D cc) ∧
      ∀ i j, (mv k k' z - mv (g * k) (g' * k') y) i j ∈ IhE D cc := by
  obtain ⟨hA, hO, hI⟩ := GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc
  rw [← move_bwd g h g' h' y, ← move_bwd g k g' k' y]
  obtain ⟨z, -, hz⟩ := exists_close_two (inc D) (OhE D) (IhE D cc) hA hO hI (mv g g' y)
    ((h'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    ((k'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    (h : Matrix (Fin N) (Fin N) (AE D)) (k : Matrix (Fin N) (Fin N) (AE D)) 1 one_pos
  exact ⟨z, hz⟩

theorem exists_corr : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ f : La D (tor0 D cc δ) M₁ M₁' → La D (tor0 D cc δ) M₂ M₂', (∀ x : La D (tor0 D cc δ) M₁ M₁', W.Om g g' (Wd D (tor0 D cc δ) (x : VC D N N') F) = Wd D (tor0 D cc δ) (f x : VC D N N') (W.Om g g' F)) ∧ (∀ x y : La D (tor0 D cc δ) M₁ M₁', (x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₁ L₁' ↔ (f x : VC D N N') - (f y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂') ∧ ∀ y : La D (tor0 D cc δ) M₂ M₂', ∃ x : La D (tor0 D cc δ) M₁ M₁', (f x : VC D N N') - (y : VC D N N') ∈ La D (tor0 D cc δ) L₂ L₂' := by
  intro D cc δ hC hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂' a1 a1' a2 a2' b1 b1' b2 b2' F hF
  have hcc : cc ≠ ⊥ := hC.1.1
  have hD := (GlobalTheory.InducedType.induced_type D).1
  have step : ∀ z : Matrix (Fin N') (Fin N) D.host.E, ∃ z' : Matrix (Fin N') (Fin N) D.host.E,
      W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) =
        Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (W.Om g g' F) ∧
      (∀ i j, (mv ((g * h : GA D N) : GL (Fin N) (AE D)) ((g' * h' : GA D N') : GL (Fin N') (AE D)) z' -
        mv (h : GL (Fin N) (AE D)) (h' : GL (Fin N') (AE D)) z) i j ∈ IhE D cc) ∧
      ∀ i j, (mv ((g * k : GA D N) : GL (Fin N) (AE D)) ((g' * k' : GA D N') : GL (Fin N') (AE D)) z' -
        mv (k : GL (Fin N) (AE D)) (k' : GL (Fin N') (AE D)) z) i j ∈ IhE D cc := by
    intro z
    obtain ⟨m, hm, hl⟩ := W.lift g g' z F hF
    obtain ⟨z', hc, h1, h2⟩ := approx_fwd hcc (g : GL (Fin N) (AE D)) h k (g' : GL (Fin N') (AE D)) h' k' z m hm
    exact ⟨z', hl z' hc, h1, h2⟩
  choose s hs1 hs2 hs3 using step
  choose r hr1 hr2 using fun x : La D (tor0 D cc δ) M₁ M₁' =>
    GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' k k' M₁ M₁' b1 b1' x x.2
  have hmem : ∀ x, pt D (tor0 D cc δ) δ (s (r x)) ∈ La D (tor0 D cc δ) M₂ M₂' := by
    intro x
    rw [pt_mem_iff hcc hδ b2 b2']
    exact entries_of_sub (hs3 (r x)) (hr2 x)
  refine ⟨fun x => ⟨_, hmem x⟩, fun x => ?_, fun x y => ?_, fun y => ?_⟩
  · have := hs1 (r x)
    rwa [← hr1 x] at this
  · rw [hr1 x, hr1 y]
    dsimp only
    rw [← pt_sub, ← pt_sub, pt_mem_iff hcc hδ a1 a1', pt_mem_iff hcc hδ a2 a2', mv_sub, mv_sub]
    exact entries_iff (hs2 (r x)) (hs2 (r y))
  · obtain ⟨y₀, hy, hy'⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hD cc δ hcc N N' _ _ M₂ M₂' b2 b2' y y.2
    obtain ⟨z, h1, h2⟩ := approx_bwd hcc (g : GL (Fin N) (AE D)) h k (g' : GL (Fin N') (AE D)) h' k' y₀
    have hz : pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) M₁ M₁' := by
      rw [pt_mem_iff hcc hδ b1 b1']
      exact entries_of_sub h2 hy'
    refine ⟨⟨_, hz⟩, ?_⟩
    have e : r ⟨_, hz⟩ = z := (pt_injective cc hδ (hr1 ⟨_, hz⟩)).symm
    dsimp only
    rw [e, hy, ← pt_sub, pt_mem_iff hcc hδ a2 a2', mv_sub]
    exact entries_trans (hs2 z) h1

end GlobalTheory.WeilCorr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTransvectionVectorsNeighbourStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transvection_vectors_neighbour : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → (q : 𝓞 D.host.E) ∈ P → (∀ a ∈ P, sgO D a ∈ P) → ∀ (B : Lat D n) (x : Fin n → D.host.E), SD D B → NbD D P B x → ∃ (b x' : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), B = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {b} ∧ nbr D B x = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x'} ∧ (∀ p ∈ P, p • b ∈ nbM D B x ∧ p • x' ∈ nbM D B x) ∧ ¬ IntE D (hE D b x') ∧ NbD D P B (b + x') ∧ nbM D B (b + x') = nbM D B x ∧ lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x') (b + x') = 0 ∧ Nat.Coprime m q ∧ (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) ∧ ∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x')) = (p : D.host.E) := by
  first | exact @GlobalTheory.NbVec.exists_vectors | exact GlobalTheory.NbVec.exists_vectors | (intros; apply GlobalTheory.NbVec.exists_vectors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvPhiSeriesSubNsmulEqDiv
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogShift

open MvPowerSeries

theorem expMv_phAt_sub_nsmul : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  intro p _ g h n hE hh
  have hh' : MvPowerSeries.constantCoeff (h : MvPowerSeries Unit ℂ_[p]) = 0 := hh
  have hX : MvPowerSeries.constantCoeff (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by
    simp [GL3Theta.Xv]
  have ha : MvPowerSeries.constantCoeff (g.phAt (h : MvPowerSeries Unit ℂ_[p])) = 0 :=
    GlobalTheory.CurveToStdLog.cc_phAt g hE hh'
  have hb : MvPowerSeries.constantCoeff (g.phAt (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    GlobalTheory.CurveToStdLog.cc_phAt g hE hX
  refine ⟨by simp [map_sub, map_mul, ha, hb], ?_⟩
  set b : MvPowerSeries Unit ℂ_[p] := g.phAt (GL3Theta.Xv ()) with hbdef
  set F : PowerSeries ℂ_[p] := ePhi1 g.lam g.abelian₂ g.C g.wq with hF

  have hbph : b = (g.ph : MvPowerSeries Unit ℂ_[p]) := by
    show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.ph = g.ph
    rw [← PowerSeries.map_algebraMap_eq_subst_X]; simp

  have hbF : expMv b * (F : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [hbph]; exact (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
  have hnb : MvPowerSeries.constantCoeff (-b) = 0 := by simp [hb]

  have hneg : expMv (-b) = (F : MvPowerSeries Unit ℂ_[p]) := by
    have h0 : expMv b * expMv (-b) = 1 := by
      rw [← GlobalTheory.CurveToStdLog.expMv_add hb hnb, add_neg_cancel, GlobalTheory.CurveToStdLog.expMv_zero]
    calc expMv (-b) = expMv (-b) * (expMv b * (F : MvPowerSeries Unit ℂ_[p])) := by rw [hbF, mul_one]
      _ = (expMv b * expMv (-b)) * F := by ring
      _ = F := by rw [h0, one_mul]
  have hsum : (g.phAt (h : MvPowerSeries Unit ℂ_[p])) - MvPowerSeries.C (n : ℂ_[p]) * b =
      g.phAt (h : MvPowerSeries Unit ℂ_[p]) + ∑ _i ∈ Finset.range n, -b := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_eq_add_neg, ← neg_mul]
    congr 1
    rw [neg_mul, mul_neg]
    congr 1
  have hsum0 : MvPowerSeries.constantCoeff (∑ _i ∈ Finset.range n, -b) = 0 := by
    rw [map_sum]; simp [hb]
  rw [hsum, GlobalTheory.CurveToStdLog.expMv_add ha hsum0,
    GlobalTheory.CurveToStdLog.expMv_sum _ (fun _ => hnb), Finset.prod_const, Finset.card_range, hneg,
    ← GlobalTheory.CurveToStdLog.inv_ePhi1 g hE hh']

end GlobalTheory.ExpLogShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtremalRowWeight
section
open GlobalTheory.DualWeyl MvPolynomial NumberField
open Formalism.GradedWeylDivisibility (rowAct rowW rowNu)
open Formalism.REAL (fockF)
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.DualWeylFock

variable {N : ℕ} {la : Fin N → ℕ}

theorem fock_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) : fockF (c • f) g = c * fockF f g := by
  rw [Formalism.REAL.fischerInner_eq_sum_of_subset _ _ f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

def fockLeft {σ : Type} (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun f := fockF f g
  map_add' f f' := Formalism.REAL.fischerInner_add_left f f' g
  map_smul' c f := fock_smul_left c f g

theorem extremal_rowWeight (hla : Antitone la) : IsWeightedHomogeneous (rowW N N) (extremal la ℂ) la := by
  have hnu : rowNu (r := N) la = la := by
    funext b
    simp [rowNu]
  have := Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl la hla
  rwa [hnu] at this

theorem evalAt_one_of_ne {μ : Fin N → ℕ} (hμ : μ ≠ la) {q : Pol N ℂ} (hq : q ∈ nabla la ℂ)
    (hw : IsWeightedHomogeneous (rowW N N) q μ) : evalAt 1 q = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hμ
  let t : Fin N → ℂ := fun b => if b = a then 2 else 1
  have hprod : ∀ e : Fin N → ℕ, ∏ b, t b ^ e b = 2 ^ e a := by
    intro e
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb; simp [t, hb]
    · simp
  have h1 := evalAt_rowAct 1 (Matrix.diagonal t) q
  have h2 := evalAt_colAct 1 (Matrix.diagonal t) q
  rw [Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t μ _ hw, hprod, Matrix.mul_one, map_smul, smul_eq_mul] at h1
  rw [colAct_of_mem hq _ (Matrix.blockTriangular_diagonal t), Matrix.one_mul, map_smul, smul_eq_mul] at h2
  simp only [diagChar, Matrix.diagonal_apply_eq] at h2
  rw [hprod] at h2
  have hne : (2 : ℂ) ^ μ a - 2 ^ la a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : (2 : ℕ) ^ μ a = 2 ^ la a := by exact_mod_cast h
    exact ha (Nat.pow_right_injective le_rfl h')
  have : ((2 : ℂ) ^ μ a - 2 ^ la a) * evalAt 1 q = 0 := by rw [sub_mul, h1, h2, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

theorem fock_extremal (hla : Antitone la) {f : Pol N ℂ} (hf : f ∈ nabla la ℂ) :
    fockF f (extremal la ℂ) = evalAt 1 f * fockF (extremal la ℂ) (extremal la ℂ) := by
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum := sum_weightedHomogeneousComponent (rowW N N) f
  rw [finsum_eq_sum _ hfin] at hsum
  rw [← hsum, Formalism.REAL.fischerInner_sum_left, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hmem := Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N la μ f hf
  have hw' := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW N N) μ f
  by_cases hμ : μ = la
  · subst hμ
    conv_lhs => rw [GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight ℂ N μ hla _ hmem hw']
    rw [fock_smul_left]
  · rw [evalAt_one_of_ne hμ hmem hw', zero_mul]
    exact Formalism.GradedWeylDivisibility.fockWeightOrth _ _ _ μ la _ _ hμ hw' (extremal_rowWeight hla)

theorem exists_form_eq (ψ : Pol N ℂ →ₗ[ℂ] ℂ) : ∃ h ∈ nabla la ℂ, ∀ f ∈ nabla la ℂ, form la f h = ψ f := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  let φ : Space la →ₗ[ℂ] ℂ := ψ ∘ₗ (nabla la ℂ).subtype ∘ₗ (toSpace la).symm.toLinearMap
  let v : Space la := (InnerProductSpace.toDual ℂ (Space la)).symm (LinearMap.toContinuousLinearMap φ)
  refine ⟨((toSpace la).symm v).1, ((toSpace la).symm v).2, fun f hf => ?_⟩
  have h1 : ⟪v, toSpace la ⟨f, hf⟩⟫_ℂ = φ (toSpace la ⟨f, hf⟩) := InnerProductSpace.toDual_symm_apply
  exact h1

theorem form_eq_fock_div (N : ℕ) (la : Fin N → ℕ) (hla : Antitone la) :
    ∀ f ∈ nabla la ℂ, ∀ f' ∈ nabla la ℂ,
      form la f f' = fockF f f' / fockF (extremal la ℂ) (extremal la ℂ) := by
  intro f hf f' hf'
  obtain ⟨hre, him⟩ := Formalism.GradedWeylDivisibility.fockPos _ (extremal la ℂ) extremal_ne_zero
  set c := fockF (extremal la ℂ) (extremal la ℂ) with hc
  have hc0 : c ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hcc : conj c = c := Complex.conj_eq_iff_im.mpr him
  obtain ⟨h, hh, H⟩ := exists_form_eq (la := la) (c⁻¹ • fockLeft f')
  have H' : ∀ g ∈ nabla la ℂ, form la g h = fockF g f' / c := fun g hg => by
    rw [H g hg, div_eq_inv_mul]; rfl
  have hE := extremal_mem (R := ℂ) hla
  have key : h = f' := by
    rw [← sub_eq_zero]
    refine eq_zero_of_evalAt_unitary (Submodule.sub_mem _ hh hf') fun u => ?_
    have hst : ∀ (g : Matrix (Fin N) (Fin N) ℂ), ∀ p ∈ nabla la ℂ, rowAct ℂ g p ∈ nabla la ℂ :=
      fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N la g p hp
    have h1 := H' _ (hst (u.1)ᴴ _ hE)
    have h2 : rowAct ℂ u.1 (rowAct ℂ (u.1)ᴴ (extremal la ℂ)) = extremal la ℂ := by
      have h3 : (u.1)ᴴ * u.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp u.2
      rw [← AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowActMul ℂ N N, h3, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
      rfl
    rw [← form_rowAct u, h2, Formalism.GradedWeylDivisibility.fockRowAdj, Matrix.conjTranspose_conjTranspose, ← conj_form,
      (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one N la hla).1 _ (hst _ _ hh), Formalism.GradedWeylDivisibility.fockHerm, fock_extremal hla (hst _ _ hf'),
      evalAt_rowAct, evalAt_rowAct, Matrix.mul_one, ← hc, ← starRingEnd_apply, map_mul, hcc,
      mul_div_cancel_right₀ _ hc0] at h1
    rw [map_sub, sub_eq_zero]
    exact (starRingEnd ℂ).injective h1
  rw [← H' f hf, key]

end GlobalTheory.DualWeylFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslateStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conj_taylor_thetaTranslate : ∀ D : D7, gal1 D := by
  first | exact @GlobalTheory.JetConj.galois_translate_sgStar | exact GlobalTheory.JetConj.galois_translate_sgStar | (intros; apply GlobalTheory.JetConj.galois_translate_sgStar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExistsStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_data_exists : ∀ D : D7, galEx D := by
  first | exact @GlobalTheory.GalExist.galEx_all | exact GlobalTheory.GalExist.galEx_all | (intros; apply GlobalTheory.GalExist.galEx_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOneStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imaginary_quadratic_field_structure : ∀ D : D7, Module.finrank D.host.K D.host.E = fF D ∧ ∃ (σ : D.host.K →+* D.host.K) (θ : D.host.K), (∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) ∧ θ ^ 2 = -(D.host.d : D.host.K) ∧ σ θ = -θ ∧ (∀ x : D.host.K, ∃ a b : ℚ, x = (a : D.host.K) + (b : D.host.K) * θ) ∧ IsIntegral ℤ ((1 + θ) / 2) ∧ (∀ y : D.host.E, D.host.conj (D.host.conj y) = y) ∧ (∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y)) ∧ ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  first | exact @GlobalTheory.QuadSubfield.quadratic_subfield | exact GlobalTheory.QuadSubfield.quadratic_subfield | (intros; apply GlobalTheory.QuadSubfield.quadratic_subfield <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpecStatement
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergReproducingKernelSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  first | exact @GlobalTheory.UnitaryTheta.KerSum.kerSum_spec | exact GlobalTheory.UnitaryTheta.KerSum.kerSum_spec | (intros; apply GlobalTheory.UnitaryTheta.KerSum.kerSum_spec <;> assumption)
end

