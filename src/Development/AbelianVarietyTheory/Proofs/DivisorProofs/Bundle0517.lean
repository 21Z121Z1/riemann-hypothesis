import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0501
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantPDivGroupOmegaTrivialHodgeTateBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorTimesSplitPrimesExponentsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductorTimesSplitPrimes_exponents : ∀ (E : Type) [Field E] [NumberField E] (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → condQ 𝔣 Q ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ condQ 𝔣 Q → Splits v) ∧ (∀ v : HeightOneSpectrum (OF E), expIn (condQ 𝔣 Q) v ≠ 0 → v.asIdeal ∣ condQ 𝔣 Q) ∧ (∀ v ∈ Q, expIn (condQ 𝔣 Q) v = 1) ∧ (∀ v ∉ Q, expIn (condQ 𝔣 Q) v = expIn 𝔣 v) ∧ {v : HeightOneSpectrum (OF E) | expIn (condQ 𝔣 Q) v ≠ 0}.Finite := by
  first | exact @GlobalTheory.CMVal.CondExp.condQ_exponents | exact GlobalTheory.CMVal.CondExp.condQ_exponents | (intros; apply GlobalTheory.CMVal.CondExp.condQ_exponents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantPDivGroupOmegaTrivialHodgeTateBasisStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantPDivGroup_omega_trivial_hodgeTate_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, IsConst G → Subsingleton G.omega ∧ ∀ (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate), Function.Bijective (Fintype.linearCombination O fun i => hodgeTate G (b i)) := by
  first | exact @GlobalTheory.ConstHT.omega_const | exact GlobalTheory.ConstHT.omega_const | (intros; apply GlobalTheory.ConstHT.omega_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
section
noncomputable section

open NumberField

namespace GlobalTheory.HeckeMellin

variable {I : Type} [Fintype I]

def term (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) : ℂ :=
  GlobalTheory.HeckeTheta.gauss n (GlobalTheory.HeckeTheta.dil y v) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))

theorem term_zero {n : I → ℤ} (hn : ∃ i, n i ≠ 0) (s : ℂ) (y : I → ℝ) : term n s 0 y = 0 := by
  have : GlobalTheory.HeckeTheta.dil y (0 : I → ℂ) = 0 := by
    funext i; simp [GlobalTheory.HeckeTheta.dil]
  rw [term, this, GlobalTheory.HeckeTheta.gauss_zero hn, zero_mul]

end GlobalTheory.HeckeMellin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutChainCosetSumScalingOfUnimodularit
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem finsum_out_inv_congr {A : Type} [Group A] (U V : Subgroup A) (e : MulAut A) (f : A → ℂ)
    (he : ∀ a, a ∈ U ↔ e a ∈ V) (hV : ∀ v ∈ V, ∀ a, f (v * a) = f a) :
    ∑ᶠ y : A ⧸ U, f (e y.out)⁻¹ = ∑ᶠ y : A ⧸ V, f y.out⁻¹ := by
  let E : A ⧸ U ≃ A ⧸ V := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he, map_mul, map_inv]
    rfl)
  have hE : ∀ a : A, E (QuotientGroup.mk a) = QuotientGroup.mk (e a) := fun a => rfl
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun y => ?_
  have h1 : E y = QuotientGroup.mk (e y.out) := by
    rw [← hE, QuotientGroup.out_eq']
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V (e y.out)
  rw [h1, hv, mul_inv_rev, hV _ (V.inv_mem v.2)]

theorem chainSum_of_unimod : Unimod → ChainIndex → ChainSum := by
  classical
  intro hUn hCh A _ U c Q d f hc hQ hind hex hV hU hfin
  have hchain := hCh A U c Q hc hind
  have hmem : ∀ (j : ℤ) (a : A), a ∈ U.comap (c ^ j).toMonoidHom ↔ (c ^ j) a ∈ U := fun j a => Iff.rfl
  have hmono : ∀ j j' : ℤ, j ≤ j' → U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ j').toMonoidHom := by
    intro j j' h
    have := (hchain j (j' - j).toNat).1
    rwa [show j + ((j' - j).toNat : ℤ) = j' by omega] at this
  have h0 : U.comap (c ^ (0 : ℤ)).toMonoidHom = U := by
    ext a
    rw [hmem, zpow_zero, MulAut.one_apply]
  choose J hJ using hex
  obtain ⟨k, hkd, hk⟩ : ∃ k : ℕ, d ≤ k ∧ ∀ y : A ⧸ U, f y.out ≠ 0 → J y.out ≤ k := by
    refine ⟨hfin.toFinset.sup (fun y => J y.out) + d.toNat, by omega, fun y hy => ?_⟩
    exact le_trans (Finset.le_sup (f := fun y : A ⧸ U => J y.out) (hfin.mem_toFinset.2 hy)) (Nat.le_add_right _ _)
  obtain ⟨l, hl⟩ : ∃ l : ℕ, d + l = k := ⟨(k - d).toNat, by omega⟩
  have hUΓ : U ≤ U.comap (c ^ (k : ℤ)).toMonoidHom := by
    have := hmono 0 k (by omega)
    rwa [h0] at this
  have iU : U.relIndex (U.comap (c ^ (k : ℤ)).toMonoidHom) = Q ^ k := by
    have := (hchain 0 k).2
    rwa [h0, zero_add] at this
  have iV : (U.comap (c ^ d).toMonoidHom).relIndex (U.comap (c ^ (k : ℤ)).toMonoidHom) = Q ^ l := by
    have := (hchain d l).2
    rwa [hl] at this
  have hsupp : ∀ a, f a ≠ 0 → a ∈ U.comap (c ^ (k : ℤ)).toMonoidHom := by
    intro a ha
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U a
    have h1 : f (QuotientGroup.mk a : A ⧸ U).out ≠ 0 := by rwa [hu, hU _ u.2]
    have h2 : (QuotientGroup.mk a : A ⧸ U).out ∈ U.comap (c ^ (k : ℤ)).toMonoidHom := by
      refine hmono (J (QuotientGroup.mk a : A ⧸ U).out : ℕ) k (by exact_mod_cast hk _ h1) ?_
      rw [hmem, zpow_natCast]
      exact hJ _
    rw [hu] at h2
    exact (Subgroup.mul_mem_cancel_right _ (hUΓ u.2)).1 h2
  have key := hUn A _ U (U.comap (c ^ d).toMonoidHom) f hUΓ (hmono d k hkd)
    (by rw [iU]; exact pow_ne_zero _ hQ) (by rw [iV]; exact pow_ne_zero _ hQ) hsupp
    (fun v hv => hV v hv) hU
  rw [finsum_out_inv_congr U (U.comap (c ^ d).toMonoidHom) (c ^ (-d)) f (fun a => by
    rw [hmem, ← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply])
    (fun v hv => hV v hv)]
  rw [iU, iV] at key
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hpow : (Q : ℂ) ^ l = (Q : ℂ) ^ k * (Q : ℂ) ^ (-d) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hQ']
    congr 1
    omega
  push_cast at key
  rw [hpow, mul_assoc] at key
  exact mul_left_cancel₀ (pow_ne_zero _ hQ') key

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutomorphismSubgroupChainIndex
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem chain_comap_eq {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom = (U.map c.toMonoidHom).comap (c ^ (j + 1)).toMonoidHom := by
  ext a
  have h : (c ^ (j + 1)) a = c ((c ^ j) a) := by
    rw [add_comm, zpow_add, zpow_one, MulAut.mul_apply]
  simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, h]
  constructor
  · intro ha
    exact ⟨_, ha, rfl⟩
  · rintro ⟨x, hx, hxa⟩
    rw [← c.injective hxa]
    exact hx

theorem chain_step {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (hc : ∀ a ∈ U, c a ∈ U) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ (j + 1)).toMonoidHom ∧
      (U.comap (c ^ j).toMonoidHom).relIndex (U.comap (c ^ (j + 1)).toMonoidHom) =
        (U.map c.toMonoidHom).relIndex U := by
  rw [chain_comap_eq U c j]
  refine ⟨Subgroup.comap_mono ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  · rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]
    exact (c ^ (j + 1)).surjective

theorem chainIndex : ChainIndex := by
  intro A _ U c Q hc hQ j l
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨h1, h2⟩ := chain_step U c hc (j + l)
    have e : j + ((l + 1 : ℕ) : ℤ) = j + l + 1 := by push_cast; ring
    rw [e]
    refine ⟨ih.1.trans h1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ ih.1 h1, ih.2, h2, hQ, pow_succ]

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6nat_holds : GlobalTheory.EtC.DivisorNaturality := by
  intro q _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f n m i j a b
    exact GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b
  · intro E E' f h
    exact (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.1 f h
  · intro E E' f L h
    exact (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 f L h
  · intro Y X f u h
    exact (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 f u h

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupVanishesOnTwoMemberCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem a6supp : DivisorSupportCondition := by
  intro q _ U V E f g hc n m i j a b ha hb
  exact GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover (ZMod q) (twPair q i j) ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)).2.1)
    ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q j)).2.1) f g hc rfl a b ha hb

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEqStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] → cusp θ m k' = cusp θ m k := by
  first | (exact @GlobalTheory.Shin.cusp_eq_of_modEq) | (exact GlobalTheory.Shin.cusp_eq_of_modEq) | (intros; apply GlobalTheory.Shin.cusp_eq_of_modEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedProductDerivativeTermNormLeUniformStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by
  first | exact @GlobalTheory.DeformedSum.Bound.dTerm_bound | exact GlobalTheory.DeformedSum.Bound.dTerm_bound | (intros; apply GlobalTheory.DeformedSum.Bound.dTerm_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantFrameComparison
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frames_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ eT eM : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame (rhoTA D) eT ∧ IsFrame D.ρM eM ∧ ∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], eT (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := inferInstance
  set d := Module.finrank ℤ_[p] Λ with hd
  have dpos : 0 < d := Module.finrank_pos
  obtain ⟨N', x, y, hN', hx, hy⟩ :=
    GlobalTheory.T.exists_span_rhoM_rhoT_mulVec_eq_top p C v O hv ε hε Λ h D d (Module.finBasis ℤ_[p] Λ)
  have hNN : N' = N := by
    have : d * N' = d * N := by rw [mul_comm, ← hN', hh]
    exact Nat.eq_of_mul_eq_mul_left dpos this
  subst hNN
  have hh' : h = N' * d := hN'

  have sM := (GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D).1
  obtain ⟨eM, heM, -⟩ := GlobalTheory.T.ainf_frame_span_generation p O Λ N' d h (Module.finBasis ℤ_[p] Λ) D.ρM x sM hh' hx

  let ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O) :=
    (RingHom.mapMatrix (ofPadic p O)).comp D.ρT.toRingHom
  have hρ : ∀ l, ρ l = rhoTA D l := fun l => rfl
  have sT : ∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
    intro c
    rw [hρ, rhoTA, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext1 i j
    by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply, Matrix.one_apply]
  let L : (Fin h → ℤ_[p]) →ₗ[ℤ_[p]] (Fin h → Ainf p O) :=
    (Algebra.linearMap ℤ_[p] (Ainf p O)).compLeft (Fin h)
  have hL : ∀ w j, L w j = ofPadic p O (w j) := fun w j => rfl
  have hLmul : ∀ (l : Λ) (w : Fin h → ℤ_[p]), L (D.ρT l *ᵥ w) = ρ l *ᵥ (fun j => ofPadic p O (w j)) := by
    intro l w; funext j
    rw [hL, hρ, rhoTA, RingHom.map_mulVec]
    rfl
  have hxT : Submodule.span (Ainf p O) (Set.range fun ij : Fin N' × Fin d =>
      ρ (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ (fun j => ofPadic p O (y ij.1 j))) = ⊤ := by
    set S := Set.range fun ij : Fin N' × Fin d =>
      ρ (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ (fun j => ofPadic p O (y ij.1 j))
    have hle : Submodule.span ℤ_[p] (Set.range fun ij : Fin N' × Fin d =>
        D.ρT (Module.finBasis ℤ_[p] Λ ij.2) *ᵥ y ij.1) ≤
        ((Submodule.span (Ainf p O) S).restrictScalars ℤ_[p]).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨ij, rfl⟩
      show L _ ∈ Submodule.span (Ainf p O) S
      rw [hLmul]
      exact Submodule.subset_span ⟨ij, rfl⟩
    rw [eq_top_iff, ← (Pi.basisFun (Ainf p O) (Fin h)).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hk := hle (hy ▸ Submodule.mem_top : Pi.single k (1 : ℤ_[p]) ∈ _)
    have e1 : L (Pi.single k 1) = Pi.basisFun (Ainf p O) (Fin h) k := by
      funext j
      rw [hL, Pi.basisFun_apply]
      by_cases hkj : j = k
      · subst hkj; simp
      · simp [Pi.single_apply, hkj]
    rw [← e1]
    exact hk
  obtain ⟨eT, heT, heT1⟩ := GlobalTheory.T.ainf_frame_span_generation p O Λ N' d h (Module.finBasis ℤ_[p] Λ) ρ
    (fun i j => ofPadic p O (y i j)) sT hh' hxT
  refine ⟨eT, eM, heT, heM, fun i l => ⟨D.ρT l *ᵥ y i, ?_⟩⟩
  rw [heT1, ← hLmul]
  rfl

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPowFinrankEqSpanDiscrStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' : ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  first | exact @GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | exact GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | (intros; apply GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEmbeddingRingHomPropertyStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_embedding_ring_hom_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ : Λ →+* O, ∃ s : RL p O Λ, (∀ f, IsTheta τ f → f s ≠ 0) ∧ (∀ σ f, σ ≠ τ → IsTheta σ f → f s = 0) ∧ ∀ f, IsTheta τ f → ∀ r, f r = 0 → (inA (xi ε) : RL p O Λ) ∣ s * r := by
  first | exact @GlobalTheory.DetInv.exists_sep_theta | exact GlobalTheory.DetInv.exists_sep_theta | (intros; apply GlobalTheory.DetInv.exists_sep_theta <;> assumption)
end

