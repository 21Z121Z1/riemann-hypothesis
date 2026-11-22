import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSplitLatticeTwistDiagonalCoprime
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem twist_split_diagonal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  intro F _ _ _ N 𝔞 𝔟 x a hcop hlev
  have hstd : ∀ w : Fin 2 → F, w ∈ stdLat F ↔ ∀ i, w i ∈ (1 : Submodule (𝓞 F) F) := by
    intro w; simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  have hsp : ∀ (z : F) (w : Fin 2 → F), w ∈ split 𝔞 𝔟 z ↔
      w 0 ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) ∧
      w 1 - w 0 * z ∈ (latM 𝔞 : Submodule (𝓞 F) F) := fun _ _ ↦ Iff.rfl
  have hA : (Matrix.diagonal ![1, (a : ZMod N)]) =
      (Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → ZMod N) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hv0 : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → F)) = ![y 0, a * y 1] := by
    intro y
    ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  have hN : ∀ w ∈ stdLat F, (N : F) • w ∈ split 𝔞 𝔟 x := by
    intro w hw
    have h := hlev.1 w hw
    rw [Nat.cast_smul_eq_nsmul] at h ⊢
    exact h
  have hz : ∀ (n : ℤ) (S : Submodule (𝓞 F) F) (m : F), m ∈ S → (n : F) * m ∈ S := by
    intro n S m hm
    rw [← zsmul_eq_mul]
    exact zsmul_mem hm n
  ext v
  rw [hA, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ _ v hlev.2]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    rw [hv0]
    have hw' := (hstd w).1 hw
    have h0 := (hsp _ _).1 (hN ![w 0, 0] ((hstd _).2 (by
      intro i; fin_cases i
      · exact hw' 0
      · exact Submodule.zero_mem _)))
    have h1 := (hsp _ _).1 (hN ![0, w 1] ((hstd _).2 (by
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hw' 1)))
    have hy' := (hsp _ _).1 hy
    rw [hsp]
    refine ⟨?_, ?_⟩
    · have := Submodule.add_mem _ hy'.1 h0.1
      convert this using 1
      simp
    · have := Submodule.add_mem _ (Submodule.add_mem _ (hz a _ _ hy'.2) h1.2) (hz a _ _ h0.2)
      convert this using 1
      simp
      ring
  · intro hv
    have hv' := (hsp _ _).1 hv
    obtain ⟨u, t, hut⟩ := hcop
    have hut' : (u : F) * a + t * N = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → F) hut
    have hm : ![0, v 1 - v 0 * (a * x)] ∈ split 𝔞 𝔟 x := by
      rw [hsp]
      refine ⟨Submodule.zero_mem _, ?_⟩
      convert hv'.2 using 1
      simp
    have hm' := (hstd _).1 (hlev.2 hm) 1
    refine ⟨![v 0, v 0 * x + u * (v 1 - v 0 * (a * x))], ?_, ![0, t * (v 1 - v 0 * (a * x))], ?_, ?_⟩
    · rw [hsp]
      refine ⟨hv'.1, ?_⟩
      convert hz u _ _ hv'.2 using 1
      simp
    · rw [hstd]
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hz t _ _ hm'
    · rw [hv0]
      ext j; fin_cases j
      · simp
      · simp
        linear_combination (-(v 1 - v 0 * (a * x))) * hut'

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfTraceIntegralUnramified
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
open scoped nonZeroDivisors

namespace GlobalTheory.LieDisc

theorem isIntegral_of_trace_integral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E,
      (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  intro E _ _ _ hu w hw
  set F := maximalRealSubfield E
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hu
    infer_instance
  have hd : differentIdeal (𝓞 F) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [hd, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  have hmem : w ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have ht := Formalism.FourierDecayAlt.P.S6x3.trace_eq E (w * algebraMap (𝓞 E) E b)
    have hi : IsIntegral ℤ (Algebra.trace F E (w * algebraMap (𝓞 E) E b)) := by
      rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective F E), ht]
      exact hw _ (RingOfIntegers.isIntegral_coe b)
    exact ⟨⟨_, hi⟩, rfl⟩
  rw [hdual] at hmem
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

end GlobalTheory.LieDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageInfOfIsSeparatedOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FinNear

theorem isAffineOpen_preimage_inf_of_isSeparated_over {Y X S : Scheme.{0}} (g : Y ⟶ X) (s : X ⟶ S)
    [IsSeparated s] {T : S.Opens} (hT : IsAffineOpen T) {D : X.Opens} (hD : IsAffineOpen D)
    (hDT : D ≤ s ⁻¹ᵁ T) {V : Y.Opens} (hV : IsAffineOpen V) (hVT : V ≤ g ⁻¹ᵁ (s ⁻¹ᵁ T)) :
    IsAffineOpen (g ⁻¹ᵁ D ⊓ V) := by
  have : IsAffine V := hV
  have : IsAffine T := hT
  have : IsAffine D := hD
  let g' : V.toScheme ⟶ (s ⁻¹ᵁ T).toScheme := g.resLE (s ⁻¹ᵁ T) V hVT
  have : IsAffineHom (g' ≫ (s ∣_ T)) := isAffineHom_of_isAffine _
  have : IsAffineHom g' := IsAffineHom.of_comp g' (s ∣_ T)
  have hD' : IsAffineOpen ((s ⁻¹ᵁ T).ι ⁻¹ᵁ D) := by
    have h := isAffineOpen_opensRange (X.homOfLE hDT)
    rwa [Scheme.opensRange_homOfLE] at h
  have h := (hD'.preimage g').image_of_isOpenImmersion V.ι
  rwa [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h

end GlobalTheory.FinNear

namespace GlobalTheory.FinNear

end GlobalTheory.FinNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionMorphismRestrictBasicOpenOfMulMStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) → ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) → IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  first | exact @GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range | exact GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range | (intros; apply GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelf
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem trace_pi_eq_sum (n : ℕ) (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    LinearMap.trace ℂ (Fin n → ℂ) A = ∑ i, A (Pi.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

theorem kills_self : ∀ (G : Type) [Group G] [Finite G] (Y : G → ℂ), IsChar ℂ ℂ Y → Kills Y Y := by
  intro G _ _ Y hY V _ _ _ ρ h
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨n, σ, hσ⟩ := hY
  have hYc : ∀ g, Y g = σ.character g := fun g => by simpa using hσ g
  have hst : ∀ g, star (Y g) = σ.character g⁻¹ := fun g => by
    rw [star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]
  rw [finsum_eq_sum_of_fintype] at h
  rw [finsum_eq_sum_of_fintype]
  simp only [hst] at h ⊢

  have hinv : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne')
  have hfr := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)
  simp only [Representation.char_linHom] at hfr
  have h' : ∑ g : G, σ.character g⁻¹ * ρ.character g = 0 := h
  rw [h', mul_zero] at hfr
  have hbot : (Representation.linHom σ ρ).invariants = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast hfr.symm

  have hsum : ∀ f : (Fin n → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom σ ρ g f = 0 := by
    intro f
    have hm : ∑ g : G, Representation.linHom σ ρ g f ∈ (Representation.linHom σ ρ).invariants := by
      intro h
      rw [map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  ext v
  have key : ∀ i : Fin n, ∑ g : G, (σ g⁻¹ (Pi.single i 1)) i • ρ g v = 0 := by
    intro i
    have := congrArg (fun F : (Fin n → ℂ) →ₗ[ℂ] V => F (Pi.single i 1))
      (hsum ((LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ).smulRight v))
    simpa [Representation.linHom_apply, LinearMap.sum_apply] using this
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
  simp only [Representation.character, trace_pi_eq_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => key i)

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.RatUnit

theorem sum_eq_dot {R : Type} [CommRing R] {r : ℕ} (σ : R → R) (G : Matrix (Fin r) (Fin r) R)
    (x y : Fin r → R) : ∑ a, ∑ b, x a * G a b * σ (y b) = x ⬝ᵥ (G *ᵥ (σ ∘ y)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp, mul_assoc]

theorem dot_mulVec {R : Type} [CommRing R] {r : ℕ} (σ : R →+* R) (G γ : Matrix (Fin r) (Fin r) R)
    (x y : Fin r → R) :
    (γ *ᵥ x) ⬝ᵥ (G *ᵥ (σ ∘ (γ *ᵥ y))) = x ⬝ᵥ ((γᵀ * G * γ.map σ) *ᵥ (σ ∘ y)) := by
  have h : σ ∘ (γ *ᵥ y) = γ.map σ *ᵥ (σ ∘ y) := by
    funext i; exact RingHom.map_mulVec σ γ y i
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x γᵀ,
    Matrix.vecMul_transpose]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in

theorem _root_.GlobalTheory.RatUnit.isUA_ratM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E), γ.det ≠ 0 → (∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (γ *ᵥ x) (γ *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) → _root_.GlobalTheory.UCls.IsUA (IsCMField.complexConj E) G (_root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ) := by
  intro E _ _ _ r G γ hdet hinv
  have hmat : ∀ i j, ∑ a, ∑ b, γ a i * G a b * IsCMField.complexConj E (γ b j) = G i j := by
    intro i j
    have h := hinv (Pi.single i 1) (Pi.single j 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
    simpa [mulVec, dotProduct, Pi.single_apply, apply_ite] using h
  let A := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
  let φ : E →+* _root_.GlobalTheory.AdLat.RA (maximalRealSubfield E) E :=
    (Algebra.TensorProduct.includeRight :
      E →ₐ[maximalRealSubfield E] A ⊗[maximalRealSubfield E] E).toRingHom
  have hφ : ∀ e : E, φ e = (1 : A) ⊗ₜ[maximalRealSubfield E] e := fun _ => rfl
  have hg : _root_.GlobalTheory.UCls.ratM (maximalRealSubfield E) γ = γ.map φ := rfl
  let τ := _root_.GlobalTheory.AdLat.sg A (IsCMField.complexConj E)
  have hτ : ∀ e : E, τ (φ e) = φ (IsCMField.complexConj E e) := by
    intro e
    simp [τ, hφ, _root_.GlobalTheory.AdLat.sg]
  unfold _root_.GlobalTheory.UCls.IsUA
  rw [hg]
  refine ⟨?_, fun x y => ?_⟩
  · have h := RingHom.map_det φ γ
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (isUnit_iff_ne_zero.mpr hdet).map φ
  · unfold _root_.GlobalTheory.AdLat.hermA
    change ∑ a, ∑ b, (γ.map φ *ᵥ x) a * φ (G a b) * τ ((γ.map φ *ᵥ y) b) =
      ∑ a, ∑ b, x a * φ (G a b) * τ (y b)
    calc _ = ∑ a, ∑ b, ∑ i, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) := by
          simp only [mulVec, dotProduct, map_apply, map_sum, map_mul, hτ, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ a, ∑ i, ∑ b, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b, ∑ j,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ j, ∑ b,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ a, ∑ b,
            x i * (φ (γ a i) * φ (G a b) * φ (IsCMField.complexConj E (γ b j))) * τ (y j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, x i * φ (G i j) * τ (y j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← hmat i j, map_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [map_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [map_mul]

end GlobalTheory.RatUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenRegularLocusOfNagataStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_regularLocus_of_nagata' : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  first | exact @GlobalTheory.isOpen_regularLocus_of_nagata | exact GlobalTheory.isOpen_regularLocus_of_nagata | (intros; apply GlobalTheory.isOpen_regularLocus_of_nagata <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImageStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_inf_ideal_sheaf_image : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W), IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) → IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  first | exact @GlobalTheory.isProper_map_inf_subschemeι | exact GlobalTheory.isProper_map_inf_subschemeι | (intros; apply GlobalTheory.isProper_map_inf_subschemeι <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
section
noncomputable section

namespace GlobalTheory.TorusFrame

open NumberField Matrix Complex GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem angles_add (φ ψ : Fin (r - 1) → ℝ) (a : Fin r) : angles (φ + ψ) a = angles φ a + angles ψ a := by
  unfold angles; split_ifs <;> simp [Finset.sum_add_distrib]; ring

theorem angles_smul (c : ℝ) (φ : Fin (r - 1) → ℝ) (a : Fin r) : angles (c • φ) a = c * angles φ a := by
  unfold angles; split_ifs <;> simp [Finset.mul_sum]

theorem angles_zero (a : Fin r) : angles (0 : Fin (r - 1) → ℝ) a = 0 := by
  unfold angles; split_ifs <;> simp

def anglesL (r : ℕ) : (Fin (r - 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun φ a := angles φ a
  map_add' φ ψ := funext fun a => angles_add φ ψ a
  map_smul' c φ := funext fun a => angles_smul c φ a

theorem continuous_angles (a : Fin r) : Continuous fun φ : Fin (r - 1) → ℝ => angles φ a :=
  ((continuous_apply a).comp (LinearMap.continuous_of_finiteDimensional (anglesL r)) :)

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, mul_apply, transpose_apply, map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem isUnit_det_of_isOrth {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    IsUnit (mat x τ).det := by
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq, det_mul, det_mul, det_transpose, det_diagonal] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_mul, zero_mul] at h
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h.symm
  unfold sgn; split_ifs <;> norm_num

def frameU {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : GL (Fin r) ℂ :=
  nonsingInvUnit (mat x τ) (isUnit_det_of_isOrth hx τ)

def phaseU (φ : Fin (r - 1) → ℝ) : GL (Fin r) ℂ where
  val := diagonal fun a => exp (I * (angles φ a : ℂ))
  inv := diagonal fun a => exp (-(I * (angles φ a : ℂ)))
  val_inv := by rw [diagonal_mul_diagonal]; simp [← exp_add]
  inv_val := by rw [diagonal_mul_diagonal]; simp [← exp_add]

def torusGL {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ) :
    X.Ψ → GL (Fin r) ℂ :=
  fun τ => frameU hx τ * phaseU (θ τ) * (frameU hx τ)⁻¹

theorem torusGL_val {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x) (θ : X.Ψ → Fin (r - 1) → ℝ) (τ : X.Ψ) :
    ((torusGL hx θ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => exp (I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ := rfl

def torusDerL {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin (r - 1) → ℝ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) where
  toFun θ τ a b := (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) a b
  map_add' θ θ' := by
    funext τ a b
    simp only [Pi.add_apply, angles_add, ofReal_add, mul_add, ← diagonal_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c θ := by
    funext τ a b
    have : (diagonal fun d => I * (angles (c • θ τ) d : ℂ)) = (c : ℂ) • diagonal fun d => I * (angles (θ τ) d : ℂ) := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h, angles_smul]; ring
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

def torusDer {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    (Ψ → Fin (r - 1) → ℝ) →L[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
  LinearMap.toContinuousLinearMap (torusDerL x)

theorem torusDer_apply {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (θ : Ψ → Fin (r - 1) → ℝ) (τ : Ψ) (a b : Fin r) :
    torusDer x θ τ a b = (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) a b := rfl

end GlobalTheory.TorusFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedComplexPartialDerivativeEqWirtingerWordStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedComplexPartialDerivative_eq_wirtingerWord : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U, iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by
  first | exact @GlobalTheory.HoloWirt.iterD_eq_wirtWord | exact GlobalTheory.HoloWirt.iterD_eq_wirtWord | (intros; apply GlobalTheory.HoloWirt.iterD_eq_wirtWord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamilyStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_admissible_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → ∀ x : Fin (r + 1) → F, x ≠ 0 → ∃ (h : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (u : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), h.det ≠ 0 ∧ (∀ v, Unimod v (u v)) ∧ (∀ (v : Place k F) (i : Fin r), (u v * g v * h) i.succ 0 = 0) ∧ admitted (fun v => u v * g v * h) ∧ admitted (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ deg g = degLine g x + deg (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x ∧ ∀ b : ℝ, LinesLE g b → LinesLE (fun v => u v * g v * h) b := by
  first | exact @GlobalTheory.iwasawa_family | exact GlobalTheory.iwasawa_family | (intros; apply GlobalTheory.iwasawa_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestriction
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem res_defect : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ),
    IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) =
      GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  intro Q q _ hqQ V U g v hQ
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (zero_dvd_iff.mp hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hqU : IsUnit (q : Γ(U, ⊤)) := by
    obtain ⟨k, hk⟩ := hqQ
    rw [hk, Nat.cast_mul] at hQ
    exact isUnit_of_mul_isUnit_left hQ
  unfold defect
  rw [Sec.res, map_sub]
  change Sec.res g _ - Sec.res g _ = _
  rw [(redMap Q q 1).nat g 0, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).1 V U g v hQ, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g _ hqU, map_pow]

end GlobalTheory.EtC.RedChern
end

