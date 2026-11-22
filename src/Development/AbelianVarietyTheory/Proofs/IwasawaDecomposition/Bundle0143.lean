import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Counterexamples.AdelicSplittingExamples.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.HermitianLattices.FinalMass
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMapStatement
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrSub_of_isIrrSub_span_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W → IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) → AbsIrrSub ρ W := by
  first | exact @GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | exact GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | (intros; apply GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClass
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayNorm

theorem int_norm_pos (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {x : 𝓞 K} (hx : x ≠ 0) :
    0 < Algebra.norm ℤ x := by
  classical
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx

  have fibre : ∀ w : InfinitePlace K,
      ∏ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w), φ (x : K) =
        ((Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    intro w
    have hset : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have key := InfinitePlace.mk_eq_iff (φ := φ) (ψ := w.embedding)
      rw [InfinitePlace.mk_embedding] at key
      rw [key]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [← h]; exact (star_star φ).symm
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [h]; exact star_star w.embedding
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [hset, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  have hprod : (algebraMap ℚ ℂ) (Algebra.norm ℚ (x : K)) =
      ((∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)]
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ (x : K)) _
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
    rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ (x : K))]
    push_cast
    exact Finset.prod_congr rfl (fun w _ => fibre w)
  have hpos : (0 : ℝ) < ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) :=
    Finset.prod_pos fun w _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx')
  have hreal : ((Algebra.norm ℚ (x : K) : ℚ) : ℝ) =
      ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) := by
    apply Complex.ofReal_injective
    rw [← hprod]
    simp
  have hq : (0 : ℚ) < Algebra.norm ℚ (x : K) := by
    have := hreal ▸ hpos
    exact_mod_cast this
  rw [← Algebra.coe_norm_int] at hq
  exact_mod_cast hq

theorem norm_cast_eq (K : Type) [Field K] [NumberField K] (p : ℕ) {x y : 𝓞 K}
    (h : x - y ∈ Ideal.span {(p : 𝓞 K)}) :
    ((Algebra.norm ℤ x : ℤ) : ZMod p) = ((Algebra.norm ℤ y : ℤ) : ZMod p) := by
  classical
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
  have hx : x = y + (p : 𝓞 K) * z := by rw [mul_comm, hz]; ring
  let b := RingOfIntegers.basis K
  have h0 : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b (p : 𝓞 K)) = 0 := by
    rw [map_natCast, map_natCast]
    ext i j
    simp
  have hmat : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b x) =
      (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b y) := by
    rw [hx, map_add, map_mul, map_add, map_mul, h0, zero_mul, add_zero]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b]
  have e1 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b x)
  have e2 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b y)
  simp only [eq_intCast] at e1 e2
  rw [e1, e2, hmat]

theorem absNorm_modEq_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  intro K _ _ _ 𝔮 p h𝔮 I α β hR hI
  unfold GlobalTheory.NT.RayPair at hR
  obtain ⟨hα, hβ, -, hβq, hαβ, -⟩ := hR

  have hnorm : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β = Algebra.norm ℤ α := by
    have e := congrArg Ideal.absNorm hI
    rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at e
    have e' : ((Ideal.absNorm I * (Algebra.norm ℤ β).natAbs : ℕ) : ℤ) =
        ((Algebra.norm ℤ α).natAbs : ℤ) := by rw [e]
    push_cast at e'
    rwa [abs_of_pos (int_norm_pos K hβ), abs_of_pos (int_norm_pos K hα)] at e'

  have htop : Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} = ⊤ := by
    rw [Ideal.isCoprime_iff_sup_eq] at hβq
    exact eq_top_mono (sup_le_sup_left h𝔮 _) hβq
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp h1
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have hu : β * u - 1 ∈ Ideal.span {(p : 𝓞 K)} := by
    have e : β * u - 1 = -c := by rw [← hac]; ring
    rw [e]; exact neg_mem hc
  have hinv := norm_cast_eq K p hu
  rw [map_mul, map_one] at hinv
  push_cast at hinv
  have hmod := norm_cast_eq K p (h𝔮 hαβ)
  have key : ((Ideal.absNorm I : ℕ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) =
      ((Algebra.norm ℤ β : ℤ) : ZMod p) := by
    have e := congrArg (fun t : ℤ => (t : ZMod p)) hnorm
    push_cast at e
    rw [e, hmod]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_one]
  linear_combination (1 - ((Ideal.absNorm I : ℕ) : ZMod p)) * hinv +
    ((Algebra.norm ℤ u : ℤ) : ZMod p) * key

end GlobalTheory.Mem.RayNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWtExistsInvForm
section
open NumberField

namespace GlobalTheory

theorem algWt_exists_invForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (a : Formalism.L2.NG.AlgWt L n), ∃ β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ, GlobalTheory.CoefDuty.IsInvForm a β := by
  intro L _ _ _ n a
  exact GlobalTheory.T.exists_invariant_hermitian_weight_form L n a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharacterValueMemKummerField
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem absNorm_pow_eq_prod_sq {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (v : HeightOneSpectrum (𝓞 L)) (h : ℕ)
    (k : L) (hk : FractionalIdeal.spanSingleton (𝓞 L)⁰ k = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ h = (∏ i, ‖φ i k‖) ^ 2 := by
  have h1 := InfinitePlace.prod_eq_abs_norm k
  rw [← hφ.prod_comp] at h1
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) k ^ (InfinitePlace.mk (φ i)).mult = ‖φ i k‖ ^ 2 := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  simp_rw [h2] at h1
  have h3 := congrArg FractionalIdeal.absNorm hk
  rw [FractionalIdeal.absNorm_span_singleton, map_pow, FractionalIdeal.coeIdeal_absNorm] at h3
  rw [← Finset.prod_pow, h1, h3]
  simp

theorem valTw_mem_kummerField : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] [IsTotallyComplex L] (φ₀ : L →+* ℂ) (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (χ : HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∀ (v : HeightOneSpectrum (𝓞 L)) (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → χ.inf k * χ.val v ^ h = 1 → χ.valTw ((r : ℝ) / 2) v ∈ kummerField φ₀ h := by
  intro L _ _ _ _ φ₀ I _ φ hφ χ n r hinf hev v h k hk hχ
  choose s hs using exists_aut φ₀
  choose m hm using hev
  have hkm : (k : L) ∈ powIdealElts L h := ⟨k.ne_zero, _, hk⟩
  have hsm : ∀ τ, s τ (k : L) ∈ powIdealElts L h := fun τ => map_mem_pow (s τ : L →+* L) hkm
  have hy : ∏ i, ((s (φ i) k ^ n i)⁻¹ * (s (φ i) k * s ((starRingEnd ℂ).comp (φ i)) k) ^ m i) ∈ powIdealElts L h :=
    prod_mem_pow _ _ fun i _ => mul_mem_pow (inv_mem_pow (zpow_mem_pow (hsm _) _))
      (zpow_mem_pow (mul_mem_pow (hsm _) (hsm _)) _)
  refine mem_kummerField φ₀ hy ?_
  have hp := congrArg (Units.val : ℂˣ → ℂ) hχ
  rw [Units.val_mul, hinf, Units.val_one, Units.val_pow_eq_pow_val] at hp
  have hN := absNorm_pow_eq_prod_sq φ hφ v h k hk
  have hpow : ∀ m : ℕ, (m : ℂ) ^ (-(((r : ℝ) / 2 : ℝ) : ℂ)) = (((m : ℝ) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_natCast, Complex.ofReal_neg]
  have hreal : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((r : ℝ) / 2))) ^ h = (∏ i, ‖φ i k‖) ^ (-r) := by
    have h0 : 0 ≤ ∏ i, ‖φ i k‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [Real.rpow_pow_comm (Nat.cast_nonneg _), hN, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hc : χ.valTw ((r : ℝ) / 2) v ^ h = ((χ.val v : ℂˣ) : ℂ) ^ h * ∏ i, ((‖φ i k‖ : ℝ) : ℂ) ^ (-r) := by
    unfold HChar.valTw
    rw [hpow, mul_pow, ← Complex.ofReal_pow, hreal, Finset.prod_zpow, Complex.ofReal_zpow, Complex.ofReal_prod]
  rw [hc, eq_inv_of_mul_eq_one_right hp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hz' : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := by simp
  rw [map_mul, map_inv₀, map_zpow₀, map_zpow₀, map_mul, ← hs, ← hs, RingHom.comp_apply, Complex.mul_conj', sq,
    mul_zpow, ← zpow_add₀ hz', ← hm, sub_eq_add_neg, zpow_add₀ hz', div_zpow, inv_div, div_eq_mul_inv]
  ring

end GlobalTheory.Mem.FieldsEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArtinRestrictEqArtinNormSinglePlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_restrict_eq_artin_norm_single_place : ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω]
    (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (W : HeightOneSpectrum (𝓞 K)),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal →
      (∀ W' : HeightOneSpectrum (𝓞 K), W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → W' = W) →
      ∀ (y : Kˣ) (τ : G K Ω),
        toAb K Ω τ = artK (localIdele K W (Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom y)) →
        toAb E Ω (τ.restrictScalars E) =
          art (localIdele E v (Units.map (algebraMap E (v.adicCompletion E)).toMonoidHom
            (Units.map (Algebra.norm E (S := K)) y))) := by
  first | exact @GlobalTheory.NormCompat.res_art_eq_art_norm | exact GlobalTheory.NormCompat.res_art_eq_art_norm | (intros; apply GlobalTheory.NormCompat.res_art_eq_art_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardDvdCardGL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open Formalism.MainNotions Formalism.L2.Col
open scoped TensorProduct

namespace GlobalTheory.Mem.DuInt

theorem idx_eq (g k : ℕ) (hg : g.Prime) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.idxColLoc g k ∧ Nat.card (GL (Fin k) (ZMod g)) = g ^ (k * (k - 1) / 2) * n := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  have h1 : Nat.card {A : GL (Fin k) (ZMod g) // StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      Nat.card (HU (ZMod g) k) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun A => ⟨fun h => ?_, fun h => isUpperUni_of_mem_uniUT le_rfl h⟩)
    have : A ∈ uSet (ZMod g) (fun i j : Fin k => i < j) :=
      ⟨h.2, fun i j hne hij => h.1 i j (lt_of_le_of_ne (not_lt.1 hij) hne.symm)⟩
    rw [← uniUT_full_eq] at this
    exact this
  have h2 := (HU (ZMod g) k).card_mul_index
  have h3 := card_HU (ZMod g) k
  rw [Nat.card_zmod] at h3
  refine ⟨(HU (ZMod g) k).index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_, by rw [← h2, h3]⟩
  unfold StandardLattice.idxColLoc StandardLattice.idxLoc
  rw [h1, ← h2]
  have h4 : (0 : ℝ) < Nat.card (HU (ZMod g) k) := by exact_mod_cast Nat.card_pos
  push_cast
  field_simp

theorem dimV_nat {R : Ranks} (P : HCParam R) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.dimV fun i => ((P.u i : ℚ) : ℝ) := by
  have hk : 0 < R.k := by have := R.m_add_three_le_k; omega
  have hanti : StrictAnti P.u := by
    have key : ∀ d : ℕ, ∀ (a : ℕ) (h : a + d + 1 < R.k), P.u ⟨a + d + 1, h⟩ < P.u ⟨a, by omega⟩ := by
      intro d
      induction d with
      | zero => intro a h; exact (P.v_gt_u ⟨a, by omega⟩).trans (P.u_gt_v ⟨a, by omega⟩)
      | succ d ih =>
        intro a h
        exact ((P.v_gt_u ⟨a + d + 1, by omega⟩).trans (P.u_gt_v ⟨a + d + 1, by omega⟩)).trans (ih a (by omega))
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < b from hab)
    exact key d a hb
  choose z hz using P.u_half
  have gen : ∀ (N : ℕ) (_ : 0 < N) (u : Fin N → ℚ) (z : Fin N → ℤ), StrictAnti u → (∀ i, u i = z i + 1 / 2) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) = StandardLattice.dimV fun i => ((u i : ℚ) : ℝ) := by
    intro N hN u z hu hz
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    obtain ⟨c, hc⟩ := Matrix.superFactorial_dvd_vandermonde_det (fun i => - z i)
    have e1 : StandardLattice.vand (fun i => ((u i : ℚ) : ℝ)) = ((Matrix.vandermonde fun i => - z i).det : ℤ) := by
      rw [Matrix.det_vandermonde]
      unfold StandardLattice.vand
      push_cast
      refine Finset.prod_congr rfl fun a _ => Finset.prod_congr (by ext; simp) fun b _ => ?_
      rw [hz a, hz b]
      push_cast
      ring
    have e2 : StandardLattice.facProd (M + 1) = (M.superFactorial : ℕ) := by
      unfold StandardLattice.facProd
      rw [← Nat.prod_range_succ_factorial]
      push_cast
      rfl
    have h3 : (0 : ℝ) < (M.superFactorial : ℕ) := by
      rw [← e2]
      exact Finset.prod_pos fun i _ => by positivity
    have h4 : 0 < StandardLattice.vand (fun i => ((u i : ℚ) : ℝ)) := by
      refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
      have := hu (Finset.mem_filter.1 hb).2
      have : ((u b : ℚ) : ℝ) < u a := by exact_mod_cast this
      linarith
    have e5 : StandardLattice.dimV (fun i => ((u i : ℚ) : ℝ)) = c := by
      unfold StandardLattice.dimV
      rw [e1, e2, hc]
      push_cast
      field_simp
    have h6 : (0 : ℝ) < c := by
      rw [← e5]
      exact div_pos h4 (e2 ▸ h3)
    have h7 : 0 < c := by exact_mod_cast h6
    refine ⟨c.toNat, by omega, ?_⟩
    rw [e5]
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) (Int.toNat_of_nonneg h7.le)
  exact gen R.k hk P.u z hanti hz

section Lat

variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def resHom (N : Submodule (𝓞 E) V) : autLat (E := E) N →* Module.End (𝓞 E) N where
  toFun γ := ((γ.1 : V →ₗ[E] V).restrictScalars (𝓞 E)).restrict fun _ hx => autLat_apply γ.2 hx
  map_one' := by ext x; rfl
  map_mul' a b := by ext x; rfl

theorem finrank_red (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (w : Ideal (𝓞 E)) [w.IsMaximal] :
    Module.finrank (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) = Module.finrank E V := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  have : Module.Flat (𝓞 E) N := inferInstance
  have hr : Module.finrank (𝓞 E) N = Module.finrank E V := by
    have : IsLocalizedModule (nonZeroDivisors (𝓞 E)) N.subtype := by
      refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
      · have := isLocalizedModule_id (nonZeroDivisors (𝓞 E)) V E
        exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (LinearMap.id : V →ₗ[𝓞 E] V) s
      · have hy : y ∈ Submodule.span E (N : Set V) := hN.span_eq_top ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
    rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 E)) N.subtype le_rfl,
      IsFractionRing.finrank_right_eq (𝓞 E) E V]
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field _
  have h1 := Module.rankAtStalk_baseChange (R := 𝓞 E) (M := N) (S := 𝓞 E ⧸ w) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank, hr] at h1
  exact h1

theorem card_dvd_card_GL (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (w : Ideal (𝓞 E)) [hw : w.IsMaximal]
    {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hn : Ideal.absNorm w = g)
    (hbig : Module.finrank ℚ E * Module.finrank E V + 1 < g) (Γ : Subgroup (V ≃ₗ[E] V)) [Finite Γ] (hΓ : Γ ≤ autLat N) :
    Nat.card Γ ∣ Nat.card (GL (Fin (Module.finrank E V)) (ZMod g)) := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.IsTorsionFree (𝓞 E) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 E) E V
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 E ⧸ w) = g := by rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w) := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
  letI : Fintype (𝓞 E ⧸ w) := Fintype.ofFinite _
  haveI : NeZero g := ⟨hg.ne_zero⟩
  let e : ZMod g ≃+* 𝓞 E ⧸ w := ZMod.ringEquivOfPrime _ hg (by rw [← hc, Nat.card_eq_fintype_card])
  let b := Module.finBasisOfFinrankEq (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) (finrank_red N hN w)
  let φ : Module.End (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) ≃*
      Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) (ZMod g) :=
    (LinearMap.toMatrixAlgEquiv b).toMulEquiv.trans e.symm.mapMatrix.toMulEquiv
  let ρ : Γ →* Module.End (𝓞 E ⧸ w) ((𝓞 E ⧸ w) ⊗[𝓞 E] N) :=
    ((Module.End.baseChangeHom (𝓞 E) (𝓞 E ⧸ w) N : _ →* _).comp (resHom N)).comp (Subgroup.inclusion hΓ)
  refine Subgroup.card_dvd_of_injective (φ.toMonoidHom.comp ρ).toHomUnits ?_
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have h1 : ρ γ = 1 := φ.injective (by rw [map_one]; exact congrArg Units.val hγ)
  refine Subtype.ext (stab0 hw.ne_top hN.fg hN.span_eq_top hg hgw hbig ⟨hΓ γ.2, 1, fun x hx => ?_⟩
    (Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite γ)))
  have h2 : (1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (resHom N ⟨γ.1, hΓ γ.2⟩ ⟨x, hx⟩) = (1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (⟨x, hx⟩ : N) :=
    LinearMap.congr_fun h1 ((1 : 𝓞 E ⧸ w) ⊗ₜ[𝓞 E] (⟨x, hx⟩ : N))
  have h3 := congrArg (TensorProduct.quotTensorEquivQuotSMul N w) h2
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.eq] at h3
  have h4 := Submodule.mem_map_of_mem (f := N.subtype) h3
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h4
  rw [pow_one]
  exact h4

theorem mass_mul_idx [StarRing E] (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
    (L : Submodule (𝓞 E) V) (hL : Submodule.IsLattice E L) (w : Ideal (𝓞 E)) [hw : w.IsMaximal]
    {g : ℕ} (hg : g.Prime) (hgw : (g : 𝓞 E) ∈ w) (hn : Ideal.absNorm w = g)
    (hbig : Module.finrank ℚ E * Module.finrank E V + 1 < g) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) := by
  obtain ⟨⟨s, hs₀⟩, hm, hp⟩ := Formalism.HermitianLatticesTheory.final_massBasic E V h hs hpos L hL
  obtain ⟨m, hm0, hm1, hm2⟩ := idx_eq g (Module.finrank E V) hg
  have key : ∀ M ∈ s, ((m / Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) = ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ * m := by
    intro M hM
    have hMl := (hs₀.1 M hM).1
    have hfin := Formalism.HermitianLatticesTheory.autFinite E V h hs hpos M hMl
    have : Finite (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V)) := hfin.to_subtype
    have e : Nat.card (Formalism.ThetaLiftIndependence.autL h M) = Nat.card (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V)) := rfl
    have h1 := card_dvd_card_GL M hMl w hg hgw hn hbig (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M) inf_le_right
    have h2 : (Nat.card (Formalism.HermitianLatticesTheory.isom h ⊓ autLat M : Subgroup (V ≃ₗ[E] V))).Coprime g := by
      rw [Nat.coprime_comm, hg.coprime_iff_not_dvd]
      intro hd
      have := prime_le_of_dvd_card _ hg hd
      omega
    rw [hm2] at h1
    have h3 := (h2.pow_right _).dvd_of_dvd_mul_left h1
    rw [e, Nat.cast_div h3 (by exact_mod_cast Nat.card_pos.ne'), div_eq_inv_mul]
  have e : ((∑ M ∈ s, m / Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) := by
    rw [hm s hs₀, ← hm1, Finset.sum_mul, Nat.cast_sum]
    exact Finset.sum_congr rfl key
  refine ⟨_, ?_, e⟩
  have : (0 : ℝ) < Formalism.HermitianLatticesTheory.mass h L * StandardLattice.idxColLoc g (Module.finrank E V) :=
    mul_pos hp (by rw [← hm1]; exact_mod_cast hm0)
  rw [← e] at this
  exact_mod_cast this

end Lat

theorem duStarOf_nat : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (hc : Tau R → HCParam R), (∀ i, H.g i % (H.QS * H.q * H.d) = 1) → (∀ i, 2 * R.f * R.k < H.g i - 1) → ∃ n : ℕ, 0 < n ∧ (n : ℝ) = duStarOf H hc := by
  intro R H hc hmod hbig
  letI := H.cmStar
  have hg := H.g_prime 0
  have hdeg : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
  have hdeg' : Module.finrank ℚ H.E = 2 * R.f := by
    rw [hdeg, show R.f = 2 * R.ord from rfl]; ring
  have hs : SplitsC H.E (H.g 0) := by
    refine splitsC_of_modEq_one R H _ hg ?_
    have := Nat.mod_modEq (H.g 0) (H.QS * H.q * H.d)
    rw [hmod 0] at this
    exact this.symm
  obtain ⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 H.E) | ((H.g 0 : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [show Set.ncard _ = _ from hs]; exact Module.finrank_pos.ne')
  have hn := (splitsC_main R H _ hg hs v hv).1
  haveI := v.isMaximal
  haveI := H.isCMField_hostE
  have hconj : ∀ (φ : H.E →+* ℂ) (x : H.E), φ (star x) = starRingEnd ℂ (φ x) := fun φ x =>
    IsCMField.complexEmbedding_complexConj H.E φ x
  have hsym : (StandardLattice.stdForm H.E R.k).IsSymm := by
    refine LinearMap.isSymm_def.mpr fun x y => ?_
    show starRingEnd H.E (∑ i, star (x i) * y i) = ∑ i, star (y i) * x i
    simp only [map_sum, starRingEnd_apply, star_mul, star_star]
  have hpos : ∀ x : Fin R.k → H.E, x ≠ 0 → 0 < Algebra.trace ℚ H.E (StandardLattice.stdForm H.E R.k x x) := fun x hx => by
    have := hStd_trace_pos hconj x hx
    rw [hStd_apply] at this
    exact this
  have hL : Submodule.IsLattice H.E (StandardLattice.stdLat H.E R.k) := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [StandardLattice.stdLat, Submodule.span_span_of_tower, ← (Pi.basisFun H.E (Fin R.k)).span_eq]
    congr 2
    funext i
    simp
  obtain ⟨n₁, p₁, e₁⟩ := mass_mul_idx _ hsym hpos _ hL v.asIdeal hg hv hn
    (by rw [Module.finrank_fin_fun, hdeg']; have := hbig 0; omega)
  rw [Module.finrank_fin_fun] at e₁
  obtain ⟨n₂, p₂, e₂, -⟩ := idx_eq (H.g 0) R.k hg
  obtain ⟨n₃, p₃, e₃, -⟩ := idx_eq (H.g 1) R.k (H.g_prime 1)
  choose d pd ed using fun τ => dimV_nat (hc τ)
  obtain ⟨f, hf⟩ : ∃ f, R.f = f + 1 := ⟨R.f - 1, by
    have : 0 < R.f := Nat.mul_pos two_pos R.ord_pos
    omega⟩
  refine ⟨n₁ * n₂ ^ f * n₃ ^ R.f * ∏ τ, d τ, ?_, ?_⟩
  · have := Finset.prod_pos (s := Finset.univ) fun τ _ => pd τ
    positivity
  · unfold duStarOf
    push_cast
    simp only [ed]
    rw [e₁, e₂, e₃, hf]
    ring

end GlobalTheory.Mem.DuInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyCoeffCongrSamePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_coeff_congr_same_place_alt : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := by
  first | exact @GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place | exact GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place | (intros; apply GlobalTheory.HeightCounting.charpoly_coeff_congr_same_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnMinorProductsFockReproducingDualWeylStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnMinorProducts_fock_reproducing_dualWeyl : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (f : MvPolynomial (Fin N × Fin N) ℚ),
    f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r) →
    ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f := by
  first | exact @GlobalTheory.WeylReproducingSym.reproducing_left | exact GlobalTheory.WeylReproducingSym.reproducing_left | (intros; apply GlobalTheory.WeylReproducingSym.reproducing_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensionalStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexForms_finiteDimensional : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → FiniteDimensional ℂ (S.Fi emb σ lam) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | exact GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | (intros; apply GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional <;> assumption)
end

