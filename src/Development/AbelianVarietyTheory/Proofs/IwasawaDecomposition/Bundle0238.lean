import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockActionsIsHolomorphicProductKRepFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldHeckeCharacterSqrtNormValues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BVal

open Formalism.L2.Host
open scoped nonZeroDivisors

section General

variable {L : Type} [Field L] [NumberField L]

theorem onId_mul (χ : HChar L) {I J : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0) :
    χ.onId (I * J) = χ.onId I * χ.onId J := by
  have hf : ∀ K : FractionalIdeal (𝓞 L)⁰ L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v K).Finite := fun K => by
    refine (FractionalIdeal.finite_factors (K := L) K).subset fun v hv h => hv ?_
    have h' : FractionalIdeal.count L v K = 0 := h
    simp [h']
  unfold HChar.onId
  rw [← finprod_mul_distrib (hf I) (hf J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul L v hI hJ, _root_.zpow_add]

theorem onId_one (χ : HChar L) : χ.onId 1 = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]

theorem onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v fun w hw => by rw [FractionalIdeal.count_maximal_coprime L w hw.symm, zpow_zero],
    FractionalIdeal.count_self, zpow_one]

theorem mem_of_primes (χ : HChar L) (M : IntermediateField ℚ ℂ) (b : 𝓞 L)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), b ∉ v.asIdeal →
      ((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M)
    (cc : Ideal (𝓞 L)) (h0 : cc ≠ ⊥) (h1 : cc ⊔ Ideal.span {b} = ⊤) :
    ((χ.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) ∈ M := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h0
  | h₂ x hx =>
    obtain rfl : x = ⊤ := Ideal.isUnit_iff.1 hx
    simp [onId_one]
  | h₃ a p ha hp ih =>
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hb : b ∉ v.asIdeal := fun hb => v.isPrime.ne_top
      (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))
    have ha1 : a ⊔ Ideal.span {b} = ⊤ := top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))
    have := mul_mem (h v hb) (ih ha ha1)
    rw [FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      show χ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = χ.val v from onId_prime χ v]
    convert this using 1
    push_cast
    ring

theorem val_mul_sqrt (α β γ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (((α * β * γ⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) =
      α.valTw 0 v * β.valTw 0 v * (γ.valTw (1 / 2) v)⁻¹ := by
  have e : (α * β * γ⁻¹).val v = α.val v * β.val v * (γ.val v)⁻¹ := rfl
  have e2 : ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [e, e2]
  simp only [HChar.valTw, Complex.cpow_neg, Complex.ofReal_zero, Complex.cpow_zero, inv_one, mul_one, mul_inv, inv_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]

end General

theorem exists_field_BIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T0), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (M' : IntermediateField ℚ ℂ), M ≤ M' → ∀ bad : ℕ, D.host.g 0 * D.host.g 1 ∣ bad → (∀ PP ∈ R.Q t, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ B : Ideal (𝓞 D.host.E) → M', BIs R i M'.val.toRingHom t bad B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i t
  obtain ⟨M₁, hM₁, -, -, hmu, heta, -⟩ := GlobalTheory.Mem.FrameVal.frame_values D.R D.host (eExp D)
    ⟨R.C.P, R.C.W, R.C.mu0, R.C.eta, R.C.chiPsi, R.C.del, R.C.del', R.C.isMu0, R.C.isEta, R.C.isChi, R.C.isDel, R.C.isDel'⟩
    fun j τ => (D.hc _).e_int j
  obtain ⟨M₂, hM₂, hxi⟩ := GlobalTheory.Mem.FrameVal.exists_of_order (hL.xi_fin t)
  refine ⟨M₁ ⊔ M₂, inferInstance, fun M' hM bad hg hQ => ?_⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M' := by
    intro v hv
    have u1 : (R.C.mu0 i).UnrAt v := (R.C.isMu0 i).unr v fun k hk => hv (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hk
      have hd : D.host.g k ∣ bad := by
        refine dvd_trans ?_ hg
        fin_cases k
        · exact dvd_mul_right _ _
        · exact dvd_mul_left _ _
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hk')
    have u2 : (R.xiH t).UnrAt v := by
      by_contra h
      rcases (hL.Q_ram t v).1 h with h | ⟨P', hP', h⟩
      · exact hv (hQ v h)
      · obtain ⟨c', hc', e⟩ := h _ (hQ P' hP')
        have e' : c' = (bad : 𝓞 D.host.E) := RingOfIntegers.ext (by
          rw [e]
          change star ((bad : 𝓞 D.host.E) : D.host.E) = ((bad : 𝓞 D.host.E) : D.host.E)
          rw [show ((bad : 𝓞 D.host.E) : D.host.E) = (bad : D.host.E) from
            map_natCast (algebraMap (𝓞 D.host.E) D.host.E) bad, star_natCast])
        exact hv (e' ▸ hc')
    obtain ⟨y1, hy1⟩ := hmu i v u1
    obtain ⟨y2, hy2⟩ := hxi v u2
    obtain ⟨y3, hy3⟩ := heta v (R.C.isEta.unr v)
    rw [val_mul_sqrt, ← hy1, ← hy2, ← hy3]
    exact mul_mem (mul_mem (hM (le_sup_left (b := M₂) y1.2)) (hM (le_sup_right (a := M₁) y2.2)))
      (inv_mem (hM (le_sup_left (b := M₂) y3.2)))
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, mem_of_primes _ M' _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl

end GlobalTheory.Mem.BVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
section
noncomputable section

namespace GlobalTheory.AdelicFrame

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idem_adele (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ Formalism.UG.intAd F, f * f = f ∧ (∃ w ∈ Formalism.UG.intAd F, f = (m : FiniteAdeleRing (𝓞 F) F) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ Formalism.UG.intAd F, 1 - f = (n : FiniteAdeleRing (𝓞 F) F) * w := by
  obtain ⟨h1, h2⟩ := integral_finiteAdele_complete_separated F
  refine GlobalTheory.IdealIdele.exists_idem (Formalism.UG.intAd F) (fun y hy => h1 y fun N hN => ?_) (fun x hx hc => ?_) m hm
  · obtain ⟨w, hw, e⟩ := hy N hN
    exact ⟨w, hw, by rw [nsmul_eq_mul]; exact e⟩
  · obtain ⟨y, hy⟩ := h2 x hx fun N k hN hk => by
      obtain ⟨w, hw, e⟩ := hc N k hN hk
      exact ⟨w, hw, by rw [nsmul_eq_mul]; exact e⟩
    refine ⟨y, ?_, fun N hN => ?_⟩
    · obtain ⟨a, ha, e⟩ := hy 1 one_pos
      rw [e, one_smul]
      exact add_mem (hx 1) ha
    · obtain ⟨a, ha, e⟩ := hy N hN
      exact ⟨a, ha, by rw [← nsmul_eq_mul]; exact e⟩

theorem exists_generator_int (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ y y' : RA F E, y * y' = 1 ∧ y ∈ hat1 F ((B : FractionalIdeal (𝓞 E)⁰ E) : Set E) ∧
      y' ∈ hat1 F (((B : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := GlobalTheory.IdealIdele.exists_local_generator B hB
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem_adele F m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hβE : (β : E) ≠ 0 := by simpa using hβ0
  have hnat : ∀ (k : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : E),
      ((k : FiniteAdeleRing (𝓞 F) F) * a) ⊗ₜ[F] x = a ⊗ₜ[F] ((k : E) * x) := by
    intro k a x
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F,
      TensorProduct.smul_tmul]
  refine ⟨(1 - f) ⊗ₜ (β : E) + f ⊗ₜ 1, (1 - f) ⊗ₜ (β : E)⁻¹ + f ⊗ₜ 1, ?_, add_mem ?_ ?_, ?_⟩
  · have e1 : (1 - f) * (1 - f) = 1 - f := by linear_combination hff
    have e2 : (1 - f) * f = 0 := by linear_combination -hff
    have e3 : f * (1 - f) = 0 := by linear_combination -hff
    simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, e1, e2, e3, hff, TensorProduct.zero_tmul,
      mul_inv_cancel₀ hβE, mul_one, add_zero, zero_add]
    rw [← TensorProduct.add_tmul, sub_add_cancel, Algebra.TensorProduct.one_def]
  · exact tmul_mem_adelicCompletion_of_integral F (sub_mem (one_mem _) hf : _ ∈ Formalism.UG.intAd F)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hβB)
  · rw [hfw, hnat, mul_one]
    refine tmul_mem_adelicCompletion_of_integral F hw ?_
    have := FractionalIdeal.mem_coeIdeal_of_mem (P := E) (𝓞 E)⁰ hmB
    rwa [map_natCast] at this
  · have := mem_adelicCompletion_mul_inv_fractionalIdeal F (B : FractionalIdeal (𝓞 E)⁰ E) 1 ((1 - f) ⊗ₜ (β : E)⁻¹ + f ⊗ₜ 1)
      (FractionalIdeal.coeIdeal_ne_zero.2 hB) fun x hx => by
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        obtain ⟨d, hd⟩ := hdvd b hb
        have hd' : (n : E) * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E β * algebraMap (𝓞 E) E d := by
          rw [← map_mul, ← hd, map_mul, map_natCast]
        simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        refine add_mem ?_ (tmul_mem_adelicCompletion_of_integral F hf ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩))
        rw [hfv, hnat]
        refine tmul_mem_adelicCompletion_of_integral F hv ((FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩)
        rw [mul_left_comm, hd']
        exact (inv_mul_cancel_left₀ hβE _).symm
    rwa [one_mul] at this

theorem exists_generator (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) :
    ∃ y y' : RA F E, y * y' = 1 ∧ y ∈ hat1 F (I : Set E) ∧
      y' ∈ hat1 F ((I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨a, B, ha, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hB : B ≠ ⊥ := by
    rintro rfl
    simp at hI
  have haE : algebraMap (𝓞 E) E a ≠ 0 := by simpa using ha
  obtain ⟨y, y', h, hy, hy'⟩ := exists_generator_int F B hB
  refine ⟨(1 ⊗ₜ (algebraMap (𝓞 E) E a)⁻¹) * y, (1 ⊗ₜ (algebraMap (𝓞 E) E a)) * y', ?_, ?_, ?_⟩
  · rw [mul_mul_mul_comm, h, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ haE, mul_one, mul_one,
      Algebra.TensorProduct.one_def]
  · exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_spanSingleton_self _ _)) _ hy
  · rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
    exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_spanSingleton_self _ _)) _ hy'

theorem mem_integral_adelic_lattice_iff (z : RA F E) :
    z ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) ↔
      Algebra.TensorProduct.comm F _ E z ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      have h1 : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ Formalism.L2.Herm.intAf F E :=
        Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
      have := mul_mem h1 h2
      rwa [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at this
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ t ∈ Formalism.L2.Herm.intAf F E, (Algebra.TensorProduct.comm F _ E).symm t ∈
        hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
      intro t ht
      induction ht using Subring.closure_induction with
      | mem z hz =>
        rcases hz with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩
        · exact one_tmul_mem_adelicCompletionOfElementSet F ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
        · exact tmul_mem_adelicCompletion_of_integral F b.2 (FractionalIdeal.one_mem_one _)
      | zero => rw [map_zero]; exact zero_mem _
      | one => rw [map_one]; exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb =>
        rw [map_mul]
        have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ ha _ hb
        rwa [mul_one] at this
    simpa only [AlgEquiv.symm_apply_apply] using key _ hz

theorem exists_basis_hat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ P Q : Matrix (Fin n) (Fin n) (RA F E), P * Q = 1 ∧ Q * P = 1 ∧ ∀ z, z ∈ hat F (L : Set (Fin n → E)) ↔
      ∀ a, (Q *ᵥ z) a ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  choose y y' hyy hy hy' using fun a => exists_generator F (cI a) (hc a)
  have hD : Matrix.diagonal y * Matrix.diagonal y' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact hyy a
  have h1 : P * Matrix.diagonal y * (Matrix.diagonal y' * Q) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ Q, hD, Matrix.one_mul, hPQ]
  refine ⟨_, _, h1, mul_eq_one_comm.1 h1, fun z => ?_⟩
  have hz : z = P *ᵥ (Q *ᵥ z) := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  conv_lhs => rw [hz, hP, key]
  refine forall_congr' fun a => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  constructor
  · intro h
    have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy' a) _ h
    rwa [inv_mul_cancel₀ (hc a)] at this
  · intro h
    have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy a) _ h
    rwa [mul_one, ← mul_assoc, hyy, one_mul] at this

theorem exists_isFrame {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), Formalism.L2.DIV.IsFrame β L := by
  obtain ⟨P, Q, hPQ, hQP, h⟩ := exists_basis_hat F L hfg hsp
  let s := Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E
  have hm : ∀ A B : Matrix (Fin n) (Fin n) (RA F E), A * B = 1 → A.map s * B.map s = 1 := fun A B hAB => by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨P.map s, Q.map s, hm _ _ hPQ, hm _ _ hQP⟩, fun x => ?_⟩
  have e : ∀ i, (Q.map s *ᵥ x) i = s ((Q *ᵥ fun j => s.symm (x j)) i) := fun i => by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply, Matrix.map_apply]
  change _ ↔ ∀ i, (Q.map s *ᵥ x) i ∈ _
  simp only [e]
  constructor
  · intro hx i
    exact (mem_integral_adelic_lattice_iff F _).1 ((h _).1 (GlobalTheory.PrincInLevel.swap_symm_mem_hat L x hx) i)
  · intro hx
    have := GlobalTheory.PrincInLevel.swap_mem_hatL L _ ((h _).2 fun i => (mem_integral_adelic_lattice_iff F _).2 (hx i))
    simpa only [s, AlgEquiv.apply_symm_apply] using this

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isSDFrame : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∃ β, IsSDFrame V β Λ 1 := by
  intro D V Λ hΛ hd
  have hl : Λ = GlobalTheory.Member.latC V := SetLike.coe_injective (hΛ.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  have hfg : Λ.FG := hl ▸ V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have h1 : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := by
      rw [hl]; rfl
    rw [h1, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  obtain ⟨β, hβ⟩ := exists_isFrame D.host.F Λ hfg hsp
  refine ⟨β, 0, hβ, hd, one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_zero, Nat.cast_one, one_smul]
    rw [← hΛ] at hx
    exact hx
  · rw [pow_zero, Nat.cast_one, one_smul, ← hΛ]
    exact hx

end GlobalTheory.AdelicFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_normalizedHaarMeasure_adelicUnitary : ∀ (D : D7) (V : HSp D), V.SigOK → ∃! μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  first | exact @GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG | exact GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG | (intros; apply GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.UnitN

theorem exists_unit_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ]
    {K : Set G} (hK : IsCompact K) (hcov : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) :
    ∃ (ν : Measure G) (𝓝 : Set G), ν.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓝 ν ∧ ν 𝓝 = 1 := by
  let μ : Measure G := Measure.haar
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain Γ μ
  have hle : μ 𝓕 ≤ μ K := by
    rw [h.measure_eq_tsum K]
    refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hK.measure_lt_top).ne
  have hpos : μ 𝓕 ≠ 0 := h.measure_ne_zero (NeZero.ne μ)
  refine ⟨(μ 𝓕)⁻¹ • μ, 𝓕, Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 hpos),
    h.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]

theorem exists_isUnitN : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e →
    ∃ ν 𝓝, GlobalTheory.Per.IsUnitN B e ν 𝓝 := by
  intro D B ρ e he
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcl : IsClosed (NFlag B e : Set (GA D B)) := by
    have : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
      DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
    have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
    have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
    convert h2 using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  have : LocallyCompactSpace (NFlag B e) := hcl.locallyCompactSpace
  have : SecondCountableTopology (NFlag B e) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))
  have : Countable (NFlagQ B e) := hinj.countable
  have : DiscreteTopology (NFlagQ B e) :=
    DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  exact exists_unit_of_cocompact (NFlagQ B e) hK h

end GlobalTheory.Per.UnitN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic : ∀ D : D7, ∃ χ : IdC D, IsHeckeChar D χ ∧ (∀ τ, HasInfExp D χ τ (1 / 2)) ∧ ResEta D χ 1 ∧ UnramEverywhere D χ := by
  first | exact @GlobalTheory.Mem.EtaTilde.exists_etaTilde | exact GlobalTheory.Mem.EtaTilde.exists_etaTilde | (intros; apply GlobalTheory.Mem.EtaTilde.exists_etaTilde <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasureInvariantSupportedOrbitNeZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreMeasure_invariant_supported_orbit_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → FibAt R σ J (tupMeas lam 1 M) ν (algebraMap F R β) m → IsInvTup R σ J m ∧ OnOrbit R σ J x m ∧ m ≠ 0 := by
  first | exact @GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero | exact GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero | (intros; apply GlobalTheory.GaugeEx.FibProp.fibre_invariant_orbit_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfLevel
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory.LevelForms

theorem finiteDimensional_of_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ (GQ L n) W) (N : ℕ), 0 < N →
    ∀ S : Submodule ℂ (GAf L n → W), (∀ f ∈ S, f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) →
    FiniteDimensional ℂ S := by
  intro L _ _ _ n W _ _ _ ρ N hN S hS
  haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
  refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n ρ N) fun f hf => ?_
  exact ⟨(hS f hf).1.1, fun κ hκ g => congrFun ((hS f hf).2 κ hκ) g⟩

end GlobalTheory.LevelForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockActionsIsHolomorphicProductKRepFamilyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockActions_isHolomorphicProductKRepFamily : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), IsHolFam ε fockL (factK n ε x₁ x₂ x₃) ∧ IsHolFam (fun _ => allPos n) fockL (factU (n := n) ε x₁ x₂ x₃) := by
  first | exact @GlobalTheory.FockHol.main | exact GlobalTheory.FockHol.main | (intros; apply GlobalTheory.FockHol.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeterssonNormSqPosAutomorphicFunctionUnitaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_normSq_pos_automorphicFunction_unitary : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsQuot V μ 𝓕 → ∀ φ, IsAutFun V φ → φ ≠ 0 → IntegrableOn (fun h => star (φ h) * φ h) 𝓕 μ → 0 < (∫ h in 𝓕, star (φ h) * φ h ∂μ).re := by
  first | exact @GlobalTheory.Mem.PetPos.petersson_pos | exact GlobalTheory.Mem.PetPos.petersson_pos | (intros; apply GlobalTheory.Mem.PetPos.petersson_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.QuotVol

theorem quot_volume_ne_zero_ne_top : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    IsQuot V μ 𝓕 → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ := fun D V μ 𝓕 h =>
  ⟨((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram μ h.1).2
      𝓕 𝓕 h.2 h.2).2,
    (GlobalTheory.Mem.VolFin.finVol D.host.F D.host.E D.sp.cm.sig (GlobalTheory.Mem.VolExists.isCMExt D.sp.cm) V.rank V.gram
      (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) μ h.1 𝓕 h.2).ne⟩

end GlobalTheory.Mem.QuotVol
end

