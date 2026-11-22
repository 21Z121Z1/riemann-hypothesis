import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0091
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PClosedPtGenUniform
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter.AvoidRing (isMultiHomog_mul isMultiHomog_pow)

noncomputable section

namespace ClosedPtGenUniform

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

theorem genNear_of_mul_eq_pow {d : K → ℤ} {a q b : MRingOver S ι} {α β δ : K → ℕ} {m : ℕ}
    (h : GenNear S ι 𝓜 d a α) (hq : IsMultiHomog q β) (hab : a * q = b ^ m) (hdeg : m • δ = α + β) :
    GenNear S ι 𝓜 d b δ := by
  intro I x hx
  obtain ⟨n, t, c, r, p, z, ht, htc, hp, hz, he⟩ := h I x hx
  refine ⟨m * n, t, c, r, fun j => q ^ n * p j, z, ht, htc, fun j => ?_, hz, ?_⟩
  · have h' := isMultiHomog_mul (isMultiHomog_pow hq n) (hp j)
    convert h' using 1
    funext k
    have hk := congrFun hdeg k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [mul_comm m n, mul_assoc, hk]
    ring
  · rw [pow_mul, ← hab, mul_pow, show a ^ n * q ^ n * t = q ^ n * (a ^ n * t) by ring, mul_smul, he,
      Finset.smul_sum]
    simp_rw [mul_smul]

theorem genNear_mul_pow (hM : GenNearMul.Statement) (hgr : KH.IsMGraded S ι 𝓜) {W : Ideal (MRingOver S ι)}
    (hW : W ≤ Module.annihilator (MRingOver S ι) M) {d n : K → ℤ} {f g : MRingOver S ι} {δ γ : K → ℕ}
    (hf : IsMultiHomog f δ) (hg : IsMultiHomog g γ) (hfd : GenNear S ι 𝓜 d f δ)
    (hgn : GenNear S ι (KH.quotPart S W) n g γ) :
    ∀ a : ℕ, GenNear S ι 𝓜 (d + a • n) (f * g ^ a) (δ + a • γ) := by
  intro a
  induction a with
  | zero => simpa using hfd
  | succ a ih =>
    have h' := hM S K ι M 𝓜 W (d + a • n) n (f * g ^ a) g (δ + a • γ) γ hgr hW
      (isMultiHomog_mul hf (isMultiHomog_pow hg a)) hg ih hgn
    rw [succ_nsmul, succ_nsmul, pow_succ, ← mul_assoc, ← add_assoc, ← add_assoc]
    exact h'

end ClosedPtGenUniform

open ClosedPtGenUniform in

theorem ClosedPtGenUniform.proof (hG : GradedSubmodules.Statement) (hF : ClosedPtFibreLift.Statement)
    (hN : ChartNakayamaGen.Statement) (hM : GenNearMul.Statement) : ClosedPtGenUniform.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e P hP
  classical
  obtain ⟨hPprime, hPhom, hPrel⟩ := hP.1
  choose i hi using hPrel

  let I : KH.Cell K ι 0 := ⟨fun k => {i k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hI : ∀ k, ∀ j ∈ I.1 k, (X ⟨k, j⟩ : MRingOver S ι) ∉ P := by
    intro k j hj
    rw [Finset.mem_singleton.mp hj]
    exact hi k
  have : IsNoetherianRing (MRingOver S ι) := inferInstance

  obtain ⟨hWhom, hMsub⟩ := hG S K ι M 𝓜 hgr
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVPM : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) M) :=
    hV.trans (LinearMap.annihilator_le_of_injective (P • ⊤ : Submodule (MRingOver S ι) M).subtype
      (P • ⊤ : Submodule (MRingOver S ι) M).injective_subtype)
  obtain ⟨cM, hcM⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) M) (subGrading 𝓜 (P • ⊤)) inferInstance
    (hMsub P hPhom).1 hVPM e
  obtain ⟨fM, δM, hfM, hfMP, hgenM⟩ := hN S K ι M 𝓜 P (e + cM • N) hS hfin hgr hPprime hPhom I hI
    (hF S K ι M 𝓜 P (e + cM • N) hS hfin hgr hP (hcM cM le_rfl) I hI)

  set W := Module.annihilator (MRingOver S ι) M with hWdef
  have hWgr : KH.IsMGraded S ι (KH.quotPart S W) := QuotPartGraded.proof S K ι W hWhom
  have hQfin : Module.Finite (MRingOver S ι) (MRingOver S ι ⧸ W) := inferInstance
  obtain ⟨-, hQsub⟩ := hG S K ι (MRingOver S ι ⧸ W) (KH.quotPart S W) hWgr
  have : IsNoetherian (MRingOver S ι) (MRingOver S ι ⧸ W) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have hVQ : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ W) := by
    rw [Ideal.annihilator_quotient]
    exact hV
  have hVPQ : V ≤ Module.annihilator (MRingOver S ι) (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)) :=
    hVQ.trans (LinearMap.annihilator_le_of_injective
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).subtype
      (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W)).injective_subtype)
  obtain ⟨cO, hcO⟩ := hH (P • ⊤ : Submodule (MRingOver S ι) (MRingOver S ι ⧸ W))
    (subGrading (KH.quotPart S W) (P • ⊤)) inferInstance (hQsub P hPhom).1 hVPQ 0
  have hgenO : ∀ n : ℕ, cO ≤ n → ∃ (g : MRingOver S ι) (γ : K → ℕ), IsMultiHomog g γ ∧ g ∉ P ∧
      GenNear S ι (KH.quotPart S W) (0 + n • N) g γ := fun n hn =>
    hN S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hPprime hPhom I hI
      (hF S K ι _ (KH.quotPart S W) P (0 + n • N) hS hQfin hWgr hP (hcO n hn) I hI)
  set n₁ := cO + 1 with hn₁
  obtain ⟨g₁, γ₁, hg₁, hg₁P, hgen₁⟩ := hgenO n₁ (by omega)
  obtain ⟨g₂, γ₂, hg₂, hg₂P, hgen₂⟩ := hgenO (n₁ + 1) (by omega)

  refine ⟨fM * g₁ * g₂, δM + γ₁ + γ₂, cM + n₁ * n₁, isMultiHomog_mul (isMultiHomog_mul hfM hg₁) hg₂, ?_, ?_⟩
  · intro hmem
    rcases hPprime.mem_or_mem hmem with h | h
    · rcases hPprime.mem_or_mem h with h | h
      · exact hfMP h
      · exact hg₁P h
    · exact hg₂P h
  intro c hc
  have hpos : 0 < n₁ := by omega
  set q := (c - cM) / n₁ with hq
  set s := (c - cM) % n₁ with hs
  have hdm : n₁ * q + s = c - cM := Nat.div_add_mod (c - cM) n₁
  have hsn : s < n₁ := Nat.mod_lt _ hpos
  have hqn : n₁ ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hpos]
    omega
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (le_trans hsn.le hqn)
  have hca : c = cM + a * n₁ + s * (n₁ + 1) := by
    have h1 : c - cM + cM = c := Nat.sub_add_cancel (by omega)
    rw [← h1, ← hdm, ha]
    ring
  have hA := genNear_mul_pow hM hgr le_rfl hfM hg₁ hgenM hgen₁ a
  have hB := genNear_mul_pow hM hgr le_rfl (isMultiHomog_mul hfM (isMultiHomog_pow hg₁ a)) hg₂ hA hgen₂ s
  have htw : e + cM • N + a • (0 + n₁ • N) + s • (0 + (n₁ + 1) • N) = e + c • N := by
    rw [hca]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]
    push_cast
    ring
  rw [htw] at hB
  refine genNear_of_mul_eq_pow hB
    (isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_pow hfM (a + s)) (isMultiHomog_pow hg₁ (s + 1)))
      (isMultiHomog_pow hg₂ (a + 1))) (m := a + s + 1) (by ring) ?_
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreRepresentatives

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem isMultiHomog_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {f : MRingOver R ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (map φ f : MRingOver S ι) a :=
  fun m hm => hf m (support_map_subset φ f hm)

omit [Fintype K] in

theorem isMultiHomog_lincomb {f g : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) (c d : ℂ) : IsMultiHomog (C c * f - C d * g) a := by
  classical
  intro m hm
  rw [C_mul', C_mul'] at hm
  rcases Finset.mem_union.1 (support_sub _ _ _ hm) with h | h
  · exact hf m (support_smul h)
  · exact hg m (support_smul h)

theorem eval_smul {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) (r : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : eval (fun p => r p.1 * z p) s = (∏ k, r k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ p : (Σ k, ι k), r p.1 ^ d p) = ∏ k, r k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, r k ^ d ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem eval_eq_zero_of_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, (∃ a, IsMultiHomog f a) → eval z (map (Int.castRingHom ℂ) f) = 0)
    (f : MRing ι) (hf : f ∈ mCoordIdeal y) : eval z (map (Int.castRingHom ℂ) f) = 0 := by
  rw [eq_sum_multihomogeneous_components f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun b _ => hz _ ?_ ⟨b, isMultiHomog_i2comp b f⟩
  exact i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal y) b hf

end FibreRepresentatives

open FibreRepresentatives in

theorem FibreRepresentatives.proof (h : AvoidFormFinite.Statement) : FibreRepresentatives.Statement := by
  intro K _ ι _ Ω _ y D e L he hL hL0 ζ
  classical
  set Lc : Fin (D + 1) → MRingOver ℂ ι := fun j => map (Int.castRingHom ℂ) (L j) with hLc
  by_cases hζ : ζ = 0
  · refine ⟨∅, by simp, fun z hz ⟨t, ht⟩ => ?_⟩
    obtain ⟨j, hj⟩ := hL0 z hz
    exact absurd (by simpa [hζ] using ht j) hj
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ζ j₀ ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hζ (funext hne)
  let S : Set (MRingOver ℂ ι) :=
    {g | ∃ f ∈ mCoordIdeal y, (∃ a, IsMultiHomog f a) ∧ g = map (Int.castRingHom ℂ) f} ∪
      Set.range fun j => C (ζ j₀) * Lc j - C (ζ j) * Lc j₀

  have key : ∀ z : (Σ k, ι k) → ℂ, ((∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval z s = 0) ↔
      (z ∈ mcPts (mCoordIdeal y) ∧ ∃ t : ℂ, ∀ j, eval z (Lc j) = t * ζ j) := by
    intro z
    constructor
    · rintro ⟨hb, hS⟩
      refine ⟨⟨hb, eval_eq_zero_of_homog y z fun f hf ha => hS _ (Or.inl ⟨f, hf, ha, rfl⟩)⟩,
        eval z (Lc j₀) / ζ j₀, fun j => ?_⟩
      have h1 := hS _ (Or.inr ⟨j, rfl⟩)
      simp only [map_sub, map_mul, eval_C] at h1
      field_simp
      linear_combination h1
    · rintro ⟨hz, t, ht⟩
      refine ⟨hz.1, fun s hs => ?_⟩
      rcases hs with ⟨f, hf, -, rfl⟩ | ⟨j, rfl⟩
      · exact hz.2 f hf
      · simp only [map_sub, map_mul, eval_C, ht]
        ring
  have hSh : ∀ s ∈ S, ∃ a, IsMultiHomog s a := by
    rintro s (⟨f, -, ⟨a, ha⟩, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨a, isMultiHomog_map _ ha⟩
    · exact ⟨e, isMultiHomog_lincomb (isMultiHomog_map _ (hL j)) (isMultiHomog_map _ (hL j₀)) _ _⟩
  have hG : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) →
      eval z (Lc j₀) ≠ 0 := by
    intro z hb hS h0
    obtain ⟨hz, t, ht⟩ := (key z).1 ⟨hb, hS⟩
    have ht0 : t = 0 := by
      have := ht j₀
      rw [h0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hj₀
    obtain ⟨j, hj⟩ := hL0 z hz
    exact hj (by simpa [hLc, ht0] using ht j)
  obtain ⟨T, hT⟩ := h K ι S (Lc j₀) e he (isMultiHomog_map _ (hL j₀)) hSh hG
  refine ⟨T.filter fun t => (∀ k, ∃ i, t ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval t s = 0, fun z hz => ?_,
    fun z hz hfib => ?_⟩
  · exact (key z).1 (Finset.mem_filter.1 hz).2
  · obtain ⟨hb, hS⟩ := (key z).2 ⟨hz, hfib⟩
    obtain ⟨t, htT, r, hr, rfl⟩ := hT z hb hS
    have hinv : t = fun p => (r p.1)⁻¹ * (r p.1 * t p) := by
      funext p
      rw [← mul_assoc, inv_mul_cancel₀ (hr p.1), one_mul]
    refine ⟨t, Finset.mem_filter.2 ⟨htT, fun k => ?_, fun s hs => ?_⟩, r, hr, rfl⟩
    · obtain ⟨i, hi⟩ := hb k
      exact ⟨i, fun h0 => hi (by simp [h0])⟩
    · obtain ⟨a, ha⟩ := hSh s hs
      rw [hinv, eval_smul ha (fun k => (r k)⁻¹), hS s hs, mul_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreSectionLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

set_option maxHeartbeats 1000000 in

theorem FibreSectionLift.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hsq : KH.CechDSqStatement) (hdg : KH.CechDDegStatement) (hR : ReductionComplex.Statement)
    (hZ : ZeroCocycleSection.Statement) (hC : SecCochReduce.Statement) : FibreSectionLift.Statement := by
  intro K _ _ ι _ _ Ω _ y D p a hV hp hH1
  have hH1' : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) := hH1
  show ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 0,
    ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y (ZMod p) s a = z
  intro z hz'

  let instC : ∀ n : ℕ, Module ℤ (KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) := fun n =>
    (fun {A : Type} {_ : AddCommMonoid A} {i : Module ℤ A} (_ : Submodule ℤ A) => i)
      (KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n)
  let instZ : Module ℤ (KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := Submodule.module _
  let instCp : ∀ n : ℕ, Module (ZMod p) (KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n) :=
    fun n => (fun {A : Type} {_ : AddCommMonoid A} {i : Module (ZMod p) A} (_ : Submodule (ZMod p) A) => i)
      (KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n)
  let instZp : Module (ZMod p) (KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) :=
    Submodule.module _
  let instH : Module ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) :=
    Submodule.Quotient.module _
  obtain ⟨hd, hrd, hon, hker₀, hnzd₀, hkill₀⟩ := hR K ι Ω y D p a hV hp

  have hker : ∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w' := by
    intro n w hw h0
    obtain ⟨w', h1, h2⟩ := hker₀ n w hw h0
    exact ⟨w', h1, by convert h2 using 2⟩
  have hnzd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      (p : ℤ) • w = 0 → w = 0 := fun n w h => hnzd₀ n w (by convert h using 2)
  have hkill : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0 := fun n w => by convert hkill₀ n w using 3
  have hgr : KH.IsMGraded ℤ ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) :=
    hG ℤ K ι _ (by rw [FibreReduction.idealOver_int]; exact hV.2.1.2.1)
  have hfin : Module.Finite ℤ (KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) := by
    exact (hS ℤ K ι _ _ inferInstance inferInstance hgr).1 a 1
  have dd : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ (n + 1) (KH.cechD ℤ ι _ n w) = 0 := fun n w =>
    LinearMap.congr_fun (hsq ℤ K ι _ n) w
  have dsmul : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      KH.cechD ℤ ι _ n ((p : ℤ) • w) = (p : ℤ) • KH.cechD ℤ ι _ n w := fun n w =>
    map_zsmul (KH.cechD ℤ ι _ n).toAddMonoidHom (p : ℤ) w
  have memZ : ∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n → KH.cechD ℤ ι _ n w = 0 →
        w ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n := fun n w hC hD =>
    Submodule.mem_inf.mpr ⟨hC, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hD⟩

  let f : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 →ₗ[ℤ]
      KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1 := LinearMap.lsmul ℤ _ (p : ℤ)
  have hq : ∀ x : KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1,
      f (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((p : ℤ) • x) := fun x => by
    rw [LinearMap.lsmul_apply, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, map_zsmul]
    exact int_smul_eq_zsmul instH (p : ℤ) _
  have hsurj : Function.Surjective f := by
    intro h
    induction h using Submodule.Quotient.induction_on with
    | H x =>
    have hx := Submodule.mem_inf.mp x.2
    have hxd : KH.cechD ℤ ι _ 1 x.1 = 0 := by
      have := hx.2
      rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
    have hrx : FibreReduction.redCoch y p 1 x.1 ∈
        KH.cechZc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1 :=
      Submodule.mem_inf.mpr ⟨hrd 1 _ hx.1, by
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, ← hd, hxd, map_zero]⟩
    have h0' : (Submodule.Quotient.mk ⟨_, hrx⟩ :
        KH.cechHc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a 1) = 0 := Subsingleton.elim _ _
    have h0 := (Submodule.Quotient.mk_eq_zero _).mp h0'
    obtain ⟨u, hu, hdu⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp h0)
    obtain ⟨u', hu', hru'⟩ := hon 0 u hu
    have hdu' := hdg ℤ K ι _ _ a 0 u' hu'
    obtain ⟨x', hx'C, hx'eq⟩ := hker 1 (x.1 - KH.cechD ℤ ι _ 0 u') (sub_mem hx.1 hdu') (by
      rw [map_sub, hd, hru']
      exact sub_eq_zero.mpr hdu.symm)
    have hx'Z := memZ 1 x' hx'C (hnzd 2 _ (by rw [← dsmul, ← hx'eq, map_sub, hxd, dd, sub_self]))
    refine ⟨Submodule.Quotient.mk ⟨x', hx'Z⟩, ?_⟩
    rw [hq, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, map_zsmul]
    refine Submodule.mem_map.mpr ⟨-u', neg_mem hu', ?_⟩
    rw [LinearMap.restrictScalars_apply, map_neg, Submodule.subtype_apply, Submodule.subtype_apply]
    show _ = (p : ℤ) • x' - x.1
    rw [← hx'eq]
    abel
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hsurj

  obtain ⟨w, hwC, hrw⟩ := hon 0 z (Submodule.mem_inf.mp hz').1
  have hzd : KH.cechD (ZMod p) ι _ 0 z = 0 := by
    have := (Submodule.mem_inf.mp hz').2
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker] at this
  obtain ⟨w', hw'C, hw'eq⟩ := hker 1 _ (hdg ℤ K ι _ _ a 0 w hwC) (by rw [hd, hrw, hzd])
  have hw'Z := memZ 1 w' hw'C (hnzd 2 _ (by rw [← dsmul, ← hw'eq, dd]))
  have hcls : (Submodule.Quotient.mk ⟨w', hw'Z⟩ : KH.cechHc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 1) = 0 := by
    apply hinj
    rw [map_zero, hq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_zsmul, Submodule.subtype_apply]
    exact Submodule.mem_map.mpr ⟨w, hwC, hw'eq⟩
  obtain ⟨v, hvC, hdv⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hcls))
  have hv0 := memZ 0 (w - (p : ℤ) • v) (sub_mem hwC (zsmul_mem hvC _)) (by
    rw [map_sub, dsmul]
    rw [LinearMap.restrictScalars_apply] at hdv
    rw [hdv]
    exact sub_eq_zero.mpr hw'eq)
  obtain ⟨s, hs, hsv⟩ := hZ K ι Ω y a _ hv0
  refine ⟨s, hs, ?_⟩
  rw [← hC K ι Ω y p a s hs, hsv, map_sub, hkill, sub_zero, hrw]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPrimeBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormPrimeBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p : ℕ, p.Prime → ∃ C : ℕ,
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∀ m : Fin (D + 1) →₀ ℕ,
            -((C * τ : ℕ) : ℤ) ≤ padicValRat p ((c (Module.finrank (pullField y L) Ω)).coeff m)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocIdealKer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def LocIdealKer.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (T : Submonoid (MRingOver S ι)) (d : K → ℤ),
    KH.IsMGraded S ι 𝓜 → IsMultiHomogIdeal P → (∀ t ∈ T, ∃ a : K → ℕ, IsMultiHomog t a) →
    ∀ w ∈ KH.locPart ι 𝓜 T d,
      (w ∈ locIdealPart 𝓜 T P d ↔
        IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
          (LocalizedModule.mkLinearMap T (M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M)))
          (P • ⊤ : Submodule (MRingOver S ι) M).mkQ w = 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibreDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameFibreDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))))
      (i : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) → fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k),
      IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) i →
      ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) i = projDeg x e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibrePt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameFibrePt.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))),
      IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal (Sum.inr : Unit → Unit ⊕ Unit) G) 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

