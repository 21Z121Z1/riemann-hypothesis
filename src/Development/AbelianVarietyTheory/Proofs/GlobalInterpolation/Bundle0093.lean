import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0082
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSdLatTwOExpS
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.TwistSd

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem mem_twO_iff (N : Submodule (𝓞 E) (Sp E n)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : Sp E n) :
    y ∈ twist₂ N c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ localization₂ Q.asIdeal N := by
  simp [twist₂, Submodule.mem_iInf]

omit [StarRing E] in
theorem zpow_smul_mem (M : Submodule (𝓞 E) (Sp E n)) (c : ℕ) {k : ℤ} (hk : 0 ≤ k) {y : Sp E n} (hy : y ∈ M) :
    ((c : E) ^ k) • y ∈ M := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  have : ((c : E) ^ (m : ℤ)) • y = ((c : 𝓞 E) ^ m) • y := by
    rw [← algebraMap_smul E ((c : 𝓞 E) ^ m) y, map_pow, map_natCast, zpow_natCast]
  rw [this]
  exact M.smul_mem _ hy

omit [StarRing E] in

theorem isLattice_twO {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) : Submodule.IsLattice E (twist₂ N c e) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 : ∀ x ∈ twist₂ N c e, (c : E) • x ∈ N := fun x hx => mem_of_locP fun Q => by
    have := zpow_smul_mem _ c (k := 1 + e Q) (by have := he Q; omega) ((mem_twO_iff N c e x).1 hx Q)
    rwa [smul_smul, zpow_add₀ hcE, zpow_one, mul_inv_cancel_right₀ (zpow_ne_zero _ hcE)] at this
  have h2 : ∀ x ∈ N, (c : E) • x ∈ twist₂ N c e := fun x hx => (mem_twO_iff N c e _).2 fun Q => by
    have := zpow_smul_mem _ c (k := 1 - e Q) (by have := he Q; omega) (mem_localization_of_mem Q hx)
    rwa [zpow_sub₀ hcE, zpow_one, div_eq_mul_inv, mul_comm, ← smul_smul] at this
  refine ⟨?_, ?_⟩
  · let f : Sp E n →ₗ[𝓞 E] Sp E n := ((c : E) • (LinearMap.id : Sp E n →ₗ[E] Sp E n)).restrictScalars (𝓞 E)
    have hf : Function.Injective f := fun x y h => smul_right_injective _ hcE h
    refine Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hN.fg ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le]
    intro x hx
    have : x = (c : E)⁻¹ • (c : E) • x := by rw [smul_smul, inv_mul_cancel₀ hcE, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (h2 x hx))

theorem hStd_zpow_left (c : ℕ) (k : ℤ) (y x : Sp E n) :
    hStd E n (((c : E) ^ k) • y) x = hStd E n y (((c : E) ^ k) • x) := by
  rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, map_zpow₀, map_natCast]

theorem isSdLat_twO {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) (hodd : ∀ Q, e (conjPrime₂ Q) = -e Q) :
    IsSdLat (twist₂ N c e) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨isLattice_twO hN.1 hc he, ?_⟩
  change dual (hStd E n) (twist₂ N c e) = twist₂ N c e
  apply le_antisymm
  · intro x hx
    rw [mem_dual] at hx
    refine (mem_twO_iff N c e x).2 fun Q' => ?_
    obtain ⟨Q, rfl⟩ : ∃ Q, Q' = conjPrime₂ Q := ⟨conjPrime₂ Q', (GlobalTheory.GO.UniExt.conjP_involutive Q').symm⟩
    rw [GlobalTheory.GO.UniExt.mem_localization_conj_iff hN.1.fg hN.2, hodd, zpow_neg, inv_inv]
    intro y hy
    have hy' : ((c : E) ^ e Q) • y ∈ localization₂ Q.asIdeal (twist₂ N c e) := by
      rwa [mem_localization_twist N hc he, smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hcE), one_smul]
    obtain ⟨t, ht, hty⟩ := hy'
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx _ hty)
    refine ⟨r, cO E t, fun h => ht (by rwa [mem_conjP, cO_cO] at h), ?_⟩
    rw [hr, ← hStd_zpow_left, hStd_osmul_left, ← algebraMap_smul E (cO E t) x, LinearMap.map_smul, smul_eq_mul]
  · intro x hx
    rw [mem_dual]
    intro y hy
    refine mem_of_locP fun Q' => ?_
    obtain ⟨Q, rfl⟩ : ∃ Q, Q' = conjPrime₂ Q := ⟨conjPrime₂ Q', (GlobalTheory.GO.UniExt.conjP_involutive Q').symm⟩
    have h1 := (mem_twO_iff N c e x).1 hx (conjPrime₂ Q)
    rw [GlobalTheory.GO.UniExt.mem_localization_conj_iff hN.1.fg hN.2, hodd, zpow_neg, inv_inv] at h1
    obtain ⟨r, s, hs, hrs⟩ := h1 _ ((mem_twO_iff N c e y).1 hy Q)
    rw [← hStd_zpow_left, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ hcE), one_smul] at hrs
    exact ⟨s, hs, Submodule.mem_one.2 ⟨r, by rw [← hrs, Algebra.smul_def]⟩⟩

theorem expS_conjP {S : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (Q : HeightOneSpectrum (𝓞 E)) :
    expS S (conjPrime₂ Q) = -expS S Q := by
  unfold expS
  rw [GlobalTheory.GO.UniExt.conjP_involutive]
  by_cases h : Q ∈ S
  · simp [h, hS Q h]
  · by_cases h' : conjPrime₂ Q ∈ S <;> simp [h, h']

theorem isSdLat_twO_expS : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)) (c : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat N → 0 < c →
    IsSdLat (twist₂ N c (expS S)) ∧ IsSdLat (twist₂ N c fun Q => -expS S Q) := by
  intro E _ _ _ n N c S hS hN hc
  refine ⟨isSdLat_twO hN hc (expS_bound S) (expS_conjP hS), isSdLat_twO hN hc (fun Q => ?_) fun Q => ?_⟩
  · have := expS_bound S Q
    omega
  · rw [expS_conjP hS]

end GlobalTheory.ThetaMove.TwistSd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsTransvSurjInv
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.Step

open GlobalTheory.ThetaInter

section Transversal

variable {G : Type*} [AddCommGroup G]

def IsTransv {I : Type*} (A B : AddSubgroup G) (r : I → G) : Prop :=
  (∀ i, r i ∈ A) ∧ (∀ i j, r i - r j ∈ B → i = j) ∧ ∀ a ∈ A, ∃ i, a - r i ∈ B

theorem IsTransv.finsum_eq {I J M : Type*} [AddCommMonoid M] {A B : AddSubgroup G} {r : I → G} {r' : J → G}
    (h : IsTransv A B r) (h' : IsTransv A B r') (F : G → M) (hF : ∀ a ∈ A, ∀ a' ∈ A, a - a' ∈ B → F a = F a') :
    ∑ᶠ i, F (r i) = ∑ᶠ j, F (r' j) := by
  choose e he using fun i => h'.2.2 (r i) (h.1 i)
  refine finsum_eq_of_bijective e ⟨fun i j hij => h.2.1 i j ?_, fun j => ?_⟩ fun i => hF _ (h.1 i) _ (h'.1 _) (he i)
  · have := B.sub_mem (he i) (he j)
    rwa [hij, sub_sub_sub_cancel_right] at this
  · obtain ⟨i, hi⟩ := h.2.2 (r' j) (h'.1 j)
    refine ⟨i, (h'.2.1 _ _ ?_).symm⟩
    have := B.add_mem hi (he i)
    rwa [sub_add_sub_cancel] at this

theorem IsTransv.finite {I : Type*} {A B : AddSubgroup G} {r : I → G} (h : IsTransv A B r) (hf : B.relIndex A ≠ 0) :
    Finite I := by
  have : Finite (A ⧸ B.addSubgroupOf A) := Nat.finite_of_card_ne_zero hf
  refine Finite.of_injective (fun i => ((⟨r i, h.1 i⟩ : A) : A ⧸ B.addSubgroupOf A)) fun i j hij => h.2.1 i j ?_
  have := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hij.symm)
  simpa [neg_add_eq_sub] using this

theorem isTransv_out (A B : AddSubgroup G) :
    IsTransv A B fun c : A ⧸ B.addSubgroupOf A => ((Quotient.out c : A) : G) := by
  refine ⟨fun c => (Quotient.out c).2, fun c c' h => ?_, fun a ha => ⟨((⟨a, ha⟩ : A) : A ⧸ B.addSubgroupOf A), ?_⟩⟩
  · rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', eq_comm, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using h
  · have := AddSubgroup.mem_addSubgroupOf.1
      (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' ((⟨a, ha⟩ : A) : A ⧸ B.addSubgroupOf A)))
    simpa [neg_add_eq_sub] using this

theorem isTransv_surjInv {R : Type*} [Ring R] [Module R G] (A B : Submodule R G) :
    IsTransv A.toAddSubgroup B.toAddSubgroup fun z : ↥A ⧸ B.comap A.subtype =>
      ((Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z : ↥A) : G) := by
  have hs := Function.surjInv_eq (Submodule.Quotient.mk_surjective (B.comap A.subtype))
  refine ⟨fun c => Subtype.prop _, fun c c' h => ?_, fun a ha => ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩⟩
  · rw [← hs c, ← hs c', Submodule.Quotient.eq]
    exact h
  · exact (Submodule.Quotient.eq (B.comap A.subtype)).1 (hs (Submodule.Quotient.mk ⟨a, ha⟩)).symm

end Transversal

section Heis

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ}

theorem alpha_neg (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {x : V} (hx : x ∈ A) : α (-x) = α x := by
  have h0 : α 0 = 1 := by
    have h := hs.2 0 A.zero_mem 0 A.zero_mem
    rw [alpha_sq hs A.zero_mem] at h
    simpa [altE] using h
  have h1 : altE H x (-x) = 0 := by
    have := altE_swap hH x x
    simp only [altE, map_neg, Complex.neg_im] at this ⊢
    linarith
  have h := hs.2 x hx (-x) (A.neg_mem hx)
  rw [add_neg_cancel, h0, h1] at h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  linear_combination α (-x) * alpha_sq hs hx * (-1) - α x * h

theorem alpha_opU_congr (hH : IsHerm H) {A B : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α B) {x y : V} (hx : x ∈ A) (hy : y ∈ A) (hxy : x - y ∈ B) (z : V) :
    α x * opU H x F z = α y * opU H y F z := by
  have h := alpha_opU_add hH hd hs hy (A.sub_mem hx hy) F z
  rw [add_sub_cancel, ← opU_mul y (α (x - y))] at h
  rw [h]
  congr 2
  funext w
  exact hF _ hxy w

end Heis

theorem cosSum_inter (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W] (V : Type)
    [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (ι : W →+ V) (As L₁ L₂ : Submodule (𝓞 E) W) (θ : V → ℂ)
    (Ξ : W → ℂ) (hH : IsHerm H) (hι : Function.Injective ι) (hdA : IsSelfDual H (As.toAddSubgroup.map ι))
    (hsA : IsSemiChar H (As.toAddSubgroup.map ι) α) (hd₁ : IsSelfDual H (L₁.toAddSubgroup.map ι))
    (hs₁ : IsSemiChar H (L₁.toAddSubgroup.map ι) α) (hθ : θ ∈ fixedBy H α (L₂.toAddSubgroup.map ι))
    (h21 : L₂ ⊓ As ≤ L₁) (h1 : L₁ ≤ (L₁ ⊓ As) ⊔ (L₁ ⊓ L₂))
    (hfin : L₂.toAddSubgroup.relIndex As.toAddSubgroup ≠ 0)
    (hΞ : ∀ t ∈ As, ∀ y ∈ L₁ ⊓ As, Ξ (t + y) = Ξ t) (z : V) :
    cosSum H α ι As L₁ (inter H α (L₂.toAddSubgroup.map ι) (L₁.toAddSubgroup.map ι) θ) Ξ z =
      ((Real.sqrt (L₂.toAddSubgroup.relIndex L₁.toAddSubgroup : ℕ) : ℝ) : ℂ)⁻¹ * cosSum H α ι As L₂ θ Ξ z := by
  classical
  obtain ⟨I, r, hr, hI⟩ : ∃ (I : Type) (r : I → W), IsTransv As.toAddSubgroup L₁.toAddSubgroup r ∧
      ∀ F : W → ℂ, latSum As L₁ F = ∑ᶠ i, F (r i) := ⟨_, _, isTransv_surjInv As L₁, fun _ => rfl⟩
  obtain ⟨J, y, hy⟩ : ∃ (J : Type) (y : J → W), IsTransv (L₁ ⊓ As).toAddSubgroup L₂.toAddSubgroup y :=
    ⟨_, _, isTransv_out _ _⟩
  have hy₁ : ∀ j, y j ∈ L₁ := fun j => (hy.1 j).1
  have hyA : ∀ j, y j ∈ As := fun j => (hy.1 j).2
  have hrA : ∀ i, r i ∈ As := hr.1
  have hp : IsTransv As.toAddSubgroup L₂.toAddSubgroup fun p : I × J => r p.1 - y p.2 := by
    refine ⟨fun p => As.sub_mem (hrA _) (hyA _), fun p q h => ?_, fun a ha => ?_⟩
    · have h2 : r p.1 - y p.2 - (r q.1 - y q.2) ∈ L₁ :=
        h21 ⟨h, As.sub_mem (As.sub_mem (hrA _) (hyA _)) (As.sub_mem (hrA _) (hyA _))⟩
      have h3 : p.1 = q.1 := hr.2.1 _ _ (by
        have := L₁.add_mem h2 (L₁.sub_mem (hy₁ p.2) (hy₁ q.2))
        have e : r p.1 - y p.2 - (r q.1 - y q.2) + (y p.2 - y q.2) = r p.1 - r q.1 := by abel
        rwa [e] at this)
      refine Prod.ext h3 (hy.2.1 _ _ ?_).symm
      have e : r p.1 - y p.2 - (r q.1 - y q.2) = y q.2 - y p.2 := by rw [h3]; abel
      rw [← e]
      exact h
    · obtain ⟨i, hi⟩ := hr.2.2 a ha
      obtain ⟨j, hj⟩ := hy.2.2 (-(a - r i)) ⟨L₁.neg_mem hi, As.neg_mem (As.sub_mem ha (hrA i))⟩
      refine ⟨(i, j), ?_⟩
      have := L₂.neg_mem hj
      have e : -(-(a - r i) - y j) = a - (r i - y j) := by abel
      rwa [e] at this
  have hq : IsTransv (L₁.toAddSubgroup.map ι) (L₂.toAddSubgroup.map ι) fun j => ι (y j) := by
    refine ⟨fun j => ⟨_, hy₁ j, rfl⟩, fun i j h => hy.2.1 i j ?_, ?_⟩
    · obtain ⟨s, hs, e⟩ := h
      rw [← map_sub] at e
      rw [← hι e]
      exact hs
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (h1 ha)
      obtain ⟨j, hj⟩ := hy.2.2 u hu
      refine ⟨j, u - y j + v, L₂.add_mem hj hv.2, ?_⟩
      rw [← map_sub]
      congr 1
      abel
  have hfp := hp.finite hfin
  have : Nonempty I := let ⟨i, _⟩ := hr.2.2 0 As.zero_mem; ⟨i⟩
  have : Nonempty J := let ⟨i, _⟩ := hy.2.2 0 (L₁ ⊓ As).zero_mem; ⟨i⟩
  have : Finite I := Finite.prod_left J
  have : Finite J := Finite.prod_right I
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have mA : ∀ {t : W}, t ∈ As → ι t ∈ As.toAddSubgroup.map ι := fun ht => ⟨_, ht, rfl⟩
  have hint : inter H α (L₂.toAddSubgroup.map ι) (L₁.toAddSubgroup.map ι) θ = fun w =>
      ((Real.sqrt (L₂.toAddSubgroup.relIndex L₁.toAddSubgroup : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ j, α (ι (y j)) * opU H (ι (y j)) θ w := by
    funext w
    rw [inter, relIdx, AddSubgroup.relIndex_map_map_of_injective _ _ hι,
      (isTransv_out _ _).finsum_eq hq (fun x => α x * opU H x θ w)
        fun a ha a' ha' h => alpha_opU_congr hH hd₁ hs₁ hθ ha ha' h w, finsum_eq_sum_of_fintype]
  have hR : cosSum H α ι As L₂ θ Ξ z =
      ∑ p : I × J, Ξ (r p.1 - y p.2) * (α (ι (r p.1 - y p.2)) * opU H (-(ι (r p.1 - y p.2))) θ z) := by
    rw [← finsum_eq_sum_of_fintype]
    refine (isTransv_surjInv As L₂).finsum_eq hp (fun t => Ξ t * (α (ι t) * opU H (-(ι t)) θ z)) fun a ha a' ha' h => ?_
    have h2 := hΞ a' ha' (a - a') ⟨h21 ⟨h, As.sub_mem ha ha'⟩, As.sub_mem ha ha'⟩
    rw [add_sub_cancel] at h2
    rw [h2, ← alpha_neg hH hsA (mA ha), ← alpha_neg hH hsA (mA ha'),
      alpha_opU_congr hH hdA hsA hθ (neg_mem (mA ha)) (neg_mem (mA ha'))]
    refine ⟨-(a - a'), L₂.neg_mem h, ?_⟩
    rw [map_neg, map_sub]
    abel
  rw [hR, hint, cosSum, hI, finsum_eq_sum_of_fintype, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [opU_mul, opU_sum, mul_left_comm (α _), mul_left_comm, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := hΞ (r i) (hrA i) (-y j) (neg_mem (hy.1 j))
  rw [← sub_eq_add_neg] at h2
  have e : -ι (r i - y j) = -ι (r i) + ι (y j) := by rw [map_sub]; abel
  rw [h2, ← alpha_neg hH hsA (mA (As.sub_mem (hrA i) (hyA j))), e,
    alpha_opU_add hH hdA hsA (neg_mem (mA (hrA i))) (mA (hyA j)), alpha_neg hH hsA (mA (hrA i)), opU_mul]

end GlobalTheory.ThetaMove.Step
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetCCompSubst
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open scoped ContDiff

namespace GlobalTheory.Glob.JetChainLin

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem prod_pow_eq {σ M : Type} [CommMonoid M] (F : σ → M) (e : σ →₀ ℕ) {n : ℕ} (f : Fin n → σ)
    (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset σ)) :
    (e.prod fun k n => F k ^ n) = ∏ i, F (f i) := by
  classical
  have h1 : ((Finsupp.toMultiset e).map F).prod = e.prod fun k n => F k ^ n := by
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index]
    · intro _; simp
    · intro _ _ _; rw [pow_add]
  rw [← h1, hm, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
  rfl

theorem monomial_eq_prod {σ : Type} (e : σ →₀ ℕ) {n : ℕ} (f : Fin n → σ)
    (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset σ)) :
    (MvPolynomial.monomial e (1 : ℂ)) = ∏ i, MvPolynomial.X (f i) := by
  rw [MvPolynomial.monomial_eq, prod_pow_eq (fun k => (MvPolynomial.X k : MvPolynomial σ ℂ)) e f hm]
  simp

theorem derivAt0_eq (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (e : DVar ι a b →₀ ℕ) {n : ℕ}
    (f : Fin n → DVar ι a b) (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b))) :
    iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) = derivAt0 G e := by
  classical
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  have hc : (Finsupp.toMultiset e).card = n := by rw [hm]; simp
  have p : ((List.ofFn f).map coordX).Perm ((Finsupp.toMultiset e).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hm]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p n (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx ι a b) (w : Fin n' → VCx ι a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  unfold derivAt0
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp
  · simp

theorem jetC_eq (cD : ι → ℂ) (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (e : DVar ι a b →₀ ℕ) {n : ℕ}
    (f : Fin n → DVar ι a b) (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b))) :
    jetC cD G e = (∏ i, cD (f i).1) * iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) := by
  rw [derivAt0_eq G hG e f hm, jetC, prod_pow_eq (fun k : DVar ι a b => cD k.1) e f hm]

theorem constr_prod_X (cD : ι → ℂ) (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) {n : ℕ}
    (f : Fin n → DVar ι a b) :
    (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr ℂ (jetC cD G) (∏ i, MvPolynomial.X (f i)) =
      (∏ i, cD (f i).1) * iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) := by
  classical
  have hm : Finsupp.toMultiset (Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b))) =
      (↑(List.ofFn f) : Multiset (DVar ι a b)) := Multiset.toFinsupp_toMultiset _
  rw [← monomial_eq_prod _ f hm, ← jetC_eq cD G hG _ f hm]
  have := (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr_basis ℂ (jetC cD G)
    (Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b)))
  rwa [MvPolynomial.coe_basisMonomials] at this

noncomputable def subst (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) :
    VCx ι a b →ₗ[ℂ] VCx ι a b where
  toFun z := fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j
  map_add' z w := by
    funext τ i j
    simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ i j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

omit [Fintype ι] in
theorem subst_coordX (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (k : DVar ι a b) :
    subst g h (coordX k) =
      ∑ p : Fin b × Fin a, (h k.1 p.1 k.2.1 * g k.1 k.2.2 p.2) • coordX (k.1, p.1, p.2) := by
  classical
  obtain ⟨t, k, l⟩ := k
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change ∑ k' : Fin b, ∑ l' : Fin a, h τ i k' * coordX (t, k, l) τ k' l' * g τ l' j = _
  by_cases hτ : τ = t
  · subst hτ
    rw [Finset.sum_eq_single (i, j), Finset.sum_eq_single k, Finset.sum_eq_single l]
    · simp [coordX]
    · intro l' _ hl; simp [coordX, hl]
    · simp
    · intro k' _ hk; simp [coordX, hk]
    · simp
    · rintro ⟨i', j'⟩ _ hne
      have : ¬ (i = i' ∧ j = j') := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      simp [coordX, this]
    · simp
  · simp [coordX, hτ]

theorem jetC_comp_subst : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (G : VCx ι a b → ℂ) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ), (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar ι a b →₀ ℕ, jetC cD (fun z : VCx ι a b => G (fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j)) m = (MvPolynomial.basisMonomials (DVar ι a b) ℂ).constr ℂ (jetC cD G) (MvPolynomial.aeval (fun k : DVar ι a b => ∑ i : Fin b, ∑ j : Fin a, (MvPolynomial.C (h k.1 i k.2.1 * g k.1 k.2.2 j) * MvPolynomial.X (k.1, i, j) : MvPolynomial (DVar ι a b) ℂ)) (MvPolynomial.monomial m (1 : ℂ))) := by
  intro ι _ a b cD G g h hG m
  classical
  let T : VCx ι a b →L[ℂ] VCx ι a b := LinearMap.toContinuousLinearMap (subst g h)
  have h1 : (fun z : VCx ι a b => G (fun τ i j => ∑ k : Fin b, ∑ l : Fin a, h τ i k * z τ k l * g τ l j)) =
      G ∘ T := rfl
  have hm : Finsupp.toMultiset m = (↑(List.ofFn (Finsupp.toMultiset m).toList.get) : Multiset (DVar ι a b)) := by
    rw [List.ofFn_get, Multiset.coe_toList]
  generalize (Finsupp.toMultiset m).toList.get = f at hm
  rw [h1, jetC_eq cD (G ∘ T) (fun k => (hG k).comp T.contDiff) m f hm, monomial_eq_prod m f hm,
    T.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    map_prod]
  have h2 : (fun i => T (coordX (f i))) = fun i =>
      ∑ p : Fin b × Fin a, (h (f i).1 p.1 (f i).2.1 * g (f i).1 (f i).2.2 p.2) • coordX ((f i).1, p.1, p.2) :=
    funext fun i => subst_coordX g h (f i)
  rw [h2, ContinuousMultilinearMap.map_sum, Finset.mul_sum]
  simp only [MvPolynomial.aeval_X, ← Fintype.sum_prod_type']
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← MvPolynomial.smul_eq_C_mul, map_smul,
    constr_prod_X cD G hG (fun i => ((f i).1, (r i).1, (r i).2)), ContinuousMultilinearMap.map_smul_univ]
  simp only [smul_eq_mul]
  ring

end GlobalTheory.Glob.JetChainLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
section
noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

theorem exists_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L)
    (W : HeightOneSpectrum (𝓞 L)) : ∃ Q : HeightOneSpectrum (𝓞 K),
      ∀ r : 𝓞 K, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom j r ∈ W.asIdeal := by
  letI : Algebra K L := j.toAlgebra
  exact ⟨W.under (𝓞 K), fun r => Iff.rfl⟩

theorem mem_valO_of_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L)
    (W : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : ∀ r : 𝓞 K, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom j r ∈ W.asIdeal) (x : K) :
    j x ∈ valO W ↔ x ∈ valO Q := by
  letI : Algebra K L := j.toAlgebra
  haveI : W.asIdeal.LiesOver Q.asIdeal := ⟨Ideal.ext fun r => h r⟩
  rw [mem_valO, mem_valO, show j x = algebraMap K L x from rfl,
    ← HeightOneSpectrum.valuation_liesOver L Q W x]
  exact pow_le_one_iff (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver W.asIdeal Q.ne_bot)

theorem mem_Ow_iff_valO (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) : x ∈ Ow D w ↔ x ∈ valO (D.plEq w) :=
  D.val_nonneg_iff w x

theorem resChar_mem_plEq (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar', ← WithZero.exp_zero,
    WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

theorem resChar_eq_of_mem_plEq (D : D7) (w : D.what₂.places.Pl) {T : ℕ} (hT : T.Prime)
    (h : (T : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = T := by
  by_contra hne
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (T : 𝓞 D.what₂.LL) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.what₂.places.resChar_prime w) hT).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem_plEq D w)) (Ideal.mul_mem_left _ _ h)

end GlobalTheory.LvT.Inh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitOfConjPNe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

theorem split_of_conj_ne₂ : ∀ (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (v : HeightOneSpectrum (𝓞 X.F)),
    X.Ok → conjPrime₂ P ≠ P → P.asIdeal.under (𝓞 X.F) = v.asIdeal →
    Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal = P.asIdeal * (conjPrime₂ P).asIdeal ∧
    ∀ Q : HeightOneSpectrum (𝓞 X.E), Q.asIdeal.under (𝓞 X.F) = v.asIdeal ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  intro X P v hX hP hv
  obtain rfl : P.under (𝓞 X.F) = v := HeightOneSpectrum.ext hv
  have key := GlobalTheory.MuConj.mem_above_iff hX.star_F hX.rankE P hP
  refine ⟨GlobalTheory.Mem.GoodPlace.map_eq_mul hX.rankE hP.symm ((key _).2 (Or.inr rfl)), fun Q => ?_⟩
  rw [← key Q]
  exact ⟨fun h => HeightOneSpectrum.ext h, fun h => congrArg HeightOneSpectrum.asIdeal h⟩

end GlobalTheory.ThetaMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankPolysLeTOStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_rank_and_poly_counts_le_TOv : SzRow (fun C D L => (((D.R.f * D.R.r.choose 2 : ℕ) + 2) * (nWv D.R L.sc : ℕ) + 2 * D.R.r ≤ (TOv L.sc : ℕ)) ∧ (40 * ((D.R.f * D.R.r.choose 2 : ℕ) + 2) ≤ (TOv L.sc : ℕ)) ∧ (11 * (D.R.f * D.R.r.choose 2 : ℕ) ^ 2 ≤ (TOv L.sc : ℕ)) ∧ (D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * ((D.R.f * D.R.r.choose 2 : ℕ) + 1) ≤ (TOv L.sc : ℕ))) := by
  first | exact @GlobalTheory.EX.szRow_rank_polys_le_TO | exact GlobalTheory.EX.szRow_rank_polys_le_TO | (intros; apply GlobalTheory.EX.szRow_rank_polys_le_TO <;> assumption)
end

