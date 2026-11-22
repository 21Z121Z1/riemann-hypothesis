import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapIdealSheafOfForallDivLocalEquation
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.Poinc

theorem mem_map_idealSheaf_of_forall_div :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)), (∀ x' : M.Z, π x' ∈ V.1 → ∀ f', EqAt M D x' f' → valF M₁.pt V.1 g / f' ∈ M.O x') → g ∈ (D.idealSheaf.map π).ideal V := by
  intro o Ω _ _ _ M₁ M π hπ hprop D V g hg
  haveI : QuasiCompact π := inferInstance
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker]
  change (D.idealSheaf.subschemeι.app (π ⁻¹ᵁ V.1)).hom ((π.app V.1).hom g) = 0
  rw [GlobalTheory.Cartier.app_subschemeι_eq_zero_iff]
  intro W hW
  show _ ∈ (EffCartierData.locIdeal D.U D.f D.exists_mem D.associated_germ).ideal W
  rw [EffCartierData.mem_locIdeal_iff]
  intro i x hx hi
  have hxV : x ∈ π ⁻¹ᵁ V.1 := hW hx
  have hV : (V.1 : Set M₁.Z).Nonempty := ⟨π x, hxV⟩
  rw [GlobalTheory.Cartier.germ_resG]
  have hval : valF M.pt (π ⁻¹ᵁ V.1) ((π.app V.1).hom g) = valF M₁.pt V.1 g := hπ.valF_app hV g
  have hq := hg x hxV _ ⟨i, hi, rfl⟩
  have hne : valF M.pt (D.U i) (D.f i) ≠ 0 := by
    intro h0
    have hnz := GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) x hi
    have : (M.Z.presheaf.germ (D.U i) x hi).hom (D.f i) = 0 := by
      apply M.stalkHom_injective x
      rw [map_zero]
      exact (RatModel.stalkHom_germ hi (D.f i)).trans h0
    rw [this] at hnz
    exact zero_notMem_nonZeroDivisors hnz
  rw [← map_dvd_iff (M.stalkEquiv x)]
  have e1 := RatModel.stalkEquiv_germ hi (D.f i)
  have e2 := RatModel.stalkEquiv_germ hxV ((π.app V.1).hom g)
  refine ⟨⟨_, hq⟩, ?_⟩
  apply Subtype.ext
  change (M.stalkEquiv x ((M.Z.presheaf.germ _ x hxV) ((π.app V.1).hom g)) : Ω) =
    (M.stalkEquiv x ((M.Z.presheaf.germ _ x hi) (D.f i)) : Ω) * (valF M₁.pt V.1 g / valF M.pt (D.U i) (D.f i))
  rw [e1, e2]
  simp only
  rw [hval, mul_div_cancel₀ _ hne]

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfForallMemSupPow
section
open IsLocalRing

namespace GlobalTheory.Poinc

open IsLocalRing in
variable {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] in
private theorem mem_of_forall_mem_sup_maximalIdeal_pow' (N : Ideal V) (x : V)
    (hx : ∀ e : ℕ, x ∈ N ⊔ maximalIdeal V ^ e) : x ∈ N := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := V) (M := V ⧸ N) (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmem : Ideal.Quotient.mk N x ∈
      ⨅ i : ℕ, (maximalIdeal V ^ i • ⊤ : Submodule V (V ⧸ N)) := by
    refine Submodule.mem_iInf _ |>.2 fun e => ?_
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 (hx e)
    have h1 : Ideal.Quotient.mk N (a + y) = y • Ideal.Quotient.mk N 1 := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, Algebra.smul_def, map_one,
        mul_one]
      rfl
    rw [h1]
    exact Submodule.smul_mem_smul hy Submodule.mem_top
  rw [hbot] at hmem
  exact hmem

open IsLocalRing in
variable {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] in
private theorem exists_not_mem_span_mul_maximalIdeal_sup_pow [IsDomain V] {g : V} (hg : g ≠ 0) :
    ∃ e : ℕ, g ∉ Ideal.span {g} * maximalIdeal V ⊔ maximalIdeal V ^ e := by
  by_contra h
  push_neg at h
  have hg' := mem_of_forall_mem_sup_maximalIdeal_pow' _ g h
  obtain ⟨z, hz, hgz⟩ := Ideal.mem_span_singleton_mul.1 hg'
  have hz1 : z = 1 := by
    have : g * (z - 1) = 0 := by rw [mul_sub, hgz, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hg
    · exact sub_eq_zero.1 h0
  exact (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 (hz1 ▸ hz))

open IsLocalRing in

theorem _root_.GlobalTheory.Poinc.const_mod_prime_of_approx (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] [IsNoetherianRing V] (p : Ideal V) [p.IsPrime] (O' : Subring V)
    (hO : ∀ h ∈ O', h ∈ maximalIdeal V → h ∈ p) (g b u : V) (I : Ideal V) (hg : g ≠ 0)
    (hI : I ≤ maximalIdeal V)
    (H : ∀ e : ℕ, ∃ h ∈ O',
      h * g - u * (b * g) ∈ Ideal.span {b * g} * I ⊔ maximalIdeal V ^ e) :
    (IsUnit u → b ∈ maximalIdeal V → b ∈ p) ∧ (I ≤ p → ∃ h ∈ O', h - u * b ∈ p) := by
  obtain ⟨e₀, he₀⟩ := exists_not_mem_span_mul_maximalIdeal_sup_pow hg
  choose a haO haH using H
  have hspan : Ideal.span {b * g} ≤ Ideal.span {g} :=
    Ideal.span_singleton_le_span_singleton.2 ⟨b, mul_comm b g⟩
  have hbgI : Ideal.span {b * g} * I ≤ Ideal.span {g} * maximalIdeal V := Ideal.mul_mono hspan hI
  have hpow : ∀ {e : ℕ}, e₀ ≤ e → maximalIdeal V ^ e ≤ maximalIdeal V ^ e₀ :=
    fun h => Ideal.pow_le_pow_right h

  have hunit : ∀ x ∈ O', x * g ∈ Ideal.span {g} * maximalIdeal V ⊔ maximalIdeal V ^ e₀ →
      x ∈ p := by
    intro x hxO hx
    by_contra hxp
    have hxu : IsUnit x := by
      by_contra hnu
      exact hxp (hO x hxO ((mem_maximalIdeal x).2 hnu))
    apply he₀
    have key : ((hxu.unit⁻¹ : Vˣ) : V) * (x * g) = g := by
      rw [← mul_assoc, hxu.val_inv_mul, one_mul]
    have hmul := Ideal.mul_mem_left _ ((hxu.unit⁻¹ : Vˣ) : V) hx
    rwa [key] at hmul
  refine ⟨fun hu hb => ?_, fun hIp => ?_⟩
  · have hap : ∀ e, e₀ ≤ e → a e ∈ p := by
      intro e he
      refine hunit (a e) (haO e) ?_
      have h1 : a e * g = (a e * g - u * (b * g)) + g * (u * b) := by ring
      rw [h1]
      refine Ideal.add_mem _ ?_ (Ideal.mem_sup_left (Ideal.mem_span_singleton_mul.2
        ⟨u * b, Ideal.mul_mem_left _ _ hb, rfl⟩))
      exact sup_le_sup hbgI (hpow he) (haH e)
    have hN : u * (b * g) ∈ Ideal.span {g} * p ⊔ Ideal.span {b * g} * maximalIdeal V := by
      refine mem_of_forall_mem_sup_maximalIdeal_pow' _ _ fun e => ?_
      have h1 : u * (b * g) = g * a (max e e₀) - (a (max e e₀) * g - u * (b * g)) := by ring
      rw [h1]
      refine Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left
        (Ideal.mem_span_singleton_mul.2 ⟨_, hap _ (le_max_right _ _), rfl⟩))) ?_
      refine sup_le_sup (le_sup_of_le_right (Ideal.mul_mono_right hI))
        (Ideal.pow_le_pow_right (le_max_left e e₀)) (haH (max e e₀))
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hN
    obtain ⟨q, hq, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy
    obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.1 hz
    have hcancel : b * (u - r) = q := by
      apply mul_left_cancel₀ hg
      linear_combination hyz.symm
    have hur : IsUnit (u - r) := by
      by_contra hnu
      have hm : u - r ∈ maximalIdeal V := (mem_maximalIdeal _).2 hnu
      have : u ∈ maximalIdeal V := by
        simpa using Ideal.add_mem _ hm hr
      exact (mem_maximalIdeal u).1 this hu
    rcases (inferInstance : p.IsPrime).mem_or_mem (hcancel ▸ hq) with h | h
    · exact h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h hur) (inferInstance : p.IsPrime).ne_top
  · have hdiff : ∀ e, e₀ ≤ e → a e - a e₀ ∈ p := by
      intro e he
      refine hunit _ (Subring.sub_mem _ (haO e) (haO e₀)) ?_
      have h1 : (a e - a e₀) * g =
          (a e * g - u * (b * g)) - (a e₀ * g - u * (b * g)) := by ring
      rw [h1]
      exact Ideal.sub_mem _ (sup_le_sup hbgI (hpow he) (haH e)) (sup_le_sup hbgI le_rfl (haH e₀))
    refine ⟨a e₀, haO e₀, ?_⟩
    have hN : (a e₀ - u * b) * g ∈ Ideal.span {g} * p := by
      refine mem_of_forall_mem_sup_maximalIdeal_pow' _ _ fun e => ?_
      have h1 : (a e₀ - u * b) * g =
          g * (-(a (max e e₀) - a e₀)) + (a (max e e₀) * g - u * (b * g)) := by ring
      rw [h1]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_mul.2
        ⟨_, neg_mem (hdiff _ (le_max_right _ _)), rfl⟩)) ?_
      exact sup_le_sup (Ideal.mul_mono hspan hIp) (Ideal.pow_le_pow_right (le_max_left e e₀))
        (haH (max e e₀))
    obtain ⟨q, hq, hgq⟩ := Ideal.mem_span_singleton_mul.1 hN
    have : a e₀ - u * b = q := by
      apply mul_left_cancel₀ hg
      rw [hgq, mul_comm]
    exact this ▸ hq

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRealLieIffTraceFreeSkewSigns
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

private theorem conj_zero_iff' {R : Type} [Ring R] (a b c d S : R) (hba : b * a = 1) (hcd : c * d = 1) :
    S = 0 ↔ a * S * c = 0 := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  have e : S = b * (a * S * c) * d := by
    simp only [← mul_assoc, hba, one_mul]; rw [mul_assoc, hcd, mul_one]
  rw [e, h]; simp

private theorem expand' {R : Type} [Ring R] (a b c d y z g : R) (hab : a * b = 1) (hdc : d * c = 1) :
    a * (b * (y * a) * g + g * (c * z * d)) * c = y * (a * g * c) + (a * g * c) * z := by
  have : a * (b * (y * a) * g + g * (c * z * d)) * c = (a * b) * y * (a * g * c) + (a * g * c) * z * (d * c) := by
    simp only [mul_add, add_mul, mul_assoc]
  rw [this, hab, hdc, one_mul, mul_one]

private theorem permJ' {r : ℕ} (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin r) :
    (permM e)ᵀ * Formalism.UG.Jpq p q * permM e = diagonal (fun a => if (e.symm a).isLeft then (1:ℂ) else -1) := by
  ext a b
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply, diagonal_apply, Formalism.UG.Jpq]
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]; rcases e.symm a with i | i <;> simp
  · rw [if_neg hab]
    have h := e.symm.injective.ne hab
    revert h
    generalize e.symm a = i
    generalize e.symm b = j
    rcases i with i | i <;> rcases j with j | j <;> intro h <;> simp_all [one_apply]

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem mem_comap_realLie_iff_skewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type)
    (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r),
    IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r),
      Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI Y
  rw [Submodule.mem_comap, GlobalTheory.SUVol.DensOne.mem_realLie_iff]
  refine forall_congr' fun τ => ?_
  have hdet := (det_ne_zero_of_isIdent hI τ).1
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  set Gt := G.map τ.1 with hGt
  set Yt : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => Y (τ, a, b) with hYt
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  set N := M⁻¹ with hN
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv M hu
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul M hu
  have hX : Matrix.of (fromFrame x Y τ) = M * Yt * N := rfl
  rw [hX]
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => ((sgnR σ e τ a : ℝ) : ℂ)) with hD
  have hPJP : Pᵀ * J * P = D := by
    rw [hP, hJdef, permJ', hD]
    congr 1; funext a; simp only [sgnR]; split_ifs <;> simp
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hMt : (Mᴴ)ᵀ = M.map (starRingEnd ℂ) := by ext i j; simp
  have hG' : Gt = -(Bᴴ * J * B)ᵀ := by rw [h1, transpose_neg, transpose_transpose, neg_neg]
  have hH : Mᵀ * Gt * M.map (starRingEnd ℂ) = -D := by
    rw [hG', ← hMt, Matrix.mul_neg, Matrix.neg_mul]
    rw [show Mᵀ * (Bᴴ * J * B)ᵀ * (Mᴴ)ᵀ = (Mᴴ * (Bᴴ * J * B) * M)ᵀ by simp only [transpose_mul, Matrix.mul_assoc]]
    have : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
      rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hPJP, hD, diagonal_transpose]
  have hc1 : M.map (starRingEnd ℂ) * N.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc2 : N.map (starRingEnd ℂ) * M.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have ht1 : Mᵀ * Nᵀ = 1 := by rw [← transpose_mul, hNM, transpose_one]
  have ht2 : Nᵀ * Mᵀ = 1 := by rw [← transpose_mul, hMN, transpose_one]
  have htr : (M * Yt * N).trace = ∑ a, Y (τ, a, a) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hNM, Matrix.one_mul]; rfl
  rw [htr, and_comm]
  refine and_congr_right fun _ => ?_
  rw [conj_zero_iff' Mᵀ Nᵀ (M.map (starRingEnd ℂ)) (N.map (starRingEnd ℂ)) _ ht2 hc1]
  rw [transpose_mul, transpose_mul, Matrix.map_mul, Matrix.map_mul]
  rw [expand' _ _ _ _ _ _ _ ht1 hc2, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero, ← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  rw [eq_comm (b := (0 : Matrix (Fin r) (Fin r) ℂ) a b)]
  simp [hD, hYt, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact eq_comm

end GlobalTheory.CovTop.VolUp.FrameBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanImageOfForallHeightOneOverPrime
section
open GlobalTheory.Desc

namespace GlobalTheory.Desc.LocalDescent

theorem exists_basis_of_finite : ∀ (R F : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field F] (c₀ : R →+* F), Function.Injective c₀ → ∀ (p : Ideal R), p.IsPrime → p.height = 1 → ∀ (T : Set F), T.Finite → ∃ (k : ℕ) (b : Fin k → F), (∀ j, ∃ (n : ℕ) (g : Fin n → R) (v : Fin n → F) (t : R), t ∉ p ∧ (∀ i, v i ∈ T) ∧ c₀ t * b j = ∑ i, c₀ (g i) * v i) ∧ (∀ r : Fin k → R, ∑ j, c₀ (r j) * b j = 0 → r = 0) ∧ ∃ t : R, t ∉ p ∧ ∀ v ∈ T, ∃ g : Fin k → R, c₀ t * v = ∑ j, c₀ (g j) * b j := by
  intro R F _ _ _ _ _ c₀ hc p hp hp1 T hT
  classical
  let B := Localization.AtPrime p
  haveI := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp1 B
  have hu : ∀ y : p.primeCompl, IsUnit (c₀ y) := fun y => IsUnit.mk0 _ fun h =>
    y.2 (((injective_iff_map_eq_zero c₀).mp hc _ h) ▸ p.zero_mem)
  let l : B →+* F := IsLocalization.lift hu
  have hl : ∀ r, l (algebraMap R B r) = c₀ r := fun r => IsLocalization.lift_eq hu r
  have hinj := IsLocalization.injective B p.primeCompl_le_nonZeroDivisors
  have hli : Function.Injective l := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj p.primeCompl z
    have h0 : c₀ r = 0 := by rw [← hl, ← e, map_mul, hz, zero_mul]
    rw [(injective_iff_map_eq_zero c₀).mp hc _ h0, map_zero] at e
    exact (IsLocalization.map_units B s).mul_left_eq_zero.mp e
  letI : Algebra B F := l.toAlgebra
  have hsm : ∀ (z : B) (v : F), z • v = l z * v := fun _ _ => rfl
  haveI : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective B F).mpr hli
  let E := Submodule.span B T
  haveI : Module.Finite B E := Module.Finite.span_of_finite B hT
  haveI : Module.Free B E := inferInstance
  let e := Module.finBasis B E
  have clear : ∀ {ι : Type} [Finite ι] (z : ι → B), ∃ t, t ∉ p ∧ ∃ g : ι → R,
      ∀ i, c₀ (g i) = c₀ t * l (z i) := fun z => by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl z
    choose h hh using hd
    exact ⟨d, d.2, h, fun i => by rw [← hl, hh, Algebra.smul_def, map_mul, hl]⟩
  refine ⟨_, fun j => (e j : F), fun j => ?_, fun r hr => ?_, ?_⟩
  · obtain ⟨n, z, v, hv⟩ := Submodule.mem_span_set'.mp (e j).2
    obtain ⟨t, ht, g, hg⟩ := clear z
    refine ⟨n, g, fun i => v i, t, ht, fun i => (v i).2, ?_⟩
    simp only [← hv, hg, hsm, Finset.mul_sum, mul_assoc]
  · have := Fintype.linearIndependent_iff.mp e.linearIndependent (fun j => algebraMap R B (r j))
      (Subtype.ext (by simpa [hsm, hl] using hr))
    funext j
    exact (injective_iff_map_eq_zero _).mp hinj _ (this j)
  · haveI : Finite T := hT
    obtain ⟨t, ht, g, hg⟩ := clear
      fun z : T × Fin (Module.finrank B E) => e.repr ⟨z.1, Submodule.subset_span z.1.2⟩ z.2
    refine ⟨t, ht, fun v hv => ⟨fun j => g (⟨v, hv⟩, j), ?_⟩⟩
    have := congrArg Subtype.val (e.sum_repr ⟨v, Submodule.subset_span hv⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hsm] at this
    simp only [hg, mul_assoc, ← Finset.mul_sum, this]

theorem span_test : ∀ (R₁ F₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F₁] (c₁ : R₁ →+* F₁), Function.Injective c₁ → ∀ (S : Submonoid R₁), (0 : R₁) ∉ S → ∀ (k : ℕ) (b : Fin k → F₁), (∀ r : Fin k → R₁, ∑ j, c₁ (r j) * b j = 0 → r = 0) → ∀ (x : F₁) (a : R₁), a ≠ 0 → (∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ (t * a) * x = ∑ j, c₁ (g j) * b j) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → a ∈ q → Disjoint (S : Set R₁) (q : Set R₁) → ∃ s, s ∉ q ∧ ∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ (t * s) * x = ∑ j, c₁ (g j) * b j) → ∃ (t : R₁) (g : Fin k → R₁), t ∈ S ∧ c₁ t * x = ∑ j, c₁ (g j) * b j := by
  intro R₁ F₁ _ _ _ _ _ c₁ hc S hS k b hind x a ha ⟨t, g, ht, e⟩ hloc
  classical
  have hle : S ≤ nonZeroDivisors R₁ := fun y hy =>
    mem_nonZeroDivisors_of_ne_zero fun h => hS (h ▸ hy)
  let A := Localization S
  haveI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hle
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A S hle
  have hinj := IsLocalization.injective A hle
  have hdvd : ∀ j, algebraMap R₁ A a ∣ algebraMap R₁ A (g j) := fun j => by
    refine GlobalTheory.dvd_of_forall_height_eq_one ((map_ne_zero_iff _ hinj).mpr ha) fun Q hQ h1 haQ => ?_
    obtain ⟨hq, hd⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint S A Q).mp hQ
    obtain ⟨s, hs, t', g', ht', e'⟩ := hloc (Q.comap (algebraMap R₁ A)) hq
      (by rw [IsLocalization.height_comap S Q, h1]) haQ hd
    have h0 := hind (fun j => t' * s * g j - t * a * g' j) (by
      simp only [map_sub, map_mul, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, ← e, ← e']
      ring)
    have h1 : t' * s * g j = t * a * g' j := sub_eq_zero.mp (congrFun h0 j)
    refine ⟨algebraMap R₁ A s, hs, (IsLocalization.map_units A ⟨t', ht'⟩).dvd_mul_left.mp ?_⟩
    refine ⟨algebraMap R₁ A (t * g' j), ?_⟩
    simp only [← map_mul]
    congr 1
    linear_combination h1
  choose y hy using hdvd
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite S y
  choose h hh using hd
  refine ⟨d * t, h, S.mul_mem d.2 ht, ?_⟩
  have h1 : ∀ j, (d : R₁) * g j = a * h j := fun j => hinj (by
    rw [map_mul, map_mul, hh, hy, Algebra.smul_def]; ring)
  apply mul_left_cancel₀ ((map_ne_zero_iff c₁ hc).mpr ha)
  have : c₁ a * (c₁ (d * t) * x) = c₁ d * (c₁ (t * a) * x) := by simp only [map_mul]; ring
  rw [this, e, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, h1]

theorem mem_spanBy_of_forall_height_one : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (p : Ideal R), p.IsPrime → p.height = 1 → f ∈ p → ∀ (W : Set F), (∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W) → (∀ a ∈ W, ∀ b ∈ W, a + b ∈ W) → (∀ r, ∀ a ∈ W, c₀ r * a ∈ W) → (∀ s, s ∉ p → ∀ a ∈ W, (c₀ s)⁻¹ * a ∈ W) → ∀ x ∈ spanBy c₁ (Set.range θ), (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → q.comap ρ = p → ∃ s, s ∉ q ∧ c₁ s * x ∈ spanBy c₁ (θ '' W)) → x ∈ spanBy c₁ (θ '' W) := by
  intro R R₁ F F₁ _ _ _ _ _ _ _ _ _ _ ρ c₀ c₁ θ f hf _ hρ hc₀ hcomp hlin p hp hp1 _ W hWt hWadd hWsmul hWdiv x hx hloc
  classical
  have hθ : ∀ r, θ (c₀ r) = c₁ (ρ r) := fun r => RingHom.congr_fun hcomp r
  have hc₁ : Function.Injective c₁ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have := hlin 1 (fun _ => 1) (fun g hg => by
      funext i
      have h0 : c₀ (g 0) = 0 := by simpa using hg
      rw [Subsingleton.elim i 0]
      exact (injective_iff_map_eq_zero c₀).mp hc₀ _ h0) (fun _ => r) (by simpa using hr)
    exact congrFun this 0
  have hW0 : (0 : F) ∈ W := by simpa using hWt 0
  have hWsum : ∀ (n : ℕ) (g : Fin n → R) (v : Fin n → F), (∀ i, v i ∈ W) → ∑ i, c₀ (g i) * v i ∈ W :=
    fun n g v hv => Finset.sum_induction _ (· ∈ W) (fun a b ha hb => hWadd a ha b hb) hW0
      fun i _ => hWsmul _ _ (hv i)
  have hne : ∀ t, t ∉ p → c₀ t ≠ 0 := fun t ht h =>
    ht (((injective_iff_map_eq_zero c₀).mp hc₀ _ h) ▸ p.zero_mem)
  have hρf : ρ f ≠ 0 := fun h => hf ((injective_iff_map_eq_zero ρ).mp hρ _ h)
  obtain ⟨n, r, u', hu', rfl⟩ := hx
  choose u hu using hu'
  obtain rfl : u' = fun i => θ (u i) := funext fun i => (hu i).symm
  set x := ∑ i, c₁ (r i) * θ (u i) with hxdef
  choose m hm using hWt
  let M := Finset.univ.sup fun i => m (u i)
  have hM : ∀ i, c₀ f ^ M * u i ∈ W := fun i => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.le_sup (f := fun i => m (u i)) (Finset.mem_univ i) : m (u i) ≤ M)
    have := hWsmul (f ^ d) _ (hm (u i))
    rwa [map_pow, ← mul_assoc, ← pow_add, add_comm, ← hd] at this
  let S : Submonoid R₁ := p.primeCompl.map ρ
  let G : Set (PrimeSpectrum R₁) :=
    {q | q.asIdeal.height = 1 ∧ ρ f ∈ q.asIdeal ∧ Disjoint (S : Set R₁) (q.asIdeal : Set R₁)}
  have hG : G.Finite := (GlobalTheory.finite_height_eq_one_mem hρf).subset fun q hq => ⟨hq.1, hq.2.1⟩
  have H : ∀ q : G, ∃ (s : R₁) (N : ℕ) (g : Fin N → R₁) (w : Fin N → F),
      s ∉ q.1.asIdeal ∧ (∀ l, w l ∈ W) ∧ c₁ s * x = ∑ l, c₁ (g l) * θ (w l) := by
    rintro ⟨q, h1, h2, h3⟩
    have hle : q.asIdeal.comap ρ ≤ p := fun t ht => by_contra fun htp =>
      Set.disjoint_left.mp h3 ⟨t, htp, rfl⟩ ht
    have heq : q.asIdeal.comap ρ = p :=
      le_antisymm hle ((GlobalTheory.mem_minimalPrimes_span_singleton_of_height_eq_one hp1 hf (hle h2)).2
        ⟨Ideal.comap_isPrime ρ _, (Ideal.span_singleton_le_iff_mem _).mpr h2⟩ hle)
    obtain ⟨s, hs, N, g, w', hw', e⟩ := hloc q.asIdeal q.isPrime h1 h2 heq
    choose w hw hw' using hw'
    exact ⟨s, N, g, w, hs, hw, by simp only [hw', e]⟩
  choose s N g w hs hw he using H
  haveI : Finite G := hG
  let T : Set F := Set.range (fun i => c₀ f ^ M * u i) ∪ ⋃ q : G, Set.range (w q)
  have hT : T.Finite := (Set.finite_range _).union (Set.finite_iUnion fun q => Set.finite_range _)
  have hTW : T ⊆ W := by
    rintro _ (⟨i, rfl⟩ | ⟨_, ⟨q, rfl⟩, l, rfl⟩)
    · exact hM i
    · exact hw q l
  obtain ⟨k, b, hb, hind, t, ht, hexp⟩ := exists_basis_of_finite R F c₀ hc₀ p hp hp1 T hT
  have hbW : ∀ j, b j ∈ W := fun j => by
    obtain ⟨n', g', v, t', ht', hv, e⟩ := hb j
    have := hWdiv t' ht' _ (hWsum n' g' v fun i => hTW (hv i))
    rwa [← e, inv_mul_cancel_left₀ (hne t' ht')] at this
  have key : ∀ (n' : ℕ) (g' : Fin n' → R₁) (v : Fin n' → F), (∀ i, v i ∈ T) →
      ∃ h : Fin k → R₁, c₁ (ρ t) * ∑ i, c₁ (g' i) * θ (v i) = ∑ j, c₁ (h j) * θ (b j) := by
    intro n' g' v hv
    choose h hh using fun i => hexp (v i) (hv i)
    refine ⟨fun j => ∑ i, g' i * ρ (h i j), ?_⟩
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, ← hθ, ← map_mul, hh, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hθ, mul_assoc]
  have htS : ρ t ∈ S := ⟨t, ht, rfl⟩
  obtain ⟨_, h, ⟨t₀, ht₀, rfl⟩, e⟩ := span_test R₁ F₁ c₁ hc₁ S
    (by
      rintro ⟨t₀, ht₀, e⟩
      exact ht₀ (((injective_iff_map_eq_zero ρ).mp hρ _ e) ▸ p.zero_mem))
    k (fun j => θ (b j)) (hlin k b hind) x (ρ f ^ M) (pow_ne_zero _ hρf)
    (by
      obtain ⟨h, e⟩ := key n r (fun i => c₀ f ^ M * u i) fun i => Or.inl ⟨i, rfl⟩
      refine ⟨_, h, htS, ?_⟩
      rw [← e, map_mul, mul_assoc, hxdef, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_pow, hθ, mul_left_comm])
    (by
      intro q hq h1 h2 h3
      let q' : G := ⟨⟨q, hq⟩, h1, hq.mem_of_pow_mem _ h2, h3⟩
      obtain ⟨h, e⟩ := key _ (g q') (w q') fun l => Or.inr (Set.mem_iUnion.mpr ⟨q', l, rfl⟩)
      exact ⟨s q', hs q', _, h, htS, by rw [← e, ← he, map_mul, mul_assoc]⟩)
  refine ⟨k, h, fun j => θ ((c₀ t₀)⁻¹ * b j), fun j => ⟨_, hWdiv t₀ ht₀ _ (hbW j), rfl⟩, ?_⟩
  have h0 : c₁ (ρ t₀) ≠ 0 := by rw [← hθ]; exact (map_ne_zero θ).mpr (hne t₀ ht₀)
  apply mul_left_cancel₀ h0
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  beta_reduce
  rw [map_mul, map_inv₀, hθ, mul_left_comm, mul_inv_cancel_left₀ h0]

end GlobalTheory.Desc.LocalDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemToroidalComponentClosureOfSpecializesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_toroidalComponentClosure_of_specializes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (x : Xo.XF c), x ∈ (Z : Set (Xo.XF c)) → ∀ b : Y.X, Y.j x ⤳ b → b ∈ barComp Y Z := by
  first | exact @GlobalTheory.CompHS.mem_barComp_of_specializes | exact GlobalTheory.CompHS.mem_barComp_of_specializes | (intros; apply GlobalTheory.CompHS.mem_barComp_of_specializes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRingHomComplexOfFgStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_ringHom_complex_of_fg' : ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  first | exact @GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg | exact GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg | (intros; apply GlobalTheory.FGFieldEmb.nonempty_ringHom_complex_of_fg <;> assumption)
end

