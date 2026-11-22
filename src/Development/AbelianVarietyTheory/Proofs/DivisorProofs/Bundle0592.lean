import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0013
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectivePreimage
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.GlueColim

set_option backward.isDefEq.respectTransparency false in

theorem isClosedImmersion_surjective_preimage : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0}) [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected] (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G), (∀ x : X, ∃ U ∈ 𝒰, x ∈ G U) → ∀ (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U), (∀ U, IsClosedImmersion (e U)) → (∀ U, Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → ∀ j : X ⟶ colimit F, (∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U) → IsClosedImmersion j ∧ Surjective j ∧ ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
  intro B₀ 𝒰 F _ _ X G hG hc e he hs hnat j hj
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : (G U.1).toScheme),
      F.map f (e U x) = e V (X.homOfLE (hG (show U.1 ≤ V.1 from f.le)) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat (show U.1 ≤ V.1 from f.le)]
    rfl
  have hinj : ∀ U, Function.Injective (e U) := fun U ↦ (e U).isClosedEmbedding.injective
  have key2 : ∀ {U V : 𝒰} (x : (G U.1).toScheme) (y : (G V.1).toScheme),
      colimit.ι F U (e U x) = colimit.ι F V (e V y) → x.1 = y.1 := by
    intro U V x y h
    obtain ⟨W, f, g, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := (e W).surjective z
    rw [hnat'] at h1 h2
    have h1' := congrArg Subtype.val (hinj _ h1)
    have h2' := congrArg Subtype.val (hinj _ h2)
    simp only [Scheme.homOfLE_apply] at h1' h2'
    exact h1'.symm.trans h2'
  have hj' : ∀ (U : 𝒰) (x : (G U.1).toScheme), j x.1 = colimit.ι F U (e U x) := fun U x ↦
    congr($(hj U) x)
  have hpre : ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
    intro U
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (e U).surjective y
      obtain ⟨V, hV, hxV⟩ := hc x
      have := key2 (V := ⟨V, hV⟩) y ⟨x, hxV⟩ (hy.trans (hj' ⟨V, hV⟩ ⟨x, hxV⟩))
      have h2 : y.1 = x := this
      exact h2 ▸ y.2
    · intro hx
      exact ⟨_, (hj' U ⟨x, hx⟩).symm⟩
  refine ⟨?_, ⟨?_⟩, hpre⟩
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
      (Scheme.IsLocallyDirected.openCover F)]
    intro U
    have H : IsPullback (e U) (G U.1).ι (colimit.ι F U) j :=
      IsOpenImmersion.isPullback _ _ _ _ (hj U) (by rw [hpre]; simp)
    have : pullback.snd j (colimit.ι F U) = H.flip.isoPullback.inv ≫ e U := by simp
    change IsClosedImmersion (pullback.snd j (colimit.ι F U))
    rw [this]
    infer_instance
  · intro b
    obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F b
    obtain ⟨x, rfl⟩ := (e U).surjective x
    exact ⟨_, hj' U x⟩

end GlobalTheory.GlueColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplication
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.JInt

theorem not_four_sq {u Δ : ℤ} (hu : Δ ≤ u) (hΔ : 0 < Δ) (r : ℤ) : u ^ 2 + Δ ≠ 4 * (r * r) := by
  intro h
  have h2 : (2 * |r|) ^ 2 = u ^ 2 + Δ := by rw [mul_pow, sq_abs]; linarith
  have hr0 : 0 ≤ 2 * |r| := by positivity
  have hu0 : 0 ≤ u := by linarith
  have a1 : u < 2 * |r| := by nlinarith
  have a2 : 2 * |r| < u + 1 := by nlinarith
  omega

theorem disc_pos {A B C D : ℤ} {τ : ℍ} (hC : C ≠ 0)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : 0 < -((D - A) ^ 2 + 4 * B * C) := by
  set x := (τ : ℂ).re
  set y := (τ : ℂ).im
  have hy : 0 < y := τ.im_pos
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im] at hre him
  have h1 : ((D : ℝ) - A + 2 * C * x) * y = 0 := by linear_combination -him
  have h1' : (D : ℝ) - A + 2 * C * x = 0 := (mul_eq_zero.mp h1).resolve_right hy.ne'
  have key : (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) = 4 * (C : ℝ) ^ 2 * y ^ 2 := by
    push_cast
    linear_combination (-(D : ℝ) + A - 2 * C * x) * h1' - 4 * (C : ℝ) * hre
  have hCr : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
  have : (0 : ℝ) < (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) := by rw [key]; positivity
  exact_mod_cast this

theorem main : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 →
    IsIntegral ℤ (jT τ) := by
  intro L c τ α hτ hα him
  obtain ⟨hc, hlat⟩ := hτ
  have h1 : c * (τ : ℂ) ∈ L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
  have h2 : c ∈ L.lattice := (hlat _).2 ⟨0, 1, by simp⟩
  obtain ⟨A, B, hAB⟩ := (hlat _).1 (hα _ h1)
  obtain ⟨C, D, hCD⟩ := (hlat _).1 (hα _ h2)
  have e1 : α * (τ : ℂ) = A * τ + B := by apply mul_left_cancel₀ hc; linear_combination hAB
  have e2 : α = C * τ + D := by apply mul_left_cancel₀ hc; linear_combination hCD
  have hfix : (A : ℂ) * τ + B = τ * (C * τ + D) := by rw [← e1, e2]; ring
  have hC : C ≠ 0 := by
    rintro rfl
    apply him; rw [e2]; simp
  have hΔ := disc_pos hC hfix
  set Δ := -((D - A) ^ 2 + 4 * B * C) with hΔdef
  set t := A + D
  set k := Δ + |t|
  set M := (A + k) * (D + k) - B * C with hM
  have h4M : 4 * M = (2 * k + t) ^ 2 + Δ := by rw [hM, hΔdef]; ring
  have hu : Δ ≤ 2 * k + t := by
    have := neg_abs_le t; have := abs_nonneg t; linarith
  have hMpos : 0 < M := by nlinarith
  have hm : 0 < M.toNat := by omega
  have hMc : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hMpos.le
  refine jT_isIntegral hm ?_ (Gm_vanish hm τ (A + k) B C (D + k) (by rw [hMc]) ?_)
  · rintro ⟨r, hr⟩
    have : M = (r : ℤ) * r := by rw [← hMc, hr]; push_cast; ring
    exact not_four_sq hu hΔ r (by rw [← h4M, this])
  · push_cast; linear_combination hfix

end GlobalTheory.JInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAwayFib
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem isLocalization_away_eqLocus {A B C A' B' C' : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing A'] [CommRing B'] [CommRing C'] (f : B →+* A) (g : C →+* A)
    (f' : B' →+* A') (g' : C' →+* A') (ρA : A →+* A') (ρB : B →+* B') (ρC : C →+* C')
    (hB : f'.comp ρB = ρA.comp f) (hC : g'.comp ρC = ρA.comp g)
    (x : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)))
    (φ : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)) →+*
      RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')))
    (hφ : ∀ y, (φ y : B' × C') = (ρB (y : B × C).1, ρC (y : B × C).2))
    (hlB : letI := ρB.toAlgebra; IsLocalization.Away (x : B × C).1 B')
    (hlC : letI := ρC.toAlgebra; IsLocalization.Away (x : B × C).2 C')
    (hlA : letI := ρA.toAlgebra; IsLocalization.Away (f (x : B × C).1) A') :
    letI := φ.toAlgebra
    IsLocalization.Away x
      (RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C'))) := by
  letI := ρB.toAlgebra
  letI := ρC.toAlgebra
  letI := ρA.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨⟨b, c⟩, hx⟩ := x
  have hx' : f b = g c := hx
  have eB : ∀ y, f' (ρB y) = ρA (f y) := fun y ↦ RingHom.congr_fun hB y
  have eC : ∀ y, g' (ρC y) = ρA (g y) := fun y ↦ RingHom.congr_fun hC y
  have hfst : ∀ y, ((φ y : B' × C')).1 = ρB (y : B × C).1 := fun y ↦ by rw [hφ]
  have hsnd : ∀ y, ((φ y : B' × C')).2 = ρC (y : B × C).2 := fun y ↦ by rw [hφ]
  have hpow : ∀ (y : RingHom.eqLocus (f.comp (RingHom.fst B C)) (g.comp (RingHom.snd B C)))
      (k : ℕ), ((y ^ k : RingHom.eqLocus (f.comp (RingHom.fst B C))
        (g.comp (RingHom.snd B C))) : B × C) = ((y : B × C).1 ^ k, (y : B × C).2 ^ k) :=
    fun y k ↦ by rw [SubmonoidClass.coe_pow, Prod.pow_def]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  ·
    have hu : IsUnit (φ ⟨(b, c), hx⟩) := by
      obtain ⟨u₁, hu₁⟩ := IsLocalization.Away.algebraMap_isUnit (S := B') b
      obtain ⟨u₂, hu₂⟩ := IsLocalization.Away.algebraMap_isUnit (S := C') c
      have hu₁' : (u₁ : B') = ρB b := hu₁
      have hu₂' : (u₂ : C') = ρC c := hu₂
      have e0 : f' u₁ = g' u₂ := by rw [hu₁', hu₂', eB, eC, hx']
      have e1 : f' ↑u₁⁻¹ = g' ↑u₂⁻¹ := by
        calc f' ↑u₁⁻¹ = f' ↑u₁⁻¹ * (g' u₂ * g' ↑u₂⁻¹) := by
                rw [← map_mul, Units.mul_inv, map_one, mul_one]
          _ = f' ↑u₁⁻¹ * f' u₁ * g' ↑u₂⁻¹ := by rw [e0, mul_assoc]
          _ = g' ↑u₂⁻¹ := by rw [← map_mul, Units.inv_mul, map_one, one_mul]
      refine isUnit_iff_exists_inv.mpr ⟨⟨(↑u₁⁻¹, ↑u₂⁻¹), e1⟩, ?_⟩
      apply Subtype.ext
      change (φ ⟨(b, c), hx⟩ : B' × C') * ((↑u₁⁻¹ : B'), (↑u₂⁻¹ : C')) = (1 : B' × C')
      rw [hφ]
      ext
      · change ρB b * ↑u₁⁻¹ = 1
        rw [← hu₁', Units.mul_inv]
      · change ρC c * ↑u₂⁻¹ = 1
        rw [← hu₂', Units.mul_inv]
    rintro ⟨_, n, rfl⟩
    change IsUnit (φ (⟨(b, c), hx⟩ ^ n))
    rw [map_pow]
    exact hu.pow n
  ·
    rintro ⟨⟨z₁, z₂⟩, hz⟩
    have hz' : f' z₁ = g' z₂ := hz
    obtain ⟨n₁, y₁, h₁⟩ := IsLocalization.Away.surj b z₁
    obtain ⟨n₂, y₂, h₂⟩ := IsLocalization.Away.surj c z₂
    have h₁' : z₁ * ρB b ^ (n₁ + n₂) = ρB (y₁ * b ^ n₂) := by
      change z₁ * ρB b ^ n₁ = ρB y₁ at h₁
      rw [pow_add, ← mul_assoc, h₁, map_mul, map_pow]
    have h₂' : z₂ * ρC c ^ (n₁ + n₂) = ρC (y₂ * c ^ n₁) := by
      change z₂ * ρC c ^ n₂ = ρC y₂ at h₂
      rw [add_comm, pow_add, ← mul_assoc, h₂, map_mul, map_pow]
    have hA : algebraMap A A' (f (y₁ * b ^ n₂)) = algebraMap A A' (g (y₂ * c ^ n₁)) := by
      change ρA _ = ρA _
      have k₁ := congrArg f' h₁'
      have k₂ := congrArg g' h₂'
      rw [map_mul, map_pow, eB, eB] at k₁
      rw [map_mul, map_pow, eC, eC] at k₂
      rw [← k₁, ← k₂, hz', hx']
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (f b)) hA
    change f b ^ m * f (y₁ * b ^ n₂) = f b ^ m * g (y₂ * c ^ n₁) at hm
    have hmem : f (b ^ m * (y₁ * b ^ n₂)) = g (c ^ m * (y₂ * c ^ n₁)) := by
      rw [map_mul f (b ^ m), map_pow f, hm, map_mul g (c ^ m), map_pow g, hx']
    refine ⟨(⟨(b ^ m * (y₁ * b ^ n₂), c ^ m * (y₂ * c ^ n₁)), hmem⟩,
      ⟨⟨(b, c), hx⟩ ^ (m + (n₁ + n₂)), m + (n₁ + n₂), rfl⟩), ?_⟩
    apply Subtype.ext
    change ((⟨(z₁, z₂), hz⟩ : RingHom.eqLocus _ _) : B' × C') * (φ (⟨(b, c), hx⟩ ^ (m + (n₁ + n₂))) : B' × C') = (φ _ : B' × C')
    rw [hφ, hφ, hpow]
    ext
    · change z₁ * ρB (b ^ (m + (n₁ + n₂))) = ρB (b ^ m * (y₁ * b ^ n₂))
      rw [map_mul, ← h₁']
      simp only [map_pow]
      ring
    · change z₂ * ρC (c ^ (m + (n₁ + n₂))) = ρC (c ^ m * (y₂ * c ^ n₁))
      rw [map_mul, ← h₂']
      simp only [map_pow]
      ring
  ·
    intro y y' e
    have e' : φ y = φ y' := e
    have e₁ : algebraMap B B' (y : B × C).1 = algebraMap B B' (y' : B × C).1 := by
      change ρB _ = ρB _
      rw [← hfst, ← hfst]; exact congrArg (fun t : RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')) ↦ (t : B' × C').1) e'
    have e₂ : algebraMap C C' (y : B × C).2 = algebraMap C C' (y' : B × C).2 := by
      change ρC _ = ρC _
      rw [← hsnd, ← hsnd]; exact congrArg (fun t : RingHom.eqLocus (f'.comp (RingHom.fst B' C')) (g'.comp (RingHom.snd B' C')) ↦ (t : B' × C').2) e'
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers b) e₁
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers c) e₂
    change b ^ n * _ = b ^ n * _ at hn
    change c ^ k * _ = c ^ k * _ at hk
    refine ⟨⟨⟨(b, c), hx⟩ ^ (n + k), n + k, rfl⟩, ?_⟩
    apply Subtype.ext
    change ((⟨(b, c), hx⟩ ^ (n + k) : RingHom.eqLocus _ _) : B × C) * (y : B × C) =
      ((⟨(b, c), hx⟩ ^ (n + k) : RingHom.eqLocus _ _) : B × C) * (y' : B × C)
    rw [hpow]
    ext
    · change b ^ (n + k) * _ = b ^ (n + k) * _
      calc b ^ (n + k) * (y : B × C).1 = b ^ k * (b ^ n * (y : B × C).1) := by ring
        _ = b ^ k * (b ^ n * (y' : B × C).1) := by rw [hn]
        _ = _ := by ring
    · change c ^ (n + k) * _ = c ^ (n + k) * _
      calc c ^ (n + k) * (y : B × C).2 = c ^ n * (c ^ k * (y : B × C).2) := by ring
        _ = c ^ n * (c ^ k * (y' : B × C).2) := by rw [hk]
        _ = _ := by ring

end GlobalTheory.FerrandPush

namespace GlobalTheory.FerrandPush

section Geo
variable {Y₀ Y₁ Y₂ : Scheme.{0}}

theorem upOpen_basicOpen (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i] (U : Y₀.Opens)
    (s : Γ(Y₁, upOpen i U)) : upOpen i (Y₀.basicOpen ((res i U).hom s)) = Y₁.basicOpen s := by
  have h1 : Y₀.basicOpen ((res i U).hom s) = U ⊓ i ⁻¹ᵁ Y₁.basicOpen s :=
    Scheme.basicOpen_appLE i U (upOpen i U) (preimage_upOpen i U).ge s
  have h2 : i ⁻¹ᵁ Y₁.basicOpen s ≤ U :=
    le_trans ((Scheme.Hom.preimage_mono i) (Y₁.basicOpen_le s)) (preimage_upOpen i U).le
  rw [h1, inf_eq_right.mpr h2, upOpen_preimage]

variable (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁]
  [IsClosedImmersion i₂] [Surjective i₂]

theorem fibπ_apply (U : Y₀.Opens) (a : (fib i₁ i₂).obj (op U)) :
    ((fibπ i₁ i₂).app (op U)).hom a = (res i₁ U).hom ((cone i₁ i₂ U).fst.hom a) :=
  rfl

end Geo
end GlobalTheory.FerrandPush

namespace GlobalTheory.FerrandPush

theorem isLocalization_away_fib : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂],
    ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U),
    letI := ((GlobalTheory.FerrandPush.fib i₁ i₂).map (homOfLE (Y₀.basicOpen_le
      (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a))).op).hom.toAlgebra;
    IsLocalization.Away a ((GlobalTheory.FerrandPush.fib i₁ i₂).obj
      (op (Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a)))) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ _ U hU a
  obtain ⟨hU0, hU1, hU2⟩ := hU
  have hD : Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a) ≤ U := Y₀.basicOpen_le _
  have hs2 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₂ U).hom ((cone i₁ i₂ U).snd.hom a) := a.2
  have e1 : upOpen i₁ (Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a)) =
      Y₁.basicOpen ((cone i₁ i₂ U).fst.hom a) := upOpen_basicOpen i₁ U _
  have e2 : upOpen i₂ (Y₀.basicOpen (((fibπ i₁ i₂).app (op U)).hom a)) =
      Y₂.basicOpen ((cone i₁ i₂ U).snd.hom a) := by
    rw [hs2]; exact upOpen_basicOpen i₂ U _
  exact isLocalization_away_eqLocus (res i₁ U).hom (res i₂ U).hom (res i₁ _).hom (res i₂ _).hom
    (Y₀.presheaf.map (homOfLE hD).op).hom (Y₁.presheaf.map (homOfLE (upOpen_mono i₁ hD)).op).hom
    (Y₂.presheaf.map (homOfLE (upOpen_mono i₂ hD)).op).hom
    (congrArg CommRingCat.Hom.hom (res_naturality i₁ hD))
    (congrArg CommRingCat.Hom.hom (res_naturality i₂ hD)) a
    ((fib i₁ i₂).map (homOfLE hD).op).hom (fun _ ↦ rfl)
    (hU1.isLocalization_of_eq_basicOpen _ (homOfLE (upOpen_mono i₁ hD)) e1)
    (hU2.isLocalization_of_eq_basicOpen _ (homOfLE (upOpen_mono i₂ hD)) e2)
    (hU0.isLocalization_of_eq_basicOpen _ (homOfLE hD) rfl)

end GlobalTheory.FerrandPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecMapOfThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.ThickGlue

set_option backward.isDefEq.respectTransparency false in

theorem isOpenImmersion_specMap_of_thickening : ∀ (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, IsAffineOpen U) → ∀ (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) (π : 𝒜 ⟶ B₀.presheaf), (∀ U ∈ 𝒰, Function.Surjective (π.app (op U)).hom ∧ IsNilpotent (RingHom.ker (π.app (op U)).hom)) → (∀ U ∈ 𝒰, ∀ a : 𝒜.obj (op U), letI := (𝒜.map (homOfLE (B₀.basicOpen_le ((π.app (op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a (𝒜.obj (op (B₀.basicOpen ((π.app (op U)).hom a))))) → ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V, IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
  intro B₀ 𝒰 haff 𝒜 p hp hloc
  have hloc' : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (Opposite.op U)) (W : B₀.Opens)
      (_ : W = B₀.basicOpen ((p.app (Opposite.op U)).hom a)) (h : W ≤ U),
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    rintro U hU a W rfl h
    letI := (𝒜.map (homOfLE h).op).hom.toAlgebra
    haveI := hloc U hU a
    exact IsOpenImmersion.of_isLocalization
      (S := 𝒜.obj (Opposite.op (B₀.basicOpen ((p.app (Opposite.op U)).hom a)))) a
  have hci : ∀ U ∈ 𝒰, IsClosedImmersion (toSpec p U) := fun U hU ↦
    isClosedImmersion_toSpec p (haff U hU) (hp U hU).1
  have hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U) := fun U hU ↦
    surjective_toSpec p (haff U hU) (hp U hU).1 (hp U hU).2
  have hnat : ∀ {U V : B₀.Opens} (h : U ≤ V) (x : U.toScheme),
      Spec.map (𝒜.map (homOfLE h).op) (toSpec p U x) = toSpec p V (B₀.homOfLE h x) :=
    fun h x ↦ congr($(toSpec_naturality p h) x).symm
  intro U hU V hV h
  have := hci V hV
  have := hsu U hU
  apply IsOpenImmersion.of_forall_source_exists
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
    obtain ⟨y, rfl⟩ := (toSpec p U).surjective y
    rw [hnat, hnat] at hxy
    rw [(B₀.homOfLE h).isOpenEmbedding.injective
      ((toSpec p V).isClosedEmbedding.injective hxy)]
  · intro x
    obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
    obtain ⟨f, hf, hxf⟩ := (haff V hV).exists_basicOpen_le (V := U) ⟨x.1, x.2⟩ (h x.2)
    obtain ⟨a, rfl⟩ := (hp V hV).1 f
    have h1 := hloc' U hU ((𝒜.map (homOfLE h).op).hom a) _ (by
      have := congr($(p.naturality (homOfLE h).op).hom a)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [this, Scheme.basicOpen_res]
      exact (inf_eq_right.mpr hf).symm) hf
    refine ⟨_, _, h1, ⟨toSpec p _ ⟨x.1, hxf⟩, ?_⟩, ?_⟩
    · rw [hnat]
      congr 1
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← Spec.map_comp, ← 𝒜.map_comp]
      exact hloc' V hV a _ rfl (hf.trans h)

end GlobalTheory.ThickGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTauOfUpperHalfPlaneLatticeSmulSL2Z
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.TauSmul

theorem main : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
    IsTauOf (tauPair (γ • τ)) (UpperHalfPlane.denom γ τ)⁻¹ τ ∧ IsTauOf (tauPair τ) 1 τ := by
  intro γ τ
  have hne : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  have hd : UpperHalfPlane.denom γ τ = (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) := ModularGroup.denom_apply γ τ
  have hs : ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  refine ⟨⟨inv_ne_zero hne, fun x => ?_⟩, one_ne_zero, fun x => ?_⟩
  · rw [PeriodPair.mem_lattice]
    simp only [tauPair]
    rw [hs, hd]
    rw [hd] at hne
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m * γ 0 0 + n * γ 1 0, m * γ 0 1 + n * γ 1 1, ?_⟩
      push_cast
      rw [eq_inv_mul_iff_mul_eq₀ hne]
      field_simp
      ring
    · rintro ⟨u, v, rfl⟩
      refine ⟨u * γ 1 1 - v * γ 1 0, v * γ 0 0 - u * γ 0 1, ?_⟩
      push_cast
      rw [eq_inv_mul_iff_mul_eq₀ hne]
      field_simp
      linear_combination ((u : ℂ) * τ + v) * hdet
  · rw [PeriodPair.mem_lattice]
    simp only [tauPair, mul_one, one_mul]
    exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

end GlobalTheory.TauSmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
section
noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve (scheme ptHom IsUnimodularSol)

namespace GlobalTheory.CMTorsion

def curve (Λ : PeriodPair) (Ω : ℂ) : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(Λ.g₂ / Ω ^ 4 / 4), -(Λ.g₃ / Ω ^ 6 / 4)⟩

open Classical in

def coords (Λ : PeriodPair) (Ω : ℂ) (z : ℂ) : Fin 3 → ℂ :=
  if z ∈ Λ.lattice then ![0, 1, 0] else ![Λ.weierstrassP z / Ω ^ 2, Λ.derivWeierstrassP z / (2 * Ω ^ 3), 1]

theorem isUnimodularSol_coords (Λ : PeriodPair) (Ω z : ℂ) :
    IsUnimodularSol ((curve Λ Ω).map (RingHom.id ℂ)) (coords Λ Ω z) := by
  rw [WeierstrassCurve.map_id]
  unfold coords
  split_ifs with hz
  · exact GlobalTheory.WeierstrassCurve.isUnimodularSol_zero _
  · refine GlobalTheory.WeierstrassCurve.isUnimodularSol_some ?_
    rw [WeierstrassCurve.Affine.equation_iff]
    have h := Λ.derivWeierstrassP_sq z hz
    simp only [curve]
    by_cases hΩ : Ω = 0
    · subst hΩ; simp
    · field_simp
      linear_combination 4 * h

def pt (Λ : PeriodPair) (Ω : ℂ) (z : ℂ) : Sp ℂ ⟶ scheme (curve Λ Ω) :=
  ptHom (curve Λ Ω) (RingHom.id ℂ) (coords Λ Ω z) (isUnimodularSol_coords Λ Ω z)

theorem isUnimodularSol_tan (W : WeierstrassCurve ℂ) (c : ℂ) :
    IsUnimodularSol (W.map (algebraMap ℂ (DualNumber ℂ))) ![c • DualNumber.eps, -1, 0] := by
  refine GlobalTheory.WeierstrassCurve.isUnimodularSol_origin ?_
  rw [GlobalTheory.WeierstrassCurve.equation_origin_iff]
  have : (c • DualNumber.eps : DualNumber ℂ) ^ 3 = 0 := by
    rw [pow_succ, pow_two, smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero, zero_mul]
  simp [this]

def tan (W : WeierstrassCurve ℂ) (c : ℂ) : Sp (DualNumber ℂ) ⟶ scheme W :=
  ptHom W (algebraMap ℂ (DualNumber ℂ)) ![c • DualNumber.eps, -1, 0] (isUnimodularSol_tan W c)

theorem curve_map {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ} (g : ℂ →+* ℂ) (h₂ : g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4)
    (h₃ : g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6) : (curve Λ₀ Ω₀).map g = curve Λ₁ Ω₁ := by
  ext <;> simp [curve, h₂, h₃, map_neg, map_div₀, map_ofNat]

end GlobalTheory.CMTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem jT_eq_latDisc (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) :
    jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ :=
  (ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT h).symm

theorem pow_twelve_eq_DD (Λ : PeriodPair) (c : ℂ) (τ : ℍ) (h : IsTauOf Λ c τ) (Ω : ℂ)
    (hΩ : Ω ^ 12 = latDisc Λ) : (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ := by
  have hc : c ≠ 0 := h.1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ^ 12 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Complex.I_pow_four, one_pow]
  have hd : latDisc Λ = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ :=
    ReciprocityTheory.ChartRestriction.L1.disc_eq h
  rw [div_pow, mul_pow, mul_pow, mul_pow, hI, hΩ, hd]
  field_simp
  ring

theorem jT_eq_and_pow_twelve_eq_DD : ∀ (Λ : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf Λ c τ → jT τ = 1728 * Λ.g₂ ^ 3 / latDisc Λ ∧ ∀ Ω : ℂ, Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ :=
  fun Λ c τ h => ⟨jT_eq_latDisc Λ c τ h, pow_twelve_eq_DD Λ c τ h⟩

end GlobalTheory.QFam
end

