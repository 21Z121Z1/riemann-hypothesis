import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalUnitMono
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.FockParseval

open MvPolynomial GlobalTheory.FockSeq

variable {σ : Type} [DecidableEq σ]

def unitMono (F : Fock σ) (α : σ →₀ ℕ) : F.H := (wt α)⁻¹ • F.ι (monomial α 1)

omit [DecidableEq σ] in

theorem conj_wt (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := Complex.conj_ofReal _

omit [DecidableEq σ] in

theorem wt_mul_self (α : σ →₀ ℕ) : wt α * wt α = (mfact α : ℕ) := by
  rw [← star_wt_mul, conj_wt]

theorem orthonormal_unitMono (F : Fock σ) : Orthonormal ℂ (unitMono F) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  rw [unitMono, unitMono, inner_smul_left, inner_smul_right, F.fockIP, ← mfact_cast, map_inv₀, conj_wt]
  by_cases h : α = β
  · subst h
    have := wt_ne_zero α
    rw [if_pos rfl, if_pos rfl, ← wt_mul_self]
    field_simp
  · simp [h]

theorem dense_span_unitMono (F : Fock σ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (unitMono F))).topologicalClosure := by
  intro x _
  refine closure_mono ?_ (F.dense x)
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | monomial α c =>
    have e : F.ι (monomial α c) = (c * wt α) • unitMono F α := by
      rw [unitMono, smul_smul, mul_assoc, mul_inv_cancel₀ (wt_ne_zero α), mul_one, ← map_smul, smul_monomial]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

theorem inner_unitMono {F : Fock σ} {v : F.H} {E : MvPowerSeries σ ℂ} (h : HasCoeff F v E) (α : σ →₀ ℕ) :
    inner ℂ (unitMono F α) v = wt α * MvPowerSeries.coeff α E := by
  have := wt_ne_zero α
  rw [unitMono, inner_smul_left, h α, ← mfact_cast, map_inv₀, conj_wt, ← wt_mul_self]
  field_simp

theorem parseval (σ : Type) [DecidableEq σ] (F : Fock σ) (v w : F.H) (E E' : MvPowerSeries σ ℂ)
    (hv : HasCoeff F v E) (hw : HasCoeff F w E') :
    Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E‖ ^ 2) ∧
      inner ℂ v w = ∑' α : σ →₀ ℕ, (GlobalTheory.FockSeq.mfact α : ℂ) * (starRingEnd ℂ) (MvPowerSeries.coeff α E) *
        MvPowerSeries.coeff α E' := by
  refine ⟨((orthonormal_unitMono F).inner_products_summable v).congr fun α => ?_, ?_⟩
  · rw [inner_unitMono hv, norm_mul, mul_pow, wt, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  · let b := HilbertBasis.mk (orthonormal_unitMono F) (dense_span_unitMono F)
    rw [← b.tsum_inner_mul_inner v w]
    refine tsum_congr fun α => ?_
    rw [HilbertBasis.coe_mk, ← inner_conj_symm, inner_unitMono hv, inner_unitMono hw, map_mul, conj_wt,
      ← wt_mul_self]
    ring

end GlobalTheory.FockParseval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjConjLevelLeIntegralGLAtTypePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2.IdxEx

theorem jat_le_stab_lamY {X : Fields} {Pr : Primes X} {R : Ranks} (sharp : Bool) (j : ℕ)
    (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Pr.vGs) (g : AutY X R j) (hg : g ∈ Jat (Pr := Pr) sharp j P) :
    g ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) := by
  unfold Jat at hg
  rw [if_pos hP] at hg
  unfold lamYat
  rw [if_pos hP]
  split_ifs at hg
  · exact hg.1
  · exact hg.1

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P), prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  intro X Pr R sharp j P hP h hh g hg
  obtain ⟨r, ⟨-, hr⟩, hrg⟩ := hg
  have e : (MulAut.conj h⁻¹).toMonoidHom r = h⁻¹ * r * h := by simp
  have hr' : (MulAut.conj h⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) sharp j P := hr
  rw [e] at hr'
  have h1 := jat_le_stab_lamY sharp j P hP _ hr'
  have h2 := mul_mem (mul_mem hh h1) (inv_mem hh)
  have e2 : h * (h⁻¹ * r * h) * h⁻¹ = r := by group
  rw [e2] at h2
  unfold lamYat at h2
  rw [if_pos hP] at h2
  have key : ∀ x : Sp X.E (R.N j), Loc.inX X.E (R.N j) (cOf R j) x ∈
      LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1) ↔ x ∈ stdAt X.E (R.N j) P := fun x =>
    ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
      GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩
  intro x
  have h3 := h2 (Loc.inX X.E (R.N j) (cOf R j) x)
  rw [hrg x] at h3
  exact (key _).symm.trans (h3.trans (key _))

end GlobalTheory.Mem.Col2.IdxEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldSplitsInOfIsRayPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem not_isUnit_natCast {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) : ¬ IsUnit (p : 𝓞 K) := by
  intro h
  have : IsLocalHom (algebraMap ℤ (𝓞 K)) := Algebra.IsIntegral.isLocalHom _ _
  rw [← map_natCast (algebraMap ℤ (𝓞 K))] at h
  exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ h)

theorem rayField_splitsIn_of_isRayPrime (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M)
    (hf : FiniteDimensional ℚ M) :
    letI := GlobalTheory.ParRay.algK D jE h
    haveI := GlobalTheory.ParRay.nfOf hf
    GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) →
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn M p := by
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  intro hM p hp
  obtain ⟨hpp, π, hπK, hπi, hπc, σ, hσ⟩ := hp
  have hc0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
    exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
  let φ : D.host.K →+* Qb := jE.comp (D.host.K.val : D.host.K →+* D.host.E)
  have hφ : Function.Injective φ := jE.injective.comp Subtype.val_injective
  have hint : ∀ z : D.host.K, IsIntegral ℤ (φ z) → IsIntegral ℤ z := fun z hz =>
    (isIntegral_algHom_iff φ.toIntAlgHom hφ).1 hz
  have hmem : ∀ w : Qb, w ∈ KQbar D jE → ∃ z : D.host.K, φ z = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := (IntermediateField.mem_map _).1 hw
    exact ⟨⟨z, hz⟩, rfl⟩
  have hp0 : (p : Qb) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hπ0 : π ≠ 0 := left_ne_zero_of_mul (hσ ▸ hp0)
  have hσπ : σ π = p / π := by rw [← hσ, mul_div_cancel_left₀ _ hπ0]
  have hσK : σ π ∈ KQbar D jE := hσπ ▸ div_mem (natCast_mem _ p) hπK
  obtain ⟨x, hx⟩ := hmem π hπK
  obtain ⟨y, hy⟩ := hmem (σ π) hσK
  let σZ : Qb →ₐ[ℤ] Qb := σ.toRingHom.toIntAlgHom
  let a : 𝓞 D.host.K := ⟨x, hint x (hx ▸ hπi)⟩
  let b : 𝓞 D.host.K := ⟨y, hint y (hy ▸ hπi.map σZ)⟩

  have hab : a * b = p := by
    apply RingOfIntegers.coe_injective
    apply hφ
    rw [map_mul, map_natCast, map_mul, map_natCast]
    show φ x * φ y = _
    rw [hx, hy, hσ]

  have hdvd : ∀ z : 𝓞 D.host.K,
      IsIntegral ℤ ((φ z - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) →
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.K) ∣ z - 1 := by
    intro z hz
    set c : ℕ := D.host.QS * D.host.q * D.host.d
    have hcK : (c : D.host.K) ≠ 0 := by exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
    have hφw : φ (((z : D.host.K) - 1) / c) = (φ z - 1) / c := by
      rw [map_div₀, map_sub, map_one, map_natCast]
    let w : 𝓞 D.host.K := ⟨((z : D.host.K) - 1) / c, hint _ (hφw ▸ hz)⟩
    refine ⟨w, RingOfIntegers.coe_injective ?_⟩
    show (z : D.host.K) - 1 = (c : D.host.K) * (((z : D.host.K) - 1) / c)
    rw [mul_div_cancel₀ _ hcK]
  have hca := hdvd a (by show IsIntegral ℤ ((φ x - 1) / _); rw [hx]; exact hπc)
  have hcb := hdvd b (by
    show IsIntegral ℤ ((φ y - 1) / _)
    have e : σZ ((π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) =
        (σ π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) := by
      show σ _ = _
      rw [map_div₀, map_sub, map_one, map_natCast]
    rw [hy, ← e]
    exact hπc.map σZ)

  have hpu : ¬ IsUnit (p : 𝓞 D.host.K) := not_isUnit_natCast hpp
  have hunit : ∀ (z : 𝓞 D.host.K), (z : D.host.K) ≠ 0 → IsIntegral ℤ (φ z)⁻¹ → IsUnit z := by
    intro z hz0 hz
    have hi : IsIntegral ℤ ((z : D.host.K)⁻¹) := hint _ (by rw [map_inv₀]; exact hz)
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝓞 D.host.K) (RingOfIntegers.coe_injective ?_)
    show (z : D.host.K) * (z : D.host.K)⁻¹ = 1
    exact mul_inv_cancel₀ hz0
  have hinv : ∀ (z : 𝓞 D.host.K), IsUnit z → IsIntegral ℤ (φ z)⁻¹ := by
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    have h1 : (algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K) =
        ((algebraMap (𝓞 D.host.K) D.host.K) (u : 𝓞 D.host.K))⁻¹ :=
      map_units_inv (algebraMap (𝓞 D.host.K) D.host.K) u
    have h2 : φ ((algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K)) =
        (φ ((u : 𝓞 D.host.K) : D.host.K))⁻¹ := by
      rw [h1, map_inv₀]
    rw [← h2]
    exact (RingOfIntegers.isIntegral_coe _).map φ.toIntAlgHom
  have hx0 : (x : D.host.K) ≠ 0 := fun h0 => hπ0 (by rw [← hx, h0, map_zero])
  have hy0 : (y : D.host.K) ≠ 0 := fun h0 => hp0 (by rw [← hσ, ← hy, h0, map_zero, mul_zero])
  have hu : ¬ IsUnit a := fun ha => hpu (by
    have h1 := (hinv a ha).map σZ
    have h2 : σZ (φ x)⁻¹ = (φ y)⁻¹ := by
      show σ (φ x)⁻¹ = _
      rw [map_inv₀, hx, hy]
    rw [← hab]
    exact ha.mul (hunit b hy0 (h2 ▸ h1)))
  have hu' : ¬ IsUnit b := fun hb => hpu (by
    haveI : Algebra.IsAlgebraic ℚ Qb := by
      unfold Qb; convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
    let τ : Qb ≃ₐ[ℚ] Qb := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
    let τZ : Qb →ₐ[ℤ] Qb := τ.symm.toRingEquiv.toRingHom.toIntAlgHom
    have h1 := (hinv b hb).map τZ
    have h2 : τZ (φ y)⁻¹ = (φ x)⁻¹ := by
      show τ.symm (φ y)⁻¹ = _
      rw [map_inv₀, hy, hx]
      congr 1
      exact τ.symm_apply_apply π
    rw [← hab]
    exact (hunit a hx0 (h2 ▸ h1)).mul hb)

  have hpc : ¬ p ∣ D.host.QS * D.host.q * D.host.d := fun hd => hpu (by
    have h1 : (p : 𝓞 D.host.K) ∣ a - 1 := (Nat.cast_dvd_cast hd).trans hca
    have h2 : (p : 𝓞 D.host.K) ∣ b - 1 := (Nat.cast_dvd_cast hd).trans hcb
    have h3 : (1 : 𝓞 D.host.K) = p - (a * (b - 1) + (a - 1)) := by rw [← hab]; ring
    exact isUnit_of_dvd_one (h3 ▸ dvd_sub dvd_rfl (dvd_add (h2.mul_left _) h1)))
  have hd : ¬ (p : ℤ) ∣ discr M := fun hd => hpc (GlobalTheory.Mem.RaySplit.unr_of_ray hM p hpp hd)
  exact (GlobalTheory.HostSplit.ncard_placesOver M hpp).trans
    (GlobalTheory.Mem.RaySplit.ncard_primesOver_eq hM (GlobalTheory.Mem.RaySplit.isEmpty_real D.host)
      (GlobalTheory.Mem.RaySplit.finrank_K D.host) hpp hd hab hu hu' hca hcb)

end GlobalTheory.ParRay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityMemRayClassFieldOfMultipleStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootsOfUnity_mem_rayClassField_of_multiple : ∀ (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L] [IsGalois K L] (𝔮 : Ideal (𝓞 K)) (p : ℕ), p ≠ 0 → 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → IsRayField K M 𝔮 → Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧ IsFrob L v σ} = ⊤ → (∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p]) → ∀ ζ : L, ζ ^ p = 1 → ζ ∈ Set.range (algebraMap M L) := by
  first | exact @GlobalTheory.Mem.RayZeta.root_mem_rayField | exact GlobalTheory.Mem.RayZeta.root_mem_rayField | (intros; apply GlobalTheory.Mem.RayZeta.root_mem_rayField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnLevelAtTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.TwistRowMul

open GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

theorem isUnit_of_reduction_mul {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {a b c : E} (h : redP P c = redP P a * redP P b) : LocE.unitV ξ c = LocE.unitV ξ a * LocE.unitV ξ b := by
  unfold LocE.unitV
  by_cases hc : IsUnit (redP P c)
  · have hab := hc
    rw [h] at hab
    have ha : IsUnit (redP P a) := isUnit_of_mul_isUnit_left hab
    have hb : IsUnit (redP P b) := isUnit_of_mul_isUnit_right hab
    rw [dif_pos ha, dif_pos hb, dif_pos hc, ← Units.val_mul, ← map_mul]
    have : hc.unit = ha.unit * hb.unit := Units.ext (by simpa using h)
    rw [this]
  · rw [dif_neg hc]
    by_cases ha : IsUnit (redP P a)
    · by_cases hb : IsUnit (redP P b)
      · exact absurd (h ▸ ha.mul hb) hc
      · rw [dif_neg hb, mul_zero]
    · rw [dif_neg ha, zero_mul]

variable [StarRing E]

theorem mem_parL' (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (x : Sp E (n + c)) :
    x ∈ LocE.parL P q kj n c ↔
      ∀ i : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ i.1 ∧ i.1 < n then (1 : ℤ) else 0))⁻¹ * x i) := by
  unfold LocE.parL LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt]
  rfl

theorem block_mul' (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (kj n c : ℕ)
    {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ stabL E (n + c) (stdAt E (n + c) P))
    (hg' : g' ∈ stabL E (n + c) (stdAt E (n + c) P)) (hp : g ∈ stabL E (n + c) (LocE.parL P q kj n c)) :
    (redHom P).mapMatrix (blockD P kj n hg * blockD P kj n hg') =
      (redHom P).mapMatrix (blockD P kj n (mul_mem hg hg')) := by
  ext s t
  have hs0 : kj + s.1 < n := by have := s.2; omega
  have hs : kj + s.1 < n + c := by omega
  set v : Sp E (n + c) := g' (Loc.eN E (n + c) (kj + t.1)) with hv
  have hvi : ∀ i, IntAt P (v i) := (GlobalTheory.TwistRowType.mem_stdAt P _).1 ((hg' _).2 (eN_mem P _ _))
  set w : Sp E (n + c) := fun l => if kj ≤ l.1 ∧ l.1 < n then 0 else v l with hw
  have hdec : v = w + ∑ u : Fin (n - kj), Loc.atN v (kj + u.1) • Loc.eN E (n + c) (kj + u.1) := by
    funext l
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Loc.eN, hw, smul_eq_mul]
    by_cases hl : kj ≤ l.1 ∧ l.1 < n
    · have hl2 := l.2
      rw [if_pos hl, zero_add, Finset.sum_eq_single (⟨l.1 - kj, by omega⟩ : Fin (n - kj))]
      · have e : kj + (l.1 - kj) = l.1 := by omega
        simp only [e, if_true, mul_one, Loc.atN]
        rw [dif_pos hl2]
      · intro u _ hu
        rw [if_neg, mul_zero]
        intro h
        apply hu
        apply Fin.ext
        simp only
        omega
      · simp
    · rw [if_neg hl, Finset.sum_eq_zero, add_zero]
      intro u _
      have := u.2
      rw [if_neg (by omega), mul_zero]
  have hwp : w ∈ LocE.parL P q kj n c := by
    rw [mem_parL']
    intro i
    by_cases hl : kj ≤ i.1 ∧ i.1 < n
    · simp only [hw, if_pos hl, mul_zero]
      exact (intSub P).zero_mem
    · simp only [hw, if_neg hl, zpow_zero, inv_one, one_mul]
      exact hvi i
  have hgw := (mem_parL' P q kj n c _).1 ((hp w).2 hwp) ⟨kj + s.1, hs⟩
  rw [if_pos ⟨by simp, hs0⟩, zpow_one] at hgw
  have hqE : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hqi : IntAt P (q : E) := natCast_mem (intSub P) q
  have e1 : g w ⟨kj + s.1, hs⟩ = (q : E) * ((q : E)⁻¹ * g w ⟨kj + s.1, hs⟩) := by
    rw [mul_inv_cancel_left₀ hqE]
  have hgwi : IntAt P (g w ⟨kj + s.1, hs⟩) := by rw [e1]; exact hqi.mul hgw
  have hred : redP P (g w ⟨kj + s.1, hs⟩) = 0 := by
    rw [e1, reduction_mul hqi hgw]
    have : redP P (q : E) = 0 := by
      have h := reduction_coe P (q : 𝓞 E)
      rw [map_natCast] at h
      rw [h, Ideal.Quotient.eq_zero_iff_mem]
      exact hq
    rw [this, zero_mul]
  have key : (⟨g w ⟨kj + s.1, hs⟩, hgwi⟩ : intSub P) + (blockD P kj n hg * blockD P kj n hg') s t =
      blockD P kj n (mul_mem hg hg') s t := by
    apply Subtype.ext
    have h2 : (blockD P kj n (mul_mem hg hg') s t : E) = g v ⟨kj + s.1, hs⟩ := by
      simp only [blockD, Matrix.of_apply, Loc.atN]
      rw [dif_pos hs]
      rfl
    have h1 : g v ⟨kj + s.1, hs⟩ = g w ⟨kj + s.1, hs⟩ +
        ∑ u : Fin (n - kj), Loc.atN v (kj + u.1) * g (Loc.eN E (n + c) (kj + u.1)) ⟨kj + s.1, hs⟩ := by
      conv_lhs => rw [hdec, map_add, map_sum]
      simp only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [h2, h1, Matrix.mul_apply, Subring.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Subring.coe_mul, mul_comm]
    congr 1
    simp only [blockD, Matrix.of_apply, Loc.atN]
    rw [dif_pos hs]
  have h3 := congrArg (redHom P) key
  rw [map_add, redHom_apply, hred, zero_add] at h3
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, h3]
  rfl

theorem lamQB_mul {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ LocE.JQ P q kj n c) (hg' : g' ∈ LocE.JQ P q kj n c) :
    LocE.lamQB ξ kj n (g * g').toLinearMap = LocE.lamQB ξ kj n g.toLinearMap * LocE.lamQB ξ kj n g'.toLinearMap := by
  have hg1 : g ∈ stabL E (n + c) (stdAt E (n + c) P) := hg.1
  have hg2 : g' ∈ stabL E (n + c) (stdAt E (n + c) P) := hg'.1
  unfold LocE.lamQB
  rw [← mul_inv]
  congr 1
  apply isUnit_of_reduction_mul
  rw [redP_det_block P kj n hg1, redP_det_block P kj n hg2, redP_det_block P kj n (mul_mem hg1 hg2), ← Matrix.det_mul,
    ← map_mul, block_mul' P q hq0 hq kj n c hg1 hg2 hg.2]

theorem lamRow_mul : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) sharp j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) sharp j P, lamRow Ch mu sharp j P (g * g').toLinearMap = lamRow Ch mu sharp j P g.toLinearMap * lamRow Ch mu sharp j P g'.toLinearMap := by
  intro X Pr R Ch S mu sharp j P hP g hg g' hg'
  unfold Jat at hg hg'
  rw [if_neg hP] at hg hg'
  unfold lamRow
  rw [if_neg hP, if_neg hP, if_neg hP]
  exact lamQB_mul P (qOf P) (fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _) _ _ _ _ hg hg'

end GlobalTheory.TwistRowMul

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

theorem mem_ideal_of_locally (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, app_resG] at this
  rw [← germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

theorem appLE_mem_ideal_comap (J : X.IdealSheafData) (g : W ⟶ X) (V : X.affineOpens) (A : W.affineOpens)
    (h : A.1 ≤ g ⁻¹ᵁ V.1) {a : Γ(X, V.1)} (ha : a ∈ J.ideal V) :
    (g.appLE V.1 A.1 h).hom a ∈ (J.comap g).ideal A :=
  (comap_le_iff J g _).1 le_rfl V a ha A h

theorem exists_affine_pair (g : W ⟶ X) (U : X.Opens) (A : W.Opens) (y : W) (hy : y ∈ A) (hU : g y ∈ U) :
    ∃ (V : X.affineOpens) (B : W.affineOpens), V.1 ≤ U ∧ B.1 ≤ A ∧ B.1 ≤ g ⁻¹ᵁ V.1 ∧ y ∈ B.1 := by
  obtain ⟨_, ⟨V, hV', rfl⟩, hyV, hV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  obtain ⟨_, ⟨B, hB', rfl⟩, hyB, hB⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ A ⊓ g ⁻¹ᵁ V from ⟨hy, hyV⟩) (A ⊓ g ⁻¹ᵁ V).isOpen
  exact ⟨⟨V, hV'⟩, ⟨B, hB'⟩, hV, fun x hx => (hB hx).1, fun x hx => (hB hx).2, hyB⟩

theorem Generates.ideal_comap_top_le [IsAffine W] {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) (k : L.ι) (h : ⊤ ≤ g ⁻¹ᵁ L.U k) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤
      Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) := by
  set K : Ideal Γ(W, ⊤) := Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) with hK
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop K := by
    refine (comap_le_iff _ _ _).2 fun U a ha A hA => mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (U.1 ⊓ L.U k) A.1 y hy ⟨hA hy, h trivial⟩
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X (hV.trans inf_le_left) a ∈ J.ideal V :=
      J.ideal_le_comap_ideal (U := V) (V := U) (hV.trans inf_le_left) ha
    rw [hJ.2 k V (hV.trans inf_le_right)] at h1
    have h2 : resG W hB (resG W hA ((g.app U.1).hom a)) =
        (g.appLE V.1 B.1 hBV).hom (resG X (hV.trans inf_le_left) a) := by
      rw [appLE_resG, resG_resG]
      rfl
    rw [h2]
    rw [← Ideal.mem_comap]
    refine Ideal.span_le.2 ?_ h1
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, appLE_resG, ← resG_appLE g h le_top]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  refine (key _).trans ?_
  simp

theorem Generates.generatesAlong_comap {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) : GeneratesAlong (J.comap g) σ g := by
  refine ⟨by rw [← Scheme.Hom.preimage_iSup, hJ.1, Scheme.Hom.preimage_top], fun k A h => le_antisymm ?_ ?_⟩
  · intro s hs
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := appLE_mem_ideal_comap (J.comap g) A.1.ι A ⟨⊤, isAffineOpen_top _⟩ hA hs
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := hJ.ideal_comap_top_le (A.1.ι ≫ g) k (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.span _), Ideal.mem_comap, Ideal.map_span,
      ← Set.range_comp]
    convert h2 using 3
    funext j
    exact appLE_appLE _ _ h hA _
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (L.U k) A.1 y hy (h hy)
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X hV ((σ j).f k) ∈ J.ideal V := by
      rw [hJ.2 k V hV]
      exact Ideal.subset_span ⟨j, rfl⟩
    have h2 := appLE_mem_ideal_comap J g V B hBV h1
    rw [appLE_resG] at h2
    rwa [resG_appLE]

theorem generatesAlong_comap_of_generates (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (hJ : Generates J σ) : GeneratesAlong (J.comap g) σ g :=
  hJ.generatesAlong_comap g

end GlobalTheory.ProjBlowup
end
end

