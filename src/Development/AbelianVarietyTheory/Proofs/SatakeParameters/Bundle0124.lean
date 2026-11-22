import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalRingCardinality.DataKerI
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne
section
noncomputable section

namespace GlobalTheory.KernelScalarUnit

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts GlobalTheory.UnUnitCmp
open scoped nonZeroDivisors

section Ideals

variable {K : Type} [Field K] [NumberField K]

theorem exists_pow_eq_span {𝔞 𝔟 : Submodule (𝓞 K) K} (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (a : K), 0 < n ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {a} := by
  have hu : IsUnit 𝔞 := IsUnit.of_mul_eq_one 𝔟 h
  have hv : IsUnit 𝔟 := IsUnit.of_mul_eq_one 𝔞 (by rw [mul_comm]; exact h)
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔞, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hu)⟩
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔟, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hv)⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact h
  let U : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mkOfMulEqOne I J hIJ
  have h1 : ClassGroup.mk K (U ^ Fintype.card (ClassGroup (𝓞 K))) = 1 := by rw [map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := ClassGroup.mk_eq_one_iff.1 h1
  refine ⟨_, a, Fintype.card_pos (α := ClassGroup (𝓞 K)), ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

omit [NumberField K] in
theorem map_mem_one (c : K →+* K) {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, rfl⟩

omit [NumberField K] in
theorem map_mem_pow (c : K →+* K) {𝔞 𝔟 : Submodule (𝓞 K) K} (h : ∀ x ∈ 𝔞, c x ∈ 𝔟) :
    ∀ (n : ℕ), ∀ x ∈ 𝔞 ^ n, c x ∈ 𝔟 ^ n
  | 0, x, hx => by rw [pow_zero] at *; exact map_mem_one c hx
  | n + 1, x, hx => by
    rw [pow_succ] at *
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]; exact Submodule.mul_mem_mul (map_mem_pow c h n a ha) (h b hb)
    · rw [map_add]; exact add_mem ha hb

theorem exists_pow_eq_span_normOne (c : K →+* K) (hc : ∀ x, c (c x) = x) {𝔞 𝔟 : Submodule (𝓞 K) K}
    (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (z : K), 0 < n ∧ c z * z = 1 ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {z} := by
  obtain ⟨n, a, hn, ha⟩ := exists_pow_eq_span h
  have hb' : 𝔟 ^ n = Submodule.span (𝓞 K) {c a} := by
    apply le_antisymm
    · intro y hy
      have h1 := map_mem_pow c (fun x hx => (hb x).1 hx) n y hy
      rw [ha, Submodule.mem_span_singleton] at h1
      obtain ⟨r, hr⟩ := h1
      refine Submodule.mem_span_singleton.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, ?_⟩
      rw [← hc y, ← hr, Algebra.smul_def r, map_mul]
      rfl
    · rw [Submodule.span_singleton_le_iff_mem]
      exact map_mem_pow c (fun x hx => (hb _).2 (by rwa [hc])) n a (ha ▸ Submodule.mem_span_singleton_self a)
  have h2 : Submodule.span (𝓞 K) {a * c a} = 1 := by
    rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, ← ha, ← hb', ← mul_pow, h, one_pow]
  have h0 : a * c a ≠ 0 := fun h0 => by
    rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at h2
    have : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K) := h2 ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    simp at this
  have a0 : a ≠ 0 := left_ne_zero_of_mul h0
  have c0 : c a ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨n + n, a / c a, by omega, ?_, ?_⟩
  · rw [map_div₀, hc]; field_simp
  · rw [pow_add, ha, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_one (Submodule.span (𝓞 K) {a / c a}), ← h2,
      Submodule.span_mul_span, Set.singleton_mul_singleton]
    congr 2
    field_simp

end Ideals

theorem normOne_pow (D : D7) : NormOnePowerPrincipal D := by
  let := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rintro 𝔞 ⟨𝔟, hb, h⟩
  obtain ⟨n, z, hn, hz, e⟩ := exists_pow_eq_span_normOne (D.host.conj : D.host.E →+* D.host.E)
    (fun x => by change D.host.conj (D.host.conj x) = x; rw [← hs, ← hs, star_star]) hb h
  have hz' : star z * z = 1 := by rw [hs]; exact hz
  exact ⟨n, ⟨z, hz', by rw [mul_comm]; exact hz'⟩, hn, e⟩

section Local

variable {K : Type} [Field K] [NumberField K] {C : Type} [NormedField C] [IsUltrametricDist C] (ψ : K →+* C)

omit [NumberField K] in
theorem norm_int_le (a : 𝓞 K) : ‖ψ (a : K)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int ψ a.isIntegral_coe)

def ball (r : ℝ) (hr : 0 ≤ r) : Submodule (𝓞 K) K where
  carrier := {x | ‖ψ x‖ ≤ r}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simpa using hr
  smul_mem' := fun c a ha => by
    simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le ψ c)).trans ha

end Local

section Det

variable (D : D7) {l : ℕ} [Fact l.Prime] (ψ : D.host.E →+* ℂ_[l]) {N : ℕ}
  {L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {P : Matrix (Fin N) (Fin N) D.host.E}

end Det

section Power

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def lamTau (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (emb_mem (embT D τ)))

theorem tauEmb_eq (τ : D.what₂.Tau) : tauEmb D lam τ = lamTau D lam τ := by
  funext x
  unfold tauEmb lamC
  rw [dif_pos (emb_mem (embT D τ) x)]
  rfl

def IsIntGL {N : ℕ} (k : Matrix (Fin N) (Fin N) ℂ) : Prop := (∀ a b, IntAt lam (k a b)) ∧ UnitAt lam k.det

def IsBasisLam {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ τ, ∃ (P : Matrix (Fin N) (Fin N) D.host.E) (k : Matrix (Fin N) (Fin N) ℂ),
    LocBasisW D (tauEmb D lam τ) L P ∧ IsIntGL lam k ∧ y τ = P.map (embT D τ) * k

end Power

section Main

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

def detU (D : D7) {N : ℕ} (γ : letI := D.host.cmStar; Matrix.unitaryGroup (Fin N) D.host.E) : D.Dt :=
  letI := D.host.cmStar
  D.e1Dt ⟨(γ : Matrix (Fin N) (Fin N) D.host.E).det, Matrix.det_of_mem_unitary γ.2⟩

def RepScalarTie (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  letI := D.host.cmStar
  ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (γ : Matrix.unitaryGroup (Fin (D.R.N i)) D.host.E) (γ' : Matrix.unitaryGroup (Fin (D.R.N (i + 1))) D.host.E)
      (k : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ)
      (k' : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) ℂ),
      EqAt D (D.what₂.places.resChar w) (SDLat.smulLat γ.1 ((O u μ).lat i c).1) ((O u μ).L0 i).1 ∧
      EqAt D (D.what₂.places.resChar w) (SDLat.smulLat γ'.1 ((O u μ).lat (i + 1) c').1) ((O u μ).L0 (i + 1)).1 ∧
      (∀ τ, IsIntGL (E.lam w) (k τ)) ∧ (∀ τ, IsIntGL (E.lam w) (k' τ)) ∧
      E.un u μ w i c c' = lamV (E.lam w)
        (((rhoOf D (O u μ).mt i (detU D γ * (O u μ).dt i c) : ℂˣ) : ℂ) *
          ((rhoOf' D (O u μ).mt i (detU D γ' * (O u μ).dt (i + 1) c') : ℂˣ) : ℂ) *
          (∏ τ, (k τ).det ^ (D.chTw u μ).sSharp i τ) * (∏ τ, (k' τ).det ^ (D.chTw u μ).sDiv i τ)⁻¹)

def FrameScalarTie (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (y : (D.chTw u μ).Y i) (y' : (D.chTw u μ).Y (i + 1)),
      IsBasisLam D (E.lam w) ((O u μ).lat i c).1 ((O u μ).frm i y) ∧
      IsBasisLam D (E.lam w) ((O u μ).lat (i + 1) c').1 ((O u μ).frm (i + 1) y') ∧
      E.un u μ w i c c' = lamV (E.lam w) (epsFr D u μ i c c' y y')

variable (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ))

end Main

end GlobalTheory.KernelScalarUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomConjEquivMemHomAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory

theorem latSum_transport_equiv {E : Type} [Field E] [NumberField E] {H H₂ M : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] [AddCommMonoid M] (e : H ≃ₗ[𝓞 E] H₂) (A B : Submodule (𝓞 E) H)
    (A₂ B₂ : Submodule (𝓞 E) H₂) (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (hB : ∀ x, e x ∈ B₂ ↔ x ∈ B) (G : H → M) (F₂ : H₂ → M)
    (hG : ∀ x x', x - x' ∈ B → G x = G x') (hF : ∀ x, F₂ (e x) = G x) : latSum A₂ B₂ F₂ = latSum A B G := by
  have hAm : A.map (e : H →ₗ[𝓞 E] H₂) = A₂ := by
    ext y
    rw [Submodule.mem_map_equiv, ← hA, e.apply_symm_apply]
  let eA : ↥A ≃ₗ[𝓞 E] ↥A₂ := e.ofSubmodules A A₂ hAm
  have heA : ∀ x : A, ((eA x : A₂) : H₂) = e x := fun x => rfl
  have hBm : (B.comap A.subtype).map (eA : ↥A →ₗ[𝓞 E] ↥A₂) = B₂.comap A₂.subtype := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.subtype_apply, ← hB, ← heA, eA.apply_symm_apply]
  let q := Submodule.Quotient.equiv (B.comap A.subtype) (B₂.comap A₂.subtype) eA hBm
  unfold latSum
  rw [← finsum_comp_equiv q.toEquiv]
  refine finsum_congr fun z => ?_
  set r := Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z with hr
  set r₂ := Function.surjInv (Submodule.Quotient.mk_surjective (B₂.comap A₂.subtype)) (q.toEquiv z) with hr₂
  have h1 : Submodule.Quotient.mk r = z := Function.surjInv_eq _ z
  have h2 : Submodule.Quotient.mk r₂ = q z := Function.surjInv_eq _ _
  have h3 : q z = Submodule.Quotient.mk (eA r) := by
    rw [← h1]; rfl
  rw [h3, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, heA] at h2
  have h4 : (r₂ : H₂) = e (e.symm r₂) := (e.apply_symm_apply _).symm
  rw [h4, hF]
  apply hG
  rw [← hB, map_sub, ← h4]
  exact h2

noncomputable def homConjEquiv {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b ≃ₗ[𝓞 E] HomE E a b where
  toFun x := γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap
  invFun x := γ'.symm.toLinearMap ∘ₗ x ∘ₗ γ.toLinearMap
  map_add' x y := by simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' r x := by
    ext y i
    simp [equiv_osmul]
  left_inv x := by ext y i; simp
  right_inv x := by ext y i; simp

theorem homConjEquiv_mem_homAt {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 E))) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    homConjEquiv γ γ' x ∈ homAt S (gmap γ N) (gmap γ' N') ↔ x ∈ homAt S N N' := by
  show (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) ∈ homAt S (gmap γ N) (gmap γ' N') ↔ _
  constructor
  · intro h P hP y hy
    have h1 := h P hP (γ y) ((mem_localization_gmap P γ N _).2 (by simpa using hy))
    have h2 := (mem_localization_gmap P γ' N' _).1 h1
    simpa using h2
  · intro h P hP y hy
    have h1 := h P hP (γ.symm y) ((mem_localization_gmap P γ N _).1 hy)
    exact (mem_localization_gmap P γ' N' _).2 (by simpa using h1)

theorem mem_divLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ divLat c A₂ ↔ x ∈ divLat c A := by
  show ((c : 𝓞 E) • e x) ∈ A₂ ↔ ((c : 𝓞 E) • x) ∈ A
  rw [← map_smul, hA]

theorem mem_mulLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ mulLat c A₂ ↔ x ∈ mulLat c A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e.symm y, (hA _).1 (by rw [e.apply_symm_apply]; exact hy), ?_⟩
    apply e.injective
    rw [← hxy]
    show e ((c : 𝓞 E) • e.symm y) = (c : 𝓞 E) • y
    rw [map_smul, e.apply_symm_apply]
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e y, (hA _).2 hy, ?_⟩
    rw [← hxy]
    show (c : 𝓞 E) • e y = e ((c : 𝓞 E) • y)
    rw [map_smul]

theorem kerOf_gmap_frames : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (Sa : Finset (HeightOneSpectrum (𝓞 E))) (D cA cB : ℕ) (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (sS sT : SB → E → K), ThDist.Ok th Sa D rho rho' sS sT → ∀ (γ : UF E a) (γ' : UF E b) (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB) (κ : GLQ E a SB) (κ' : GLQ E b SB) (Ξ Ξ₂ : HomE E a b → K) (c : K), IsSdLat N → IsSdLat N' → (∀ x z, z ∈ mulLat cB (homAt Sa N N') → Ξ (x + z) = Ξ x) → (∀ x : HomE E a b, Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) * ∏ P : SB, (sS P ((LinearEquiv.det (κ P).1 : Eˣ) : E) * sT P ((LinearEquiv.det (κ' P).1 : Eˣ) : E)) = c * Ξ x) → kerOf th Sa cA cB (gmap γ.1 N) (fun P => γ.1 * (fr P * (κ P).1)) (gmap γ'.1 N') (fun P => γ'.1 * (fr' P * (κ' P).1)) Ξ₂ = c • ((rho' γ') ∘ₗ kerOf th Sa cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  intro E K _ _ _ _ a b SB V V' _ _ _ _ th Sa D cA cB rho rho' sS sT hok γ γ' N fr N' fr' κ κ' Ξ Ξ₂ c hN hN' hΞ hΞ₂
  have hm : ∀ (g : UF E a), rho g ∘ₗ rho g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm' : ∀ (g : UF E b), rho' g ∘ₗ rho' g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  let φ : (V →ₗ[K] V') ≃+ (V →ₗ[K] V') :=
    { toFun := fun L => rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹
      invFun := fun L => rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ
      left_inv := fun L => by
        have h1 := hm γ⁻¹
        have h2 := hm' γ'⁻¹
        rw [inv_inv] at h1 h2
        show rho' γ'⁻¹ ∘ₗ (rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹) ∘ₗ rho γ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, h2]; simp
      right_inv := fun L => by
        show rho' γ' ∘ₗ (rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ) ∘ₗ rho γ⁻¹ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc, hm']; simp
      map_add' := fun L L' => by simp [LinearMap.comp_add, LinearMap.add_comp] }
  have hH := homConjEquiv_mem_homAt Sa γ.1 γ'.1 N N'
  unfold kerOf
  rw [latSum_transport_equiv (homConjEquiv γ.1 γ'.1) (divLat cA (homAt Sa N N')) (mulLat cB (homAt Sa N N')) _ _
    (mem_divLat_equiv_iff _ _ _ hH cA) (mem_mulLat_equiv_iff _ _ _ hH cB)
    (fun x => c • φ (Ξ x • th N fr N' fr' cB x))]
  · show _ = c • φ _
    unfold latSum
    rw [φ.map_finsum, smul_finsum]
  · intro x x' hx
    have h1 : Ξ x = Ξ x' := by
      have := hΞ x' (x - x') hx
      rwa [add_sub_cancel] at this
    rw [h1, hok.cong N fr N' fr' cB x x' hN hN' hx]
  · intro x
    show Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) • th _ _ _ _ cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap)
      = c • (rho' γ' ∘ₗ (Ξ x • th N fr N' fr' cB x) ∘ₗ rho γ⁻¹)
    rw [hok.equiv γ γ' N (fun P => fr P * (κ P).1) N' (fun P => fr' P * (κ' P).1) cB x hN hN',
      hok.det N fr N' fr' cB x κ κ' hN hN', LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp,
      LinearMap.comp_smul, smul_smul, smul_smul, hΞ₂]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtFormOfMemStdAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_form_of_mem_stdAt (a : E) (η : Sp E n →ₗ[E] E) (h : ∀ i, IntAt P (a * η (Pi.single i 1))) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : IntAt P (a * η v) := by
  rw [GlobalTheory.TopInv.form_apply η v, Finset.mul_sum]
  refine GlobalTheory.TopStep.intAt_sum _ fun j _ => ?_
  rw [mul_left_comm]
  exact (mem_stdAt.1 hv j).mul (h j)

theorem intAt_form_comp_iff (a : E) (κ : GLint E n P) (η : Sp E n →ₗ[E] E) :
    (∀ i, IntAt P (a * (η ∘ₗ κ.1.toLinearMap) (Pi.single i 1))) ↔ ∀ i, IntAt P (a * η (Pi.single i 1)) := by
  refine ⟨fun h i => ?_, fun h i => intAt_form_of_mem_stdAt a η h (glint_mem κ (single_mem_stdAt i))⟩
  have h1 := intAt_form_of_mem_stdAt a _ h (glint_mem κ⁻¹ (single_mem_stdAt i))
  have e : κ.1 ((κ⁻¹).1 (Pi.single i 1)) = Pi.single i 1 := LinearEquiv.apply_symm_apply κ.1 _
  have e' : (η ∘ₗ κ.1.toLinearMap) ((κ⁻¹).1 (Pi.single i 1)) = η (Pi.single i 1) := congrArg η e
  rwa [e'] at h1

end SlopeTestRemainingChoices

theorem psi_add_int {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) {k : ℕ}
    (hk : k ≤ c.D P) {x z : X.E} (hx : IntAt P.1 ((qOf P.1 : X.E) ^ k * x)) (hz : IntAt P.1 (z - x)) :
    c.psi P ((epsSg : X.E) * z) = c.psi P ((epsSg : X.E) * x) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
  have hq := fun m => intAt_pow (GlobalTheory.TopStep.intAt_nat (P := P.1) (qOf P.1)) m
  have hd := he.mul hz
  have h1 : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * ((epsSg : X.E) * x)) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    have := (hq d).mul (he.mul hx)
    convert this using 1
    rw [hd, pow_add]
    ring
  have := hc.psi_add P _ _ h1 ((hq _).mul hd)
  rw [hc.psi_int P _ hd, mul_one] at this
  rw [← this]
  congr 1
  ring

theorem ftY_comp_glint : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (P : rowSG Pr sel mu), (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ {n : ℕ} (κ : GLint X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) (y' y'' : Sp X.E n), (P.1 ∈ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → (P.1 ∉ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)) → (P.1 ∈ Pr.vGs → κ.1 y'' - y' ∈ stdAt X.E n P.1) → (P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 y'' - y') ∈ stdAt X.E n P.1) → ftY sel mu cst P (η ∘ₗ κ.1.toLinearMap) y'' = ftY sel mu cst P η y' := by
  intro X Pr sel S mu cst hc P hD n κ η y' y'' hy1 hy2 hk1 hk2
  have hq := qOf_ne_zero (P := P.1)
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP, if_pos hP]
    have hi := intAt_form_comp_iff 1 κ η
    simp only [one_mul] at hi
    by_cases h : ∀ i, IntAt P.1 (η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      have h' : ∀ i, IntAt P.1 (1 * η (Pi.single i 1)) := fun i => by rw [one_mul]; exact h i
      refine psi_add_int hc P (hc.D_pos P) ?_ ?_
      · have := intAt_form_of_mem_stdAt 1 η h' (v := (qOf P.1 : X.E) • y') (mem_stdAt.2 (hy1 hP))
        rwa [one_mul, map_smul, smul_eq_mul, ← pow_one (qOf P.1 : X.E)] at this
      · have := intAt_form_of_mem_stdAt 1 η h' (hk1 hP)
        rwa [one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]
  · rw [if_neg hP, if_neg hP]
    have hi := intAt_form_comp_iff ((qOf P.1 : X.E) ^ cst.M) κ η
    by_cases h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      refine congrArg _ (psi_add_int hc P (hD hP) ?_ ?_)
      · have := intAt_form_of_mem_stdAt _ η h (v := (qOf P.1 : X.E) ^ cst.M • y') (mem_stdAt.2 (hy2 hP))
        rwa [map_smul, smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul] at this
      · have := intAt_form_of_mem_stdAt _ η h (hk2 hP)
        rwa [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]

end GlobalTheory.TopLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

namespace GlobalTheory.SplitPairLift

theorem isIrreducible_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (χ : G →* ℂˣ) : (twist ρ χ).IsIrreducible := by
  let e : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at h1⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 h

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detIrr (n : ℕ) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 h.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth h.detChar
  irr := isIrreducible_twist π.irr _

theorem twist_twist_inv {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) :
    twist (twist π.π (detChar (Fin n) χ)) (detChar (Fin n) χ⁻¹) = π.π := by
  rw [twist_twist]
  have : detChar (Fin n) χ⁻¹ * detChar (Fin n) χ = 1 := by
    ext g; simp
  rw [this, twist_one]

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem e_spehLoc (T : WDTie N A) (p : Part A.CG) (w : PlE H) :
    T.e w (spehLoc N A p w) = speh (T.e w (A.locG p.π w)) p.d := by
  unfold spehLoc speh
  generalize ((p.d : ℝ) - 1) / 2 = s
  have key : ∀ L : List ℝ,
      T.e w (L.foldr (fun j acc => A.lpSum (A.lpTw (A.locG p.π w) (s - j)) acc) (A.lpZero w)) =
        L.foldr (fun j acc => ((T.e w (A.locG p.π w)).lpTw (s - j)).lpSum acc) (WD.lpZero _) := by
    intro L
    induction L with
    | nil => exact T.zero w
    | cons j l ih => rw [List.foldr_cons, List.foldr_cons, T.sum, T.tw, ih]
  exact key _

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.HoweDualityGL → ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T), Laws S → RowUnit S → PairRead S → ∀ i, PairLift N A i := by
  intro hBZ hB hH R H what₂ N A T S hL hU hP i σ P hpair w hw
  have hne : what₂.isot (N.j i) σ ≠ ⊥ := by
    obtain ⟨f, hf, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hf
    apply hF
    rw [hf, map_zero, inner_zero_right]
  have hrt : R.r < R.t := by
    have := R.rank_add_five_le
    unfold Ranks.r
    omega
  have L := hL i w hw
  set X := S i w hw with hX
  let π' := twistIrr (X.rep P) X.eta_ok.1
  let cμ := detIrr 1 X.mu_ok.1
  let τ := detIrr R.t X.mu_ok.1
  let cη := detIrr 1 X.eta_ok.1.inv
  have h1 : Nonempty (π'.π.Equiv (prod₂ (X.row σ).π τ.π)) :=
    GlobalTheory.T.theta_correspondence_large_rank hBZ hB hH _ R.r R.t X.mu _ _ (X.row σ).π π'.π hrt X.mu_ok.1 X.mu_ok.2 (X.row σ).smooth
      (X.row σ).irr (hU i w hw σ hne) π'.smooth π'.irr (hP i w hw σ P hpair)
  have h2 := L.prod _ _ (X.row σ) τ π' h1
  have h3 := L.det R.t X.mu cμ τ ⟨.refl _⟩ ⟨.refl _⟩
  have h4 := L.twist _ X.eta⁻¹ cη π' (X.rep P) ⟨.refl _⟩ (by
    show Nonempty ((X.rep P).π.Equiv (twist (twist (X.rep P).π (detChar _ X.eta)) (detChar _ X.eta⁻¹)))
    rw [twist_twist_inv]
    exact ⟨.refl _⟩)
  have h5 := X.locMu cμ ⟨.refl _⟩
  have h6 := X.locEta cη ⟨.refl _⟩
  have h7 : A.lpDim (A.locG A.etaTinv w) = 1 := by
    rw [← T.dim, h6, L.dim]
  apply (T.e w).injective
  unfold liftPar
  rw [T.char _ _ _ h7, T.sum, e_spehLoc, X.locV, X.locW σ hne, h4, h2, h3, h6]
  show _ = ((X.rc _ (X.row σ)).lpSum (speh (T.e w (A.locG (A.muC i) w)) R.t)).lpChar _
  rw [h5]

end GlobalTheory.SplitPairLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOperator_maps_stabiliserEquivariant_forms : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (G : StabDat C), FormsAre M O G → (∀ i < D.R.m, UnfIs O i (nuT D u i)) → (∀ i < D.R.m, ∀ c c', Differentiable ℂ (O.Th i c c')) → (∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw O i c c' g) → ∀ i < D.R.m, ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  first | exact @GlobalTheory.KerJ.FiCore.K_mem_Fi | exact GlobalTheory.KerJ.FiCore.K_mem_Fi | (intros; apply GlobalTheory.KerJ.FiCore.K_mem_Fi <;> assumption)
end

