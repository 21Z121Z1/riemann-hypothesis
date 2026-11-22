import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsScalarTowerMdlOm
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.ZetaB

open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.NeedB GlobalTheory.KEdge

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def tInv (l N R : ℕ) : ZMod N := ((l : ZMod N) ^ R)⁻¹

def uIdx (l N R : ℕ) (x : ZMod N) : Fin 2 → ℚ := ![1 / (l : ℚ) ^ R, ((x * tInv l N R).val : ℚ) / N]

def vIdx (l N R : ℕ) : Fin 2 → ℚ := ![0, 1 / (l : ℚ) ^ R + ((tInv l N R).val : ℚ) / N]

def uIdxMu (l N R : ℕ) (x : ZMod N) : Fin 2 → ℚ := ![1 / (l : ℚ) ^ R + ((x * tInv l N R).val : ℚ) / N, 0]

def vIdxMu (l N R : ℕ) : Fin 2 → ℚ := ![((tInv l N R).val : ℚ) / N, 1 / (l : ℚ) ^ R]

def atN (X : Tower Ω ε) (N : ℕ) (f : X.K) : X.K := X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f

def topLev (N M' : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma M'

def cycFix (Ω : Type) [Field Ω] [Algebra ℚ Ω] (M : ℕ) : Subgroup (Ω ≃ₐ[ℚ] Ω) where
  carrier := {s | ∀ z : Ω, z ^ M = 1 → s z = z}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb z hz
    simp only [Set.mem_setOf_eq] at *
    rw [AlgEquiv.mul_apply, hb z hz, ha z hz]
  inv_mem' := by
    intro a ha z hz
    simp only [Set.mem_setOf_eq] at *
    show a.symm z = z
    rw [AlgEquiv.symm_apply_eq]
    exact (ha z hz).symm

abbrev Om (X : Tower Ω ε) : Type := AlgebraicClosure X.K

attribute [local instance] algMdl

theorem isScalarTower_mdl_om (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    @IsScalarTower (mdl X Γ' S) (lev X Γ') (Om X) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_mdl_om

open Classical in

def rootOf {L : Type*} [Field L] (k : ℕ) (a : L) : L := if h : ∃ b : L, b ^ k = a then h.choose else 0

open Classical in

def kumHom {F L : Type*} [Field F] [Field L] [Algebra F L] (N : ℕ) (ζ θ : L) : (L ≃ₐ[F] L) →* Multiplicative (ZMod N) :=
  if h : ∀ g g' : L ≃ₐ[F] L, kum (N := N) ζ θ (g * g') = kum ζ θ g + kum ζ θ g' then
    { toFun := fun g => Multiplicative.ofAdd (kum (N := N) ζ θ g)
      map_one' := by
        have h1 := h 1 1
        rw [mul_one] at h1
        have h0 : kum (N := N) ζ θ (1 : L ≃ₐ[F] L) = 0 := by
          have := congrArg (fun t => t - kum (N := N) ζ θ (1 : L ≃ₐ[F] L)) h1
          simpa using this.symm
        rw [h0]; rfl
      map_mul' := fun g g' => by rw [h g g']; rfl }
  else 1

abbrev topR (r n : ℕ) : ℕ := r + n

abbrev topG (l N m r n : ℕ) : Subgroup SL(2, ℤ) := topLev N (m * l ^ (r + n))

abbrev topK (X : Tower Ω ε) (l N m r n : ℕ) : Subfield X.K := lev X (topG l N m r n)

abbrev topF (X : Tower Ω ε) (l N m r n : ℕ) : Subfield X.K :=
  mdl X (topG l N m r n) (cycFix Ω (m * l ^ (r + n)))

def zetaOm (X : Tower Ω ε) (l n : ℕ) : Om X := algebraMap Ω (Om X) (eOm ε (1 / (l : ℚ) ^ n))

def uTop (X : Tower Ω ε) (l N r n c : ℕ) (x : ZMod N) : X.K := atN X N (siegel X c (uIdxMu l N (r + n) x))

def vTop (X : Tower Ω ε) (l N r n d : ℕ) : X.K := atN X N (siegel X d (vIdxMu l N (r + n)))

def kapU (X : Tower Ω ε) (l N m r n c : ℕ) (x : ZMod N) : (Om X ≃ₐ[topF X l N m r n] Om X) →* Multiplicative (ZMod (l ^ n)) :=
  kumHom (l ^ n) (zetaOm X l n) (rootOf (l ^ n) (algebraMap X.K (Om X) (uTop X l N r n c x)))

def kapV (X : Tower Ω ε) (l N m r n d : ℕ) : (Om X ≃ₐ[topF X l N m r n] Om X) →* Multiplicative (ZMod (l ^ n)) :=
  kumHom (l ^ n) (zetaOm X l n) (rootOf (l ^ n) (algebraMap X.K (Om X) (vTop X l N r n d)))

open Classical in

def etaTop (X : Tower Ω ε) (l N m r n c d : ℕ) (x : ZMod N) : (Om X ≃ₐ[topF X l N m r n] Om X) → ZMod (l ^ n) :=
  if h : ∃ η : (Om X ≃ₐ[topF X l N m r n] Om X) → ZMod (l ^ n),
      IsLocallyConstant (fun g : geo (topF X l N m r n) (topK X l N m r n) (Om X) => η g) ∧
      CobOn (geo (topF X l N m r n) (topK X l N m r n) (Om X)) (kapU X l N m r n c x) (kapV X l N m r n d) η ∧
      ∀ B : ValuationSubring (Om X), (∀ a : Ω, algebraMap Ω (Om X) a ∈ B) → algebraMap X.K (Om X) X.jK ∈ B →
        ∀ g ∈ geo (topF X l N m r n) (topK X l N m r n) (Om X), Inert B g → η g = 0
  then h.choose else 0

def wTop (X : Tower Ω ε) (l N m r n c d : ℕ) (x : ZMod N) (σ : Om X ≃ₐ[topF X l N m r n] Om X) :
    topK X l N m r n :=
  topW (F := topF X l N m r n) (K := topK X l N m r n) (Ω := Om X) (zetaOm X l n) (kapU X l N m r n c x)
    (kapV X l N m r n d) (etaTop X l N m r n c d x) σ⁻¹

open Classical in

def unitOf (X : Tower Ω ε) (a : X.K) : X.Kˣ := if h : a = 0 then 1 else Units.mk0 a h

def clsHat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.K) : X.Khat l :=
  AdicCompletion.of (idl l) (X.Kl l) ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul (unitOf X a))

def secF (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) (a : X.K) : X.Fn l :=
  fun u => (u 0) ^ w • clsHat X l a

def cR (l N : ℕ) (r₀ : ZMod l) : ℤ := (N : ℤ) * ((-r₀ * (N : ZMod l)⁻¹).val : ℤ)

def gR (l N : ℕ) (r₀ : ZMod l) : SL(2, ℤ) :=
  ⟨!![1, 0; cR l N r₀, 1], by simp [Matrix.det_fin_two]⟩

abbrev TopCos (l N m r n : ℕ) : Type :=
  Quotient (QuotientGroup.rightRel ((topG l N m r n).subgroupOf (Gam N l)))

def push (X : Tower Ω ε) (l N m r n : ℕ) [Fact l.Prime] (b : X.Fn l) : X.Fn l :=
  ∑ r₀ : (ZMod l)ˣ, ∑ᶠ q : TopCos l N m r n,
    X.act l (((gR l N (r₀ : ZMod l) * ((Quotient.out q : Gam N l) : SL(2, ℤ)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) b

open Classical in

def liftF (X : Tower Ω ε) (F : Subfield X.K) (s : Ω ≃ₐ[ℚ] Ω) : Om X ≃ₐ[F] Om X :=
  if h : ∀ a : F, IsAlgClosure.equivOfEquiv (Om X) (Om X) (X.gal s) (algebraMap F (Om X) a) = algebraMap F (Om X) a then
    AlgEquiv.ofRingEquiv h
  else 1

def clsGam (X : Tower Ω ε) (l N m r n w c d : ℕ) [Fact l.Prime] (x : ZMod N)
    (τ : Om X ≃ₐ[topF X l N m r n] Om X) : X.Fn l :=
  push X l N m r n (secF X l w ((wTop X l N m r n c d x τ : topK X l N m r n) : X.K))

open Classical in

def shap {G V U : Type*} [Group G] [AddCommMonoid V] [Group U] (H : Subgroup G) (χ : G →* U) (act : G → V → V) (z : G → V)
    (s : G) (x : U) : V :=
  ∑ᶠ (q : G ⧸ H) (_ : χ (Quotient.out q) = x),
    act (Quotient.out q) (z ((Quotient.out q)⁻¹ * s * Quotient.out (QuotientGroup.mk (s⁻¹ * Quotient.out q) : G ⧸ H)))

def zetaBχ (X : Tower Ω ε) (l N m r n w c d : ℕ) [Fact l.Prime] (x : ZMod N) {U : Type*} [Group U]
    (χ : Formalism.ConjugateSelfDual.G ℚ Ω →* U) :
    Formalism.ConjugateSelfDual.G ℚ Ω → U → X.Fn l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Fn l))) :=
  fun s x' => Submodule.Quotient.mk
    (shap (cycFix Ω (m * l ^ (r + n))) χ (fun g b => X.galB l g b)
      (fun t => clsGam X l N m r n w c d x (liftF X (topF X l N m r n) t)) s x')

def zetaB (X : Tower Ω ε) (l N m r n w c d : ℕ) [Fact l.Prime] (x : ZMod N) :
    Formalism.ConjugateSelfDual.G ℚ Ω → (ZMod (l ^ r))ˣ → X.Fn l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Fn l))) :=
  zetaBχ X l N m r n w c d x (ReciprocityTheory.Gal.cycMod ℚ Ω l r)

theorem cR_mod (l N : ℕ) [Fact l.Prime] (hN : (N : ZMod l) ≠ 0) (r₀ : ZMod l) : ((cR l N r₀ : ℤ) : ZMod l) = -r₀ := by
  simp only [cR, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [mul_comm (-r₀), ← mul_assoc, mul_inv_cancel₀ hN, one_mul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.eval_clsHat (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n
        (_root_.GlobalTheory.ZetaB.clsHat X l a) =
      X.cls l n (_root_.GlobalTheory.ZetaB.unitOf X a) := by
  unfold _root_.GlobalTheory.ZetaB.clsHat
  rw [AdicCompletion.eval_of]
  rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.unitOf_val (X : _root_.GlobalTheory.KZ.Tower Ω ε) {a : X.K}
    (ha : a ≠ 0) : ((_root_.GlobalTheory.ZetaB.unitOf X a : (X.K)ˣ) : X.K) = a := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dif_neg ha]
  rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in

theorem _root_.GlobalTheory.ZetaB.unitOf_zero (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    _root_.GlobalTheory.ZetaB.unitOf X 0 = 1 := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dif_pos rfl]

theorem vecMul_gR (l N : ℕ) [Fact l.Prime] (hN : (N : ZMod l) ≠ 0) (r₀ : ZMod l) :
    ![-r₀, -1] ᵥ* (((gR l N r₀ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod l)) = ![0, -1] := by
  funext i
  fin_cases i <;> simp [gR, Matrix.vecMul, dotProduct, Fin.sum_univ_two, cR_mod l N hN]

example : tInv 3 5 1 = 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [tInv, pow_one]
  exact inv_eq_of_mul_eq_one_right (by decide +revert)

example : uIdxMu 3 5 1 1 = ![11 / 15, 0] ∧ vIdxMu 3 5 1 = ![2 / 5, 1 / 3] := by
  have h : tInv 3 5 1 = 2 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [tInv, pow_one]
    exact inv_eq_of_mul_eq_one_right (by decide +revert)
  have h2 : (2 : ZMod 5).val = 2 := rfl
  unfold uIdxMu vIdxMu
  rw [h, one_mul, h2]
  constructor <;> norm_num

example : cR 3 5 1 = 5 := by
  have h : (-1 * ((5 : ℕ) : ZMod 3)⁻¹) = 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [inv_eq_of_mul_eq_one_right (show ((5 : ℕ) : ZMod 3) * 2 = 1 by decide +revert)]
    decide +revert
  rw [cR, h]
  rfl

example : ((gR 3 5 1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = cR 3 5 1 := by
  simp [gR]

end GlobalTheory.ZetaB
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ.SiegelModel

open GlobalTheory.Sieg GlobalTheory.Sieg.Model

theorem isOpen_Hs : IsOpen Hs :=
  isOpen_lt continuous_const Complex.continuous_im

theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hloc : nhdsWithin Complex.I (Hs \ {Complex.I}) = nhdsWithin Complex.I {Complex.I}ᶜ :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI))
  have hne : (nhdsWithin Complex.I (Hs \ {Complex.I})).NeBot := by
    rw [hloc]
    infer_instance
  refine hne.mono ?_
  unfold Filter.codiscreteWithin
  exact le_iSup₂ (f := fun x (_ : x ∈ Hs) => nhdsWithin x (Hs \ {x})) Complex.I hI

theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => h z hz)

theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  unfold sgC
  rw [UpperHalfPlane.ofComplex_apply]

theorem germ_sgC_ne_zero {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) : ((sgC c x : ℂ → ℂ) : Mero) ≠ 0 := by
  intro h0
  rw [← Filter.Germ.coe_zero] at h0
  have hev := Filter.Germ.coe_eq.1 h0
  have := neBot_Hs
  obtain ⟨z, hz0, hzH⟩ := (hev.and (Filter.self_mem_codiscreteWithin Hs)).exists
  have hsg := (multipliable_and_sg_ne_zero h ⟨z, hzH⟩).2.2
  apply hsg
  have e : sgC c x z = sg c x ⟨z, hzH⟩ := sgC_coe c x ⟨z, hzH⟩
  rw [← e]
  exact hz0

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε)

theorem an_injective : Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

theorem siegel_eq {c : ℕ} {x : Fin 2 → ℚ} {f : T.K} (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) :
    siegel T c x = f := by
  have hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  unfold siegel
  rw [dif_pos hex]
  exact an_injective T (hex.choose_spec.trans hf.symm)

theorem siegel_ne_zero_iff {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) :
    siegel T c x ≠ 0 ↔ T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  constructor
  · intro hne
    by_cases hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero)
    · obtain ⟨f, hf⟩ := hex
      rw [siegel_eq T hf]
      exact hf
    · exact absurd (by unfold siegel; exact dif_neg hex) hne
  · intro hmem h0
    rw [h0, map_zero] at hmem
    exact germ_sgC_ne_zero h hmem.symm

theorem sg_one {x : Fin 2 → ℚ}
    (hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ))) (τ : ℍ) : sg 1 x τ = 1 := by
  have ht : ee (pt x τ) ≠ 1 := by
    intro h1
    obtain ⟨h0, n, hn⟩ := ee_eq_one (a := x 0) (b := x 1) τ h1
    exact hx ⟨⟨0, by rw [h0]; simp⟩, ⟨n, hn⟩⟩
  have hne : (1 : ℂ) - ee (pt x τ) ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have hfac : ∀ m : ℕ, cthFac 1 (ee τ) (ee (pt x τ)) (m + 1) = 1 := by
    intro m
    obtain ⟨h1, h2⟩ := ne_one_of_not_int hx τ (m + 1)
    simp only [cthFac, one_pow, pow_one]
    exact div_self (mul_ne_zero h1 h2)
  simp [sg, cth, hfac, hne]

theorem siegel_one {x : Fin 2 → ℚ}
    (hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ))) : siegel T 1 x = 1 := by
  refine siegel_eq T ?_
  rw [map_one, ← Filter.Germ.coe_one]
  refine germ_eq_of_eqOn fun z hz => ?_
  have e : sgC 1 x z = sg 1 x ⟨z, hz⟩ := sgC_coe 1 x ⟨z, hz⟩
  rw [Pi.one_apply, e, sg_one hx]

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem sl_siegel {c : ℕ} {x : Fin 2 → ℚ} (γ : SL(2, ℤ))
    (hmem : T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero))
    (hγ : ∀ τ : ℍ, sg c x (γ • τ) = sg c (act x γ) τ) :
    T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  refine (siegel_eq T ?_).symm
  rw [T.an_sl _ _ _ hmem]
  refine germ_eq_of_eqOn fun z hz => ?_
  have e1 : mob (ofSL γ) z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := mob_ofSL γ ⟨z, hz⟩
  have e2 : sgC c (act x γ) z = sg c (act x γ) ⟨z, hz⟩ := sgC_coe c (act x γ) ⟨z, hz⟩
  show sgC c x (mob (ofSL γ) z) = sgC c (act x γ) z
  rw [e1, sgC_coe, hγ, e2]

theorem an_siegel {c : ℕ} {x : Fin 2 → ℚ} (M : ℕ) (hM : 0 < M) (hd : DifferentiableOn ℂ (sgC c x) Hs)
    (hmod : ∀ (γ : SL(2, ℤ)) (τ : ℍ), sg c x (γ • τ) = sg c (act x γ) τ)
    (hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ)
    (hexp : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c (act x γ) τ)) :
    T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by

  have hγz : ∀ (γ : SL(2, ℤ)) (z : ℂ) (hz : z ∈ Hs), sgC c x (mob (ofSL γ) z) = sg c (act x γ) ⟨z, hz⟩ := by
    intro γ z hz
    rw [mob_ofSL γ ⟨z, hz⟩, sgC_coe, hmod]
  have hlev' : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, sgC c x (mob (ofSL γ) z) = sgC c x z := by
    intro γ hγ z hz
    rw [hγz γ z hz, hlev γ hγ, ← sgC_coe]
  have hexp' : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ z ∈ Hs,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M))
        (sgC c x (mob (ofSL γ) z)) := by
    intro γ
    obtain ⟨a, n0, ha, hs⟩ := hexp γ
    refine ⟨a, n0, ha, fun z hz => ?_⟩
    rw [hγz γ z hz]
    exact hs ⟨z, hz⟩
  obtain ⟨f, hf⟩ := T.mem_q (sgC c x) M hM hd hlev' hexp'
  rw [siegel_eq T hf]
  exact hf

theorem siegel_zero_index {c : ℕ} : siegel T c 0 = 0 := by
  refine siegel_eq T (f := 0) ?_
  rw [map_zero, ← Filter.Germ.coe_zero]
  refine germ_eq_of_eqOn fun z _ => ?_
  simp [sgC, sg, cth, pt, ee]

end GlobalTheory.KZ.SiegelModel
end
end

