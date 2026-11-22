import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Formalism.PairingDivisors.StatementN

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport

section Quadratic

variable {K : Type} [Field K] [NumberField K]

def Fixes (φK : K →+* ℂ) (σ : ℂ ≃+* ℂ) : Prop := ∀ x : K, σ (φK x) = φK x

def IsInvIdealOf (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Prop :=
  ∀ x : K, x ∈ 𝔞 ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x) v) ≤ 1

def IsLatOf (φK : K →+* ℂ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (Λ : PeriodPair) : Prop :=
  (Λ.lattice : Set ℂ) = φK '' (𝔞 : Set K)

def jLat (Λ : PeriodPair) : ℂ := 1728 * Λ.g₂ ^ 3 / latDisc Λ

def nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : ℝ := ((FractionalIdeal.absNorm 𝔞 : ℚ) : ℝ)

def Equidistributed (φK : K →+* ℂ) (j₀ : ℂ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Prop :=
  IsAlgebraic ℚ j₀ ∧
  (∀ σ σ' : ℂ ≃+* ℂ, Fixes φK σ → Fixes φK σ' →
    (ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') ↔ σ j₀ = σ' j₀)) ∧
  ∀ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L → IsGalois ℚ L → (∀ x : K, φK x ∈ L) → j₀ ∈ L →
    ∀ C : ClassGroup (𝓞 K),
      Nat.card {τ : L →+* ℂ // ∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧ ClassGroup.mk K (𝔞 σ) = C}
        * (2 * classNumber K) = Module.finrank ℚ L

end Quadratic

section CM

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def lamF (s : ℕ) (χ : HChar E) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

def IsConjWt (φ : I → E →+* ℂ) (σ : ℂ ≃+* ℂ) (κ κ' : I → ℕ) : Prop :=
  ∀ i j : I, (∀ x : E, σ (φ i x) = φ j x) → κ' j = κ i

def IsConjChar (φ : I → E →+* ℂ) (s : ℕ) (κ' : I → ℕ) (σ : ℂ ≃+* ℂ) (χ χ' : HChar E) : Prop :=
  (∀ y : (Af E)ˣ, lamF s χ' y = σ (lamF s χ y)) ∧ HasInf χ' φ (fun i => (κ' i : ℤ) + s)

def IsValSum (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E)))
    (χ : HChar E) (T : ℂ) : Prop :=
  IsFinSetSplitPlacesCoprimeConductor 𝔣 Q ∧ IsValChar φ s κ 𝔣 Q χ ∧ IsToricSum φ s κ (condQ 𝔣 Q) χ T

def IsConjSum (φ : I → E →+* ℂ) (s : ℕ) (κ' : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E)))
    (σ : ℂ ≃+* ℂ) (χ χ' : HChar E) (T' : ℂ) : Prop :=
  IsConjChar φ s κ' σ χ χ' ∧ IsToricSum φ s κ' (condQ 𝔣 Q) χ' T'

end CM

def upIdele (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] : (Af K)ˣ →* (Af E)ˣ :=
  Units.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K E).toMonoidHom

def TransportFor {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I]
    (d : ℕ) (φK : K →+* ℂ) (ΛK : PeriodPair) (t : (ℂ ≃+* ℂ) → (Af K)ˣ)
    (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair)
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) : Prop :=
  (∀ (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ), IsValSum φ s κ 𝔣 Q χ T →
    IsAlgebraic ℚ (beta E d s κ ΛK T) ∧
    ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∀ κ' : I → ℕ, IsConjWt φ σ κ κ' →
      ∀ (χ' : HChar E) (T' : ℂ), IsConjSum φ s κ' 𝔣 Q σ χ χ' T' →
        σ (beta E d s κ ΛK T) =
          ((C0 E d (2 * s) κ : ℂ) * ((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ (∑ i, κ i))⁻¹ *
              (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') ^ 12 / latDisc (Λ σ) ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i) ∧
        ‖σ (beta E d s κ ΛK T)‖ =
          (C0 E d (2 * s) κ * ‖T'‖) ^ 12 *
            ((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (Λ σ)‖) ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i))⁻¹) ∧
  (∀ (Q₁ Q₂ : Finset (HeightOneSpectrum (OF E))) (χ₁ χ₂ : HChar E) (T₁ T₂ : ℂ),
    IsValSum φ s κ 𝔣 Q₁ χ₁ T₁ → IsValSum φ s κ 𝔣 Q₂ χ₂ T₂ → T₂ ≠ 0 →
    IsAlgebraic ℚ (T₁ / T₂) ∧
    ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∀ κ' : I → ℕ, IsConjWt φ σ κ κ' →
      ∀ (χ₁' χ₂' : HChar E) (T₁' T₂' : ℂ), IsConjSum φ s κ' 𝔣 Q₁ σ χ₁ χ₁' T₁' → IsConjSum φ s κ' 𝔣 Q₂ σ χ₂ χ₂' T₂' →
        T₂' ≠ 0 ∧
        σ (T₁ / T₂) = ((lamF s χ₁' (upIdele K E (t σ)))⁻¹ * T₁') / ((lamF s χ₂' (upIdele K E (t σ)))⁻¹ * T₂'))

def Transport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ), 4 < d → Module.finrank ℚ K = 2 → discr K = -(d : ℤ) →
  ∀ (φK : K →+* ℂ) (ΛK : PeriodPair), IsLatOf φK 1 ΛK →
  ∃ (t : (ℂ ≃+* ℂ) → (Af K)ˣ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair),
    (∀ σ : ℂ ≃+* ℂ, Fixes φK σ →
      IsInvIdealOf (t σ) (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ∧ IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) (Λ σ) ∧
        jLat (Λ σ) = σ (jLat ΛK)) ∧
    Equidistributed φK (jLat ΛK) 𝔞 ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] [Algebra K E], UnramFin E →
    ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ), 2 ≤ Fintype.card I → IsCMType φ →
      (∀ i, (φ i).comp (algebraMap K E) = φK) →
    ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)), 1 ≤ s → (∀ i, 1 ≤ κ i) → IsBaseCond 𝔣 →
      TransportFor d φK ΛK t 𝔞 Λ φ s κ 𝔣

theorem nrm_ne_zero {K : Type} [Field K] [NumberField K] (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  unfold nrm
  have : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := fun h =>
    𝔞.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this

theorem lamF_ne_zero {E : Type} [Field E] [NumberField E] (s : ℕ) (χ : HChar E) (y : (Af E)ˣ) : lamF s χ y ≠ 0 := by
  have h : 0 < modF y := by
    unfold modF
    refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos ?_ _
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.pos_of_ne_zero this
  exact mul_ne_zero (Units.ne_zero _) (by exact_mod_cast (pow_pos h s).ne')

example {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) (n l T : ℂ) :
    ((C0 E d (2 * s) κ : ℂ) * n * l * T) ^ 12 / latDisc Λ ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i) =
      beta E d s κ Λ (n * l * T) := by
  rw [beta_eq]; ring

example {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (χ : HChar E)
    (h : HasInf χ φ fun i => (κ i : ℤ) + s) : IsConjChar φ s κ (RingEquiv.refl ℂ) χ χ := ⟨fun _ => rfl, h⟩

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

variable {E : Type} [Field E] [NumberField E]

def latMod (c : Ideal (OF E)) (y : (Af E)ˣ) : Submodule (OF E) E where
  carrier := lattice c y
  zero_mem' := (latticeSub c y).zero_mem
  add_mem' := fun ha hb => (latticeSub c y).add_mem ha hb
  smul_mem' := fun a x hx => by
    rw [Algebra.smul_def]
    exact mul_mem_lattice (algebraMap_mem_orderC c a) hx

@[simp] theorem coe_latMod (c : Ideal (OF E)) (y : (Af E)ˣ) : (latMod c y : Set E) = lattice c y := rfl

def TrInt (x : E) : Prop := ∃ n : ℤ, Algebra.trace ℚ E x = n

theorem TrInt.zero : TrInt (0 : E) := ⟨0, by simp⟩

theorem TrInt.add {x y : E} (hx : TrInt x) (hy : TrInt y) : TrInt (x + y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m + n, by rw [map_add, hm, hn]; push_cast; rfl⟩

variable [IsCMField E]

abbrev bar (x : E) : E := IsCMField.complexConj E x

theorem bar_algebraMap (a : OF E) : bar (algebraMap (OF E) E a) = algebraMap (OF E) E a :=
  (IsCMField.complexConj E).commutes (a : maximalRealSubfield E)

def dualLat (L : Submodule (OF E) E) : Submodule (OF E) E where
  carrier := {z | ∀ x ∈ L, TrInt (z * bar x)}
  zero_mem' := fun x _ => by rw [zero_mul]; exact TrInt.zero
  add_mem' := fun ha hb x hx => by rw [add_mul]; exact (ha x hx).add (hb x hx)
  smul_mem' := fun a z hz x hx => by
    have h := hz (a • x) (L.smul_mem a hx)
    have e : z * bar (a • x) = a • z * bar x := by
      rw [Algebra.smul_def, Algebra.smul_def, bar, map_mul, ← bar, bar_algebraMap]; ring
    rwa [e] at h

def polMod (L : Submodule (OF E) E) : Submodule (OF E) E where
  carrier := {ξ | bar ξ = -ξ ∧ ∀ x ∈ L, ∀ y ∈ L, TrInt (ξ * x * bar y)}
  zero_mem' := ⟨by simp, fun x _ y _ => by rw [zero_mul, zero_mul]; exact TrInt.zero⟩
  add_mem' := fun {a b} ha hb => ⟨by
      have h1 := ha.1
      have h2 := hb.1
      simp only [bar] at h1 h2 ⊢
      rw [map_add, h1, h2]; ring,
    fun x hx y hy => by rw [add_mul, add_mul]; exact (ha.2 x hx y hy).add (hb.2 x hx y hy)⟩
  smul_mem' := fun a ξ hξ => ⟨by
      have h1 := hξ.1
      rw [Algebra.smul_def, bar, map_mul, ← bar, ← bar, bar_algebraMap, h1]; ring,
    fun x hx y hy => by
      have h := hξ.2 (a • x) (L.smul_mem a hx) y hy
      have e : ξ * (a • x) = a • ξ * x := by rw [Algebra.smul_def, Algebra.smul_def]; ring
      rwa [e] at h⟩

def polPos {I : Type} (φ : I → E →+* ℂ) (e₀ : ℤˣ) (L : Submodule (OF E) E) : Set E :=
  {ξ | ξ ∈ polMod L ∧ ∀ i, 0 < ((e₀ : ℤ) : ℝ) * (φ i ξ).im}

def GenAt (l : ℕ) (M : Submodule (OF E) E) (ξ : E) : Prop :=
  ξ ∈ M ∧ ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : OF E, (n : E) * η = algebraMap (OF E) E a * ξ

def mulLat (ξ : E) (L : Submodule (OF E) E) : Submodule (OF E) E := L.map (LinearMap.mulLeft (OF E) ξ)

def polIndex (ξ : E) (L : Submodule (OF E) E) : ℕ := (mulLat ξ L).toAddSubgroup.relIndex (dualLat L).toAddSubgroup

def ModulePart {I : Type} (φ : I → E →+* ℂ) (e₀ : ℤˣ) : Prop :=
  ∀ (c : Ideal (OF E)), c ≠ ⊥ → ∀ y : (Af E)ˣ,
    Module.Invertible (OF E) (polMod (latMod c y)) ∧
    polMod (latMod c y) * latMod c y = dualLat (latMod c y) ∧
    (polPos φ e₀ (latMod c y)).Nonempty ∧
    ∀ l : ℕ, l.Prime →
      (∃ ξ ∈ polPos φ e₀ (latMod c y), GenAt l (polMod (latMod c y)) ξ) ∧
      ∀ ξ ∈ polPos φ e₀ (latMod c y), GenAt l (polMod (latMod c y)) ξ →
        mulLat ξ (latMod c y) ≤ dualLat (latMod c y) ∧ polIndex ξ (latMod c y) ≠ 0 ∧ (polIndex ξ (latMod c y)).Coprime l

def SizePart {I : Type} (φ : I → E →+* ℂ) (e₀ : ℤˣ) : Prop :=
  ∀ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q →
    ∀ l : ℕ, l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
      ∀ y : (Af E)ˣ, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (y : Af E) P = 1) →
        ∀ ξ ∈ polPos φ e₀ (latMod (condQ 𝔣 Q) y), GenAt l (polMod (latMod (condQ 𝔣 Q) y)) ξ →
          ξ ≠ 0 ∧ (∀ σ : E →+* ℂ, IntAt l (σ ξ)⁻¹) ∧
          (¬ (l : ℤ) ∣ discr E → (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 → (l : OF E) ∉ v.asIdeal) →
            ∀ σ : E →+* ℂ, UnitAt l (σ ξ))

def PolarisationModule : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], UnramFin E →
    ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ → ∀ e₀ : ℤˣ, ModulePart φ e₀ ∧ SizePart φ e₀

def PolarisationModuleInduced : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], UnramFin E →
    ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
      ∀ (d : ℕ) (δ : E), 0 < d → δ ^ 2 = -(d : E) → (∀ i, φ i δ = Complex.I * (Real.sqrt d : ℝ)) →
        ∀ e₀ : ℤˣ, ModulePart φ e₀ ∧ SizePart φ e₀

theorem polMod_mul_le (L : Submodule (OF E) E) : polMod L * L ≤ dualLat L :=
  Submodule.mul_le.2 fun _ hξ x hx y hy => hξ.2 x hx y hy

example {I : Type} (φ : I → E →+* ℂ) (e₀ : ℤˣ) (L : Submodule (OF E) E) (ξ : E) :
    ξ ∈ polPos φ (-e₀) L ↔ -ξ ∈ polPos φ e₀ L := by
  simp [polPos]

example {I : Type} [Nonempty I] (φ : I → E →+* ℂ) (e₀ : ℤˣ) (L : Submodule (OF E) E) : (0 : E) ∉ polPos φ e₀ L :=
  fun h => by simpa using h.2 (Classical.arbitrary I)

end GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
section
noncomputable section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

variable {E : Type} [Field E] [NumberField E]

def ValGe_vp (l : ℕ) (r : ℝ) (a : ℂ) : Prop :=
  ∀ (m : ℤ) (n : ℕ), 0 < n → r ≤ (m : ℝ) / n → IntAt l ((l : ℂ) ^ m * a ^ n)

def IsClassZeta (C : ClassGroup (OF E)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun 𝔞 : {𝔞 : (Ideal (OF E))⁰ // ClassGroup.mk0 𝔞 = C} =>
      ((Ideal.absNorm (𝔞.1 : Ideal (OF E)) : ℕ) : ℂ) ^ (-s)) (Z s)

def IsClassZetaVals (k : ℕ) (z : ClassGroup (OF E) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)

def cE_vp (l : ℕ) (z : ClassGroup (OF E) → ℚ) : ℕ :=
  Finset.univ.sup fun C => (-padicValRat l (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E))).toNat

def delta_vp (E : Type) [Field E] [NumberField E] (l : ℕ) : ℝ :=
  (padicValInt l (discr E) : ℝ) / (Module.finrank ℚ E : ℝ)

def a0 (𝔣 : Ideal (OF E)) (l : ℕ) : ℕ :=
  sSup {n | ∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ expIn 𝔣 v = n}

open Classical in

def c_vp (𝔣 : Ideal (OF E)) (l : ℕ) : ℝ :=
  if ∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ v.asIdeal ∣ 𝔣 then (a0 𝔣 l : ℝ) else delta_vp E l

variable {I : Type} [Fintype I]

open Classical in

def n_vp (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (l : ℕ) : ℝ :=
  if c_vp 𝔣 l = 0 then 0
  else Formalism.PairingDivisionLocalBalance.nl ((2 * s * Fintype.card I : ℕ) : ℝ) (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) (c_vp 𝔣 l)
    ((if l = 2 then 1 else 0) + (if l = d then 1 / 2 else 0))

def IsFieldData (d : ℕ) (φ : I → E →+* ℂ) : Prop :=
  d.Prime ∧ 4 < d ∧ UnramFin E ∧ (∀ x : E, IsOfFinOrder x → ∏ i, φ i x = 1) ∧ (2 : ℤ) ∣ discr E ∧
    2 ≤ Fintype.card I ∧ IsCMType φ ∧ ∃ w : E, w ^ 2 = -(d : E) ∧ ∀ i, φ i w = Complex.I * (Real.sqrt d : ℝ)

def IsIntLattice (d : ℕ) (Λ : PeriodPair) : Prop :=
  ∀ x : ℂ, x ∈ Λ.lattice ↔ IsIntegral ℤ x ∧ ∃ a b : ℚ, x = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt d : ℝ))

def IsClassTerm (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (y : (Af E)ˣ) (T : ℂ) : Prop :=
  ∃ S : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y) S ∧ T = ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0

def IsPicChar (c : Ideal (OF E)) (ψ : HChar E) : Prop :=
  (∀ x : Eˣ, infPart ψ x = 1) ∧ ∀ u ∈ hatOUnits c, finPart ψ u = 1

def IsLevelChar (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (χ : HChar E) : Prop :=
  IsUnitary χ ∧ TrivOnF χ ∧ HasInf χ φ (fun i => (κ i : ℤ) + s) ∧
    ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Over P v → LevelLe χ P (expIn 𝔣 v)

def betaBound_vp (d s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (z : ClassGroup (OF E) → ℚ) (l : ℕ) : ℝ :=
  12 * ((cE_vp l z : ℝ) + n_vp d s κ 𝔣 l + (Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ : ℝ) * (a0 𝔣 l : ℝ))

def DenomBound (d s : ℕ) (φ : I → E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Λ : PeriodPair)
    (z : ClassGroup (OF E) → ℚ) (χ : HChar E) : Prop :=
  ∀ l : ℕ, l.Prime → ∀ Q : Finset (HeightOneSpectrum (OF E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    (∀ (y : (Af E)ˣ) (T : ℂ), IsClassTerm φ s κ (condQ 𝔣 Q) χ y T →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ T)) ∧
    (∀ (ψ : HChar E) (T : ℂ), IsPicChar (condQ 𝔣 Q) ψ → IsToricSum φ s κ (condQ 𝔣 Q) (χ * ψ) T →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ T))

def ToricDenominator : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I]
    (d : ℕ) (φ : I → E →+* ℂ) (s : ℕ), IsFieldData d φ → 1 ≤ s →
    ∃ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z ∧
      ∀ (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Λ : PeriodPair) (χ : HChar E),
        IsBaseCond 𝔣 → IsIntLattice d Λ → IsValChar φ s κ 𝔣 ∅ χ → DenomBound d s φ κ 𝔣 Λ z χ

def ToricDenominatorLevel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I]
    (d : ℕ) (φ : I → E →+* ℂ) (s : ℕ), IsFieldData d φ → 1 ≤ s →
    ∃ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z ∧
      ∀ (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Λ : PeriodPair) (χ : HChar E),
        IsBaseCond 𝔣 → IsIntLattice d Λ → IsLevelChar φ s κ 𝔣 χ → DenomBound d s φ κ 𝔣 Λ z χ

theorem ToricDenominatorLevel.exact (h : ToricDenominatorLevel) : ToricDenominator := by
  intro E _ _ _ _ I _ d φ s hd hs
  obtain ⟨z, hz, H⟩ := h E I d φ s hd hs
  refine ⟨z, hz, fun κ 𝔣 Λ χ h𝔣 hΛ hχ => H κ 𝔣 Λ χ h𝔣 hΛ ⟨hχ.1, hχ.2.1, hχ.2.2.1, fun v P hP => ?_⟩⟩
  exact (((hχ.2.2.2 v P hP).2 (by simp)) _).2 le_rfl

theorem expIn_le_two {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) (v : HeightOneSpectrum (OF E)) : expIn 𝔣 v ≤ 2 := by
  by_cases hv : v.asIdeal ∣ 𝔣
  · exact (h.2.2 v hv).2.1
  · rw [expIn, multiplicity_eq_zero.2 hv]; omega

theorem expIn_le_maxConductorExponentOverPrime {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) {l : ℕ} {v : HeightOneSpectrum (OF E)}
    (hv : (l : OF E) ∈ v.asIdeal) : expIn 𝔣 v ≤ a0 𝔣 l :=
  le_csSup ⟨2, by rintro _ ⟨w, -, rfl⟩; exact expIn_le_two h w⟩ ⟨v, hv, rfl⟩

example (l : ℕ) (a : ℂ) (h : ValGe_vp l 0 a) : IntAt l a := by
  simpa using h 0 1 one_pos (by simp)

example (c : Ideal (OF E)) : IsPicChar c (1 : HChar E) := ⟨fun _ => rfl, fun _ _ => rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
end
end

