import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.DiracOfDiracZeroModule
section
noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

structure IsCoreMod0 {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (χ : Inf n)
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) : Prop where
  pair : IsPair E1 E2
  ch1 : ∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (χ true) m • x
  ch2 : ∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (χ false) m • x
  nontriv : Nontrivial V
  irr : ∀ v w : V, v ≠ 0 → ∃ x ∈ alg E1 E2, x v = w
  der : IsDerivK σ (kF E1 E2)

theorem IsCoreMod.toCoreMod0 {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {χ : Inf n}
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {A : V →ₗ[ℂ] V}
    (h : IsCoreMod χ E1 E2 σ A) : IsCoreMod0 χ E1 E2 σ :=
  ⟨h.pair, h.ch1, h.ch2, h.nontriv, h.irr, h.der⟩

def DiracInequalityWithoutSplitComponent : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)),
    IsCoreMod0 (infOf lam) E1 E2 σ → ∀ ν : Fin n → ℝ, hwSp E1 E2 ν ≠ ⊥ → LSq lam ≤ spinSq ν

def AdmLeast0 : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)),
    IsCoreMod0 (infOf lam) E1 E2 σ → ∀ lev : Fin n → ℕ, IsLev lam lev → hwSp E1 E2 (muQ lam lev) ≠ ⊥ →
      (∀ lev' : Fin n → ℕ, IsLev lam lev' → hwSp E1 E2 (muQ lam lev') ≠ ⊥ →
        nsq (muQ lam lev + rhoV n) ≤ nsq (muQ lam lev' + rhoV n)) → AdmFor lam lev E1 E2

theorem adm_least_of_zero_module (h : AdmLeast0) : AdmLeast := fun n lam hlam V _ _ E1 E2 σ _ hc => h n lam hlam V E1 E2 σ hc.toCoreMod0

theorem adm_least_zero_of_dirac (hN : SecondTypeWeightsShorter) (hD : DiracInequalityWithoutSplitComponent) (hH : LemmaHT) : AdmLeast0 := by
  intro n lam hlam V _ _ E1 E2 σ hc lev hlev _ hleast
  refine ⟨hc.pair.gl1, hc.pair.gl2, hc.pair.comm, hc.pair.unitK, fun x => ?_, hc.ch1, hc.ch2, fun ν hν => ?_⟩
  · obtain ⟨S, hS, hxS, -, hK, -⟩ := hc.der.2 x
    exact ⟨S, hS, hxS, hK⟩
  · by_contra hne
    obtain ⟨hνT, hlt⟩ := hN n lam hlam lev hlev ν hν
    have hνh : ν ∈ harmSet lam := ((hH n lam hlam).2 ν hνT).2
      (le_antisymm ((hH n lam hlam).2 ν hνT).1 (hD n lam hlam V E1 E2 σ hc ν hne))
    classical
    simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hνh
    obtain ⟨lev', hlev', rfl⟩ := hνh
    exact absurd (hleast _ hlev' hne) (not_le.2 hlt)

end PositivityTheory.RgBcC.RealD
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HarmTop
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC.Real

variable {n : ℕ}

def hwK {W : Type*} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W) (μ : Fin n → ℝ) : Submodule ℂ W where
  carrier := {v | Formalism.REAL.KHighest (fun _ => true) F μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add, hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add, hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm], fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

def IsDerE (E : KMod n) (F : Fin n → Fin n → Module.End ℂ E.V) : Prop :=
  ∀ (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) →
    ∀ w : E.V, HasDerivAt (fun t : ℝ => E.ρ (γ t) w) (∑ a, ∑ b, X a b • F a b w) 0

def dualF (E : KMod n) (F : Fin n → Fin n → Module.End ℂ E.V) : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ) :=
  fun a b => -((ContinuousLinearMap.compL ℂ E.V E.V ℂ).flip (LinearMap.toContinuousLinearMap (F a b))).toLinearMap

def castW (ν : Fin n → ℤ) : Fin n → ℝ := fun a => (ν a : ℝ)

def chE (lam : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam z ^ 2

def tchE (lam : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam fun a => z a ^ 2

def IsExp (f : (Fin n → ℂ) → ℂ) (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℤ) : Prop :=
  (∀ ν ∈ S, Antitone ν) ∧ ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
    f z = ∑ ν ∈ S, (c ν : ℂ) * weylChar ν z

def DerEx : Prop := ∀ (n : ℕ) (E : KMod n), ∃ F, IsDerE E F

def HomDec : Prop :=
  ∀ (n : ℕ) (χ : Inf n) (E : KMod n) (T : E.V →L[ℂ] E.V) (F : Fin n → Fin n → Module.End ℂ E.V), IsDerE E F →
    (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsCoreMod χ E1 E2 σ A →
      FiniteDimensional ℂ (invA σ E) →
      ∃ S : Finset (Fin n → ℝ), (∀ ν, hwK (dualF E F) ν ≠ ⊥ ↔ ν ∈ S) ∧
        (∀ ν ∈ S, FiniteDimensional ℂ (hwSp E1 E2 ν)) ∧ (invA σ E ≠ ⊥ → ∃ ν ∈ S, hwSp E1 E2 ν ≠ ⊥) ∧
        trOn (invA σ E) (flipA E A T) =
          ∑ ν ∈ S, trOn (hwK (dualF E F) ν) (dualT E T).toLinearMap * trOn (hwSp E1 E2 ν) A

def WtE : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) (F : Fin n → Fin n → Module.End ℂ E.V), IsLefK lam E T →
    IsDerE E F → ∀ (S : Finset (Fin n → ℤ)) (d c : (Fin n → ℤ) → ℤ), IsExp (chE lam) S d → IsExp (tchE lam) S c →
      (∀ μ : Fin n → ℝ, hwK (dualF E F) μ ≠ ⊥ → ∃ ν ∈ S, castW ν = μ ∧ d ν ≠ 0) ∧
      ∀ ν ∈ S, Module.finrank ℂ (hwK (dualF E F) (castW ν)) = d ν ∧
        trOn (hwK (dualF E F) (castW ν)) (dualT E T).toLinearMap = c ν

def ExpEx : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∃ (S : Finset (Fin n → ℤ)) (d c : (Fin n → ℤ) → ℤ),
    IsExp (chE lam) S d ∧ IsExp (tchE lam) S c

def CoefE : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (S : Finset (Fin n → ℤ)) (d c : (Fin n → ℤ) → ℤ),
    IsExp (chE lam) S d → IsExp (tchE lam) S c →
      (∀ ν ∈ S, d ν ≠ 0 → inCone (fun a => (a : ℕ)) (m0 lam - castW ν)) ∧
      ∀ μ ∈ harmSet lam, ∃ ν ∈ S, castW ν = μ ∧ d ν ≠ 0 ∧ c ν = 2 ^ n

def DomSel : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ ν : Fin n → ℤ, Antitone ν →
    inCone (fun a => (a : ℕ)) (m0 lam - castW ν) → LSq lam ≤ spinSq (castW ν) → castW ν ∈ harmSet lam

def HarmTop : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → harmSet lam ⊆ topTypes lam

end PositivityTheory.RgBcC.RealD
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
section
noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

open Formalism.REAL (GlRel)

def LeviCommutantWordReduction : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ b : FreeAlgebra ℂ (Bool × Fin n × Fin n), InvLv lev b →
    ∀ ν : Fin n → ℝ, (∀ a c, lev a = lev c → ν a = ν c) → ∃ z : FreeAlgebra ℂ (ℕ × ℂ),
      ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
        ∀ h : H, (∀ a c, lev a = lev c → (F1 a c + F2 a c) h = if a = c then (ν a : ℂ) • h else 0) →
          evLv lev F1 F2 b h = evCap lev F1 z h

def CapelliProductsScalar : Prop :=
  ∀ (n : ℕ) (L : Fin n → ℝ), StrictAnti L → ∀ lev : Fin n → ℕ, Monotone lev → ∀ (ν : Fin n → ℝ) (σ1 σ2 : ℕ → ℂ),
    (∀ j, (∑ a ∈ blk lev j, (ν a : ℂ)) - ((blk lev j).card : ℂ) * (σ1 j + σ2 j) = 2 * ∑ a ∈ blk lev j, (L a : ℂ)) →
    ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
    ∀ c : H, (∀ a b, lev a = lev b → (F1 a b + F2 a b) c = if a = b then (ν a : ℂ) • c else 0) →
      (∀ u : ℂ, capProd F1 lev σ1 u c = (∏ a, (u + (L a : ℂ))) • c) →
      (∀ u : ℂ, capProd F2 lev σ2 u c = (∏ a, (u + (L a : ℂ))) • c) →
      ∀ j u, capS F1 lev j u c = (∏ a ∈ blk lev j, (u + σ1 j + (L a : ℂ))) • c

def InvPick : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), AdmFor lam lev E1 E2 → ∀ (μ : Fin n → ℝ) (v w : V),
    v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → v ≠ 0 → (∃ x ∈ alg E1 E2, x v = w) → ∃ a, InvKP n a ∧ evKP E1 E2 a v = w

def LevStab : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 → ∀ p q, lev p = lev q →
      ∀ x ∈ bdSub lev E1 E2, firstLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2 ∧ secondLeviFamily lev E1 E2 p q x ∈ bdSub lev E1 E2

def LevRel : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 → IsLevPairA lev (firstLeviFamily lev E1 E2) (secondLeviFamily lev E1 E2)

def SemiCls : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v ∈ hwSp E1 E2 (muQ lam lev), ∀ a c, lev a = lev c →
        (firstLeviFamily lev E1 E2 a c + secondLeviFamily lev E1 E2 a c) (Pi.single (omU lev) v) =
          if a = c then ((muQ lam lev a + 2 * rhoU lev a : ℝ) : ℂ) • Pi.single (omU lev) v else 0

def CapCls : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∃ σ1 σ2 : ℕ → ℂ,
    (∀ j, (∑ a ∈ blk lev j, ((muQ lam lev a + 2 * rhoU lev a : ℝ) : ℂ)) - ((blk lev j).card : ℂ) * (σ1 j + σ2 j) =
      2 * ∑ a ∈ blk lev j, (Lr lam a : ℂ)) ∧
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v ∈ hwSp E1 E2 (muQ lam lev), ∀ u : ℂ,
        capProd (firstLeviFamily lev E1 E2) lev σ1 u (Pi.single (omU lev) v : Cq n V) - (∏ a, (u + (Lr lam a : ℂ))) • (Pi.single (omU lev) v : Cq n V) ∈
            bdSub lev E1 E2 ∧
        capProd (secondLeviFamily lev E1 E2) lev σ2 u (Pi.single (omU lev) v : Cq n V) - (∏ a, (u + (Lr lam a : ℂ))) • (Pi.single (omU lev) v : Cq n V) ∈
            bdSub lev E1 E2

def MultiplicityAssembly : Prop :=
  InvPick → InjUU → HCdecLv → ActUU → LevStab → LevRel → SemiCls → CapCls → LeviCommutantWordReduction → CapelliProductsScalar → MultFor

end PositivityTheory.RgBcC.RealD
end
end

