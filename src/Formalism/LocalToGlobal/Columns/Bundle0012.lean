import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteEtaGenerators.CompEqEmbedding
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfinityTypeCharacter.ContinuousUnitsMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GlobalFormGenerator.IntValuationConjP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostFieldFacts.HostFieldFacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTypeEmbeddings.OnePsi
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0009
import Formalism.LocalToGlobal.Columns.Bundle0008
import Formalism.LocalToGlobal.Columns.MemOfSmulMemOfAddEqOne
import Formalism.LocalToGlobal.Columns.CardPathsEqSubmodulePairs
import Formalism.LocalToGlobal.Columns.NeighbourConjOfTopNeighbour

-- bundled from Formalism.LocalToGlobal.Columns.HeckeEx
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Col

namespace HeckeEx

open Formalism.L2.Host Formalism.L2.Host.CharEx

section Gen

variable {L : Type} [Field L] [NumberField L]

def compU (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* (w.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun a => a.2 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem exists_unifO (w : HeightOneSpectrum (𝓞 L)) : ∃ ϖ : 𝓞 L, ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 := by
  have hlt : w.asIdeal ^ 2 < w.asIdeal := Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl
  obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt hlt
  exact ⟨x, hx, hx2⟩

def resU (w : HeightOneSpectrum (𝓞 L)) (y : 𝓞 L) (hy : y ∉ w.asIdeal) : (𝓞 L ⧸ w.asIdeal)ˣ :=
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  Units.mk0 (Ideal.Quotient.mk w.asIdeal y) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])

theorem ne_zero_of_notMem {w : HeightOneSpectrum (𝓞 L)} {y : 𝓞 L} (hy : y ∉ w.asIdeal) : (y : L) ≠ 0 := by
  intro h
  apply hy
  have : y = 0 := by exact_mod_cast h
  rw [this]
  exact w.asIdeal.zero_mem

def unitO {w : HeightOneSpectrum (𝓞 L)} (y : 𝓞 L) (hy : y ∉ w.asIdeal) : Lˣ := Units.mk0 (y : L) (ne_zero_of_notMem hy)

def TameSpec (w : HeightOneSpectrum (𝓞 L)) (ϖ : 𝓞 L) (c : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ) (lam : (w.adicCompletion L)ˣ →* ℂˣ) : Prop :=
  (∀ x : Lˣ, (x : L) = (ϖ : L) → lam (atFin w x) = 1) ∧
  (∀ x, IsUnitAt w x → ‖((lam x : ℂˣ) : ℂ)‖ = 1) ∧
  (∀ x, IsUnitAt w x → Valued.v ((x : w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) → lam x = 1) ∧
  (∀ (x : Lˣ) (y : 𝓞 L) (cl : (𝓞 L ⧸ w.asIdeal)ˣ), (x : L) = (y : L) →
    (cl : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → lam (atFin w x) = c cl)

def TameLocEx : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (ϖ : 𝓞 L), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 →
    ∀ c : (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ, ∃ lam : (w.adicCompletion L)ˣ →* ℂˣ, TameSpec w ϖ c lam

def LocRep : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (ϖ : 𝓞 L), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 →
    ∀ x : L, x ≠ 0 → ∃ (y z : 𝓞 L) (n : ℤ), y ∉ w.asIdeal ∧ z ∉ w.asIdeal ∧ x * (z : L) = (y : L) * (ϖ : L) ^ n

def tameSet (L : Type) [Field L] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 L))) : Set (Ideles L) :=
  {u | u ∈ unitIdeles L ∧ ∀ w ∈ S, Valued.v ((u : AdeleRing (𝓞 L) L).2 w - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ))}

def OpenTame : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 L))), IsOpen (tameSet L S)

end Gen

section Col

variable {X : Fields}

theorem hxConjO_invol (X : Fields) (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  show star (star (x : X.E)) = x
  exact star_star _

def cP (X : Fields) (w : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := w.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro h
    have h1 : X.conjO p ∈ w.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, hxConjO_invol X]; exact hp
    rw [h, Ideal.mem_bot] at h1
    apply hp0
    rw [← hxConjO_invol X p, h1, map_zero]

theorem mem_cP (w : HeightOneSpectrum (𝓞 X.E)) (r : 𝓞 X.E) : r ∈ (cP X w).asIdeal ↔ X.conjO r ∈ w.asIdeal := Iff.rfl

theorem conj_mem_cP {w : HeightOneSpectrum (𝓞 X.E)} {y : 𝓞 X.E} (hy : y ∈ w.asIdeal) : X.conjO y ∈ (cP X w).asIdeal := by
  rw [mem_cP, hxConjO_invol X]; exact hy

theorem conj_notMem_sq_cP {w : HeightOneSpectrum (𝓞 X.E)} {y : 𝓞 X.E} (hy : y ∉ w.asIdeal ^ 2) :
    X.conjO y ∉ (cP X w).asIdeal ^ 2 := by
  intro h
  have h2 : (cP X w).asIdeal ^ 2 ≤ (w.asIdeal ^ 2).comap X.conjO := Ideal.le_comap_pow _ 2
  have h3 := h2 h
  rw [Ideal.mem_comap, hxConjO_invol X] at h3
  exact hy h3

def conjU (X : Fields) : X.Eˣ →* X.Eˣ := Units.map (starRingEnd X.E).toMonoidHom

def resConj (X : Fields) (w : HeightOneSpectrum (𝓞 X.E)) : 𝓞 X.E ⧸ (cP X w).asIdeal →+* 𝓞 X.E ⧸ w.asIdeal :=
  Ideal.quotientMap w.asIdeal X.conjO le_rfl

variable {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (j : Fin m)

def cW (w : {w // w ∈ Pr.vGs}) : (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* ℂˣ :=
  ((Units.map σ₀.toMonoidHom).comp (Ch.chi j w))⁻¹

def cB (w : {w // w ∈ Pr.vGs}) : (𝓞 X.E ⧸ (cP X w.1).asIdeal)ˣ →* ℂˣ :=
  ((cW Ch σ₀ j w).comp (Units.map (resConj X w.1).toMonoidHom))⁻¹

def unifW (w : HeightOneSpectrum (𝓞 X.E)) : 𝓞 X.E := (exists_unifO w).choose

theorem unifW_mem (w : HeightOneSpectrum (𝓞 X.E)) : unifW w ∈ w.asIdeal := (exists_unifO w).choose_spec.1

theorem unifW_notMem (w : HeightOneSpectrum (𝓞 X.E)) : unifW w ∉ w.asIdeal ^ 2 := (exists_unifO w).choose_spec.2

variable (hT : TameLocEx)

def lamW (w : {w // w ∈ Pr.vGs}) : (w.1.adicCompletion X.E)ˣ →* ℂˣ :=
  (hT X.E w.1 (unifW w.1) (unifW_mem w.1) (unifW_notMem w.1) (cW Ch σ₀ j w)).choose

def lamB (w : {w // w ∈ Pr.vGs}) : ((cP X w.1).adicCompletion X.E)ˣ →* ℂˣ :=
  (hT X.E (cP X w.1) (X.conjO (unifW w.1)) (conj_mem_cP (unifW_mem w.1)) (conj_notMem_sq_cP (unifW_notMem w.1))
    (cB Ch σ₀ j w)).choose

def psiF : Ideles X.E →* ℂˣ :=
  ∏ w : {w // w ∈ Pr.vGs}, ((lamW Ch σ₀ j hT w).comp (compU w.1) * (lamB Ch σ₀ j hT w).comp (compU (cP X w.1)))

variable {Ch σ₀ j hT}

theorem conjPrime_under₂ (hX : X.Ok) (w : HeightOneSpectrum (𝓞 X.E)) : (cP X w).under (𝓞 X.F) = w.under (𝓞 X.F) := by
  apply HeightOneSpectrum.ext
  ext r
  show X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) r) ∈ w.asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) r ∈ w.asIdeal
  have e : X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r := by
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 X.F) (𝓞 X.E) r : 𝓞 X.E) : X.E) = _
    have e2 : ((algebraMap (𝓞 X.F) (𝓞 X.E) r : 𝓞 X.E) : X.E) = algebraMap X.F X.E (r : X.F) := rfl
    rw [e2, hX.star_F]
  rw [e]

variable (Ch σ₀ j hT)

open Classical in

def ramS : Finset (HeightOneSpectrum (𝓞 X.E)) := Pr.vGs ∪ Pr.vGs.image (cP X)

end Col

section Eta

variable {X : Fields}

open Classical in

structure EtaFactsC (X : Fields) (σ₀ : X.K →+* ℂ) (s0 : X.E) : Prop where
  unram : ∀ P : HeightOneSpectrum (𝓞 X.E), (aboveF (L := X.E) X.F (P.under (𝓞 X.F))).card = 1 →
    P.asIdeal.ramificationIdx (𝓞 X.F) = 1
  onePsi : ∀ w : InfinitePlace X.F,
    (Finset.univ.filter (fun i => InfinitePlace.mk (X.embC σ₀ i) ∈ aboveInf (L := X.E) X.F w)).card = 1
  fixF : ∀ x : X.E, star x = x → ∃ a : X.F, algebraMap X.F X.E a = x
  roots : ∀ z : X.E, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → z = 1 ∨ z = -1
  sqrt_ne : s0 ≠ 0
  isCMField_complexConj_s_eq_neg : star s0 = -s0
  sqrt_pos : ∀ s : X.Eˣ, (s : X.E) = s0 → ∀ i, ∃ r : ℝ, 0 < r ∧ X.embC σ₀ i (s : X.E) = Complex.I * r
  card4 : 4 ∣ Fintype.card X.Tau
  dsplit : ∀ s : X.Eˣ, (s : X.E) = s0 →
    ∀ P : HeightOneSpectrum (𝓞 X.E), ordF P s ≠ 0 → (aboveF (L := X.E) X.F (P.under (𝓞 X.F))).card ≠ 1

def conjAlg (hX : X.Ok) : X.E →ₐ[X.F] X.E :=
  { starRingEnd X.E with commutes' := fun a => hX.star_F a }

end Eta

end HeckeEx

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.HeckeInertSq
section
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Sq

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def HiRel (a : 𝓞 E) (X Y : Submodule (𝓞 E) (Sp E n)) : Prop :=
  (∀ x ∈ X, a • x ∈ Y) ∧ ∀ y ∈ Y, a • y ∈ X

theorem HiRel.symm {a : 𝓞 E} {X Y : Submodule (𝓞 E) (Sp E n)} (h : HiRel a X Y) : HiRel a Y X := ⟨h.2, h.1⟩

theorem HiRel.of_ideal {I : Ideal (𝓞 E)} {X Y : Submodule (𝓞 E) (Sp E n)} (h1 : I • X ≤ Y) (h2 : I • Y ≤ X)
    {a : 𝓞 E} (ha : a ∈ I) : HiRel a X Y := ⟨fun x hx => h1 (Submodule.smul_mem_smul ha hx), fun y hy => h2 (Submodule.smul_mem_smul ha hy)⟩

theorem hi_quot {α β : 𝓞 E} (hab : α + β = 1) {X X' Y Y' : Submodule (𝓞 E) (Sp E n)}
    (hXX' : HiRel α X X') (hYY' : HiRel α Y Y') (hXY : HiRel β X Y) (hX'Y' : HiRel β X' Y') :
    Nonempty ((X ⧸ (Y ⊓ X).comap X.subtype) ≃ₗ[𝓞 E] (X' ⧸ (Y' ⊓ X').comap X'.subtype)) := by
  let g : X →ₗ[𝓞 E] X' :=
    LinearMap.codRestrict X' ((α • LinearMap.id : Sp E n →ₗ[𝓞 E] Sp E n).comp X.subtype)
      (fun x => hXX'.1 x.1 x.2)
  let f : X →ₗ[𝓞 E] (X' ⧸ (Y' ⊓ X').comap X'.subtype) := ((Y' ⊓ X').comap X'.subtype).mkQ.comp g
  have key : α * α + β * (1 + α) = 1 := by linear_combination (1 + α) * hab
  have hker : LinearMap.ker f = (Y ⊓ X).comap X.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    change Submodule.Quotient.mk (g x) = 0 ↔ (x : Sp E n) ∈ Y ⊓ X
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_inf]
    change (α • (x : Sp E n) ∈ Y' ∧ α • (x : Sp E n) ∈ X') ↔ ((x : Sp E n) ∈ Y ∧ (x : Sp E n) ∈ X)
    constructor
    · rintro ⟨h1, -⟩
      refine ⟨?_, x.2⟩
      have e : (x : Sp E n) = α • (α • (x : Sp E n)) + β • ((1 + α) • (x : Sp E n)) := by
        calc (x : Sp E n) = (1 : 𝓞 E) • (x : Sp E n) := (one_smul _ _).symm
          _ = (α * α + β * (1 + α)) • (x : Sp E n) := by rw [key]
          _ = _ := by simp only [add_smul, mul_smul]
      rw [e]
      exact Y.add_mem (hYY'.2 _ h1) (hXY.1 _ (X.smul_mem _ x.2))
    · rintro ⟨h1, -⟩
      exact ⟨hYY'.1 _ h1, hXX'.1 _ x.2⟩
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨⟨α • (x' : Sp E n), hXX'.2 _ x'.2⟩, ?_⟩
    change Submodule.Quotient.mk (g ⟨α • (x' : Sp E n), hXX'.2 _ x'.2⟩) = Submodule.Quotient.mk x'
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_inf]
    change (α • (α • (x' : Sp E n)) - (x' : Sp E n) ∈ Y') ∧ (α • (α • (x' : Sp E n)) - (x' : Sp E n) ∈ X')
    have e : α • (α • (x' : Sp E n)) - (x' : Sp E n) = -(β • ((1 + α) • (x' : Sp E n))) := by
      rw [smul_smul, smul_smul, eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← add_smul, key, one_smul, sub_self]
    refine ⟨?_, X'.sub_mem (X'.smul_mem _ (X'.smul_mem _ x'.2)) x'.2⟩
    rw [e]
    exact Y'.neg_mem (hX'Y'.1 _ (X'.smul_mem _ x'.2))
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)⟩

theorem hi_inf_le {α β : 𝓞 E} (hab : α + β = 1) {N M Z : Submodule (𝓞 E) (Sp E n)}
    (hN : ∀ x ∈ N, α • x ∈ Z) (hM : ∀ x ∈ M, β • x ∈ Z) : N ⊓ M ≤ Z := by
  intro x hx
  have hx' : x = α • x + β • x := by rw [← add_smul, hab, one_smul]
  rw [hx']
  exact Z.add_mem (hN x (Submodule.mem_inf.1 hx).1) (hM x (Submodule.mem_inf.1 hx).2)

theorem hi_le {α β : 𝓞 E} (hab : α + β = 1) {X X₁ N M : Submodule (𝓞 E) (Sp E n)}
    (hXN : HiRel α X N) (hXM : HiRel β X M) (h1N : HiRel α X₁ N) (h1M : HiRel β X₁ M) : X ≤ X₁ := by
  intro x hx
  have hNM : N ⊓ M ≤ X₁ := hi_inf_le hab h1N.2 h1M.2
  have hc : α • (β • x) ∈ X₁ := by
    refine hNM (Submodule.mem_inf.2 ⟨hXN.1 _ (X.smul_mem β hx), ?_⟩)
    rw [smul_comm]
    exact hXM.1 _ (X.smul_mem α hx)
  have hd : α • (α • x) ∈ X₁ := h1N.2 _ (hXN.1 x hx)
  have he : β • (β • x) ∈ X₁ := h1M.2 _ (hXM.1 x hx)
  have key : α * α + α * β + (α * β + β * β) = 1 := by
    have h2 : (α + β) * (α + β) = 1 := by rw [hab, one_mul]
    linear_combination h2
  have hx' : x = α • (α • x) + α • (β • x) + (α • (β • x) + β • (β • x)) := by
    calc x = (1 : 𝓞 E) • x := (one_smul _ _).symm
      _ = (α * α + α * β + (α * β + β * β)) • x := by rw [key]
      _ = _ := by simp only [add_smul, mul_smul]
  rw [hx']
  exact X₁.add_mem (X₁.add_mem hd hc) (X₁.add_mem hc he)

theorem hi_eq {α β : 𝓞 E} (hab : α + β = 1) {X X₁ N M : Submodule (𝓞 E) (Sp E n)}
    (hXN : HiRel α X N) (hXM : HiRel β X M) (h1N : HiRel α X₁ N) (h1M : HiRel β X₁ M) : X = X₁ := le_antisymm (hi_le hab hXN hXM h1N h1M) (hi_le hab h1N h1M hXN hXM)

theorem hi_transport {γ δ : 𝓞 E} (hgd : γ + δ = 1) {X X' Y Y' : Submodule (𝓞 E) (Sp E n)}
    (hXX' : HiRel γ X X') (hYY' : HiRel γ Y Y') (hX'Y' : ∀ x ∈ X', δ • x ∈ Y') {K : Ideal (𝓞 E)}
    (h : K • X ≤ Y) : K • X' ≤ Y' := by
  rw [Submodule.smul_le] at h ⊢
  intro k hk x hx
  have h1 : γ • (γ • (k • x)) ∈ Y' := by
    have e : γ • (γ • (k • x)) = γ • (k • (γ • x)) := by rw [smul_comm γ k x]
    rw [e]
    exact hYY'.1 _ (h k hk _ (hXX'.2 x hx))
  have h2 : δ • ((1 + γ) • (k • x)) ∈ Y' := hX'Y' _ (X'.smul_mem _ (X'.smul_mem _ hx))
  have key : γ * γ + δ * (1 + γ) = 1 := by linear_combination (1 + γ) * hgd
  have e2 : k • x = γ • (γ • (k • x)) + δ • ((1 + γ) • (k • x)) := by
    calc k • x = (1 : 𝓞 E) • (k • x) := (one_smul _ _).symm
      _ = (γ * γ + δ * (1 + γ)) • (k • x) := by rw [key]
      _ = _ := by simp only [add_smul, mul_smul]
  rw [e2]
  exact Y'.add_mem h1 h2

def hiCorner (α β : 𝓞 E) (M N : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E n) :=
  α • M ⊔ β • N

theorem hiCorner_le {α β : 𝓞 E} {M N Z : Submodule (𝓞 E) (Sp E n)} (h1 : ∀ m ∈ M, α • m ∈ Z)
    (h2 : ∀ x ∈ N, β • x ∈ Z) : hiCorner α β M N ≤ Z := by
  unfold hiCorner
  refine sup_le ?_ ?_
  · intro z hz
    obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact h1 m hm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact h2 x hx

theorem hiCorner_memL (α β : 𝓞 E) (M N : Submodule (𝓞 E) (Sp E n)) {m : Sp E n} (hm : m ∈ M) :
    α • m ∈ hiCorner α β M N := Submodule.mem_sup_left (Submodule.smul_mem_pointwise_smul m α M hm)

theorem hiCorner_memR (α β : 𝓞 E) (M N : Submodule (𝓞 E) (Sp E n)) {x : Sp E n} (hx : x ∈ N) :
    β • x ∈ hiCorner α β M N := Submodule.mem_sup_right (Submodule.smul_mem_pointwise_smul x β N hx)

theorem hiCorner_inf {α β : 𝓞 E} (hab : α + β = 1) (M N : Submodule (𝓞 E) (Sp E n)) :
    M ⊓ N ≤ hiCorner α β M N := by
  intro x hx
  have hx' : x = α • x + β • x := by rw [← add_smul, hab, one_smul]
  rw [hx']
  exact Submodule.add_mem_sup (Submodule.smul_mem_pointwise_smul x α M (Submodule.mem_inf.1 hx).1)
    (Submodule.smul_mem_pointwise_smul x β N (Submodule.mem_inf.1 hx).2)

theorem hiCorner_rel {α β : 𝓞 E} {N e M : Submodule (𝓞 E) (Sp E n)} (hNe : HiRel α N e) (heM : HiRel β e M) :
    HiRel β N (hiCorner α β M N) ∧ HiRel α (hiCorner α β M N) M := by
  have hmem : ∀ y ∈ hiCorner α β M N, ∃ m ∈ M, ∃ x ∈ N, α • m + β • x = y := by
    intro y hy
    unfold hiCorner at hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy1
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy2
    exact ⟨m, hm, x, hx, rfl⟩
  refine ⟨⟨fun x hx => hiCorner_memR α β M N hx, fun y hy => ?_⟩,
    ⟨fun y hy => ?_, fun m hm => hiCorner_memL α β M N hm⟩⟩
  · obtain ⟨m, hm, x, hx, rfl⟩ := hmem y hy
    rw [smul_add, smul_comm β α m]
    exact N.add_mem (hNe.2 _ (heM.2 _ hm)) (N.smul_mem _ (N.smul_mem _ hx))
  · obtain ⟨m, hm, x, hx, rfl⟩ := hmem y hy
    rw [smul_add, smul_comm α β x]
    exact M.add_mem (M.smul_mem _ (M.smul_mem _ hm)) (heM.1 _ (hNe.1 _ hx))

theorem hi_exists_conj {I J : Ideal (𝓞 E)} (hJ : ∀ a ∈ J, cO E a ∈ J) (hIJ : I ⊔ J = ⊤) :
    ∃ α ∈ I, ∃ β ∈ J, α + β = 1 ∧ cO E α = α ∧ cO E β = β := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ I ⊔ J by rw [hIJ]; exact Submodule.mem_top)
  have hc1 : cO E a + cO E b = 1 := by rw [← map_add, hab, map_one]
  refine ⟨a * cO E a, Ideal.mul_mem_right _ _ ha, 1 - a * cO E a, ?_, by ring, ?_, ?_⟩
  · have e : 1 - a * cO E a = a * cO E b + b * cO E a + b * cO E b := by
      have h1 : (a + b) * (cO E a + cO E b) = 1 := by rw [hab, hc1, one_mul]
      linear_combination -h1
    rw [e]
    exact J.add_mem (J.add_mem (Ideal.mul_mem_left _ _ (hJ b hb)) (Ideal.mul_mem_right _ _ hb))
      (Ideal.mul_mem_right _ _ hb)
  · rw [map_mul, cO_cO, mul_comm]
  · rw [map_sub, map_one, map_mul, cO_cO, mul_comm]

theorem hi_hStd_conj {a : 𝓞 E} (ha : cO E a = a) (m x : Sp E n) :
    hStd E n (a • m) x = hStd E n m (a • x) := by
  rw [wmp_hStd_osmul_left, wmp_hStd_osmul_right, ha]

theorem hiCorner_mem_dual {α β : 𝓞 E} (hα : cO E α = α) (hβ : cO E β = β) {M N : Submodule (𝓞 E) (Sp E n)}
    (hM : IsUnimodular (hStd E n) M) (hN : IsUnimodular (hStd E n) N) (x : Sp E n) :
    x ∈ dual (hStd E n) (hiCorner α β M N) ↔ α • x ∈ M ∧ β • x ∈ N := by
  constructor
  · intro hx
    rw [mem_dual] at hx
    refine ⟨?_, ?_⟩
    · rw [← show dual (hStd E n) M = M from hM, mem_dual]
      intro m hm
      rw [← hi_hStd_conj hα]
      exact hx _ (hiCorner_memL α β M N hm)
    · rw [← show dual (hStd E n) N = N from hN, mem_dual]
      intro y hy
      rw [← hi_hStd_conj hβ]
      exact hx _ (hiCorner_memR α β M N hy)
  · rintro ⟨h1, h2⟩
    have hM' : α • x ∈ dual (hStd E n) M := by rw [show dual (hStd E n) M = M from hM]; exact h1
    have hN' : β • x ∈ dual (hStd E n) N := by rw [show dual (hStd E n) N = N from hN]; exact h2
    rw [mem_dual]
    intro y hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy1
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy2
    rw [map_add, LinearMap.add_apply, hi_hStd_conj hα, hi_hStd_conj hβ]
    exact Submodule.add_mem _ ((mem_dual M _).1 hM' m hm) ((mem_dual N _).1 hN' z hz)

theorem hiCorner_unimodular {α β : 𝓞 E} (hab : α + β = 1) (hα : cO E α = α) (hβ : cO E β = β)
    {N e M : Submodule (𝓞 E) (Sp E n)} (hN : IsUnimodular (hStd E n) N) (hM : IsUnimodular (hStd E n) M)
    (hNe : HiRel α N e) (heM : HiRel β e M) : IsUnimodular (hStd E n) (hiCorner α β M N) := by
  obtain ⟨hr1, hr2⟩ := hiCorner_rel hNe heM
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := (hiCorner_mem_dual hα hβ hM hN x).1 hx
    have hinf := hiCorner_inf hab M N
    refine mem_of_smul_mem_of_add_eq_one hab ?_ ?_
    · refine mem_of_smul_mem_of_add_eq_one hab (hiCorner_memL α β M N h1) (hinf ⟨M.smul_mem β h1, ?_⟩)
      rw [smul_comm β α x]
      exact N.smul_mem α h2
    · refine mem_of_smul_mem_of_add_eq_one hab (hinf ⟨?_, N.smul_mem α h2⟩) (hiCorner_memR α β M N h2)
      rw [smul_comm α β x]
      exact M.smul_mem β h1
  · intro x hx
    exact (hiCorner_mem_dual hα hβ hM hN x).2 ⟨hr2.1 x hx, hr1.2 x hx⟩

theorem hiCorner_lattice {α β : 𝓞 E} (hab : α + β = 1) {N e M : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) (hM : Submodule.IsLattice E M) {i j : 𝓞 E} (hi : i ≠ 0) (hj : j ≠ 0)
    (hNi : ∀ x ∈ N, i • x ∈ e) (hej : ∀ y ∈ e, j • y ∈ M) : Submodule.IsLattice E (hiCorner α β M N) := by
  have hD : Submodule.IsLattice E (M ⊔ N) := ⟨hM.fg.sup hN.fg, by
    rw [eq_top_iff, ← hM.span_eq_top]
    exact Submodule.span_mono (SetLike.coe_subset_coe.2 (le_sup_left : M ≤ M ⊔ N))⟩
  refine lattice_of_smul hN hD (hiCorner_le (fun m hm => Submodule.mem_sup_left (M.smul_mem α hm))
    (fun x hx => Submodule.mem_sup_right (N.smul_mem β hx))) (mul_ne_zero hj hi) fun x hx => ?_
  refine hiCorner_inf hab M N ⟨?_, N.smul_mem _ hx⟩
  rw [mul_smul]
  exact hej _ (hNi x hx)

end Sq

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
section
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem pathCount_symmetric_holds : DecorationPathSymmetry E n ST SG := by
  intro P Q hP hQ hSTP hSGP hSTQ hSGQ i j d f
  by_cases hQP : Q = P
  · subst hQP
    exact pathCount_symm_same_prime Q hP hSTP hSGP i j d f
  by_cases hQP' : Q = conjPrime₂ P
  · subst hQP'
    exact pathCount_conj_symm (P := P) hP hSTP hSGP (fun i j d f => pathCount_symm_same_prime P hP hSTP hSGP i j d f) i j d f
  exact pathCount_symm_distinct P Q hP hQ hQP hQP' hSTP hSGP hSTQ hSGQ i j d f

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem heckeOperators_commute (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : HeckeComm c S0 :=
  heckeComm_of_paths c S0 pathCount_symmetric_holds

end Formalism.L2.Col
end
end

