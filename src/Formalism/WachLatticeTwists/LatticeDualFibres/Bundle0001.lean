import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

-- bundled from Formalism.WachLatticeTwists.LatticeDualFibres.MapHOneCommSquare
section
universe u

open ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

def MapHOneCommSquare : Prop :=
  ∀ (R G M M₁ M₂ M₃ : Type u) [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M]
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [IsTopologicalAddGroup M₁]
    [ContinuousConstSMul R M₁]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [IsTopologicalAddGroup M₂]
    [ContinuousConstSMul R M₂]
    [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₃] [IsTopologicalAddGroup M₃]
    [ContinuousConstSMul R M₃]
    (ρ : Representation R G M) (ρ₁ : Representation R G M₁) (ρ₂ : Representation R G M₂)
    (ρ₃ : Representation R G M₃)
    (u : M →ₗ[R] M₁) (v : M₁ →ₗ[R] M₃) (u' : M →ₗ[R] M₂) (v' : M₂ →ₗ[R] M₃)
    (hu : Continuous u) (hv : Continuous v) (hu' : Continuous u') (hv' : Continuous v')
    (eu : ∀ g m, u (ρ g m) = ρ₁ g (u m)) (ev : ∀ g m, v (ρ₁ g m) = ρ₃ g (v m))
    (eu' : ∀ g m, u' (ρ g m) = ρ₂ g (u' m)) (ev' : ∀ g m, v' (ρ₂ g m) = ρ₃ g (v' m)),
    (∀ m, v (u m) = v' (u' m)) →
    ∀ x : H1 ρ, mapH1 ρ₁ ρ₃ v hv ev (mapH1 ρ ρ₁ u hu eu x) =
      mapH1 ρ₂ ρ₃ v' hv' ev' (mapH1 ρ ρ₂ u' hu' eu' x)

def StatCupSquare : Prop :=
  ∀ (R G M₁ M₁' M M' P M₂ M₂' P₂ : Type u) [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁] [IsTopologicalAddGroup M₁]
    [ContinuousConstSMul R M₁]
    [AddCommGroup M₁'] [Module R M₁'] [TopologicalSpace M₁'] [IsTopologicalAddGroup M₁']
    [ContinuousConstSMul R M₁']
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    [ContinuousConstSMul R M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [ContinuousConstSMul R P]
    [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [IsTopologicalAddGroup M₂]
    [ContinuousConstSMul R M₂]
    [AddCommGroup M₂'] [Module R M₂'] [TopologicalSpace M₂'] [IsTopologicalAddGroup M₂']
    [ContinuousConstSMul R M₂']
    [AddCommGroup P₂] [Module R P₂] [TopologicalSpace P₂] [IsTopologicalAddGroup P₂]
    [ContinuousConstSMul R P₂]
    (ρ₁ : Representation R G M₁) (ρ₁' : Representation R G M₁')
    (ρ : Representation R G M) (ρ' : Representation R G M') (ρP : Representation R G P)
    (ρ₂ : Representation R G M₂) (ρ₂' : Representation R G M₂') (ρP₂ : Representation R G P₂)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (ρ g x) (ρ' g y) = ρP g (b x y)) (hρ' : ContAction ρ')
    (b₂ : M₂ →ₗ[R] M₂' →ₗ[R] P₂) (hb₂ : Continuous fun p : M₂ × M₂' => b₂ p.1 p.2)
    (hbe₂ : ∀ g x y, b₂ (ρ₂ g x) (ρ₂' g y) = ρP₂ g (b₂ x y)) (hρ₂' : ContAction ρ₂')
    (α : M₁ →ₗ[R] M) (hα : Continuous α) (eα : ∀ g m, α (ρ₁ g m) = ρ g (α m))
    (β : M₁' →ₗ[R] M') (hβ : Continuous β) (eβ : ∀ g m, β (ρ₁' g m) = ρ' g (β m))
    (α₂ : M₁ →ₗ[R] M₂) (hα₂ : Continuous α₂) (eα₂ : ∀ g m, α₂ (ρ₁ g m) = ρ₂ g (α₂ m))
    (β₂ : M₁' →ₗ[R] M₂') (hβ₂ : Continuous β₂) (eβ₂ : ∀ g m, β₂ (ρ₁' g m) = ρ₂' g (β₂ m))
    (γ : P₂ →ₗ[R] P) (hγ : Continuous γ) (eγ : ∀ g m, γ (ρP₂ g m) = ρP g (γ m)),
    (∀ a a', b (α a) (β a') = γ (b₂ (α₂ a) (β₂ a'))) →
    ∀ (x : H1 ρ₁) (y : H1 ρ₁'),
      cupProductH1H1 ρ ρ' ρP b hb hbe hρ' (mapH1 ρ₁ ρ α hα eα x) (mapH1 ρ₁' ρ' β hβ eβ y) =
        mapH2 ρP₂ ρP γ hγ eγ
          (cupProductH1H1 ρ₂ ρ₂' ρP₂ b₂ hb₂ hbe₂ hρ₂' (mapH1 ρ₁ ρ₂ α₂ hα₂ eα₂ x)
            (mapH1 ρ₁' ρ₂' β₂ hβ₂ eβ₂ y))

def StatConnTors : Prop :=
  ∀ (O G T V A : Type u) [CommRing O] [IsDomain O] [Group G] [TopologicalSpace G]
    [AddCommGroup T] [Module O T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul O T]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul O V]
    [AddCommGroup A] [Module O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul O A]
    (ρT : Representation O G T) (ρV : Representation O G V) (ρA : Representation O G A)
    (j : T →ₗ[O] V) (q : V →ₗ[O] A),
    Topology.IsEmbedding j → (∀ g m, j (ρT g m) = ρV g (j m)) → (∀ g m, q (ρV g m) = ρA g (q m)) →
    Function.Surjective q → LinearMap.ker q = LinearMap.range j → ContAction ρV →
    (∀ c : O, c ≠ 0 → Function.Bijective fun v : V => c • v) →
    (∀ a : A, ∃ c : O, c ≠ 0 ∧ c • a = 0) →
    ∃ δ : H0 ρA →ₗ[O] H1 ρT, LinearMap.range δ = Submodule.torsion O (H1 ρT)

end Formalism.RepresentationBoundsCohomology.LOC
end
end

-- bundled from Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
section
universe u

open Formalism.NG (KO)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

section Lat

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def IsLatticeIn {V : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (L : Submodule O V) : Prop :=
  L.FG ∧ Submodule.span (FractionRing O) (L : Set V) = ⊤

def StableUnder {G V : Type u} [Group G] [AddCommGroup V] [Module O V] (ρ : Representation O G V)
    (L : Submodule O V) : Prop := ∀ g, ∀ x ∈ L, ρ g x ∈ L

def EquivToQuot {G VY VT : Type u} [Group G] [AddCommGroup VY] [Module O VY] [AddCommGroup VT]
    [Module O VT] (ρY : Representation O G VY) (ρT : Representation O G VT) (Y : Submodule O VY)
    (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T) : Prop :=
  ∀ (g : G) (y : Y) (hy : ρY g y ∈ Y) (x : VT), φ y = Submodule.Quotient.mk x →
    φ ⟨ρY g y, hy⟩ = Submodule.Quotient.mk (ρT g x)

def fibre {VY VT : Type u} [AddCommGroup VY] [Module O VY] [AddCommGroup VT] [Module O VT]
    (Y : Submodule O VY) (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T) : Submodule O (VY × VT) where
  carrier := {p | ∃ h : p.1 ∈ Y, φ ⟨p.1, h⟩ = Submodule.Quotient.mk p.2}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Y.add_mem ha hb, ?_⟩
    have : (⟨(a + b).1, Y.add_mem ha hb⟩ : Y) = ⟨a.1, ha⟩ + ⟨b.1, hb⟩ := rfl
    rw [this, map_add, ha', hb']; rfl
  zero_mem' := ⟨Y.zero_mem, by
    have : (⟨(0 : VY × VT).1, Y.zero_mem⟩ : Y) = 0 := rfl
    rw [this, map_zero]; rfl⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Y.smul_mem c ha, ?_⟩
    have : (⟨(c • a).1, Y.smul_mem c ha⟩ : Y) = c • ⟨a.1, ha⟩ := rfl
    rw [this, map_smul, ha']; rfl

def dualLat {V V' : Type u} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) : Submodule O V' where
  carrier := {f | ∀ x ∈ T, b x f ∈ (1 : Submodule O (FractionRing O))}
  add_mem' := by
    intro f g hf hg x hx
    rw [map_add]; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  zero_mem' := by
    intro x _
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro c f hf x hx
    rw [map_smul]; exact Submodule.smul_mem _ c (hf x hx)

def fibreDual {VY VT VY' VT' : Type u} [AddCommGroup VY] [Module O VY] [AddCommGroup VT]
    [Module O VT] [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT'] [Module O VT']
    (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O) (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O)
    (Y : Submodule O VY) (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T) :
    Submodule O (VT' × VY') where
  carrier := {p | p.1 ∈ dualLat bT T ∧ ∀ (y : Y) (x : VT), φ y = Submodule.Quotient.mk x →
    bY y p.2 - bT x p.1 ∈ (1 : Submodule O (FractionRing O))}
  add_mem' := by
    rintro p r ⟨hp, hp'⟩ ⟨hr, hr'⟩
    refine ⟨Submodule.add_mem _ hp hr, fun y x h => ?_⟩
    have : bY y (p + r).2 - bT x (p + r).1 = (bY y p.2 - bT x p.1) + (bY y r.2 - bT x r.1) := by
      simp only [Prod.snd_add, Prod.fst_add, map_add]; ring
    rw [this]; exact Submodule.add_mem _ (hp' y x h) (hr' y x h)
  zero_mem' := ⟨Submodule.zero_mem _, fun y x _ => by
    simp only [Prod.snd_zero, Prod.fst_zero, map_zero, sub_zero]; exact Submodule.zero_mem _⟩
  smul_mem' := by
    rintro c p ⟨hp, hp'⟩
    refine ⟨Submodule.smul_mem _ c hp, fun y x h => ?_⟩
    have : bY y (c • p).2 - bT x (c • p).1 = c • (bY y p.2 - bT x p.1) := by
      simp only [Prod.smul_snd, Prod.smul_fst, map_smul, smul_sub]
    rw [this]; exact Submodule.smul_mem _ c (hp' y x h)

def PerfectRight {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) : Prop :=
  ∀ ψ : V →ₗ[FractionRing O] FractionRing O, ∃! f : V', ∀ x, b x f = ψ x

def EquivPair {G V V' : Type u} [Group G] [AddCommGroup V] [Module O V] [AddCommGroup V']
    [Module O V'] (ε : G →* Oˣ) (ρ : Representation O G V) (ρ' : Representation O G V')
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) : Prop :=
  ∀ g x f, b (ρ g x) (ρ' g f) = (ε g : O) • b x f

end Lat

def StatImageKilled : Prop :=
  ∀ (O VY VT : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup VY] [Module O VY] [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT]
    [IsScalarTower O (FractionRing O) VT] (Y : Submodule O VY) (T : Submodule O VT)
    (φ : Y →ₗ[O] VT ⧸ T) (ϖ : O), Irreducible ϖ → Y.FG → IsLatticeIn T →
    ∃ a : ℕ, ∀ y, (ϖ ^ a) • φ y = 0

def StatFibreLattice : Prop :=
  ∀ (O G VY VT : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group G]
    [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY]
    [IsScalarTower O (FractionRing O) VY]
    [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT]
    [IsScalarTower O (FractionRing O) VT]
    (ρY : Representation O G VY) (ρT : Representation O G VT) (Y : Submodule O VY)
    (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T),
    IsLatticeIn Y → IsLatticeIn T → StableUnder ρY Y → StableUnder ρT T → EquivToQuot ρY ρT Y T φ →
    IsLatticeIn (fibre Y T φ) ∧
    (∀ g, ∀ p ∈ fibre Y T φ, (ρY g p.1, ρT g p.2) ∈ fibre Y T φ) ∧
    (∀ x ∈ T, ((0 : VY), x) ∈ fibre Y T φ) ∧
    (∀ y ∈ Y, ∃ x, (y, x) ∈ fibre Y T φ)

def StatDualLattice : Prop :=
  ∀ (O G V V' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group G]
    [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V']
    [IsScalarTower O (FractionRing O) V']
    (ε : G →* Oˣ) (ρ : Representation O G V) (ρ' : Representation O G V')
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V),
    IsLatticeIn T → StableUnder ρ T → PerfectRight b → EquivPair ε ρ ρ' b →
    IsLatticeIn (dualLat b T) ∧ Module.finrank O (dualLat b T) = Module.finrank O T ∧
    StableUnder ρ' (dualLat b T) ∧ dualLat b.flip (dualLat b T) = T

def StatDualFibreLattice : Prop :=
  ∀ (O G VY VT VY' VT' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group G]
    [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY]
    [IsScalarTower O (FractionRing O) VY]
    [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT]
    [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VY'] [Module O VY'] [Module (FractionRing O) VY']
    [IsScalarTower O (FractionRing O) VY']
    [AddCommGroup VT'] [Module O VT'] [Module (FractionRing O) VT']
    [IsScalarTower O (FractionRing O) VT']
    (ε : G →* Oˣ) (ρY : Representation O G VY) (ρT : Representation O G VT)
    (ρY' : Representation O G VY') (ρT' : Representation O G VT')
    (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O) (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O)
    (Y : Submodule O VY) (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T),
    IsLatticeIn Y → IsLatticeIn T → StableUnder ρY Y → StableUnder ρT T → EquivToQuot ρY ρT Y T φ →
    PerfectRight bY → PerfectRight bT → EquivPair ε ρY ρY' bY → EquivPair ε ρT ρT' bT →
    IsLatticeIn (fibreDual bY bT Y T φ) ∧
    (∀ g, ∀ p ∈ fibreDual bY bT Y T φ, (ρT' g p.1, ρY' g p.2) ∈ fibreDual bY bT Y T φ) ∧
    (∀ f ∈ dualLat bT T, ∃ g, (f, g) ∈ fibreDual bY bT Y T φ)

def StatQuotEmbeds : Prop :=
  ∀ (O V : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (T : Submodule O V), IsLatticeIn T →
    Module.finrank O T = Module.finrank (FractionRing O) V ∧
    ∃ e : (V ⧸ T) →ₗ[O] (Fin (Module.finrank O T) → KO O), Function.Injective e

end Formalism.RepresentationBoundsCohomology.LOC
end
end

