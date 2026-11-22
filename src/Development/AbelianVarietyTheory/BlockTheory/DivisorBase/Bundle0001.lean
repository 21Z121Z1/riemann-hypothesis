import Mathlib

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarMultiplier
section
open scoped TensorProduct NumberField
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarMultiplier

abbrev Af : Type := FiniteAdeleRing ℤ ℚ

def zHat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum ℤ, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers ℚ)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers ℚ)
  neg_mem' ha v := neg_mem (ha v)

def zHatUnits : Subgroup Afˣ := zHat.toSubmonoid.units

def hat {V : Type} [AddCommGroup V] [Module ℚ V] (N : Set V) : AddSubgroup (Af ⊗[ℚ] V) :=
  AddSubgroup.closure {t | ∃ z ∈ zHat, ∃ x ∈ N, t = z ⊗ₜ[ℚ] x}

def IsQuadField (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) : Prop :=
  d.Prime ∧ 3 < d ∧ d % 4 = 3 ∧ Module.finrank ℚ K = 2 ∧ δ ^ 2 = -(d : K)

abbrev Idele (K : Type) [Field K] [NumberField K] : Type := (Af ⊗[ℚ] K)ˣ

def ideleNorm (K : Type) [Field K] [NumberField K] : Idele K →* Afˣ :=
  Units.map (Algebra.norm Af : Af ⊗[ℚ] K →* Af)

def IsUnitIdele {K : Type} [Field K] [NumberField K] (s : Idele K) : Prop :=
  (s : Af ⊗[ℚ] K) ∈ hat (Set.range (algebraMap (𝓞 K) K)) ∧
    ((s⁻¹ : Idele K) : Af ⊗[ℚ] K) ∈ hat (Set.range (algebraMap (𝓞 K) K))

def NormUnitCond {K : Type} [Field K] [NumberField K] (s : Idele K) (q : ℚ) : Prop :=
  ∃ u ∈ zHatUnits, (u : Af) = (((ideleNorm K s)⁻¹ : Afˣ) : Af) * algebraMap ℚ Af q

def IdeleNormStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K), IsQuadField K d δ →
    ∀ s : Idele K,
      (∃! q : ℚ, 0 < q ∧ NormUnitCond s q) ∧
      ∀ q : ℚ, 0 < q → NormUnitCond s q →
        (∃ x : Kˣ, Algebra.norm ℚ (x : K) = q⁻¹) ∧ (IsUnitIdele s → q = 1)

section Herm

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W]

def IsHermitian (h : LinearMap.BilinMap ℚ W E) : Prop :=
  (∀ (a : E) (x y : W), h (a • x) y = a * h x y) ∧
    ∀ x y : W, h y x = NumberField.IsCMField.complexConj E (h x y)

omit [NumberField.IsCMField E] in

def HasSignatureAt (h : LinearMap.BilinMap ℚ W E) (τ : E →+* ℂ) (p q : ℕ) : Prop :=
  ∃ b : Module.Basis (Fin p ⊕ Fin q) E W,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) ∧
    (∀ i, 0 < (τ (h (b (Sum.inl i)) (b (Sum.inl i)))).re) ∧
    (∀ j, (τ (h (b (Sum.inr j)) (b (Sum.inr j)))).re < 0)

omit [NumberField.IsCMField E] [Module E W] in

def traceForm (h : LinearMap.BilinMap ℚ W E) (ξ : E) : LinearMap.BilinForm ℚ W :=
  LinearMap.compr₂ h (Algebra.trace ℚ E ∘ₗ LinearMap.mulLeft ℚ ξ)

end Herm

section Groups

variable {E : Type} [Field E] [NumberField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

def adelicScalar (W : Type) [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]
    (a : E) : Af ⊗[ℚ] W →ₗ[Af] Af ⊗[ℚ] W :=
  LinearMap.baseChange Af ((LinearMap.lsmul E W a).restrictScalars ℚ)

def adelicGL (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module ℚ W]
    [Module E W] [IsScalarTower ℚ E W] : Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) where
  carrier := {g | ∀ (a : E) (x : Af ⊗[ℚ] W), g (adelicScalar W a x) = adelicScalar W a (g x)}
  mul_mem' {g g'} hg hg' a x := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg', hg]
  one_mem' _ _ := rfl
  inv_mem' {g} hg a x := by
    apply g.injective
    rw [hg]
    simp [LinearEquiv.coe_inv]

omit [Module E W] [IsScalarTower ℚ E W] in

def HasMultiplier (ψ : LinearMap.BilinForm ℚ W) (g : Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) (ν : Afˣ) :
    Prop :=
  ∀ x y, ψ.baseChange Af (g x) (g y) = (ν : Af) * ψ.baseChange Af x y

def similitudes (ψ : LinearMap.BilinForm ℚ W) : Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) where
  carrier := {g | ∃ ν, HasMultiplier ψ g ν}
  mul_mem' := by
    rintro g g' ⟨ν, hν⟩ ⟨ν', hν'⟩
    refine ⟨ν * ν', fun x y => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hν, hν', Units.val_mul, mul_assoc]
  one_mem' := ⟨1, fun x y => by simp⟩
  inv_mem' := by
    rintro g ⟨ν, hν⟩
    refine ⟨ν⁻¹, fun x y => ?_⟩
    have := hν (g.symm x) (g.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    rw [this, Units.inv_mul_cancel_left]
    rfl

def isometries (h : LinearMap.BilinMap ℚ W E) : Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) where
  carrier := {g | ∀ x y, h.baseChange Af (g x) (g y) = h.baseChange Af x y}
  mul_mem' {g g'} hg hg' x y := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, hg']
  one_mem' _ _ := rfl
  inv_mem' {g} hg x y := by
    have := hg (g.symm x) (g.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm

def stab (L : AddSubgroup (Af ⊗[ℚ] W)) : Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) where
  carrier := {g | ∀ x, g x ∈ L ↔ x ∈ L}
  mul_mem' {g g'} hg hg' x := by
    rw [LinearEquiv.mul_apply, hg, hg']
  one_mem' _ := Iff.rfl
  inv_mem' {g} hg x := by
    have := hg (g.symm x)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm

def congr (L L' : AddSubgroup (Af ⊗[ℚ] W)) : Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) where
  carrier := {g | g ∈ stab L ∧ ∀ x ∈ L, g x - x ∈ L'}
  mul_mem' := by
    rintro g g' ⟨hg, h1⟩ ⟨hg', h2⟩
    refine ⟨mul_mem hg hg', fun x hx => ?_⟩
    have := add_mem (h1 (g' x) ((hg' x).2 hx)) (h2 x hx)
    simpa [LinearEquiv.mul_apply] using this
  one_mem' := ⟨one_mem _, fun x _ => by simpa using zero_mem L'⟩
  inv_mem' := by
    rintro g ⟨hg, h1⟩
    refine ⟨inv_mem hg, fun x hx => ?_⟩
    have := neg_mem (h1 (g.symm x) ((inv_mem hg x).2 hx))
    simpa [LinearEquiv.coe_inv] using this

def simGroup (h : LinearMap.BilinMap ℚ W E) (ξ : E) :
    Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) :=
  adelicGL E W ⊓ similitudes (traceForm h ξ)

def unitaryGroup (h : LinearMap.BilinMap ℚ W E) : Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) :=
  adelicGL E W ⊓ isometries h

variable [Module (𝓞 E) W]

def simLevel (h : LinearMap.BilinMap ℚ W E) (ξ : E) (Λ : Submodule (𝓞 E) W)
    (I : Ideal (𝓞 E)) : Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) :=
  simGroup h ξ ⊓ congr (hat (Λ : Set W)) (hat ((I • Λ : Submodule (𝓞 E) W) : Set W))

def simPrincipal (h : LinearMap.BilinMap ℚ W E) (ξ : E) (Λ : Submodule (𝓞 E) W) (N : ℕ) :
    Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) :=
  simLevel h ξ Λ (Ideal.span {(N : 𝓞 E)})

def unitaryPrincipal (h : LinearMap.BilinMap ℚ W E) (ξ : E) (Λ : Submodule (𝓞 E) W) (N : ℕ) :
    Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) :=
  simPrincipal h ξ Λ N ⊓ unitaryGroup h

def unitaryStab (h : LinearMap.BilinMap ℚ W E) (Λ : Submodule (𝓞 E) W) :
    Subgroup (Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W) :=
  unitaryGroup h ⊓ stab (hat (Λ : Set W))

omit [IsScalarTower ℚ E W] in

def IsSelfDualLattice (ψ : LinearMap.BilinForm ℚ W) (Λ : Submodule (𝓞 E) W) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set W) = ⊤ ∧
    ∀ x : W, x ∈ Λ ↔ ∀ y ∈ Λ, ∃ m : ℤ, ψ x y = m

omit [Module E W] [IsScalarTower ℚ E W] in

def Induces (Λ : Submodule (𝓞 E) W) (I : Ideal (𝓞 E)) (g : Af ⊗[ℚ] W ≃ₗ[Af] Af ⊗[ℚ] W)
    (φ : (Λ ⧸ (I • ⊤ : Submodule (𝓞 E) Λ)) ≃ₗ[𝓞 E] (Λ ⧸ (I • ⊤ : Submodule (𝓞 E) Λ))) : Prop :=
  ∀ x y : Λ, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
    g ((1 : Af) ⊗ₜ[ℚ] (x : W)) - (1 : Af) ⊗ₜ[ℚ] (y : W) ∈
      hat ((I • Λ : Submodule (𝓞 E) W) : Set W)

end Groups

def LevelGroupStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K)
    (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] [Algebra K E]
    (W : Type) [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (h : LinearMap.BilinMap ℚ W E) (p q : ℕ) (ξ : E) (Λ : Submodule (𝓞 E) W)
    (M : ℕ) (𝔐 𝔐' : Ideal (𝓞 K)),
    IsQuadField K d δ →
    IsGalois K E →
    (∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (NumberField.maximalRealSubfield E)) P) →
    IsHermitian h →
    q < p →
    (∀ τ : E →+* ℂ, HasSignatureAt h τ p q) →
    NumberField.IsCMField.complexConj E ξ = -ξ →
    (∀ τ : E →+* ℂ, τ (algebraMap K E δ) = Complex.I * (Real.sqrt d : ℂ) → 0 < (τ ξ).im) →
    IsSelfDualLattice (traceForm h ξ) Λ →
    3 ≤ M → Odd M →
    (∀ x : 𝓞 K, x ∈ 𝔐' ↔ ∃ y ∈ 𝔐, algebraMap (𝓞 K) E x =
      NumberField.IsCMField.complexConj E (algebraMap (𝓞 K) E y)) →
    𝔐 * 𝔐' = Ideal.span {(M : 𝓞 K)} → 𝔐 ⊔ 𝔐' = ⊤ →
    (∀ ν : Afˣ, (∃ g ∈ simLevel h ξ Λ (𝔐'.map (algebraMap (𝓞 K) (𝓞 E))),
        HasMultiplier (traceForm h ξ) g ν) ↔ ν ∈ zHatUnits) ∧
      simLevel h ξ Λ (𝔐'.map (algebraMap (𝓞 K) (𝓞 E))) ⊓ unitaryGroup h =
        unitaryPrincipal h ξ Λ M ∧
      simPrincipal h ξ Λ M ≤ simLevel h ξ Λ (𝔐'.map (algebraMap (𝓞 K) (𝓞 E))) ∧
      ∀ φ, ∃ g ∈ unitaryStab h Λ, Induces Λ (𝔐'.map (algebraMap (𝓞 K) (𝓞 E))) g φ

def Statement : Prop := IdeleNormStatement ∧ LevelGroupStatement

example (K : Type) [Field K] [NumberField K] : NormUnitCond (1 : Idele K) 1 :=
  ⟨1, one_mem _, by simp⟩

theorem simLevel_mono {E : Type} [Field E] [NumberField E]
    {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]
    [Module (𝓞 E) W] (h : LinearMap.BilinMap ℚ W E) (ξ : E) (Λ : Submodule (𝓞 E) W)
    {I J : Ideal (𝓞 E)} (hIJ : I ≤ J) : simLevel h ξ Λ I ≤ simLevel h ξ Λ J := by
  rintro g ⟨hg, h1, h2⟩
  refine ⟨hg, h1, fun x hx => AddSubgroup.closure_mono ?_ (h2 x hx)⟩
  rintro t ⟨z, hz, y, hy, rfl⟩
  exact ⟨z, hz, y, Submodule.smul_mono_left hIJ hy, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarMultiplier
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.IdeleNormTraceForm
section
open NumberField IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm

abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

def Zhat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).mul_mem _ _ (ha v) (hb v)
  one_mem' := fun v => (v.adicCompletionIntegers ℚ).one_mem
  add_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).add_mem _ _ (ha v) (hb v)
  zero_mem' := fun v => (v.adicCompletionIntegers ℚ).zero_mem
  neg_mem' := fun {a} ha v => (v.adicCompletionIntegers ℚ).neg_mem _ (ha v)

def ZhatUnits : Subgroup Afˣ := Zhat.toSubmonoid.units

abbrev Adelic (V : Type) [AddCommGroup V] [Module ℚ V] : Type := Af ⊗[ℚ] V

def hat {V : Type} [AddCommGroup V] [Module ℚ V] (L : Set V) : Submodule Zhat (Adelic V) :=
  Submodule.span Zhat ((fun x : V => (1 : Af) ⊗ₜ[ℚ] x) '' L)

def IsPrimeImagQuad (d : ℕ) (K : Type) [Field K] [NumberField K] (δ : K) : Prop :=
  d.Prime ∧ 3 < d ∧ d % 4 = 3 ∧ δ ^ 2 = -(d : K) ∧ Module.finrank ℚ K = 2

def ideleNorm (K : Type) [Field K] [NumberField K] : (Adelic K)ˣ →* Afˣ :=
  Units.map (Algebra.norm Af : Adelic K →* Af)

def ratIdele : ℚˣ →* Afˣ := Units.map (algebraMap ℚ Af : ℚ →+* Af).toMonoidHom

def IsUnitIdele {K : Type} [Field K] [NumberField K] (s : (Adelic K)ˣ) : Prop :=
  (s : Adelic K) ∈ hat {x : K | IsIntegral ℤ x} ∧
    ((s⁻¹ : (Adelic K)ˣ) : Adelic K) ∈ hat {x : K | IsIntegral ℤ x}

def IsNormScale {K : Type} [Field K] [NumberField K] (s : (Adelic K)ˣ) (q : ℚˣ) : Prop :=
  0 < (q : ℚ) ∧ (ideleNorm K s)⁻¹ * ratIdele q ∈ ZhatUnits

def IdeleNormScaleAt (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ s : (Adelic K)ˣ,
    (∃! q : ℚˣ, IsNormScale s q) ∧
    (∀ q : ℚˣ, IsNormScale s q →
      (∃ x : Kˣ, Algebra.norm ℚ (x : K) = ((q⁻¹ : ℚˣ) : ℚ)) ∧ (IsUnitIdele s → q = 1))

def IdeleNormScale : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (δ : K),
    IsPrimeImagQuad d K δ → IdeleNormScaleAt K

section Groups

variable (E : Type) [Field E] [NumberField E]
variable {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

def IsHermitian [IsCMField E] (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : Prop :=
  (∀ (a : E) (x y : W), h (a • x) y = a * h x y) ∧
    ∀ x y : W, h y x = IsCMField.complexConj E (h x y)

def HasSignature (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (p q' : ℕ) : Prop :=
  ∀ τ : E →+* ℂ, ∃ b : Module.Basis (Fin p ⊕ Fin q') E W,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) ∧
    (∀ i, 0 < (τ (h (b (Sum.inl i)) (b (Sum.inl i)))).re) ∧
    (∀ i, (τ (h (b (Sum.inr i)) (b (Sum.inr i)))).re < 0)

def traceForm (ξ₀ : E) (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : LinearMap.BilinForm ℚ W :=
  h.compr₂ (Algebra.trace ℚ E ∘ₗ LinearMap.mulLeft ℚ ξ₀)

def adelicSmul (a : E) : Adelic W →ₗ[Af] Adelic W :=
  LinearMap.baseChange Af ((LinearMap.lsmul E W a).restrictScalars ℚ)

variable (W) in

def linearAd : Subgroup (Adelic W ≃ₗ[Af] Adelic W) where
  carrier := {g | ∀ (a : E) (x : Adelic W), g (adelicSmul E a x) = adelicSmul E a (g x)}
  mul_mem' := fun {g g'} hg hg' a x => by
    simp only [LinearEquiv.mul_apply]; rw [hg' a x, hg a]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {g} hg a x => by
    apply g.injective
    rw [hg a]
    change g (g.symm _) = adelicSmul E a (g (g.symm x))
    simp

def unitaryAd (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : Subgroup (Adelic W ≃ₗ[Af] Adelic W) :=
  linearAd E W ⊓
  { carrier := {g | ∀ x y : Adelic W,
      LinearMap.BilinMap.baseChange Af h (g x) (g y) = LinearMap.BilinMap.baseChange Af h x y}
    mul_mem' := fun {g g'} hg hg' x y => by
      simp only [LinearEquiv.mul_apply]; rw [hg, hg']
    one_mem' := fun _ _ => rfl
    inv_mem' := fun {g} hg x y => by
      rw [← hg]
      change LinearMap.BilinMap.baseChange Af h (g (g.symm x)) (g (g.symm y)) = _
      simp }

def HasMultiplier (ψ : LinearMap.BilinForm ℚ W) (g : Adelic W ≃ₗ[Af] Adelic W) (ν : Afˣ) : Prop :=
  ∀ x y : Adelic W, ψ.baseChange Af (g x) (g y) = (ν : Af) * ψ.baseChange Af x y

def similitudeAd (ψ : LinearMap.BilinForm ℚ W) : Subgroup (Adelic W ≃ₗ[Af] Adelic W) :=
  linearAd E W ⊓
  { carrier := {g | ∃ ν : Afˣ, HasMultiplier ψ g ν}
    mul_mem' := fun {g g'} ⟨ν, hg⟩ ⟨ν', hg'⟩ => ⟨ν * ν', fun x y => by
      simp only [LinearEquiv.mul_apply]; rw [hg, hg', Units.val_mul, mul_assoc]⟩
    one_mem' := ⟨1, fun x y => by simp⟩
    inv_mem' := fun {g} ⟨ν, hg⟩ => ⟨ν⁻¹, fun x y => by
      have := hg (g.symm x) (g.symm y)
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [this, ← mul_assoc, Units.inv_mul, one_mul]; rfl⟩ }

omit [Module E W] [IsScalarTower ℚ E W] in

def stabAd (L : Set W) : Subgroup (Adelic W ≃ₗ[Af] Adelic W) where
  carrier := {g | ∀ x, g x ∈ hat L ↔ x ∈ hat L}
  mul_mem' := fun {g g'} hg hg' x => by
    simp only [LinearEquiv.mul_apply]; rw [hg, hg']
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {g} hg x => by
    rw [← hg]
    change g (g.symm x) ∈ _ ↔ _
    simp

def congrAd (L L' : Set W) : Subgroup (Adelic W ≃ₗ[Af] Adelic W) where
  carrier := {g | g ∈ stabAd L ∧ ∀ x ∈ hat L, g x - x ∈ hat L'}
  mul_mem' := fun {g g'} hg hg' => ⟨(stabAd L).mul_mem hg.1 hg'.1, fun x hx => by
    have h1 := hg.2 _ ((hg'.1 x).2 hx)
    have h2 := (hat L').add_mem h1 (hg'.2 x hx)
    simpa [LinearEquiv.mul_apply] using h2⟩
  one_mem' := ⟨(stabAd L).one_mem, fun x _ => by simp⟩
  inv_mem' := fun {g} hg => ⟨(stabAd L).inv_mem hg.1, fun x hx => by
    have hx' : g.symm x ∈ hat L := ((stabAd L).inv_mem hg.1 x).2 hx
    have h1 := (hat L').neg_mem (hg.2 _ hx')
    simp only [LinearEquiv.apply_symm_apply, neg_sub] at h1
    exact h1⟩

variable [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

def IsSelfDualLattice (ψ : LinearMap.BilinForm ℚ W) (Λ : Submodule (𝓞 E) W) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set W) = ⊤ ∧
    ∀ y : W, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ m : ℤ, ψ x y = m

def simLevel (ψ : LinearMap.BilinForm ℚ W) (Λ : Submodule (𝓞 E) W) (I : Ideal (𝓞 E)) :
    Subgroup (Adelic W ≃ₗ[Af] Adelic W) :=
  similitudeAd E ψ ⊓ congrAd (Λ : Set W) ((I • Λ : Submodule (𝓞 E) W) : Set W)

def simPrincipal (ψ : LinearMap.BilinForm ℚ W) (Λ : Submodule (𝓞 E) W) (N : ℕ) :
    Subgroup (Adelic W ≃ₗ[Af] Adelic W) :=
  simLevel E ψ Λ (Ideal.span {(N : 𝓞 E)})

def principal (ξ₀ : E) (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (Λ : Submodule (𝓞 E) W) (N : ℕ) :
    Subgroup (Adelic W ≃ₗ[Af] Adelic W) :=
  simPrincipal E (traceForm E ξ₀ h) Λ N ⊓ unitaryAd E h

def unitaryStab (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (Λ : Submodule (𝓞 E) W) :
    Subgroup (Adelic W ≃ₗ[Af] Adelic W) :=
  unitaryAd E h ⊓ stabAd (Λ : Set W)

def Induces (Λ : Submodule (𝓞 E) W) (I : Ideal (𝓞 E)) (g : Adelic W ≃ₗ[Af] Adelic W)
    (φ : (Λ ⧸ (I • ⊤ : Submodule (𝓞 E) Λ)) ≃ₗ[𝓞 E] (Λ ⧸ (I • ⊤ : Submodule (𝓞 E) Λ))) : Prop :=
  ∀ x y : Λ, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
    g ((1 : Af) ⊗ₜ[ℚ] (x : W)) - (1 : Af) ⊗ₜ[ℚ] (y : W) ∈
      hat ((I • Λ : Submodule (𝓞 E) W) : Set W)

def LevelClauses (ξ₀ : E) (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (Λ : Submodule (𝓞 E) W) (M : ℕ)
    (I : Ideal (𝓞 E)) : Prop :=
  {ν : Afˣ | ∃ g ∈ simLevel E (traceForm E ξ₀ h) Λ I, HasMultiplier (traceForm E ξ₀ h) g ν}
      = (ZhatUnits : Set Afˣ) ∧
  simLevel E (traceForm E ξ₀ h) Λ I ⊓ unitaryAd E h = principal E ξ₀ h Λ M ∧
  simPrincipal E (traceForm E ξ₀ h) Λ M ≤ simLevel E (traceForm E ξ₀ h) Λ I ∧
  ∀ φ : (Λ ⧸ (I • ⊤ : Submodule (𝓞 E) Λ)) ≃ₗ[𝓞 E] (Λ ⧸ (I • ⊤ : Submodule (𝓞 E) Λ)),
    ∃ g ∈ unitaryStab E h Λ, Induces E Λ I g φ

end Groups

def conjIdeal {K : Type} [Field K] [NumberField K] (c : K ≃ₐ[ℚ] K) (𝔐 : Ideal (𝓞 K)) :
    Ideal (𝓞 K) :=
  𝔐.map (RingOfIntegers.mapRingHom (c : K →+* K))

def LevelGroup : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (δ : K) (c : K ≃ₐ[ℚ] K) (σ₀ : K →+* ℂ)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] [IsGalois K E]
    (W : Type) [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (p q' : ℕ) (ξ₀ : E) (Λ : Submodule (𝓞 E) W)
    (M : ℕ) (𝔐 : Ideal (𝓞 K)),
    IsPrimeImagQuad d K δ → c δ = -δ →
    (∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P.asIdeal) →
    IsHermitian E h → HasSignature E h p q' → 1 ≤ p + q' → ((q' < p ∧ 1 ≤ q') ∨ q' = 0) →
    IsCMField.complexConj E ξ₀ = -ξ₀ →
    (∀ τ : E →+* ℂ, τ.comp (algebraMap K E) = σ₀ → 0 < (τ ξ₀).im) →
    IsSelfDualLattice E (traceForm E ξ₀ h) Λ →
    3 ≤ M → Odd M → Ideal.span {(M : 𝓞 K)} = 𝔐 * conjIdeal c 𝔐 → 𝔐 ⊔ conjIdeal c 𝔐 = ⊤ →
    LevelClauses E ξ₀ h Λ M ((conjIdeal c 𝔐).map (algebraMap (𝓞 K) (𝓞 E)))

def NormAndLevel : Prop := IdeleNormScale ∧ LevelGroup

example (K : Type) [Field K] [NumberField K] : IsNormScale (1 : (Adelic K)ˣ) 1 :=
  ⟨by simp, by simp⟩

example (E : Type) [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module ℚ W]
    (ξ₀ : E) (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (x y : W) :
    traceForm E ξ₀ h x y = Algebra.trace ℚ E (ξ₀ * h x y) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm
end
end

