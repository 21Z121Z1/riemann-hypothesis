import Mathlib

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsOneCocycleOnSubgroup
section
noncomputable section

namespace GlobalTheory.KCoh

variable {R : Type*} [CommRing R] {G : Type*} [Group G]
variable {M M' M'' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

def IsOneCocycleOnSubgroup (ρ : Representation R G M) (H : Subgroup G) (a : G → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g + ρ g (a h)

def d1 (ρ : Representation R G M) (b : G → M) (g h : G) : M := ρ g (b h) - b (g * h) + b g

def IsTwoCocycleOnSubgroup (ρ : Representation R G M) (H : Subgroup G) (z : G → G → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ k ∈ H, ρ g (z h k) - z (g * h) k + z g (h * k) - z g h = 0

def Cob (ρ : Representation R G M) (H : Subgroup G) (z : G → G → M) (η : G → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, z g h = d1 ρ η g h

def Eqv (ρ : Representation R G M) (ρ' : Representation R G M') (f : M →ₗ[R] M') : Prop :=
  ∀ g m, f (ρ g m) = ρ' g (f m)

def Eqv₂ (ρ : Representation R G M) (ρ' : Representation R G M') (ρ'' : Representation R G M'')
    (β : M →ₗ[R] M' →ₗ[R] M'') : Prop :=
  ∀ g m m', β (ρ g m) (ρ' g m') = ρ'' g (β m m')

def Triv (ρ : Representation R G M) (H : Subgroup G) : Prop := ∀ h ∈ H, ∀ m, ρ h m = m

def cup (ρ' : Representation R G M') (β : M →ₗ[R] M' →ₗ[R] M'') (a : G → M) (b : G → M') (g h : G) : M'' :=
  β (a g) (ρ' g (b h))

def edge (ρ : Representation R G M) (z : G → G → M) (η : G → M) (σ h : G) : M :=
  ρ σ (η (σ⁻¹ * h * σ)) - η h + z h σ - z σ (σ⁻¹ * h * σ)

def conj (ρ : Representation R G M) (σ : G) (φ : G → M) (h : G) : M := ρ σ (φ (σ⁻¹ * h * σ))

def tw (χ : G →* Rˣ) (ρ : Representation R G M) : Representation R G M where
  toFun g := (χ g : R) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext m
    simp [mul_smul, smul_comm (χ h : R) (χ g : R)]

def chr (χ : G →* Rˣ) : Representation R G R := tw χ (Representation.trivial R G R)

def sh (S : Type*) [MulAction G S] (ρ : Representation R G M) : Representation R G (S → M) where
  toFun g :=
    { toFun := fun f s => ρ g (f (g⁻¹ • s))
      map_add' := fun f f' => by funext s; simp
      map_smul' := fun c f => by funext s; simp }
  map_one' := by ext f s; simp
  map_mul' g h := by ext f s; simp [mul_smul]

def push {S S' : Type*} [Fintype S'] (π : S' → S) : (S' → M) →ₗ[R] (S → M) :=
  open Classical in
  { toFun := fun f s => ∑ s' ∈ Finset.univ.filter (fun s' => π s' = s), f s'
    map_add' := fun f f' => by funext s; simp [Finset.sum_add_distrib]
    map_smul' := fun c f => by funext s; simp [Finset.smul_sum] }

def pull {S S' : Type*} (π : S' → S) : (S → M) →ₗ[R] (S' → M) := LinearMap.funLeft R M π

def ptw (S : Type*) (β : M →ₗ[R] M' →ₗ[R] M'') : (S → M) →ₗ[R] (S → M') →ₗ[R] (S → M'') :=
  LinearMap.mk₂ R (fun f f' s => β (f s) (f' s))
    (fun _ _ _ => by funext s; simp) (fun _ _ _ => by funext s; simp)
    (fun _ _ _ => by funext s; simp) (fun _ _ _ => by funext s; simp)

def fam {S : Type*} (f : S → M →ₗ[R] M') : (S → M) →ₗ[R] (S → M') where
  toFun m s := f s (m s)
  map_add' _ _ := by funext s; simp
  map_smul' _ _ := by funext s; simp

def lg {Ω : Type*} [Field Ω] {N : ℕ} (ζ a b : Ω) : ZMod N :=
  open Classical in
  if h : ∃ i : ZMod N, a = ζ ^ i.val * b then h.choose else 0

def kum {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S : Type*} [MulAction (Ω ≃ₐ[F] Ω) S] (N : ℕ) (ζ : Ω)
    (θ : S → Ω) (g : Ω ≃ₐ[F] Ω) (s : S) : ZMod N :=
  lg ζ (g (θ (g⁻¹ • s))) (θ s)

def Roots {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S : Type*} [MulAction (Ω ≃ₐ[F] Ω) S] (N : ℕ)
    (θ : S → Ω) : Prop :=
  (∀ s, θ s ≠ 0) ∧ ∀ (g : Ω ≃ₐ[F] Ω) s, θ (g • s) ^ N = g (θ s ^ N)

@[simp] theorem sh_apply (S : Type*) [MulAction G S] (ρ : Representation R G M) (g : G) (f : S → M) (s : S) :
    sh S ρ g f s = ρ g (f (g⁻¹ • s)) := rfl

@[simp] theorem tw_apply (χ : G →* Rˣ) (ρ : Representation R G M) (g : G) (m : M) :
    tw χ ρ g m = (χ g : R) • ρ g m := rfl

@[simp] theorem pull_apply {S S' : Type*} (π : S' → S) (f : S → M) (s : S') : pull (R := R) π f s = f (π s) := rfl

@[simp] theorem ptw_apply (S : Type*) (β : M →ₗ[R] M' →ₗ[R] M'') (f : S → M) (f' : S → M') (s : S) :
    ptw S β f f' s = β (f s) (f' s) := rfl

@[simp] theorem fam_apply {S : Type*} (f : S → M →ₗ[R] M') (m : S → M) (s : S) : fam f m s = f s (m s) := rfl

example (ρ : Representation R G M) (H : Subgroup G) : IsTwoCocycleOnSubgroup ρ H 0 ∧ Cob ρ H 0 0 :=
  ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp [d1]⟩

example (ρ : Representation R G M) (H : Subgroup G) (b : G → M) : Cob ρ H (d1 ρ b) b := fun _ _ _ _ => rfl

example {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S : Type*} [MulAction (Ω ≃ₐ[F] Ω) S] (N : ℕ) :
    Roots (F := F) N (fun _ : S => (1 : Ω)) := ⟨fun _ => one_ne_zero, fun g s => by simp⟩

end GlobalTheory.KCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
section
noncomputable section

open scoped Matrix

namespace GlobalTheory.KA

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]

def ShCoc {X : Type*} [Monoid X] (ρ : Γ → Matrix (Fin 2) (Fin 2) R) (κ : Γ →* X) (Y : Γ → X → Fin 2 → R) : Prop :=
  ∀ s t x, Y (s * t) x = Y s x + ρ s *ᵥ Y t (x * κ s)

def ShCocOn {X : Type*} [Monoid X] (H : Subgroup Γ) (ν : Γ → R) (κ : Γ →* X) (z : Γ → X → R) : Prop :=
  ∀ s ∈ H, ∀ t ∈ H, ∀ x, z (s * t) x = z s x + ν s * z t (x * κ s)

def push {X X' : Type*} [Fintype X'] [DecidableEq X] {M : Type*} [AddCommMonoid M] (π : X' → X) (Y : Γ → X' → M) :
    Γ → X → M :=
  fun s x => ∑ x' ∈ Finset.univ.filter (fun x' => π x' = x), Y s x'

def spec {X : Type*} [Fintype X] (η : X → R) (Y : Γ → X → Fin 2 → R) : Γ → Fin 2 → R :=
  fun s => ∑ x, η x • Y s x

end GlobalTheory.KA

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
section
noncomputable section

namespace GlobalTheory.PRep

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

def eig (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) : Submodule k V where
  carrier := {v | ∀ h : H, ρ (h : G) v = (χ h : k) • v}
  add_mem' := by
    intro a b ha hb h
    rw [map_add, ha h, hb h, smul_add]
  zero_mem' := by intro h; simp
  smul_mem' := by
    intro c v hv h
    rw [map_smul, hv h, smul_comm]

def fixed (ρ : Representation k G V) (H : Subgroup G) : Submodule k V := eig ρ H 1

def twKer (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Submodule k V :=
  Submodule.span k {w | ∃ (n : N) (v : V), w = ρ (n : G) v - (ψ n : k) • v}

abbrev TwJacquet (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Type := V ⧸ twKer ρ N ψ

abbrev Jacquet (ρ : Representation k G V) (N : Subgroup G) : Type := TwJacquet ρ N 1

theorem twKer_le_comap (ρ : Representation k G V) (N : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    twKer ρ N 1 ≤ (twKer ρ N 1).comap (ρ g) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  have hn : g * (n : G) * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 hg n).1 n.2
  refine Submodule.subset_span ⟨⟨_, hn⟩, ρ g v, ?_⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

def jacquet (ρ : Representation k G V) (N : Subgroup G) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) : Representation k M (Jacquet ρ N) where
  toFun m := (twKer ρ N 1).mapQ (twKer ρ N 1) (ρ (s m)) (twKer_le_comap ρ N _ (hs m))
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

def onFixed (ρ : Representation k G V) (N : Subgroup G) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) : Representation k M (fixed ρ N) where
  toFun m := (ρ (s m)).restrict (p := fixed ρ N) (q := fixed ρ N) (by
    intro v hv n
    have hn : (s m)⁻¹ * (n : G) * (s m)⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem (hs m)) n).1 n.2
    have h := hv ⟨_, hn⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h ⊢
    conv_rhs => rw [← h]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp only [map_mul]
    rfl

section Top
variable [TopologicalSpace G]

def IsSmooth (ρ : Representation k G V) : Prop := ∀ v : V, IsOpen {g : G | ρ g v = v}

def IsAdmissible (ρ : Representation k G V) : Prop :=
  IsSmooth ρ ∧ ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional k (fixed ρ K)

end Top

variable {W : Type} [AddCommGroup W] [Module k W]

def rightReg (k G W : Type) [Field k] [Group G] [AddCommGroup W] [Module k W] :
    Representation k G (G → W) where
  toFun g := LinearMap.funLeft k W (fun x => x * g)
  map_one' := by ext f x; simp [LinearMap.funLeft]
  map_mul' a b := by ext f x; simp [LinearMap.funLeft, mul_assoc]

def indSpace (H : Subgroup G) (σ : Representation k H W) : Submodule k (G → W) where
  carrier := {f | ∀ (h : H) (g : G), f (h * g) = σ h (f g)}
  add_mem' := by
    intro a b ha hb h g
    simp [ha h g, hb h g]
  zero_mem' := by intro h g; simp
  smul_mem' := by
    intro c f hf h g
    simp [hf h g]

def sub (ρ : Representation k G V) (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) :
    Representation k G U where
  toFun g := (ρ g).restrict (hU g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

def ind (H : Subgroup G) (σ : Representation k H W) : Representation k G (indSpace H σ) :=
  sub (rightReg k G W) (indSpace H σ) (by
    intro g f hf h x
    have := hf h (x * g)
    simpa [rightReg, LinearMap.funLeft, mul_assoc] using this)

section Top2
variable [TopologicalSpace G] [IsTopologicalGroup G]

def smoothPart (ρ : Representation k G V) : Submodule k V where
  carrier := {v | IsOpen {g : G | ρ g v = v}}
  add_mem' := by
    intro a b ha hb
    let T : Subgroup G :=
      { carrier := {g | ρ g (a + b) = a + b}
        mul_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *; rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]; simp }
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((ha.inter hb).mem_nhds (by simp)) ?_)
    rintro g ⟨h1, h2⟩
    show ρ g (a + b) = a + b
    rw [map_add, h1, h2]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    by_cases hc : c = 0
    · simp [hc]
    · have : {g : G | ρ g (c • v) = c • v} = {g : G | ρ g v = v} := by
        ext g; simp [smul_right_inj hc]
      show IsOpen {g : G | ρ g (c • v) = c • v}
      rw [this]; exact hv

theorem smoothPart_stable (ρ : Representation k G V) (g : G) (v : V) (hv : v ∈ smoothPart ρ) :
    ρ g v ∈ smoothPart ρ := by
  have : {x : G | ρ x (ρ g v) = ρ g v} = (fun x => g⁻¹ * x * g) ⁻¹' {x : G | ρ x v = v} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
    constructor
    · intro h; rw [h, ← Module.End.mul_apply, ← map_mul]; simp
    · intro h
      have := congrArg (ρ g) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  show IsOpen {x : G | ρ x (ρ g v) = ρ g v}
  rw [this]
  exact IsOpen.preimage (by fun_prop) hv

def smoothRep (ρ : Representation k G V) : Representation k G (smoothPart ρ) :=
  sub ρ (smoothPart ρ) (smoothPart_stable ρ)

def smInd (H : Subgroup G) (σ : Representation k H W) :
    Representation k G (smoothPart (ind H σ)) := smoothRep (ind H σ)

def cIndSpace (H : Subgroup G) (σ : Representation k H W) : Submodule k (smoothPart (ind H σ)) where
  carrier := {f | ∃ C : Set G, IsCompact C ∧ ∀ g, f.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c}
  add_mem' := by
    rintro a b ⟨C, hC, ha⟩ ⟨D, hD, hb⟩
    refine ⟨C ∪ D, hC.union hD, fun g hg => ?_⟩
    by_cases h : a.1.1 g = 0
    · obtain ⟨h, hh, c, hc, e⟩ := hb g (by intro h'; apply hg; simp [h, h'])
      exact ⟨h, hh, c, Or.inr hc, e⟩
    · obtain ⟨h, hh, c, hc, e⟩ := ha g h
      exact ⟨h, hh, c, Or.inl hc, e⟩
  zero_mem' := ⟨∅, isCompact_empty, by simp⟩
  smul_mem' := by
    rintro c f ⟨C, hC, hf⟩
    exact ⟨C, hC, fun g hg => hf g (by intro h; apply hg; simp [h])⟩

def cInd (H : Subgroup G) (σ : Representation k H W) : Representation k G (cIndSpace H σ) :=
  sub (smInd H σ) (cIndSpace H σ) (by
    rintro g f ⟨C, hC, hf⟩
    refine ⟨(fun c => c * g⁻¹) '' C, hC.image (by fun_prop), fun x hx => ?_⟩
    obtain ⟨h, hh, c, hc, e⟩ := hf (x * g) hx
    exact ⟨h, hh, c * g⁻¹, ⟨c, hc, rfl⟩, by rw [← mul_assoc, ← e]; group⟩)

def IsSupercuspidal (ρ : Representation k G V) : Prop :=
  IsSmooth ρ ∧ ∀ (v : V) (l : Module.Dual k V), l ∈ smoothPart ρ.dual →
    ∃ C : Set G, IsCompact C ∧ ∀ g, l (ρ g v) ≠ 0 → ∃ z ∈ Subgroup.center G, ∃ c ∈ C, g = z * c

end Top2

end GlobalTheory.PRep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

variable (L : Type) [Field L] [NumberField L]

abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ

def diagUnits : Lˣ →* Ideles L := Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom

open Classical in

def finSingle (v : HeightOneSpectrum (𝓞 L)) : v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L where
  toFun x := ⟨Pi.mulSingle v x, by
    refine Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset ?_)
    intro w hw
    by_contra h
    apply hw
    have h' : w ≠ v := h
    rw [Pi.mulSingle_eq_of_ne h']
    exact one_mem _⟩
  map_one' := by
    apply Subtype.ext
    exact Pi.mulSingle_one v
  map_mul' x y := by
    apply Subtype.ext
    exact Pi.mulSingle_mul v x y

def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp (finSingle L v))

open Classical in

def infIdele (w : InfinitePlace L) : (w.Completion)ˣ →* Ideles L :=
  Units.map ((MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
    (MonoidHom.mulSingle (fun w : InfinitePlace L => w.Completion) w))

theorem valued_algebraMap_eq_one (v : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L x)) = 1 := by
  show Valued.v ((algebraMap (𝓞 L) L x : L) : v.adicCompletion L) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff).mpr hx

end GlobalTheory.Mem.Chr
end
end

