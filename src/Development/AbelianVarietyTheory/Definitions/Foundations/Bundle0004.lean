import Mathlib
import ReciprocityTheory.DualLattices.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
section
namespace GlobalTheory.FGDepth

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C]

def toE (x : WithTop ℝ) : EReal := (WithBot.some x : WithBot (WithTop ℝ))

def mfact {σ : Type} (α : σ →₀ ℕ) : C := α.prod fun _ n => (n.factorial : C)

def derivAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ α ∈ P.support, P.coeff α * mfact α * coeff α g

def content (v : AddValuation C (WithTop ℝ)) {σ : Type} (P : MvPolynomial σ C) : EReal :=
  ⨅ α ∈ P.support, toE (v (P.coeff α * mfact α))

variable {v : AddValuation C (WithTop ℝ)}

def IsExp {d : ℕ} (G : LogFGL v d) (ex : Fin d → MvPowerSeries (Fin d) C) : Prop :=
  (∀ a, constantCoeff (ex a) = 0) ∧ ∀ a, subst ex (G.lg a) = X a

def expOf {d : ℕ} (G : LogFGL v d) : Fin d → MvPowerSeries (Fin d) C :=
  Classical.epsilon (IsExp G)

def expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) :
    (Σ b, Fin (d b)) → MvPowerSeries (Σ b, ι b) C :=
  fun x => subst (fun e : Fin (d x.1) =>
    ∑ a, u x.1 a e • (X ⟨x.1, a⟩ : MvPowerSeries (Σ b, ι b) C)) (expOf (G x.1) x.2)

def depth {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C) : EReal :=
  ⨅ f : {f : MvPowerSeries (Σ b, Fin (d b)) C // MvIsInt v f},
    toE (v (derivAt0 P (subst (expAlong G u) f.1)))

def detPow (C : Type) [Field C] (i c : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) C :=
  (Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C))) ^ c

def IsSatFrame (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (u : Fin i → Fin d → C) : Prop :=
  (∀ a e, IsIntV v (u a e)) ∧
    ∃ r : Fin i → Fin d, v (Matrix.det (Matrix.of fun a b => u a (r b))) = 0

def detDepth {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C) (c : ℕ) : EReal :=
  depth (fun _ : Fin i => G) (fun _ => u) (detPow C i c)

def IsCharLog {d : ℕ} (G : LogFGL v d) (l : Fin d → C) : Prop :=
  ∃ χ : MvPowerSeries (Fin d) C, MvIsInt v χ ∧
    ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => l e ^ n / (n.factorial : C)

end

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
section
noncomputable section

namespace GlobalTheory.K4

open GlobalTheory.KEdge GlobalTheory.NeedB

variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def geo (F K Ω : Type*) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] :
    Subgroup (Ω ≃ₐ[F] Ω) :=
  (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup

def IsTopW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) (w : K) :
    Prop :=
  w ≠ 0 ∧ ∃ θ : Ω, θ ^ N = algebraMap K Ω w ∧ ∀ g ∈ geo F K Ω, kum (K := F) (N := N) ζ θ g = edge x y η σ g

open Classical in

def topW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) : K :=
  if h : ∃ w : K, IsTopW ζ x y η σ w then h.choose else 1

def topCoc {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) : K :=
  topW ζ x y η σ⁻¹

namespace TopW

variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}

theorem mem_geo (g : Ω ≃ₐ[F] Ω) : g ∈ geo F K Ω ↔ ∀ z : K, g (algebraMap K Ω z) = algebraMap K Ω z := by
  unfold geo
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h z
    exact h _ ⟨z, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    exact h z

theorem conj_mem_geo [Normal F K] (σ : Ω ≃ₐ[F] Ω) {h : Ω ≃ₐ[F] Ω} (hh : h ∈ geo F K Ω) : σ * h * σ⁻¹ ∈ geo F K Ω := by
  rw [mem_geo] at hh ⊢
  intro z
  have h1 : σ⁻¹ (algebraMap K Ω z) = algebraMap K Ω ((σ⁻¹).restrictNormal K z) :=
    (AlgEquiv.restrictNormal_commutes σ⁻¹ K z).symm
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, hh, ← h1]
  exact σ.apply_symm_apply _

theorem exists_of_fixed [IsGalois K Ω] {z : Ω} (hz : ∀ g ∈ geo F K Ω, g z = z) : ∃ c : K, algebraMap K Ω c = z :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) z).2 fun g =>
    hz (AlgEquiv.restrictScalarsHom F g) ((mem_geo _).2 fun w => g.commutes w)

theorem apply_eq_kum [NeZero N] (hζ : IsPrimitiveRoot ζ N) {θ : Ω} {w : K} (hw0 : w ≠ 0)
    (hw : θ ^ N = algebraMap K Ω w) {g : Ω ≃ₐ[F] Ω} (hg : g ∈ geo F K Ω) :
    g θ = ζ ^ (kum (K := F) (N := N) ζ θ g).val * θ := by
  have hw1 : algebraMap K Ω w ≠ 0 := by simpa using hw0
  have hθ : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hw
    exact hw1 hw.symm
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hw, (mem_geo g).1 hg, div_self hw1]
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine kum_choose_spec ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, he, div_mul_cancel₀ _ hθ]

theorem pow_val_add [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem pow_val_mul [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a * b).val = (ζ ^ b.val) ^ a.val := by
  rw [← pow_mul, mul_comm b.val, ZMod.val_mul]
  conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem edge_mul_conj {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ τ h : Γ) :
    edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h := by
  simp only [edge, map_mul, map_inv, toAdd_mul, toAdd_inv, mul_inv_rev]
  have : σ * τ * h * (τ⁻¹ * σ⁻¹) = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
  rw [this]; ring

theorem edge_inv {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) :
    edge x y η σ⁻¹ h = η (σ⁻¹ * h * σ) - η h + (x h).toAdd * (y σ).toAdd - (x σ).toAdd * (y h).toAdd := by
  simp only [edge, map_inv, toAdd_inv, inv_inv]
  ring

theorem isTopW_topW_of_exists {σ : Ω ≃ₐ[F] Ω} (h : ∃ w : K, IsTopW ζ x y η σ w) :
    IsTopW ζ x y η σ (topW (K := K) ζ x y η σ) := by
  unfold topW
  rw [dif_pos h]
  exact h.choose_spec

theorem topW_ne_zero (σ : Ω ≃ₐ[F] Ω) : topW (K := K) ζ x y η σ ≠ 0 := by
  by_cases h : ∃ w : K, IsTopW ζ x y η σ w
  · exact (isTopW_topW_of_exists h).1
  · unfold topW
    rw [dif_neg h]
    exact one_ne_zero

theorem unique [NeZero N] [IsGalois K Ω] (hζ : IsPrimitiveRoot ζ N) {σ : Ω ≃ₐ[F] Ω} {w v : K}
    (hw : IsTopW ζ x y η σ w) (hv : IsTopW ζ x y η σ v) : ∃ c : K, c ≠ 0 ∧ w = v * c ^ N := by
  obtain ⟨hw0, θ, hθ, hθk⟩ := hw
  obtain ⟨hv0, ψ, hψ, hψk⟩ := hv
  have hv1 : algebraMap K Ω v ≠ 0 := by simpa using hv0
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  obtain ⟨c, hc⟩ := exists_of_fixed (F := F) (K := K) (z := θ / ψ) fun g hg => by
    rw [map_div₀, apply_eq_kum hζ hw0 hθ hg, apply_eq_kum hζ hv0 hψ hg, hθk g hg, hψk g hg,
      mul_div_mul_left _ _ (pow_ne_zero _ hz)]
  have key : w = v * c ^ N := by
    apply (algebraMap K Ω).injective
    rw [map_mul, map_pow, hc, div_pow, hθ, hψ, mul_div_cancel₀ _ hv1]
  refine ⟨c, ?_, key⟩
  rintro rfl
  rw [zero_pow (NeZero.ne N), mul_zero] at key
  exact hw0 key

example : geo ℝ ℝ ℂ = ⊤ := by
  ext g
  simp only [mem_geo, Subgroup.mem_top, iff_true]
  exact fun z => g.commutes z

example [NeZero N] (hζ : IsPrimitiveRoot ζ N) (σ : Ω ≃ₐ[F] Ω) : IsTopW (N := N) ζ 1 1 0 σ (1 : K) :=
  ⟨one_ne_zero, 1, by simp, fun g _ => by
    rw [kum_eq_of hζ one_ne_zero 0 (by simp)]
    simp [edge]⟩

example (σ : ℂ ≃ₐ[ℝ] ℂ) : ¬ IsTopW (N := 2) (-1 : ℂ) 1 1 0 σ (-1 : ℝ) := by
  intro h
  have hζ : IsPrimitiveRoot (-1 : ℂ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have h1 : IsTopW (N := 2) (-1 : ℂ) 1 1 0 σ (1 : ℝ) :=
    ⟨one_ne_zero, 1, by simp, fun g _ => by
      rw [kum_eq_of hζ one_ne_zero 0 (by simp)]
      simp [edge]⟩
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℝ ℂ := {}
  obtain ⟨c, -, hc⟩ := unique hζ h h1
  nlinarith [sq_nonneg c]

end TopW

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.Letter
section
noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.OverY (X : Tower Ω ε) (W : ValuationSubring X.K) : Prop :=
  (∀ c : Ω, algebraMap Ω X.K c ∈ W) ∧ X.jK ∈ W

def Tower.Un (X : Tower Ω ε) (m : ℕ) : Set X.Kˣ :=
  {f | ∀ W, X.OverY W → ∃ g : X.Kˣ, W.valuation ((f : X.K) / (g : X.K) ^ m) = 1}

abbrev Tower.Kl (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := TensorProduct ℤ ℤ_[l] (Additive X.Kˣ)

abbrev idl (l : ℕ) [Fact l.Prime] : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l])}

abbrev Tower.Khat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := AdicCompletion (idl l) (X.Kl l)

def Tower.cls (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.Kˣ) :
    X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l))) :=
  Submodule.Quotient.mk ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul f)

def Tower.ASet (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Set (X.Khat l) :=
  {a | ∀ n : ℕ, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f}

def Tower.A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Khat l) := Submodule.span ℤ_[l] (X.ASet l)

def Tower.kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Khat l →ₗ[ℤ_[l]] X.Khat l :=
  AdicCompletion.map (idl l) (LinearMap.baseChange ℤ_[l]
    (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))))

abbrev Tower.Fn (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : Type := (Fin 2 → ℤ_[l]) → X.Khat l

def Tower.Pol (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w : ℕ) : Set (X.Fn l) :=
  {b | ∃ c : Fin (w + 1) → X.Khat l, (∀ i, c i ∈ X.A l) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}

def mZl (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ_[l] := m.map (Int.castRingHom ℤ_[l])

def Tower.act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.sl (toGQ m)).toRingEquiv (b (mZl l m *ᵥ u))
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp

def Gam (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l

def Tower.BSet (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Set (X.Fn l) :=
  {b | b ∈ X.Pol l w ∧ ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b}

def Tower.B (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (X.Fn l) := Submodule.span ℤ_[l] (X.BSet N l w)

def IsDiam (N l d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l ∧ (en γ 1 1 : ZMod N) = d

def sgD (N l d : ℕ) : SL(2, ℤ) := Classical.epsilon (IsDiam N l d)

def Tower.diam (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (d : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)

def Tower.heckeT (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (q : ℕ) : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) +
    X.act l ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])

def Tower.heckeU (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : X.Fn l →ₗ[ℤ_[l]] X.Fn l :=
  ∑ j ∈ Finset.range l, X.act l !![1, (j : ℤ); 0, (l : ℤ)]

def Tower.galB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : X.Fn l →ₗ[ℤ_[l]] X.Fn l where
  toFun b u := X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1])
  map_add' b b' := by funext u; simp
  map_smul' c b := by funext u; simp

inductive Letter
  | T (q : ℕ)
  | U
  | D (d : ℕ)

def Tower.op (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : Letter → (X.Fn l →ₗ[ℤ_[l]] X.Fn l)
  | Letter.T q => X.heckeT N l q
  | Letter.U => X.heckeU l
  | Letter.D d => X.diam N l d

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.LocallyConstantTwoCochain
section
noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IsCyc (T : Tower p Ω) (k : ℕ) (χ : Gal p Ω → ZMod (p ^ k)) : Prop :=
  ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val

def LocallyConstantTwoCochain (k : ℕ) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  (∀ g h, IsInt p (ξ g h)) ∧ ∀ g h, ∃ S : Finset Ω, ∀ g' h' : Gal p Ω,
    (∀ x ∈ S, g' x = g x ∧ h' x = h x) → Cong p k (ξ g' h') (ξ g h)

def IsTwistedTwoCocycleModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ t ∈ H,
    Cong p k (((χ g).val : Ω) * g (ξ h t) + ξ g (h * t)) (ξ (g * h) t + ξ g h)

def IsTwistedTwoCoboundaryModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, LocallyConstantOneCochain k w ∧ ∀ g ∈ H, ∀ h ∈ H,
    Cong p k (ξ g h) (((χ g).val : Ω) * g (w h) - w (g * h) + w g)

end GlobalTheory.K5
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Subfield X.K :=
  ⨅ γ ∈ Γ', RingHom.eqLocusField (X.sl (ofSL γ)).toRingEquiv.toRingHom (RingHom.id X.K)

def mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Subfield X.K :=
  lev X Γ' ⊓ ⨅ s ∈ S, RingHom.eqLocusField (X.gal s).toRingHom (RingHom.id X.K)

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
section
noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

section Formal

variable {R : Type*} [CommRing R]

def Uo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (l * n)

def Vo (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then a (n / l) else 0

def dep (l : ℕ) (a : ℕ → R) : ℕ → R := fun n => if l ∣ n then 0 else a n

def To (k : ℕ) (c : R) (q : ℕ) (a : ℕ → R) : ℕ → R := fun n => a (q * n) + c * (q : R) ^ (k - 1) * Vo q a n

def mul (a b : ℕ → R) : ℕ → R := fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def eis (j : ℕ) (c : R) (a b : ℤ → R) : ℕ → R := fun n =>
  if n = 0 then c else ∑ p ∈ n.divisorsAntidiagonal, a p.1 * (p.1 : R) ^ (j - 1) * b p.2

def Zs (k l : ℕ) (u v : ℤ → R) (F : ℕ → ℕ → R) : ℕ → R := fun n =>
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ x ∈ p.1.divisorsAntidiagonal, ∑ y ∈ p.2.divisorsAntidiagonal,
    if l ∣ p.1 ∨ l ∣ p.2 then 0 else (x.1 : R) ^ (k - 2) * u x.2 * v y.1 * F x.1 y.1

def quo {M : ℕ} (f : ZMod M → R) : ℕ → ℕ → R := fun x x' => f ((x : ZMod M) * (x' : ZMod M)⁻¹)

def lam (B : ℕ) (c a : ℕ → R) : R := ∑ n ∈ Finset.range B, c n * a n

end Formal

section Level

variable {K : Type*} [Field K]

def val (B : ℕ) (c : ℕ → K) (l : ℕ) (α : K) (r : ℕ) (a : ℕ → K) : K := (α ^ r)⁻¹ * lam B c ((Uo l)^[r] a)

def Fser (j M : ℕ) (ζ : K) (b : ℤ → K) (c : K) (u w : ZMod M) : ℕ → K := fun s =>
  if s = 0 then c else ∑ p ∈ s.divisorsAntidiagonal,
    ((if (p.1 : ZMod M) = u then ((p.1 : K) / M) ^ (j - 1) * ζ ^ (w.val * p.2) * b p.2 else 0) -
      (if -(p.1 : ZMod M) = u then (-(p.1 : K) / M) ^ (j - 1) * (ζ ^ (w.val * p.2))⁻¹ * b (-(p.2 : ℤ)) else 0))

end Level

section Bridge

variable {K : Type*} [Field K] [CharZero K]

theorem mul_eq_cmul (f g : ℕ → K) : mul f g = GlobalTheory.KummerEisensteinGalois.cmul f g := by
  funext n
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f i * g j) n

end Bridge

example : eis 4 (0 : ℤ) (fun _ => 1) (fun _ => 1) 2 = 9 := by decide

example : To 12 (1 : ℤ) 2 (fun n => if n = 1 then 1 else if n = 4 then -1472 else 0) 2 = (-24) ^ 2 := by
  simp [To, Vo]

example (u v : ℤ → ℤ) (F : ℕ → ℕ → ℤ) : Zs 3 3 u v F 2 = u 1 * v 1 * F 1 1 := by
  simp [Zs, Finset.Nat.antidiagonal_succ]

def hat {N : ℕ} (φ : ZMod N → ℂ) (d : ℤ) : ℂ := ∑ y ∈ Finset.range N, φ y * cexp (2 * π * Complex.I * (y * d) / N)

def qs (a : ℕ → ℂ) (τ : ℍ) : ℂ := ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)

def PolyB (a : ℕ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A

def Inv (k L : ℕ) (χ : ℤ → ℂ) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ : ℍ, f (γ • τ) = χ (γ 1 1) * (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ k * f τ

def MF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := PolyB a ∧ Inv k L χ (qs a)

def CF (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) : Prop := MF k L χ a ∧ ∃ C : ℝ, ∀ τ : ℍ, ‖qs a τ‖ ^ 2 * τ.im ^ k ≤ C

def ch {N : ℕ} (χ : DirichletCharacter ℂ N) : ℤ → ℂ := fun d => χ (d : ZMod N)

structure Prim (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) : Prop where
  cf : CF k N (ch χ) g
  one : g 1 = 1
  zero : ∀ n : ℕ, ¬ n.Coprime N → g n = 0
  eig : ∀ q : ℕ, q.Prime → ¬ q ∣ N → To k (ch χ q) q g = fun n => g q * g n

structure Wt (L : ℕ) (ρ : ℍ → ℝ) : Prop where
  meas : Measurable ρ
  nonneg : ∀ τ, 0 ≤ ρ τ
  sum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ)) • τ)) 1
  supp : ∃ S : Finset SL(2, ℤ), ∀ τ, ρ τ ≠ 0 → ∃ γ ∈ S, γ • τ ∈ ModularGroup.fd

def pet (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) : ℂ := ∫ τ : ℍ, (ρ τ : ℂ) * (conj (h τ) * f τ * (τ.im : ℂ) ^ k)

def petIP (k : ℕ) (ρ : ℍ → ℝ) (f h : ℍ → ℂ) : ℂ := ∫ τ : ℍ, 2 * (ρ τ : ℂ) * (f τ * conj (h τ) * (τ.im : ℂ) ^ k)

structure EigF (k N l : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) : Prop where
  T : ∀ a, MF k (N * l) (ch ε) a → ∀ q : ℕ, q.Prime → ¬ q ∣ N * l → lam B c (To k (ch ε q) q a) = t q * lam B c a
  U : ∀ a, MF k (N * l) (ch ε) a → lam B c (Uo l a) = α * lam B c a

def trm (j : ℕ) (s : ℝ) (z : ℂ) : ℂ := (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)

def dif (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) : ℤ × ℤ → ℂ := fun x =>
  F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, F (x + (r : ℤ) • v)

def lat (j : ℕ) (s : ℝ) (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ) : ℂ :=
  ∑' x : ℤ × ℤ, Φ x * dif L v (dif L v fun y => trm j s ((y.1 : ℂ) * τ + y.2)) x

end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
section
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def rowT (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val + (p : ℤ) ^ n * w.1,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * w.2)

def pieceT (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (smF d 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

def pieceTRaw (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (w w' : ℤ × ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 w).1 (rowT N p n γ 0 w).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 w').1 (rowT N p n γ 1 w').2) r

end GlobalTheory.KummerEisensteinGalois
end
end

