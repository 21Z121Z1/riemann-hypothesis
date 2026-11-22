import Mathlib

-- bundled from Formalism.LogSumExpBounds.StatementC
section
namespace Formalism.NuclearRankWeightBounds.C

open Matrix

section
variable (RR : Type*) (K : Type*) [CommRing RR] [CommRing K] [Algebra RR K]

abbrev KmodR : Type _ := K ⧸ LinearMap.range (Algebra.linearMap RR K)

variable {RR}

abbrev coker {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) : Type _ :=
  (Fin k → RR) ⧸ LinearMap.range Z.mulVecLin

def toK {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) : Matrix (Fin k) (Fin k) K :=
  Z.map (algebraMap RR K)

noncomputable def rowInvMod {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K) :
    (Fin k → RR) →ₗ[RR] KmodR RR K :=
  (Submodule.mkQ _).comp
    { toFun := fun v => ∑ i, ∑ j, r i * (toK K Z)⁻¹ i j * algebraMap RR K (v j)
      map_add' := by intro v w; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        rw [RingHom.id_apply]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring }

noncomputable def descend {k : ℕ} (Z : Matrix (Fin k) (Fin k) RR) (r : Fin k → K) :
    coker Z →ₗ[RR] KmodR RR K := by
  classical
  exact if hZ : LinearMap.range Z.mulVecLin ≤ LinearMap.ker (rowInvMod K Z r) then
    (LinearMap.range Z.mulVecLin).liftQ (rowInvMod K Z r) hZ else 0

variable {m : ℕ}

def ebar (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker Z :=
  Submodule.Quotient.mk (Pi.single (Fin.last m) 1)

noncomputable def lam (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker Z →ₗ[RR] KmodR RR K :=
  descend K Z (Pi.single (Fin.last m) 1)

noncomputable def kappa (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : K :=
  (toK K Z)⁻¹ (Fin.last m) (Fin.last m)

def blk (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : Matrix (Fin m) (Fin m) RR :=
  Z.submatrix Fin.castSucc Fin.castSucc

def bbar (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker (blk Z) :=
  Submodule.Quotient.mk (fun i => Z (Fin.castSucc i) (Fin.last m))

noncomputable def cval (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : K :=
  algebraMap RR K (Z (Fin.last m) (Fin.last m)) -
    ∑ i, ∑ j, algebraMap RR K (Z (Fin.last m) (Fin.castSucc i)) * (toK K (blk Z))⁻¹ i j *
      algebraMap RR K (Z (Fin.castSucc j) (Fin.last m))

noncomputable def alpha (Z : Matrix (Fin (m+1)) (Fin (m+1)) RR) : coker (blk Z) →ₗ[RR] KmodR RR K :=
  descend K (blk Z) (fun j => algebraMap RR K (Z (Fin.last m) (Fin.castSucc j)))

end

def CornerInv : Prop :=
  ∀ (K : Type) [CommRing K] (m : ℕ) (Z : Matrix (Fin (m+1)) (Fin (m+1)) K),
    IsUnit Z.det → IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det →
    (Z (Fin.last m) (Fin.last m) -
      ∑ i, ∑ j, Z (Fin.last m) (Fin.castSucc i) *
        (Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ i j * Z (Fin.castSucc j) (Fin.last m)) *
      Z⁻¹ (Fin.last m) (Fin.last m) = 1

def KappaMod : Prop :=
  ∀ (RR K : Type) [CommRing RR] [CommRing K] [Algebra RR K] (m₁ m₂ : ℕ)
    (Z₁ : Matrix (Fin (m₁+1)) (Fin (m₁+1)) RR) (Z₂ : Matrix (Fin (m₂+1)) (Fin (m₂+1)) RR),
    IsUnit (toK K Z₁).det → IsUnit (toK K Z₂).det →
    ∀ θ : coker Z₁ ≃ₗ[RR] coker Z₂, θ (ebar Z₁) = ebar Z₂ →
      (lam K Z₂).comp θ.toLinearMap = lam K Z₁ →
      kappa K Z₁ - kappa K Z₂ ∈ Set.range (algebraMap RR K)

def IsoTransfer : Prop :=
  ∀ (RR K : Type) [CommRing RR] [CommRing K] [Algebra RR K], Function.Injective (algebraMap RR K) →
    ∀ (m₁ m₂ : ℕ)
    (Z₁ : Matrix (Fin (m₁+1)) (Fin (m₁+1)) RR) (Z₂ : Matrix (Fin (m₂+1)) (Fin (m₂+1)) RR),
    IsUnit (toK K Z₁).det → IsUnit (toK K Z₂).det →
    IsUnit (toK K (blk Z₁)).det → IsUnit (toK K (blk Z₂)).det →
    kappa K Z₁ = kappa K Z₂ →
    Nonempty ({θ : coker Z₁ ≃ₗ[RR] coker Z₂ //
        θ (ebar Z₁) = ebar Z₂ ∧ (lam K Z₂).comp θ.toLinearMap = lam K Z₁} ≃
      {θ : coker (blk Z₁) ≃ₗ[RR] coker (blk Z₂) //
        θ (bbar Z₁) = bbar Z₂ ∧ (alpha K Z₂).comp θ.toLinearMap = alpha K Z₁})

def EssSurj : Prop :=
  ∀ (RR K : Type) [CommRing RR] [CommRing K] [Algebra RR K], Function.Injective (algebraMap RR K) →
    ∀ (m : ℕ) (Z' : Matrix (Fin m) (Fin m) RR) (b : Fin m → RR) (α : coker Z' →ₗ[RR] KmodR RR K)
      (c : K), IsUnit (toK K Z').det → IsUnit c →
      (Submodule.Quotient.mk c : KmodR RR K) = -α (Submodule.Quotient.mk b) →
      ∃ Z : Matrix (Fin (m+1)) (Fin (m+1)) RR, IsUnit (toK K Z).det ∧ blk Z = Z' ∧
        (fun i => Z (Fin.castSucc i) (Fin.last m)) = b ∧
        (∀ v, alpha K Z (Submodule.Quotient.mk v) = α (Submodule.Quotient.mk v)) ∧
        cval K Z = c

def CharSumIso : Prop :=
  ∀ (RR Q : Type) [CommRing RR] [AddCommGroup Q] [Module RR Q] (ψ : AddChar Q ℂ)
    (C₁ C₂ : Type) [AddCommGroup C₁] [Module RR C₁] [Fintype C₁]
    [AddCommGroup C₂] [Module RR C₂] [Fintype C₂]
    [Fintype (C₁ ≃ₗ[RR] C₂)] [Fintype (C₁ →ₗ[RR] Q)]
    (e₁ : C₁) (e₂ : C₂) (la₁ : C₁ →ₗ[RR] Q) (la₂ : C₂ →ₗ[RR] Q),
    Function.Bijective (fun α : C₁ →ₗ[RR] Q => ψ.compAddMonoidHom α.toAddMonoidHom) →
    ∑ θ : C₁ ≃ₗ[RR] C₂, ∑ α : C₁ →ₗ[RR] Q, ∑ β : C₁,
        ψ (α (e₁ - θ.symm e₂) + (la₁ - la₂ ∘ₗ θ.toLinearMap) β)
      = ((Fintype.card C₁ : ℂ) ^ 2) *
        (Nat.card {θ : C₁ ≃ₗ[RR] C₂ // θ e₁ = e₂ ∧ la₂ ∘ₗ θ.toLinearMap = la₁} : ℂ)

end Formalism.NuclearRankWeightBounds.C
end

-- bundled from Formalism.LogSumExpBounds.StatementD
section
namespace Formalism.NuclearRankWeightBounds.D

open Finset

noncomputable def lead {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) : ℂ :=
  if hi : i ≤ N then (A.submatrix (Fin.castLE hi) (Fin.castLE hi)).det else 1

noncomputable def hs {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, ‖Y a b‖ ^ 2)

def q0 {N : ℕ} (ep : Fin N → Bool) : ℕ :=
  min (univ.filter fun a => ep a = true).card (univ.filter fun a => ep a = false).card

def Decay : Prop :=
  ∀ (N : ℕ) (s : ℕ → ℝ) (ep : Fin N → Bool) (h : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ),
    (∀ i, 0 ≤ s i) → Y.IsHermitian → (∀ a b, ep a = ep b → Y a b = 0) →
    (∀ a b : Fin N, b < a → ep a ≠ ep b → h ≤ ∑ i ∈ Ico (b.val + 1) (a.val + 1), s i) →
    ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re ^ (-(s i))
      ≤ Real.exp (-(h * min (hs Y ^ 2) (hs Y / Real.sqrt (2 * (q0 ep : ℝ)))) / 8)

end Formalism.NuclearRankWeightBounds.D
end

-- bundled from Formalism.LogSumExpBounds.StatementE
section
namespace Formalism.NuclearRankWeightBounds.E

section
variable {K : Type*} [CommRing K] [StarRing K] {V : Type*} [AddCommGroup V] [Module K V]

def IsHerm (h : V →ₗ[K] V →ₗ⋆[K] K) : Prop := ∀ v w, h w v = star (h v w)

def tau (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V) (v : V) : V :=
  v + h v x • u - h v u • x
end

def TauIsom : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V),
    IsHerm h → h x x = 0 → h u u = 0 → h u x = 0 →
    ∀ v w, h (tau h x u v) (tau h x u w) = h v w

def TauInv : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x u : V),
    IsHerm h → h x x = 0 → h u u = 0 → h u x = 0 →
    ∀ v, tau h x (-u) (tau h x u v) = v ∧ tau h x u (tau h x (-u) v) = v

def TauComp : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (x x' u : V),
    IsHerm h → h x x = 0 → h x' x' = 0 → h u u = 0 → h u x = 0 → h u x' = 0 →
    ∀ v, tau h x u (tau h x' (-u) v)
      = v + h v (x - x') • u - h v u • (x - x') + (h v u * h x' x) • u

def TauLattice : Prop :=
  ∀ (K : Type) [CommRing K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) (O : Subring K) (abelian₂ : AddSubgroup V) (x x' u : V),
    IsHerm h → (∀ a ∈ O, star a ∈ O) →
    (∀ a ∈ O, ∀ v ∈ abelian₂, a • v ∈ abelian₂) →
    (∀ v ∈ abelian₂, ∀ w ∈ abelian₂, h v w ∈ O) →
    h x x = 0 → h x' x' = 0 → h u u = 0 → h u x = 0 → h u x' = 0 →
    x - x' ∈ abelian₂ → u ∈ abelian₂ → h x' x ∈ O →
    tau h x u '' (abelian₂ : Set V) = tau h x' u '' (abelian₂ : Set V)

def mass {C : Type*} [Fintype C] (wt : C → C → ℝ) (c : C) : ℝ := ∑ c', wt c c'

noncomputable def sway {C : Type*} [Fintype C] (om : C → ℂ) (wt : C → C → ℝ) (c : C) : ℂ :=
  (om c)⁻¹ * ∑ c', (wt c c' : ℂ) * om c'

def PhaseSum : Prop :=
  ∀ (C : Type) [Fintype C] (om : C → ℂ) (wt : C → C → ℝ) (C1 : Finset C) (m0 ep : ℝ),
    (∀ c, ‖om c‖ = 1) → (∀ c c', wt c c' = wt c' c) → (∀ c c', 0 ≤ wt c c') → 0 < m0 →
    (∀ c, c ∉ C1 → sway om wt c = (mass wt c : ℂ)) →
    (∀ c ∈ C1, |mass wt c - m0| ≤ ep * m0 ∧ ‖sway om wt c‖ ≤ ep * m0) →
    ‖∑ c ∈ C1, om c‖ ≤ 2 * ep * (C1.card : ℝ)

end Formalism.NuclearRankWeightBounds.E
end

-- bundled from Formalism.LogSumExpBounds.StatementZ
section
namespace Formalism.NuclearRankWeightBounds.Z

open Finset

def LatSum : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ) (S : Finset (Fin f → ℂ)),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ o ∈ S, o ∈ La ∧ o ≠ 0) →
      ∑ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2)

def ZLift : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ)
      (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (Z : Finset (Fin f → ℂ)) (U : (Fin f → ℂ) → H) (B : ℝ),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ z ∈ Z, ∀ v, z v ≠ 0) →
      (∀ z ∈ Z, ∀ z' ∈ Z, (fun v => (z v)⁻¹ - (z' v)⁻¹) ∉ La → inner ℂ (U z) (U z') = 0) →
      (∀ A : Finset (Fin f),
        ∑ z ∈ Z, (∏ v ∈ A, (2 / (x v * ‖z v‖)) ^ (2 * K)) * ‖U z‖ ^ 2 ≤ B) →
      ∑ z ∈ Z, ∑ z' ∈ Z.erase z, ‖inner ℂ (U z) (U z')‖
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * B

end Formalism.NuclearRankWeightBounds.Z
end

