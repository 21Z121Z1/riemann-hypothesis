import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F : Type} [Field F] [Algebra ℂ F] {V V' : Type} [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V]
  [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V']

def Lat (A : Subalgebra ℂ F) (M : Submodule ℂ V) : Prop :=
  (∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) ∧ ∃ (n : ℕ) (v : Fin n → V) (φ : Fin n → V →ₗ[F] F), (∀ k, v k ∈ M) ∧ (∀ k, ∀ m ∈ M, φ k m ∈ A) ∧
    ∀ m ∈ M, m = ∑ k, φ k m • v k

variable (F V V') in

def actF : F ⊗[ℂ] F →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] V') :=
  (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V) (Algebra.lsmul ℂ ℂ V'))

variable (V') in

def ctrF (ψ : V →ₗ[F] F) : V ⊗[ℂ] V' →ₗ[ℂ] V' := TensorProduct.lift ((Algebra.lsmul ℂ ℂ V').toLinearMap ∘ₗ ψ.restrictScalars ℂ)

def f0 {d : ℕ} (x : Fin (d + 1) → Fˣ) (j : Fin (d + 1)) (l : Fin d) : F ⊗[ℂ] F :=
  ((x (j.succAbove l) : F) / x j) ⊗ₜ 1 - 1 ⊗ₜ ((x (j.succAbove l) : F) / x j)

def R0 {d : ℕ} (x : Fin (d + 1) → Fˣ) (I J : Finset (Fin (d + 1))) : Subalgebra ℂ (F ⊗[ℂ] F) :=
  (Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val).range

def omG {d : ℕ} (x : Fin (d + 1) → Fˣ) (i : Fin (d + 1)) : F := ∏ l, ((x l : F) / x i)

variable (V') in

def resP (ρ : F →ₗ[ℂ] ℂ) : F ⊗[ℂ] V' →ₗ[ℂ] V' := TensorProduct.lift ((LinearMap.lsmul ℂ V') ∘ₗ ρ)

end

section
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

structure ZF {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) : Prop where
  adm : (sysZ K x 0).admitted n z
  diag : ∀ l, Algebra.TensorProduct.lmul' ℂ (z l) = 0
  gen : ∀ i, Algebra.adjoin ℂ {b : K | b ∈ rB ℂ K (xv x) {i} ∧ ∃ l N, n l = (N, N) ∧
    z l = (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)} = rB ℂ K (xv x) {i}

def IsDiag (τ : DR ℂ K →ₗ[K] K) (a : ℕ) (c : Finset (Two d ⊕ₗ Mi d) → DR ℂ K ⊗[ℂ] DR ℂ K) : Prop :=
  ∀ i j L, L.card = d → Acts (F := F) K τ a (c (uni (uni {i} {j}) L)) ((-1) ^ d * kap K x L)

abbrev pr (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) : (Finset (Fin (d + 1)) → DR ℂ K) →ₗ[ℂ] (Finset (Fin (d + 1)) → DR ℂ K) →ₗ[ℂ] ℂ :=
  cupPair ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))

end

def GoodZ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a : ℕ, (sysZ K x a).Good ∧ (sysP K x a).Good ∧
  ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t → omB ℂ K (rB ℂ K (xv x) s) a ≤ omB ℂ K (rB ℂ K (xv x) t) a

def LatOm : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a : ℕ) (I : Finset (Fin (d + 1))), I.Nonempty →
  Lat (rA ℂ (xv x) I) (omB ℂ K (rB ℂ K (xv x) I) a) ∧
  ∀ w ∈ ⋀[K]^a Ω[K⁄ℂ], w ∈ Submodule.span F (omB ℂ K (rB ℂ K (xv x) I) a : Set (DR ℂ K))

def LatA : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I : Finset (Fin (d + 1))), ∀ i ∈ I, Lat (rA ℂ (xv x) I) (omA ℂ (xv x) I) ∧
  (∀ y : F, y ∈ omA ℂ (xv x) I ↔ y / omG x i ∈ rA ℂ (xv x) I) ∧
  ∀ j, ∀ y ∈ omA ℂ (xv x) (insert j I), ∃ N : ℕ, ((x j : F) / x i) ^ N * y ∈ omA ℂ (xv x) I

def Reg0 : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I J : Finset (Fin (d + 1))), ∀ j ∈ I, j ∈ J →
  Reg (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (f0 x j)

def Ker0 : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I J : Finset (Fin (d + 1))), ∀ j ∈ I, j ∈ J → ∀ m ∈ R0 x I J,
  Algebra.TensorProduct.lmul' ℂ m = 0 →
  m ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (Set.range (f0 x j))

def RegLat : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (V V' : Type) [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V]
  [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V'] (I J : Finset (Fin (d + 1))) (M : Submodule ℂ V)
  (M' : Submodule ℂ V'), Lat (rA ℂ (xv x) I) M → Lat (rA ℂ (xv x) J) M' → ∀ j ∈ I, j ∈ J →
  Reg (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') (f0 x j) ∧
  ∀ m ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M', (∀ ψ : V →ₗ[F] F, ctrF V' ψ m = 0) →
    m ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') (Set.range (f0 x j))

def DualForm : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ ψ : DR ℂ K →ₗ[F] F,
  (∃ w ∈ ⋀[K]^a Ω[K⁄ℂ], ∀ y ∈ ⋀[K]^(d - a) Ω[K⁄ℂ], ψ y = Algebra.trace F K (τ (y * w))) ∧
  ∃ w ∈ ⋀[K]^(d - a) Ω[K⁄ℂ], ∀ y ∈ ⋀[K]^a Ω[K⁄ℂ], ψ y = Algebra.trace F K (τ (w * y))

def ColZ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ I J, ∀ i ∈ I, ∀ j ∈ J,
  KE (kos (sysZ K x a).act ((sysZ K x a).M I J) fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l)) d ∧
  ∀ m ∈ (sysZ K x a).M I J, Acts (F := F) K τ a m 0 →
    m ∈ sm (sysZ K x a).act ((sysZ K x a).M I J) (Set.range fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l))

def ColP : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a I J, ∀ i ∈ I, ∀ j ∈ J,
  KE (kos (sysP K x a).act ((sysP K x a).M I J) fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l)) d ∧
  ∀ m ∈ (sysP K x a).M I J, mulP F K m = 0 →
    m ∈ sm (sysP K x a).act ((sysP K x a).M I J) (Set.range fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l))

def ActsLin : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a : ℕ,
  (∀ m m' c c', Acts (F := F) K τ a m c → Acts (F := F) K τ a m' c' →
    Acts (F := F) K τ a (m + m') (c + c') ∧ Acts (F := F) K τ a (m - m') (c - c')) ∧
  (∀ m c s, Acts (F := F) K τ a m c → Acts (F := F) K τ a (actZ K s m) (Algebra.TensorProduct.lmul' ℂ s * c)) ∧
  (∀ i j M m, m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) → Acts (F := F) K τ a m 0) ∧
  (∀ (u : (K ⊗[ℂ] K)ˣ) M m i j, m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) →
    Acts (F := F) K τ a (actZ K u m) 0) ∧
  (∀ (s : F ⊗[ℂ] K) m, mulP F K ((sysP K x a).act s m) =
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K) s • mulP F K m) ∧
  ∀ (s : F ⊗[ℂ] K) m w, muP F K τ (actZ K (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K) s) m) w =
    (sysP K x a).act s (muP F K τ m w)

def IdJ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ j, ∃ m ∈ (sysZ K x a).M {j} {j}, Acts (F := F) K τ a m (algebraMap F K (omG x j))

def IdIJ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ i j, ∃ m ∈ (sysZ K x a).M {i} {j}, Acts (F := F) K τ a m (algebraMap F K (omG x i))

def ZFam : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∃ (m : ℕ) (n : Fin m → ℕ × ℕ) (z : Fin m → K ⊗[ℂ] K), ZF K x n z

def KapInd : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  (π : S →ₐ[ℂ] K), (∀ i, π (T.X i) = algebraMap F K (x i)) → (∀ i, π (T.Y i) = algebraMap F K (x i)) →
  ∀ i L, L.card = d → π (detC T.rowMu (uni {i} L)) = kap K x L

def ZCol : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∀ i j, ∃ c ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) {i} {j}).Z d,
    ∀ L : Finset (Mi d), L.card = d → Acts (F := F) K τ a (c (uni L ∅)) ((-1) ^ d * kap K x L)

def ZEx : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∃ c ∈ ((sysZ K x a).cx (app n11 n) (app (sysZ K x a).mu z)).Z (d + 2), IsDiag K x τ a (resK inlE c)

def PLift : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a I J, I.Nonempty → J.Nonempty → ∀ w ∈ omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a,
  ∃ y ∈ ((sysP K x a).colCx n11 (sysP K x a).mu I J).Z d, ∀ L, L.card = d → mulP F K (y L) = kap K x L • w

def PCmp : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a p : ℕ), ∀ c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2),
  (∀ b L, d < L.card → c (uni b L) = 0) →
  ∀ γ ∈ (acx (mixF fun I J : Finset (Fin (d + 1)) => omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) fun _ => 1).B (p + 2),
  (∀ b L, L.card = d → mulP F K (c (uni b L)) = kap K x L • γ b) → c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).B (d + p + 2)

def PTheta : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a p : ℕ), ∀ β ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  ∃ c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2), (∀ b L, d < L.card → c (uni b L) = 0) ∧
    (∀ b L, L.card = d → mulP F K (c (uni b L)) = kap K x L • ((-1 : ℤ) ^ ((p + 1) * d)) • edge2 β b) ∧
    ∀ J, c (uni (uni Finset.univ J) ∅) = 1 ⊗ₜ β J

def PCup : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (a p : ℕ), a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  rcup (muP F K τ) p c α ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2) ∧
    (∀ b L, d < L.card → rcup (muP F K τ) p c α (uni b L) = 0) ∧
    ∀ b L, L.card = d → mulP F K (rcup (muP F K τ) p c α (uni b L)) = kap K x L • ((-1 : ℤ) ^ (p * (d + 1) + d)) • edge1 α b

def PInt : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), ∀ t ∈ (sysP K x a).mix.B (d + p + 2),
  (fun J => resP (DR ℂ K) ρ (t (uni Finset.univ J))) ∈ (omCx (rB ℂ K (xv x)) a).B p

def RCupTop : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), a ≤ d → ∀ t ∈ (sysZ K x a).mix.B (d + 2), ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  (fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (t (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) ∈
    (omCx (rB ℂ K (xv x)) a).B p

def ZAct : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  α - (fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) ∈
    (omCx (rB ℂ K (xv x)) a).B p

def ZId : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ a : ℕ, a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∃ (m : ℕ) (p : Fin m → ℕ) (e f : Fin m → Finset (Fin (d + 1)) → DR ℂ K),
    (∀ k, p k ≤ d ∧ e k ∈ (omCx (rB ℂ K (xv x)) (d - a)).Z (d - p k) ∧ f k ∈ (omCx (rB ℂ K (xv x)) a).Z (p k)) ∧
    top c - ∑ k, join (TensorProduct.mk ℂ _ _) (e k) (f k) ∈ (sysZ K x a).mix.B (d + 2) ∧
    ∀ q : ℕ, ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z q,
      α - ∑ k ∈ Finset.univ.filter (fun k => p k = q), pr K τ ρ (e k) α • f k ∈ (omCx (rB ℂ K (xv x)) a).B q

def PrB : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a q : ℕ), a ≤ d → q ≤ d → ∀ e ∈ (omCx (rB ℂ K (xv x)) (d - a)).Z (d - q),
  ∀ y ∈ (omCx (rB ℂ K (xv x)) a).B q, pr K τ ρ e y = 0

end UpperTheory.Gal.productCup_of_system

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FiltrationBoundaryCriterionOfWdBasic
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]

private lemma wd_apply' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

private lemma wd_congr' (w : σ → Module.End ℂ E) (c c' : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, w i = 0 ∨ c (t.erase i) = c' (t.erase i)) : wd w c t = wd w c' t := by
  rw [wd_apply', wd_apply']
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases h i hi with h | h
  · simp [h]
  · rw [h]

private lemma card_erase_mem' {Q t : Finset σ} {i : σ} (hi : i ∈ t) (hQ : i ∈ Q) :
    (((t.erase i) ∩ Q).card : ℤ) = ((t ∩ Q).card : ℤ) - 1 := by
  have h1 : (t.erase i) ∩ Q = (t ∩ Q).erase i := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have h2 : i ∈ t ∩ Q := Finset.mem_inter.2 ⟨hi, hQ⟩
  have h3 : 0 < (t ∩ Q).card := Finset.card_pos.2 ⟨i, h2⟩
  rw [h1, Finset.card_erase_of_mem h2]
  omega

private lemma card_erase_not' {Q t : Finset σ} {i : σ} (hQ : i ∉ Q) :
    (t.erase i) ∩ Q = t ∩ Q := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩
    exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨fun e => hQ (e ▸ h'), h⟩, h'⟩

private lemma levQ' (w : σ → Module.End ℂ E) (Q : Finset σ) {m m' : ℤ} (hm : m' = m + 1)
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m') (wd (wOn Q w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m') := ht
  have h0 : wd (wOn Q w) y t = wd (wOn Q w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · right
      refine hy _ ?_
      have h1 := card_erase_mem' hi hiQ
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      omega
    · left
      simp [wOn, hiQ]
  rw [h0, map_zero]
  rfl

private lemma levC' (w : σ → Module.End ℂ E) (Q : Finset σ) {m : ℤ}
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m) (wd (wOn Qᶜ w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m) := ht
  have h0 : wd (wOn Qᶜ w) y t = wd (wOn Qᶜ w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · left
      simp [wOn, hiQ]
    · right
      refine hy _ ?_
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      rw [card_erase_not' hiQ]
      exact ht'
  rw [h0, map_zero]
  rfl

private lemma wd_split' (hW : WdBasic) (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (Q : Finset σ) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = wd (wOn Q w) c t + wd (wOn Qᶜ w) c t := by
  have h := (hW σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w)
  have h2 : wOn Q w + wOn Qᶜ w = w := by
    funext i
    by_cases hi : i ∈ Q <;> simp [wOn, hi]
  rw [h2] at h
  rw [h]
  rfl

private lemma sub_cocycle' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    (hcx : (acx A w).IsCx) {n : ℤ} {c y : Finset σ → E} (hc : c ∈ (acx A w).Z n)
    (hy : y ∈ (acx A w).C (n - 1)) : c - wd w y ∈ (acx A w).Z n := by
  obtain ⟨h1, h2⟩ := hcx _ y hy
  rw [sub_add_cancel] at h1
  obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hc1 h1, ?_⟩
  have h3 : wd w c = 0 := hc2
  have h4 : wd w (wd w y) = 0 := h2
  show wd w (c - wd w y) = 0
  rw [map_sub, h3, h4, sub_zero]

private lemma of_sub' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E} {n : ℤ}
    {c y : Finset σ → E} (hy : y ∈ (acx A w).C (n - 1)) (h : c - wd w y ∈ (acx A w).B n) :
    c ∈ (acx A w).B n := by
  have h2 : wd w y ∈ (acx A w).B n := Submodule.mem_map_of_mem hy
  simpa using add_mem h h2

private lemma low' (hW : WdBasic) {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {Q : Finset σ} {d : ℤ} (hok : WOk A w) (hq : QEx A w Q d) :
    ∀ k : ℕ, k ≤ d.toNat → ∀ (n : ℤ) (c : Finset σ → E), c ∈ (acx A w).Z n →
      Lev Q (· ≤ (k : ℤ) - 1) c → c ∈ (acx A w).B n := by
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  intro k
  induction k with
  | zero =>
    intro _ n c hc hl
    have h0 : c = 0 := by
      funext s
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((0 : ℕ) : ℤ) - 1)
      omega
    rw [h0]
    exact zero_mem _
  | succ k ih =>
    intro hk n c hc hl
    have hkd : (k : ℤ) < d := by omega
    have hl' : ∀ s, (k : ℤ) < ((s ∩ Q).card : ℤ) → c s = 0 := by
      intro s hs
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - 1)
      push_cast
      omega
    obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
    have hc3 : wd w c = 0 := hc2
    let cm : Finset σ → E := fun s => if ((s ∩ Q).card : ℤ) = k then c s else 0
    have hcm : cm ∈ (acx A w).C n := by
      refine Submodule.mem_pi.2 fun s hs => ?_
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · have : cm s = c s := if_pos h
        rw [this]
        exact Submodule.mem_pi.1 hc1 s hs
      · have : cm s = 0 := if_neg h
        rw [this]
        exact zero_mem _
    have hcl : Lev Q (· = (k : ℤ)) cm := fun s hs => if_neg hs
    have hkill : wd (wOn Q w) cm = 0 := by
      funext t
      by_cases ht : ((t ∩ Q).card : ℤ) = k + 1
      · have e1 : wd (wOn Q w) cm t = wd (wOn Q w) c t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · right
            have h1 := card_erase_mem' hi hiQ
            exact if_pos (by omega)
          · left
            simp [wOn, hiQ]
        have e2 : wd (wOn Qᶜ w) c t = wd (wOn Qᶜ w) 0 t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · left
            simp [wOn, hiQ]
          · right
            refine hl' _ ?_
            rw [card_erase_not' hiQ]
            omega
        have e3 := wd_split' hW A w Q c t
        rw [hc3, e2, map_zero] at e3
        rw [e1]
        simpa using e3.symm
      · exact levQ' w Q rfl hcl t ht
    obtain ⟨y, hy, hyl, hyd⟩ := hq n k hkd cm hcm hcl hkill
    refine of_sub' hy (ih (by omega) n _ (sub_cocycle' hcx hc hy) ?_)
    intro s hs
    have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (k : ℤ) - 1) := hs
    have e1 := wd_split' hW A w Q y s
    have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
      show ¬ (((s ∩ Q).card : ℤ) = (k : ℤ) - 1)
      omega)
    have e3 : wd (wOn Q w) y s = cm s := congrFun hyd s
    have e4 : cm s = c s := by
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · exact if_pos h
      · have : cm s = 0 := if_neg h
        rw [this, hl' s (by omega)]
    show c s - wd w y s = 0
    rw [e1, e2, e3, e4, add_zero, sub_self]

end

theorem UpperTheory.Gal.productCup_of_system.filtrationBoundaryCriterion_of_wdBasic :
    WdBasic → FiltrationBoundaryCriterion := by
  intro hW σ E _ _ _ _ A w Q d n hok hq c hc hl hy0
  obtain ⟨y, hy, hyl, hyd⟩ := hy0
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  have hl' : ∀ s, d < ((s ∩ Q).card : ℤ) → c s = 0 := by
    intro s hs
    refine hl s ?_
    show ¬ (((s ∩ Q).card : ℤ) ≤ d)
    omega
  refine of_sub' hy (low' hW hok hq d.toNat le_rfl n _ (sub_cocycle' hcx hc hy) ?_)
  intro s hs
  have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (d.toNat : ℤ) - 1) := hs
  have hge : d ≤ ((s ∩ Q).card : ℤ) := by omega
  have e1 := wd_split' hW A w Q y s
  have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
    show ¬ (((s ∩ Q).card : ℤ) = d - 1)
    omega)
  show c s - wd w y s = 0
  rw [e1, e2, add_zero]
  by_cases h : ((s ∩ Q).card : ℤ) = d
  · rw [hyd s h, sub_self]
  · have e3 : wd (wOn Q w) y s = 0 := levQ' w Q (by ring) hyl s h
    rw [e3, hl' s (by omega), sub_self]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KSubOf
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.kSub_of :
    FiltrationBoundaryCriterion → SubQEx → KSub := by
  intro gl sub S E _ _ _ _ act κ _ _ R M r hst hr
  refine ⟨?_, ?_⟩
  · intro d e hK m hm c hc
    have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
      refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm]
    have hQ := sub S E act κ M r d e hK
    have hcard : (img e).card = d := by simp [img]
    refine gl κ E (fun _ => M) (fun l => act (r l)) (img e) d m hW hQ c hc ?_
      ⟨0, Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
    · intro s hs
      exfalso
      apply hs
      have h1 : (s ∩ img e).card ≤ (img e).card := Finset.card_le_card Finset.inter_subset_right
      rw [hcard] at h1
      exact_mod_cast h1
    · intro s hs
      have h1 : (s ∩ img e).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
      have hne : (s.card : ℤ) ≠ m := by
        have : ((s ∩ img e).card : ℤ) ≤ s.card := by exact_mod_cast h1
        omega
      have h2 : c s ∈ (if (s.card : ℤ) = m then M else ⊥ : Submodule ℂ E) := hc.1 s (Set.mem_univ s)
      rw [if_neg hne, Submodule.mem_bot] at h2
      rw [h2, map_zero]
      rfl
  · intro n c hc L
    obtain ⟨y, hy, rfl⟩ := hc
    have hval : ∀ i ∈ L, y (L.erase i) ∈ M := by
      intro i _
      have h2 : y (L.erase i) ∈ (if ((L.erase i).card : ℤ) = n - 1 then M else ⊥ : Submodule ℂ E) :=
        hy (L.erase i) (Set.mem_univ _)
      split_ifs at h2 with h
      · exact h2
      · rw [Submodule.mem_bot] at h2
        rw [h2]
        exact M.zero_mem
    have hexp : (kos act M r).D y L
        = ∑ i ∈ L, (GlobalTheory.cubeSign L i : ℤ) • act (r i) (y (L.erase i)) := by
      simp [kos, acx, wd]
    rw [hexp]
    refine Submodule.sum_mem _ fun i hi => ?_
    refine Submodule.smul_of_tower_mem _ _ ?_
    have h3 : act (r i) (y (L.erase i)) ∈ M.map (act (r i)) := ⟨_, hval i hi, rfl⟩
    exact (le_iSup₂_of_le (r i) (Set.mem_range_self i) le_rfl : M.map (act (r i)) ≤ sm act M (Set.range r)) h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrLin
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.trLin_of :
    TrLin := by
  intro V _ _ ι _ φ v hv
  have hfin : FiniteDimensional ℂ V := by
    refine Module.Finite.of_surjective (Fintype.linearCombination ℂ v) ?_
    intro y
    exact ⟨fun k => φ k y, by rw [Fintype.linearCombination_apply]; exact (hv y).symm⟩
  refine ⟨hfin, fun u => ?_⟩
  have hu : u = ∑ k, dualTensorHom ℂ V V (φ k ⊗ₜ u (v k)) := by
    ext y
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply]
    conv_lhs => rw [hv y]
    rw [map_sum]
    simp [map_smul]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.trace_eq_contract_apply]
  simp
end

