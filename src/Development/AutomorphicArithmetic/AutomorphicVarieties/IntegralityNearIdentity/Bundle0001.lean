import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0030
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0015
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0025
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0024
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0014
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0054
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0051

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear
section
namespace UpperTheory.V.Lib.Small

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

theorem eq_one_of_near {l : ℕ} [Fact l.Prime] {u : PadicAlgCl l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1)
    (h : ‖u - 1‖ < 1) : u = 1 :=
  _root_.UpperTheory.Reformulated.B.S7.eq_one_of_near hm hu h

theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin n) : (X * Y) a a = X a a * Y a a :=
  _root_.UpperTheory.Reformulated.B.S8.diag_mul X Y hX hY a

theorem fg_mod_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n

theorem conj_diagonal {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.charpoly = ∏ a, (Polynomial.X - Polynomial.C (d a))) :
    ∃ h : GL (Fin n) K, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * h = Matrix.diagonal d :=
  _root_.UpperTheory.Reformulated.B.MirabolicColumnBlock.conj_diagonal d hd M hM

end UpperTheory.V.Lib.Small
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.IsIntegralOfNormLe
section
namespace UpperTheory.V.Lib.Small

theorem mem_of_coeff {O σ ι : Type} [CommRing O] (I : Ideal (MvPowerSeries σ O)) (e : ι → σ) (s : Finset ι)
    (hs : ∀ i ∈ s, MvPowerSeries.X (e i) ∈ I) (f : MvPowerSeries σ O)
    (hf : ∀ n : σ →₀ ℕ, (∀ i ∈ s, n (e i) = 0) → MvPowerSeries.coeff n f = 0) : f ∈ I :=
  _root_.UpperTheory.Reformulated.B.S1.mem_of_coeff I e s hs f hf

theorem eigen_mem {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] (T : Module.End k M) (μ : ι → k)
    (hμ : Function.Injective μ) (Y : Submodule k M) (hY : ∀ y ∈ Y, T y ∈ Y) (s : Finset ι) (x : ι → M)
    (hx : ∀ j, T (x j) = μ j • x j) (h : ∑ j ∈ s, x j ∈ Y) : ∀ j ∈ s, x j ∈ Y :=
  _root_.UpperTheory.Reformulated.B.S2.eigen_mem T μ hμ Y hY s x hx h

theorem single_mem {k : Type} [Field k] {n : ℕ} (W : Submodule k (Fin n → k)) (d : Fin n → k) (hd : Function.Injective d)
    (hW : ∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) (v : Fin n → k) (hv : v ∈ W) (i : Fin n) (hi : v i ≠ 0) :
    (Pi.single i 1 : Fin n → k) ∈ W :=
  _root_.UpperTheory.Reformulated.B.S3.single_mem W d hd hW v hv i hi

theorem isIntegral_of_norm_le {l : ℕ} [Fact l.Prime] {z : PadicAlgCl l} (hz : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z :=
  _root_.UpperTheory.Reformulated.B.S4.isIntegral_of_norm_le hz

theorem norm_lt_one {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    (y : R →ₐ[ℤ_[l]] PadicAlgCl l) (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha

theorem norm_lt_one' {l : ℕ} [Fact l.Prime] {O R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing R] [IsLocalRing R] [Algebra O R]
    (y : R →ₐ[O] PadicAlgCl l) (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha

end UpperTheory.V.Lib.Small
end

