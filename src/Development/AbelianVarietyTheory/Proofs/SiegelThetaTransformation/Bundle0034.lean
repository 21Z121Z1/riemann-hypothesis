import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0031
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierExpansionHolomorphicTube
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolution
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetHermitianFormAtFramePeriodCoordsOfUnitFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_hermitianFormAtFramePeriodCoords_of_unitFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, IsUnitFr X x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ z w, hermForm Hm z w = hx X bas idx x z w) → Hm.det = ((∏ τ : X.Ψ, X.c τ ^ r : ℝ) : ℂ) := by
  first | exact @GlobalTheory.Dict.det_hx_of_isUnitFr | exact GlobalTheory.Dict.det_hx_of_isUnitFr | (intros; apply GlobalTheory.Dict.det_hx_of_isUnitFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmField_generator_at_primes_dividing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  first | exact @GlobalTheory.Dict.exists_generator_at_primes_dividing | exact GlobalTheory.Dict.exists_generator_at_primes_dividing | (intros; apply GlobalTheory.Dict.exists_generator_at_primes_dividing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEventuallyCongr
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory

namespace GlobalTheory.IsoTower

theorem finite_quot_nsmul (M : Type) [AddCommGroup M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    Finite (M ⧸ (nsmulAddMonoidHom n : M →+ M).range) := by
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨y, rfl⟩

theorem exists_eventually_congr {L M : Type} [AddCommGroup L] [AddCommGroup M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (U : Ultrafilter ℕ) (g : ℕ → L →+ M) {n : ℕ} (hn : 0 < n)
    (P : ℕ → Prop) (hP : ∀ᶠ j in U, P j) :
    ∃ i, P i ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e := by
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 (inferInstance : Module.Finite ℤ L))
  have := hSf.to_subtype
  have := finite_quot_nsmul M hn
  let φ : ℕ → S → M ⧸ (nsmulAddMonoidHom n : M →+ M).range := fun j s => QuotientAddGroup.mk (g j s)
  obtain ⟨v, hv⟩ := Ultrafilter.eq_pure_of_finite (U.map φ)
  have hv' : ∀ᶠ j in U, φ j = v := by
    have : {v} ∈ U.map φ := by
      rw [hv]
      exact rfl
    exact this
  obtain ⟨i, hi, hPi⟩ := (hv'.and hP).exists
  refine ⟨i, hPi, hv'.mono fun j hj a => ?_⟩
  have h := AddMonoidHom.eq_of_eqOn_dense hS
    (f := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g i))
    (g := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g j))
    (fun s hs => congrFun (hi.trans hj.symm) ⟨s, hs⟩)
  obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 (DFunLike.congr_fun h a)
  refine ⟨e, ?_⟩
  have he' : n • e = -g i a + g j a := he
  rw [he']
  abel

theorem exists_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D D' : Datum H), (∀ n : ℕ, 0 < n → ∃ f : D.La →ₗ[𝓞 E] D'.La, ((∀ a, (∃ e, f a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f a + n • e) ∧ ∀ a a', (n : ℤ) ∣ D'.EF (f a) (f a') - D.EF a a') → ∃ f : ℕ → D.La →ₗ[𝓞 E] D'.La, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') := by
  intro E _ _ _ H D D' hex
  have := D.fin
  have := D'.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) D'.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have hc : ∀ {r : ℕ}, 0 < r → ∀ {a c : D.La}, r • a = r • c → a = c := fun {r} hr a c h => by
    have h' : (r : ℤ) • a = (r : ℤ) • c := by simpa only [natCast_zsmul] using h
    exact smul_right_injective D.La (by exact_mod_cast hr.ne' : (r : ℤ) ≠ 0) h'
  choose g hg using fun j : ℕ => hex _ j.factorial_pos
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj => Nat.dvd_factorial hn hj)
  have hs : ∀ n : ℕ, ∃ i : ℕ, 0 < n → (n ∣ i.factorial ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨i, hi⟩ := exists_eventually_congr U (fun j => (g j).toAddMonoidHom) hn _ (hU n hn)
      exact ⟨i, fun _ => hi⟩
  choose s hs using hs
  refine ⟨fun n => g (s n), fun n m hn hm a => ?_, fun n hn => ?_, fun n hn a a' => ?_⟩
  · obtain ⟨j, h1, h2⟩ := ((hs _ (Nat.mul_pos hn hm)).2.and (hs n hn).2).exists
    obtain ⟨e1, h1⟩ := h1 a
    obtain ⟨e2, h2⟩ := h2 a
    refine ⟨e2 - m • e1, ?_⟩
    show g (s (n * m)) a = g (s n) a + _
    rw [smul_sub, ← mul_smul, ← add_sub_assoc, ← h2, h1, add_sub_cancel_right]
  · obtain ⟨r, hr⟩ := (hs n hn).1
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left (hr ▸ (s n).factorial_pos)
    obtain ⟨⟨h1, h2⟩, -⟩ := hg (s n)
    rw [hr] at h1 h2
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨e, he⟩
      have he' : g (s n) a = n • e := he
      obtain ⟨b, hb⟩ := (h1 (r • a)).1 ⟨e, by rw [map_nsmul, he', mul_comm, mul_smul]⟩
      exact ⟨b, hc hr0 (by rw [hb, mul_comm, mul_smul])⟩
    · rintro ⟨e, rfl⟩
      exact ⟨_, map_nsmul _ _ _⟩
    · obtain ⟨a, e, h⟩ := h2 a'
      exact ⟨a, r • e, by rw [h, mul_smul]⟩
  · exact (Int.natCast_dvd_natCast.2 (hs n hn).1).trans ((hg (s n)).2 a a')

end GlobalTheory.IsoTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLatticesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_extend_to_all_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (mu : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ ga ∈ Δ, IsUn X ga) → (∀ ga ∈ Δ, ∀ L' ∈ 𝓛, mapL ga L' ∈ 𝓛 ∧ ‖mu ga L'‖ = 1) → (∀ ga ∈ Δ, ∀ ga' ∈ Δ, ∀ L' ∈ 𝓛, mu (ga * ga') L' = mu ga (mapL ga' L') * mu ga' L') → (∀ k, L k ∈ 𝓛) → (∀ k k', ∀ ga ∈ Δ, mapL ga (L k) = L k' → k = k') → (∀ k, ∀ ga ∈ Δ, mapL ga (L k) = L k → mu ga (L k) = 1) → (∀ k, IsStabForm X Δ (L k) la (Q k)) → ∃ F : Lt E r → Frame X.Ψ r → ℂ, IsForm X Δ 𝓛 mu la F ∧ ∀ k, ∀ x ∈ X.dom, F (L k) x = Q k x := by
  first | exact @GlobalTheory.Dict.exists_form_extend | exact GlobalTheory.Dict.exists_form_extend | (intros; apply GlobalTheory.Dict.exists_form_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierEntire
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.LevelTheta

theorem exists_fourier_entire {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z, ∀ m : ι → ℤ, f (z + fun i => (m i : ℂ)) = f z) :
    ∃ a : (ι → ℤ) → ℂ,
      (∀ z, HasSum (fun ν : ι → ℤ => a ν * cexp (2 * π * I * ∑ i, (ν i : ℂ) * z i)) (f z)) ∧
      ∀ (w : ι → ℂ) (ν : ι → ℤ), a ν = ∫ x in Set.Icc (0 : ι → ℝ) 1,
        f ((fun i => (x i : ℂ)) + w) *
          cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * ((x i : ℂ) + w i))) := by
  obtain ⟨a, h1, h2⟩ := exists_fourier_expansion_tube ι Set.univ f isOpen_univ convex_univ
    hf.differentiableOn (fun z _ m => hper z m)
  refine ⟨a, fun z => h1 z trivial, fun w ν => ?_⟩
  have key := Koecher.setIntegral_unitCube_tube (U := Set.univ)
    (f := fun z => f z * cexp (-(2 * π * I * ∑ i, (ν i : ℂ) * z i))) isOpen_univ
    isPreconnected_univ (fun _ _ _ => trivial)
    (hf.differentiableOn.mul (Differentiable.differentiableOn (by fun_prop))) (fun z hz i => ?_)
    (Set.mem_univ (fun i => I * (((0 : ι → ℝ) i : ℝ) : ℂ))) (Set.mem_univ w)
  · rw [h2 0 trivial ν]
    refine Eq.trans ?_ key
    exact (setIntegral_congr_set (μ := volume) (Measure.univ_pi_Ico_ae_eq_Icc
      (f := (0 : ι → ℝ)) (g := 1)))
  · have e0 : (Pi.single i 1 : ι → ℂ) = fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℂ) := by
      funext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij]
    have e : ∑ j, (ν j : ℂ) * (z + (Pi.single i 1 : ι → ℂ)) j
        = ∑ j, (ν j : ℂ) * z j + ν i := by
      simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
    rw [e, e0, hper z, mul_add, neg_add, Complex.exp_add]
    have : cexp (-(2 * π * I * (ν i : ℂ))) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I (-ν i)]
      congr 1
      push_cast
      ring
    rw [this, mul_one]

theorem quad_add {ι : Type} [Fintype ι] {τ : Matrix ι ι ℂ} (h : τ.IsSymm) (u v : ι → ℂ) :
    (u + v) ⬝ᵥ τ *ᵥ (u + v) = u ⬝ᵥ τ *ᵥ u + 2 * (u ⬝ᵥ τ *ᵥ v) + v ⬝ᵥ τ *ᵥ v := by
  have : v ⬝ᵥ τ *ᵥ u = u ⬝ᵥ τ *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, h.eq, dotProduct_comm]
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, this]
  ring

theorem exists_thS_eq : ∀ (n g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ Siegel (Fin g) → ∀ (N : ℕ), 0 < N → ∀ Θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ Θ → (∀ (a : Fin n → Fin g → ℤ) ζ, Θ (fun k i => ζ k i + N * a k i) = Θ ζ) → (∀ (b : Fin n → Fin g → ℤ) ζ, cexp (π * I * ∑ k, ((fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ)) + 2 * ((fun i => (N * b k i : ℂ)) ⬝ᵥ ζ k))) * Θ (fun k => ζ k + τ *ᵥ fun i => (N * b k i : ℂ)) = Θ ζ) → ∃ φ : TF n g, IsSB φ ∧ ∀ ζ, thS φ τ ζ = Θ ζ := by
  intro n g τ hτ N hN Θ hΘ hp hq
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨a, hs, ha⟩ := exists_fourier_entire (ι := Fin n × Fin g)
    (fun z => Θ fun k i => N * z (k, i)) (hΘ.comp (by fun_prop)) (fun z m => by
      rw [← hp (fun k i => m (k, i)) fun k i => N * z (k, i)]
      congr 1
      funext k i
      simp [mul_add])
  let e : (Fin n × Fin g → ℤ) → Matrix (Fin n) (Fin g) ℚ :=
    fun ν => Matrix.of fun k i => (ν (k, i) : ℚ) / N
  have he : Function.Injective e := by
    intro m m' hmn
    funext ⟨k, i⟩
    have h1 : (m (k, i) : ℚ) / N = (m' (k, i) : ℚ) / N := congrFun (congrFun hmn k) i
    exact_mod_cast (div_left_inj' hNq).1 h1
  let Q : Matrix (Fin n) (Fin g) ℚ → ℂ := fun x => ∑ k, qv (x k) ⬝ᵥ τ *ᵥ qv (x k)
  let φ : TF n g := fun x => Function.extend e a 0 x * cexp (-(π * I * Q x))
  have hφe : ∀ ν, φ (e ν) = a ν * cexp (-(π * I * Q (e ν))) := fun ν => by
    simp only [φ, he.extend_apply]
  have hφ0 : ∀ x, x ∉ Set.range e → φ x = 0 := fun x hx => by
    simp only [φ]
    rw [Function.extend_apply' _ _ _ hx]
    simp
  have hshift : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ),
      e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ)) =
        e (fun p => ν p + N ^ 2 * b p.1 p.2) := by
    intro ν b
    ext k i
    simp only [e, of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  have hlaw : ∀ (ν : Fin n × Fin g → ℤ) (b : Fin n → Fin g → ℤ),
      φ (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) = φ (e ν) := by
    intro ν b
    have hQ : Q (e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) =
        Q (e ν) + 2 * ∑ k, ∑ i, (ν (k, i) : ℂ) * (τ *ᵥ fun j => (b k j : ℂ)) i +
          ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ (fun i => (N * b k i : ℂ)) := by
      simp only [Q, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : qv ((e ν + (N : ℚ) • (Matrix.of fun k i => (b k i : ℚ))) k) =
          qv (e ν k) + fun i => (N * b k i : ℂ) := by
        funext i
        simp [qv]
      rw [h1, quad_add hτ.1]
      congr 2
      have h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ) := by
        funext i; simp
      rw [h2, mulVec_smul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [qv, e, of_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
    have h := hφe (fun p => ν p + N ^ 2 * b p.1 p.2)
    rw [← hshift] at h
    rw [h, hφe, hQ, ha 0, ha (fun p => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) ν,
      ← integral_mul_const, ← integral_mul_const]
    congr 1
    funext x
    rw [← hq b]
    have h3 : (fun k => (fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) k +
        τ *ᵥ fun i => (N * b k i : ℂ)) =
        fun k i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) +
          fun p : Fin n × Fin g => (τ *ᵥ fun j => (b p.1 j : ℂ)) p.2) (k, i) := by
      funext k i
      have h2 : (fun i => (N * b k i : ℂ)) = (N : ℂ) • fun i => (b k i : ℂ) := by
        funext i; simp
      rw [h2, mulVec_smul]
      simp [mul_add]
    rw [h3, mul_comm (cexp _) (Θ _)]
    simp only [mul_assoc (Θ _), ← Complex.exp_add]
    congr 2
    have h4 : ∑ k, (fun i => (N * b k i : ℂ)) ⬝ᵥ
        (fun i => (N : ℂ) * ((fun p : Fin n × Fin g => (x p : ℂ)) + 0) (k, i)) =
        ∑ k, ∑ i, (N : ℂ) ^ 2 * b k i * x (k, i) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Pi.zero_apply]
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h4]
    simp only [Fintype.sum_prod_type, Pi.zero_apply, add_zero, mul_add, add_mul,
      Finset.sum_add_distrib, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    ring
  refine ⟨φ, ⟨N, hN, fun x hx => ?_, fun x y hy => ?_⟩, fun ζ => ?_⟩
  · obtain ⟨ν, rfl⟩ : x ∈ Set.range e := by
      by_contra h
      exact hx (hφ0 x h)
    intro k i
    have : ((N : ℚ) • e ν) k i = algebraMap ℤ ℚ (ν (k, i)) := by
      simp only [e, of_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
      field_simp
    rw [this]
    exact isIntegral_algebraMap
  · have : ∀ k i, ∃ m : ℤ, (m : ℚ) = y k i := fun k i => by
      simpa using IsIntegrallyClosed.isIntegral_iff.1 (hy k i)
    choose b hb using this
    obtain rfl : y = Matrix.of fun k i => (b k i : ℚ) := by
      ext k i
      simp [hb]
    by_cases hx : x ∈ Set.range e
    · obtain ⟨ν, rfl⟩ := hx
      exact hlaw ν b
    · rw [hφ0 x hx]
      refine hφ0 _ ?_
      rintro ⟨ν, hν⟩
      refine hx ⟨fun p => ν p + N ^ 2 * (-b) p.1 p.2, ?_⟩
      rw [← hshift, hν]
      ext k i
      simp
  · have h1 := hs fun p => ζ p.1 p.2 / N
    have h2 : (fun k i => (N : ℂ) * (ζ k i / N)) = ζ := by
      funext k i
      field_simp
    simp only [h2] at h1
    refine HasSum.tsum_eq ?_
    refine (he.hasSum_iff fun x hx => by rw [hφ0 x hx, zero_mul]).1 ?_
    convert h1 using 2 with ν
    simp only [Function.comp_apply]
    rw [hφe, mul_assoc, ← Complex.exp_add]
    congr 2
    have h3 : ∑ k, qv (e ν k) ⬝ᵥ ζ k = ∑ p : Fin n × Fin g, (ν p : ℂ) * (ζ p.1 p.2 / N) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [qv, e, of_apply]
      push_cast
      ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, h3]
    simp only [Q]
    ring

end GlobalTheory.Ker.LevelTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowHighest_harmonic_polyDeriv_unitaryAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ P ∈ Harm.rowHighest ℂ k k', ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ F : (Fin n → Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv P (letterDir X hr idx) (fun z => F (hAct X idx h z)) 0 = I2.polyDeriv P' (letterDir X hr idx) F 0 := by
  first | exact @GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct | exact GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct | (intros; apply GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.GenLatCmp

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_range_iff (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_std (v : Fin n → E) : v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (v i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun i => mem_range_iff (v i)

theorem std_eq : Formalism.L2.Pj.stdLat E n = stdL E n := by
  apply le_antisymm
  · intro v hv
    rw [mem_std] at hv
    have : v = ∑ i, (⟨v i, hv i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_std]
    intro j
    by_cases h : j = i
    · subst h; simpa using isIntegral_one
    · simpa [Pi.single_apply, h] using isIntegral_zero

theorem span_smul_le (k : ℕ) (A B : Lt E n) :
    Ideal.span {(k : 𝓞 E)} • A ≤ B ↔ ∀ v ∈ A, (k : E) • v ∈ B := by
  have e : ∀ v : Fin n → E, (k : 𝓞 E) • v = (k : E) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    rw [← e]
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [e]; exact h v hv

theorem natCast_smul_mem (k : ℕ) {A : Lt E n} {v : Fin n → E} (hv : v ∈ A) : (k : E) • v ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]; exact A.toAddSubgroup.nsmul_mem hv k

theorem fg_of_smul_le {Λ : Lt E n} {s : ℕ} (hs : 0 < s) (h : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n) :
    Λ.FG := by
  have h0 : (stdL E n).FG := Submodule.fg_span (Set.finite_range _)
  have h1 := h0.map ((LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E))
  refine h1.of_le fun v hv => ⟨(s : E) • v, h v hv, ?_⟩
  have : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  simp [smul_smul, this]

variable [IsCMField E]

theorem herm_one_eq (x y : Fin n → E) :
    herm 1 x y = cc (∑ j, IsCMField.complexConj E (x j) * y j) := by
  simp [herm, cc, Matrix.one_apply]

theorem unimod_iff (Λ : Lt E n) : (⟨Λ⟩ : GenLat E n).Unimod ↔
    ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y) := by
  refine forall_congr' fun x => iff_congr Iff.rfl (forall₂_congr fun y _ => ?_)
  rw [mem_range_iff, herm_one_eq]
  refine ⟨Base.isIntegral_cc, fun h => ?_⟩
  simpa [cc] using Base.isIntegral_cc h

theorem smul_mem_std {Λ : Lt E n} (hU : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) {s : ℕ}
    (h : ∀ v ∈ stdL E n, (s : E) • v ∈ Λ) : ∀ v ∈ Λ, (s : E) • v ∈ stdL E n := by
  intro v hv
  rw [← std_eq, mem_std]
  intro i
  have := (hU v).1 hv _ (h (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩))
  convert this using 1
  simp [herm, cc, Matrix.one_apply, Pi.single_apply, mul_comm, apply_ite (IsCMField.complexConj E)]

theorem genLat_vset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : Lt E n), (∀ bad M : ℕ, 0 < bad → Odd M → Λ ∈ Vset E n (2 * bad * M) → (⟨Λ⟩ : GenLat E n).Unimod ∧ (⟨Λ⟩ : GenLat E n).TrivAt bad ∧ (⟨Λ⟩ : GenLat E n).TrivAt M ∧ ∃ N, NOK Λ N M) ∧ (∀ M N : ℕ, 0 < M → (⟨Λ⟩ : GenLat E n).Unimod → (⟨Λ⟩ : GenLat E n).TrivAt M → NOK Λ N M → Λ ∈ Vset E n M) ∧ (∀ M M' : ℕ, M ∣ M' → Λ ∈ Vset E n M' → Λ ∈ Vset E n M) ∧ stdLat E n = stdL E n := by
  intro E _ _ _ n Λ
  refine ⟨?_, ?_, ?_, std_eq⟩
  · rintro bad M - hM ⟨-, hU, s, -, hs, h1, h2⟩
    have t : ∀ m, s.Coprime m → (⟨Λ⟩ : GenLat E n).TrivAt m := fun m hm =>
      ⟨s, hm, by rw [std_eq, span_smul_le]; exact h1, by rw [std_eq, span_smul_le]; exact h2⟩
    refine ⟨(unimod_iff Λ).2 hU, t _ hs.coprime_mul_right_right.coprime_mul_left_right,
      t _ hs.coprime_mul_left_right, s * M, ?_, Dvd.intro_left _ rfl, ?_⟩
    · exact (Nat.coprime_two_right.1 hs.coprime_mul_right_right.coprime_mul_right_right).mul hM
    · rw [span_smul_le]
      intro v hv
      refine ⟨?_, natCast_smul_mem _ hv⟩
      rw [std_eq] at hv
      rw [mul_comm, Nat.cast_mul, mul_smul]
      exact natCast_smul_mem M (h2 v hv)
  · rintro M N - hU ⟨k, hk, h1, h2⟩ ⟨hN, -, h3⟩
    rw [unimod_iff] at hU
    rw [std_eq, span_smul_le] at h1 h2 h3
    have h4 : ∀ v ∈ stdL E n, (N : E) • v ∈ Λ := fun v hv => (h3 v hv).1
    have h5 := smul_mem_std hU h4
    refine ⟨fg_of_smul_le hN.pos h5, hU, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      exact ⟨N, hN.pos, hk ▸ Nat.coprime_one_right N, h5, h4⟩
    · exact ⟨k, hk0, hk, h1, h2⟩
  · rintro M M' hM ⟨a, b, s, hs, hc, h⟩
    exact ⟨a, b, s, hs, hc.coprime_dvd_right hM, h⟩

end GlobalTheory.Dict.GenLatCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolyDerivKillsDoubledHeatSolutionStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_polyDeriv_kills_doubled_heat_solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (n m : ℕ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), r ≤ n → InvFam P → ∀ D : CM X.Ψ r r → CM X.Ψ n r → CM X.Ψ n r → ℂ, IsHeat X.Ψ D → (∀ Z ∈ Hn X.Ψ r, D Z 0 0 = 0) → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, biDeriv X hr idx P (fun z₁ w => kZero X idx x₁ x₂ z₁ w * D (dblZ X x₁ x₂) (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w)) = 0 := by
  first | exact @GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | exact GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero | (intros; apply GlobalTheory.SW.biDeriv_kZero_mul_heat_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticeDiagonalUnitaryPatchedStandardStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_diagonal_unitary_patched_standard : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n r M : ℕ) (𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ 𝔍 → IsCoprime 𝔍 (conjI 𝔍) → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ccT h * h = 1 ∧ ∀ Λ ∈ Vset E n M, ∃ Λ' ∈ Vset E n M, ∃ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' ∧ (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' ∧ (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' := by
  first | exact @GlobalTheory.Dict.Patch.main | exact GlobalTheory.Dict.Patch.main | (intros; apply GlobalTheory.Dict.Patch.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSuccStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_formula_degree_succ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → SWAt Ψ n (N + 1) := by
  first | exact @GlobalTheory.SW.swAt_succ | exact GlobalTheory.SW.swAt_succ | (intros; apply GlobalTheory.SW.swAt_succ <;> assumption)
end

