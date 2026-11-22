import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreIsotropicPointsInjectiveRoots
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0042
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FourierTranslatesVacuumRootsLevelPoints
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0038
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibrePrincipalBundleSignEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootsLevelPointsSameVacuumTranslates
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreIsotropicPointsInjectiveRootsStatement
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
theorem _root_.GlobalTheory.T.analyticFibre_isotropic_points_injective_roots : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (n N : ℕ) (Λ : Lt E n), 0 < N → (∀ (Jx : Type) (u : Jx → Matrix (Fin n) (Fin r) E), (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') → (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') → (∀ i, InZh Xo (⟨Λ⟩ : GenLat E n) N (fun b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ GeoInj Xo y.x (fun i b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → l.M ∣ N → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ q b, A.ex (pv X idx x ((N : E)⁻¹ • Y q b)) ^ N = levPt Xo y.x (levRep (q b)) ∧ (∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (A.ex (pv X idx x ((N : E)⁻¹ • Y q b)))) ∧ ∃ u ∈ L, (N ^ 2 : ℕ) • ((N : E)⁻¹ • Y q b) = (2 : ℕ) • u := by
  first | exact @GlobalTheory.Dict.points_inZh_geoInj_roots | exact GlobalTheory.Dict.points_inZh_geoInj_roots | (intros; apply GlobalTheory.Dict.points_inZh_geoInj_roots <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_ex_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo s ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
    (x0 : Sp ℂ ⟶ Xo.X) (h : x0 = F.u i P) :
    ∃ ex : (Fin g → ℂ) → (ptO Xo x0 ⟶ Xo.univ.t.G),
      (∀ z, (ex z).left = (F.ex i P z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧
      (∀ z, ex z = 1 ↔ z ∈ P.range) ∧
      (∀ (a : 𝓞 E) z, ex (fun j => ty j (a : E) * z j) = ex z ≫ Xo.univ.t.act.act a) ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo x0 a = ex ((l.M : ℂ)⁻¹ • P (F.t i a)) := by
  subst h
  refine ⟨F.ex i P, fun _ => rfl, F.ex_add i P hP, F.ex_onto i P hP, F.ex_ker i P hP, F.ex_lin i P hP, ?_⟩
  intro a ha
  exact F.ex_eta i P hP a ha

set_option maxHeartbeats 1000000 in

theorem uw_anFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp) (bas : (Fin W.g ⊕ Fin W.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin W.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (W.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx W.e x.1 (U.X k).Λ (unC U k x), A.Marked (W.mark k) ∧ ∃ θ, A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k bas idx hS hpv hrow x hxu
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Pm, hPm, hPer, hux, hder, hfr⟩ := W.pt k x
  obtain ⟨Hm, χl, fr, θ, Fd, hHm, -, hIm, hfrhol, hfrne, hfrg, hfr0, hfrper, hread, hFd, hmean⟩ := hfr hxu
  obtain ⟨ex, hexl, hadd, honto, hker, hlin, hmark⟩ :=
    exists_ex_transport W.F (W.ik k) Pm hPer (U.un k x).x hux

  have hPv : ∀ a, Pm a = pv (U.X k) idx x.1 (W.φ k a : Fin r → E) := fun a => funext fun j => by
    rw [hPm, hpv]
  have hφs : ∀ u ∈ (U.X k).Λ, ∃ a, (W.φ k a : Fin r → E) = u := fun u hu =>
    ⟨(W.φ k).symm ⟨u, hu⟩, by simp⟩
  have hembφ : ∀ a, W.emb k a = (W.φ k a : Fin r → E) := fun a => rfl
  have hrange : ∀ z, z ∈ Pm.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := by
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, SetLike.coe_mem _, hPv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hPv a⟩
  obtain ⟨-, -, -, -, -, hspan, hEF⟩ := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr W k
  have hrng : Set.range (W.emb k) = ((U.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [hembφ]
      exact SetLike.coe_mem _
    · intro hv
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hembφ a⟩
  obtain ⟨-, -, -, -, hsm, -, hL, -⟩ := hx_laws E r (U.X k) W.g bas idx 0 hS ⟨0, rfl⟩ x.1 x.2

  have him : ∀ u ∈ (U.X k).Λ, ∀ v ∈ (U.X k).Λ,
      (hermForm Hm (pv (U.X k) idx x.1 u) (pv (U.X k) idx x.1 v)).im = (EF (U.X k) u v : ℝ) := by
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hφs u hu
    obtain ⟨b, rfl⟩ := hφs v hv
    rw [← hPv, ← hPv, hIm, ← hembφ, ← hembφ, ← hEF a b]
    norm_cast
  have hH : ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w :=
    (hL (U.X k).Λ (hrng ▸ hspan)).2 Hm hHm him
  have hfun : (fun z => (ex z).left) = fun z => (W.F.ex (W.ik k) Pm z).left := funext hexl
  refine ⟨{ ex := ex
            ex_add := hadd
            ex_onto := honto
            ex_ker := fun z => (hker z).trans (hrange z)
            ex_lin := fun a z => by
              have e : (fun j => rowType (U.X k) (idx j) (a : E) * z j) =
                  fun j => relab c σ (W.e j).1 (a : E) * z j := funext fun j => by rw [hrow]
              rw [e]
              exact hlin a z
            hol := by
              intro V f
              simp only [Set.sep_univ, hexl]
              exact ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol W.F (W.ik k) Pm hPer V f
            der := fun ℓ => by
              rw [hfun]
              exact hder ℓ.1 ℓ.2
            fr := fr
            fr_hol := fun j => by simp only [hexl]; exact hfrhol j
            fr_ne := fun j z => by simp only [hexl]; exact hfrne j z
            fr_g := fun j j' z => by simp only [hexl]; exact hfrg j j' z
            fr_0 := fun j => by simp only [hexl]; exact hfr0 j
            χ := fun v => if ‖χl (pv (U.X k) idx x.1 v)‖ = 1 then χl (pv (U.X k) idx x.1 v) else 1
            χ_norm := fun v _ => by
              try dsimp only
              split_ifs with h
              · exact h
              · simp
            fr_per := fun v hv j z hz => by
              obtain ⟨a, rfl⟩ := hφs v hv
              obtain ⟨hn, hp⟩ := hfrper a j z
              try dsimp only
              rw [← hPv, if_pos hn, ← hH, ← hH]
              exact hp (by simpa only [hexl] using hz) }, ?_, θ, ?_, ?_⟩
  · intro a ha
    have hM : pv (U.X k) idx x.1 (((l.M : E)⁻¹) • W.mark k a) = (l.M : ℂ)⁻¹ • Pm (W.F.t (W.ik k) a) := by
      funext j
      simp only [hsm, hrow, hPv, Pi.smul_apply, smul_eq_mul, map_inv₀, map_natCast]
      rfl
    exact (hmark a ha).trans (congrArg ex hM.symm)
  · intro j z pt h1 h2 h3
    rw [zpow_one]
    exact hread j z pt (h1.trans (hexl z)) h2 (by simpa only [hexl] using h3)
  · refine ⟨Pm.range, Fd, hrange, hFd, ?_⟩
    simpa only [hH] using hmean

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibreStatement
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
theorem _root_.GlobalTheory.T.exists_analyticFrame_of_analyticFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∃ Φ : AnVal.AnPt y g (fun j => rowType X (idx j)) e, (∀ z, Φ.e z = A.ex z) ∧ Φ.fr = A.fr ∧ (∀ z, z ∈ Φ.lat ↔ ∃ v ∈ L, z = pv X idx x v) ∧ (∀ z w, hermForm Φ.Hm z w = hx X bas idx x z w) ∧ (∀ v ∈ L, Φ.χ (pv X idx x v) = A.χ v) ∧ (∀ (k : ℤ) F θ, Φ.toAnFr.Rd k F θ ↔ A.Reads k F θ) ∧ ∀ (k : ℕ) a θ, AnVal.fock Φ.Hm (k : ℤ) a θ = Dict.fock X bas idx x k a θ := by
  first | exact @GlobalTheory.Dict.AnFib.exists_anPt | exact GlobalTheory.Dict.AnFib.exists_anPt | (intros; apply GlobalTheory.Dict.AnFib.exists_anPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSumStatement
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
theorem _root_.GlobalTheory.T.exists_even_reps_tensorLattice_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ N : ℕ, Odd N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∃ u : Fin ((⟨Λ⟩ : GenLat E n).zCard N r) → Matrix (Fin n) (Fin r) E, (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') ∧ (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') ∧ 0 < (⟨Λ⟩ : GenLat E n).zCard N r ∧ 0 < (⟨Λ⟩ : GenLat E n).mIdx N r ∧ ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∑ i, heisG X bas (u i) v = (((⟨Λ⟩ : GenLat E n).zCard N r : ℕ) : ℂ) • projA X bas w (tens Λ L) v := by
  first | exact @GlobalTheory.Dict.ZLat.exists_reps_sum | exact GlobalTheory.Dict.ZLat.exists_reps_sum | (intros; apply GlobalTheory.Dict.ZLat.exists_reps_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticDoubledHermitianCoordinatesStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_doubled_hermitian_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ), IsSympl X bas → ∃ F : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ] ((QI E r → ℚ) × (QI E r → ℚ)), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) ∧ ∀ (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) (y₁ y₂ : Fin r → E), y₁ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)) → y₂ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr))) → (∀ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = ∑ j, (F u).2 (a, j) • Module.finBasis ℚ E j) ∧ ∀ a j, (F u).1 (a, j) = Algebra.trace ℚ E ((Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc (Module.finBasis ℚ E j)) := by
  first | exact @GlobalTheory.SW.DblLat.dbl_lat | exact GlobalTheory.SW.DblLat.dbl_lat | (intros; apply GlobalTheory.SW.DblLat.dbl_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsThetaEqOfTranslationInvariantMultiple
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Onto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem exponent_eq {x : Frame X.Ψ r}
    (h : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) (z p : Fin n → Fin g → ℂ) :
    -(π * I * ((∑ k, hx X bas idx x (z k) (p k)).im : ℝ)) +
      -(π / 2 * ∑ k, hx X bas idx x (z k + p k) (z k + p k)) =
    -(π / 2 * ∑ k, hx X bas idx x (z k) (z k)) +
      -(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • p k) (p k)) := by
  have h1 (k) : hx X bas idx x (z k + p k) (z k + p k) = hx X bas idx x (z k) (z k) +
      hx X bas idx x (z k) (p k) + conj (hx X bas idx x (z k) (p k)) +
      hx X bas idx x (p k) (p k) := by
    rw [← h]
    simp only [hx, mulVec_add, star_add, add_dotProduct, dotProduct_add]
    ring
  have h2 (k) : hx X bas idx x (z k + (1 / 2 : ℂ) • p k) (p k) = hx X bas idx x (z k) (p k) +
      1 / 2 * hx X bas idx x (p k) (p k) := by
    simp only [hx, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
  simp only [h1, h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum]
  have h3 := Complex.sub_conj (∑ k, hx X bas idx x (z k) (p k))
  push_cast at h3
  linear_combination (π / 2 : ℂ) * h3

theorem exists_canonical (h τ W : Matrix (Fin g) (Fin g) ℂ) (hu : IsUnit h.det)
    (hτ : τ ∈ Siegel (Fin g)) (hW : W.IsSymm) (hY : W * τ.map (fun z => (z.im : ℂ)) = 1)
    {D : ℂ} (hD : D ≠ 0) {N : ℕ} (hN : 0 < N) {θ : (Fin n → Fin g → ℂ) → ℂ}
    (hθ : Differentiable ℂ θ)
    (key : ∀ a b : Fin n → Fin g → ℤ, ∃ p : Fin n → Fin g → ℂ,
      (∀ k, h *ᵥ p k = (fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ)) ∧
      ∀ z : Fin n → Fin g → ℂ, cexp (-(π * ∑ k, (h *ᵥ (z k + (1 / 2 : ℂ) • p k)) ⬝ᵥ W *ᵥ
        star (h *ᵥ p k))) * θ (fun k => z k + p k) = θ z) :
    ∃ φ : TF n g, IsSB φ ∧ ∀ z : Fin n → Fin g → ℂ,
      D * cexp (π / 2 * ∑ k, (h *ᵥ z k) ⬝ᵥ W *ᵥ (h *ᵥ z k)) * thS φ τ (fun k => h *ᵥ z k) = θ z := by
  obtain ⟨c, hcd⟩ : ∃ c : (Fin n → Fin g → ℂ) → ℂ,
    c = fun ζ => cexp (π / 2 * ∑ k, ζ k ⬝ᵥ W *ᵥ ζ k) := ⟨_, rfl⟩
  obtain ⟨Θ, hΘd⟩ : ∃ Θ : (Fin n → Fin g → ℂ) → ℂ,
    Θ = fun ζ => (D * c ζ)⁻¹ * θ fun k => h⁻¹ *ᵥ ζ k := ⟨_, rfl⟩
  have hc (ζ) : D * c ζ ≠ 0 := mul_ne_zero hD (hcd ▸ Complex.exp_ne_zero _)
  have hΘ : Differentiable ℂ Θ := by
    rw [hΘd]
    refine Differentiable.mul (Differentiable.inv ?_ hc) (hθ.comp ?_)
    · simp only [hcd, mulVec, dotProduct]
      fun_prop
    · refine differentiable_pi.2 fun k => differentiable_pi.2 fun i => ?_
      simp only [mulVec, dotProduct]
      fun_prop
  have main : ∀ (a b : Fin n → Fin g → ℤ) (ζ : Fin n → Fin g → ℂ),
      cexp (π * I * ∑ k, ((fun i => (N * b k i : ℂ)) ⬝ᵥ τ *ᵥ
        (fun i => (N * b k i : ℂ)) + 2 * ((fun i => (N * b k i : ℂ)) ⬝ᵥ ζ k) +
        (fun i => (N * a k i : ℂ)) ⬝ᵥ (fun i => (N * b k i : ℂ)))) *
      Θ (fun k => ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))) = Θ ζ := by
    intro a b ζ
    have hq (m : Fin g → ℤ) : qv (fun i => (N * m i : ℚ)) = fun i => (N * m i : ℂ) := by
      funext i; simp [qv]
    obtain ⟨p, hp, h1⟩ := key a b
    have h1 := h1 fun k => h⁻¹ *ᵥ ζ k
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
      heis_exponent _ _ hτ.1 hW hY (fun i => (N * a k i : ℚ)) (fun i => (N * b k i : ℚ)) (ζ k)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at he
    have he' := congrArg cexp he
    rw [Complex.exp_add, Complex.exp_add] at he'
    simp only [hq] at he'
    have h2 (k) : h⁻¹ *ᵥ (ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))) =
        h⁻¹ *ᵥ ζ k + p k := by
      rw [← hp, mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    simp only [mulVec_add h, mulVec_smul h, hp, mulVec_mulVec, mul_nonsing_inv _ hu,
      one_mulVec] at h1
    simp only [hΘd, h2]
    rw [← h1, ← mul_assoc, ← mul_assoc]
    congr 1
    have h3 := hc ζ
    have h4 := hc fun k => ζ k + ((fun i => (N * a k i : ℂ)) + τ *ᵥ fun i => (N * b k i : ℂ))
    rw [mul_inv_eq_iff_eq_mul₀ h4, mul_assoc (_ * c ζ)⁻¹, eq_inv_mul_iff_mul_eq₀ h3]
    simp only [hcd]
    linear_combination D * he'
  obtain ⟨φ, hφ, h5⟩ := GlobalTheory.Ker.LevelTheta.exists_thS_eq n g τ hτ N hN Θ hΘ (fun a ζ => by
      have := main a 0 ζ
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, ← Pi.zero_def, mulVec_zero, add_zero,
        dotProduct_zero, zero_dotProduct, Finset.sum_const_zero, Complex.exp_zero, one_mul] at this
      exact this) (fun b ζ => by
      have := main 0 b ζ
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, ← Pi.zero_def, zero_add, add_zero,
        zero_dotProduct] at this
      exact this)
  refine ⟨φ, hφ, fun z => ?_⟩
  have h6 := hc fun k => h *ᵥ z k
  rw [h5]
  simp only [hΘd, hcd, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] at h6 ⊢
  exact mul_inv_cancel_left₀ h6 (θ z)

theorem exists_thA_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ (N : ℕ), 0 < N → ∀ θ : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ θ → (∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ v : WR X n, cexp (-(π * I * (EFR X v (N • embR X y) : ℝ))) * (gaussR X bas idx x (zR X idx x (v + N • embR X y)) * θ (zR X idx x (v + N • embR X y))) = gaussR X bas idx x (zR X idx x v) * θ (zR X idx x v)) → ∃ φ : TF n g, IsSB φ ∧ ∀ z, thA X bas idx φ x z = θ z := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x hx' N hN θ hθ hinv
  obtain ⟨⟨L, hL⟩, him, -⟩ := GlobalTheory.Ker.zR_laws E r X g q0 hr bas idx n hs hn x hx'
  have hconj := (GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hx').1
  have hu := isUnit_det_hMat idx hs hx'
  have key : ∀ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) → ∀ z : Fin n → Fin g → ℂ,
      cexp (-(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • (N • pv X idx x (y k)))
        (N • pv X idx x (y k)))) * θ (fun k => z k + N • pv X idx x (y k)) = θ z := by
    intro y hy z
    obtain ⟨v, rfl⟩ := L.surjective z
    have h1 : zR X idx x (N • embR X y) = fun k => N • pv X idx x (y k) := by
      rw [← hL, map_nsmul, hL]; rfl
    have h2 : zR X idx x (v + N • embR X y) = fun k => L v k + N • pv X idx x (y k) := by
      rw [← hL, map_add, hL (N • _), h1]; rfl
    have h3 := hinv y hy v
    rw [← him, h1, h2, ← hL v, gaussR, gaussR, ← mul_assoc, ← Complex.exp_add,
      exponent_eq idx hconj (L v) fun k => N • pv X idx x (y k), Complex.exp_add, mul_assoc] at h3
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h3
  refine exists_canonical (hMat X bas idx x) (tauMat X bas idx x) (imInv X bas idx x) hu
    ⟨tauMat_isSymm idx hs hx', tauMat_im_posDef idx hs hx'⟩ (imInv_isSymm idx hs hx')
    (imInv_mul_im idx hs hx') (pow_ne_zero (n / 2) hu.ne_zero) hN hθ fun a b =>
    ⟨fun k => N • pv X idx x (bas (Sum.elim (a k) (b k))), fun k => ?_,
      key (Matrix.of fun k => (bas (Sum.elim (a k) (b k)) : Fin r → E)) fun k => (bas _).2⟩
  beta_reduce
  rw [← Nat.cast_smul_eq_nsmul ℂ, mulVec_smul, pv, hMat_mulVec_per_bas idx hs hx', smul_add,
    ← mulVec_smul]
  rfl

end GlobalTheory.Ker.Onto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FourierTranslatesVacuumRootsLevelPointsStatement
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
theorem _root_.GlobalTheory.T.fourier_translates_vacuum_roots_levelPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)), SelfD X L → IsMark l L mk → ∀ Λ ∈ Vset E n l.M, ∀ N : ℕ, NOK Λ N l.M → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ p : TF n g, IsSB p → (∀ u ∈ tens Λ L, epsW X w u • heisG X bas u p = p) → ∀ u ∈ tens Λ ((Ideal.span {2} * conjI (Mfr l)) • L), ∑ᶠ q, cexp (-(2 * Real.pi * I * ((∑ b, EF X (u b) (Y q b) : ℚ) : ℂ))) • heisG X bas (Y q) p = ((Nat.card (Fin n → LevQ Dw l) : ℕ) : ℂ) • heisG X bas u (projA X bas w (tens Λ (idq (Mfr l) (conjI (Mfr l)) L)) p) := by
  first | exact @GlobalTheory.Dict.poisson_roots | exact GlobalTheory.Dict.poisson_roots | (intros; apply GlobalTheory.Dict.poisson_roots <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem thetaSignExpEF_inv_of_selfDual_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (L : Lt E r) (hL : SelfD X L) (w : 𝓞 E) (v : Fin r → E) (hv : v ∈ L) :
    (eps1 X (w : E) v)⁻¹ = eps1 X (w : E) v := by
  have hwv : (w : E) • v ∈ L := by
    have h := L.smul_mem w hv
    rwa [← algebraMap_smul E w v] at h
  obtain ⟨k, hk⟩ := (hL.2 v).1 hv ((w : E) • v) hwv
  unfold eps1
  rw [hk, ← Complex.exp_neg, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  push_cast
  ring

theorem isTheta1_of_reads_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ θ, A.Reads 1 y.s θ → IsTheta1 X bas idx (H.w0 : E) x L θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨-, hall⟩ := reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s
  obtain ⟨hd, hper⟩ := hall θ hθ
  refine ⟨hd, fun v hv => ?_⟩
  have h := hper v hv
  rw [analyticFibre_principalBundle_sign_eq E H Dw l Xo c r g X bas idx e x L y A hs hx hL v hv, pow_one,
    thetaSignExpEF_inv_of_selfDual_lattice X L hL H.w0 v hv] at h
  exact h

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLatticeStatement
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
theorem _root_.GlobalTheory.T.levelOne_theta_eq_smul_of_selfDual_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, ∀ θ θ' : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L θ → IsTheta1 X bas idx w x L θ' → θ' ≠ 0 → ∃ a : ℂ, θ = a • θ' := by
  first | exact @GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 | exact GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 | (intros; apply GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelTestFunction_finite_sum_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, IsSB (D.phi bas hn v₀ L Λ) ∧ IsVac X bas D.w (tens Λ (D.sh L)) (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ (∀ L' ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), s.card = Nat.card D.J ∧ (∀ y ∈ s, y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • (L ⊓ L')) ∧ ‖D.dat hn y‖ = 1 ∧ ∀ y' ∈ s, (∀ k, Cong X D.𝔪 (y k) (y' k)) → y = y') ∧ D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ D.phi bas hn v₀ L' Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L')))) ∧ ∀ γ ∈ D.grp, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → ∀ t : ℂ, ‖t‖ = 1 → wG X bas idx γ (v₀ L) = t • v₀ (mapL γ L) → wG X bas idx γ (D.phi bas hn v₀ L Λ) = (t * ((D.lam k : ℂˣ) : ℂ)⁻¹) • D.phi bas hn v₀ (mapL γ L) Λ := by
  first | exact @GlobalTheory.SW.RecSum.phi_sum_equivariant | exact GlobalTheory.SW.RecSum.phi_sum_equivariant | (intros; apply GlobalTheory.SW.RecSum.phi_sum_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensityStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∃ L : WR X n ≃L[ℝ] (Fin n → Fin g → ℂ), ∀ v, L v = zR X idx x v) ∧ (∀ v v' : WR X n, (∑ k, hx X bas idx x (zR X idx x v k) (zR X idx x v' k)).im = EFR X v v') ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, EFR X (embR X y) (embR X y') = ((∑ k, EF X (y k) (y' k) : ℚ) : ℝ)) ∧ DenseRange (embR X (n := n)) ∧ ∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = zR X idx x v := by
  first | exact @GlobalTheory.Ker.zR_laws | exact GlobalTheory.Ker.zR_laws | (intros; apply GlobalTheory.Ker.zR_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootsLevelPointsSameVacuumTranslatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_levelPoints_same_vacuum_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (n : ℕ), IsSympl X bas → Even n → ∀ L : Lt E r, SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n l.M, ∀ Λ' ∈ Vset E n l.M, Moves h Λ Λ' → ∀ N N' : ℕ, (⟨Λ⟩ : GenLat E n).LevOK N l.M → (⟨Λ'⟩ : GenLat E n).LevOK N' l.M → ∀ Y Y' : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → IsRoots l L mk N' Y' → (∃ e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l), ∀ q, LevMoves h q (e q)) ∧ ∀ q q', LevMoves h q q' → ∀ u : TF n g, IsVac X bas (H.w0 : E) (tens Λ' L) u → heisG X bas (Y' q') u = heisG X bas (h * Y q) u := by
  first | exact @GlobalTheory.Dict.RootsMove.roots_move | exact GlobalTheory.Dict.RootsMove.roots_move | (intros; apply GlobalTheory.Dict.RootsMove.roots_move <;> assumption)
end

