import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3182
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0034
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3306
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumber
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernLine

theorem eq_homogeneousComponent {κ R : Type} [AddCommGroup R] (f : MvPolynomial κ ℝ →+ R) (D : ℕ)
    (hf : ∀ d, d ≠ D → ∀ Q : MvPolynomial κ ℝ, Q.IsHomogeneous d → f Q = 0) (P : MvPolynomial κ ℝ) :
    f P = f (homogeneousComponent D P) := by
  conv_lhs => rw [← sum_homogeneousComponent P]
  rw [map_sum, Finset.sum_eq_single D]
  · intro b _ hb
    exact hf b hb _ (homogeneousComponent_isHomogeneous b P)
  · intro hD
    rw [Finset.mem_range, not_lt] at hD
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem interPoly_eq_zero {F : Type} [Field F] (Y : Var F) {κ : Type} (Δ : κ → Y.Dv) (d : ℕ) (hd : d ≠ Y.dim)
    (Q : MvPolynomial κ ℝ) (hQ : Q.IsHomogeneous d) : Y.interPoly Δ Q = 0 := by
  classical
  rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' : m.degree = d := by
    have := hQ (mem_support_iff.mp hm)
    first
    | (rw [Finsupp.degree_eq_weight_one]; exact this)
    | exact this
  rw [show monomial m (coeff m Q) = coeff m Q • basisMonomials κ ℝ m by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, Var.interPoly, Module.Basis.constr_basis, dif_neg, smul_zero]
  rintro ⟨s, hs⟩
  apply hd
  rw [← hm', ← hs, map_sum]
  simp

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hC F _ σ X κ _ Δ L r ψ hψ P
  have hR : X.interPoly Δ P = X.interPoly Δ (homogeneousComponent X.dim P) :=
    eq_homogeneousComponent (X.interPoly Δ).toAddMonoidHom X.dim (fun d hd Q hQ => interPoly_eq_zero X Δ d hd Q hQ) P
  have hL : ∀ x, dens (evalF (atlas X σ) (fun a => c1W (ψ a)) P x) =
      dens (evalF (atlas X σ) (fun a => c1W (ψ a)) (homogeneousComponent X.dim P) x) := by
    intro x
    let f : MvPolynomial κ ℝ →+ ℂ :=
      { toFun := fun Q => dens (evalF (atlas X σ) (fun a => c1W (ψ a)) Q x)
        map_zero' := by simp [evalF, LineForm.fld, dens]
        map_add' := fun Q Q' => by
          simp only [evalF, LineForm.fld, map_add, Subalgebra.coe_add]
          exact LineForm.TopInt.dens_add _ _ }
    refine eq_homogeneousComponent f X.dim (fun d hd Q hQ => ?_) P
    exact GlobalTheory.T.topDensity_hermitianForms_eq_zero_offDegree X.dim κ _ d Q hQ hd
  rw [hR, ← GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber hC F σ X κ Δ L r ψ hψ _ (homogeneousComponent_isHomogeneous _ P)]
  simp only [HolAtlas.integral, LineForm.TopInt.part_congr _ hL]

end GlobalTheory.ChernLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordina
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.OmegaCoord

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_eq_zero_of_mem_sq {g : MvPowerSeries (Fin d) k}
    (hg : g ∈ RingHom.ker (constantCoeff (R := k) (σ := Fin d)) ^ 2) (α : Fin d →₀ ℕ)
    (hα : α.degree < 2) : coeff α g = 0 := by
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdeg : q.1.degree + q.2.degree < 2 := by rw [← map_add, hq]; exact hα
    rw [RingHom.mem_ker] at ha hb
    rcases Nat.lt_or_ge q.1.degree 1 with h | h
    · have : q.1 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, ha, zero_mul]
    · have : q.2 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, hb, mul_zero]
  · rw [map_add, ha, hb, add_zero]

variable {A : Type} [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i))
  (haug : ∀ i, Coalgebra.counit (R := k) (x i) = 0)

include haug in

theorem exists_eq_sum (hsurj : Function.Surjective (evA k x hx)) (u : Cot k A) :
    ∃ w : Fin d → k, u = ∑ i, w i • dUnit k (x i) := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ u
  obtain ⟨f, rfl⟩ := hsurj a
  exact ⟨lin f, (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug f).2⟩

include haug in

theorem eq_zero_of_sum (hsurj : Function.Surjective (evA k x hx))
    (hker : ∀ f, evA k x hx f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < 2 → coeff α f = 0)
    (w : Fin d → k) (hw : ∑ i, w i • dUnit k (x i) = 0) : w = 0 := by
  set f : MvPowerSeries (Fin d) k := ∑ i, w i • X i with hf
  have hlin : lin f = w := by
    funext i
    simp [f, lin, coeff_X, Finsupp.single_eq_single_iff]
  have hcc : constantCoeff f = 0 := by simp [f]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug f
  have hd : dUnit k (evA k x hx f) = 0 := by rw [h2, hlin, hw]
  have hε : ∀ g, Bialgebra.counitAlgHom k A (evA k x hx g) = constantCoeff g := fun g =>
    (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug g).1
  rw [dUnit, AugCot.d_eq_zero_iff, hε, hcc, map_zero, sub_zero] at hd
  have hK : RingHom.ker (Bialgebra.counitAlgHom k A) =
      Ideal.map (evA k x hx) (RingHom.ker (constantCoeff (R := k) (σ := Fin d))) := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective _ hsurj]
    constructor
    · intro ha
      obtain ⟨g, rfl⟩ := hsurj a
      refine ⟨g, ?_, rfl⟩
      rw [RingHom.mem_ker] at ha ⊢
      rw [← hε]; exact ha
    · rintro ⟨g, hg, rfl⟩
      rw [RingHom.mem_ker] at hg ⊢
      rw [hε]; exact hg
  rw [hK, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hsurj] at hd
  obtain ⟨g, hg, hgf⟩ := hd
  have hfg : evA k x hx (f - g) = 0 := by rw [map_sub, hgf, sub_self]
  funext i
  have hdeg : (Finsupp.single i 1 : Fin d →₀ ℕ).degree < 2 := by simp
  have e1 := hker _ hfg (Finsupp.single i 1) hdeg
  rw [map_sub, coeff_eq_zero_of_mem_sq hg _ hdeg, sub_zero] at e1
  rw [← hlin]; exact e1

end GlobalTheory.OmegaCoord

namespace GlobalTheory.OmegaCoord

theorem omega_coord : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit k (c.x n i)) ∈ G.omegaSub) ∧
      ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i) := by
  intro p k _ d G c
  have hres : ∀ n (w : Fin d → k), cotMap (G.res n) (∑ i, w i • dUnit k (c.x (n + 1) i)) =
      ∑ i, w i • dUnit k (c.x n i) := by
    intro n w
    simp only [map_sum, map_smul, cotMap_d, c.res]
  refine ⟨fun w n => hres n w, fun u => ?_⟩
  have hu : ∀ n, cotMap (G.res n) (u.1 (n + 1)) = u.1 n := u.2
  obtain ⟨n0, hn0⟩ := c.presents.2 2
  have hone := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).1
  have hker : ∀ j f, c.ev (n0 + j) f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < 2 → coeff α f = 0 := by
    intro j
    induction j with
    | zero => exact hn0
    | succ j ih =>
      intro f hf
      refine ih f ?_
      rw [← hone (n0 + j) f]
      exact (congrArg (G.res (n0 + j)) hf).trans (map_zero _)
  have hind : ∀ j (v w : Fin d → k), ∑ i, v i • dUnit k (c.x (n0 + j) i) =
      ∑ i, w i • dUnit k (c.x (n0 + j) i) → v = w := by
    intro j v w h
    have := eq_zero_of_sum (c.x (n0 + j)) (c.nil _) (c.aug _) (c.presents.1 _) (hker j) (v - w)
      (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
    exact sub_eq_zero.1 this
  have hspan : ∀ n, ∃ w : Fin d → k, u.1 n = ∑ i, w i • dUnit k (c.x n i) := fun n =>
    exists_eq_sum (c.x n) (c.nil n) (c.aug n) (c.presents.1 n) (u.1 n)
  obtain ⟨w, hw⟩ := hspan n0
  have hup : ∀ j, u.1 (n0 + j) = ∑ i, w i • dUnit k (c.x (n0 + j) i) := by
    intro j
    induction j with
    | zero => exact hw
    | succ j ih =>
      obtain ⟨v, hv⟩ := hspan (n0 + j + 1)
      have h1 : ∑ i, v i • dUnit k (c.x (n0 + j) i) = ∑ i, w i • dUnit k (c.x (n0 + j) i) := by
        rw [← hres, ← hv, hu, ih]
      rw [← hind j v w h1]
      exact hv
  have hdown : ∀ n j, u.1 (n + j) = ∑ i, w i • dUnit k (c.x (n + j) i) →
      u.1 n = ∑ i, w i • dUnit k (c.x n i) := by
    intro n j
    induction j with
    | zero => exact id
    | succ j ih =>
      intro h
      refine ih ?_
      rw [← hu, ← hres]
      exact congrArg (cotMap (G.res (n + j))) h
  refine ⟨w, fun n => hdown n n0 (by rw [Nat.add_comm]; exact hup n), fun w' hw' => ?_⟩
  exact hind 0 w' w ((hw' n0).symm.trans (hup 0))

end GlobalTheory.OmegaCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenKawamataLogTerminalLocusLogCanonicalLocus
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isOpen_kltLocus_lcLocus : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  intro hP k _ _ X _ _ _ p n hp hdim Δ m G hm hG
  obtain ⟨η, hη⟩ := hG.exists_isLogMult hm
  have hZ : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : x ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at this
    exact this
  obtain ⟨Y, hY, s, hs, K, B, hres, -⟩ := GlobalTheory.T.exists_log_resolution hP k X p n hp hdim η m G hη.ne_zero ⊥ hZ
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := hres.smooth.smooth
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (s ≫ p)
  exact GlobalTheory.T.log_resolution_multiplier_open k X p n hp hdim Δ η m G Y s K B hη hres

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalAddGeneralMemberLinearSystem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeneralMember

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem regAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

theorem unitAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : UnitAt (q y) f) : UnitAt y (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap y a, ha.map _, (functionFieldMap_algebraMap q y a).symm⟩

theorem supp_nsmul_le (D : CartierDiv X) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

theorem functionFieldMap_mem_sections (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X}
    {f : X.functionField} (h : f ∈ A.sections) : functionFieldMap q f ∈ (pullCart q A).sections := by
  refine CartierDiv.mem_sections.2 fun y => ?_
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  have h1 := hg.regularAt_iff.1 (CartierDiv.mem_sections.1 h (q y))
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := regAt_functionFieldMap q y h1
  rwa [map_mul] at this

theorem generatesAt_pullCart (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X} {y : Y}
    {f : X.functionField} (h : A.GeneratesAt (q y) f) :
    (pullCart q A).GeneratesAt y (functionFieldMap q f) := by
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := unitAt_functionFieldMap q y (hg.generatesAt_iff.1 h)
  rwa [map_mul] at this

variable [IsLocallyNoetherian X]

theorem isLogMult_add {p : X ⟶ Sp ℂ} {n : ℕ} {Δ : X → ℚ} {η : RatForms p n} {m m' b e : ℕ}
    {G D₀ : CartierDiv X} {a : ℚ} (hG : IsLogMult p n Δ η m G) (hm' : 0 < m') (he : 0 < e)
    (hab : a = b / e) :
    IsLogMult p n (Δ + a • qWeil D₀ m') η (m * (e * m')) ((e * m') • G + m • (b • D₀)) := by
  refine ⟨hG.ne_zero, Nat.mul_pos hG.pos (Nat.mul_pos he hm'), fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨g₁, hg₁⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((hg₁.nsmul (e * m')).add ((hd.nsmul b).nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow, E.ord_pow] at h3
  have h4 := hG.eqn z g₁ hg₁ z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h2 : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, hd', h3, hab]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory.GeneralMember

open GlobalTheory.GeneralMember in

theorem GlobalTheory.PairStep.kltAt_add_general_member : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (ι : Type) [Fintype ι] (s : ι → X.functionField), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : X.functionFieldˣ, (t : X.functionField) = ∑ i, Cartier.constFn p (u i) * s i → ∀ y : X, (∃ i, A.GeneratesAt y (s i)) → ∀ a c : ℚ, 0 ≤ a → c < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + c • qWeil (GlobalTheory.Cartier.CartierDiv.principal t + A) 1) y := by
  intro hP X _ _ _ p n hproj hn Δ D m G A ι _ s hm hG hD hs
  obtain ⟨η, hη⟩ := hG.exists_isLogMult hm
  obtain ⟨m', D₀, hm', -, rfl⟩ := hD
  obtain ⟨Y, hY, π, hπ, K, B, hres, hB⟩ :=
    GlobalTheory.T.exists_log_resolution hP ℂ X p n hproj hn η m G hη.ne_zero D₀.supp D₀.supp_ne_top
  haveI : IsNoetherian Y := isNoetherian_of_isProjOver hres.proj
  haveI := hres.smooth
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1
  haveI : IsProper (π ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper π := IsProper.of_comp π p
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.T.exists_bertini_poly_discrepancy_snc_boundary Y (π ≫ p) n hres.proj B hres.snc (pullCart π A) ι
    (fun i => functionFieldMap π (s i)) fun i => functionFieldMap_mem_sections π (hs i)
  refine ⟨Q, hQ0, fun u hu t ht y ⟨i, hi⟩ a c ha hc hklt => ?_⟩

  set b : ℕ := a.num.toNat with hb
  set e : ℕ := a.den with he
  have hepos : 0 < e := a.den_pos
  have hab : a = b / e := by
    have h0 : (0 : ℤ) ≤ a.num := Rat.num_nonneg.2 ha
    have h1 : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    rw [hb, he, h1]
    exact (Rat.num_div_den a).symm
  set m'' := m * (e * m') with hm''
  set G' := (e * m') • G + m • (b • D₀) with hG'
  have hm''pos : 0 < m'' := Nat.mul_pos hm (Nat.mul_pos hepos hm')
  have hmult : IsLogMult p n (Δ + a • qWeil D₀ m') η m'' G' := isLogMult_add hη hm' hepos hab

  have hΘ : pullCart π G' - m'' • K = (e * m') • (pullCart π G - m • K) + (m * b) • pullCart π D₀ := by
    have hn1 : ∀ (r : ℕ) (D : CartierDiv X), pullCart π (r • D) = r • pullCart π D :=
      fun r D => map_nsmul (pullCartHom π) r D
    rw [hG', pullCart_add, hn1, hn1, hn1, hm'']
    module
  have hsupp : (pullCart π G' - m'' • K).supp ≤ B := by
    rw [hΘ]
    refine (CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hres.supp)
      ((supp_nsmul_le _ _).trans fun w hw => hB w ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y π D₀).1 w hw)))
  have hres' : IsLogRes p n η m'' G' π K B := { hres with supp := hsupp }

  obtain ⟨g'', hg''⟩ := G'.exists_isEqn y
  have hL := hmult.eqn y g'' hg''
  obtain ⟨ya, hya⟩ := A.exists_isEqn y
  have hH : (CartierDiv.principal t + A).IsEqn y (t * ya) := (CartierDiv.isEqn_principal t y).add hya
  have hHz : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal t + A) 1 z = (E.ord (t * ya) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    obtain ⟨V, hV, hHV⟩ := hH.exists_nhds
    rw [qWeil, (hHV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, hL₂, hdisc⟩ := isLogEqn_add_smul X p n (Δ + a • qWeil D₀ m')
    (qWeil (CartierDiv.principal t + A) 1) η y m'' 1 g'' (t * ya) c hm''pos one_pos hL hHz
  rw [hL₂.kltAt_iff hn hη.ne_zero hm₂]
  intro E hE
  rw [hdisc]

  obtain ⟨E', hE'⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p π hres.bir E
  obtain ⟨y', rfl, hy'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p π hres.bir inferInstance E' E hE' y hE
  have hη' : EtaleKlt.ratPull p π n η ≠ 0 := fun h =>
    hη.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p π hres.bir n).1 (h.trans (map_zero _).symm))
  have hΘm : ∀ w, w ⤳ y' → (pullCart π G' - m'' • K).mult w < m'' := fun w hw =>
    ((GlobalTheory.T.log_resolution_multiplier_local ℂ X p n hproj hn _ η m'' G' Y π K B hmult hres' (π y')).1.1 hklt) w
      (hw.map π.continuous)
  have hΘe : (pullCart π G' - m'' • K + m'' • K).IsEqn y' (fnPull π g'') := by
    rw [sub_add_cancel]; exact isEqn_pullCart π hg''
  have ht' : ((fnPull π t : Y.functionFieldˣ) : Y.functionField) =
      ∑ i, Cartier.constFn (π ≫ p) (u i) * functionFieldMap π (s i) := by
    change functionFieldMap π (t : X.functionField) = _
    rw [ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← EtaleKlt.functionFieldMap_comp_constFn p π, RingHom.comp_apply]
  have hH' : (CartierDiv.principal (fnPull π t) + pullCart π A).IsEqn y' (fnPull π (t * ya)) := by
    rw [map_mul]; exact (CartierDiv.isEqn_principal _ y').add (isEqn_pullCart π hya)
  have key := hQ u hu (fnPull π t) ht' y' ⟨i, generatesAt_pullCart π hi⟩ (EtaleKlt.ratPull p π n η)
    K (pullCart π G' - m'' • K) m'' c (fnPull π g'') (fnPull π (t * ya)) hη' hres.div hm''pos
    hsupp hc hΘm hΘe hH' E' hy'
  have e1 := GlobalTheory.T.form_order_birational_pullback ℂ X Y p π hres.bir E' E hE' n η hη.ne_zero
  have e2 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' g''
  have e3 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' (t * ya)
  simp only [discrep, e1, e2, e3] at key
  simpa [discrep] using key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

theorem ker_eq_range_of_range_eq_ker {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (_ : Module.Finite K V) (_ : Module.Finite K W) (f : V →ₗ[K] W)
    (g : W →ₗ[K] V) (hd : Module.finrank K V = Module.finrank K W) (h0 : g ∘ₗ f = 0)
    (h1 : LinearMap.range g = LinearMap.ker f) : LinearMap.ker g = LinearMap.range f := by
  have e1 := g.finrank_range_add_finrank_ker
  have e2 := f.finrank_range_add_finrank_ker
  rw [h1] at e1
  exact (Submodule.eq_of_le_of_finrank_eq (LinearMap.range_le_ker_iff.2 h0) (by omega)).symm

theorem rigExt_field_of_charP (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
    Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height ∧
    LinearMap.range (rigExtMap (verschiebung h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) ∧
    LinearMap.range (rigExtMap (relFrob h G)) = Submodule.span K (Set.range (absFrob h G).rig) := by
  obtain ⟨-, f1, d1, d2⟩ := GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G
  obtain ⟨-, f2, d3, -⟩ := GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h (frobTwist h G)
  have h4 := le_antisymm (range_rigExtMap_verschiebung_le h G) (GlobalTheory.T.range_rigOfOmega_le_range_rigExtMap_verschiebung' p K h G)
  have h5 := le_antisymm (GlobalTheory.T.ker_rigExtMap_relFrob_le_range_rigOfOmega' p K h G)
    (LinearMap.range_le_ker_iff.2 (rigExtMap_relFrob_comp_rigOfOmega h G))
  have h6 : rigExtMap (verschiebung h G) ∘ₗ rigExtMap (relFrob h G) = 0 :=
    (rigExtMap_comp (verschiebung h G) (relFrob h G)).symm.trans
      ((congrArg rigExtMap (verschiebung_comp_relFrob h G)).trans
        (GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id p K h (frobTwist h G) (frobTwist h G)).2)
  exact ⟨f1, d1, d2, h4, h5, ker_eq_range_of_range_eq_ker f2 f1 _ _
    (d3.trans ((frobTwist_height h G).trans d1.symm)) h6 (h4.trans h5.symm),
    range_rigExtMap_relFrob h G⟩

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneGivesLiftData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.PrimBase

theorem base_of_ties : Hypotheses3 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  intro hP D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM
  have hGiv : GlobalTheory.LiftRows.Given R.toRealDat F.lv2 :=
    GlobalTheory.GivenOfTop.given_of_top R F hT.ok hT.char hT.ex hT.host hT.params hT.ccK hT.guard hT.types
  have hStab : GoodStable A3.A.X := GlobalTheory.T.goodCharacters_dual_stable_of_thetaLift_scalars hP.q12 R.toRealDat F.lv2 hGiv
  have hCD : GlobalTheory.CuspMult.CuspDecomp D := GlobalTheory.CuspDec.cuspDecomp hP.q3 hP.q2 D
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hP.q2 D
  have hCore := GlobalTheory.CoreOfWeak.core_of_weak R F hT.char hT.ex
  have hSch : GlobalTheory.Hk3.SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP.q2 R.toRealDat
  have hTR : GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF :=
    GlobalTheory.T.transfer_eigensystem_parts_three_levels_of_mult_eq R.toRealDat F.lv2 1 hT.ok.ok2 hCore.1 hSch hStab hCD hM R.SF hCore.2.1
  have hFix : ∀ t P, GlobalTheory.Hk3.Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R.toRealDat t P :=
    GlobalTheory.FixAllGood.fixAll_of_good R F hT.char hT.ex
  have hU := GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective hP.q5 hP.q3 hP.q4 hP.q6 hP.q2 hP.q1 hP.q7 hP.q8
    (GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod hP.q9) hP.q10 hP.q11 R.toRealDat F.lv2 hGiv hT.ccK
    hT.char.allPl hFix R.SF hCore.2.1 hTR
  exact ⟨hGiv, hStab, hCD, hLI, hTR, hU.2.2.1, hU.2.2.2⟩

end GlobalTheory.PrimBase
end

