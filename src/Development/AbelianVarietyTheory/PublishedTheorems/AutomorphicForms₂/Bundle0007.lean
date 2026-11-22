import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.Published

def ArBirational : Prop :=
  ∀ (k : Type) [CommRing k] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp k) (p' : X' ⟶ Sp k) (D : ℕ),
    IsArithVar p D → IsArithVar p' D → GenSmooth p D → GenSmooth p' D →
      ∀ (π : X' ⟶ X) (hπ : π ≫ p = p') (U : X.Opens), (U : Set X).Nonempty →
        IsIso (π ∣_ U) → ∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a → (L.pull π hπ).IsSelfInter a

def ChernDegree : Prop :=
  ∀ (F : Type) [Field F] (Y : Var F) (σ : F →+* ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), Presents Δ L r →
    ∀ φ : Weight Y.str σ L, φ.IsCInf →
      φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧
        φ.chernInt Y.dim Set.univ (fun _ => 1) = (Y.inter (fun _ => Δ) : ℝ)

def ArDegree : Prop := ArBirational ∧ ChernDegree

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay

variable {D : D7}

def quotHeight (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) : NNReal :=
  ⨅ γ : GQ V, height θ V ((γ : GA D V) * g)

def IsRapidDecay (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ g : GA D V, ‖φ g‖ * (quotHeight θ V g : ℝ) ^ N ≤ C

end GlobalTheory.CuspDecay

namespace GlobalTheory.Published

def CuspRapidDecay : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (e : LieInf V → GA D V), IsExpFam θ V e →
      ∀ φ : GA D V → ℂ, IsAutFun V φ → IsSmoothInf V e φ → IsUnifModerate θ V e φ → IsCuspFun V φ →
        GlobalTheory.CuspDecay.IsRapidDecay θ V φ

end GlobalTheory.Published

namespace GlobalTheory.CuspDecay

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem quotHeight_le (g : GA D V) {γ : GA D V} (hγ : γ ∈ GQ V) : quotHeight θ V g ≤ height θ V (γ * g) :=
  ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : GQ V)

theorem one_le_quotHeight (g : GA D V) : 1 ≤ quotHeight θ V g :=
  le_ciInf fun _ => one_le_height θ V _

theorem exists_height_le (g : GA D V) : ∃ γ ∈ GQ V, height θ V (γ * g) ≤ 2 * quotHeight θ V g := by
  have h : quotHeight θ V g < 2 * quotHeight θ V g :=
    lt_mul_of_one_lt_left (zero_lt_one.trans_le (one_le_quotHeight g)) one_lt_two
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt h
  exact ⟨γ, γ.2, hγ.le⟩

theorem IsRapidDecay.bounded {φ : GA D V → ℂ} (h : IsRapidDecay θ V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem IsRapidDecay.mul_bounded {φ ψ : GA D V → ℂ} (h : IsRapidDecay θ V φ)
    (hψ : ∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) {N : ℕ} {C : ℝ} (hC : ∀ g, ‖ψ g‖ ≤ C * (height θ V g : ℝ) ^ N) :
    ∃ B : ℝ, ∀ g, ‖ψ g‖ * ‖φ g‖ ≤ B := by
  obtain ⟨C', hC'⟩ := h N
  refine ⟨|C| * 2 ^ N * C', fun g => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
  have h2 : ‖ψ g‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ)) ^ N := by
    rw [← hψ γ hγ g]
    exact (hC _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _))
  calc ‖ψ g‖ * ‖φ g‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ)) ^ N * ‖φ g‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖φ g‖ * (quotHeight θ V g : ℝ) ^ N) := by rw [mul_pow]; ring
    _ ≤ |C| * 2 ^ N * C' := mul_le_mul_of_nonneg_left (hC' g) (by positivity)

theorem exists_norm_le_height_pow (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ g‖ ≤ C * (height θ V g : ℝ) ^ N := by
  obtain ⟨-, -, h1⟩ := (GlobalTheory.SmoothForms.isAutFunSm_iff hθ V φ).1 h
  obtain ⟨⟨e, he⟩, h2⟩ := h1 θ hθ
  obtain ⟨-, -, N, hN⟩ := h2 e he
  obtain ⟨C, hC⟩ := hN []
  exact ⟨N, C, hC⟩

theorem isRapidDecay_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : IsRapidDecay θ V φ := by
  obtain ⟨ha, -, h1⟩ := (GlobalTheory.SmoothForms.isAutFunSm_iff hθ V φ).1 h
  obtain ⟨⟨e, he⟩, h2⟩ := h1 θ hθ
  obtain ⟨hs, -, hg⟩ := h2 e he
  exact hP D θ hθ V e he φ ha hs hg hc

theorem bounded_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C :=
  (isRapidDecay_of_cuspForm hP hθ h hc).bounded

theorem mul_bounded_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {ψ φ : GA D V → ℂ}
    (hψ : IsAutFunSm θ V ψ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : ∃ B : ℝ, ∀ g, ‖ψ g‖ * ‖φ g‖ ≤ B := by
  obtain ⟨N, C, hC⟩ := exists_norm_le_height_pow hθ hψ
  exact (isRapidDecay_of_cuspForm hP hθ h hc).mul_bounded hψ.left hC

theorem measure_lt_top (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : μ 𝓕 < ⊤ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  exact hV D.host.F D.host.E D.sp.cm.sig h1 V.rank V.gram (h2 V) μ hμ 𝓕 h𝓕

theorem integrableOn_star_mul (hP : GlobalTheory.Published.CuspRapidDecay) (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (hθ : IsInfFam θ)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {ψ φ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IntegrableOn (fun g => star (ψ g) * φ g) 𝓕 μ := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨B, hB⟩ := mul_bounded_of_cuspForm hP hθ hψ h hc
  refine Measure.integrableOn_of_bounded (M := B) (measure_lt_top hV V μ 𝓕 hμ h𝓕).ne
    ((hψ.cont.star.mul h.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hB g

end GlobalTheory.CuspDecay

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.Test

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem eps_zero {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hc : Continuous ψ) (h1 : ψ ≠ 1) : ε E w h ψ (WD.lpZero h) = 1 := by
  have := hε.add E w h ψ hc h1 (WD.lpZero h) (WD.lpZero h)
  rw [WD.lpSum_zero] at this
  exact left_eq_mul.1 this

theorem unr_lpOfChar_iff (ha : IsLocalArtin h a) {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).unr ↔ IsUnram χ := by
  rw [WD.lpOfChar, WD.unr_mk]
  constructor
  · rintro ⟨-, H⟩ x hx
    obtain ⟨σ, rfl⟩ := ha.surj x
    have h0 : deg σ = 0 := by
      have := ha.ord_eq σ
      rw [ord_eq_zero_iff.2 hx] at this
      omega
    have h2 := congrFun (LinearMap.congr_fun (H ⟨_, deg_eq_zero_iff.mp h0⟩) fun _ => 1) 0
    have h3 : χ (a (ineIncl h ⟨_, deg_eq_zero_iff.mp h0⟩)) = 1 := by simpa using h2
    exact h3
  · intro H
    refine ⟨rfl, fun σ => LinearMap.ext fun v => funext fun i => ?_⟩
    have : χ (a (ineIncl h σ)) = 1 := H _ (ord_eq_zero_iff.1 (by rw [ha.ord_eq]; simp))
    simp [this]

theorem lpOfChar_unrChar (ha : IsLocalArtin h a) (c : ℂˣ) (hc) :
    WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp a) hc = WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := by
  simp only [WD.lpOfChar, WDRep.diag, ha.unrChar_comp]

theorem lpChar_lpSp_one (x : WD h) : x.lpChar (WD.lpSp h 1) = x := by
  have h1 : WD.lpSp h 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

theorem not_isIrrWD_zero : ¬ IsIrrWD (WD.lpZero h) := by
  rintro ⟨n, b, hb, hi⟩
  have hn : n = 0 := by simpa [WD.lpZero] using congrArg WD.lpDim hb
  subst hn
  have : Nontrivial (Subrepresentation b.ρ) := inferInstance
  obtain ⟨S, T, hST⟩ := this
  exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem exists_steinberg {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h}
    (H : Laws a ha ε rc) : ∃ x : IrrGL (w.adicCompletion E), x.1 = 2 ∧ rc x = WD.lpSp h 2 ∧ ¬ IsSpherical x.rep := by
  obtain ⟨x, hx⟩ := H.bij.2 (WD.lpSp h 2)
  refine ⟨x, by rw [← H.dim, hx]; simp, hx, fun hs => (sp_two_spec h).2.2.2 (hx ▸ (H.sph x).1 hs)⟩

end GlobalTheory.LocLanglands.Test
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Transport

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fixed_ne_bot_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (hπ : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hπ
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => h0 ?_⟩
  · exact (φ.toIntertwiningMap.isIntertwining _ _ u v).symm.trans
      (congrArg φ (GlobalTheory.Parabolic.mem_fixed.1 hv u hu))
  · exact φ.toLinearEquiv.injective (h1.trans (map_zero _).symm)

end Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def toIrrRep {n : ℕ} (π : Irr (w.adicCompletion E) n) : IrrRep (GL (Fin n) (w.adicCompletion E)) :=
  ⟨π.V, π.π, π.smooth, π.irr⟩

theorem IsRec.recLaws {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecLaws fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  have hc : ∀ (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1),
      Nonempty (c.π.Equiv (detRep (Fin 1) χ)) → ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
    rintro χ c ⟨φ⟩
    have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
      ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
    have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
      Units.continuous_map (continuous_matrix fun i j => by
        rw [Subsingleton.elim i j]; simpa using continuous_id')
    have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
      refine MonoidHom.ext fun z => congrArg χ ?_
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩
  refine ⟨fun n π => H.dim _, fun n π π' => H.eq_iff _ _, fun r t σ τ π hπ => H.prod r t _ _ _ hπ, ?_, ?_, ?_, ?_⟩
  · intro t χ c τ h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, (H.eq_iff (toIrrRep τ) (IrrRep.det (Fin t) χ hχ)).2 h2, H.det, sumList, List.foldr_map, speh]
    simp [List.foldr_map, ← List.map_eq_flatMap]
  · intro n χ c π π' h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, ← H.twist]
    exact congrArg rc ((IrrGL.of_eq_of.2 h2).trans (IrrGL.tw_of π.π π.smooth π.irr χ hχ).symm)
  · intro n π
    rw [← H.sph]
    exact ⟨fixed_ne_bot_of_equiv (equivRep (toIrrRep π)).symm, fixed_ne_bot_of_equiv (equivRep (toIrrRep π))⟩
  · intro n π α hα
    have φ := equivRep (toIrrRep π)
    rw [H.sat (cls (toIrrRep π)) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩, WD.frobEig_diag]

theorem _root_.GlobalTheory.Published.LocalLanglandsGL.exists_recLaws (H : GlobalTheory.Published.LocalLanglandsGL) (h : IsPlaceOver A w) :
    ∃ rc : ∀ n, Irr (w.adicCompletion E) n → WD h, RecLaws rc :=
  let ⟨_, hrc, _⟩ := H.1 E Ω A w h
  ⟨_, hrc.recLaws⟩

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] (Y : Var F) {κ : Type} (Δ : κ → Y.Dv)

open Classical in

def interPoly : MvPolynomial κ ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials κ ℝ).constr ℝ fun d =>
    if h : ∃ s : Fin Y.dim → κ, ∑ i, Finsupp.single (s i) 1 = d then (Y.inter (Δ ∘ h.choose) : ℝ) else 0

private theorem inter_comp_eq_of_sum_single_eq (s t : Fin Y.dim → κ)
    (h : ∑ i, Finsupp.single (t i) 1 = ∑ i, Finsupp.single (s i) (1 : ℕ)) :
    Y.inter (Δ ∘ t) = Y.inter (Δ ∘ s) := by
  classical
  have hc : ∀ k, Fintype.card {i // t i = k} = Fintype.card {i // s i = k} := by
    intro k
    have hk := congrArg (fun f : κ →₀ ℕ => f k) h
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply] at hk
    simpa [Fintype.card_subtype, Finset.sum_boole] using hk
  let σ : Fin Y.dim ≃ Fin Y.dim := (Equiv.sigmaFiberEquiv t).symm.trans
    ((Equiv.sigmaCongrRight fun k => Fintype.equivOfCardEq (hc k)).trans (Equiv.sigmaFiberEquiv s))
  have hσ : ∀ i, s (σ i) = t i := fun i => ((Fintype.equivOfCardEq (hc (t i))) ⟨i, rfl⟩).2
  have hcomp : Δ ∘ t = (Δ ∘ s) ∘ σ := funext fun i => by simp only [Function.comp_apply, hσ]
  rw [hcomp, inter_comp_perm]

theorem interPoly_prod (s : Fin Y.dim → κ) : Y.interPoly Δ (∏ i, MvPolynomial.X (s i)) = Y.inter (Δ ∘ s) := by
  classical
  have hprod : (∏ i, MvPolynomial.X (s i) : MvPolynomial κ ℝ) =
      (basisMonomials κ ℝ) (∑ i, Finsupp.single (s i) 1) := by
    simp only [coe_basisMonomials]
    rw [monomial_sum_one]
    rfl
  have h : ∃ t : Fin Y.dim → κ, ∑ i, Finsupp.single (t i) 1 = ∑ i, Finsupp.single (s i) 1 := ⟨s, rfl⟩
  rw [hprod]
  unfold interPoly
  rw [Module.Basis.constr_basis, dif_pos h]
  exact_mod_cast inter_comp_eq_of_sum_single_eq Y Δ s h.choose h.choose_spec

theorem interPoly_prod_sum [Fintype κ] (a : Fin Y.dim → κ → ℤ) :
    Y.interPoly Δ (∏ i, ∑ x, C (a i x : ℝ) * MvPolynomial.X x) = Y.inter fun i => ∑ x, a i x • Δ x := by
  classical
  rw [Fintype.prod_sum, map_sum, ← interForm_apply, MultilinearMap.map_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [interForm_apply]
  have e1 : (∏ i, C (a i (p i) : ℝ) * MvPolynomial.X (p i) : MvPolynomial κ ℝ) =
      ((∏ i, a i (p i) : ℤ) : ℝ) • ∏ i, MvPolynomial.X (p i) := by
    rw [Finset.prod_mul_distrib, ← map_prod, C_mul']
    push_cast
    rfl
  rw [e1, map_smul, interPoly_prod, smul_eq_mul]
  rw [show (fun i => a i (p i) • Δ (p i)) = fun i => a i (p i) • (Δ ∘ p) i from rfl, inter_zsmul]
  push_cast
  rfl

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.GoodMetric

section Forms

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def topCoeff (P : MvPolynomial (Fin n × Fin n) ℂ) : ℂ :=
  ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * coeff (∑ a, Finsupp.single (a, w a) 1) P

abbrev coordVec (a : Fin n) : V n := EuclideanSpace.single a 1

def curvPoly (G : V n → Matrix r r ℂ) (v : V n) : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ a, ∑ b, C (curv G v (coordVec a) (coordVec b) i j) * X (a, b)

def chernPoly (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  (Matrix.charpolyRev (-curvPoly G v)).coeff k

def chernTop {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) (v : V n) : ℝ :=
  (Real.pi ^ n)⁻¹ * (topCoeff (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R)).re

def poinWt (S : Finset (Fin n)) (v : V n) (a : Fin n) : ℝ := if a ∈ S then ‖v a‖ * |Real.log ‖v a‖| else 1

structure GoodBound (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (G : V n → Matrix r r ℂ) (v : V n) : Prop where
  entry : ∀ i j, ‖G v i j‖ ≤ c * (∑ a ∈ S, |Real.log ‖v a‖|) ^ N
  det : ‖(G v).det‖⁻¹ ≤ c * (∑ a ∈ S, |Real.log ‖v a‖|) ^ N
  form : ∀ a i j, ‖conn G v (coordVec a) i j‖ * poinWt S v a ≤ c
  dbar : ∀ a b i j, ‖curv G v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c
  del : ∀ a b i j, ‖(mdel (fun u => conn G u (coordVec b)) v (coordVec a) -
    mdel (fun u => conn G u (coordVec a)) v (coordVec b)) i j‖ * (poinWt S v a * poinWt S v b) ≤ c

end Forms

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ}

section Metric

variable {X : Var F} {σ : F →+* ℂ}

def IsHoloChart (e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)) : Prop :=
  ∀ (W : X.X.Opens) (f : Γ(X.X, W)),
    DifferentiableOn ℂ (ev X.str σ W f ∘ e.symm) (e.target ∩ e.symm ⁻¹' ptsIn X.str σ W)

variable (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)

structure IsMetricOn : Prop where
  posDef : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), ∀ τ, (H A y τ).PosDef
  smooth : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), ∀ τ i j,
    CInfAt (fun z => (H A z τ i j).re) y ∧ CInfAt (fun z => (H A z τ i j).im) y
  trans : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ τ,
    H A' y τ = (A' * A⁻¹).map (ratVal · y) τ * H A y τ * ((A' * A⁻¹).map (ratVal · y) τ)ᴴ

def IsGood : Prop :=
  ∀ y ∉ ptsIn X.str σ O, ∃ (e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)) (S : Finset (Fin X.dim)),
    IsHoloChart e ∧ y ∈ e.source ∧ (∀ a ∈ S, e y a = 0) ∧ (∀ z ∈ e.source, z ∉ ptsIn X.str σ O ↔ ∃ a ∈ S, e z a = 0) ∧
      ∃ A ∈ E.S (under y), ∃ (c : ℝ) (N : ℕ), ∀ᶠ z in 𝓝[ptsIn X.str σ O] y, ∀ τ,
        GoodBound S c N (fun v => H A (e.symm v) τ) (e z)

def chernTopPart (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ) : Measure (CxPts X.str σ) :=
  glueMeas (fun c : AlgChart X.str σ X.dim => c.e) fun c y =>
    ENNReal.ofReal ((ε : ℤ) * chernTop R (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y))

def HasChernIntegral (R : MvPolynomial (ι × ℕ) ℝ) (t : ℝ) : Prop :=
  (∀ ε, chernTopPart E H R ε (ptsIn X.str σ O) ≠ ⊤) ∧
    (chernTopPart E H R 1).real (ptsIn X.str σ O) - (chernTopPart E H R (-1)).real (ptsIn X.str σ O) = t

end Metric

abbrev Root (m : ι → ℕ) : Type := Σ τ, Fin (m τ)

def IsGraded {Y : Var F} (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv) : Prop :=
  ∃ B ∈ E'.S (genericPoint Y.X), ∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ,
    (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t

variable (m)

def chernRoots : MvPolynomial (ι × ℕ) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ :=
  aeval fun x => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) ℝ x.2)

variable [Fintype ι]

def fibrePoint : MvPolynomial (Root m) ℝ := ∏ x : Root m, (-X x) ^ (m x.1 - 1 - x.2)

def rootDiscr : MvPolynomial (Root m) ℝ :=
  ∏ τ, ∏ j : Fin (m τ), ∏ i ∈ Finset.Iio j, (X ⟨τ, j⟩ - X ⟨τ, i⟩)

variable {m} in
open Classical in

def antisymm (Q : MvPolynomial (Root m) ℝ) : MvPolynomial (Root m) ℝ :=
  ∑ w : ∀ τ, Equiv.Perm (Fin (m τ)),
    ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q

end GlobalTheory.GoodMetric
end
end

