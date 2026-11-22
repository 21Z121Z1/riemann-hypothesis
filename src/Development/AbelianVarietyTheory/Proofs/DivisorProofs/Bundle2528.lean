import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanImageOfForallHeightOneOverPrimeStatement
section
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_image_of_forall_height_one_over_prime : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (p : Ideal R), p.IsPrime → p.height = 1 → f ∈ p → ∀ (W : Set F), (∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W) → (∀ a ∈ W, ∀ b ∈ W, a + b ∈ W) → (∀ r, ∀ a ∈ W, c₀ r * a ∈ W) → (∀ s, s ∉ p → ∀ a ∈ W, (c₀ s)⁻¹ * a ∈ W) → ∀ x ∈ spanBy c₁ (Set.range θ), (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → q.comap ρ = p → ∃ s, s ∉ q ∧ c₁ s * x ∈ spanBy c₁ (θ '' W)) → x ∈ spanBy c₁ (θ '' W) := by
  first | exact @GlobalTheory.Desc.LocalDescent.mem_spanBy_of_forall_height_one | exact GlobalTheory.Desc.LocalDescent.mem_spanBy_of_forall_height_one | (intros; apply GlobalTheory.Desc.LocalDescent.mem_spanBy_of_forall_height_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanRelationsConductorOfEvalEqZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero : ∀ (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E] (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D) (F : σ → MvPolynomial ν R), Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) → RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) → IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ) → ∀ G : MvPolynomial ν R', MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0 → G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔ (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  first | exact @GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | exact GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | (intros; apply GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalPolynomialLinearFactorSplit
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigProj

open Polynomial

theorem eigProj_poly : ∀ (E : Type) [Field E] [NumberField E] (b : E) (σ : E →+* ℂ), ∃ (Q : Polynomial Qb) (c : ℂ),
    (Polynomial.X - Polynomial.C (σ b)) * Q.map (algebraMap Qb ℂ) = Polynomial.C c * (minpoly ℚ b).map (algebraMap ℚ ℂ) ∧
    (Q.map (algebraMap Qb ℂ)).eval (σ b) = 1 := by
  intro E _ _ b σ
  have hint : IsIntegral ℚ b := Algebra.IsIntegral.isIntegral b
  have hcomp : σ.comp (algebraMap ℚ E) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hroot : (minpoly ℚ b).eval₂ (algebraMap ℚ ℂ) (σ b) = 0 := by
    rw [← hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hmem : σ b ∈ algebraicClosure ℚ ℂ := by
    exact mem_algebraicClosure_iff.2 (hint.map (σ.toRatAlgHom)).isAlgebraic
  set β : Qb := ⟨σ b, hmem⟩ with hβ
  have hι : algebraMap Qb ℂ β = σ b := rfl
  have hcompQ : (algebraMap Qb ℂ).comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hrootQ : (minpoly ℚ b).eval₂ (algebraMap ℚ Qb) β = 0 := by
    apply (algebraMap Qb ℂ).injective
    rw [Polynomial.hom_eval₂, hcompQ, hι, hroot, map_zero]
  set fQ := (minpoly ℚ b).map (algebraMap ℚ Qb) with hfQ
  have hfQroot : fQ.IsRoot β := by
    rw [Polynomial.IsRoot, hfQ, Polynomial.eval_map]; exact hrootQ
  set g := fQ /ₘ (X - C β) with hg
  have hfac : (X - C β) * g = fQ := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hfQroot
  have hsep : (minpoly ℚ b).Separable := Algebra.IsSeparable.isSeparable ℚ b
  have hder := hsep.eval₂_derivative_ne_zero (algebraMap ℚ Qb) hrootQ
  have hgβ : g.eval β ≠ 0 := by
    intro h0
    apply hder
    have : (derivative (minpoly ℚ b)).eval₂ (algebraMap ℚ Qb) β = (derivative fQ).eval β := by
      rw [hfQ, Polynomial.derivative_map, Polynomial.eval_map]
    rw [this, ← hfac, derivative_mul]
    simp [h0]
  refine ⟨C (g.eval β)⁻¹ * g, (algebraMap Qb ℂ (g.eval β))⁻¹, ?_, ?_⟩
  · have key : (X - C β) * (C (g.eval β)⁻¹ * g) = C (g.eval β)⁻¹ * fQ := by rw [← hfac]; ring
    have := congrArg (Polynomial.map (algebraMap Qb ℂ)) key
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hι, map_inv₀] at this
    simp only [Polynomial.map_mul, Polynomial.map_C, map_inv₀]
    rw [this, hfQ, Polynomial.map_map, hcompQ]
  · rw [Polynomial.eval_map, ← hι, Polynomial.eval₂_at_apply, Polynomial.eval_mul, Polynomial.eval_C,
      inv_mul_cancel₀ hgβ, map_one]

end GlobalTheory.EigProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetrics
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombChern

section Bundle

variable {X : Scheme.{0}} [IsIntegral X]

theorem presents_zpow {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) (n : ℤ) :
    Presents (n • D) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n) fun j => r (j PUnit.unit) ^ n := by
  have mem : ∀ (j : PUnit → L.ι) {x : X}, x ∈ (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j →
      x ∈ L.U (j PUnit.unit) := fun j x hx => by simpa using Set.mem_iInter.1 hx PUnit.unit
  refine ⟨LB.isLB_linComb h.isLB _ _, fun j j' hjj => ?_, fun j x hx => (h.isEqn _ x (mem j hx)).zsmul n⟩
  have l : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j ⊓
      (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j' ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    fun x hx => ⟨mem j hx.1, mem j' hx.2⟩
  have hg : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).g j j' = res l (L.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
    change ∏ _k : PUnit, _ = _
    exact Fintype.prod_unique _
  have key : ∀ {U : X.Opens} (hU : genericPoint X ∈ U) (u : Γ(X, U)ˣ) (m : ℤ),
      fnOf U hU ((u ^ m : Γ(X, U)ˣ) : Γ(X, U)) = fnOf U hU (u : Γ(X, U)) ^ m := fun hU u m => by
    have e := congrArg Units.val (map_zpow (Units.map (fnOf _ hU).toMonoidHom) u m)
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at e
    exact e
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, h.isRatSec _ _ (l hjj), mul_zpow, hg, key]
  congr 2
  exact (fnOf_resG l hjj _).symm

end Bundle

section Comb

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (T : ι → LB X) (b : ι → ℤ)

noncomputable def cBun : List ι → LB X
  | [] => LB.triv X
  | i :: l => CechPic.tens (LB.LinComb (T i) (K := PUnit) (fun _ => 𝟙 X) fun _ => b i) (cBun l)

noncomputable def cEq (r : ∀ i, (T i).ι → X.functionFieldˣ) : ∀ l, (cBun T b l).ι → X.functionFieldˣ
  | [] => fun _ => 1
  | i :: l => fun q => r i (q.1 PUnit.unit) ^ b i * cEq r l q.2

theorem presents_cBun {D : ι → CartierDiv X} {r : ∀ i, (T i).ι → X.functionFieldˣ}
    (hr : ∀ i, Presents (D i) (T i) (r i)) :
    ∀ l, Presents ((l.map fun i => b i • D i).sum) (cBun T b l) (cEq T b r l)
  | [] => presents_zero
  | i :: l => by
    rw [List.map_cons, List.sum_cons]
    exact (presents_zpow (hr i) (b i)).tens (presents_cBun hr l)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

noncomputable def cWt (ψ : ∀ i, Weight p σ (T i)) : ∀ l, Weight p σ (cBun T b l)
  | [] => Weight.ofFun 0
  | i :: l => ((ψ i).zpow (b i)).tens (cWt ψ l)

theorem isCInf_cWt {ψ : ∀ i, Weight p σ (T i)} (h : ∀ i, (ψ i).IsCInf) : ∀ l, (cWt T b ψ l).IsCInf
  | [] => Weight.isCInf_ofFun fun y => cInfAt_const 0 y
  | i :: l => ((h i).zpow (b i)).tens (isCInf_cWt h l)

noncomputable def cIdx (ψ : ∀ i, Weight p σ (T i)) (x : CxPts p σ) : ∀ l, (cBun T b l).ι
  | [] => PUnit.unit
  | i :: l => (fun _ => pick (ψ i).isLB x, cIdx ψ x l)

theorem mem_cIdx (ψ : ∀ i, Weight p σ (T i)) (x : CxPts p σ) :
    ∀ l, x ∈ ptsIn p σ ((cBun T b l).U (cIdx T b ψ x l))
  | [] => mem_ptsIn_top
  | i :: l => mem_ptsIn_inf.2 ⟨mem_pow_iff.2 (mem_pick (ψ i).isLB x), mem_cIdx ψ x l⟩

theorem cWt_φ (ψ : ∀ i, Weight p σ (T i)) (x z : CxPts p σ) :
    ∀ l, (cWt T b ψ l).φ (cIdx T b ψ x l) z = (l.map fun i => (b i : ℝ) * (ψ i).φ (pick (ψ i).isLB x) z).sum
  | [] => rfl
  | i :: l => by
    rw [List.map_cons, List.sum_cons, ← cWt_φ ψ x z l]
    exact congrArg (· + _) ((ψ i).zpow_φ (b i) _ z)

end Comb

section Met

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem metWeight_isCInf_at {e : ℕ} {M : Man e} (I : ManIs M Y) (a : Fin (M.n + 1)) {Δ : Y.Dv}
    {m : C.Met Y (I.ε a) Δ} (hm : ∀ y, PosAt m y) {Q : LocPot (M.X a)}
    (hQ : IsPot (I.pt a) m Q ∧ IsPotential (M.A a) Q) : (metWeight Δ m hm).IsCInf := by
  intro c y hy
  obtain ⟨x, rfl⟩ := (I.pt a).surjective y
  have hxU : (I.pt a).symm (I.pt a x) ∈ Q.U x := by simpa using Q.mem_U x
  obtain ⟨f, hf⟩ := hQ.1 x
  have key : ∀ z : Pts Y (I.ε a), (I.pt a).symm z ∈ Q.U x → z ∈ ptsIn Y.str (I.ε a) ((toLB Δ).U c) →
      UnitAt (under z) (f * (c.1.2 : Y.Fn)) ∧ (metWeight Δ m hm).φ c z =
        2 * Q.φ x ((I.pt a).symm z) + Real.log (‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2) := by
    intro z hz hzc
    have hzc' : under z ∈ c.1.1 := mem_ptsIn.1 hzc
    obtain ⟨h₁, h₂, h₃⟩ := hf _ hz
    rw [Homeomorph.apply_symm_apply] at h₁ h₂ h₃
    have he : Δ.IsEqn (under z) c.1.2 := c.2.2 _ hzc'
    have hu := he.generatesAt_iff.1 h₁
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 he
    have hp := pn_pos_of_generatesAt (C := C) hgen (hm z)
    have hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2 := pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2
    have e₁ : (f * (c.1.2 : Y.Fn)) * (c.1.2 : Y.Fn)⁻¹ = f := by
      rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
    have e₂ := C.pn_mul Y _ Δ m _ _ z hu.regAt hgen.regularAt
    rw [e₁] at e₂
    refine ⟨hu, ?_⟩
    rw [metWeight_φ, h₃, lnN, e₂, Real.log_mul hr.ne' hp.ne']
    ring
  have hS : IsOpen ((I.pt a).symm ⁻¹' Q.U x) := (Q.isOpen_U x).preimage (I.pt a).symm.continuous
  refine (((MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.cInfAt_of_smoothOn_tAtlas (isAlgAtlas_tAtlas I a) (Q.isOpen_U x)
    (hQ.2.1 x) hxU).const_mul 2).add
    (MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.cInfAt_log_normSq_ratVal (key _ hxU hy).1)).congr ?_
  filter_upwards [hS.mem_nhds hxU, (isOpen_ptsIn _).mem_nhds hy] with z hz hzc
  exact (key z hz hzc).2

end Met

theorem mInt_combPot_eq_inter : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : GlobalTheory.ProjVar.Var F)
    (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (ι : Type) [Fintype ι] (Δ : ι → Y.Dv)
    (m : ∀ i (σ : F →+* ℂ), (cxSt F).Met Y σ (Δ i)) (b : ι → ℤ) (Q : ι → LocPot (M.X a)), Y.dim = e →
    (∀ i σ, (cxSt F).mSmooth Y σ (Δ i) (m i σ)) →
    (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) →
    mInt (M.A a) (fun _ => InhabCalc.combPot Q (fun i => (b i : ℝ)) (fun _ => 0)) (fun _ => 1) =
      (Y.inter (fun _ => ∑ i, b i • Δ i) : ℝ) := by
  intro hCD F _ _ Y e M I a ι _ Δ m b Q hdim _ hQ
  subst hdim
  have hm : ∀ i y, PosAt (m i (I.ε a)) y := by
    intro i y
    obtain ⟨x, rfl⟩ := (I.pt a).surjective y
    obtain ⟨f, hf⟩ := (hQ i).1 x
    exact (hf x ((Q i).mem_U x)).2.1
  let ψ : ∀ i, Weight Y.str (I.ε a) (toLB (Δ i)) := fun i => metWeight (Δ i) (m i (I.ε a)) (hm i)
  have hψ : ∀ i, (ψ i).IsCInf := fun i => metWeight_isCInf_at I a (hm i) (hQ i)
  let l := (Finset.univ : Finset ι).toList
  have hp := presents_cBun (fun i => toLB (Δ i)) b (fun i => presents_toLB (Δ i)) l
  have hD : (l.map fun i => b i • Δ i).sum = ∑ i, b i • Δ i := Finset.sum_map_toList _ _
  rw [hD] at hp
  let φ := cWt (fun i => toLB (Δ i)) b ψ l
  have hφ : φ.IsCInf := isCInf_cWt _ b hψ l
  obtain ⟨-, hc⟩ := hCD F Y (I.ε a) _ _ _ hp φ hφ
  have := CxPts.secondCountableTopology_of_isProjOver (I.ε a) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (I.ε a) Y.isProjOver
  have hA := isAlgAtlas_tAtlas I a
  rw [← hc, ChernMA.chernInt_eq_mInt hφ hA continuous_const]
  let TM : LocPot (M.X a) := InhabCalc.combPot Q (fun i => (b i : ℝ)) (fun _ => 0)
  have hTM : IsPotential (M.A a) TM :=
    InhabCalc.isPotential_combPot _ _ (fun i => (hQ i).2) _ _ (fun _ => contDiffOn_const)
  let T : LocPot (Pts Y (I.ε a)) := TM.pullback (I.pt a).symm (I.pt a).symm.continuous
  have hT : IsPotential (tAtlas (M.A a) (I.pt a)) T :=
    PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback _ _ _ _ _ _ hTM
  have hsf : SameForm (tAtlas (M.A a) (I.pt a)) φ.locPot T := by
    refine Weight.sameForm_of_re (R := hA.anRead) _ hA hT fun x => ?_
    have h6 := fun i => HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq F (cxSt F) Y (I.ε a) _ _ hA (Δ i)
      (m i (I.ε a)) (hm i) _ (IsPot.pullback_symm (hQ i).1) x (pick (ψ i).isLB x) (mem_pick _ x)
    choose W hW hxW G hG hGe using h6
    refine ⟨cIdx _ b ψ x l, mem_cIdx _ b ψ x l, ⋂ i, W i, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hxW,
      fun z => ∑ i, (b i : ℂ) * G i z, (hA.holoOn_iff hA.anRead (isOpen_iInter_of_finite hW)).1 ?_, fun z hz => ?_⟩
    · intro j t ht
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        analyticAt_const.mul (hG i j t ⟨ht.1, Set.mem_iInter.1 ht.2 i⟩)
    · have e1 : ∀ i, (ψ i).φ (pick (ψ i).isLB x) z =
          2 * ((Q i).φ ((I.pt a).symm x) ((I.pt a).symm z) + (G i z).re) := fun i => by
        have := hGe i z (Set.mem_iInter.1 hz i)
        simp only [LocPot.pullback] at this
        linarith
      have e3 : T.φ x z = ∑ i, (b i : ℝ) * (Q i).φ ((I.pt a).symm x) ((I.pt a).symm z) + 0 := rfl
      have e4 : ∀ i, ((b i : ℂ) * G i z).re = (b i : ℝ) * (G i z).re := fun i => by simp
      rw [cWt_φ, Finset.sum_map_toList, e3, Complex.re_sum]
      simp only [e1, e4]
      rw [Finset.sum_div, add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  rw [SameForm.mInt_eq (fun _ => hsf), MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas _ _ _ _ _ _ _ (fun _ => hT)
    continuous_const]
  refine InhabCalc.mInt_congr_φ (M.A a) (fun _ => ?_) _
  funext x z
  simp [T, TM, LocPot.pullback]

end GlobalTheory.CombChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

namespace GlobalTheory.Points

theorem eq_of_forall_mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {z z' : X} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : ∀ f : Γ(X, U), z ∈ X.basicOpen f ↔ z' ∈ X.basicOpen f) : z = z' := by
  have key : ∀ (x : U) (f : Γ(X, U)),
      f ∉ (hU.primeIdealOf x).asIdeal ↔ x.1 ∈ X.basicOpen f := by
    intro x f
    have e1 := hU.fromSpec_primeIdealOf x
    have e2 := hU.fromSpec_preimage_basicOpen f
    have : hU.primeIdealOf x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x.1 ∈ X.basicOpen f := by
      rw [← e1]; rfl
    rw [← this, e2]; rfl
  have e : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩ := by
    apply PrimeSpectrum.ext
    ext f
    rw [← not_iff_not, key, key]
    exact h f
  have e1 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  have e2 := hU.fromSpec_primeIdealOf ⟨z', hz'⟩
  rw [e] at e1
  exact e1.symm.trans e2

theorem point_eq_of_inv_mem_iff :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z z' : M.Z, z ∈ U → z' ∈ U → (∀ a ∈ M.ringOn (U : Set M.Z), a ≠ 0 → (a⁻¹ ∈ M.O z ↔ a⁻¹ ∈ M.O z')) → z = z' := by
  intro o Ω _ _ _ M U hU z z' hz hz' h
  refine eq_of_forall_mem_basicOpen_iff hU hz hz' fun f => ?_
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have ha : valF M.pt U f ∈ M.ringOn U := (mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩
  rw [← isUnit_valF_iff hz f, ← isUnit_valF_iff hz' f, isUnit_O_iff, isUnit_O_iff]
  exact and_congr_right fun h0 => h _ ha h0

end GlobalTheory.Points
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingEssFiniteTypeInt
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

theorem essFiniteType_int_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  intro o Ω _ _ _ hA M x
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o := M.s x
  letI A : Algebra o ((Sp o).presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o _ ((Sp o).presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o ((Sp o).presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o := hA.ft
  have h₀ : (algebraMap ℤ o).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h₃ : (M.stalkEquiv x).toRingHom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (M.stalkEquiv x).surjective).essFiniteType
  have h := ((h₀.comp h₂).comp h₁)
  have h' := h.comp h₃
  rw [← RingHom.essFiniteType_algebraMap]
  convert h'
  exact RingHom.ext_int _ _

end GlobalTheory.Izumi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingResidueFieldFiniteOfClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.ResFin

theorem finite_residueField_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), IsClosed ({x} : Set M.Z) → Finite (ResidueField (M.O x)) := by
  intro o Ω _ _ _ hA M x hx
  haveI : Algebra.FiniteType ℤ o := hA.ft
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  haveI : LocallyOfFiniteType M.s := M.lft
  have h := finite_residueField_of_isClosed_of_locallyOfFiniteType_int (M.s ≫ spMap (algebraMap ℤ o)) x hx
  haveI : Finite (ResidueField (M.Z.presheaf.stalk x)) := h
  exact Finite.of_equiv _ (ResidueField.mapEquiv (M.stalkEquiv x)).toEquiv

end GlobalTheory.ResFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularityOfDensity
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.Modif

theorem isTest_comp (p : ℕ) [Fact p.Prime] {X X' : Scheme.{0}} (π : X' ⟶ X) (Xw : X.Opens)
    (yb' : Sp 𝓞_ℂ_[p] ⟶ X') (h : IsTest p (π ⁻¹ᵁ Xw) yb') : IsTest p Xw (yb' ≫ π) := by
  obtain ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ π, hT, hk, by rw [← Category.assoc, e]⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  have : (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb') z ∈ π ⁻¹ᵁ Xw := hr ⟨z, rfl⟩
  simpa [Scheme.Hom.comp_apply] using this

theorem preimage_basicOpen_p (p : ℕ) {X X' : Scheme.{0}} (π : X' ⟶ X) :
    π ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) = X'.basicOpen (p : Γ(X', ⊤)) := by
  rw [Scheme.preimage_basicOpen, map_natCast]
  rfl

end GlobalTheory.FlatModel.Modif

namespace GlobalTheory.FlatModel

open Modif

theorem modSt_of_densSt : DensSt → ModSt := by
  intro hD F _ _ V p _ hp X s Xw hXi hXn hXp hXf hXw hGI n K hK hC
  have hDVR := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V (Fact.out : p.Prime).ne_zero hp).1
  have : LocallyOfFiniteType s := by
    obtain ⟨N, i, hi, rfl⟩ := hXp
    have := isProper_str V N
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := by
    obtain ⟨N, i, hi, rfl⟩ := hXp
    have := isProper_str V N
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str V N)
  choose R _ ξ J _ Q u hξ hx hcl using hC
  haveI : ∀ x, IsOpenImmersion (ξ x) := hξ
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => ((ξ x).opensRange : Set X))
    fun x => (ξ x).opensRange.isOpen.mem_nhds (by simpa using hx x)
  choose e he using fun x => GlobalTheory.T.open_immersion_ring_factor X (R x) (ξ x)
  let U : t → X.Opens := fun j => (ξ j.1).opensRange
  let m : t → ℕ := fun j => Nat.card (J j.1) + 1
  let A : ∀ j : t, Fin (m j) → Γ(X, U j) := fun j =>
    Fin.cons ((p : Γ(X, U j)) ^ n) fun i => e j.1 (Q j.1 ((Finite.equivFin (J j.1)).symm i))
  obtain ⟨Jd, hJd, hPr⟩ := GlobalTheory.HTLine.princ_of_finite X p U m A (fun j => isAffineOpen_opensRange (ξ j.1))
    fun j => ⟨n, Ideal.subset_span ⟨0, rfl⟩⟩
  obtain ⟨X'', X', b, ν, hEff, hI', hN', hP', hF', hpr, hiso⟩ := GlobalTheory.T.exists_blowup_normalization_cartier F V p hp X s hXi hXn hXp hXf Jd hJd
  have hT : ∀ yb', IsTest p ((ν ≫ b) ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ (ν ≫ b)) := isTest_comp p (ν ≫ b) Xw
  have hle : (ν ≫ b) ⁻¹ᵁ Xw ≤ X'.basicOpen (p : Γ(X', ⊤)) := by
    rw [← preimage_basicOpen_p p (ν ≫ b)]
    exact fun x hx => hXw hx
  have : LocallyOfFiniteType (ν ≫ b ≫ s) := by
    obtain ⟨N, i, hi, e'⟩ := hP'
    have := isProper_str V N
    rw [← e']
    infer_instance
  refine ⟨X', ν ≫ b ≫ s, (ν ≫ b) ⁻¹ᵁ Xw, fun yb' => K (yb' ≫ (ν ≫ b)), hI', hN', hP', hF', hle, ?_,
    fun yb' h => hK _ (hT yb' h), ?_, fun yb h => ?_⟩
  · have := GlobalTheory.T.geometrically_irreducible_pullback_iso V X X' s (ν ≫ b) Xw _ hXw hiso hGI
    simpa only [Category.assoc] using this
  · intro x'
    by_cases hx' : x' ∈ X'.basicOpen (p : Γ(X', ⊤))
    · exact GlobalTheory.T.unit_chart_at_invertible_p p X' _ _ x' hx'
    have hmem : (ν ≫ b) x' ∈ ⋃ x ∈ t, ((ξ x).opensRange : Set X) := by rw [ht]; exact Set.mem_univ _
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x, hxt, hfx⟩ := hmem
    obtain ⟨V', hV', hxV', hVa, k, hk⟩ := hPr X'' X' b ν hEff x' ⟨x, hxt⟩ hfx
    have heq := he x X' (ν ≫ b) V' hVa hV'
    refine GlobalTheory.T.localization_units_charts p n X X' (ν ≫ b) Xw K (R x) (ξ x) (J x) (Q x) (u x) (hcl x) hT Γ(X', V') hVa.fromSpec
      _ x' inferInstance (by rw [hVa.range_fromSpec]; exact hxV') heq
      (fun hne => hD F V p hp X' (ν ≫ b ≫ s) _ hI' hF' inferInstance hle hne Γ(X', V') hVa.fromSpec inferInstance
        ⟨x', by rw [hVa.range_fromSpec]; exact hxV', hx'⟩) ?_
    have hA0 : ((ν ≫ b).appLE (ξ x).opensRange V' hV').hom ((p : Γ(X, (ξ x).opensRange)) ^ n) =
        (p : Γ(X', V')) ^ n := by rw [map_pow, map_natCast]
    revert hk
    refine Fin.cases (fun hk => Or.inr fun j => ?_) (fun i hk => Or.inl ⟨(Finite.equivFin (J x)).symm i,
      fun j => ?_, ?_⟩) k
    · have := hk ((Finite.equivFin (J x)) j).succ
      simpa [A, U, hA0] using this
    · have := hk ((Finite.equivFin (J x)) j).succ
      simpa [A, U] using this
    · have := hk 0
      simpa [A, U, hA0] using this
  · obtain ⟨yb', h1, h2⟩ := GlobalTheory.T.test_point_lift_proper p X X' (ν ≫ b) hpr Xw _ hXw hiso yb h
    exact ⟨yb', h1, fun κ hκ => by show κ ∈ K (yb' ≫ (ν ≫ b)); rw [h2]; exact hκ⟩

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLawsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundleIso_normalised_respects_laws : ∀ (S S' : Scheme.{0}) (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : RigLB B) (M' : RigLB B') (c : CubicalStr B M) (c' : CubicalStr B' M') (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M'.L) ((abelian₂ B M.L).pull β₂)) (hβ : IsGrpPullback B' B f β), IsAbelianScheme B' → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (x x' y : T ⟶ B') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' ∧ ∀ (u u' v : Over.mk (T.hom ≫ f) ⟶ B), u.left = x.left ≫ β → u'.left = x'.left ≫ β → v.left = y.left ≫ β → lamVal w (lift (x * x') y).left z J J' * cubV c' z J' x x' y = @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J u u' v) * lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' := by
  first | exact @GlobalTheory.LamRigid.lam_iso_laws | exact GlobalTheory.LamRigid.lam_iso_laws | (intros; apply GlobalTheory.LamRigid.lam_iso_laws <;> assumption)
end

