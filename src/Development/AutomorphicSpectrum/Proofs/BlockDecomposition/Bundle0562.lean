import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.UnitaryBC PositivityTheory.PRW.GKD

namespace GlobalTheory.CompanionTheory.TwistNorm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem val_expId (ω : HChar E) (t : ℝ) :
    ((ω.1 (GlobalTheory.DiscChar.expId E t) : ℂˣ) : ℂ) = Complex.exp (t * dchi ω 1) := by
  refine (chiInf_expU ω _).trans (congrArg _ ?_)
  rw [show (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) from funext fun _ => by simp, map_smul]
  simp

theorem isNormalised_rank_zero (π : CuspSub E 0) : IsNormalised π := fun φ _ t g => by
  rw [Subsingleton.elim (splitCentre E 0 t * g) g]

theorem isNormalised_twist {π : CuspSub E a} {ω ν : HChar E} (hω : π.HasCentral ω)
    (hν : ∀ t : ℝ, ((chiDet a ν (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (-(t * dchi ω 1))) :
    IsNormalised (π.twist ν) := by
  rintro _ ⟨ψ, hψ, rfl⟩ t g
  change ψ.1 (splitCentre E a t * g) * (chiDet a ν (splitCentre E a t * g) : ℂˣ) = ψ.1 g * (chiDet a ν g : ℂˣ)
  have h1 : ψ.1 (splitCentre E a t * g) = Complex.exp (t * dchi ω 1) * ψ.1 g := by
    rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar, hω.apply hψ]
    exact congrArg (· * ψ.1 g) (val_expId ω t)
  rw [h1, map_mul, Units.val_mul, hν, mul_mul_mul_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem exists_twist_normalised : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a),
    ∃ (π₀ : CuspSub E a) (χ : HChar E), IsNormalised π₀ ∧ π = π₀.twist χ := by
  intro E _ _ _ a π
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨π, 1, isNormalised_rank_zero π, π.twist_one.symm⟩
  · obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitCentreChar.exists_hChar_splitCentre E a ha (dchi ω 1)
    refine ⟨π.twist ν, ν⁻¹, isNormalised_twist hω hν, ?_⟩
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]

end GlobalTheory.CompanionTheory.TwistNorm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatio
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ

theorem ev_dehomog_of_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    ∀ (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder w z → w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) →
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c f) w =
      eval z (map (Int.castRingHom ℂ) f) / ∏ k, z ⟨k, c k⟩ ^ a k := by
  intro m n c f a hf w z H hw
  have hmem : ∀ k, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) := fun k =>
    GlobalTheory.CxPts.ptsIn_mono (mchart_le c k) hw
  have hX : ∀ q, GlobalTheory.CxPts.evHom hw (dehomog c (X q)) = z q / z ⟨q.1, c q.1⟩ := by
    rintro ⟨k, i⟩
    rw [← GlobalTheory.CxPts.ev_eq hw]
    simp only [dehomog, coe_eval₂Hom, eval₂_X]
    rw [GlobalTheory.CxPts.ev_res _ hw]
    exact (H k (c k)).2 i (hmem k)
  have hφ : (GlobalTheory.CxPts.evHom hw).comp (dehomog c) =
      eval₂Hom (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · simp
    · simpa using hX q
  have hv : GlobalTheory.CxPts.evHom hw (dehomog c f) =
      eval₂ (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) f := by
    simpa using congrArg (fun φ => φ f) hφ
  rw [GlobalTheory.CxPts.ev_eq hw, hv, MvPolynomial.eval_map, eval₂_eq', eval₂_eq', Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  have hden : ∏ q : Σ k, Bk n k, z ⟨q.1, c q.1⟩ ^ e q = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Bk n k => e ⟨k, i⟩) (z ⟨k, c k⟩)).trans (by rw [hf e he k])
  simp only [div_pow, Finset.prod_div_distrib, hden]
  rw [mul_div_assoc]

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnEvProd
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.Ar.ProdHolo

variable {k : Type} [CommRing k] {Z X : Scheme.{0}} {q : Z ⟶ Sp k} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem mem_ptsIn_preimage {π : Z ⟶ X} {z : CxPts q σ} {x : CxPts p σ} (h : z.1 ≫ π = x.1)
    {U : X.Opens} (hx : x ∈ ptsIn p σ U) : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := by
  rw [mem_ptsIn] at hx ⊢
  rw [← h] at hx
  exact hx

theorem ev_appLE {π : Z ⟶ X} {z : CxPts q σ} {x : CxPts p σ} (h : z.1 ≫ π = x.1)
    {U : X.Opens} {W : Z.Opens} (e : W ≤ π ⁻¹ᵁ U) (hz : z ∈ ptsIn q σ W)
    (a : Γ(X, U)) :
    CxPts.ev q σ W ((π.appLE U W e).hom a) z = CxPts.ev p σ U a x := by
  have h1 := GlobalTheory.CxPts.ev_res (p := q) (σ := σ) e hz ((π.app U).hom a)
  refine Eq.trans ?_ (h1.trans ?_)
  · rfl
  · have h2 := GlobalTheory.Points.valR_comp z.1 π U a
    rw [h] at h2
    exact h2.symm

theorem differentiableOn_ev_prod : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (σ : k →+* ℂ) {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] (T : Set E) (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V →
  ∀ (s₁ : E → CxPts f σ) (s₂ : E → CxPts g σ) (s : E → CxPts (pullback.fst f g ≫ f) σ),
  (∀ v, (s v).1 ≫ pullback.fst f g = (s₁ v).1) → (∀ v, (s v).1 ≫ pullback.snd f g = (s₂ v).1) →
  (∀ v ∈ T, s₁ v ∈ ptsIn f σ U) → (∀ v ∈ T, s₂ v ∈ ptsIn g σ V) →
  (∀ a : Γ(X, U), DifferentiableOn ℂ (CxPts.ev f σ U a ∘ s₁) T) →
  (∀ b : Γ(Y, V), DifferentiableOn ℂ (CxPts.ev g σ V b ∘ s₂) T) →
  IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
  (∀ v ∈ T, s v ∈ ptsIn (pullback.fst f g ≫ f) σ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) ∧
  ∀ t : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
    DifferentiableOn ℂ (CxPts.ev (pullback.fst f g ≫ f) σ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) t ∘ s) T := by
  intro k _ X Y f g σ E _ _ T U V hU hV s₁ s₂ s h₁ h₂ m₁ m₂ d₁ d₂
  have H := IsPullback.of_hasPullback f g
  obtain ⟨hW, po⟩ := GlobalTheory.Conormal.isAffineOpen_and_isPushout H (U := ⊤) (T₀ := V) (W := U)
    (isAffineOpen_top _) hV hU le_top le_top
  have hin : ∀ v ∈ T, s v ∈ ptsIn (pullback.fst f g ≫ f) σ
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := fun v hv =>
    mem_ptsIn_inf.2 ⟨mem_ptsIn_preimage (h₁ v) (m₁ v hv), mem_ptsIn_preimage (h₂ v) (m₂ v hv)⟩
  refine ⟨hW, hin, fun t => ?_⟩
  have ht : t ∈ Subring.closure (Set.range (pullback.fst f g |>.appLE U
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_left).hom ∪
      Set.range (pullback.snd f g |>.appLE V
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_right).hom) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout po]
    trivial
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact (d₁ a).congr fun v hv => ev_appLE (h₁ v) _ (hin v hv) a
    · exact (d₂ b).congr fun v hv => ev_appLE (h₂ v) _ (hin v hv) b
  | zero =>
    exact (differentiableOn_const 0).congr fun v hv => by
      simp only [Function.comp_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_zero]
  | one =>
    exact (differentiableOn_const 1).congr fun v hv => by
      simp only [Function.comp_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_one]
  | add x y _ _ hx hy =>
    exact (hx.add hy).congr fun v hv => by
      simp only [Function.comp_apply, Pi.add_apply, GlobalTheory.CxPts.ev_add]
  | neg x _ hx =>
    exact hx.neg.congr fun v hv => by
      simp only [Function.comp_apply, Pi.neg_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_neg]
  | mul x y _ _ hx hy =>
    exact (hx.mul hy).congr fun v hv => by
      simp only [Function.comp_apply, Pi.mul_apply, GlobalTheory.CxPts.ev_mul]

end GlobalTheory.CompanionTheory.Ar.ProdHolo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnEvPtP
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem differentiableOn_eval₂_ratio (N : ℕ) (c : Fin (N + 1))
    (p : MvPolynomial {j : Fin (N + 1) // j ≠ c} ℤ) :
    DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ =>
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : {j // j ≠ c} => w j.1 / w c) p)
      {w | w c ≠ 0} := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact differentiableOn_const _
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at hp ⊢
    have hj : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => w j.1) {w | w c ≠ 0} :=
      (differentiable_apply j.1).differentiableOn
    have hc : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => w c) {w | w c ≠ 0} :=
      (differentiable_apply c).differentiableOn
    have hinv : DifferentiableOn ℂ (fun w : Fin (N + 1) → ℂ => (w c)⁻¹) {w | w c ≠ 0} :=
      fun w hw => (hc w hw).inv hw
    simp only [div_eq_mul_inv]
    exact hp.mul (hj.mul hinv)

theorem differentiableOn_ev_ptP (N : ℕ) (c : Fin (N + 1)) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    DifferentiableOn ℂ (fun w => CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w))
      {w | w c ≠ 0} := by
  have h : (fun w => CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w)) =
      fun w : Fin (N + 1) → ℂ => MvPolynomial.eval₂Hom (Int.castRingHom ℂ)
        (fun j : {j // j ≠ c} => w j.1 / w c) ((chartAlgEquiv ℤ N c).symm a) := by
    funext w
    exact CxPts.ev_ofHom _ _ _ a
  rw [h]
  exact differentiableOn_eval₂_ratio N c _

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnPhi
section
open MeasureTheory Complex Filter Topology
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

noncomputable def maj (σ t : ℝ) : ℝ := (1 + ‖t‖ ^ 2) ^ (-σ / 2)

theorem integrable_maj {σ : ℝ} (h : 1 < σ) : Integrable (maj σ) := by
  have : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < σ := by simpa using h
  exact integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) this

theorem maj_nonneg (σ t : ℝ) : 0 ≤ maj σ t := by
  unfold maj; positivity

theorem maj_anti {σ τ : ℝ} (h : σ ≤ τ) (t : ℝ) : maj τ t ≤ maj σ t := by
  unfold maj
  apply Real.rpow_le_rpow_of_exponent_le
  · nlinarith [sq_nonneg ‖t‖]
  · linarith

theorem norm_KK (a b : ℝ) (s : ℂ) (t : ℝ) :
    ‖KK (s / 2 + a) (s / 2 + b) 1 t‖ = maj (s.re + a + b) t := by
  set w : ℂ := 1 + I * t with hw
  have hc : (1 : ℂ) - I * t = (starRingEnd ℂ) w := by simp [hw, sub_eq_add_neg]
  have hwre : w.re = 1 := by simp [hw]
  have hw0 : w ≠ 0 := by intro h; simp [h] at hwre
  have hc0 : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).2 hw0
  have hn : ‖w‖ ^ 2 = 1 + ‖t‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hw]
    ring
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hargpi : arg w ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.1 h).1
    linarith
  have harg : arg ((starRingEnd ℂ) w) = - arg w := by
    rw [Complex.arg_conj, if_neg hargpi]
  unfold KK maj
  rw [norm_mul, Complex.ofReal_one, hc, ← hw, norm_cpow_of_ne_zero hc0, norm_cpow_of_ne_zero hw0,
    Complex.norm_conj, harg, ← hn]
  have e1 : (-(s / 2 + (a : ℂ))).re = -(s.re / 2 + a) := by simp
  have e2 : (-(s / 2 + (b : ℂ))).re = -(s.re / 2 + b) := by simp
  have e3 : (-(s / 2 + (a : ℂ))).im = -(s.im / 2) := by simp
  have e4 : (-(s / 2 + (b : ℂ))).im = -(s.im / 2) := by simp
  rw [e1, e2, e3, e4]
  rw [← Real.rpow_natCast ‖w‖ 2, ← Real.rpow_mul hpos.le]
  have e5 : ((2 : ℕ) : ℝ) * (-(s.re + a + b) / 2) = -(s.re / 2 + a) + -(s.re / 2 + b) := by
    push_cast; ring
  rw [e5, Real.rpow_add hpos]
  field_simp
  rw [← Real.exp_add]
  simp

theorem norm_ee (ξ t : ℝ) : ‖ee (-((ξ : ℂ) * t))‖ = 1 := by
  unfold ee
  have : 2 * (Real.pi : ℂ) * I * (-((ξ : ℂ) * t)) = ((-(2 * Real.pi * ξ * t) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem continuous_ee (ξ : ℝ) : Continuous fun t : ℝ => ee (-((ξ : ℂ) * t)) := by
  unfold ee; fun_prop

theorem continuous_ee' (t : ℝ) : Continuous fun ξ : ℝ => ee (-((ξ : ℂ) * t)) := by
  unfold ee; fun_prop

theorem continuous_KK (α β : ℂ) : Continuous fun t : ℝ => KK α β 1 t := by
  unfold KK
  refine Continuous.mul ?_ ?_
  · refine Continuous.cpow (by fun_prop) continuous_const fun t => ?_
    left; simp
  · refine Continuous.cpow (by fun_prop) continuous_const fun t => ?_
    left; simp

theorem differentiable_KK (a b t : ℝ) :
    Differentiable ℂ fun s : ℂ => KK (s / 2 + a) (s / 2 + b) 1 t := by
  have h1 : ((1 : ℝ) : ℂ) - I * t ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 : ((1 : ℝ) : ℂ) + I * t ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  unfold KK
  refine Differentiable.mul ?_ ?_
  · exact Differentiable.const_cpow (by fun_prop) (Or.inl h1)
  · exact Differentiable.const_cpow (by fun_prop) (Or.inl h2)

theorem norm_integrand (a b : ℝ) (s : ℂ) (ξ t : ℝ) :
    ‖KK (s / 2 + a) (s / 2 + b) 1 t * ee (-((ξ : ℂ) * t))‖ = maj (s.re + a + b) t := by
  rw [norm_mul, norm_KK, norm_ee, mul_one]

theorem integrable_KK (a b : ℝ) {s : ℂ} (h : 1 < s.re + a + b) :
    Integrable fun t => KK (s / 2 + a) (s / 2 + b) 1 t :=
  (integrable_maj h).mono' (continuous_KK _ _).aestronglyMeasurable
    (Eventually.of_forall fun t => (norm_KK a b s t).le)

theorem differentiableOn_Phi (a b ξ : ℝ) :
    DifferentiableOn ℂ (fun s : ℂ => Phi (s / 2 + a) (s / 2 + b) ξ) (HP (1 - a - b)) := by
  have hU : IsOpen (HP (1 - a - b)) := isOpen_lt continuous_const Complex.continuous_re
  refine (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := (volume : Measure ℝ))
    (F := fun t s => KK (s / 2 + a) (s / 2 + b) 1 t * ee (-((ξ : ℂ) * t))) hU ?_ ?_ ?_).1
  · intro y _
    exact ((continuous_KK _ _).mul (continuous_ee ξ)).aestronglyMeasurable
  · refine Eventually.of_forall fun t => ?_
    exact ((differentiable_KK a b t).mul_const _).differentiableOn
  · intro x hx
    have hx' : 1 - a - b < x.re := hx
    refine ⟨{y | (x.re + a + b + 1) / 2 < y.re + a + b}, ?_, maj ((x.re + a + b + 1) / 2),
      integrable_maj (by linarith), Eventually.of_forall fun t y hy => ?_⟩
    · refine (isOpen_lt continuous_const (by fun_prop)).mem_nhds ?_
      show (x.re + a + b + 1) / 2 < x.re + a + b
      linarith
    · rw [norm_integrand]
      exact maj_anti (le_of_lt hy) t

theorem continuous_Phi (a b : ℝ) {s : ℂ} (h : 1 < s.re + a + b) :
    Continuous fun ξ : ℝ => Phi (s / 2 + a) (s / 2 + b) ξ := by
  unfold Phi
  refine continuous_of_dominated (bound := maj (s.re + a + b)) (fun ξ => ?_) (fun ξ => ?_)
    (integrable_maj h) ?_
  · exact ((continuous_KK _ _).mul (continuous_ee ξ)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => (norm_integrand a b s ξ t).le
  · exact Eventually.of_forall fun t => continuous_const.mul (continuous_ee' t)

theorem norm_Phi_le (a b : ℝ) {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (h : σ ≤ s.re + a + b) (ξ : ℝ) :
    ‖Phi (s / 2 + a) (s / 2 + b) ξ‖ ≤ ∫ t, maj σ t := by
  unfold Phi
  refine norm_integral_le_of_norm_le (integrable_maj hσ) (Eventually.of_forall fun t => ?_)
  rw [norm_integrand]
  exact maj_anti h t

theorem w0 : W0 := by
  intro a b
  refine ⟨fun ξ => differentiableOn_Phi a b ξ, fun s hs => ?_, fun δ B hδ => ?_⟩
  · have hs' : 1 - a - b < s.re := hs
    have h : 1 < s.re + a + b := by linarith
    exact ⟨integrable_KK a b h, continuous_Phi a b h⟩
  · have hC : 0 ≤ ∫ t, maj (1 + δ) t := integral_nonneg fun t => maj_nonneg _ t
    refine ⟨∫ t, maj (1 + δ) t, fun s ξ h1 _ => ?_⟩
    refine (norm_Phi_le a b (σ := 1 + δ) (by linarith) (by linarith) ξ).trans ?_
    refine le_mul_of_one_le_right hC ?_
    exact Real.one_le_exp (by positivity)

end GlobalTheory.CompanionTheory.HalfWeight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHermitianIntegralUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.NegStep

theorem integral_neg_of_secondCountable {G E : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure G) [μ.IsAddHaarMeasure] (f : G → E) :
    ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  have : μ.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μ
  exact integral_neg_eq_self f μ

theorem colJoin_zero_mul {R : Type*} [NonUnitalNonAssocSemiring R] {m r s : ℕ} (p : Matrix (Fin m) (Fin r) R)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) R) (c : Matrix (Fin r) (Fin (r + s)) R)
    (h : ∀ j : Fin r, a (Fin.castAdd s j) = c j) :
    colJoin p (0 : Matrix (Fin m) (Fin s) R) * a = p * c := by
  ext i k
  simp [Matrix.mul_apply, Fin.sum_univ_add, h]

theorem inner_neg_neg {D : D7} (V : HSp D) {n : ℕ} (t : Mx D V.rank n) : inner V (-t) (-t) = inner V t t := by
  unfold GlobalTheory.StdUnn.inner
  rw [adj_neg]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem integral_colJoin_neg_eq_J : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (r s : ℕ) (μr : Measure (Mx D V.rank r))
    (𝓕r : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μr 𝓕r →
    ∀ (c : Matrix (Fin r) (Fin (r + s)) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsCompl c a →
    ∀ (b : HermE D r) (Φ : Mx D V.rank (r + s) → ℂ),
      ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr = J ψ V μr (pull c Φ) b := by
  intro D ψ V r s μr 𝓕r hcov c a hca b Φ
  obtain ⟨h1, h2, h3, h4, -⟩ := lattice_Mx D V.rank r
  have hB : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have hH : μr.IsAddHaarMeasure := hcov.1
  have hrow : ∀ j : Fin r, rat a (Fin.castAdd s j) = rat c j := by
    intro j
    have := hca.2 (Fin.castAdd s j) j.isLt
    funext k
    show incA D (a (Fin.castAdd s j) k) = incA D (c j k)
    rw [this]
    rfl
  have key : ∀ t : Mx D V.rank r,
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) =
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))) (-t) := by
    intro t
    have e : (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a) : Mx D V.rank (r + s)) = HMul.hMul (-t) (rat c) :=
      colJoin_zero_mul (-t) (rat a) (rat c) hrow
    show _ = Φ (HMul.hMul (-t) (rat c)) * _
    rw [e, inner_neg_neg, mul_comm]
  exact (integral_congr_ae (Filter.Eventually.of_forall key)).trans
    (integral_neg_of_secondCountable (E := ℂ) μr
      (fun y : Mx D V.rank r => pull c Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (rat b.1) (inner V y y) : Mx D r r)))))

end GlobalTheory.CompanionTheory.EisUnfold.NegStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAnalyticIsoOfIsAnalyticUniformization
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticUniformization

theorem exists_analyticIso_of_isAnalyticUniformization (Λ : Submodule ℤ ℂ)
    (E : WeierstrassCurve ℂ) (f : ℂ →+ E.toAffine.Point)
    (hf : GroundTheory.Global.Elliptic.IsAnalyticUniformization Λ f) :
    ∃ ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point,
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := by
  let φ : (ℂ ⧸ Λ.toAddSubgroup) →+ E.toAffine.Point :=
    QuotientAddGroup.lift Λ.toAddSubgroup f fun z hz => (hf.map_eq_zero_iff z).2 hz
  have hφ : ∀ z : ℂ, φ (QuotientAddGroup.mk z) = f z := fun z => rfl
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hφ] at hx
    exact (QuotientAddGroup.eq_zero_iff z).2 ((hf.map_eq_zero_iff z).1 hx)
  have hsurj : Function.Surjective φ := fun P => by
    obtain ⟨z, rfl⟩ := hf.surjective P
    exact ⟨QuotientAddGroup.mk z, hφ z⟩
  let ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point :=
    AddEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hξ : ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := fun z => rfl
  refine ⟨ξ, fun z hz => ?_, hξ⟩
  have hz0 : f z ≠ 0 := fun h => hz ((hf.map_eq_zero_iff z).1 h)
  obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine z hz0
  refine ⟨X, Y, hX, hY, hev.mono fun w hw => ?_⟩
  obtain ⟨h, hw⟩ := hw
  exact ⟨h, (hξ w).trans hw⟩

end GlobalTheory.CompanionTheory.EllipticUniformization
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegTestFunctionNearOneStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonneg_test_function_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧ IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv | exact GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.exists_bump_conjInv <;> assumption)
end

