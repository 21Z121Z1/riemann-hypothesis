import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleConjugateUnipotentTranslate
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0553
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0547
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleConjugateUnipotentTranslateStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_semisimple_conjugate_unipotent_translate : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (δ : GF V), IsRegSS δ.1.1 → δ ∈ (frameFlag hC).parRat D.sp.cm → ∀ ν ∈ (frameFlag hC).unipRat D.sp.cm,
      ∃ g : GF V, g * δ * g⁻¹ = δ * ν := by
  first | exact @GlobalTheory.CompanionTheory.ParabConj.conj_translate | exact GlobalTheory.CompanionTheory.ParabConj.conj_translate | (intros; apply GlobalTheory.CompanionTheory.ParabConj.conj_translate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
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

namespace GlobalTheory.CompanionTheory.MixZ.FnForm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG_apply {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

def chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (mchart c) x hx).hom
    (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2))

theorem ptCoord_eq_mul_chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    ptCoord x p = ptCoord x ⟨p.1, c p.1⟩ * chartCoord c x hx p := by
  obtain ⟨k, j⟩ := p
  let P : MP ℤ m n ⟶ PSpace ℤ (n k) := prB n k
  let W₀ : (MP ℤ m n).Opens := blockChart n k (ptChart x k)
  let W₁ : (MP ℤ m n).Opens := blockChart n k (c k)
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := le_rfl
  have hx₀ : x ∈ W₀ := mem_ptChart x k
  have hx₁ : x ∈ W₁ := mchart_le c k hx
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right.trans h₁
  have e₀ : ∀ l : Bk n k, ptCoord x ⟨k, l⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (ptChart x k) hV₀ l) := by
    intro l
    show ((MP ℤ m n).evaluation W₀ x hx₀).hom (pullRatio P W₀ (ptChart x k) h₀ l) = _
    rw [← evaluation_resG_apply (inf_le_left : V ≤ W₀) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₀) inf_le_left)
  have e₁ : chartCoord c x hx ⟨k, j⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (c k) hV₁ j) := by
    show ((MP ℤ m n).evaluation (mchart c) x hx).hom (resG _ (mchart_le c k) (pullRatio P W₁ (c k) h₁ j)) = _
    rw [evaluation_resG_apply, ← evaluation_resG_apply (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  show ptCoord x ⟨k, j⟩ = ptCoord x ⟨k, c k⟩ * chartCoord c x hx ⟨k, j⟩
  rw [e₀ j, e₀ (c k), e₁, ← map_mul]
  exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := j)).symm

theorem evaluation_dehomog (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (f : Pol n) :
    ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) = aeval (chartCoord c x hx) f := by
  have e : ((MP ℤ m n).evaluation (mchart c) x hx).hom.comp (dehomog c) =
      (aeval (chartCoord c x hx) : Pol n →ₐ[ℤ] _).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp [dehomog, chartCoord])
  exact congrArg (fun φ => φ f) e

theorem aeval_ptCoord_eq_mul (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) {f : Pol n}
    {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) :
    aeval (ptCoord x) f = (∏ k, ptCoord x ⟨k, c k⟩ ^ a k) *
      ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) := by
  rw [evaluation_dehomog, ← GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.aeval_smul hf]
  exact congrArg (fun v => aeval v f) (funext (ptCoord_eq_mul_chartCoord c x hx))

theorem fnAt_ne_zero_of_notMem_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  intro m n X _ i _ c h f a hf hnot h0
  refine hnot ((mem_ptIdeal_iff_aeval_ptCoord m n _ f a hf).2 ?_)
  have hx : i (genericPoint X) ∈ mchart c := h
  have h1 : i.app (mchart c) (dehomog c f) = 0 :=
    fnOf_injective _ h (h0.trans (map_zero _).symm)
  have h2 : ((MP ℤ m n).evaluation (mchart c) _ hx).hom (dehomog c f) = 0 := by
    apply (i.residueFieldMap (genericPoint X)).hom.injective
    rw [map_zero]
    refine (Scheme.evaluation_naturality_apply i (genericPoint X) hx _).trans ?_
    rw [h1, map_zero]
  rw [aeval_ptCoord_eq_mul c _ hx hf, h2, mul_zero]

end GlobalTheory.CompanionTheory.MixZ.FnForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootCountEqCardZmod
section
open Finset

namespace GlobalTheory.CompanionTheory.SquareRootCount

def rootCount (n : ℤ) (e : ℕ) : ℕ :=
  ((range e).filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card

noncomputable def addCharAt (d : ℕ) (t : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (d : ℂ))

noncomputable def rootSum (n : ℤ) (d : ℕ) : ℂ :=
  ∑ x ∈ range d, ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d),
    addCharAt d ((r : ℤ) * ((x : ℤ) ^ 2 - n))

theorem geom_addChar {e : ℕ} (he : 0 < e) (m : ℤ) :
    ∑ r ∈ range e, addCharAt e ((r : ℤ) * m) = if (e : ℤ) ∣ m then (e : ℂ) else 0 := by
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (e : ℂ))) e :=
    Complex.isPrimitiveRoot_exp e he.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (e : ℂ)) with hζ
  have hterm : ∀ r : ℕ, addCharAt e ((r : ℤ) * m) = (ζ ^ m) ^ r := by
    intro r
    rw [← zpow_natCast, ← zpow_mul, hζ, ← Complex.exp_int_mul]
    unfold addCharAt
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  split_ifs with h
  · rw [(hprim.zpow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hprim.zpow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1]
    have : (ζ ^ m) ^ e = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    simp [this]

theorem count_periodic (n : ℤ) (e k : ℕ) :
    ((range (e * k)).filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card = k * rootCount n e := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : ∀ s : Finset ℕ, (s.filter fun x : ℕ => (e : ℤ) ∣ (x : ℤ) ^ 2 - n).card
        = ∑ x ∈ s, if (e : ℤ) ∣ (x : ℤ) ^ 2 - n then 1 else 0 := fun s => by
      rw [card_filter]
    rw [hs] at ih ⊢
    rw [Nat.mul_succ, sum_range_add, ih, Nat.succ_mul]
    congr 1
    unfold rootCount
    rw [hs]
    refine sum_congr rfl fun x _ => ?_
    have : (e : ℤ) ∣ (((e * k + x : ℕ) : ℤ)) ^ 2 - n ↔ (e : ℤ) ∣ (x : ℤ) ^ 2 - n := by
      have hd : (e : ℤ) ∣ (((e * k + x : ℕ) : ℤ)) ^ 2 - (x : ℤ) ^ 2 :=
        ⟨k * (e * k + 2 * x), by push_cast; ring⟩
      constructor
      · intro h
        have := dvd_sub h hd
        simpa using this
      · intro h
        have := dvd_add h hd
        simpa using this
    simp only [this]

theorem sum_moebius_divisors {m : ℕ} (hm : m ≠ 0) :
    ∑ g ∈ m.divisors, ArithmeticFunction.moebius g = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

theorem sum_coprime_eq {d : ℕ} (hd : 0 < d) (f : ℕ → ℂ) :
    ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d), f r
      = ∑ g ∈ d.divisors, (ArithmeticFunction.moebius g : ℂ) * ∑ r ∈ range (d / g), f (g * r) := by
  have hind : ∀ r : ℕ, (if Nat.Coprime r d then f r else 0)
      = ∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) * f r else 0 := by
    intro r
    have hg : Nat.gcd r d ≠ 0 := Nat.gcd_ne_zero_right hd.ne'
    have hdiv : (Nat.gcd r d).divisors = d.divisors.filter (· ∣ r) := by
      ext g
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩
        exact ⟨⟨h2, hd.ne'⟩, h1⟩
      · rintro ⟨⟨h2, -⟩, h1⟩
        exact ⟨⟨h1, h2⟩, hg⟩
    have h := sum_moebius_divisors hg
    rw [hdiv, sum_filter] at h
    have h' : (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) else 0)
        = if Nat.Coprime r d then 1 else 0 := by
      have := congrArg (fun z : ℤ => (z : ℂ)) h
      simp only [Int.cast_sum] at this
      simp only [apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, Int.cast_one] at this
      exact this
    have h'' : (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) * f r else 0)
        = (∑ g ∈ d.divisors, if g ∣ r then (ArithmeticFunction.moebius g : ℂ) else 0) * f r := by
      rw [sum_mul]
      refine sum_congr rfl fun g _ => ?_
      split_ifs <;> simp
    rw [h'', h']
    split_ifs <;> simp
  rw [sum_filter]
  simp_rw [hind]
  rw [sum_comm]
  refine sum_congr rfl fun g hg => ?_
  have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  rw [← sum_filter, ← mul_sum]
  congr 1
  have himg : (range d).filter (fun r => g ∣ r) = (range (d / g)).image (fun r => g * r) := by
    ext r
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hr, k, rfl⟩
      refine ⟨k, ?_, rfl⟩
      rw [Nat.lt_div_iff_mul_lt' hgd]
      exact hr
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      rwa [Nat.lt_div_iff_mul_lt' hgd] at hk
  rw [himg, sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hg0 hab

theorem addCharAt_mul {g e : ℕ} (hg : 0 < g) (he : 0 < e) (t : ℤ) :
    addCharAt (g * e) ((g : ℤ) * t) = addCharAt e t := by
  unfold addCharAt
  congr 1
  have h1 : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have h2 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  push_cast
  field_simp

theorem rootSum_eq (n : ℤ) {d : ℕ} (hd : 0 < d) :
    rootSum n d
      = (d : ℂ) * ∑ e ∈ d.divisors, (ArithmeticFunction.moebius (d / e) : ℂ) * (rootCount n e : ℂ) := by
  have hinner : ∀ x : ℕ, ∑ r ∈ (range d).filter (fun r : ℕ => Nat.Coprime r d),
      addCharAt d ((r : ℤ) * ((x : ℤ) ^ 2 - n))
      = ∑ g ∈ d.divisors, (ArithmeticFunction.moebius g : ℂ) *
          (if ((d / g : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - n then ((d / g : ℕ) : ℂ) else 0) := by
    intro x
    rw [sum_coprime_eq hd]
    refine sum_congr rfl fun g hg => ?_
    have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
    have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
    have he : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hg0
    congr 1
    rw [← geom_addChar he]
    refine sum_congr rfl fun r _ => ?_
    conv_lhs => rw [← Nat.mul_div_cancel' hgd]
    rw [← addCharAt_mul hg0 he]
    congr 1
    push_cast
    ring
  unfold rootSum
  simp_rw [hinner]
  rw [sum_comm]
  rw [← Nat.sum_div_divisors d (fun e => (ArithmeticFunction.moebius (d / e) : ℂ) * (rootCount n e : ℂ)), mul_sum]
  refine sum_congr rfl fun g hg => ?_
  have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  have he : 0 < d / g := Nat.div_pos (Nat.le_of_dvd hd hgd) hg0
  rw [← mul_sum, Nat.div_div_self hgd hd.ne']
  have hcount : ∑ x ∈ range d, (if ((d / g : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - n then ((d / g : ℕ) : ℂ) else 0)
      = ((d / g : ℕ) : ℂ) * ((g : ℂ) * (rootCount n (d / g) : ℂ)) := by
    have hc := count_periodic n (d / g) g
    rw [Nat.div_mul_cancel hgd] at hc
    rw [← sum_filter, sum_const, nsmul_eq_mul, hc]
    push_cast
    ring
  rw [hcount]
  have hdc : (d : ℂ) = ((d / g : ℕ) : ℂ) * (g : ℂ) := by
    exact_mod_cast (Nat.div_mul_cancel hgd).symm
  rw [hdc]
  ring

theorem rootCount_eq_card_zmod (n : ℤ) (e : ℕ) [NeZero e] :
    rootCount n e = (univ.filter fun x : ZMod e => x ^ 2 = (n : ZMod e)).card := by
  have key : ∀ x : ℕ, (e : ℤ) ∣ (x : ℤ) ^ 2 - n ↔ ((x : ZMod e)) ^ 2 = (n : ZMod e) := by
    intro x
    rw [← CharP.intCast_eq_zero_iff (ZMod e) e]
    push_cast
    exact sub_eq_zero
  unfold rootCount
  refine card_bij (fun x _ => (x : ZMod e)) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and]
    exact (key x).1 (mem_filter.1 hx).2
  · intro a ha b hb hab
    have ha' := mem_range.1 (mem_filter.1 ha).1
    have hb' := mem_range.1 (mem_filter.1 hb).1
    have := (ZMod.natCast_eq_natCast_iff' a b e).1 hab
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  · intro y hy
    refine ⟨y.val, ?_, by simp⟩
    refine mem_filter.2 ⟨mem_range.2 (ZMod.val_lt y), (key _).2 ?_⟩
    simpa using (mem_filter.1 hy).2

theorem rr_eq_rootSum (n : ℤ) (d : ℕ) : Ad3.S.RR n d = rootSum n d := by
  unfold Ad3.S.RR rootSum Ad3.S.GS
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun r _ => ?_
  unfold Ad3.S.ee addCharAt
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rr_eq : Ad3.S.N1 := fun n d hd => by
  rw [rr_eq_rootSum]
  exact rootSum_eq n hd

end GlobalTheory.CompanionTheory.SquareRootCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAnyHaar
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt

theorem integrable_isSchwartzBruhat_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M n dx hdx Φ hΦ
  exact (GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.continuous_integrable σ hCM dx hdx hΦ).2

end GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzHeisLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm GlobalTheory.CompanionTheory.AgreeO GlobalTheory.CompanionTheory.AgreeO.Sys
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (evI realAd At tens Rest IsStd SInf)
open GlobalTheory.WeilM (schr)
open scoped SchwartzMap LineDeriv

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  simp [evI, realAd]

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  simp [linForm, map_sum, LinearMap.sum_apply]

open scoped Classical in

theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add, map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]

end GlobalTheory.CompanionTheory.AgreeO.Sys.HeisD

namespace GlobalTheory.CompanionTheory.AgreeO.Sys

end GlobalTheory.CompanionTheory.AgreeO.Sys

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilIntegralNormalisedStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_integral_normalised : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (fouH σ ψ db τ) db → (∀ z, ∫ y, fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∫ y, fouH σ ψ db τ y * (starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∂dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallHeightVectorIsotropicStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_height_vector_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt | exact GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt | (intros; apply GlobalTheory.CompanionTheory.RedCov.isotropic_of_hgt_lt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLeStatement
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specializes_iff_point_ideal_le : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x y : MP ℤ m n), x ⤳ y ↔ ptIdeal x ≤ ptIdeal y := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le | exact GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le | (intros; apply GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantHeckeKernelStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictly_dominant_hecke_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ T : Module.End ℂ (fixed π J), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker | exact GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker | (intros; apply GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker <;> assumption)
end

