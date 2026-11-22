import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory.Cartier

namespace GlobalTheory.LogDR

variable {X : Scheme.{0}} [IsIntegral X]

def inter {ι : Type} (U : ι → X.Opens) (s : Finset ι) : X.Opens := s.inf U

def cechFam {C : Type} {E : C → CartierDiv X} {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X)
    (a : ℕ) : Finset ι → AddSubgroup (abelian₂ X.functionField) :=
  fun s => logSec (suppAll E) G a (inter 𝒜.U s)

def Decomp (p : ℕ) {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι]
    (𝒜 : SncAtlas E n ι) : Prop :=
  ∀ (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ a b : ℕ,
    DI.HypZero (extD X.functionField) (fun q => cechFam 𝒜 (p • G + ∑ c, r c • E c) q) (a + b) →
      DI.CechZero (cechFam 𝒜 G a) b

end GlobalTheory.LogDR
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.PairModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hecke_pow {η : (AE D)ˣ →* Circle} (hη : IsHeckeChar D η) (n : ℕ) : IsHeckeChar D (η ^ n) := by
  refine ⟨?_, fun x => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact hη.1.pow n
  · rw [MonoidHom.pow_apply, hη.2 x, one_pow]

theorem res_pow {η : (AE D)ˣ →* Circle} (hη : ResEta D η 1) (n : ℕ) : ResEta D (η ^ n) n :=
  ⟨hη.1, fun e he a => by rw [MonoidHom.pow_apply, hη.2 e he a, pow_one]⟩

theorem exp_pow {η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} (hη : HasInfExp D η τ (1 / 2)) (n : ℕ) :
    HasInfExp D (η ^ n) τ ((n : ℚ) / 2) := by
  obtain ⟨m, hm, h1, h2⟩ := hη
  have hm1 : m = 1 := by
    have : (m : ℚ) = 1 := by rw [hm]; norm_num
    exact_mod_cast this
  subst hm1
  refine ⟨n, by push_cast; ring, h1, fun θ hθ x hx hx' => ?_⟩
  rw [MonoidHom.pow_apply, Circle.coe_pow, h2 θ hθ x hx hx', zpow_one, zpow_natCast]

theorem unramAt_of_everywhere {η : (AE D)ˣ →* Circle} (hη : UnramEverywhere D η) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) : UnramAt ε η := by
  intro x h1 h2 h3
  refine hη x ?_ h2 h3
  obtain ⟨α, rfl, -⟩ := hε
  have h4 := congrArg (infPart D) h1
  have h5 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show infPart D ((pairA D.host.F 0 α) ⊗ₜ 1) = 0
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [map_mul, h5, zero_mul, map_sub, map_one] at h4
  exact (sub_eq_zero.1 h4.symm)

theorem isPair_pow {η : (AE D)ˣ →* Circle} (hη : IsEtaTilde D η) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (k : ℕ) (W : HSp D) (hW : W.SigOK)
    (om : GA D (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) × GA D W →*
      Module.End ℂ (WO (D := D) (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) W → ℂ))
    (hom : IsWeilDatumO ψ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) W (η ^ (2 * k)) (η ^ W.rank) om) :
    IsPair ψ θ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) W (η ^ (2 * k)) (η ^ W.rank) om where
  weil := hom
  inf := hθ
  std := Matrix.ext fun i j => by
    refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral (2 * k) (fun _ => false) (2 * k) 0 i j).trans ?_
    exact (Matrix.one_apply (i := i) (j := j)).symm
  even := ⟨k, two_mul k⟩
  sigV := Examples₂.posSpace_sigOK _ _
  sigW := hW
  expV τ := ⟨k, by have := exp_pow (hη.2.2.2 τ) (2 * k); convert this using 1; push_cast; ring⟩
  expW τ := ⟨0, by have := exp_pow (hη.2.2.2 τ) W.rank; convert this using 1; push_cast; ring⟩
  unr v ε h := by
    have h1 := unramAt_of_everywhere hη.2.1 h.1
    exact ⟨fun x a b c => by rw [MonoidHom.pow_apply, h1 x a b c, one_pow],
      fun x a b c => by rw [MonoidHom.pow_apply, h1 x a b c, one_pow]⟩
  eta := ⟨η, hη⟩

theorem exists_isPair (hη : ∃ η, IsEtaTilde D η)
    (hex : ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
      IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, IsWeilDatumO ψ S T χS χT om)
    (k : ℕ) (W : HSp D) (hW : W.SigOK) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V : HSp D) (χV χW : (AE D)ˣ →* Circle)
      (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), V.rank = 2 * k ∧ IsPair ψ θ V W χV χW om := by
  obtain ⟨η, hη⟩ := hη
  obtain ⟨⟨θ, hθ⟩, ψ, hψ⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨om, hom⟩ := hex ψ hψ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral (2 * k)) W (η ^ (2 * k)) (η ^ W.rank)
    (hecke_pow hη.1 _) (hecke_pow hη.1 _) (res_pow hη.2.2.1 _) (res_pow hη.2.2.1 _)
  exact ⟨ψ, θ, _, _, _, om, rfl, isPair_pow hη hθ k W hW om hom⟩

theorem markAd_one {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (W : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) : MarkAd l W rfl ι 1 ι := fun a _ =>
  ⟨0, zero_mem _, by
    rw [map_one, nsmul_zero]
    show finVec W (ι a) - (1 : Matrix _ _ _).mulVec (finVec W (ι a)) = 0
    rw [Matrix.one_mulVec, sub_self]⟩

theorem markAd_of_markBy {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {r : ℕ}
    {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ}
    {lab : Fin g → D.host.E →+* ℂ} (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (h γ : GA D V)
    (hm : MarkBy U V hr dict ι F ik φ h γ) :
    MarkAd l V hr ι (γ * h) ((U.X (dict h).1).Λ.subtype ∘ₗ (φ (dict h).1).toLinearMap ∘ₗ F.t (ik (dict h).1)) :=
  hm.2.2

theorem finite_levQc {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (l : Level H) : Finite (LevQc Dw l) := by
  have hM : Mfr l ≠ ⊥ := by
    intro h
    have h₁ : l.Mb * Mfr l = Ideal.span {(l.M : 𝓞 E)} := l.prod
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := (Mfr l).finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul (Mfr l) (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem hatC_phiHat {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (c : Coeff l) {n : ℕ}
    (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l) :
    inC c (phiHat c φ q) = hatC l (fun x => inC c (φ x)) q := by
  haveI := finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  have hz : inC c (zetaM c) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    rw [zetaM, map_pow]
    show zeta l.M' ^ (l.M' / l.M) = _
    obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have h0 : 0 < l.M := by have := l.three_le; omega
    have h1 : l.M' ≠ 0 := Nat.lcm_ne_zero h0.ne' l.A_pos.ne'
    have h2 : (m : ℂ) ≠ 0 := by rintro h; apply h1; rw [hm, Nat.cast_eq_zero.1 h, mul_zero]
    have h3 : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0.ne'
    rw [zeta, ← Complex.exp_nat_mul, hm, Nat.mul_div_cancel_left _ h0]
    congr 1
    push_cast
    field_simp
  rw [phiHat, hatC, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀, hz]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem row_identity {O : OMDat C R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ} (hs : SerOf O κ v₀ cc ph) {ι x₀} (hp : O.Pins κ v₀ ι x₀) (t : Tp)
    (x : O.Cl' t → VsV D i O.c'.F) (hx : O.Plc t x) (f) (hf : f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank)
    (hth : IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f)
    (q : AutQ (Wc D i)) :
    ph * O.thAd t x q = 1 * cc (O.dict q.out).1 * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu f q := by
  obtain ⟨h, J', h1, -, h3, h4⟩ := (hp.tuple t).reps
  obtain ⟨x₁, hx₁⟩ := (h4 x).1 hx
  rw [h3 _ x hx₁, one_mul]
  have := hs.2.2 t h J' h1 _ x hx₁ f hf hth q.out
  exact this.trans (mul_assoc _ _ _)

theorem phase_eq_inv_mul_product {p a c l m r : ℂ} (h0 : p ≠ 0) (h : p * a = c * l * m * r) : 1 * a = p⁻¹ * c * l * m * r := by
  field_simp
  linear_combination h

theorem constant_unique_of_eq_product {p a c c' l m r : ℂ} (h0 : p ≠ 0) (ha : a ≠ 0) (h : p * a = c * l * m * r) (h' : p * a = c' * l * m * r) :
    c = c' := by
  have hne := mul_ne_zero h0 ha
  rw [mul_assoc, mul_assoc] at h h'
  exact mul_right_cancel₀ (fun hz => hne (by rw [h, hz, mul_zero])) (h.symm.trans h')

theorem phase_one {O : OMDat C R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ} (hs : SerOf O κ v₀ cc ph) : SerOf O κ v₀ (fun k => ph⁻¹ * cc k) 1 := by
  have h0 : ph ≠ 0 := fun h => by have := hs.2.1; rw [h, norm_zero] at this; exact zero_ne_one this
  refine ⟨fun k => by rw [norm_mul, norm_inv, hs.2.1, hs.1 k]; norm_num, norm_one, fun t h J' h1 y x h2 f hf h3 g => ?_⟩
  exact phase_eq_inv_mul_product h0 (hs.2.2 t h J' h1 y x h2 f hf h3 g)

theorem const_unique {O : OMDat C R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {cc cc' : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ} (hs : SerOf O κ v₀ cc ph) (hs' : SerOf O κ v₀ cc' ph)
    {t : Tp} {h J'} (h1 : RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t)) {y x} (h2 : Place R i (tup t) h O.c0' y x)
    {f} (hf : f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank)
    (h3 : IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f)
    {g : GA D (Wc D i)} (hg : R.thF i (tup t) y v₀ g ≠ 0) : cc (O.dict g).1 = cc' (O.dict g).1 := by
  have e := hs.2.2 t h J' h1 y x h2 f hf h3 g
  have e' := hs'.2.2 t h J' h1 y x h2 f hf h3 g
  have h0 : ph ≠ 0 := fun h => by have := hs.2.1; rw [h, norm_zero] at this; exact zero_ne_one this
  exact constant_unique_of_eq_product h0 hg e e'

end

end GlobalTheory.AdTh.PairModel
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxIs {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) (σ : c.F →+* ℂ) {r g : ℕ} (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r)
    (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

def GenReads {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r g : ℕ} (U : Unf Xo c σ r) (k : U.Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : (U.X k).dom) (ϑ : (Fin g → ℂ) → ℂ) : Prop :=
  letI : Algebra c.F ℂ := σ.toAlgebra
  ∃ A : AnFib (U.X k) bas idx e x.1 (U.X k).Λ (unC (Formalism.L2.PjFree.Unf.ofPj U) k x),
    A.Reads 1 (unC (Formalism.L2.PjFree.Unf.ofPj U) k x).s ϑ

variable {D : D7}

def AtComp (θ : InfFam D) (W : HSp D) {r : ℕ} (hr : W.rank = r) {Comp : Type} (X : Comp → Data D.host.E r)
    (dict : GA D W → Σ k, Frame (X k).Ψ r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h γ : GA D W) : Prop :=
  γ ∈ GQ W ∧ latR hr (latG W (γ * h)) = (X (dict h).1).Λ ∧
    (dict h).2 = frMove θ W hr (X (dict h).1) (γ * h) (fun τ => x₀ τ.1)

def CcIs (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (mu : GA D W → ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : U.Comp → ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ∀ h γ : GA D W, AtComp θ W hr U.X dict x₀ h γ →
    ∀ (hx' : (dict h).2 ∈ (U.X (dict h).1).dom) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ)
      (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl (U.X (dict h).1) bas →
      IdxIs c σ (U.X (dict h).1) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U (dict h).1 bas idx e ⟨(dict h).2, hx'⟩ ϑ →
      ∀ w : WO V W, w.map (finPart D) = 0 →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X (dict h).1) bas idx (dict h).2
            (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b) (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b)) *
          ∏ b, ϑ (zOf θ V W hr (U.X (dict h).1) idx (dict h).2 w b)

theorem CcIs.norm {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc : U.Comp → ℂ}
    (h : CcIs θ V W hr U dict mu x₀ om f₀ cc) (k : U.Comp) : ‖cc k‖ = 1 := h.1 k

end

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.DI

def IsLifted (p : ℕ) {X : Scheme.{0}} [IsIntegral X] (Z : Set X) {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (x : ι → Fin n → X.functionFieldˣ) : Prop :=
  ∃ (Kt : Type) (_ : CommRing Kt) (π : Kt →+* X.functionField) (F : ι → Kt →+* Kt),
    IsFlatLift p π ∧ (∀ i, IsFrob p π (F i)) ∧
    (∀ i l, ∃ z, π z = (x i l : X.functionField) ∧ F i z = z ^ p) ∧
    ∀ (y : X) (s : Finset ι), (∀ i ∈ s, y ∈ U i) → ∀ g : X.functionFieldˣ, LogDR.LogUnit Z y g →
      LogLift p π F s (LogDR.locRing y : Set X.functionField) (g : X.functionField)

def stalkIm {Y : Scheme.{0}} {η y : Y} (h : η ⤳ y) : Subring (Y.presheaf.stalk η) :=
  (Y.presheaf.stalkSpecializes h).hom.range

end GlobalTheory.DI
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr
section
noncomputable section

open GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def markedSumIrr (G : HTGroup p) (wt sel : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol) then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

def fullSumIrr (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ ∃ μ, (Quot.out q).Mark μ then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

def CompareIrr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (r : ℕ), 0 < r → ∀ (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
      IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      Match G r K φ K' f' →
      (G.n : ℂ) * markedSumIrr G wt sel L.K.toSubgroup f r K φ = fullSumIrr G wt L.K.toSubgroup f 1 K' f'

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι]

def zp (L : HermLB p) (n : ℤ) : HermLB p := (L.pow n.toNat).tens (L.pow (-n).toNat).dual

def comb (L : ι → HermLB p) (n : ι → ℤ) : HermLB p :=
  (Finset.univ : Finset ι).toList.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p)

def lin (n : ι → ℝ) : MvPolynomial ι ℝ := ∑ i, C (n i) * MvPolynomial.X i

def fnB (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) : HermLB p where
  B := LB.triv X
  isLB := LB.isLB_triv X
  φ σ := Weight.ofFun (u σ)
  cInf σ := fun _ y _ => hu σ y
  conj := hc

def chInt (L : HermLB p) (D : ℕ) (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) : ℝ :=
  ∑ᶠ σ, (L.φ σ).chernInt D Set.univ (f σ)

def gdeg (L : HermLB p) (D : ℕ) : ℝ := chInt L D fun _ _ => 1

def IsArFun [IsIntegral X] (L : ι → HermLB p) (D : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, (comb L n).IsSelfInter (Φ (lin (fun i => (n i : ℝ)) ^ (D + 1)))) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0

def IsGeoFun (L : ι → HermLB p) (D : ℕ) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ D) = gdeg (comb L n) D) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Ψ P = 0

def IsAlgPt (x : X) : Prop :=
  CharZero (X.residueField x) ∧ topologicalKrullDim (closure ({x} : Set X)) = 1

def IsPtHt (L : HermLB p) (x : X) (a : ℝ) : Prop :=
  ∃ h, L.IsArithHeight h ∧ h x = a * Nat.card (X.residueField x →+* ℂ)

def NefFib (L : HermLB p) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

def arVol (L : HermLB p) (D : ℕ) : EReal :=
  limsup (fun m : ℕ => ENNReal.log ((L.pow m).smallSec.encard : ENNReal) *
    ((((D + 1).factorial : ℝ) / (m : ℝ) ^ (D + 1) : ℝ) : EReal)) atTop

theorem nefFib_of_isNef {L : HermLB p} {D : ℕ} (h : L.IsNef D) : NefFib L := h.vertical

end GlobalTheory.ArInt
end
end

