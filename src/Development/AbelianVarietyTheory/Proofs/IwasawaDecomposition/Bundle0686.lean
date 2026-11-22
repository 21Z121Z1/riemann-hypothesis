import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.Bundle0035
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc

noncomputable section

namespace GlobalTheory.PolFan.TameZ

def IsDom (g n : ℕ) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) : Prop :=
  ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Projective ℤ X₁) (r : (Fin n → ℤ) →ₗ[ℤ] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ Module.finrank ℤ X₁ ≤ g ∧
    B₁ ∈ realForms (id : ℤ → ℤ) X₁ ∧ IsPosDef B₁ ∧ ∀ a b, B a b = B₁ (r a) (r b)

variable {g n m : ℕ}

theorem isDom_comp_iff {r : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ)} (hr : Function.Surjective r)
    (B : (Fin m → ℤ) → (Fin m → ℤ) → ℝ) :
    IsDom g n (fun a b => B (r a) (r b)) ↔ IsDom g m B := by
  constructor
  · rintro ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩
    have he' : ∀ a b, B (r a) (r b) = B₁ (s a) (s b) := he
    have : Module.Finite ℤ X₁ := Module.Finite.of_surjective s hs
    have : Module.IsTorsionFree ℤ X₁ := inferInstance
    have hk : LinearMap.ker r ≤ LinearMap.ker s := fun a ha => by
      rw [LinearMap.mem_ker] at ha ⊢
      refine OffDom.eq_zero_of_posDef hd ?_
      calc B₁ (s a) (s a) = B (r a) (r a) := (he' a a).symm
        _ = B (r 0) (r 0) := by rw [ha, map_zero]
        _ = B₁ (s 0) (s 0) := he' 0 0
        _ = 0 := by simp
    let s' := (LinearMap.ker r).liftQ s hk ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
    have hs' : ∀ a, s' (r a) = s a := fun a => by
      have e : (r.quotKerEquivOfSurjective hr).symm (r a) = Submodule.Quotient.mk a :=
        (LinearEquiv.symm_apply_eq _).2 (by simp)
      simp only [s', LinearMap.comp_apply, LinearEquiv.coe_coe, e]
      rfl
    refine ⟨X₁, _, inferInstance, s', B₁, fun y => ?_, hq, hB, hd, fun x y => ?_⟩
    · obtain ⟨a, rfl⟩ := hs y
      exact ⟨r a, hs' a⟩
    · obtain ⟨a, rfl⟩ := hr x
      obtain ⟨b, rfl⟩ := hr y
      rw [hs', hs']
      exact he' a b
  · rintro ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩
    exact ⟨X₁, _, inferInstance, s ∘ₗ r, B₁, hs.comp hr, hq, hB, hd, fun a b => he _ _⟩

theorem isDom_smul {t : ℝ} (ht : 0 < t) {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (h : IsDom g n B) :
    IsDom g n (fun a b => t * B a b) := by
  obtain ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩ := h
  refine ⟨X₁, _, inferInstance, s, t • B₁, hs, hq, Submodule.smul_mem _ _ hB, fun k x hx c hc => ?_,
    fun a b => by simp [he a b]⟩
  refine (mul_pos ht (hd k x hx c hc)).trans_eq ?_
  simp only [Finset.mul_sum, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem isDom_smul_iff {t : ℝ} (ht : 0 < t) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) :
    IsDom g n (fun a b => t * B a b) ↔ IsDom g n B := by
  constructor
  · intro h
    have := isDom_smul (inv_pos.2 ht) h
    simpa only [inv_mul_cancel_left₀ ht.ne'] using this
  · exact isDom_smul ht

theorem toFun_zeroForm (φ : InvFun ℤ) (n : ℕ) : φ.toFun n (fun _ _ => 0) = 0 := by
  have := φ.inv n 0 0 (fun y => ⟨0, Subsingleton.elim _ _⟩) (fun _ _ => 0)
  rw [φ.zero] at this
  exact this

variable (g) in
open Classical in

def cutFun (φ : InvFun ℤ) : InvFun ℤ where
  toFun n B := if IsDom g n B then φ.toFun n B else 0
  inv n m r hr B := by
    by_cases h : IsDom g m B
    · rw [if_pos ((isDom_comp_iff hr B).2 h), if_pos h]
      exact φ.inv n m r hr B
    · rw [if_neg (mt (isDom_comp_iff hr B).1 h), if_neg h]
  zero B := by
    split_ifs
    · exact φ.zero B
    · rfl

variable {φ : InvFun ℤ}

theorem cutFun_of {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (h : IsDom g n B) :
    (cutFun g φ).toFun n B = φ.toFun n B := if_pos h

theorem cutFun_of_not {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (h : ¬ IsDom g n B) :
    (cutFun g φ).toFun n B = 0 := if_neg h

theorem cutFun_homog (hpol : IsPolFan id g φ) (n k : ℕ) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) :
    (cutFun g φ).toFun n (fun a b => k * B a b) = k * (cutFun g φ).toFun n B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul]
    by_cases h : IsDom g n (fun _ _ => (0 : ℝ))
    · rw [cutFun_of h, toFun_zeroForm]
    · rw [cutFun_of_not h]
  have ht : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases h : IsDom g n B
  · rw [cutFun_of ((isDom_smul_iff ht B).2 h), cutFun_of h]
    obtain ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩ := h
    obtain rfl : B = fun a b => B₁ (s a) (s b) := funext fun a => funext fun b => he a b
    have : Module.Finite ℤ X₁ := Module.Finite.of_surjective s hs
    have e1 := φ.eval_eq hs (fun x y => (k : ℝ) * B₁ x y)
    have e2 := φ.eval_eq hs (fun x y => B₁ x y)
    rw [← e1, ← e2]
    have := (hpol X₁ hq).homog B₁ (hd.mem_psdCone hB) k ht.le
    simpa [evalR] using this
  · rw [cutFun_of_not (mt (isDom_smul_iff ht B).1 h), cutFun_of_not h, mul_zero]

theorem cutFun_nonneg (hpol : IsPolFan id g φ) (n : ℕ) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) :
    0 ≤ (cutFun g φ).toFun n B := by
  by_cases h : IsDom g n B
  · rw [cutFun_of h]
    obtain ⟨X₁, _, _, s, B₁, hs, hq, hB, hd, he⟩ := h
    obtain rfl : B = fun a b => B₁ (s a) (s b) := funext fun a => funext fun b => he a b
    have : Module.Finite ℤ X₁ := Module.Finite.of_surjective s hs
    have e : φ.toFun n (fun a b => B₁ (s a) (s b)) = evalR φ B₁ := by
      rw [evalR, φ.eval_eq hs]
    rw [e]
    exact (hpol X₁ hq).evalR_nonneg (hd.mem_psdCone hB)
  · rw [cutFun_of_not h]

theorem evalR_cutFun {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (hX : Module.finrank ℤ X ≤ g)
    {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (id : ℤ → ℤ) X) : evalR (cutFun g φ) B = evalR φ B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' ℤ X
  unfold evalR
  rw [(cutFun g φ).eval_eq hr, φ.eval_eq hr]
  refine cutFun_of ?_
  obtain ⟨X₁, _, i₁, _, s, B₁, hs, hB₁, hd, he⟩ := hB
  obtain rfl : i₁ = AddCommGroup.toIntModule X₁ := Subsingleton.elim _ _
  have : Module.Finite ℤ X₁ := Module.Finite.of_surjective s hs
  have hrk : Module.finrank ℤ X₁ ≤ g := by
    have := LinearMap.finrank_range_le s
    rw [LinearMap.range_eq_top.2 hs, finrank_top] at this
    exact this.trans hX
  exact ⟨X₁, _, inferInstance, s ∘ₗ r, B₁, hs.comp hr, hrk, hB₁, hd, fun a b => he _ _⟩

theorem toReal_mem_psdCone_int {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms (id : ℤ → ℤ) X) (hp : ∀ y, 0 ≤ β y y) : toReal β ∈ psdCone (id : ℤ → ℤ) X := by
  have := ConeSub.sum_smul_toReal_mem_psdCone ℤ id X 1 ![β] ![1] (by simp [hβ]) (by simp [hp]) (by simp)
  simpa using this

theorem isCone_of_agree {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {φ₁ φ₂ : InvFun ℤ}
    (h : ∀ B ∈ psdCone (id : ℤ → ℤ) X, evalR φ₁ B = evalR φ₂ B) {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (hc : IsCone id φ₁ γ) : IsCone id φ₂ γ := by
  have hz : ∀ β ∈ balForms (id : ℤ → ℤ) X, (∀ y, 0 ≤ β y y) → φ₁.evalZ β = φ₂.evalZ β := fun β hβ hp => by
    rw [← evalR_toReal, ← evalR_toReal]
    exact h _ (toReal_mem_psdCone_int hβ hp)
  refine ⟨hc.mem, hc.nonneg, hc.basis, (linearOn_iff φ₂ γ).2 fun c hcn => ?_, ?_⟩
  · rw [← h _ (ConeSub.sum_smul_toReal_mem_psdCone ℤ id X m γ c hc.mem hc.nonneg hcn),
      (linearOn_iff φ₁ γ).1 hc.linear c hcn]
    exact Finset.sum_congr rfl fun i _ => by rw [hz _ (hc.mem i) (hc.nonneg i)]
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hc.strict
    exact ⟨N, ℓ, hN, fun i => by rw [← hz _ (hc.mem i) (hc.nonneg i)]; exact h1 i,
      fun β hβ hp => by rw [← hz β hβ hp]; exact h2 β hβ hp,
      fun β hβ hp he => h3 β hβ hp (by rw [hz β hβ hp]; exact he)⟩

theorem isPolFanOn_of_agree {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {φ₁ φ₂ : InvFun ℤ}
    (agree : ∀ B ∈ psdCone (id : ℤ → ℤ) X, evalR φ₂ B = evalR φ₁ B) (h : IsPolFanOn id φ₁ X) :
    IsPolFanOn id φ₂ X := by
  have hz : ∀ β ∈ balForms (id : ℤ → ℤ) X, (∀ y, 0 ≤ β y y) → φ₂.evalZ β = φ₁.evalZ β := fun β hβ hp => by
    rw [← evalR_toReal, ← evalR_toReal]
    exact agree _ (toReal_mem_psdCone_int hβ hp)
  have hc : ∀ {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone id φ₂ γ ↔ IsCone id φ₁ γ := fun γ =>
    ⟨isCone_of_agree agree, isCone_of_agree fun B hB => (agree B hB).symm⟩
  refine ⟨fun B hB t ht => ?_, fun B hB B' hB' => ?_, fun β hβ hp => ?_, fun β hβ hp h0 => ?_,
    fun m m' γ s hγ => ?_, fun B hB => ?_, ?_⟩
  · rw [agree _ (smul_mem_psdCone hB ht), agree _ hB]
    exact h.homog B hB t ht
  · have hsum : B + B' ∈ psdCone (id : ℤ → ℤ) X := by
      obtain ⟨m, γ, c, hγ, hc, rfl⟩ := h.cover B hB
      obtain ⟨m', γ', c', hγ', hc', rfl⟩ := h.cover B' hB'
      have := ConeSub.sum_smul_toReal_mem_psdCone ℤ id X (m + m') (Fin.append γ γ') (Fin.append c c')
        (fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hγ.mem, hγ'.mem])
        (fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hγ.nonneg, hγ'.nonneg])
        (fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hc, hc'])
      simpa [Fin.sum_univ_add] using this
    rw [agree _ hB, agree _ hB', agree _ hsum]
    exact h.superadd B hB B' hB'
  · rw [hz β hβ hp]
    exact h.integral β hβ hp
  · rw [hz β hβ hp]
    exact h.pos β hβ hp h0
  · exact (hc _).2 (h.face m m' γ s ((hc _).1 hγ))
  · obtain ⟨m, γ, c, hγ, hc', e⟩ := h.cover B hB
    exact ⟨m, γ, c, (hc _).2 hγ, hc', e⟩
  · obtain ⟨S, hS, h1⟩ := h.finite
    exact ⟨S, hS, fun m γ hγ => h1 m γ ((hc _).1 hγ)⟩

theorem exists_tame : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ →
    ∃ φs : InvFun ℤ, IsPolFan id g φs ∧ IsTame φs ∧ AgreesPsd g φs φ := by
  intro g φ hpol
  refine ⟨cutFun g φ, fun X _ i _ _ hX => ?_, ⟨cutFun_homog hpol, cutFun_nonneg hpol⟩,
    fun X _ _ _ hX B hB => evalR_cutFun hX hB⟩
  obtain rfl : i = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  exact isPolFanOn_of_agree (fun B hB => evalR_cutFun hX hB) (hpol X hX)

end GlobalTheory.PolFan.TameZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelLatticeRiemannFormOffBoundaryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialKernel_lattice_riemannForm_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (x : CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner | exact GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner | (intros; apply GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_inner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtraTiedCol
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Top.Bl.WPt.extraTied_col : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Forms.ColsExtraTiedS q.x.col.full q.O.ex ∧ ∃ g : Formalism.L2.G.GroupCompatibilityAll (q.w.D q.Z) q.O.gatT q.O.ex.cmp, HEq g q.x.col.g ∧ g.herm = q.x.col.full.1.to0 ∧ g.forms = fun u => (q.x.col.C.forms u).to0 := by
  intro 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, K', X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kt, div, thT, obj, ox, real,
    dsig_eq, hgauge, good⟩ := x
  obtain ⟨⟨C, std, stdLv, full, stdDt, Gt, cmp', g, herm_eq, forms_eq, gpl⟩, isRec, om⟩ := col
  dsimp only at hlev herrX ker_eq ⊢
  cases ker_eq
  exact ⟨⟨⟨hlev, herrX, gpl⟩, kt.iw, kt.iw_pos⟩, g, HEq.rfl, herm_eq, forms_eq⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanImageOfIsCompl
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame GlobalTheory.FlagPts
open scoped TensorProduct

namespace GlobalTheory.RedRank

theorem finrank_span_image_of_isCompl {R S M M' : Type*} [CommRing R] [Nontrivial R] [Field S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
    {g : M →ₗ[R] M'} (hb : IsBaseChange S g) {P Q : Submodule R M} (hPQ : IsCompl P Q)
    [Module.Free R P] [Module.Finite R P] :
    Module.finrank S (Submodule.span S (g '' P)) = Module.finrank R P := by
  let φ : S ⊗[R] P →ₗ[S] M' := (g ∘ₗ P.subtype).liftBaseChange S
  let π := P.linearProjOfIsCompl Q hPQ
  have hφ : Function.Injective φ := by
    refine Function.LeftInverse.injective (g := (π.baseChange S) ∘ₗ hb.equiv.symm.toLinearMap) fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y =>
      have h1 : hb.equiv.symm (g y) = (1 : S) ⊗ₜ[R] (y : M) := by
        rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
      simp [φ, h1, π, TensorProduct.smul_tmul']
      exact congrArg (s ⊗ₜ[R] ·) (Submodule.linearProjOfIsCompl_apply_left hPQ y)
    | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at hx hy ⊢; rw [hx, hy]
  have hr : LinearMap.range φ = Submodule.span S (g '' P) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s y => simpa [φ] using Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_image_of_mem g y.2))
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    · rintro _ ⟨y, hy, rfl⟩
      exact LinearMap.mem_range.2 ⟨(1 : S) ⊗ₜ[R] (⟨y, hy⟩ : P), by simp [φ]⟩
  rw [← hr, LinearMap.finrank_range_of_inj hφ, Module.finrank_baseChange]

end GlobalTheory.RedRank

open GlobalTheory.EigenSplit in

theorem GlobalTheory.LocM.At.finrank_eigBar : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
    ∀ τ : PsiT D, Module.finrank ct.kbar (ct.eigBar τ) = N := by
  intro D A N j S κ p ct τ
  have := S.Dw.fin
  have := S.Dw.proj
  have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
  have : Module.Flat ℤ S.Dw.La := Module.Flat.trans ℤ (𝓞 D.host.E) S.Dw.La
  have : Module.Free ct.V₀ (ct.V₀ ⊗[ℤ] S.Dw.La) := Module.free_of_flat_of_isLocalRing
  let ρZ : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La := Module.toModuleEnd ℤ S.Dw.La
  obtain ⟨Q, hQ⟩ := exists_isCompl_eigenSub_of_valuationRing (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))
  have := free_eigenSub_of_valuationRing (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))
  have := finite_eigenSub_of_valuationRing (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))
  have hg : ∀ x, ct.redLa x = extendTensor ℤ ct.V₀ ct.kbar S.Dw.La x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact (map_zero _).symm
    | tmul r a => rfl
    | add x y hx hy => rw [map_add, hx, hy]; exact (map_add _ x y).symm
  have h0 : Module.finrank ct.kbar (ct.eigBar τ) =
      Module.finrank ct.V₀ (eigenSub (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))) := by
    rw [At.eigBar, show (ct.redLa : _ → _) = extendTensor ℤ ct.V₀ ct.kbar S.Dw.La from funext hg]
    exact GlobalTheory.RedRank.finrank_span_image_of_isCompl
      (P := eigenSub (baseChangeAction ct.V₀ ρZ) (embV κ.c ct.W (embOf D τ))) (isBaseChange_extendTensor ℤ ct.V₀ ct.kbar S.Dw.La) hQ
  letI : Algebra ct.V₀ ℂ := ((algebraMap κ.c.F ℂ).comp (algebraMap ct.V₀ κ.c.F)).toAlgebra
  have hσ : Function.Injective fun σ : D.host.E →+* ℂ => embV κ.c ct.W σ := fun σ σ' h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.host.E))
      (RingHom.ext fun a => congrArg (fun f : 𝓞 D.host.E →+* ct.V₀ => (((f a : ct.V₀) : κ.c.F) : ℂ)) h)
  have h1 := finrank_eigenSub_of_charZero (E := D.host.E) (A := ct.V₀) (N := ct.V₀ ⊗[ℤ] S.Dw.La)
    (ρ := baseChangeAction ct.V₀ ρZ) (M := ℂ ⊗[ℤ] S.Dw.La)
    (ρ' := baseChangeAction (ℂ) ρZ)
    (f := extendTensor ℤ ct.V₀ (ℂ) S.Dw.La) (S := ℂ) hσ (NumberField.Embeddings.card D.host.E ℂ)
    (extendTensor_equivariant ct.V₀ (ℂ) ρZ) (isBaseChange_extendTensor ℤ ct.V₀ (ℂ) S.Dw.La) (embOf D τ)
  have h2 := GlobalTheory.TensorDet.finrank_eigenSub (O := ℤ) (M := S.Dw.La) (k := ℂ)
    ((algebraMap ct.V₀ (ℂ)).comp (embV κ.c ct.W (embOf D τ))) (RingHom.ext_int _ _)
  have h3 : GlobalTheory.TensorDet.rightAction (ℂ) ℤ (𝓞 D.host.E) S.Dw.La = baseChangeAction (ℂ) ρZ := by
    ext a : 1
    rw [GlobalTheory.TensorDet.rightAction_apply, baseChangeAction_apply]
    rfl
  rw [h3, h1, S.Dw.rank, S.rank_eq] at h2
  rw [h0, h2]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellValuativeExistenceOverUnionOfOpens
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Valu

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_surj {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem exists_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.affineOpens) (hx : x (IsLocalRing.closedPoint A) ∈ (U.1 : Set X)) :
    ∃ φ : Γ(X, U.1) →+* A, x = spMap φ ≫ U.2.fromSpec := by
  have htop : x ⁻¹ᵁ U.1 = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem x hx
  have hr : Set.range x ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : y ∈ x ⁻¹ᵁ U.1 := by rw [htop]; trivial
    exact this
  have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  obtain ⟨φ, hφ⟩ := sp_surj (B := Γ(X, U.1)) (@IsOpenImmersion.lift _ _ _ U.2.fromSpec x hi hr)
  exact ⟨φ, (@IsOpenImmersion.lift_fac _ _ _ U.2.fromSpec x hi hr).symm.trans (congrArg (· ≫ U.2.fromSpec) hφ)⟩

theorem indep_cellVec {T : Type} {m : T → ℕ} {k : Type} [Field k] {M : ℕ} (D c : Let m → Fin (M + 1) → k) (w : Pm m)
    (x : CellVar m → k) (h : LeftInv D c) (τ : T) :
    LinearIndependent k fun j : Fin (m τ) => cellVec c w x ⟨τ, j⟩ := by
  have h1 := (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m k M D c w x h).1 _ _ (down_std τ (m τ) le_rfl)
  rw [GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.1] at h1
  have h2 := Matrix.linearIndependent_rows_of_det_ne_zero (h1.trans_ne one_ne_zero)
  let L : (Fin (M + 1) → k) →ₗ[k] (Fin (m τ) → k) :=
    Matrix.toLin' (Matrix.of fun l' r => D ((wLet w ∘ std τ (m τ) le_rfl) l') r)
  exact LinearIndependent.of_comp L h2

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S ι : Type} [CommRing S] {c c' : Let m → ι → S} (h : InBlock c c')
    (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_uvec {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (c : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) (ψ : CR m U →+* S) :
    (fun z => ψ ∘ uvec c w z) =
      cellVec (fun z => (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ∘ c z) w (ψ ∘ MvPolynomial.X) :=
  funext fun z => map_cellVec ψ _ w _ z

theorem sp_cbase {X : Scheme.{0}} {T : Type} {m : T → ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (ψ : CR m U →+* S) :
    spMap ψ ≫ cbase m U = spMap (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ≫ U.2.fromSpec := by
  rw [cbase, ← Category.assoc, sp_comp]

theorem exists_integral_cell : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (A k : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k] [IsFractionRing A k] b' w' (a : Sp k ⟶ Sp (CR m (V b'))) (x : Sp A ⟶ X), Set.range x ⊆ ⋃ b, ((V b).1 : Set X) → a ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x → ∃ b w, ∃ l : Sp A ⟶ Sp (CR m (V b)), l ≫ cbase m (V b) = x ∧ spMap (algebraMap A k) ≫ l ≫ h b w = a ≫ h b' w' := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP A k _ _ _ _ _ _ b' w' a x hx ha
  obtain ⟨ψ', rfl⟩ := sp_surj a
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hx ⟨IsLocalRing.closedPoint A, rfl⟩)
  obtain ⟨φ, rfl⟩ := exists_of_closedPoint x (V b) hb
  have ha' : spMap ((algebraMap A k).comp φ) ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← sp_cbase, ha, ← Category.assoc, sp_comp]
  obtain ⟨w, y, d, hy, hd, ht⟩ := GlobalTheory.T.exists_integral_flagCell_of_valuedField T m k (ValuationRing.valuation A k).valuationSubring M _ _
    (inBlock_cellVec (hC.compat k b b' _ _ ha') w' (ψ' ∘ MvPolynomial.X))
    (indep_cellVec _ _ w' _ ((hC.inv b').map _))
  have hy' : ∀ v, ∃ t : A, algebraMap A k t = y v := fun v => (ValuationRing.mem_integer_iff A k (y v)).1 (hy v)
  choose t hyt using hy'
  let χ : CR m (V b) →+* A := MvPolynomial.eval₂Hom φ t
  have hχ : χ.comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) = φ := MvPolynomial.eval₂Hom_comp_C φ t
  have hχ' : ((algebraMap A k).comp χ).comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) =
      (algebraMap A k).comp φ := by rw [RingHom.comp_assoc, hχ]
  refine ⟨b, w, spMap χ, by rw [sp_cbase, hχ], ?_⟩
  rw [← Category.assoc, sp_comp]
  refine GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hC hP k b b' w w' _ ψ' d ?_ hd ?_
  · rw [sp_cbase, sp_cbase, hχ', ha']
  · have e : ((algebraMap A k).comp χ) ∘ MvPolynomial.X = y := funext fun v => by
      rw [← hyt]
      exact congrArg (algebraMap A k) (MvPolynomial.eval₂Hom_X' φ t v)
    rw [map_uvec, map_uvec, hχ', e]
    exact ht

end GlobalTheory.FlagEmb.Valu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameTransportEtaIsHeckeElementLiftsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameTransport_eta_isHeckeElement_lifts : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (hx1 : 1 ≤ x.2) (hx2 : x.2 ≤ (Vc X.toD7 i).rank) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (Ut : Formalism.L2.Col.MhlUnif Pb) (g : Bridge.Gf (Vc X.toD7 i)) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * ((Formalism.L2.Col.mhlEta X.toD7.sp.cm X.B.R.nV v Ut.hπ0 x.2 : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    (envL X I hX U Xg tr L cV i t).isT x g := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.eta_isHecke | exact GlobalTheory.Mem.R3.LiftBrg.eta_isHecke | (intros; apply GlobalTheory.Mem.R3.LiftBrg.eta_isHecke <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_generating_at_point : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] (φ : R →+* W) (ξ : GtPt D.toPre (Over.mk (spMap φ))) (x' : Over.mk (spMap φ) ⟶ G), IsPointOf U ξ x' → ∀ (b : Sp W ⟶ D.toPre.P.A.left), ξ.b.left = b → ∀ (g' : Frame U.LG.L (Y := Sp W) x'.left) (g : Frame D.toPre.P.L b), g'.IsGen → g.IsGen → FrRel U (T := Sp W) x'.left b g' g → ∀ (k : ℕ) (σ : H0 U.LG.L k) (F : ∀ α, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ F) → ∃ (s : W) (t : D.toPre.X → W), (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JL), Good U.LG.L z JL → sval σ (r ≫ x'.left) z JL = gs r z ⊤ (toΓ W s) * (val g' r z JL ^ k).val) ∧ (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JM), Good D.toPre.P.L z JM → sval (F α) (r ≫ b) z JM * (val (ξ.s α) r z JM).val = gs r z ⊤ (toΓ W (t α)) * (val g r z JM ^ k).val) ∧ ∀ e : ℕ, ∃ S : Finset D.toPre.X, (∀ α ∉ S, t α ∈ I.map φ ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map φ ^ (e + 1) := by
  first | exact @GlobalTheory.RayEv.Transport.exists_adic_expansion | exact GlobalTheory.RayEv.Transport.exists_adic_expansion | (intros; apply GlobalTheory.RayEv.Transport.exists_adic_expansion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacesGroupContainsChartLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 4000000 in

theorem further_group_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ (W : ∀ v, v ∈ Q → Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) (ψ : (∀ v : Q, ↥(W v.1 v.2)) →* ℂˣ), (∀ v hv, W v hv ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0) ∧ (∀ v hv, ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ W v hv) ∧ (∀ β v hv, (K β).lev.Uloc v ≤ (W v hv).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ∧ (∀ β v hv, ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v hv)).FiniteIndex) ∧ (∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(W v.1 v.2)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z) := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hfin hoff hchi Lb0 hLb
  classical
  rcases isEmpty_or_nonempty Ch with hE | hNE
  · refine ⟨fun v _ => levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0, 1, fun v hv => le_rfl,
      fun v hv => ⟨1, one_pos, fun x hx => hx.1⟩, fun β => hE.elim β, fun β => hE.elim β, fun β => hE.elim β⟩
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_character_allCharts_furtherPlaces I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hfin hoff hchi Lb0 hLb
    refine ⟨fun v _ => (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom), ψ, fun v hv => iSup_le fun β => GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv, fun v hv => ?_, fun β v hv => ?_, fun β v hv => GlobalTheory.T.chartLocalGroup_finiteIndex_at_furtherPlace I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv, hψ⟩
    · obtain ⟨β⟩ := hNE
      obtain ⟨n, hn, hx⟩ := GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ I hI hP l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hoff hchi Lb0 hLb β v hv
      exact ⟨n, hn, fun x h => le_iSup (fun β' => ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) β (hx x h)⟩
    · intro x hx
      refine ⟨(reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).symm x, le_iSup (fun β' => ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) β ?_, ?_⟩
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]; exact hx
      · rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_divOf_ne_bot_of_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ) (h : CxFr Z σ → ℂ), τ (H.rt : E) = H.rt0 → HorFn τ h → (C.Y.H0 (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥ ∧ C.Y.H0 (-divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥) := by
  first | exact @GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn | exact GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn | (intros; apply GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn <;> assumption)
end

