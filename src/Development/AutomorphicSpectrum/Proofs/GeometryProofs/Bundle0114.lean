import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0110

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

section Block

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def blkV (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) : (Σ k, J₀ k) → Σ k, J k :=
  fun p => ⟨bk p.1, bx p.1 p.2⟩

theorem isBlockMap_blkV {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k)) (h : Function.Injective bk) :
    IsBlockMap bk (blkV bk bx) := by
  refine ⟨h, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, a⟩ ⟨k', a'⟩ e
    have e1 : bk k = bk k' := congrArg Sigma.fst e
    obtain rfl := h e1
    have e2 : bx k a = bx k a' := by simpa [blkV] using e
    rw [(bx k).injective e2]
  · rintro ⟨_, a⟩ ⟨k, rfl⟩
    exact ⟨⟨k, (bx k).symm a⟩, by simp [blkV]⟩

variable {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}

def restr (v : (Σ k, J₀ k) → Σ k, J k) : ((Σ k, J k) → ℂ) →L[ℝ] ((Σ k, J₀ k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Σ k, J k => ℂ) (v p)

theorem restr_ne (hv : IsBlockMap κ v) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K₀) :
    ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem isSmoothHerm_pull (hv : IsBlockMap κ v) {A : HermLine J₀} (hA : IsSmoothHerm A) :
    IsSmoothHerm (pullHerm hv A) := by
  have h := ContDiffOn.comp (s := {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA
    (restr v).contDiff.contDiffOn (fun z hz => restr_ne hv hz)
  exact h

theorem isConj_pull (hv : IsBlockMap κ v) {A : HermLine J₀} (hA : IsConjInvariantH A) :
    IsConjInvariantH (pullHerm hv A) := fun z => hA fun p => z (v p)

theorem isConj_tensor {A B : HermLine J} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B) :
    IsConjInvariantH (A.tensor B) := fun z => by
  show A.h _ * B.h _ = A.h _ * B.h _
  rw [hA, hB]

theorem mCoordIdeal_le_imageZ {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (i : Ω₀ →+* Ω) {y₀ : (Σ k, J₀ k) → Ω₀}
    {y : (Σ k, J k) → Ω} {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k))
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) :
    mCoordIdeal y₀ ≤ imageZ (blkV bk bx) (mCoordIdeal y) := by
  intro f hf
  let Φ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp i) fun k => MvPolynomial.X (bk k)
  have key : ∀ f : MRing J₀, mConeMap y (rename (blkV bk bx) f) = Φ (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap, Φ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
      obtain ⟨k, a⟩ := n
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, Φ, blkV, hy]
  have hf' : mConeMap y₀ f = 0 := hf
  show mConeMap y (rename (blkV bk bx) f) = 0
  rw [key, hf', map_zero]

theorem mem_mcPts_restr (hv : IsBlockMap κ v) {P₀ : Ideal (MRing J₀)} {P : Ideal (MRing J)}
    (hP : P₀ ≤ imageZ v P) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) : (fun p => z (v p)) ∈ mcPts P₀ := by
  refine ⟨restr_ne hv hz.1, fun f hf => ?_⟩
  have := hz.2 _ (hP hf)
  have e : (rename v : MRing J₀ →ₐ[ℤ] MRing J).toRingHom f = rename v f := rfl
  rw [e, map_rename, eval_rename] at this
  exact this

end Block

section Lines

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * z p) = Real.log (A.h z) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have h1 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)) (A.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (h1 k)), add_comm]
  simp only [Real.log_zpow]

theorem prod_zpow_sum {R : Type} [Field R] {X : Type} (s : Finset X) {r : R} (hr : r ≠ 0) (a : X → ℤ) :
    ∏ x ∈ s, r ^ a x = r ^ ∑ x ∈ s, a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, zpow_add₀ hr, ih]

def stepLine {N : ℕ} (T : Fin N → HermLine J) (i : Fin N) : HermLine J where
  a := fun k => -∑ x ∈ Finset.Iic i, (T x).a k
  h z := ∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹
  pos z hz := Finset.prod_pos fun x _ => inv_pos.2 ((T x).pos z hz)
  smul c z hc := by
    have h1 : ∀ k, (‖c k‖ : ℝ) ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    simp only [(T _).smul c z hc, mul_inv, Finset.prod_mul_distrib]
    congr 1
    simp only [← Finset.prod_inv_distrib]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_neg, ← prod_zpow_sum _ (h1 k), Finset.prod_inv_distrib]

theorem log_stepLine {N : ℕ} (T : Fin N → HermLine J) (i : Fin N) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) :
    Real.log ((stepLine T i).h z) = -∑ x ∈ Finset.Iic i, Real.log ((T x).h z) := by
  show Real.log (∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹) = _
  rw [Real.log_prod fun x _ => inv_ne_zero ((T x).pos z hz).ne']
  simp only [Real.log_inv, Finset.sum_neg_distrib]

theorem isSmoothHerm_stepLine {N : ℕ} {T : Fin N → HermLine J} (hT : ∀ x, IsSmoothHerm (T x)) (i : Fin N) :
    IsSmoothHerm (stepLine T i) := by
  show ContDiffOn ℝ _ (fun z => ∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹) _
  exact contDiffOn_prod fun x _ => (hT x).inv fun z hz => ((T x).pos z hz).ne'

def corr {Ψ : Type} {N : ℕ} (T : Ψ × Fin N → HermLine J) : Option (Ψ × Fin N) → HermLine J
  | none => Top.trivLine J
  | some r => stepLine (fun k => T (r.1, k)) r.2

theorem isSmoothHerm_trivLine : IsSmoothHerm (Top.trivLine J) := contDiffOn_const

theorem isSmoothHerm_corr {Ψ : Type} {N : ℕ} {T : Ψ × Fin N → HermLine J} (hT : ∀ r, IsSmoothHerm (T r))
    (a : Option (Ψ × Fin N)) : IsSmoothHerm (corr T a) := by
  cases a with
  | none => exact isSmoothHerm_trivLine
  | some r => exact isSmoothHerm_stepLine (fun k => hT (r.1, k)) r.2

def IsFlatOn {P Jd : Ideal (MRing J)} {e : ℕ} (R : AnLogRes P Jd e) (T : HermLine J) : Prop :=
  PB.SamePot R.A Set.univ (potOf R T) (ReciprocityTheory.AnForm.M.LocPot.ofFun 0)

def withTop {P Jd : Ideal (MRing J)} {e : ℕ} (R : AnLogRes P Jd e) (hP : ¬ (⊤ : Ideal (MRing J)) ≤ P)
    (hE : Cmp.IsEmbedded R.A P R.U R.lift) : AnLogRes P ⊤ e where
  homog := ⟨{1}, fun f hf => ⟨0, by
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    have hm0 : m = 0 := by
      rw [MvPolynomial.support_one] at hm
      simpa using hm
    simp [hm0]⟩, by simp⟩
  nondeg := hP
  X := R.X
  A := R.A
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  lift := R.lift
  holo := R.holo
  mem := R.mem
  compat := R.compat
  surj z hz _ := hE.surj z hz
  inj x x' _ h := hE.inj x x' h
  immersion x _ p hp j hj := hE.immersion x p hp j hj
  snc f a hf hh hz := R.snc f a hf hh fun z hz' h0 => by
    have h1 := (hz z hz' h0).2 1 trivial
    simp at h1
  null j := by
    have : {x | R.lift x x ∈ mcPts (⊤ : Ideal (MRing J))} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have h1 := h.2 1 trivial
      simp at h1
    rw [this]
    simp

end Lines

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

def pushCpt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀} {i : Ω₀ →+* Ω}
    (hd : Dominates ξ ξ₀ h i) (p : Cpt ξ) : Cpt ξ₀ := ⟨h p.1, hd.specializes p⟩

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def IsRatio (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (bk : K₀ → K)
    (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀)
    (φ : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w →
    ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) →
      ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u ∧
        φ w * ∏ k, ‖w (blkV bk bx ⟨k, c₀ k⟩)‖ ^ a₀ k = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ a k

end Points

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

def IsCovOf (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) : Prop :=
  GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i ∧ 𝔐.f = h ≫ 𝔐₀.f ∧ 𝔐.cst = i.comp 𝔐₀.cst

def FlagsOver {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω) : Prop :=
  ∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ

def GenPull {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω) {h : 𝔐.X ⟶ 𝔐₀.X}
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) : Prop :=
  ∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s (a : Fin (labelRk D s)) (t₀ : Ω₀),
    ((𝔐₀.V s).gr (Fl₀.b s) a).IsGenAt (pushCpt hd q) t₀ → ((𝔐.V s).gr (Fl.b s) a).IsGenAt q (i t₀)

def NormPull {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω)
    (h : 𝔐.X ⟶ 𝔐₀.X) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) s (a : Fin (labelRk D s)) (t₀ : Ω₀) (ν : ℝ),
    𝔐₀.M.IsGrNorm 𝔐₀.t.PP.L (𝔐₀.V s) (Fl₀.b s) a (z ≫ h) t₀ ν →
      𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) a z (i t₀) ν

end Cover

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricTorusPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos

theorem core_gram_posDef {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent ℂ v) :
    (Matrix.of fun a b => core.inner (v a) (v b)).PosDef := by
  let _ : NormedAddCommGroup V := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore core.toCore
  have hp := Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv
  have hG : (Matrix.gram ℂ v) = Matrix.of fun a b => core.inner (v a) (v b) := by
    ext i j
    rfl
  rw [hG] at hp
  exact hp

theorem cochar_indep {Xc : Type} [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] {r : ℕ}
    (β : Fin r → (Xc →+ ℤ)) (hβ : LinearIndependent ℤ β) :
    LinearIndependent ℂ (fun a => (Int.castAddHom ℂ).comp (β a)) := by
  let b := Module.Free.chooseBasis ℤ Xc
  let ev : (Xc →+ ℤ) →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ Xc → ℤ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    have : f.toIntLinearMap = 0 := b.ext fun i => congrFun hf i
    ext x
    exact LinearMap.congr_fun this x
  have h1 : LinearIndependent ℤ (ev ∘ β) := hβ.map' ev hev
  have h2 : LinearIndependent ℂ (fun a => algebraMap ℤ ℂ ∘ (ev ∘ β) a) :=
    linearIndependent_algebraMap_comp_iff.2 h1
  let evC : (Xc →+ ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ Xc → ℂ) :=
    { toFun := fun f i => f (b i), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp evC h2

theorem exists_diff {S : Scheme.{0}} {T G : Over S} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    {R : Type} [CommRing R] {x : Sp R ⟶ S} {E F : Type} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (M : LieModel T x E) (N : LieModel G x F) : ∃ A : E →ₗ[R] F, ∀ e, N.pt (A e) = M.pt e ≫ u := by
  have ht : ∀ e, IsTanAt G x (M.pt e ≫ u) := by
    intro e
    have h1 := (LieEx.isTanAt_iff x T _).1 (M.tan e)
    refine (LieEx.isTanAt_iff x G _).2 ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (h1 =≫ u).trans ?_
    exact MonObj.one_comp u
  choose A hA using fun e => N.onto _ (ht e)
  refine ⟨{ toFun := A, map_add' := fun e e' => N.inj ?_, map_smul' := fun c e => N.inj ?_ }, hA⟩
  · rw [N.add, hA, hA, hA, M.add, MonObj.mul_comp]
  · apply Over.OverMorphism.ext
    rw [N.smul, hA, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc]

theorem gramAt_posDef_of_diff_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y)
    (Z' : Scheme.{0}) (ρ : Z' ⟶ X) (G' : Over Z') [GrpObj G'] (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ →
    ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc] (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (r : ℕ)
    (β : Module.Basis (Fin r) ℤ (Xc →+ ℤ)) (zc : Sp ℂ ⟶ Z') (Mz : LieModel (splitTorus Z' Xc) zc (Xc →+ ℂ)), IsCocharLie Mz →
    (∀ δ, Mz.pt δ ≫ u = 1 → δ = 0) → ∀ v : Fin r → (epsAt (zc ≫ ρ) ⟶ G),
      (∀ a, (v a).left = (Mz.pt ((Int.castAddHom ℂ).comp (β a)) ≫ u).left ≫ Φ) → (RootHt.gramAt h (zc ≫ ρ) v).PosDef := by
  intro X Ω _ K J y ξ G _ _ Li _ _ M h Z' ρ G' _ Φ hΦ Xc _ _ _ u _ r β zc Mz _ hker v hv
  obtain ⟨V, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ (zc ≫ ρ)
  obtain ⟨A, hA⟩ := exists_diff u Mz (LiePull.modelPull hΦ zc MR)
  have hA' : ∀ δ, (MR.pt (A δ)).left = (Mz.pt δ ≫ u).left ≫ Φ := by
    intro δ
    rw [← hA, ← LiePull.pts_left hΦ (LiePull.eps_assoc zc)]
    exact congrArg (fun k => k.left) ((LiePull.tanPts hΦ zc).apply_symm_apply (MR.pt (A δ))).symm
  have hk : LinearMap.ker A = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro δ hδ
    apply hker
    rw [← hA, hδ]
    have := (LiePull.modelPull hΦ zc MR).add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hli := (cochar_indep β β.linearIndependent).map' A hk
  obtain ⟨core, hcore⟩ := h.herm (zc ≫ ρ) V MR
  have key := core_gram_posDef core _ hli
  have hv' : ∀ a, v a = MR.pt (A ((Int.castAddHom ℂ).comp (β a))) := fun a =>
    Over.OverMorphism.ext ((hv a).trans (hA' _).symm)
  have hm : RootHt.gramAt h (zc ≫ ρ) v = Matrix.of fun a b =>
      core.inner ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) a) ((A ∘ fun a => (Int.castAddHom ℂ).comp (β a)) b) := by
    ext a c
    simp only [RootHt.gramAt, Matrix.of_apply, hcore, hv', Function.comp_apply]
  rw [hm]
  exact key

end GlobalTheory.CompanionTheory.Ar.TorusUnif.GramPos
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Bridge

theorem comb_eig_frame : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ :=
  @PositivityTheory.Xgf.lie_model_eigenvectors_action

end GlobalTheory.CompanionTheory.Ar.Fl.Bridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabLie

theorem lieModel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (V : Type) [AddCommGroup V] [Module R V] (M : LieModel t'.G x V), ∃ Mf : LieModel t.G (x ≫ f) V, ∀ e, (Mf.pt e).left = (M.pt e).left ≫ m.φ := by
  intro E _ _ _ H S S' t' t f m R _ x V _ _ M
  obtain ⟨Mf, h⟩ := (LiePull.lieModel_pullback S S' t.G t'.G f m.φ m.cart R x V).2 M
  exact ⟨Mf, fun e => (h e).symm⟩

end GlobalTheory.CompanionTheory.Ar.SabLie
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelValueLift
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.LieTangent

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp

theorem centre_field_base {K K' : Type} [Field K] [Field K'] {X : Scheme.{0}} (φ : K →+* K')
    (z : Sp K ⟶ X) : centre (Spec.map (CommRingCat.ofHom φ) ≫ z) = centre z := by
  have : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K') = IsLocalRing.closedPoint K :=
    Subsingleton.elim _ _
  change (Spec.map (CommRingCat.ofHom φ) ≫ z) _ = z _
  rw [Scheme.Hom.comp_apply, this]

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem extends_generise (M : LieModel G ξ E) (p : Cpt ξ) {y : X} (hy : genPt ξ ⤳ y) (c : y ⤳ p.1) {e : E}
    {v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G} (h : M.Extends p e v) :
    M.Extends ⟨y, hy⟩ e (epsBase (R := X.presheaf.stalk p.1) (R' := X.presheaf.stalk y)
      (X.presheaf.stalkSpecializes c).hom (Scheme.SpecMap_stalkSpecializes_fromSpecStalk c) ≫ v) := by
  rw [LieModel.extends_iff] at *
  refine ⟨isTanAt_base _ _ h.1, ?_⟩
  rw [h.2, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, ← dualMap_comp]
  congr 3
  exact RingHom.ext fun s => (genMap_specializes p hy c s).symm

theorem valAt_lie_base {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R')
    (M : LieModel G ξ E) {z : Sp R ⟶ X} {z' : Sp R' ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ z = z')
    (hg : genPt ξ ⤳ centre z') {e : E} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z' e (epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  refine ⟨hg, _, extends_generise M ⟨centre z, h1⟩ hg (centre_specializes φ z) hv, ?_⟩
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, spec_comp, ← dualMap_comp, ← dualMap_comp]
  congr 3
  exact congrArg (fun g => g.hom) (stalk_base φ z).symm

end

theorem pull_lie_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc] (MB : LieModel G z Bc) (x : Bc) (e : Li)
    (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
    M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x v →
    ∃ v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G, M.ValAt _ e v' ∧
      MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) x v' := by
  intro X Ω _ ξ G _ Li _ _ M L _ _ z σ Bc _ _ MB x e v hv hl
  have hz : Spec.map (CommRingCat.ofHom σ) ≫ (spMap (algebraMap (𝓞 L) L) ≫ z) =
      spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z := by
    rw [← Category.assoc, spec_comp]
  have hg : genPt ξ ⤳ centre (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) := by
    obtain ⟨h1, -⟩ := hv
    rw [← hz, centre_field_base]
    exact h1
  refine ⟨epsBase σ hz ≫ v, valAt_lie_base σ M hz hg hv, ?_⟩
  unfold LieModel.Lifts at *
  change (Spec.map _ ≫ v.left) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rw [Category.comp_id] at hl
  rw [hl, ← Category.assoc, spec_comp, ← dualMap_comp]

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_period_limit : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) ∧ Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) ∧ (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) ∧ (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) ∧ (∀ φ : W →+ ℤ, (∀ x : W, (∀ x' : W, L.E x x' = 0) → φ x = 0) → ∃ x₀ : W, ∀ x : W, φ x = L.E x₀ x) ∧ ∀ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian → (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.E x x') → (∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0) → ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ (v ⬝ᵥ Hb *ᵥ star v).re ≤ C * ∑ i, ‖v i‖ ^ 2 ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : W, (∀ x' : W, L.E x x' = 0) ∧ p = per x}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice | exact GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_section_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalBoundHeightCompareStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_bound_height_compare : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω) (c : ℝ), VertBound y a u c → ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val → |ptHt (fun k => (a k : ℝ)) φ L w - (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)| ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound | exact GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound <;> assumption)
end

