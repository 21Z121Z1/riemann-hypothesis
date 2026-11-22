import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.Bundle0002
import Formalism.PairingDivisors.StatementH

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

abbrev KeyRule : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ

def IsKeyRule (κ : KeyRule) : Prop :=
    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ 8 * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ 4 * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
      KeyPB x' x f → (κ K' x' : K') = f (κ K x)) ∧
    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (κ k xk : k) = r u) ∧
    (∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ),
      τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
      u.IsRig x.rig → u.IsFn x.th (thetaChar τ a b) →
      (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) → κ ℂ x = 1) ∧
    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ‖(κ ℂ x : ℂ)‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g)

section Fibre

variable {R R' : Type} [CommRing R] [CommRing R']

def IsFibreOf (x : KeyIn R') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (rig : LB.Gen (L.pull (eSec G)))
    (θ : L.Sec) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (f : R →+* R') : Prop :=
  ∃ (φ : x.P.A.left ⟶ G.left) (he : eSec x.P.A ≫ φ = spMap f ≫ eSec G)
    (e : LB.Iso x.P.L (L.pull φ)) (hg : x.P.g = n) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x.P.A G (spMap f) φ ∧ e.IsGen ∧
    LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap f) he L rig) ∧
    (∀ (j : (L.pull φ).ι) (i : x.P.L.ι) (h : (L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (θ.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L.pull φ).U j ⊓ x.P.L.U i) from (e.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x.v i).left ≫ φ = spMap F ≫ (w (i.cast hg)).left

def IsMul {X : Over (Sp R)} {L : LB X.left} (σ : L.Sec) (a : R) (θ : L.Sec) : Prop :=
  ∀ i, σ.f i = constFn X.hom _ a * θ.f i

def Generates {X : Over (Sp R)} {L : LB X.left} (θ : L.Sec) : Prop :=
  ∀ σ : L.Sec, ∃! a : R, IsMul σ a θ

end Fibre

section Box

variable {S : Scheme.{0}}

abbrev pow (G : Over S) (N : ℕ) : Over S := ∏ᶜ (fun _ : Fin N => G)

abbrev pr (G : Over S) (N : ℕ) (k : Fin N) : (pow G N).left ⟶ G.left := (Pi.π (fun _ : Fin N => G) k).left

abbrev boxLB (G : Over S) (L : LB G.left) (N : ℕ) : LB (pow G N).left :=
  LB.LinComb L (K := Fin N) (pr G N) (fun _ => 1)

def tensorSec {X Y : Scheme.{0}} {L : LB X} {N : ℕ} (φ : Fin N → (Y ⟶ X)) (θ : L.Sec) :
    (LB.LinComb L (K := Fin N) φ (fun _ => 1)).Sec where
  f j := ∏ k, ((φ k).appLE _ _ (LB.wchart_le L φ j k)).hom (θ.f (j k))
  compat j j' := by
    have hle : ∀ k, LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := fun k =>
      le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k))
    show resG Y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)
        (∏ k, ((φ k).appLE _ _ (LB.wchart_le L φ j k)).hom (θ.f (j k))) =
      ((∏ k, (res (hle k) (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (1 : ℤ) :
        Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ) : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')) *
      resG Y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)
        (∏ k, ((φ k).appLE _ _ (LB.wchart_le L φ j' k)).hom (θ.f (j' k)))
    rw [map_prod, map_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h := congrArg ((φ k).appLE _ _ (hle k)).hom (θ.compat (j k) (j' k))
    rw [map_mul] at h
    simp only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at h
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, zpow_one]
    exact h

abbrev boxSec (G : Over S) {L : LB G.left} (θ : L.Sec) (N : ℕ) : (boxLB G L N).Sec := tensorSec (pr G N) θ

end Box

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsBaseRing (β : O →+* c.F) : Prop :=
  Function.Injective β ∧ ∀ x : c.F, IsIntegral ℤ x → x ∈ Set.range β

theorem isBaseRing_local (c : Coeff l) (W : ValuationSubring ℂ) : IsBaseRing (c.V W).subtype := by
  refine ⟨Subtype.val_injective, fun x hx => ?_⟩
  have h : IsIntegral (c.V W) x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
  exact ⟨y, hy⟩

def UnitAt (κ : KeyRule) (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] : Prop :=
  ∀ (y : Sp K ⟶ Xo.XF c) (yt : Sp V ⟶ Y.X), spMap (algebraMap V K) ≫ yt = y ≫ Y.j →
    ∀ (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w →
      ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) →
        (Generates (X := t.G) θ →
          (∃ u : Vˣ, (κ K x : K) = algebraMap V K u) ∧
          ∀ N : ℕ, 8 ∣ N → Generates (X := pow t.G N) (boxSec t.G θ N)) ∧
        ∀ N : ℕ, 8 ∣ N → ∀ (σ : (boxLB t.G t.PP.L N).Sec) (a : V), Generates (X := pow t.G N) σ →
          IsMul (X := pow t.G N) (boxSec t.G θ N) a σ →
          ∃ u : Vˣ, algebraMap V K a * (κ K x : K) ^ (N / 8) = algebraMap V K u

def AtValuedPoints (Q : ∀ (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K], Prop) : Prop :=
  (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Q V K) ∧
  ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra V C], IsUnitBall V C → Q V C

def FramesAt (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] : Prop :=
  ∀ (y : Sp K ⟶ Xo.XF c) (yt : Sp V ⟶ Y.X), spMap (algebraMap V K) ≫ yt = y ≫ Y.j →
    ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)) (θ : t.PP.L.Sec) (x : KeyIn K),
      IsLieBasis w ∧ Generates (X := t.G) θ ∧ IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K)

def KeyUnitOnModels : Prop :=
  ∀ κ : KeyRule, IsKeyRule κ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
      (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ),
      1 ≤ D.p + D.q → IsBaseRing β → p.Prime → Y.LevelStructureConditions p → Y.N3 → Y.N4 → Y.SplitFibres →
      AtValuedPoints (fun V K _ _ _ _ => UnitAt κ Y V K)

def FramesOnModels : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ),
    1 ≤ D.p + D.q → IsBaseRing β → p.Prime → Y.LevelStructureConditions p → Y.N3 → Y.N4 → Y.SplitFibres →
    AtValuedPoints (fun V K _ _ _ _ => FramesAt Y V K)

end GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.InfinitePlaceDepthSums
section
open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums

def numL (x ε : ℝ) : ℝ := x ^ ε

def numB (x ε : ℝ) : ℝ := Real.exp (numL x ε)

def numLa (E : Type) [Field E] [NumberField E] (x ε : ℝ) : ℝ :=
  Real.log (x * numB x ε * rootDiscr E)

def numF (E : Type) [Field E] [NumberField E] : ℕ := finrank ℚ (maximalRealSubfield E)

def numN (k m t : ℕ) : ℕ := k + m * (t + (k + m + 5) + 1)

def depthSum {E : Type} [Field E] [NumberField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) : ℝ :=
  ∑ v ∈ S0, (e v : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)

def formFrame {K : Type} [Field K] [NumberField K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) :
    Matrix (Fin n) (Fin n) ℂ :=
  (CFC.sqrt (H.map v.embedding))⁻¹

theorem formFrame_spec {K : Type} [Field K] [NumberField K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    IsUnit (formFrame H v).det ∧
      ((formFrame H v)⁻¹).conjTranspose * (formFrame H v)⁻¹ = H.map v.embedding := by
  unfold formFrame
  generalize H.map v.embedding = A at h
  have h0 : 0 ≤ A := h.posSemidef.nonneg
  have h1 : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  have hd : IsUnit (CFC.sqrt A).det := by
    have : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 h.isUnit
    rw [← h1, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hh : (CFC.sqrt A).conjTranspose = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)).isHermitian
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hd, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hd, hh, h1]

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def logNormV_sq (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) (v : InfinitePlace K) : ℝ :=
  Real.log (opNormAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) (formFrame (Df.HV Bs.μ0))
    (Pi.basisFun K (Fin a)).dualBasis (dualFrame XM) v vm ^ 2)

def rowFrame (S : IndefData Df) (v : InfinitePlace K) : Matrix (Fin S.D) (Fin S.D) ℂ :=
  ((Real.sqrt (S.κ v) : ℝ) : ℂ) • S.XE v

def logNormPsi_sq (S : IndefData Df) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (Ψ : (Fin S.D → K) →ₗ[K] Module.Dual K (Fin a → K)) (v : InfinitePlace K) : ℝ :=
  Real.log (opNormAt (Pi.basisFun K (Fin S.D)) (rowFrame S)
    (Pi.basisFun K (Fin a)).dualBasis (dualFrame XM) v Ψ ^ 2)

open Classical in

def occurring (Df : DefSide Bs) : Finset Bs.Ix := Finset.univ.filter fun p => Df.Qp Bs.μ0 p ≠ ⊥

theorem occurring_nonempty (hW : Df.WF) (hp : Df.Pos) : (occurring Df).Nonempty := by
  by_contra hne
  have hall : ∀ p, Df.Qp Bs.μ0 p = ⊥ := by
    intro p
    by_contra h
    exact hne ⟨p, by simp [occurring, h]⟩
  have htop := hW.Qp_top
  simp only [hall, iSup_bot] at htop
  have : Nonempty (Fin (Df.dQ Bs.μ0)) := ⟨⟨0, hp⟩⟩
  exact bot_ne_top htop

def lamMin (hW : Df.WF) (S : IndefRows Df) (v : InfinitePlace K) : ℝ :=
  (occurring Df).inf' (occurring_nonempty hW S.pos) fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)

def TestMap (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) : Prop :=
  (∀ v, IsUnit (XM v).det) ∧ LinearMap.ker vm = Df.U Bs.μ0

def Factors (S : IndefData Df) {a : ℕ}
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (Ψ : (Fin S.D → K) →ₗ[K] Module.Dual K (Fin a → K)) : Prop :=
  ∀ F, Ψ ((S.ι Bs.μ0).mulVec ((Df.Pq Bs.μ0).mulVec F)) = vm F

def NormComparison (hW : Df.WF) (S : IndefRows Df) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (Ψ : (Fin S.D → K) →ₗ[K] Module.Dual K (Fin a → K)) : Prop :=
  ∀ v, logNormPsi_sq S.toIndefData XM Ψ v ≤ logNormV_sq Df XM vm v - lamMin hW S v

def MeanNormBound (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) (C f m N b L Sig : ℝ) : Prop :=
  meanInf K (logNormV_sq Df XM vm) ≤ C * f * m * N * b * L + C * m ^ 2 * N ^ 2 * Sig

def ScalarLowerBound (hW : Df.WF) (S : IndefRows Df) (C f m N L La : ℝ) : Prop :=
  -(C * f * m * N ^ 2 * La) ≤ meanInf K (lamMin hW S) ∧
  -(3 * C * f * m * N ^ 2 * L) ≤ -(C * f * m * N ^ 2 * La) ∧
  ∀ v, -(C * f * m * N ^ 2 * La) ≤ lamMin hW S v

def MeanBounds (C : ℝ) [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df)
    {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) (k t : ℕ) (x ε : ℝ) : Prop :=
  1 ≤ x → TestMap Df XM vm →
    MeanNormBound Df XM vm C (numF E) (Fintype.card Bs.J) (numN k (Fintype.card Bs.J) t)
      (numB x ε) (numL x ε) (depthSum S0 e) ∧
    ScalarLowerBound hW S C (numF E) (Fintype.card Bs.J) (numN k (Fintype.card Bs.J) t)
      (numL x ε) (numLa E x ε)

def InfinitePlaces (C : ℝ) [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df)
    {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (Ψ : (Fin S.D → K) →ₗ[K] Module.Dual K (Fin a → K))
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) (k t : ℕ) (x ε : ℝ) : Prop :=
  (TestMap Df XM vm → Factors S.toIndefData vm Ψ → NormComparison hW S XM vm Ψ) ∧
    MeanBounds C hW S XM vm E S0 e k t x ε

theorem le_lamMin (hW : Df.WF) (S : IndefRows Df) (v : InfinitePlace K) (c : ℝ)
    (h : ∀ p, Df.Qp Bs.μ0 p ≠ ⊥ → c ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) : c ≤ lamMin hW S v := by
  classical
  refine Finset.le_inf' _ _ fun p hp => h p ?_
  simpa [occurring] using hp

theorem numLa_eq (E : Type) [Field E] [NumberField E] {x : ℝ} (ε : ℝ) (hx : 0 < x) :
    numLa E x ε = numL x ε + Real.log x + Real.log (rootDiscr E) := by
  have hr : 0 < rootDiscr E := Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero E)) _
  have hb : 0 < numB x ε := Real.exp_pos _
  rw [numLa, Real.log_mul (mul_pos hx hb).ne' hr.ne', Real.log_mul hx.ne' hb.ne', numB, Real.log_exp]
  ring

example : numN 6 2 3 = 6 + 2 * (3 + ((6 + 2 - 1) + 6) + 1) := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledValuationFormula
section
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

open Formalism.DivisionValues Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K]

def primePow (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

def scaledAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) (B : Submodule (𝓞 K) (Fin d → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (primePow w n) B)

def ValGE_vw {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) (Fin d → K)) (y : Fin d → K)
    (c : ℝ) : Prop :=
  ∃ n : ℤ, c ≤ (n : ℝ) ∧ y ∈ scaledAt w n B

def DenLE_vw {d d' : ℕ} (w : HeightOneSpectrum (𝓞 K)) (φ : Matrix (Fin d') (Fin d) K)
    (A : Submodule (𝓞 K) (Fin d → K)) (B : Submodule (𝓞 K) (Fin d' → K)) (c : ℝ) : Prop :=
  ∃ a : ℤ, (a : ℝ) ≤ c ∧ ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A, φ.mulVec x ∈ scaledAt w (-a) B

def dualCoord {d : ℕ} (MM : Submodule (𝓞 K) (Fin d → K)) : Submodule (𝓞 K) (Fin d → K) where
  carrier := {y | ∀ x ∈ MM, y ⬝ᵥ x ∈ Set.range (algebraMap (𝓞 K) K)}
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    rintro y z hy hz x hx
    obtain ⟨a, ha⟩ := hy x hx
    obtain ⟨c, hc⟩ := hz x hx
    exact ⟨a + c, by rw [map_add, ha, hc, add_dotProduct]⟩
  smul_mem' := by
    rintro r y hy x hx
    obtain ⟨a, ha⟩ := hy x hx
    exact ⟨r * a, by rw [map_mul, ha, smul_dotProduct, Algebra.smul_def]⟩

def bound (C f m N L b Sig0 : ℝ) : ℝ :=
  C * f * b * N * m * (m * L + m * Sig0) + C * f * m ^ 2 * N ^ 2 * (L + Sig0) * b

def sigZero {P : Type} (S0 : Finset P) (e q : P → ℕ) : ℝ := ∑ v ∈ S0, (e v : ℝ) * Real.log (q v : ℝ)

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def ClauseA (S : IndefData Df) {d : ℕ} (MV : Submodule (𝓞 K) (Fin d → K))
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (dF : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Df.Mt (S.μ w)),
    ValGE_vw w MV ((v (S.μ w)).mulVec F) (-dF w)

def FormulaTwo (S : IndefData Df) {d : ℕ} (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K)
    (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), r (S.μ w) ≠ 0 ∧
    PSI * S.ι (S.μ w) * Df.Pq (S.μ w) = (r (S.μ w))⁻¹ • v (S.μ w)

def ClauseAConsequence (S : IndefData Df) {d : ℕ} (MV : Submodule (𝓞 K) (Fin d → K))
    (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K) (dF : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), DenLE_vw w PSI S.RR MV ((vw w (r (S.μ w)) : ℝ) + dF w)

omit [StarRing K] in

def ClauseB (dF : HeightOneSpectrum (𝓞 K) → ℝ) (B : ℝ) : Prop :=
  (Function.support dF).Finite ∧ ∑ᶠ w : HeightOneSpectrum (𝓞 K), 2 * lw w * dF w ≤ B

def DenominatorsLE (S : IndefData Df) [∀ t, Submodule.IsLattice K (Df.Mt t)] {d : ℕ}
    (MV : Submodule (𝓞 K) (Fin d → K)) [Submodule.IsLattice K MV]
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (B : ℝ) : Prop :=
  ∃ dF : HeightOneSpectrum (𝓞 K) → ℝ,
    ClauseA S MV v dF ∧
    (∀ (PSI : Matrix (Fin d) (Fin S.D) K) (r : Bs.Tup → K), FormulaTwo S v PSI r → ClauseAConsequence S MV PSI r dF) ∧
    ClauseB dF B

def FP (S : IndefData Df) [∀ t, Submodule.IsLattice K (Df.Mt t)] {d : ℕ}
    (MV : Submodule (𝓞 K) (Fin d → K)) [Submodule.IsLattice K MV]
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (C : ℝ) (f m N : ℕ) (L b Sig0 : ℝ) : Prop :=
  DenominatorsLE S MV v (bound C f m N L b Sig0)

def LatticeValuationBound' (S : IndefData Df) [∀ t, Submodule.IsLattice K (Df.Mt t)] {d : ℕ}
    (MM : Submodule (𝓞 K) (Fin d → K)) [Submodule.IsLattice K (dualCoord MM)]
    (v : ∀ t, Matrix (Fin d) (Fin (Df.nV t)) K) (C : ℝ) (f m N : ℕ) (L : ℝ)
    {P : Type} (S0 : Finset P) (e q : P → ℕ) : Prop :=
  FP S (dualCoord MM) v C f m N L (Real.exp L) (sigZero S0 e q)

def FPFamily (Ix : ℝ → Type) (K : ∀ x, Ix x → Type) [∀ x i, Field (K x i)] [∀ x i, NumberField (K x i)]
    [∀ x i, StarRing (K x i)] (Bs : ∀ x i, DefBase (K x i)) (Df : ∀ x i, DefSide (Bs x i))
    (S : ∀ x i, IndefData (Df x i)) [∀ x i t, Submodule.IsLattice (K x i) ((Df x i).Mt t)]
    (d : ∀ x, Ix x → ℕ) (MV : ∀ x i, Submodule (𝓞 (K x i)) (Fin (d x i) → K x i))
    [∀ x i, Submodule.IsLattice (K x i) (MV x i)]
    (v : ∀ x i t, Matrix (Fin (d x i)) (Fin ((Df x i).nV t)) (K x i))
    (f m N : ∀ x, Ix x → ℕ) (L b Sig0 : ∀ x, Ix x → ℝ) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Ix x,
    FP (S x i) (MV x i) (v x i) C (f x i) (m x i) (N x i) (L x i) (b x i) (Sig0 x i)

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula
end
end

