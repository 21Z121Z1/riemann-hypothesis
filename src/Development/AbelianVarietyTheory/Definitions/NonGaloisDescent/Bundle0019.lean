import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ThetaSchur (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T')) (𝓕 : Set (WO S T')), IsCovolOne (ratL T' S) μ 𝓕 →
    ∀ L : Module.End ℂ (WO S T' → ℂ), (∀ f, IsThetaFunO ψ S T' f → IsThetaFunO ψ S T' (L f)) →
      (∃ C : ℝ, ∀ f, IsThetaFunO ψ S T' f → nrm2 μ 𝓕 (L f) ≤ C * nrm2 μ 𝓕 f) →
      (∀ w f, IsThetaFunO ψ S T' f → L (heisO ψ S T' w f) = heisO ψ S T' w (L f)) →
      ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T' f → L f = c • f

abbrev levW (R : RealDat D A Ks) (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := levG _ (R.βW i) (R.datWp i R.triv)

def coef (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i)))
    (g : GA D (Wc D i)) : ℂ :=
  thetaIP μ 𝓕 (R.ωP i t (1, g) (R.vP i t)) (R.vP i t) / thetaIP μ 𝓕 (R.vP i t) (R.vP i t)

def jointVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W) :
    WO (Vc D i) (Wc D i) → ℂ :=
  R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)

def IsUnitVec (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : Prop :=
  ∀ ρ, ‖((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)‖ = 1

def val (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : (R.HW i (sg0 D A)).H) :
    GA D (Wc D i) → ℂ :=
  (R.HW i (sg0 D A)).e x fun ρ => v ρ

def AdjFormula (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → ∀ v, IsUnitVec R i v → ∀ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W),
    ∃ a : ℝ, 0 < a ∧ ∀ x y, ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ =
      (a : ℂ) * ∑ k, ∫ h in R.fdV i t,
        star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t)

def LevFix (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ k ∈ levW R i, ∀ P, R.ωP i t (1, k) (R.ptP i t P) = R.ptP i t P

def FactInf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), ∀ P P',
    thetaIP μ 𝓕 (R.ωP i t (1, u * γ) (R.ptP i t P)) (R.ptP i t P') =
      thetaIP μ 𝓕 (R.ωP i t (1, u) (R.ptP i t P)) (R.ptP i t P') * coef R i t μ 𝓕 γ

def RealLow (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ

def VecNe (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → thetaIP μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0 ∧
    ∃ v w, IsUnitVec R i v ∧ thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) ≠ 0

def trPair (R : RealDat D A Ks) (i : Fin D.R.m) (γ : GA D (Wc D i)) (x y : (R.HW i (sg0 D A)).H) : ℂ :=
  ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
    (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y))

def FinSum (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ a : ℝ, 0 < a ∧ ∀ x y,
    HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (a : ℂ) * (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y))
      ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ

def TrivAt (V : HSp D) (f : AE D) (g : GA D V) : Prop := ∀ a b, f * (mt V g - 1) a b = 0

def IsFinIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) : Prop :=
  ∃ ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε

def FinMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f →
    ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k →
      coef R i t μ 𝓕 (γ * k) = coef R i t μ 𝓕 γ * coef R i t μ 𝓕 k

def BadSupp (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f →
    ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → coef R i t μ 𝓕 k = 0

def latIndex (W : HSp D) (g : GA D W) : ℕ :=
  ((Formalism.L2.NTheta.LamHat W).map (finMat D.sp.cm.sig W.gram g).mulVecLin.toAddMonoidHom).relIndex (Formalism.L2.NTheta.LamHat W)

def GoodMod (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f →
    (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k →
      ‖coef R i t μ 𝓕 k‖ ^ 2 * (latIndex (Wc D i) k : ℝ) ^ (Vc D i).rank = 1

def IndexSum (W : HSp D) (n : ℕ) : Prop :=
  ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v f, IsFinIdem D v f →
    ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') →
      ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ s v

def LocSmall (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 →
    ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v f, IsFinIdem D v f →
      ∀ C : Finset (GA D (Wc D i)), (∀ g ∈ C, SuppF (Wc D i) f g ∧ g ∉ levW R i) →
        (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ levW R i → g = g') → ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ ≤ s v

def LevProd (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  levW R i ≤ GfC (Wc D i) ∧ (∀ k ∈ levW R i, levChi _ (R.βW i) (R.datWp i R.triv) k = 1) ∧
  ∃ cmp : HeightOneSpectrum (𝓞 D.host.F) → (GA D (Wc D i) →* GA D (Wc D i)),
    (∀ v f, IsFinIdem D v f → ∀ g, SuppF (Wc D i) f (cmp v g) ∧ TrivAt (Wc D i) f (g * (cmp v g)⁻¹)) ∧
    (∀ g ∈ GfC (Wc D i), (g ∈ levW R i ↔ ∀ v, cmp v g ∈ levW R i) ∧ {v | cmp v g ∉ levW R i}.Finite)

def TransLaws (R : RealDat D A Ks) (i : Fin D.R.m) : Prop :=
  (∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∃ C : Finset (GA D (Wc D i)), (∀ γ ∈ C, SuppF (Wc D i) f γ) ∧
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) ∧
  (∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∀ C : Finset (GA D (Wc D i)), (∀ γ ∈ C, SuppF (Wc D i) f γ) →
      IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C →
      ∀ y, ∃ y', (R.HW i (sg0 D A)).e y' = heckeOn (R.MW i (sg0 D A)) C ((R.HW i (sg0 D A)).e y) ∧
        ∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' = ∑ δ ∈ C, trPair R i (γ * δ) x y) ∧
  (∀ γ ∈ GfC (Wc D i), ∃ B : (R.HW i (sg0 D A)).H →L[ℂ] (R.HW i (sg0 D A)).H, ‖B‖ ≤ 1 ∧ ∀ x y, trPair R i γ x y = ⟪x, B y⟫_ℂ) ∧
  (∀ γ ∈ GfC (Wc D i), ∀ k ∈ levW R i, ∀ k' ∈ levW R i, ∀ x y, trPair R i (k * γ * k') x y = trPair R i γ x y) ∧
  (∀ γ ∈ GfC (Wc D i), ∀ x y, trPair R i γ⁻¹ x y = star (trPair R i γ y x)) ∧
  ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.NX
open scoped TensorProduct
open Classical

namespace GlobalTheory.TowerCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLevN (E : ExpSet D) (N : ℕ) : Prop :=
  N ≠ 0 ∧ (∀ p : ℕ, p.Prime → p ∣ N →
    p ≠ 2 ∧ Nat.Coprime p E.l ∧ (∀ a, p ≠ E.pde a) ∧ (∀ a, p ≠ E.gp a) ∧ D.host.cls p = .splitK ∧
      ¬ p ∣ Ideal.absNorm D.host.ccK) ∧ Squarefree N

def LevN (E : ExpSet D) : Type := {N : ℕ // IsLevN E N}

def LevN.one (E : ExpSet D) : LevN E :=
  ⟨1, one_ne_zero, fun _ hp h => absurd (Nat.dvd_one.1 h) hp.ne_one, squarefree_one⟩

def modN (E : ExpSet D) (N : ℕ) : ℕ := E.gp 0 * E.gp 1 * E.pde 0 * E.pde 1 * N

def KgW (E : ExpSet D) : Subgroup (GA D E.W) := levA E.W (Formalism.L2.DIV.Kg D.sp.cm E.W.gram E.βW E.Pg)

def InKN (E : ExpSet D) (N : ℕ) (κ : GA D E.W) : Prop :=
  κ ∈ levA E.W (Formalism.L2.DIV.Kg D.sp.cm E.W.gram E.βW (E.Pg ∪ E.Pd)) ∧
    ∃ Z : Matrix (Fin E.W.rank) (Fin E.W.rank) (Formalism.IndefR.Datum.EAf D), IsIntM Z ∧
      (E.βW⁻¹ * finE E.W κ * E.βW).val = 1 + N • Z

structure IsLevDat (E : ExpSet D) (N : ℕ) (e : AE D) (Φ : WO E.V E.W → ℂ) : Prop where
  idem : ∃ P1 : Finset (Formalism.L2.DIV.Pl D.host.E), (∀ L ∈ P1, ((N : ℕ) : 𝓞 D.host.E) ∈ L.asIdeal) ∧
    IsIdemSum e (E.Pg ∪ E.Pd ∪ P1)
  supp : ∀ x, Φ x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapO E.V E.W E.βV E.βW x)
  inv : ∀ u, IsHalf (cA D e) u → IsIntM (frMapO E.V E.W E.βV E.βW u) → ∀ x, Φ (x + modN E N • u) = Φ x

structure IsCompFn (E : ExpSet D) (N : ℕ) (c : GA D E.W → ℂ) : Prop where
  det : ∀ g g' : GA D E.W, (mt E.W g).det = (mt E.W g').det → c g = c g'
  left : ∀ γ ∈ GQ E.W, ∀ g, c (γ * g) = c g
  arch : ∀ u ∈ GinfC E.W, ∀ g, c (g * u) = c g
  right : ∀ κ, InKN E N κ → ∀ g, c (g * κ) = c g

def IsLevG (E : ExpSet D) (F : GA D E.W → ℂ) : Prop := ∀ κ ∈ KgW E, ∀ g, F (g * κ) = F g

def serAt (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) (s : GA D E.V) (φ : WO E.V E.W → ℂ) (P : C.Cf) :
    GA D E.W → ℂ :=
  fun g => thetaKO E.om s g (E.fock φ (C.rd P))

structure TowerRat (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) (Base : Set (GA D E.W → ℂ))
    (L1 FO : Subfield ℂ) where

  LQ : LevN E → Subfield ℂ

  Rat : ∀ N : LevN E, Submodule (LQ N) (GA D E.W → ℂ)
  numField : ∀ N, NumberField (LQ N)
  le_LQ : ∀ N, L1 ≤ LQ N
  zeta : ∀ (N : LevN E) (z : ℂ), z ^ modN E N.1 = 1 → z ∈ LQ N

  ser : ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ (e : AE D) (Φ φ : WO E.V E.W → ℂ), IsLevDat E N.1 e Φ → (∀ x, Φ x ∈ L') →
      IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) (cA D e) (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
      ∀ s ∈ GfC E.V, ∀ P : C.Cf, serAt E C s φ P ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ))

  comp : ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ c : GA D E.W → ℂ, IsCompFn E N.1 c → (∀ g, c g ∈ L') →
      ∀ F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ)), c * F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ))

  inj : ∀ (N : LevN E) (n : ℕ) (v : Fin n → GA D E.W → ℂ), (∀ a, v a ∈ Rat N) →
    LinearIndependent (LQ N) v → LinearIndependent ℂ v

  desc : ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ)), IsLevG E F → F ∈ Submodule.span L' Base

  field : ∀ N, LQ N ≤ FO

  one_le : LQ (LevN.one E) ≤ L1

def AdaptL (E : ExpSet D) (s : GA D E.V) : Prop :=
  ∃ k ∈ E.KV, ∃ h : GA D E.V, s = h * k ∧
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ((E.l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (mt E.V h - 1) a b = 0

structure TowerInt {E : ExpSet D} {O : Type} [CommRing O] {C : CoefLat E O} {Base : Set (GA D E.W → ℂ)}
    {L1 FO : Subfield ℂ} (_T : TowerRat E C Base L1 FO) (Λ : Subring ℂ) (BaseInt : Submodule Λ (GA D E.W → ℂ)) where

  Int : LevN E → Submodule Λ (GA D E.W → ℂ)

  serInt : ∃ c : ℕ, ∀ (N : LevN E) (e : AE D) (Φ φ : WO E.V E.W → ℂ), IsLevDat E N.1 e Φ → (∀ x, Φ x ∈ Λ) →
    IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) (cA D e) (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
      ∀ s ∈ GfC E.V, AdaptL E s → ∀ P ∈ C.LL s, ((E.l : ℂ) ^ c) • serAt E C s φ P ∈ Int N

  compInt : ∀ (N : LevN E) (c : GA D E.W → ℂ), IsCompFn E N.1 c → (∀ g, c g ∈ Λ) →
    ∀ F ∈ Int N, c * F ∈ Int N

  descInt : ∃ c₀ : ℕ, ∀ (N : LevN E) (F : GA D E.W → ℂ), F ∈ Int N → IsLevG E F → ((E.l : ℂ) ^ c₀) • F ∈ BaseInt

section Fields

variable (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) (Base : Set (GA D E.W → ℂ))
  (LQ : LevN E → Subfield ℂ) (Rat : ∀ N : LevN E, Submodule (LQ N) (GA D E.W → ℂ))
  (Λ : Subring ℂ) (BaseInt : Submodule Λ (GA D E.W → ℂ)) (Int : LevN E → Submodule Λ (GA D E.W → ℂ))

def SerField : Prop :=
  ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ (e : AE D) (Φ φ : WO E.V E.W → ℂ), IsLevDat E N.1 e Φ → (∀ x, Φ x ∈ L') →
      IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) (cA D e) (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
      ∀ s ∈ GfC E.V, ∀ P : C.Cf, serAt E C s φ P ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ))

def CompField : Prop :=
  ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ c : GA D E.W → ℂ, IsCompFn E N.1 c → (∀ g, c g ∈ L') →
      ∀ F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ)), c * F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ))

def InjField : Prop :=
  ∀ (N : LevN E) (n : ℕ) (v : Fin n → GA D E.W → ℂ), (∀ a, v a ∈ Rat N) →
    LinearIndependent (LQ N) v → LinearIndependent ℂ v

def DescField : Prop :=
  ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ)), IsLevG E F → F ∈ Submodule.span L' Base

def SerIntField : Prop :=
  ∃ c : ℕ, ∀ (N : LevN E) (e : AE D) (Φ φ : WO E.V E.W → ℂ), IsLevDat E N.1 e Φ → (∀ x, Φ x ∈ Λ) →
    IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) (cA D e) (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
      ∀ s ∈ GfC E.V, AdaptL E s → ∀ P ∈ C.LL s, ((E.l : ℂ) ^ c) • serAt E C s φ P ∈ Int N

def CompIntField : Prop :=
  ∀ (N : LevN E) (c : GA D E.W → ℂ), IsCompFn E N.1 c → (∀ g, c g ∈ Λ) →
    ∀ F ∈ Int N, c * F ∈ Int N

def DescIntField : Prop :=
  ∃ c₀ : ℕ, ∀ (N : LevN E) (F : GA D E.W → ℂ), F ∈ Int N → IsLevG E F → ((E.l : ℂ) ^ c₀) • F ∈ BaseInt

variable {E C Base LQ Rat Λ BaseInt Int}

def TowerRat.ofFields {L1 FO : Subfield ℂ} (h1 : ∀ N, NumberField (LQ N)) (h2 : ∀ N, L1 ≤ LQ N)
    (h3 : ∀ (N : LevN E) (z : ℂ), z ^ modN E N.1 = 1 → z ∈ LQ N) (hs : SerField E C LQ Rat) (hc : CompField E LQ Rat)
    (hi : InjField E LQ Rat) (hd : DescField E Base LQ Rat) (h4 : ∀ N, LQ N ≤ FO) (h5 : LQ (LevN.one E) ≤ L1) :
    TowerRat E C Base L1 FO :=
  ⟨LQ, Rat, h1, h2, h3, hs, hc, hi, hd, h4, h5⟩

def TowerInt.ofFields {L1 FO : Subfield ℂ} (T : TowerRat E C Base L1 FO) (hs : SerIntField E C Λ Int)
    (hc : CompIntField E Λ Int) (hd : DescIntField E Λ BaseInt Int) : TowerInt T Λ BaseInt :=
  ⟨Int, hs, hc, hd⟩

end Fields

section Covers

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.CoverRead

variable {E : ExpSet D} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (hV : T.V j σ = E.W)
  (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (z : ℂ)

def scaled (X : Set (GA D (T.V j σ) → ℂ)) : Set (GA D E.W → ℂ) := {F | ∃ φ ∈ X, F = z • castDict hV φ}

def ratOf (Cv : Cover T j σ) (K : Subfield ℂ) : Submodule K (GA D E.W → ℂ) :=
  Submodule.span K (scaled hV z (Cv.ratForms a n))

def placesIn {L : Type} [Field L] [NumberField L] (ι : L →+* ℂ) (Λ : Subring ℂ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {la | ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ}

def intOf (Cv : Cover T j σ) (Λ : Subring ℂ) : Submodule Λ (GA D E.W → ℂ) :=
  Submodule.span Λ (scaled hV z (Cv.intForms a n (placesIn Cv.σ₂ Λ)))

structure CovTie (Cv : LevN E → Cover T j σ) : Prop where
  unif : ∀ N, (Cv N).IsUnif
  lev : ∀ N, (Cv N).d.l₂.M = modN E N.1
  pos : ∀ N : LevN E, 0 < modN E N.1
  curve : ∀ N, GlobalTheory.FinalJoin.WeberIn T.Q.H (Cv N).d.c₂.F (modN E N.1) ∨ GlobalTheory.CompRat.CurveOver T.Q.H (Cv N).d.c₂.F (modN E N.1)
  lat : E.ΛW = L0c D E.W
  pl : ∀ PP ∈ E.Pg ∪ E.Pd, ((modN E 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal

end Covers

end GlobalTheory.TowerCov
end
end

