import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def KeyUnit {K : Type} [Field K] [NumberField K] {g : ℕ} (Λ : Submodule (𝓞 K) (Fin g → K)) (k : K) : Prop :=
  (∀ c : Matrix (Fin g) (Fin g) K, (∀ i, c i ∈ Λ) → IsIntegral ℤ (k * c.det ^ 4)) ∧
  (1 : K) ∈ Submodule.span (𝓞 K) {z | ∃ c : Matrix (Fin g) (Fin g) K, (∀ i, c i ∈ Λ) ∧ z = k * c.det ^ 4}

def Frame (κ : Rule) {K : Type} [Field K] [NumberField K] (F : SemiFib K) {K'' : Type} [Field K''] [NumberField K'']
    [Algebra K K''] (x : KeyIn K'') (hg : x.P.g = F.P₀.g) (ψ : x.P.A.left ⟶ F.P₀.A.left) {AA : Over (Sp (𝓞 K''))} [GrpObj AA]
    (φ : x.P.A.left ⟶ AA.left) : Prop :=
  IsOver F ψ φ ∧ IsSemiAbelian AA ∧ IsGrpPullback x.P.A AA (spMap (algebraMap (𝓞 K'') K'')) φ ∧
  (∀ k, IsVecOver (algebraMap K K'') ψ (F.v k) (x.v (k.cast hg.symm))) ∧ KeyUnit (latBC K'' F.lieLat) (κ K'' x : K'')

def TrFull {K : Type} [Field K] (P : PolAV (Sp K)) (N : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (f : K →+* Ω) (z : Over.mk (spMap f) ⟶ P.A), z ^ N = 1 →
    ∃ U : ThetaGrp P.A P.L (N : ℤ) (baseOver (Sp K)), FinOrdT P U ∧ spMap f ≫ U.pt.left = z.left

def IsTrAt {R : Type} [CommRing R] (x : KeyIn R) (m : ℕ) (z : Sp R ⟶ x.P.A.left) (s : (lbPow x.P.L (m ^ 2)).Sec) : Prop :=
  ∃ th U t, IsPolAVSectionInverseImage x.P (baseOver (Sp R)) x.th th ∧ FinOrdT x.P U ∧ Tr x.P x.rig m th U t ∧
    OnT x.P (baseOver (Sp R)) (m ^ 2) s t ∧ U.pt.left = z

def Val0 {K : Type} [Field K] (x : KeyIn K) (n : ℕ) (s : (lbPow x.P.L n).Sec) (β : K) : Prop :=
  ∀ i : x.P.L.ι, ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U i →
    valR (X := x.P.A.left) (eSec x.P.A) _ (s.f fun _ => i) = β * valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i).val ^ n

structure PB {K K' : Type} [Field K] [Field K'] (x : KeyIn K) (f : K →+* K') where

  x' : KeyIn K'
  hg : x'.P.g = x.P.g

  ψ : x'.P.A.left ⟶ x.P.A.left
  key : KeyPB x' x f
  fib : IsPolFibre f x.P x'.P ψ
  vec : ∀ i, IsVecOver f ψ (x.v (i.cast hg)) (x'.v i)

  w : ∀ n, LB.Iso ((lbPow x.P.L n).pull ψ) (lbPow x'.P.L n)
  gen : ∀ n, (w n).IsGen
  rig : ∀ (n : ℕ) (i : x.P.L.ι) (i' : x'.P.L.ι), ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (eSec x'.P.A) ⁻¹ᵁ x'.P.L.U i' →
    valR (X := x'.P.A.left) (eSec x'.P.A) _ ((w n).s (fun _ => i', fun _ _ => i)).val *
      f (valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i).val) ^ n =
      valR (X := Sp K') (𝟙 _) _ (x'.rig.s fun _ => i').val ^ n
  tr : ∀ (m : ℕ) z s, IsTrAt x m z s → ∃ z' s', z' ≫ ψ = spMap f ≫ z ∧ IsTrAt x' m z' s' ∧ SecMaps (w (m ^ 2)) (secPull s ψ) s'

structure Cx {K : Type} [Field K] (x : KeyIn K) (σ : K →+* ℂ) extends PB x σ where

  u : HolUnif x'.P.A x'.P.L x'.P.g

  Hm : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ

  χ : u.Λ → ℂ

  W : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ

  θ : (Fin x'.P.g → ℂ) → ℂ

  Fd : Set (Fin x'.P.g → ℂ)

  Ef : LinearMap.BilinForm ℤ u.Λ
  ah : u.IsAH Hm χ
  isRig : u.IsRig x'.rig
  fn : u.IsFn x'.th θ
  theta : u.IsThetaFn Hm χ 1 θ
  diff : ∀ i, u.IsDiff (W i) (x'.v i)
  fd : IsAddFundamentalDomain u.Λ Fd volume
  ef : ∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im
  efb : Function.Bijective Ef
  secs : ∀ (n : ℕ) s, ∃! Θ, u.IsThetaFn Hm χ n Θ ∧ u.IsFnPow n s Θ

def nrmAt {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (Θ : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) : ℝ :=
  ‖Θ z‖ ^ 2 * Real.exp (-(Real.pi * n * (hermForm Hm z z).re))

def meanSq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (Θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) : ℝ :=
  (∫ z in Fd, nrmAt Hm n Θ z) / (volume Fd).toReal

def Cx.nth {K : Type} [Field K] {x : KeyIn K} {σ : K →+* ℂ} (c : Cx x σ) : ℝ := meanSq c.Hm 1 c.θ c.Fd

def ExtAlong {X Y Z : Scheme.{0}} {M : LB X} {φ : Y ⟶ X} {N : LB Y} (w : LB.Iso (M.pull φ) N) (s : N.Sec) (j : Z ⟶ X)
    (φ' : Y ⟶ Z) : Prop :=
  ∃ t : (M.pull j).Sec, ∀ (i : N.ι) (p : PUnit → M.ι) (V : Y.Opens) (h₁ : V ≤ N.U i ⊓ (M.pull φ).U p)
    (h₂ : V ≤ φ' ⁻¹ᵁ (M.pull j).U p),
    resG Y (h₁.trans inf_le_left) (s.f i) =
      resG Y h₁ (@id (Γ(Y, N.U i ⊓ (M.pull φ).U p)ˣ) (w.s (i, p)) : Γ(Y, N.U i ⊓ (M.pull φ).U p)) *
        (φ'.appLE _ V h₂).hom (t.f p)

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsPow8F
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def IsPow8 {S : Scheme.{0}} (P P₈ : PolAV S) (d : ℕ) (pr : Fin 8 → (P₈.A ⟶ P.A)) (inc : P.A ⟶ P₈.A) : Prop :=
  (∀ u, IsMonHom (pr u)) ∧ IsMonHom inc ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ P.A)), ∃! x : T ⟶ P₈.A, ∀ u, x ≫ pr u = y u) ∧
    (∀ u, inc ≫ pr u = if u = 0 then 𝟙 P.A else 1) ∧ LBIso (P₈.L.pull inc.left) (lbPow P.L d)

def IsPow8F {K : Type} [Field K] [NumberField K] (F F₈ : SemiFib K) (d : ℕ) (e : Fin 8 × Fin F.P₀.g ≃ Fin F₈.P₀.g) : Prop :=
  ∃ (pr : Fin 8 → (F₈.P₀.A ⟶ F.P₀.A)) (inc : F.P₀.A ⟶ F₈.P₀.A) (prG : Fin 8 → (F₈.G ⟶ F.G)),
    IsPow8 F.P₀ F₈.P₀ d pr inc ∧ (∀ u, IsMonHom (prG u)) ∧
    (∀ (T : Over (Sp (𝓞 K))) (y : Fin 8 → (T ⟶ F.G)), ∃! x : T ⟶ F₈.G, ∀ u, x ≫ prG u = y u) ∧
    (∀ u, F₈.φ ≫ (prG u).left = (pr u).left ≫ F.φ) ∧
    ∀ u i u', F₈.v (e (u, i)) ≫ pr u' = if u = u' then F.v i else toUnit _ ≫ η[F.P₀.A]

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def KeyAtMap {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R')
    (φ : x'.P.A.left ⟶ x.P.A.left) : Prop :=
  ∃ (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left

def LocSet {R K : Type} [CommRing R] [Field K] (f : R →+* K) (x : KeyIn K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {φ : x.P.A.left ⟶ G.left} {M : RigLB G} {m : ℕ} (w : LB.Iso (M.L.pull φ) (lbPow x.P.L (m ^ 2)))
    (y : Fin x.P.g → (epsR R ⟶ G)) : Prop :=
  IsSemiAbelian G ∧ IsGrpPullback x.P.A G (spMap f) φ ∧ Nonempty (CubicalStr G M) ∧ w.IsGen ∧ RigPow f w x.rig ∧
    IsLieBasis y ∧ ∀ i, IsVecOver f φ (y i) (x.v i)

def SecAgree {X Y Z W : Scheme.{0}} {N : LB Z} {a : X ⟶ Z} {b : Y ⟶ Z} (s : (N.pull a).Sec) (t : (N.pull b).Sec)
    (p : W ⟶ X) (q : W ⟶ Y) : Prop :=
  ∀ (i : N.ι) (O : W.Opens) (h₁ : O ≤ p ⁻¹ᵁ (N.pull a).U fun _ => i) (h₂ : O ≤ q ⁻¹ᵁ (N.pull b).U fun _ => i),
    (p.appLE _ _ h₁).hom (s.f fun _ => i) = (q.appLE _ _ h₂).hom (t.f fun _ => i)

def IntU {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) (w₀ : GlobalTheory.UT.W0 U) (t : GlobalTheory.UT.SecA A F k) : Prop :=
  ∃ (σ' : U.SecGF F k) (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))),
    GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
      (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ' ∧
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F) 1

def AllUQ (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (_ : Unif (IsLocalRing.maximalIdeal V) D A G) (_ : D.toPre.X → ℤ) {F : Type} [Field F] [Algebra (FractionRing V) F],
    AddValuation F (WithTop ℚ) → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), DVR.QForm.IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      DVR.ValOver ϖ F v → P U Q v

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

section Generic

variable {G : Type} [Group G]

def locPart (T K : Subgroup G) (x : G) : Subgroup G := T ⊓ K.map (MulAut.conj x).toMonoidHom

def volRat (U V : Subgroup G) : ℝ := (V.relIndex U : ℝ) / (U.relIndex V : ℝ)

def maxWt (T K : Subgroup G) (x : G) : ℝ := ⨆ h : G, volRat (locPart T K h) (locPart T K x)

def orbSum (θ : G →* G) (K : Subgroup G) (δ : G) (w : G → ℝ) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    (w (Quotient.out q) : ℂ) * GlobalTheory.BCT.avg fun k : K => f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k))

def twOrbM (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (maxWt (GlobalTheory.BCT.twCent θ δ) K) f

def twOrbU (θ : G →* G) (K : Subgroup G) (δ : G) (U : Subgroup G) (f : G → ℂ) : ℂ :=
  orbSum θ K δ (fun x => volRat U (locPart (GlobalTheory.BCT.twCent θ δ) K x)) f

theorem volRat_self (V : Subgroup G) : volRat V V = 1 := by
  simp [volRat, Subgroup.relIndex_self]

end Generic

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def frobR (r : ℕ) : Kn p K r →+* Kn p K r where
  toFun x := ⟨frobK p K (x : PadicAlgCl p), Kn_stable p K r (frobK p K) x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

def intR (r : ℕ) : Subring (Kn p K r) := (Obar p).toSubring.comap (algebraMap (Kn p K r) (PadicAlgCl p))

def intK : Subring K := (Obar p).toSubring.comap (algebraMap K (PadicAlgCl p))

def sig (n r : ℕ) : GL (Fin n) (Kn p K r) →* GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.map (frobR p K r)

def Kint (n r : ℕ) : Subgroup (GL (Fin n) (Kn p K r)) :=
  (GeneralLinearGroup.map (intR p K r).subtype).range

def KintK (n : ℕ) : Subgroup (GL (Fin n) K) :=
  (GeneralLinearGroup.map (intK p K).subtype).range

def nrm (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) : GL (Fin n) (Kn p K r) :=
  (List.map (fun i => (⇑(sig p K n r))^[i] δ) (List.range r)).prod

def SigConj (n r : ℕ) (δ δ' : GL (Fin n) (Kn p K r)) : Prop :=
  ∃ g : GL (Fin n) (Kn p K r), δ' = g⁻¹ * δ * sig p K n r g

def twCentR (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) : Subgroup (GL (Fin n) (Kn p K r)) :=
  GlobalTheory.BCT.twCent (sig p K n r) δ

def TO (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (φ : GL (Fin n) (Kn p K r) → ℂ) : ℂ :=
  twOrbM (sig p K n r) (Kint p K n r) δ φ

def TOU (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (U : Subgroup (GL (Fin n) (Kn p K r)))
    (φ : GL (Fin n) (Kn p K r) → ℂ) : ℂ :=
  twOrbU (sig p K n r) (Kint p K n r) δ U φ

def Orb (n : ℕ) (γ : GL (Fin n) K) (f : GL (Fin n) K → ℂ) : ℂ :=
  twOrbM (MonoidHom.id _) (KintK p K n) γ f

def OrbU (n : ℕ) (γ : GL (Fin n) K) (U : Subgroup (GL (Fin n) K)) (f : GL (Fin n) K → ℂ) : ℂ :=
  twOrbU (MonoidHom.id _) (KintK p K n) γ U f

def pDiag (n r : ℕ) (a : Fin n → ℤ) : GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal fun i => (p : Kn p K r) ^ a i) (by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))

def phiR (n r : ℕ) (a : Fin n → ℤ) (g : GL (Fin n) (Kn p K r)) : ℂ :=
  if ∃ k₁ ∈ Kint p K n r, ∃ k₂ ∈ Kint p K n r, g = k₁ * pDiag p K n r a * k₂ then 1 else 0

def unitK (n : ℕ) (g : GL (Fin n) K) : ℂ := if g ∈ KintK p K n then 1 else 0

def KotInv (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (m : ℤ) : Prop :=
  ‖((GeneralLinearGroup.det δ : (Kn p K r)ˣ) : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ m

def unif : Kˣ :=
  if h : ∃ π : Kˣ, vK p K π = 1 then h.choose
  else Units.mk0 (p : K) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)

def unifR (r : ℕ) : (Kn p K r)ˣ :=
  Units.map (IntermediateField.inclusion (show K ≤ Kn p K r from le_sup_left)).toRingHom.toMonoidHom (unif p K)

def piDiag (n r : ℕ) (a : Fin n → ℤ) : GL (Fin n) (Kn p K r) :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal fun i => ((unifR p K r ^ a i : (Kn p K r)ˣ) : Kn p K r)) (by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _)

def phiRu (n r : ℕ) (a : Fin n → ℤ) (g : GL (Fin n) (Kn p K r)) : ℂ :=
  if ∃ k₁ ∈ Kint p K n r, ∃ k₂ ∈ Kint p K n r, g = k₁ * piDiag p K n r a * k₂ then 1 else 0

def KotInvU (n r : ℕ) (δ : GL (Fin n) (Kn p K r)) (m : ℤ) : Prop :=
  vK p (Kn p K r) (GeneralLinearGroup.det δ) = m

end GlobalTheory.LKLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory

namespace GlobalTheory.JSW.WhitModel

open GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem mem_NA_iff (u : GA E a) : u ∈ NA E a ↔ ∃ X : Pos a → Ad E, u = uGL X := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun p => (u : Matrix (Fin a) (Fin a) (Ad E)) p.1.1 p.1.2, Units.ext ?_⟩
    refine Matrix.ext fun i j => ?_
    rw [coe_uGL, uMat_apply]
    split_ifs with h h'
    · subst h; exact h1 i
    · rfl
    · exact h0 i j (lt_of_le_of_ne (not_lt.1 h') (Ne.symm h))
  · rintro ⟨X, rfl⟩
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [coe_uGL, uMat_apply, if_neg (ne_of_gt h), dif_neg (not_lt.2 h.le)]
    · rw [coe_uGL, uMat_apply, if_pos rfl]

theorem superDiag_uGL (X : Pos a → Ad E) : GlobalTheory.Whittaker.superDiag (uGL X) = supSum 0 X := by
  classical
  unfold GlobalTheory.Whittaker.superDiag supSum
  refine (Finset.sum_sigma' _ _ _).trans ?_
  symm
  refine Finset.sum_bij (fun p _ => ⟨p.1.1, p.1.2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp.1]
  · intro p _ q _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact ⟨⟨(i, j), by rw [Fin.lt_def]; simp only; omega⟩, by simp [h], rfl⟩
  · intro p _
    simp only [coe_uGL, uMat_apply]
    rw [if_neg (ne_of_lt p.2), dif_pos p.2]

theorem whit_mul {F : GA E a → ℂ} (hc : Continuous F) (hl : AutomorphicForm.IsLeftInvariant F) {u : GA E a}
    (hu : u ∈ NA E a) (g : GA E a) : whit F (u * g) = psiN u * whit F g := by
  obtain ⟨X, rfl⟩ := (mem_NA_iff u).1 hu
  rw [psiN, superDiag_uGL]
  exact MultiplicityOne.whittaker_uGL_mul hc hl X g

theorem whit_rank_one {F : GA E 1 → ℂ} (hc : Continuous F) (g : GA E 1) : whit F g = F g := by
  rw [whit, whittaker_eq_partialCoeff hc one_pos, partialCoeff_self]

theorem exists_psiN_ne_one : ∃ u ∈ NA E 2, psiN u ≠ 1 := by
  by_contra h
  push Not at h
  refine GroundTheory.Global.adelicChar_ne_one (K := E) (AddChar.ext _ _ fun x => ?_)
  have h1 := h (uGL fun _ => x) ((mem_NA_iff _).2 ⟨_, rfl⟩)
  have h2 : GlobalTheory.Whittaker.superDiag (uGL (n := 2) fun _ => x) = x := by
    simp [GlobalTheory.Whittaker.superDiag, Finset.sum_filter, uMat_apply]
  rw [psiN, h2] at h1
  exact Subtype.ext h1

theorem whit_const_two : whit (fun _ : GA E 2 => (1 : ℂ)) 1 = 0 := by
  obtain ⟨u, hu, h⟩ := exists_psiN_ne_one (E := E)
  have h1 := whit_mul (F := fun _ : GA E 2 => (1 : ℂ)) continuous_const (fun _ _ => rfl) hu 1
  have h2 : whit (fun _ : GA E 2 => (1 : ℂ)) (u * 1) = whit (fun _ : GA E 2 => (1 : ℂ)) 1 := rfl
  rw [h2] at h1
  by_contra h0
  exact h ((mul_eq_right₀ h0).1 h1.symm)

theorem psiLoc_eq (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    psiLoc w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := by
  classical
  rw [psiLoc, GroundTheory.Global.localAdelicChar_apply]
  congr 2

theorem diagPow_val {K : Type} [CommRing K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    (diagPow ϖ l : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun i => (ϖ : K) ^ l i := by
  simp [diagPow]

theorem diagPow_zero {K : Type} [CommRing K] {n : ℕ} (ϖ : Kˣ) : diagPow ϖ (0 : Fin n → ℕ) = 1 :=
  Units.ext (by rw [diagPow_val]; simp)

theorem tl_comp (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ))
    (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (tl ϖ l) = diagPow (ϖ w) (l w) := by
  classical
  have hc : ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := fun _ => rfl
  have key : ∀ L : List (HeightOneSpectrum (𝓞 E)), L.Nodup →
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E))
        (L.map fun v => finGL E a (locGL E a v (diagPow (ϖ v) (l v)))).prod =
        if w ∈ L then diagPow (ϖ w) (l w) else 1 := by
    intro L hL
    induction L with
    | nil => simp
    | cons v L ih =>
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, ih hL.2, hc, pFin_finGL]
      by_cases h : w = v
      · subst h; rw [pLoc_locGL, if_neg hL.1, if_pos List.mem_cons_self, mul_one]
      · rw [pLoc_locGL_of_ne h, one_mul]; simp [h]
  rw [tl, key _ (Finset.nodup_toList _)]
  split_ifs with h
  · rfl
  · rw [Finset.mem_toList, Finsupp.notMem_support_iff] at h
    rw [h, diagPow_zero]

theorem loc_mem_supS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) (w.adicCompletion E)) : finGL E a (locGL E a w g) ∈ supS E a S ↔ w ∈ S ∨ g = 1 := by
  have hc : ∀ v, ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) g) := fun _ _ => rfl
  constructor
  · intro h
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · have := h w hw
      rw [hc, pFin_finGL, pLoc_locGL] at this
      exact Or.inr this
  · rintro (h | rfl) v hv
    · rw [hc, pFin_finGL, pLoc_locGL_of_ne (fun e : v = w => hv (by rw [e]; exact h))]
    · simp

theorem NA_inter_supS_subset (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) :
    NA E (m + 1) ∩ supS E (m + 1) S ⊆ mirS E S m := by
  rintro u ⟨⟨h0, h1⟩, hS⟩
  refine ⟨hS, fun j => ?_⟩
  split_ifs with h
  · subst h; exact h1 _
  · exact h0 _ _ (lt_of_le_of_ne (Fin.le_last j) h)

theorem isRapidInf_dirac (c : ℂ) (y : GL (Fin a) (Cinf E)) :
    IsRapidInf (Measure.dirac ()) (fun _ => c) (fun _ : Unit => y) :=
  ⟨measurable_const, measurable_const, fun _ => integrable_const _⟩

theorem not_isRapidInf_const : ¬ IsRapidInf (volume : Measure ℝ) (fun _ => 1) (fun _ => (1 : GL (Fin a) (Cinf E))) := by
  rintro ⟨-, -, h⟩
  have := h 0
  simp [integrable_const_iff] at this
  exact (measure_ne_top (volume : Measure ℝ) Set.univ) Real.volume_univ

variable [IsTotallyComplex E]

theorem inf_mem_supS (S : Finset (HeightOneSpectrum (𝓞 E))) (y : GL (Fin a) (Cinf E)) : infGL E a y ∈ supS E a S := by
  intro v _
  change GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) (infGL E a y)) = 1
  rw [pFin_infGL]; exact map_one _

theorem mspanR_triv (ha : a ≤ 1) : mspanR (CuspSub.triv E ha) = Submodule.span ℂ {fun _ => 1} := by
  apply le_antisymm
  · refine sInf_le ⟨fun φ hφ => ?_, fun F hF h => ?_, fun F hF X _ ν _ k γ _ => ?_⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hF
      exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hF
      exact Submodule.mem_span_singleton.2 ⟨∫ x, k x * c ∂ν, by funext g; simp⟩
  · refine le_sInf fun S hS => Submodule.span_le.2 ?_
    rintro _ rfl
    exact hS.1 (oneFn E a) (Submodule.mem_span_singleton_self _)

end GlobalTheory.JSW.WhitModel
end
end

