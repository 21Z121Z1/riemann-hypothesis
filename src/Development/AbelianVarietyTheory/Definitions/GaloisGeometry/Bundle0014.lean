import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetStepEqZeroExample
section
noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

section Exp

open MvPolynomial Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {ι : Type} [Fintype ι] {a b : ℕ}

def expFn (r : ℂ) (ap : ι → Matrix (Fin a) (Fin b) ℂ) (z : VCx ι a b) : ℂ :=
  r * Complex.exp (∑ k : DVar ι a b, ap k.1 k.2.2 k.2.1 * z k.1 k.2.1 k.2.2)

def inclMat (K : Type) [Field K] (ι : Type) (a b : ℕ) : ι → Matrix (Fin a) (Fin b) K := fun _ α β => if (α : ℕ) = β then 1 else 0

end Exp

namespace ChSrc

open Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {X : Fields} {R : Ranks} (σ : X.K →+* ℂ)

theorem jetInVV_trueWt (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) : JetInVV X.K (trueWt hc i) (trueWt hc (i + 1)) (nuEnd hc i) := by
  have hab : R.N i < R.N (i + 1) := by
    simp only [Ranks.N]
    nlinarith
  have hW : WtCompat hab (trueWt hc i) (trueWt hc (i + 1)) (sD hc i) (sS hc i) (nuEnd hc i) := by
    refine ⟨fun τ a => ?_, fun τ j hj => trueWt_new hc hi τ j (by omega), fun τ => nuEnd_cast hc hi τ⟩
    have h1 := trueWt_old hc hi τ (Fin.castLE hab.le a) (by simp)
    simp only [Fin.coe_castLE] at h1
    rw [h1]
    ring
  haveI : Infinite X.K := Infinite.of_injective (Nat.cast : ℕ → X.K) Nat.cast_injective
  intro J P hP
  exact GlobalTheory.JetPoint.jetMap_mem hab.le (nuEnd hc i) P _
    (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem X.K X.Tau _ _ hab _ _ _ _ _ hW ap P hP) J

def exampleJetChain (hc : X.Tau → HCParam R) : ChSrc X R :=
  { toyExample hc with
    kk := fun i _ _ =>
      { k := fun _ _ => jetOp (trueWt hc i) (trueWt hc (i + 1)) (ptTable (inclMat X.K X.Tau _ _)) (nuEnd hc i)
        equiv := fun _ _ _ _ => rfl } }

def toyExpThetaFamily (hc : X.Tau → HCParam R) : (exampleJetChain hc).ThFam := fun _ _ _ => expFn Complex.I (inclMat ℂ X.Tau _ _)

end ChSrc

end GlobalTheory.GO
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def labIn (n : ℕ) (s : List ℕ) : List ℤ :=
  s.map (fun a => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a => -(a : ℤ))

def IsLabElt (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (x : Bridge.Gf V) : Prop :=
  ∃ (e f : AE D) (ϖ : 𝓞 D.host.E) (α : GA D V), IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ α ∈ GfC V ∧
    (x : GL _ _) = finHom V α ∧ SuppF V f α ∧ DivAt V e (ϖ : D.host.E) d α

def IsLocElt (V : HSp D) (P : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ (e f : AE D) (g : GA D V), IsPrimeIdem P e f ∧ g ∈ GfC V ∧ (x : GL _ _) = finHom V g ∧ SuppF V f g

def SphOp (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (R : Finset (GA D V)) : Prop :=
  Hecke₂ V (KsphC V ∅) (fun _ => 1) ∅ P d R

def IsLab (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Prop := ∃ R, SphOp V P d R

open Classical in

def rep (V : HSp D) (P : Pl D.host.E) (d : List ℤ) : Finset (GA D V) :=
  if h : IsLab V P d then h.choose else ∅

def hyp (V : HSp D) (P : Pl D.host.E) : Set (GA D V) :=
  {k | k ∈ KsphC V ∅ ∧ ∃ e f, IsPrimeIdem P e f ∧ SuppF V f k}

def opOf {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (c : List ℤ →₀ ℂ) : Module.End ℂ M :=
  c.sum fun d z => z • ∑ γ ∈ rep V P d, π γ

def hk (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  c.sum fun d z => z • heckeLin V (rep V P d)

def hkF (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ) (F : Bridge.Gf V → W) :
    Bridge.Gf V → W :=
  fun h => c.sum fun d z => z • ∑ γ ∈ rep V P d, F (h * (finHom V).rangeRestrict γ)

def dualC (c : List ℤ →₀ ℂ) : List ℤ →₀ ℂ := Finsupp.mapDomain dualLab c

open Classical in

def evC (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (c : List ℤ →₀ ℂ) : ℂ :=
  c.sum fun d z => if IsLab V P d then z * a d else 0

def splitC (n : ℕ) (z : ℕ → ℂ) : List ℤ →₀ ℂ := ∑ j ∈ Finset.range (n + 1), Finsupp.single (splitLab n j) (z j)

def UnrPl (P : Pl D.host.E) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ e f, IsPrimeIdem P e f → ∀ x : (AE D)ˣ, f * ((x : AE D) - 1) = (x : AE D) - 1 →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def IsVacAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : Pl D.host.E) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ e f', IsPrimeIdem P e f' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True),
    IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f

section Pair

variable (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E)

def VacFix : Prop := ∀ f, IsVacAt ψ S T P f → ∀ k ∈ hyp S P, ∀ k' ∈ hyp T P, om (k, k') f = f

def Match (cS cT : List ℤ →₀ ℂ) : Prop :=
  ∀ f, IsVacAt ψ S T P f →
    opOf (om.comp (MonoidHom.inl _ _)) P cS f = opOf (om.comp (MonoidHom.inr _ _)) P cT f

def SphCorr : Prop :=
  VacFix ψ om P ∧ (∀ cT, ∃ cS, Match ψ om P cS cT) ∧ ∀ cS, ∃ cT, Match ψ om P cS cT

end Pair

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure Core (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP

variable (R : RealDat D A Ks)

def Good (t : T) (P : Pl D.host.E) : Prop := ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P

def IsSF (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ v, v ∈ SF ↔ ∃ PP ∈ R.Pg, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def CorrAll (t : T) (P : Pl D.host.E) : Prop :=
  (∀ k, k + 1 < D.R.m → SphCorr R.ψ (R.ωY t k) P) ∧ SphCorr R.ψ (R.ωX t) P ∧ ∀ i, SphCorr R.ψ (R.ωP i t) P

def FixAll (t : T) (P : Pl D.host.E) : Prop :=
  (∀ k, k + 1 < D.R.m → VacFix R.ψ (R.ωY t k) P) ∧ VacFix R.ψ (R.ωX t) P ∧ ∀ i, VacFix R.ψ (R.ωP i t) P

def SchurAll : Prop :=
  (∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv))
    (R.νY t j) (R.fdY t j)) ∧
  SchurMult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.ν0 R.fd0 ∧
  ∀ i, SchurMult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (R.νW i) (R.fdW i)

def MatchE (t : T) (P : Pl D.host.E) (cX c0 : List ℤ →₀ ℂ) : Prop :=
  ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) →
    R.HE.e (R.Th t y') = postOn (R.MY 0) (hk (Yc D 0) P c0) (R.HE.e (R.Th t y))

def MatchW (i : Fin D.R.m) (t : T) (P : Pl D.host.E) (cV cW : List ℤ →₀ ℂ) : Prop :=
  ∀ y y' : (R.HV i t).H, (R.HV i t).e y' = hkF (Vc D i) P cV ((R.HV i t).e y) →
    (R.HW i (sg0 D A)).e (R.thG i t y') = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P cW) ((R.HW i (sg0 D A)).e (R.thG i t y))

def TwoSided (t : T) (P : Pl D.host.E) : Prop :=
  ((∀ cX, ∃ c0, MatchE R t P cX c0) ∧ ∀ c0, ∃ cX, MatchE R t P cX c0) ∧
    ∀ i, (∀ cV, ∃ cW, MatchW R i t P cV cW) ∧ ∀ cW, ∃ cV, MatchW R i t P cV cW

def EEc (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Pl D.host.E → List ℤ → ℂ) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF c).comap R.HE.e

def Wcc (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ) :
    Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap
      (R.HW i _).e

def eH (i : Fin D.R.m) : Module.End ℂ (R.HW i (sg0 D A)).H :=
  ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g

def IsOpsE (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H) : Prop :=
  ∀ P, Good R A.μ0 P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (hk (Yc D 0) P c) (R.HE.e x)

def IsOpsW (i : Fin D.R.m) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HW i (sg0 D A)).H) : Prop :=
  ∀ P, Good R A.μ0 P → ∀ c x, (R.HW i _).e (h P c x) = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P c) ((R.HW i _).e x)

def IsOpsX (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX t).H) : Prop :=
  ∀ P, Good R t P → ∀ c x, (R.HX t).e (h P c x) = hkF D.sp.X' P c ((R.HX t).e x)

def IsOpsV (i : Fin D.R.m) (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) : Prop :=
  ∀ P, Good R t P → ∀ c x, (R.HV i t).e (h P c x) = hkF (Vc D i) P c ((R.HV i t).e x)

def NormalFam {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (ok : Pl D.host.E → Prop)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ H) : Prop :=
  (∀ P P', ok P → ok P' → ∀ c c', Commute (h P c) (h P' c')) ∧
    ∀ P, ok P → ∀ c, LinearMap.adjoint (h P c) = h P (dualC (Finsupp.mapRange star (star_zero ℂ) c))

end Real

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def locH (σ : L →+* L) (δ : L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : L :=
  δ * Matrix.trace (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (y.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * x)

structure LocPair (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M) : Prop where
  unr : Formalism.UG.IsUnramInv ϖ σ q
  odd : Odd q
  intS : JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)
  intT : JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L)
  hermS : ∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i
  hermT : ∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i
  delta : Valued.v δ = 1 ∧ σ δ = -δ
  psi_int : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1
  psi_ne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1
  rho_zero : ρ 0 = 1
  rho_mul : ∀ x y, ρ x * ρ y = ψ ((locH σ δ JS JT x y + σ (locH σ δ JS JT x y)) / 2) • ρ (x + y)
  span : Submodule.span ℂ {w | ∃ x s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) ∧ w = ρ x s} = ⊤
  norm : ∀ g h x, ω (g, h) * ρ x =
    ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * ω (g, h)
  fix : ∀ (g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) (h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)), (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    ∀ s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) → ω (g, h) s = s

def LocVac {n n' : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (s : M) : Prop :=
  ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s

end Local

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.TopStep

section Aut

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem card_autU (N : Submodule (𝓞 E) (Sp E n)) : Nat.card (autU N) = Nat.card (Mem.Col2.autO N) :=
  Nat.card_congr
    { toFun := fun γ => ⟨γ.1.1, γ.1.2, mem_autLat.2 (mem_autU.1 γ.2)⟩
      invFun := fun γ => ⟨⟨γ.1, γ.2.1⟩, mem_autU.2 (mem_autLat.1 γ.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_autU_dvd_tilN (N : Submodule (𝓞 E) (Sp E n)) : Nat.card (autU N) ∣ Nat.card (autU (tilN N)) := by
  let f : autU N →* autU (tilN N) :=
    ((extUH rfl).comp (autU N).subtype).codRestrict _ fun γ => mem_autU.2 (by
      have h := tilN_gmap γ.1.1 N
      rw [mem_autU.1 γ.2] at h
      exact h.symm)
  refine Subgroup.card_dvd_of_injective f fun a b hab => Subtype.ext (Subtype.ext (LinearEquiv.ext fun x => ?_))
  have h : extE a.1.1 = extE b.1.1 := congrArg (fun z : autU (tilN N) => z.1.1) hab
  have h1 := initL_extE a.1.1 (incl E n x)
  rw [h, initL_extE] at h1
  have h2 : initL E n (incl E n x) = x := by
    funext i
    simp [initL, incl, LinearMap.funLeft_apply]
  rw [h2] at h1
  exact h1.symm

theorem exists_card_autU_dvd {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) (k : ℕ) :
    ∃ N' : Submodule (𝓞 E) (Sp E (n + k)), IsSdLat N' ∧ Nat.card (autU N) ∣ Nat.card (autU N') := by
  induction k with
  | zero => exact ⟨N, hN, dvd_rfl⟩
  | succ k ih =>
    obtain ⟨N', h1, h2⟩ := ih
    exact ⟨tilN N', ⟨tilN_lattice h1.1, tilN_unimodular h1.2⟩, h2.trans (card_autU_dvd_tilN N')⟩

theorem card_autU_dvd_DGam (hE : PosStar E) (R : Ranks) (hm : 1 ≤ R.m) {i : ℕ} (hi : i ≤ R.m) {N : Submodule (𝓞 E) (Sp E (R.N i))}
    (hN : IsSdLat N) : Nat.card (autU N) ∣ Mem.Col2.DGam E R := by
  have hle : R.N i ≤ R.N R.m := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨N', h1, h2⟩ := exists_card_autU_dvd hN k
  refine h2.trans ?_
  rw [card_autU]
  exact Mem.Col2.dvd_DGam hE R (hk ▸ Mem.Col2.N_mem_gamRanks R hm le_rfl) h1.1 h1.2

end Aut

section Rho

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ : X.K →+* ℂ)
  (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ)

def muInvPt (i : ℕ) {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) : X.K :=
  muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) p.deco.1.N (frsF sel mu p)

def rhoPt (i : ℕ) {u : Pr.Word} (p : ChPt (R := R) sel mu u i) : ℂ :=
  σ (muInvPt Ch sel mu cst i p) * chi (R.N i) p.deco.1.N ^ (-((R.N (i + 1) / 2 : ℕ) : ℤ))

def rhoPt' (i : ℕ) {u : Pr.Word} (p : ChPt (R := R) sel mu u (i + 1)) : ℂ :=
  (σ (muInvPt Ch sel mu cst i p))⁻¹ * chi (R.N (i + 1)) p.deco.1.N ^ (((R.N i / 2 : ℕ) : ℤ))

def RhoUnit : Prop :=
  (∀ i, i < R.m → ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
    ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) N fr)‖ = 1) ∧
  ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → ‖chi n N‖ = 1

def ChiSplit (A : Amb X) : Prop :=
  ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    A.chiF a b N N' = chi a N ^ (((b / 2 : ℕ) : ℤ)) * chi b N' ^ (-((a / 2 : ℕ) : ℤ))

variable {Ch sel mu cst σ chi}

theorem RhoUnit.norm_rhoPt (h : RhoUnit Ch sel mu cst σ chi) {i : ℕ} (hi : i < R.m) {u : Pr.Word} (p : ChPt (R := R) sel mu u i) :
    ‖rhoPt Ch sel mu cst σ chi i p‖ = 1 := by
  rw [rhoPt, norm_mul, norm_zpow, muInvPt, h.1 i hi, h.2 _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩, one_zpow, one_mul]

theorem RhoUnit.norm_rhoPt' (h : RhoUnit Ch sel mu cst σ chi) {i : ℕ} (hi : i < R.m) {u : Pr.Word} (p : ChPt (R := R) sel mu u (i + 1)) :
    ‖rhoPt' Ch sel mu cst σ chi i p‖ = 1 := by
  rw [rhoPt', norm_mul, norm_inv, norm_zpow, muInvPt, h.1 i hi, h.2 _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩, one_zpow, inv_one, one_mul]

theorem rhoUnit_of {D : D7} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    (ht : Ch.Tied s.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) (hG : G.σ₀ = s.σ₀) (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) :
    RhoUnit Ch sel mu cst s.σ₀ (chiLat s χ) :=
  ⟨fun _ hi _ N fr => hG ▸ norm_muInvDet hX hPr hsel hS (hG ▸ ht) hL hi N fr, fun _ _ hN => norm_chiLat hX hs hχ hN⟩

end Rho

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
  (P : LevFam X.E X.K R.r Pr.vGs) (c : TopDepth R cst.M)

@[reducible] def twFam : ℕ → GFam X.K := levFam W sel mu cst L u m2 b hY (topLevG Ch P) (topLevQ R sel mu c.pos)

def TwEquiv : Prop :=
  MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) ∧ Cp1Equiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY ∧
    TopEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY P c

variable {W Ch sel mu cst L A u m2 b hY P c}

theorem TwEquiv.kerEquivC (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hX : X.Ok) (hPr : Pr.Ok) (hm : R.m = m2 + 2) (hc : cst.Ok)
    (H : TilOk Pr sel mu u) : KerEquivC W Ch sel mu cst L A u m2 b hY P :=
  ⟨h.1, h.2.1, h.2.2.cp2Equiv hX hPr hm hc H (tameFr_chTh W Ch sel mu cst A u m2)⟩

def twistedKernelPointCoset (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (al : L.β m2) :
    ClsKer ((chF W sel mu L u m2).mem al) (cplMem W sel mu cst L u m2 b hY).gsd :=
  cplKer1 (topCpl h.2.1 h.2.2 al)

def twistedKernelCosetPoint (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) :
    ClsKer (cplMem W sel mu cst L u m2 b hY).gsd (frmMem W sel mu L u (topLevG Ch P) (topLevQ R sel mu c.pos)).gsd where
  k d p' := topDegreeKTwo W Ch sel mu cst (chTh W Ch sel mu cst A u m2) d.1.1 d.1.2 p'
  equiv g g₁ d p' := h.2.2 g g₁ d.1.1 d.1.2 p'

def twKer (h : TwEquiv W Ch sel mu cst L A u m2 b hY P c) : KerFam (twFam W Ch sel mu cst L u m2 b hY P c) :=
  spKer (matFam h.1) (twistedKernelPointCoset h) (twistedKernelCosetPoint h)

def twXi (i j : ℕ) (e : j = i + 1) : ∀ (β : (twFam W Ch sel mu cst L u m2 b hY P c i).β) (β' : (twFam W Ch sel mu cst L u m2 b hY P c j).β),
    (twFam W Ch sel mu cst L u m2 b hY P c i).D β → (twFam W Ch sel mu cst L u m2 b hY P c j).D β' → HomE X.E (R.N i) (R.N j) → X.K
  | .mat al _, .mat be _ =>
    (match j, e, be with | _, rfl, be => XiEntry Ch sel mu cst L i al be :
      ChPt (R := R) sel mu u i → ChPt (R := R) sel mu u j → HomE X.E (R.N i) (R.N j) → X.K)
  | .mat al _, .cpl h' =>
    (match i, j, (Nat.succ.inj (h'.symm.trans e) : m2 = i), h', al with
      | _, _, rfl, rfl, al => fun p₀ d => XiCpl1 Ch sel mu cst L m2 al p₀ d.1.1 d.1.2 :
      ChPt (R := R) sel mu u i → (twFam W Ch sel mu cst L u m2 b hY P c j).D (.cpl h') → HomE X.E (R.N i) (R.N j) → X.K)
  | .cpl h, .top h' =>
    (match i, j, h, h' with | _, _, rfl, rfl => fun d p' => XiTop Ch sel mu cst m2 d.1.1 d.1.2 p' :
      (twFam W Ch sel mu cst L u m2 b hY P c i).D (.cpl h) → (twFam W Ch sel mu cst L u m2 b hY P c j).D (.top h') →
        HomE X.E (R.N i) (R.N j) → X.K)
  | .mat _ _, .top _ => fun _ _ _ => 0
  | .cpl _, .mat _ _ => fun _ _ _ => 0
  | .cpl _, .cpl _ => fun _ _ _ => 0
  | .top _, _ => fun _ _ _ => 0

def twRep (i : ℕ) (x : (twFam W Ch sel mu cst L u m2 b hY P c i).Cl) : ChPt (R := R) sel mu u i :=
  levPt i x.1 (((twFam W Ch sel mu cst L u m2 b hY P c i).mem x.1).outSec.rep x.2)

def twSrc (chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ) (hX : X.Ok) (hm : R.m = m2 + 2) (hF : ∀ j, (chF W sel mu L u j).Ok)
    (hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c) (hρ : RhoUnit Ch sel mu cst A.σ₀ chi) : ChSrc X R where
  F := twFam W Ch sel mu cst L u m2 b hY P c
  ok := levFam_ok hF (topGSD_ok W Ch sel mu hX P u c)
  lam := W.lamTrue u
  eV _ := LinearEquiv.refl _ _
  kk := twKer hK
  rho i x := rhoPt Ch sel mu cst A.σ₀ chi i (twRep i x)
  rho' i x := rhoPt' Ch sel mu cst A.σ₀ chi i (twRep (i + 1) x)
  rho_norm _ hi _ := hρ.norm_rhoPt hi _
  rho'_norm _ hi _ := hρ.norm_rhoPt' hi _
  DG := Mem.Col2.DGam X.E R
  DG_pos := Mem.Col2.DGam_pos (posStar_of_ok hX) R
  dvd i hi x := (card_stab_dvd_autU i x.1 _).trans
    (card_autU_dvd_DGam (posStar_of_ok hX) R (by omega) hi ⟨(twRep i x).deco.2.lat, (twRep i x).deco.2.uni⟩)

def twSrcOf {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {G : ChGlob X R.m} {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : ∀ i, Pr.g i ∈ S) (ht : Ch.Tied s.σ₀ e G.mu0 eta) (hL : L.Ok Ch sel mu cst G m2) (hG : G.σ₀ = s.σ₀) (hs : s.Ok)
    (hχ : TaylorLogMetric.IsChi D χ) (hF : ∀ j, (chF W sel mu L u j).Ok) (hK : TwEquiv W Ch sel mu cst L (ambOf s B χ cD) u m2 b hY P c) : ChSrc X R :=
  twSrc (chiLat s χ) hX hL.hm hF hK (rhoUnit_of hX hPr hsel hS ht hL hG hs hχ)

section Laws

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi}

end Laws

variable (b hY P c) in

def twStart {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) :
    MfV W Ch u →ₗ[X.K] (twFam W Ch sel mu cst L u m2 b hY P c 0).Forms :=
  spIn m2 R.m _ _ 0 ∘ₗ startC hL u

section Col

variable {chi : ∀ n : ℕ, Submodule (𝓞 X.E) (Sp X.E n) → ℂ} {hX : X.Ok} {hm : R.m = m2 + 2} {hF : ∀ j, (chF W sel mu L u j).Ok}
  {hK : TwEquiv W Ch sel mu cst L A u m2 b hY P c} {hρ : RhoUnit Ch sel mu cst A.σ₀ chi} {G : ChGlob X R.m}

end Col

example : Nonempty (twFam W Ch sel mu cst L u m2 b hY P c R.m).Cl :=
  (inferInstance : Nonempty (TopPt R sel mu u)).elim fun p => ⟨⟨.top rfl, Quotient.mk _ p⟩⟩

example : Nonempty (twFam W Ch sel mu cst L u m2 b hY P c (m2 + 1)).Cl :=
  haveI : NeZero (R.N (m2 + 1)) := ⟨(R.N_pos _).ne'⟩
  open Classical in ⟨⟨.cpl rfl, Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG Pr sel mu) (stdLat X.E (R.N (m2 + 1)))
    fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)}), 0, zero_mem _, rfl⟩⟩⟩

example (hm : R.m = m2 + 2) (i : ℕ) (hi : R.m < i) : IsEmpty (twFam W Ch sel mu cst L u m2 b hY P c i).Cl :=
  ⟨fun x => (SpIdx.isEmpty_of_lt (by omega) hi).false x.1⟩

example (σ : X.K →+* ℂ) (z : ℂ) (i : ℕ) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (h : muInvPt Ch sel mu cst i p = 1) (h' : muInvPt Ch sel mu cst i p' = 1) :
    rhoPt Ch sel mu cst σ (fun _ _ => z) i p = (z ^ (R.N (i + 1) / 2))⁻¹ ∧ rhoPt' Ch sel mu cst σ (fun _ _ => z) i p' = z ^ (R.N i / 2) := by
  simp only [rhoPt, rhoPt', h, h', map_one, one_mul, inv_one, zpow_neg, zpow_natCast, and_self]

end Chain

end GlobalTheory.GO
end
end

