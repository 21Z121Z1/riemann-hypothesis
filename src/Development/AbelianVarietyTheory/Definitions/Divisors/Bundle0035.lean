import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import ReciprocityTheory.Automorphisms.Unitary
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.LocusEqTopOfDualPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.principalLevelFrame
open scoped TensorProduct

namespace GlobalTheory.StdFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostS (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

def tensCastR {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := by
  subst h
  exact (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).toRingEquiv

variable {D : D7}

def StdPsi {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  (∃ (β : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
      (β' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
      β * β' = 1 ∧ β' * β = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V.gram (P.ψ κ) =
        β * ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (tensCastR hF).symm) * β') ∧
  ∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ P.ψ κ ∈ KsphC V ∅

end GlobalTheory.StdFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

section Translates

variable {S : Scheme.{0}} (P : PolAV S)

def IsPolAVSectionInverseImage (T : Over S) (s : P.L.Sec) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) : Prop :=
  ∀ (i : P.L.ι) (h : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => i) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U i),
    t.f (fun _ => i) = ((snd T P.A).left.appLE _ _ h).hom (s.f i)

def OnT (T : Over S) (n : ℕ) (s : (lbPow P.L n).Sec) (t : LB.Sec (LPow P.A P.L (n : ℤ) T)) : Prop :=
  ∀ (i : P.L.ι) (h : (LPow P.A P.L (n : ℤ) T).U (fun _ => i) ≤ (snd T P.A).left ⁻¹ᵁ (lbPow P.L n).U (fun _ => i)),
    t.f (fun _ => i) = ((snd T P.A).left.appLE _ _ h).hom (s.f (fun _ => i))

def Tr (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {T : Over S} (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T))
    (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T) (t : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)),
    α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s₁ t

def FinOrdT {k : ℤ} {T : Over S} (U : ThetaGrp P.A P.L k T) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ U.pt ^ n = 1 ∧ LB.Gen.Corr P.L _ _ _ _ (powGen P.A P.L k U n) (LB.oneGen P.L)

def ThJetT (ρ : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {B : Type} [CommRing B] (s : Sp B ⟶ S)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (Over.mk s))) {I : Type} (pt : I → (Over.mk s ⟶ P.A)) {g : ℕ}
    (y : Fin g → (Sp (DualNumber B) ⟶ (Over.mk s ⊗ P.A).left)) (ϑ : I → B) (J : I → Fin g → B) : Prop :=
  ∃ (U : I → ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)) (t : I → LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)))
    (i₀ : P.L.ι) (c : Fin g → B),
    (∀ i, SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr P ρ m th (U i) (t i)) ∧
    ⊤ ≤ (s ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ ∧
    ∀ i j, valR (y j) ((LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk s)).U fun _ => i₀) ((t i).f fun _ => i₀) =
      TrivSqZeroExt.inl (valR s ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ (m ^ 2)) *
        (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i j + c j * ϑ i))

end Translates

def epsLift {R : Type} [CommRing R] {A : Over (Sp R)} (v : epsR R ⟶ A) :
    Sp (DualNumber R) ⟶ (baseOver (Sp R) ⊗ A).left :=
  (lift (Over.homMk (epsR R).hom (by simp) : epsR R ⟶ baseOver (Sp R)) v).left

def ThJet {R : Type} [CommRing R] (x : KeyIn R) {g : ℕ} (hg : x.P.g = g) (m : ℕ) {I : Type}
    (pt : I → (baseOver (Sp R) ⟶ x.P.A)) (ϑ : I → R) (J : I → Fin g → R) : Prop :=
  ∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp R)) x.th th ∧
    ThJetT x.P x.rig m (𝟙 (Sp R)) th pt (fun j => epsLift (x.v (j.cast hg.symm))) ϑ J

def IsTr {R : Type} [CommRing R] (x : KeyIn R) (m : ℕ) (s : (lbPow x.P.L (m ^ 2)).Sec) : Prop :=
  ∃ th U t, IsPolAVSectionInverseImage x.P (baseOver (Sp R)) x.th th ∧ FinOrdT x.P U ∧ Tr x.P x.rig m th U t ∧
    OnT x.P (baseOver (Sp R)) (m ^ 2) s t

def RigPow {R K : Type} [CommRing R] [Field K] (f : R →+* K) {P : PolAV (Sp K)} {G : Over (Sp R)} [GrpObj G]
    {φ : P.A.left ⟶ G.left} {M : RigLB G} {n : ℕ} (w : LB.Iso (M.L.pull φ) (lbPow P.L n))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) : Prop :=
  ∀ (i : P.L.ι) (p : PUnit → M.L.ι), ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i →
    ⊤ ≤ (spMap f) ⁻¹ᵁ (show (Sp R).Opens from (M.L.pull (eSec G)).U p) →
    valR (X := P.A.left) (eSec P.A) _ (w.s (fun _ => i, p)).val * valR (X := Sp R) (spMap f) _ (M.rig.s p).val =
      valR (X := Sp K) (𝟙 _) _ (ρ.s fun _ => i).val ^ n

def Rule4 (κ : Rule) : Prop := Homog (fun _ => 1) κ ∧ Funct κ ∧ ThetaOne κ ∧ FamUnit κ

def LocInt (κ : Rule) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K], Finite (IsLocalRing.ResidueField R) → ∀ (x : KeyIn K),
    (letI := x.P.isAb.comm; GlobalTheory.ZH.HypS x.P.A x.P.L) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left) (M : RigLB G) (m : ℕ)
      (w : LB.Iso (M.L.pull φ) (lbPow x.P.L (m ^ 2))) (y : Fin x.P.g → (epsR R ⟶ G)),
      1 ≤ m → IsSemiAbelian G → IsGrpPullback x.P.A G (spMap (algebraMap R K)) φ → Nonempty (CubicalStr G M) → w.IsGen →
      RigPow (algebraMap R K) w x.rig → IsLieBasis y → (∀ i, IsVecOver (algebraMap R K) φ (y i) (x.v i)) →
      (∃ r : R, algebraMap R K r * (κ K x : K) = 1) →
      ∀ s, IsTr x m s → ∃ t : M.L.Sec, SecMaps w (secPull t φ) s

def KapF (κ : Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → Nonempty (C ≃+* ℂ) →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) →
      ‖c‖ ^ 8 * ‖algebraMap (FractionRing V) C (κ (FractionRing V) x : FractionRing V)‖ = 1

def Deform (κ : Rule) {C : Type} [NormedField C] [CharZero C] (e : C →+* ℂ) (x : KeyIn C) {g : ℕ} (hg : x.P.g = g) (m : ℕ)
    (ζ : Cˣ) (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) : Prop :=
  ∃ (Θ : (Fin (2 * g) → ZMod (m ^ 2)) → PowerSeries C) (Γ : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → PowerSeries C) (π : C) (b : ℝ),
    ‖π‖ < 1 ∧ (∀ a n, ‖PowerSeries.coeff n (Θ a)‖ ≤ b ∧ ∀ j, ‖PowerSeries.coeff n (Γ a j)‖ ≤ b) ∧
    ThJet x hg m (levelPoint lev hg) (fun a => ∑' n, PowerSeries.coeff n (Θ a) * π ^ n)
      (fun a j => ∑' n, PowerSeries.coeff n (Γ a j) * π ^ n) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a, (Summable fun n => ‖e (PowerSeries.coeff n (Θ a)) * u ^ n‖) ∧
        ∀ j, Summable fun n => ‖e (PowerSeries.coeff n (Γ a j)) * u ^ n‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun a => ∑' n, e (PowerSeries.coeff n (Θ a)) * u ^ n)
          (fun a j => ∑' n, e (PowerSeries.coeff n (Γ a j)) * u ^ n) ∧ (κ ℂ x₀ : ℂ) = e k

def Transfer (κ : Rule) : Prop :=
  ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀,
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      (e : C →+* ℂ) (x : KeyIn C) (hg : x.P.g = g) (ζ : Cˣ) (lev : Out.Level x.P ((n ^ j) ^ 2) (unitOn ζ)) (k : C),
      Deform κ e x hg (n ^ j) ζ lev k → (κ C x : C) = k

section Jets

abbrev redE (F : Type) [CommRing F] : Sp F ⟶ Sp (DualNumber F) := spMap (TrivSqZeroExt.fstHom F F F).toRingHom

variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

def vE (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : DualNumber F :=
  valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) (t.s fun k => J (redE F ≫ r ≫ φ k)).val

def sE (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (J : (Sp F ⟶ X) → L.ι) : DualNumber F :=
  valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) (s.f fun k => J (redE F ≫ r ≫ φ k))

end Jets

section GtJets

variable {R : Type} [CommRing R] [IsDomain R]

abbrev TE (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] : Over (Sp R) :=
  Over.mk (spMap (algebraMap F (DualNumber F)) ≫ (TF (R := R) F).hom)

def dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : DualNumber A →+* DualNumber B where
  toFun z := TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm, add_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

variable {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {N : NumD F}

def jc (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (gm : GtPt D (TE R F)) (α : N.X) : DualNumber F :=
  sE (s.s (ν.eX α)) (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) gm.b).left ν.J *
    vE (gm.s (ν.eX α)) (𝟙 _) ν.J

def Adapted (ν : NumOf D F N) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) {r g : ℕ} (bX : Module.Basis (Fin r) ℤ N.X)
    (σ : Fin g ≃ Fin D.P.g ⊕ Fin r) (gm : Fin g → GtPt D (TE R F)) : Prop :=
  IsLieBasis vB ∧ (∀ j, ∃ o : GtPtF D F, o.IsZero ∧ GtPt.IsPullF F (redE F) (gm j) o) ∧
  (∀ i, (gm (σ.symm (Sum.inl i))).b.left =
    spMap (dualMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left) ∧
  ∀ l, (gm (σ.symm (Sum.inr l))).b = DegPre.zeroT D (TE R F) ∧
    ∀ χ, vE ((gm (σ.symm (Sum.inr l))).s (ν.eX χ)) (𝟙 _) ν.J = 1 + TrivSqZeroExt.inr ((bX.repr χ l : ℤ) : F)

def BKey (κ : Rule) [CharZero F] (ν : NumOf D F N) (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (k : F) : Prop :=
  (D.P.g = 0 → N.th 1 ^ 8 * k = 1) ∧
  ∀ (hg : 1 ≤ D.P.g) (hr : D.rig.IsGen) (th : D.P.L.Sec) (hth) (hv : IsLieBasis vB) (x : KeyIn F),
    (∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i,
      ν.th.f (fun _ => i) = resG _ h (th.f i)) →
    KeyPB x ⟨D.P, hg, D.rig, hr, th, hth, vB, hv⟩ ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) →
    (κ F x : F) = k

end GtJets

def QLevel {O : Type} [CommRing O] (N : NumD O) (g k : ℕ) (ζ : Oˣ) (q : (Fin (2 * g) → ZMod k) → N.QT k) : Prop :=
  IsPrimitiveRoot ζ k ∧ (∀ a b, N.QEq (q a * q b) (q (a + b))) ∧ (∀ a b, N.QEq (q a) (q b) → a = b) ∧
  (∀ p, ∃ a, N.QEq (q a) p) ∧ ∀ i j, N.wp (q (Pi.single i 1)) (q (Pi.single j 1)) = ζ ^ stdSymp g i j

def IsEvFam {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (f : N.X → N.A → O) : Prop :=
  (∀ (h : N.Gt) (χ : N.X), f (p.1.1.toAdd + m • χ) h.b * h.s (p.1.1.toAdd + m • χ) = N.evT m p h χ) ∧
  ∀ α, (∀ χ, α ≠ p.1.1.toAdd + m • χ) → ∀ x, f α x = 0

def Arch (κ : Rule) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R), D.PsiEven → D.TauBimult →
    ∀ [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g r m k : ℕ), 1 ≤ g → Odd m → m ^ 2 ∣ k →
    ∀ (β : N.Form k) (ζ : ℂˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q →
    ∀ (s : (Fin (2 * g) → ZMod (m ^ 2)) → Fam D ℂ (m ^ 2)), (∀ a, ∃ f, ν.FamV (s a) f ∧ IsEvFam N m (q a) f) →
    ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin D.P.g ⊕ Fin r)
      (gm : Fin g → GtPt D (TE R ℂ)), Adapted ν vB bX σ gm → ∀ k₀ : ℂ, BKey κ ν vB k₀ →
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      (∀ a j, (Summable fun α => ‖(jc ν (s a) (gm j) α).fst * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
        Summable fun α => ‖(jc ν (s a) (gm j) α).snd * u ^ (β.be α α / (2 * m ^ 2)).toNat‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn ζ)) (ϑ : _ → ℂ),
        (∀ a j, ϑ a = ∑' α, (jc ν (s a) (gm j) α).fst / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) ϑ
          (fun a j => ∑' α, (jc ν (s a) (gm j) α).snd / ν.rg ^ (m ^ 2) * u ^ (β.be α α / (2 * m ^ 2)).toNat) ∧
        (κ ℂ x₀ : ℂ) = k₀

def HypF {K : Type} [Field K] [NumberField K] (F : SemiFib K) : Prop :=
  letI := F.P₀.isAb.comm; GlobalTheory.ZH.HypS F.P₀.A F.P₀.L

def SectionsLowS : Prop := ∀ g : ℕ, 0 < g → ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = g →
  HypF F → ∀ h : HermFam K (Fin F.P₀.g → K), F.IsHerm h → ∀ m : ℕ, 1 ≤ m →
  ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'],
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left) (AA : Over (Sp (𝓞 K''))) (_ : GrpObj AA) (_ : IsCommMonObj AA)
      (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (w : LB.Iso (MM.L.pull φ) (lbPow P.L (4 * m ^ 2))) (r : ℕ)
      (b : Fin r → (lbPow P.L (4 * m ^ 2)).Sec) (E : Submodule (𝓞 K'') (Fin r → K'')) (hE : HermFam K'' (Fin r → K'')),
      IsOver F ψ φ ∧ IsWeak w ∧ Function.Bijective (fun c : Fin r → K'' => secComb P.A.hom c b) ∧
      (∀ c ∈ E, ∃ t : MM.L.Sec, SecMaps w (secPull t φ) (secComb P.A.hom c b)) ∧
      IsThetaMeanSquareNorm w b hE F.P₀.g ∧ Full E ∧ MuGe hE E (-F.falt h / 2 - C)

def SecJetsLowS : Prop := ∀ g : ℕ, 0 < g → ∃ C : ℝ, ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = g →
  HypF F → ∀ (h : HermFam K (Fin F.P₀.g → K)) (ρ : (K →+* ℂ) → ℝ), F.IsHerm h → F.IsRho ρ →
  ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (x : Fin F.P₀.g → K'), x ≠ 0 → ∀ n : ℕ, 2 ≤ n →
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra K' K'') (_ : Algebra K K'') (_ : IsScalarTower K K' K'')
      (h'' : HermFam K'' (Fin F.P₀.g → K'')), IsBC h h'' ∧
      JetSysLow h'' (latBC K'' F.lieLat) (fun i => algebraMap K' K'' (x i)) n (-F.falt h / 2 - C)
        fun i σ => jetBd F.P₀.g (4 * n ^ 2) i (ρ (σ.comp (algebraMap K K'')))

def WeakMat : Prop := ∀ g : ℕ, ∃ c : ℝ, ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K)
  (h : HermFam K (Fin F.P₀.g → K)) (ρ : (K →+* ℂ) → ℝ), F.P₀.g = g → F.IsHerm h → F.IsRho ρ →
  (∑ σ, (ρ σ ^ 2)⁻¹) / (Module.finrank ℚ K : ℝ) ≤ c * (1 + max (F.falt h) 0)

def WeakMatS : Prop := ∀ g : ℕ, ∃ c : ℝ, ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K)
  (h : HermFam K (Fin F.P₀.g → K)) (ρ : (K →+* ℂ) → ℝ), F.P₀.g = g → HypF F → F.IsHerm h → F.IsRho ρ →
  (∑ σ, (ρ σ ^ 2)⁻¹) / (Module.finrank ℚ K : ℝ) ≤ c * (1 + max (F.falt h) 0)

def LineLow (p : ∀ (K : Type) [Field K] [NumberField K], SemiFib K → Prop) : Prop := ∀ g : ℕ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), F.P₀.g = g → 0 < g → p K F → ∀ h, F.IsHerm h →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (h' : HermFam K' (Fin F.P₀.g → K'))
      (x : Fin F.P₀.g → K'), IsBC h h' → x ≠ 0 →
      deg h' (lineLat (latBC K' F.lieLat) x) ≤ C * Real.log (2 + max (F.falt h) 0)

end GlobalTheory.MBLow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Points GlobalTheory.Twist GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isStandardSmooth_mvPolynomial (R σ : Type) [CommRing R] [Finite σ] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card σ) R (MvPolynomial σ R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial σ R) σ Empty :=
    { __ := Algebra.Generators.mvPolynomial R σ
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial σ R) σ Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem smoothOfRelativeDimension_pspace (R : Type) [CommRing R] (M : ℕ) :
    SmoothOfRelativeDimension M (PSpace.str R M) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} M)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension M))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} M) (chartCover R M)
    fun (i : Fin (M + 1)) => ?_
  change SmoothOfRelativeDimension M (chartι R M i ≫ _)
  rw [chartι_str]
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension M)).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have h := isStandardSmooth_mvPolynomial R {j : Fin (M + 1) // j ≠ i}
  rw [show Nat.card {j : Fin (M + 1) // j ≠ i} = M by simp] at h
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap M).2 h

variable (k : Type) [Field k] (M : ℕ)

theorem geometricallyConnected_pspace : GeometricallyConnected (PSpace.str k M) :=
  ⟨geometrically_iff_of_commRing.2 fun K _ _ _ _ _ h =>
    have e := (isPullback_baseChange M (algebraMap k K)).isoIsPullback _ _ h
    e.hom.homeomorph.surjective.connectedSpace e.hom.continuous⟩

abbrev projSys : LinSys k where
  Y := PSpace k M
  str := PSpace.str k M
  D := M
  L := O1 k M
  isLB := O1_isLB k M
  N := M + 1
  b := coord k M

namespace projSys

theorem algebraΓ_eq : (projSys k M).algebraΓ = algebraSections k M ⊤ :=
  Algebra.algebra_ext _ _ fun r => (LB.resG_self (X := PSpace k M) le_top _).symm

theorem isVariety (hM : 1 ≤ M) : (projSys k M).IsVariety :=
  ⟨smoothOfRelativeDimension_pspace k M, ⟨M, 𝟙 _, inferInstance, Category.id_comp _⟩,
    geometricallyConnected_pspace k M, hM⟩

theorem basePointFree : (projSys k M).BasePointFree := iSup_nonzeroLocus_coord k M

theorem form_eq {d : ℕ} {g : MvPolynomial (Fin (M + 1)) k} (hg : g.IsHomogeneous d) :
    (projSys k M).form hg = ProjSpace.formSec d g hg := by
  rw [ProjCoh.formSec_eq]
  exact congrArg (fun a : Algebra k Γ(PSpace k M, ⊤) =>
    letI := a; Twist.formSec (coord k M) (mem_polyGrading_natCast.2 hg)) (algebraΓ_eq k M)

theorem imageIdeal_eq_bot : (projSys k M).imageIdeal = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro g ⟨d, hg, h⟩
  refine (formSec_inj hg (isHomogeneous_zero _ k d)).1 ((form_eq k M hg).symm.trans (h.trans ?_))
  exact LB.f_injective (funext fun j => (formOn_zero (hi := (On_U k M d j).le)).symm)

theorem del_eq_one : (projSys k M).del = 1 := by
  have h := interNum_const_of_polynomial k (structureModule (PSpace k M)) (O1_isLB k M) (d := M)
    (Polynomial.preHilbertPoly ℚ M 0) (Polynomial.natDegree_preHilbertPoly ℚ M 0).le
    (ProjCoh.chi_sheafO_eq_eval k M)
  rw [Polynomial.coeff_preHilbertPoly_self, mul_inv_cancel₀ (Nat.cast_ne_zero.2 M.factorial_ne_zero)] at h
  rw [LinSys.del, algebraΓ_eq]
  exact_mod_cast h

theorem eq_of_sameImage {y y' : PSpace k M} (h : (projSys k M).SameImage y y') : y = y' := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun d g hg => ?_)
  replace hg : g.IsHomogeneous d := hg
  have := h d g hg
  rw [form_eq, nonzeroLocus_formSec] at this
  exact not_iff_not.1 this

theorem noContract (bd : Set (PSpace k M)) : (projSys k M).NoContract bd := fun C _ _ hC _ h => by
  have : Subsingleton C := ⟨fun a b => Subtype.ext (eq_of_sameImage k M (h _ a.2 _ b.2))⟩
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at this
  exact absurd this (by decide)

abbrev gen : PSpace k M := AmpleModel.genericPt k M

theorem gen_mem (i : Fin (M + 1)) : gen k M ∈ chart k M i := fun h => X_ne_zero (R := k) i h

theorem indep : (projSys k M).Indep := fun u hu => by
  have hg : (∑ j, C (u j) * X j : MvPolynomial (Fin (M + 1)) k).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k j).C_mul _
  have h0 : (∑ j, C (u j) * X j : MvPolynomial (Fin (M + 1)) k) = 0 := by
    by_contra hne
    have h1 : ptOf (resPt (gen k M)) ∈ nonzeroLocus ((projSys k M).form hg) := by
      rw [ptOf_resPt, form_eq, nonzeroLocus_formSec]
      exact hne
    refine ((projSys k M).powVal_ne_zero_iff _ _).2 h1 ?_
    have h2 := (projSys k M).val_comb (resPt (gen k M)) u
    rw [hu, LinSys.val_zero] at h2
    rw [LinSys.powVal_form, h2, eval₂_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [eval₂_mul, eval₂_C, eval₂_X]
  funext j
  have := congrArg (eval (Pi.single j 1 : Fin (M + 1) → k)) h0
  simpa [Pi.single_apply] using this

theorem valR_resPt {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (hy : y ∈ U) (f : Γ(Y, U)) :
    valR (resPt y) U f = Y.evaluation U y hy f := by
  have ht : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ U := (le_preimage_iff (C := Y.presheaf.stalk y) _ U).2 (by
    rw [show Y.fromSpecStalk y (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y from
      Scheme.fromSpecStalk_closedPoint]; exact hy)
  have e : valMap (C := Y.presheaf.stalk y) (Y.fromSpecStalk y) U ht = Y.presheaf.germ U y hy := by
    change (Y.fromSpecStalk y).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
    simp only [Category.assoc]
    have e : (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE (le_top : Y.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  exact (valR_spMap_comp (Y.residue y).hom (Y.fromSpecStalk y) U ht f).trans (congrArg (Y.residue y).hom
    ((valR_eq (C := Y.presheaf.stalk y) _ _ ht f).trans (congrArg (fun q => q.hom f) e)))

theorem birational : (projSys k M).Birational := by
  refine ⟨gen k M, ?_, eq_top_iff.2 fun r _ => ?_⟩
  · exact Set.eq_univ_of_forall fun x => (ProjectiveSpectrum.le_iff_mem_closure _ _ x).1
      (show ⊥ ≤ x.asHomogeneousIdeal from bot_le)
  have hx : ptOf (resPt (gen k M)) ∈ chart k M 0 := by rw [ptOf_resPt]; exact gen_mem k M 0
  have hx' := (le_iff_ptOf_mem _ _).2 hx
  obtain ⟨c, hc, h, -⟩ := (projSys k M).exists_frame_change (resPt (gen k M)) (0 : Fin (M + 1)) hx
  have key : ∀ f : Γ(PSpace k M, chart k M 0),
      valR (resPt (gen k M)) _ f ∈ (projSys k M).ratioField (resPt (gen k M)) := fun f => by
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective k M 0 f
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine Subfield.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [algHom_C, ← resG_algebraMap le_top, ← algebraΓ_eq]
      exact ((valR_res _ le_top hx' _).trans ((projSys k M).valR_algebraMap _ a)).symm
    | add p q hp hq => rw [map_add, valR_add _ _ hx']; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, valR_mul _ _ hx', aeval_X]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ⟨j, (0 : Fin (M + 1)), ?_⟩))
      have h0 : 1 = c * (projSys k M).coords (resPt (gen k M)) (0 : Fin (M + 1)) :=
        (valR_one _ _ hx').symm.trans ((congrArg _ (ratioOn_self (hi := le_rfl)).symm).trans (h (coord k M 0)))
      rw [← mul_div_mul_left _ _ hc, ← h0, div_one]
      exact h (coord k M j)
  obtain ⟨t, rfl⟩ := (PSpace k M).residue_surjective _ r
  let := (PSpace k M).presheaf.algebra_section_stalk (U := chart k M 0) ⟨gen k M, gen_mem k M 0⟩
  have := (isAffineOpen_chart k M 0).isLocalization_stalk ⟨gen k M, gen_mem k M 0⟩
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj
    ((isAffineOpen_chart k M 0).primeIdealOf ⟨gen k M, gen_mem k M 0⟩).asIdeal.primeCompl t
  have hs := (IsLocalization.map_units ((PSpace k M).presheaf.stalk (gen k M)) s).map
    ((PSpace k M).residue (gen k M)).hom
  have e' := congrArg ((PSpace k M).residue (gen k M)).hom e
  rw [map_mul, ← eq_div_iff hs.ne_zero] at e'
  have ha := key a
  have hb := key s
  rw [valR_resPt _ _ (gen_mem k M 0)] at ha hb
  exact e' ▸ div_mem ha hb

end projSys
end GlobalTheory.Adelic
end
end

