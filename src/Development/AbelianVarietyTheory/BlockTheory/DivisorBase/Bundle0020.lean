import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateFieldBounds
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldBounds

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist HostTie CharTie FieldTie)

section Chain

variable {K : Type} [Field K] [NumberField K] [StarRing K] (Q : KerChain K)

def clsNum (i : ℕ) : ℕ :=
  if i ≤ Q.n then ⨆ b : (Q.F i).β, Nat.card ((Q.F i).mem b).Cl
  else if i = Q.n + 1 then Nat.card Q.S.Cl else Nat.card Q.S₁.Cl

def idxNum (i : ℕ) : ℕ :=
  if i ≤ Q.n then Fintype.card (Q.F i).β
  else if i = Q.n + 1 then ⨆ c : Q.S.Cl, (Q.Y.ys (Q.S.outSec.rep c)).ncard else 1

def FactorBounds (v : InfinitePlace K) (c : ℕ → ℝ) : Prop :=
  (∀ i < Q.n, ∀ φ : (Q.F i).Forms,
    (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤
      Real.exp (c (i + 1)) * (famIpAt (Q.F i) (Q.hF i) v φ φ).re) ∧
  ∀ φ : (Q.F Q.n).Forms,
    (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤
      Real.exp (c (Q.n + 1) + c (Q.n + 2)) * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re

end Chain

section Numbers

variable {D : D7} (large₂ : SizeData₂ D) (EX : ErrX D)

def nuRows (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.N D.R.m)) : ℝ :=
  if h : i.1 < D.R.N (j - 1) then ((((recWts EX).nuW u j τ).w ⟨i.1, h⟩ : ℤ) : ℝ) else 0

def scalK (D : D7) (CK : ℝ) (u : D.what₂.Word) : ℝ :=
  CK * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 *
    Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * (D.mem u).A.T)

def boundB (C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  Formalism.DimensionVariation.sizeB (nuRows EX u) large₂.logOm D.R.f D.R.m (D.R.N D.R.m) large₂.sc.L large₂.La C j

def boundA (C : ℝ) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (large₂.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    C * ((D.host.TT.card : ℝ) * large₂.sc.b' * D.R.N D.R.m + D.R.f * (D.R.m * large₂.etaSz + large₂.Sc) * D.R.N D.R.m +
      D.R.f * (D.R.N D.R.m : ℝ) ^ 2) * large₂.La

end Numbers

def ConjField (D : D7) (δ : ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (c : D.what₂.Tau → M)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : Prop :=
  (∀ x : D.what₂.LL, D.what₂.embLL x ∈ M) ∧ TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M ∧
    (∀ τ, TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {c τ}) ∧
    ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ)) (t ρ)

section Emb

variable {D : D7} {δ : ℂ} {M : IntermediateField ℚ ℂ} [NumberField M] {c : D.what₂.Tau → M} {t : (M →ₐ[ℚ] ℂ) → ℂ}

def ConjField.under (h : ConjField D δ M c t) (ρ : M →ₐ[ℚ] ℂ) : D.what₂.LL →+* ℂ :=
  (ρ : M →+* ℂ).comp (D.what₂.embLL.codRestrict M h.1)

variable (δ c) in

def logOmAt (τ : D.what₂.Tau) (ρ : M →ₐ[ℚ] ℂ) : ℝ := -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D D.host.ccK δ) ρ (c τ)

variable (D δ t) in

def logTh0At (ρ : M →ₐ[ℚ] ℂ) : ℝ :=
  Real.log (GL3Theta.normSq1 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ))
    (GL3Theta.th0 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ)) (t ρ)))

variable (δ c t) in

def sizeAt (EX : ErrX D) (CK : ℝ) (u : D.what₂.Word) (Q : KerChain D.what₂.LL) (j : ℕ) (ρ : M →ₐ[ℚ] ℂ) : ℝ :=
  Formalism.DimensionVariation.liftedMapLogSize (nuRows EX u) (fun l => (D.R.N (l - 1) : ℝ) * D.R.N l) (fun _ _ => scalK D CK u) (logOmAt δ c) (logTh0At D δ t)
            (fun l => Real.log (clsNum Q (l - 1))) (fun l => Real.log (clsNum Q l)) D.host.v j ρ +
    Real.log ((idxNum Q (j - 1) : ℝ) * idxNum Q j)

end Emb

def ParamHyp {D : D7} (large₂ : SizeData₂ D) (EX : ErrX D) (Cs : ℝ) : Prop :=
  Nonempty (ParameterChoice' D large₂) ∧ placeRankTwoOne.Sizes D large₂ Cs ∧ Formalism.L2.Col.Sizes (recPrimes EX) (recWts EX) large₂.sc.a

section Stmt

variable {D : D7} (large₂ : SizeData₂ D) {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

def KernelNorms (CK C : ℝ) : Prop :=
  ∀ (δ : ℂ) (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ → TaylorLogMetric.IsChi D χ →
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (c : D.what₂.Tau → M) (t : (M →ₐ[ℚ] ℂ) → ℂ) (hM : ConjField D δ M c t)
    (u : D.what₂.Word) (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel (1 : Twist D)))
    (I : ChIdx (recFields D) (recPrimes EX) D.R (QE sel ((1 : Twist D) : Chr (recFields D).F (recFields D).E (recFields D).K)))
    (b : I.β (D.R.m - 2 + 1)) (hY : YbHyp (R := D.R) sel (1 : Twist D) cst I u (D.R.m - 2) b)
    (hK : KerEquivC (recWts EX) Ch sel (1 : Twist D) cst I (ambOf (recSeam D) B χ fun τ => (c τ : ℂ)) u (D.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF (recWts EX) sel (1 : Twist D) I u j).Ok)
    (hE : (evGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) u).Ok),
    I.Ok Ch sel (1 : Twist D) cst (recGlob D mu0) (D.R.m - 2) → cst.sharp = true →
    FieldTie sel (ambOf (recSeam D) B χ fun τ => (c τ : ℂ)) (1 : Twist D) cst u →
    let Q : KerChain D.what₂.LL := KerChain.ofCol (recWts EX) Ch sel (1 : Twist D) cst I
      (chKerC (recWts EX) Ch sel (1 : Twist D) cst I (ambOf (recSeam D) B χ fun τ => (c τ : ℂ)) u (D.R.m - 2) b hY (rPsymF Ch) hK) hF hE
    (∀ ρ : M →ₐ[ℚ] ℂ, FactorBounds Q (InfinitePlace.mk (hM.under ρ)) fun j => sizeAt δ c t EX CK u Q j ρ) ∧
      ∀ j, 1 ≤ j → j ≤ D.R.m →
        (∑ ρ : M →ₐ[ℚ] ℂ, sizeAt δ c t EX CK u Q j ρ) / (Module.finrank ℚ M : ℝ) ≤ boundB large₂ EX C u j

def PeriodNorm (C : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (hP : (mtildeGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch)).Ok)
    (hE : (evGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) u).Ok)
    (Xg : Finset (G0 (recFields D).E (recPrimes EX).vGs D.R.r → (recFields D).K)) (s : D.what₂.LL →+* ℂ)
    (ψ : (evGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) u).EqFun)
    (F : V0X (recWts EX) Ch sel (1 : Twist D) Xg (rPsymF Ch)),
    ‖s (PtilFF (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) hP u ψ.1 F.1.1)‖ ^ 2 ≤
      Real.exp (boundA large₂ C u) *
        ((evGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) u).ipAt hE (InfinitePlace.mk s) ψ.1 ψ.1).re *
        ((mtildeGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch)).ipAt hP (InfinitePlace.mk s) F.1.1 F.1.1).re

end Stmt

def ColumnNormsAt (Cs CK C : ℝ) (D : D7) (large₂ : SizeData₂ D) (EX : ErrX D) : Prop :=
  ∀ (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
    (eta : Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)),
    HostTie EX → CharTie Ch mu0 eta sel → ParamHyp large₂ EX Cs → KernelNorms large₂ Ch mu0 sel CK C ∧ PeriodNorm large₂ Ch sel C

def ColumnNorms : Prop :=
  ∀ Cs : ℝ, ∃ CK C : ℝ, 0 ≤ CK ∧ 0 ≤ C ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (EX : ErrX D), ColumnNormsAt Cs CK C D large₂ EX

example (M : IntermediateField ℚ ℂ) [NumberField M] :
    Fintype.card (M →ₐ[ℚ] ℂ) = Module.finrank ℚ M ∧ 0 < Module.finrank ℚ M :=
  ⟨AlgHom.card ℚ M ℂ, Module.finrank_pos⟩

open Formalism.L2.DIV.Inst Formalism.L2.Indef.Examples₂ in

example (v : InfinitePlace K3) : FactorBounds (ptQ 0 (fun _ => 1) 1 1) v fun _ => 0 := by
  refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun φ => ?_⟩
  rw [ptInF_eta φ, pt_cpl]
  have h1 := pt_ipAt pt_ok v ((1 * 1 : K3) • fun _ : Fin 1 => (φ () : Unit → K3) ())
  have h2 := pt_famIpAt v (fun _ : Fin 1 => (φ () : Unit → K3) ())
  refine le_of_eq ?_
  refine (congrArg Complex.re h1).trans ?_
  refine Eq.trans ?_ (congrArg (fun z : ℂ => Real.exp (0 + 0) * z.re) h2).symm
  simp

open Formalism.L2.DIV.Inst Formalism.L2.Indef.Examples₂ in

example (v : InfinitePlace K3) : ¬ FactorBounds (ptQ 0 (fun _ => 1) 2 1) v fun _ => 0 := by
  intro h
  have h0 := h.2 (ptInF fun _ => 1)
  rw [pt_cpl] at h0
  have h1 := congrArg Complex.re (pt_ipAt pt_ok v ((1 * 2 : K3) • fun _ : Fin 1 => (1 : K3)))
  have h2 := congrArg (fun z : ℂ => Real.exp (0 + 0) * z.re) (pt_famIpAt v (fun _ : Fin 1 => 1))
  have h3 := h1.symm.le.trans (h0.trans h2.le)
  simp only [Complex.ofReal_re, Pi.smul_apply, smul_eq_mul, mul_one, one_mul, map_ofNat, map_one, add_zero, Real.exp_zero] at h3
  norm_num at h3

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldBounds
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Pol

def PosForm (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Type :=
  {β : levelForms H 1 X // ∀ y, 0 ≤ (β : LinearMap.BilinForm ℤ X) y y}

variable {H : Host E}

abbrev PosForm.form {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (β : PosForm H X) : LinearMap.BilinForm ℤ X := β.1.1

def PosForm.ofLevel {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {N : ℕ} (γ : levelForms H N X)
    (h : ∀ y, 0 ≤ (γ : LinearMap.BilinForm ℤ X) y y) : PosForm H X :=
  ⟨⟨γ.1, γ.2.1, γ.2.2.1, fun _ _ => by simp⟩, h⟩

def IsCuspLattice (E : Type) [Field E] [NumberField E] (q : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Prop :=
  Module.Finite (𝓞 E) X ∧ Module.Projective (𝓞 E) X ∧ Module.finrank (𝓞 E) X ≤ q

def IsSemilinearOverK (H : Host E) {X X₁ : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X₁] [Module (𝓞 E) X₁]
    (r : X →+ X₁) : Prop :=
  ∃ σ : 𝓞 E ≃+* 𝓞 E, σ H.rt = H.rt ∧ ∀ (a : 𝓞 E) (x : X), r (a • x) = σ a • r x

abbrev ConeFn (H : Host E) : Type 1 := ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X], PosForm H X → ℕ

def IsPolarisation (q : ℕ) (ψ : ConeFn H) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X], IsCuspLattice E q X → ∀ β : PosForm H X,
    (β.1 ≠ 0 → 0 < ψ X β) ∧
    ∃ ℓ : levelForms H 1 X →ₗ[ℤ] ℤ, ℓ β.1 = ψ X β ∧ ∀ γ : PosForm H X, (ψ X γ : ℤ) ≤ ℓ γ.1) ∧
  ∀ (X X₁ : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X₁] [Module (𝓞 E) X₁],
    IsCuspLattice E q X → IsCuspLattice E q X₁ → ∀ r : X →+ X₁, Function.Surjective r → IsSemilinearOverK H r →
      ∀ (β : PosForm H X) (β₁ : PosForm H X₁), (∀ y z, β.form y z = β₁.form (r y) (r z)) → ψ X β = ψ X₁ β₁

theorem IsPolarisation.zero {q : ℕ} {ψ : ConeFn H} (h : IsPolarisation q ψ) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (hX : IsCuspLattice E q X) {β : PosForm H X} (e : β.1 = 0) : ψ X β = 0 := by
  obtain ⟨-, ℓ, h1, -⟩ := h.1 X hX β
  rw [e, map_zero] at h1
  omega

def IsConeOf (ψ : ConeFn H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {m : ℕ} (γ : Fin m → PosForm H X) : Prop :=
  ∃ (N : ℕ) (ℓ : levelForms H 1 X →ₗ[ℤ] ℤ), 0 < N ∧ ∀ β : PosForm H X,
    (N * ψ X β : ℤ) ≤ ℓ β.1 ∧
      ((N * ψ X β : ℤ) = ℓ β.1 ↔ ∃ (k : ℕ) (n : Fin m → ℕ), 0 < k ∧ k • β.1 = ∑ i, n i • (γ i).1)

def NoEquivalentRays {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {m : ℕ} (γ : Fin m → PosForm H X) : Prop :=
  ∀ (i j : Fin m) (g : X ≃+ X), IsSemilinearOverK H g.toAddMonoidHom →
    (∀ y z, (γ i).form y z = (γ j).form (g y) (g z)) → i = j

end Pol

section Blow

def IsNormalisedBlowup {U Z X : Scheme.{0}} (j : U ⟶ Z) (b : Z ⟶ X) (J : X.IdealSheafData) : Prop :=
  ∃ (B : Scheme.{0}) (π : B ⟶ X) (j' : U ⟶ B) (_ : QuasiCompact j') (_ : QuasiSeparated j')
    (e : Z ≅ j'.normalization),
    FinalTheorems.Blowup π J ∧ j ≫ e.hom = j'.toNormalization ∧ e.hom ≫ j'.fromNormalization ≫ π = b

def IsRelAmpleIdeal {Z X : Scheme.{0}} (ρ : Z ⟶ X) (I : Z.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (x : Z), x ∈ ρ ⁻¹ᵁ U.1 →
    ∃ (n : ℕ) (s : Γ(Z, ρ ⁻¹ᵁ U.1)) (V : Z.affineOpens), 0 < n ∧ x ∈ V.1 ∧ V.1 ≤ ρ ⁻¹ᵁ U.1 ∧
      ∀ (y : Z) (hy : y ∈ ρ ⁻¹ᵁ U.1), Z.presheaf.germ _ y hy s ∈ FinalTheorems.stalkId I y ^ n ∧
        (y ∈ V.1 ↔ FinalTheorems.stalkId I y ^ n = Ideal.span {Z.presheaf.germ _ y hy s})

def idealAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] (χ : Sp R ⟶ X) : Ideal R :=
  ((J.comap χ).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom

example {X : Scheme.{0}} {R : Type} [CommRing R] (χ : Sp R ⟶ X) : idealAlong ⊤ χ = ⊤ := by
  simp [idealAlong, Ideal.map_top]

end Blow

section Main

variable {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
  {β : O →+* c.F}

def arcForm {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) : PosForm H a.D₀.X :=
  ⟨⟨a.be, a.be_symm, a.be_adj, fun _ _ => by simp⟩, fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (a.be_pos y h).le⟩

def chartRays {Z : Model Xo c β} {k : Type} [Field k] {m d : ℕ} {ξ : Sp (ChartRing k m d) ⟶ gen Z}
    {t : SAB H (Sp (ChartRing k m d))} {P : PELUnif (maximalIdeal (ChartRing k m d)) t}
    {γ : Fin m → levelForms H l.M' P.D.toPre.X} (h : IsToricChart Z ξ P γ) (i : Fin m) : PosForm H P.D.toPre.X :=
  PosForm.ofLevel (γ i) (h.forms.1 i)

def IsFanDivisor (Z : Model Xo c β) (ψ : ConeFn H) (I : (gen Z).IdealSheafData) : Prop :=
  FinalTheorems.EffCartier I ∧ (∀ x ∈ I.support, x ∈ genBd Z) ∧
  ∀ x ∈ genBd Z, ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Z)
    (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t)
    (γ : Fin m → levelForms H l.M' P.D.toPre.X) (h : IsToricChart Z ξ P γ),
    ξ (closedPoint _) = x ∧ IsCuspLattice E D.q P.D.toPre.X ∧ IsConeOf ψ (chartRays h) ∧
    NoEquivalentRays (chartRays h) ∧ idealAlong I ξ = Ideal.span {∏ i, bdParam k m d i ^ ψ _ (chartRays h i)}

def AbelianAtVertical [IsLocalRing O] (Z : Model Xo c β) : Prop :=
  ∀ η : Z.X, Z.s η = closedPoint O → (∀ x : Z.X, Z.s x = closedPoint O → x ⤳ η → x = η) → η ∈ abLocus Z.t.G

variable {Y : Model Xo c β}

def idealQ (T : TorModel Y) (I : (gen T.Z).IdealSheafData) : (gen Y).IdealSheafData := I.map T.bQ

def idealInt (T : TorModel Y) (I : (gen T.Z).IdealSheafData) : Y.X.IdealSheafData := (idealQ T I).map (genι Y)

def ToricFacts (T : TorModel Y) (I : (gen T.Z).IdealSheafData) : Prop :=
  (idealQ T I).comap T.bQ = I ∧ IsRelAmpleIdeal T.bQ I ∧ IsNormalisedBlowup T.Z.jQ T.bQ (idealQ T I)

def IntegralBlowup (T : TorModel Y) (I : (gen T.Z).IdealSheafData) : Prop :=
  IsNormalisedBlowup T.Z.j T.b (idealInt T I) ∧ (idealInt T I).comap (genι Y) = idealQ T I ∧
    FinalTheorems.EffCartier ((idealInt T I).comap T.b) ∧ ((idealInt T I).comap T.b).comap (genι T.Z) = I

def ChartsMonomial (T : TorModel Y) (ψ : ConeFn H) (I : (gen T.Z).IdealSheafData) : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b' : O →+* O') (ϖ : O') (a : ArcIn D l β O' b')
    (χ : Sp (PowerSeries O') ⟶ Y.X), IsArcBase O' ϖ → IsArcChart Y a ϖ χ →
      IsCuspLattice E D.q a.D₀.X ∧
      idealAlong (idealInt T I) χ = Ideal.span {PowerSeries.X ^ ψ _ (arcForm a)} ∧
      ∃ χ'' : Sp (PowerSeries O') ⟶ T.Z.X, χ'' ≫ T.b = χ ∧ IsArcChart T.Z a ϖ χ'' ∧
        ∀ χ₁ : Sp (PowerSeries O') ⟶ T.Z.X, χ₁ ≫ T.b = χ → χ₁ = χ''

def HasToroidalBlowup [IsLocalRing O] (Y : Model Xo c β) : Prop :=
  ∃ (ψ : ConeFn H) (T : TorModel Y) (I : (gen T.Z).IdealSheafData),
    IsPolarisation D.q ψ ∧ IsFanDivisor T.Z ψ I ∧ ToricFacts T I ∧ IntegralBlowup T I ∧ ChartsMonomial T ψ I ∧
    T.Z.LevelActs ∧ T.Z.N4 ∧ AbelianAtVertical T.Z

end Main

def ToroidalModelExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
    IsAbelianGalois ℚ E → Odd (D.p + D.q) → D.q < D.p →
    ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), l.GoodAt p →
    ∀ Y : Model Xo c (c.V W).subtype, Y.LevelStructureConditions p → Y.SplitFibres → Y.N3 → Y.N4 → HasToroidalBlowup Y

end GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone
end
end

