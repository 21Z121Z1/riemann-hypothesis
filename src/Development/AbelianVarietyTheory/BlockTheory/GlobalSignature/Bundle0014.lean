import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation
section
open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

def val_vp {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (p : ℕ) (x : K) : ℚ :=
  (ordE w x : ℚ) / (ordE w (p : K) : ℚ)

def UnitAt {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) : Prop := w.valuation K x = 1

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def vpIdeal (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) E :=
  (((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) * ((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
    Submodule (𝓞 E) E)

def vpLat (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E 1) :=
  (vpIdeal P).comap ((LinearMap.proj (0 : Fin 1) : Sp E 1 →ₗ[E] E).restrictScalars (𝓞 E))

def StdOver {n : ℕ} (p : ℕ) (N : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → localization₂ P.asIdeal N = stdAt E n P

def IsFrames {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} (N : Submodule (𝓞 E) (Sp E n)) (fr : Frs E n SB) : Prop :=
  ∀ (P : SB) (x : Sp E n), fr P x ∈ localization₂ P.1.asIdeal N ↔ x ∈ stdAt E n P.1

end Lat

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ)

def idTo (I : Submodule (𝓞 X.E) X.E) : TaylorLogMetric.IdE D :=
  Submodule.span (𝓞 D.host.E) (s.iE '' (I : Set X.E))

def ChiInK : Prop := ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → ∃ k : X.K, s.σ₀ k = χ 𝔞

def chiK (𝔞 : TaylorLogMetric.IdE D) : X.K := desc s.σ₀ (χ 𝔞)

def chiVp (P : HeightOneSpectrum (𝓞 X.E)) : X.K := chiK s χ (idTo s (vpIdeal P))

def chiDet {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : X.K :=
  chiK s χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N))

def chiFK (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  desc s.σ₀ (Base.chiFac χ a b (s.lat N) (s.lat N'))

example {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (cD : D.what₂.Tau → ℂ) (a b : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    chiFK s χ a b N N' = desc (ambOf s B χ cD).σ₀ ((ambOf s B χ cD).chiF a b N N') := rfl

end Chi

section Rho

variable {D : D7} (Z : Dat) (s : Seam D Z.X) (χ : TaylorLogMetric.IdE D → ℂ)
  (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) {S : Set ℕ}
  (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu))

def muInv (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInvDet sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i) (muAtT Z.Ch sel mu cst i) N fr

def scal (i : ℕ) {a b : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (fr : Frs Z.X.E a (rowSG Z.Pr sel mu))
    (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)) (fr' : Frs Z.X.E b (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInv Z sel mu cst i N fr * (muInv Z sel mu cst i N' fr')⁻¹

def rho (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInv Z sel mu cst i N fr * chiDet s χ N ^ (-((Z.R.N (i + 1) / 2 : ℕ) : ℤ))

def rho' (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  (muInv Z sel mu cst i N fr)⁻¹ * chiDet s χ N ^ (((Z.R.N i / 2 : ℕ) : ℤ))

def sPrime (i : Fin Z.R.m) (τ : Z.X.Tau) : ℚ := sExp' Z.R ((Z.W.row τ).e i) (i.1 + 1)

def sPlain (i : Fin Z.R.m) (τ : Z.X.Tau) : ℚ := sExp Z.R ((Z.W.row τ).e i) (i.1 + 1)

theorem muAt_eq_muAtT (h : MuqTie Z.Ch sel mu cst) (i : ℕ) (hi : i < Z.R.m) :
    muAt Z.Ch sel mu cst i = muAtT Z.Ch sel mu cst i := by
  funext P
  unfold muAt muAtT
  by_cases hP : P.1 ∈ Z.Pr.vGs
  · simp only [if_pos hP]
  · simp only [if_neg hP, h i hi P hP]

def PartA (u : Z.Pr.Word) : Prop :=
  ∀ P ∈ Z.Pr.vT u,
    (∀ σ : Z.X.K →+* ℂ, ‖σ (chiVp s χ P)‖ = 1) ∧
    (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∉ w.asIdeal → UnitAt w (chiVp s χ P)) ∧
    ∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal → ∀ τ : Z.X.Tau,
      (SeesP w τ P → val_vp w (Z.Pr.T u) (chiVp s χ P) = -1) ∧
      (SeesPbar w τ P → val_vp w (Z.Pr.T u) (chiVp s χ P) = 1)

def PartBChi (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) : Prop :=
  (∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((Z.Pr.T u : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      localization₂ P.asIdeal 𝔞 = localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) →
    UnitAt w (chiK s χ 𝔞)) ∧
  (∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)), IsSdLat N → StdOver (Z.Pr.T u) N → UnitAt w (chiDet s χ N)) ∧
  ∀ (a b : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)), Even a → Even b →
    IsSdLat N → IsSdLat N' → StdOver (Z.Pr.T u) N → StdOver (Z.Pr.T u) N' → UnitAt w (chiFK s χ a b N N')

def PartBMu (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) (i : ℕ) : Prop :=
  (∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)), IsSdLat N → StdOver (Z.Pr.T u) N →
    UnitAt w (muOff sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i) N) ∧
    ∀ fr : Frs Z.X.E n (rowSG Z.Pr sel mu), IsFrames N fr →
      UnitAt w (muInv Z sel mu cst i N fr) ∧ UnitAt w (rho Z s χ sel mu cst i N fr) ∧ UnitAt w (rho' Z s χ sel mu cst i N fr)) ∧
  ∀ (a b : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (fr : Frs Z.X.E a (rowSG Z.Pr sel mu))
    (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)) (fr' : Frs Z.X.E b (rowSG Z.Pr sel mu)),
    IsSdLat N → IsSdLat N' → StdOver (Z.Pr.T u) N → StdOver (Z.Pr.T u) N' → IsFrames N fr → IsFrames N' fr' →
    UnitAt w (scal Z sel mu cst i N fr N' fr')

def PartC (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) (i : Fin Z.R.m) : Prop :=
  ∀ P ∈ Z.Pr.vT u, ∀ τ : Z.X.Tau, SeesP w τ P ∨ SeesPbar w τ P →
    rho Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1) ≠ 0 ∧ rho' Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1) ≠ 0 ∧
    val_vp w (Z.Pr.T u) (rho Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1)) =
      sPrime Z i τ * val_vp w (Z.Pr.T u) (chiVp s χ P) ∧
    val_vp w (Z.Pr.T u) (rho' Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1)) =
      -sPlain Z i τ * val_vp w (Z.Pr.T u) (chiVp s χ P)

def PartD (i : ℕ) : Prop :=
  ∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)), IsSdLat N → IsFrames N fr →
    chiDet s χ N ≠ 0 ∧
    rho Z s χ sel mu cst i N fr * rho' Z s χ sel mu cst i N fr = chiDet s χ N ^ (-(((Z.R.t + 1) / 2 : ℕ) : ℤ))

def UnramOver {X : Fields} (ξ : Chr X.F X.E X.K) (p : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (p : 𝓞 X.F) ∈ v.asIdeal → v ∉ Qprime ξ

end Rho

def CharValAtT : Prop :=
  ∀ (Z : Dat) (D : D7) (s : Seam D Z.X) (χ : TaylorLogMetric.IdE D → ℂ) (u : Z.Pr.Word),
    Z.Ok → s.Ok → s.σ₀ = Z.sig0 → TaylorLogMetric.IsChi D χ → ChiInK s χ →
    PartA Z s χ u ∧
    (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal → PartBChi Z s χ u w) ∧
    ∀ (m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E) (eta : Formalism.L2.Host.HChar Z.X.E),
      Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta →
      ∀ (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)), IsSel Z.X sel →
      ∀ (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S),
        UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u) → (∀ k, UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.g k)) →
      ∀ cst : LocCst Z.X (rowSG Z.Pr sel mu), MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0 →
      ∀ i : Fin Z.R.m,
        (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal →
          PartBMu Z s χ sel mu cst u w i.1 ∧ PartC Z s χ sel mu cst u w i) ∧
        PartD Z s χ sel mu cst i.1

example {E : Type} [Field E] [NumberField E] [StarRing E] (n p : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) :
    StdOver p (stdLat E n) ∧ IsFrames (SB := SB) (stdLat E n) (fun _ => 1) :=
  ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

theorem UnitAt.ne_zero {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {x : K} (h : UnitAt w x) : x ≠ 0 := by
  rintro rfl
  simp [UnitAt] at h

end GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Lattices

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def idxExp {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : ℤ :=
  ordDet P N₂ - ordDet P N₁

def AgreeOff (T : ℕ) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), ((T : ℕ) : 𝓞 E) ∉ Q.asIdeal → localization₂ Q.asIdeal N₁ = localization₂ Q.asIdeal N₂

def InBox {K : Type} [Field K] {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt Sall N N')) ∧ ∀ x, ∀ y ∈ mulLat cB (homAt Sall N N'), Ξ (x + y) = Ξ x

end Lattices

section Jets

variable {X : Fields} {a b : ℕ}

def degAt (m : DVar X.Tau a b →₀ ℕ) (τ : X.Tau) : ℕ := ∑ β : Fin b, ∑ α : Fin a, m (τ, β, α)

def degNu (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (τ : X.Tau) : ℤ :=
  ∑ s : Fin a, ((lam τ).w s - (lam τ).detShift + (n τ : ℤ))

def JetsIn (A : Amb X) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ x ∈ divLat cA (homAt Sall N N'), ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' cB x) m

end Jets

def locScal {K : Type} [Field K] (a b q : ℕ) (w : Kˣ) (e e' : ℤ) : K :=
  ((w ^ (e' - e) : Kˣ) : K) * (q : K) ^ (((b / 2 : ℕ) : ℤ) * e - ((a / 2 : ℕ) : ℤ) * e')

section Scal

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def moveScal (u : Pr.Word) (i : ℕ) {a b : ℕ} (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  ∏ P ∈ Pr.vT u, locScal a b (Pr.T u) (mUof Ch mu i P) (idxExp P N₁ N₂) (idxExp P N₁' N₂')

end Scal

def MoveLaw : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
    (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    X.Ok → Pr.Ok → Ch.FromHecke W s.σ₀ → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) →
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ →
    (∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal)) →
    ∀ (i : ℕ), i < R.m → ∀ (b : ℕ), b = R.N (i + 1) → ∀ (lam' : X.Tau → DomWeight b)
      (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b))
      (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K),
      IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
      AgreeOff (Pr.T u) N₁ N₂ → AgreeOff (Pr.T u) N₁' N₂' →
      InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
      InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
      JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₁ N₁' →
      JetsIn (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₂ N₂' →
      kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
        moveScal Ch mu u i N₁ N₂ N₁' N₂' •
          kerOf (stepT W Ch sel mu cst (ambOf s B χ cD) u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

theorem locScal_one_one {K : Type} [Field K] (R : Ranks) (i q : ℕ) (w : Kˣ) :
    locScal (R.N i) (R.N (i + 1)) q w 1 1 = (q : K) ^ ((R.t + 1) / 2) := by
  obtain ⟨c, hc⟩ := R.t_odd
  have h1 : R.N (i + 1) = R.N i + 2 * (c + 1) := by
    unfold Ranks.N
    rw [hc]
    ring
  have h2 : (R.t + 1) / 2 = c + 1 := by omega
  have h3 : (((R.N (i + 1) / 2 : ℕ) : ℤ) * 1 - ((R.N i / 2 : ℕ) : ℤ) * 1) = ((c + 1 : ℕ) : ℤ) := by
    rw [h1]
    omega
  unfold locScal
  rw [h3, h2, sub_self, zpow_zero, Units.val_one, one_mul, zpow_natCast]

theorem locScal_zero_zero {K : Type} [Field K] (a b q : ℕ) (w : Kˣ) : locScal a b q w 0 0 = 1 := by
  simp [locScal]

theorem even_N (R : Ranks) (j : ℕ) : Even (R.N j) :=
  R.k_even.add ((R.t_odd.add_one).mul_left j)

end GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Supp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

def adj (x : HomE E a b) : HomE E b a := Matrix.toLin' (LinearMap.toMatrix' x).conjTranspose

omit [NumberField E] in

theorem adj_single (x : HomE E a b) (α : Fin a) (β : Fin b) :
    adj x (Pi.single β 1) α = star (x (Pi.single α 1) β) := by
  rw [adj, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  simp [LinearMap.toMatrix'_apply]

variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

def suppBar (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y}

def suppP (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d'.at P.1, d'.f P y = 0 → adj x y ∈ d.at P.1}

def StdAtT {n : ℕ} (d : Deco E n ST SG) : Prop := ∀ P : ST, d.at P.1 = stdAt E n P.1

end Supp

section Mom

variable {p : ℕ} [Fact p.Prime]

def InIntClosure {H I : Type} (Sup : Set H) (tab : H → I → ℂ_[p]) (M : Set I) (J : I → ℂ_[p]) : Prop :=
  ∀ F : Finset I, (F : Set I) ⊆ M → ∀ ε : ℝ, 0 < ε →
    ∃ c : H →₀ ℂ_[p], (c.support : Set H) ⊆ Sup ∧ (∀ x, ‖c x‖ ≤ 1) ∧
      ∀ m ∈ F, ‖J m - c.sum fun x r => r * tab x m‖ < ε

theorem InIntClosure.single {H I : Type} {Sup : Set H} (tab : H → I → ℂ_[p]) (M : Set I) {x : H} (hx : x ∈ Sup) :
    InIntClosure Sup tab M (tab x) := by
  classical
  intro F _ ε hε
  refine ⟨Finsupp.single x 1, ?_, ?_, ?_⟩
  · intro y hy
    have := Finsupp.support_single_subset (Finset.mem_coe.1 hy)
    rw [Finset.mem_singleton] at this
    exact this ▸ hx
  · intro y
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  · intro m _
    simp [hε]

variable {X : Fields} {a b : ℕ}

def Induces (ι : X.K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ y : 𝓞 X.K, y ∈ w.asIdeal ↔ ‖ι (y : X.K)‖ < 1

def ptTab (ι : X.K →+* ℂ_[p]) (u : X.Tau → ℂ_[p]) (x : HomE X.E a b) (m : DVar X.Tau a b →₀ ℕ) : ℂ_[p] :=
  m.prod fun k n => (u k.1 * ι (X.emb k.1 (adj x (Pi.single k.2.1 1) k.2.2))) ^ n

end Mom

section Tab

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K)

def jetSum (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  latSum (divLat cA (homAt S N N')) (mulLat cB (homAt S N N')) fun x => Ξ x * A.jetK S N N' cB x m

def RatIdx : Set (DVar X.Tau a b →₀ ℕ) :=
  {m | ∀ x ∈ divLat cA (homAt S N N'), Ξ x ≠ 0 →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' cB x) m}

def OffDatum (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (w : HeightOneSpectrum (𝓞 X.K)) (Ξ₀ : HomE X.E a b → X.K) : Prop :=
  ∀ x ∈ divLat cA (homAt SB N N'),
    w.valuation X.K (Ξ₀ x) ≤ 1 ∧ ∀ y ∈ mulLat cB (homAt SB N N'), Ξ₀ (x + y) = Ξ₀ x

end Tab

def AnaOk (D : Dat) {H : D7} (s : Seam H D.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE H → ℂ)
    (cD : H.what₂.Tau → ℂ) : Prop :=
  s.Ok ∧ s.σ₀ = D.sig0 ∧ TaylorLogMetric.IsCurveIdeal H cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice H cc δ ∧ TaylorLogMetric.IsChi H χ ∧ IsDgen H cD

def MomAt (D : Dat) {H : D7} (cc : Ideal (𝓞 H.host.K)) (A : Amb D.X) (u : D.Pr.Word) [Fact (D.Pr.T u).Prime]
    (w : HeightOneSpectrum (𝓞 D.X.K)) (ι : D.X.K →+* ℂ_[D.Pr.T u]) (un : D.X.Tau → ℂ_[D.Pr.T u]) : Prop :=
  ∀ (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)) (S : Set ℕ) (mu : Tup D.X.F D.X.E D.X.K S)
    (cst : LocCst D.X (rowSG D.Pr sel mu)),
    IsSel D.X sel → hostS H.host.q H.host.d (D.Pr.g 0) (D.Pr.g 1) (Set.range D.Pr.T) ⊆ S →
    (∀ P ∈ rowSG D.Pr sel mu, Nat.Coprime (Ideal.absNorm cc) (qOf P)) →
    ∀ (i b : ℕ), i < D.R.m → b = D.R.N (i + 1) →
    ∀ (SG SG' : Finset (HeightOneSpectrum (𝓞 D.X.E)))
      (d : DecoSet D.X.E (D.R.N i) (D.Pr.vT u) SG) (d' : DecoSet D.X.E b (D.Pr.vT u) SG'),
      StdAtT d.1 → StdAtT d'.1 →
      ∀ Ξ₀ : HomE D.X.E (D.R.N i) b → D.X.K,
        OffDatum (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N (rowSG D.Pr sel mu) w Ξ₀ →
        (seenBarC D.Pr u w →
          InIntClosure (suppBar d.1 d'.1) (ptTab ι un)
            (RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x)
            fun m => ι (jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
              (fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x) m)) ∧
        (seenC D.Pr u w →
          InIntClosure (suppP d.1 d'.1)
            (fun x m => ((D.Pr.T u : ℂ_[D.Pr.T u]) ^ (D.X.f * D.R.N i))⁻¹ * ptTab ι un x m)
            (RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x)
            fun m => ι (jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
              (fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x) m))

def JetMoments : Prop :=
  ∀ (D : Dat), D.Ok →
  ∀ (H : D7) (s : Seam H D.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ),
    AnaOk D s cc δ χ cD →
    ∀ (u : D.Pr.Word) [Fact (D.Pr.T u).Prime], Nat.Coprime (Ideal.absNorm cc) (D.Pr.T u) →
    ∀ (w : HeightOneSpectrum (𝓞 D.X.K)) (ι : D.X.K →+* ℂ_[D.Pr.T u]), Induces ι w →
      ∃ un : D.X.Tau → ℂ_[D.Pr.T u], (∀ τ, ‖un τ‖ = 1) ∧ MomAt D cc (ambOf s B χ cD) u w ι un

end GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MovementLaw
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def AgreeOff (T : ℕ) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), ((T : ℕ) : 𝓞 E) ∉ Q.asIdeal → localization₂ Q.asIdeal N₁ = localization₂ Q.asIdeal N₂

def InRangeOf {K : Type} [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) ∧ ∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x

def relOrd (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : ℤ := ordDet P N₁ - ordDet P N₂

end Generic

open Classical in

def JetsIn {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (deg : X.Tau → ℤ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K) : Prop :=
  ∀ x, Ξ x ≠ 0 → ∀ m : DVar X.Tau a b →₀ ℕ,
    (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
    ∃ y : X.K, A.σ₀ y = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

section Scalar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def muVp (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : X.Kˣ := (mUof Ch mu i P)⁻¹

def moveScal (u : Pr.Word) (i : ℕ) {a b : ℕ} (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  ∏ P ∈ Pr.vT u, ((muVp Ch mu i P ^ (-relOrd P N₁ N₂ + relOrd P N₁' N₂') : X.Kˣ) : X.K) *
    ((Pr.T u : ℕ) : X.K) ^ (((a / 2 : ℕ) : ℤ) * relOrd P N₁' N₂' - ((b / 2 : ℕ) : ℤ) * relOrd P N₁ N₂)

end Scalar

def MoveLaw : Prop :=
  ∀ (Dt : Dat), Dt.Ok →
  ∀ (D : D7) (s : Seam D Dt.X), s.Ok → s.σ₀ = Dt.sig0 →
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → δ ≠ 0 →
  ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ →
  ∀ (cD : D.what₂.Tau → ℂ)
    (sel : HeightOneSpectrum (𝓞 Dt.X.F) → HeightOneSpectrum (𝓞 Dt.X.E)), IsSel Dt.X sel →
  ∀ (S : Set ℕ), hostS D.host.q D.host.d (Dt.Pr.g 0) (Dt.Pr.g 1) (Set.range Dt.Pr.T ∪ (D.host.small : Set ℕ)) ⊆ S →
  ∀ (mu : Tup Dt.X.F Dt.X.E Dt.X.K S) (cst : LocCst Dt.X (rowSG Dt.Pr sel mu)) (u : Dt.Pr.Word),
    (∀ P ∈ Sall (Pr := Dt.Pr) sel mu u, Nat.Coprime (Ideal.absNorm cc) (Formalism.L2.Col.qOf P)) →
  ∀ (i j : ℕ), j = i + 1 → j ≤ Dt.R.m →
  ∀ (N₁ N₂ : Submodule (𝓞 Dt.X.E) (Sp Dt.X.E (Dt.R.N i))) (N₁' N₂' : Submodule (𝓞 Dt.X.E) (Sp Dt.X.E (Dt.R.N j))),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
    AgreeOff (Dt.Pr.T u) N₁ N₂ → AgreeOff (Dt.Pr.T u) N₁' N₂' →
  ∀ (fr : Frs Dt.X.E (Dt.R.N i) (rowSG Dt.Pr sel mu)) (fr' : Frs Dt.X.E (Dt.R.N j) (rowSG Dt.Pr sel mu))
    (Ξ : HomE Dt.X.E (Dt.R.N i) (Dt.R.N j) → Dt.X.K),
    InRangeOf (Sall (Pr := Dt.Pr) sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    InRangeOf (Sall (Pr := Dt.Pr) sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    JetsIn (ambOf s B χ cD) (Sall (Pr := Dt.Pr) sel mu u) (cBof sel mu cst u)
      (fun τ => ∑ k, (Dt.W.nuW u (i + 1) τ).w k) N₁ N₁' Ξ →
    JetsIn (ambOf s B χ cD) (Sall (Pr := Dt.Pr) sel mu u) (cBof sel mu cst u)
      (fun τ => ∑ k, (Dt.W.nuW u (i + 1) τ).w k) N₂ N₂' Ξ →
    kerOf (stepT Dt.W Dt.Ch sel mu cst (ambOf s B χ cD) u i (Dt.W.lamTrue u j))
        (Sall (Pr := Dt.Pr) sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      moveScal Dt.Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT Dt.W Dt.Ch sel mu cst (ambOf s B χ cD) u i (Dt.W.lamTrue u j))
          (Sall (Pr := Dt.Pr) sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

end GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw
end
end

