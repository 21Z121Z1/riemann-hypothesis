import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.MatrixKernelDiamondCommutation

-- bundled from Formalism.LocalToGlobal.KernelLattices.JetFieldLeKR
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

section Field

variable {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

def Amb.jetSet : Set ℂ :=
  {z | ∃ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b) (m : DVar X.Tau a b →₀ ℕ),
    InRange Sall D c N N' x ∧ z = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m}

def Amb.jetField : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (A.jetSet a b Sall D)

def rangeIF {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange

def Amb.HasJets : Prop := ∀ z ∈ A.jetField a b Sall D, ∃ k : X.K, A.σ₀ k = z

end Field

def JetsRatIff : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ), A.JetsRat a b Sall D ↔ A.HasJets a b Sall D

def JetsRatFin : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ), A.JetsRat a b Sall D →
    FiniteDimensional ℚ (A.jetField a b Sall D)

open Cardinal in

def FixedOfAut : Prop :=
  ∀ k : IntermediateField ℚ ℂ, #k ≤ ℵ₀ → ∀ z : ℂ, (∀ s : ℂ ≃+* ℂ, (∀ x ∈ k, s x = x) → s z = z) → z ∈ k

section KR

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (cD : D.what₂.Tau → ℂ) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1)

def kRGen : Set ℂ :=
  {z | ∃ τ x, z = TaylorLogMetric.embT D τ x} ∪ {TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc δ), TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc δ)} ∪
    {z | ∃ t : ℂ, t ∉ B.L.lattice ∧ (((2 * D0) ^ 2 : ℕ) : ℂ) * t ∈ B.L.lattice ∧ (z = B.L.weierstrassP t ∨ z = B.L.derivWeierstrassP t)} ∪
    Set.range cD ∪ {TaylorLogMetric.taylor D (B.thZero 1 1) α}

def kR : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (kRGen B cD D0 α)

end KR

def Amb.GalInv {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (k : IntermediateField ℚ ℂ) : Prop :=
  ∀ s : ℂ ≃+* ℂ, (∀ x ∈ k, s x = x) → ∀ z ∈ A.jetSet a b Sall D, s z = z

def JetsRatOfInv : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (k : IntermediateField ℚ ℂ),
    A.GalInv a b Sall D k → (∀ z ∈ k, ∃ y : X.K, A.σ₀ y = z) → A.JetsRat a b Sall D

section Norm

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
  (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ)

def RatKHyp0 : Prop :=
  s.Ok ∧ TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ TaylorLogMetric.IsChi D χ ∧ Even a ∧ Even b ∧ 0 < D0 ∧
    (ambOf s B χ cD : Amb X).LaHyp a b Sall ∧ ∀ P ∈ Sall, (2 : 𝓞 X.E) ∉ P.asIdeal

def RatKHyp (α : TaylorLogMetric.Mono D 1 1) : Prop :=
  RatKHyp0 s B χ cD a b Sall D0 ∧ TaylorLogMetric.taylor D (B.thZero 1 1) α ≠ 0

end Norm

def RatKGal : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1), RatKHyp s B χ cD a b Sall D0 α →
    (ambOf s B χ cD : Amb X).GalInv a b Sall D0 (kR B cD D0 α)

def RatKFin : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ), RatKHyp0 s B χ cD a b Sall D0 → IsDgen D cD →
    FiniteDimensional ℚ ((ambOf s B χ cD : Amb X).jetField a b Sall D0)

def KRMem {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (cD : D.what₂.Tau → ℂ) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1) : Prop :=
  ((∃ y, s.σ₀ y = TaylorLogMetric.g2 (TaylorLogMetric.lamOf D cc δ)) ∧ ∃ y, s.σ₀ y = TaylorLogMetric.g3 (TaylorLogMetric.lamOf D cc δ)) ∧
  (∀ t : ℂ, t ∉ B.L.lattice → (((2 * D0) ^ 2 : ℕ) : ℂ) * t ∈ B.L.lattice → (∃ y, s.σ₀ y = B.L.weierstrassP t) ∧ ∃ y, s.σ₀ y = B.L.derivWeierstrassP t) ∧
  (∀ τ, ∃ y, s.σ₀ y = cD τ) ∧ ∃ y, s.σ₀ y = TaylorLogMetric.taylor D (B.thZero 1 1) α

def KRInRange : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (cD : D.what₂.Tau → ℂ) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1),
    s.Ok → KRMem s B cD D0 α → ∀ z ∈ kR B cD D0 α, ∃ y : X.K, s.σ₀ y = z

def JetsRatOfKR : Prop :=
  RatKGal → ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1), RatKHyp s B χ cD a b Sall D0 α → KRMem s B cD D0 α →
    (ambOf s B χ cD : Amb X).JetsRat a b Sall D0

section Tied

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.VQTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) : Prop :=
  ∀ u μ i, i ≤ D.R.m → ∀ c : (D.chTw u μ).cls i, Set.range (t.ent.ev u μ i c) =
    {f | ∃ P ∈ DIV.VV D.what₂.LL (lam u i), f = evG ((t.O u μ).frm i) (sh u i) D.what₂.embLL P}

def KerEntTied.WtTie {ex : Extra D L hT Gi Gl K Y cX} (_t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ) : Prop :=
  ∀ u μ i, i < D.R.m → (∀ τ r, (lam u i τ).natW r + n u i τ = nuT D u i τ r) ∧ (∀ τ, sh u i τ + (D.chTw u μ).sSharp i τ = n u i τ) ∧
    (∀ τ, sh u (i + 1) τ = -(D.chTw u μ).sDiv i τ) ∧ JetInVV D.what₂.LL (lam u i) (lam u (i + 1)) (n u i)

def KerEntTied.KerJets {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (m : DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ),
    ∃ k : D.what₂.LL, D.what₂.embLL k = ((D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c') * jetC (t.O u μ).dgen ((t.O u μ).Th i c c') m

end Tied

def StepsRatOfKR : Prop :=
  RatKGal → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (α : TaylorLogMetric.Mono D 1 1), TaylorLogMetric.taylor D (t.B.thZero 1 1) α ≠ 0 → ∀ u μ i,
    0 < cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u) →
    t.amb.LaHyp (D.R.N i) (D.R.N (i + 1)) (Sall t.sel (t.tup μ) (t.word u)) → (∀ P ∈ Sall t.sel (t.tup μ) (t.word u), (2 : 𝓞 t.X.E) ∉ P.asIdeal) →
    KRMem t.seam t.B t.cD (cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u)) α →
    t.amb.JetsRat (D.R.N i) (D.R.N (i + 1)) (Sall t.sel (t.tup μ) (t.word u)) (cAof t.sel (t.tup μ) (t.cst μ) * cBof t.sel (t.tup μ) (t.cst μ) (t.word u))

def KmapRatOf : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ),
    t.VQTie lam sh → t.WtTie lam sh n → t.KerJets → OrbitPlaces.KmapRat t.ent

section Choice

abbrev fieldsWithK (X : Fields) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (e : X.Tau → X.E →+* M) : Fields :=
  { X with K := M, fieldK := inferInstance, nfK := inferInstance, starK := inferInstance, emb := e }

def Amb.withK {X : Fields} (A : Amb X) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (hM : ∀ τ x, X.embC A.σ₀ τ x ∈ M) :
    Amb (fieldsWithK X M fun τ => (X.embC A.σ₀ τ).codRestrict M (hM τ)) where
  σ₀ := algebraMap M ℂ
  δ := A.δ
  d := A.d
  sc := A.sc
  AA := A.AA
  cD := A.cD
  e := A.e
  chiF := A.chiF

end Choice

def JetSetWithK : Prop :=
  ∀ (X : Fields) (A : Amb X) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (hM : ∀ τ x, X.embC A.σ₀ τ x ∈ M)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ), (A.withK M hM).jetSet a b Sall D = A.jetSet a b Sall D

def JetsRatWithK : Prop :=
  ∀ (X : Fields) (A : Amb X) (M : IntermediateField ℚ ℂ) [NumberField M] [StarRing M] (hM : ∀ τ x, X.embC A.σ₀ τ x ∈ M)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ), A.jetField a b Sall D ≤ M → (A.withK M hM).JetsRat a b Sall D

def JetFieldLeKR : Prop :=
  RatKGal → ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D0 : ℕ) (α : TaylorLogMetric.Mono D 1 1), RatKHyp s B χ cD a b Sall D0 α →
    FiniteDimensional ℚ (kR B cD D0 α) → (ambOf s B χ cD : Amb X).jetField a b Sall D0 ≤ kR B cD D0 α

open Classical in

def degAt {ι : Type} {a b : ℕ} (m : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := (m.support.filter fun k => k.1 = τ).sum fun k => m k

def Amb.JetsRatDeg {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange Sall D c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, degAt m τ = dg τ) → ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m

def JetsRatDegOf : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (dg : X.Tau → ℕ), A.JetsRat a b Sall D → A.JetsRatDeg a b Sall D dg

def JetLocal : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (a b : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K),
    (∀ m, (∀ τ, degAt m τ = ∑ r, ((lam τ).natW r + n τ)) → J m = J' m) → ∀ P ∈ DIV.VV K lam, jetMap J n P = jetMap J' n P

def KerEntTied.RK {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u μ, Formalism.BasicNotions.DV.Used D μ → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (m : DVar D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) →₀ ℕ),
    (∀ τ, degAt m τ = ∑ r, nuT D u i τ r) →
    ∃ k : D.what₂.LL, D.what₂.embLL k = ((D.chTw u μ).rhoDet i c * (D.chTw u μ).rhoDet' i c') * jetC (t.O u μ).dgen ((t.O u μ).Th i c c') m

def KmapRatOfRK : Prop :=
  JetLocal → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (lam : ∀ (_ : D.what₂.Word) (i : ℕ), D.what₂.Tau → DomWeight (D.R.N i))
    (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ),
    t.VQTie lam sh → t.WtTie lam sh n → t.RK → OrbitPlaces.KmapRat t.ent

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KerChTie
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {Pr : Primes X} {m : ℕ}

def OffG (Pr : Primes X) (v : HeightOneSpectrum (𝓞 X.E)) : Prop := ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ v.asIdeal

def MuValTie (Ch : Chars X Pr m) (G : ChGlob X m) : Prop :=
  ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), OffG Pr v → G.σ₀ ((Ch.muVal j v : X.Kˣ) : X.K) = (((G.mu0 j).val v : ℂˣ) : ℂ)

end Gen

def MuValueOfCompatibleData : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m) (G : ChGlob X m) (e : Fin m → X.Tau → ℚ) (eta : Formalism.L2.Host.HChar X.E),
    Ch.Tied G.σ₀ e G.mu0 eta → MuValTie Ch G

def MuValRigid : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch Ch' : Chars X Pr m) (G : ChGlob X m), MuValTie Ch G → MuValTie Ch' G →
    ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), OffG Pr v → Ch.muVal j v = Ch'.muVal j v

def MuValOne : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m) (G : ChGlob X m), (∀ j, G.mu0 j = 1) →
    (MuValTie Ch G ↔ ∀ (j : Fin m) (v : HeightOneSpectrum (𝓞 X.E)), OffG Pr v → Ch.muVal j v = 1)

section Mem

variable {D : D7} {u : D.what₂.Word}

def MemLatAt (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) : Prop :=
  letI := D.host.cmStar
  ∀ i, i ≤ D.R.m → ∃ co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
    (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
    (∀ y, co y ∈ (O.L0 i).1 ↔ y ∈ (D.sp.X i).L0) ∧
    ∀ (c : (D.mem u).C.cls i) y, co y ∈ (O.lat i c).1 ↔
      ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
        y = a + D.host.conj (π : D.host.E) • b

def IsMemAt (O : GL3Theta.LiftObj D (D.mem u).C) (π : 𝓞 D.host.E) : Prop :=
  O.mt = D.muTil ∧ (∀ i c, O.dt i c = D.detCls u i c) ∧ MemLatAt O π

end Mem

def IsMemIff : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (O : GL3Theta.LiftObj D (D.mem u).C),
    O.IsMem ↔ ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
      (π : D.host.E) * D.host.conj (π : D.host.E) = ((D.mem u).A.T : D.host.E) ∧ IsMemAt O π

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.PiSide {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, t.seam.iE ((t.Pr.piT (t.word u) : 𝓞 t.X.E) : t.X.E) = ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)

def KerEntTied.memObj {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (u : D.what₂.Word) : GL3Theta.LiftObj D (D.mem u).C :=
  D.memberColumns_twistedChain_base u ▸ t.O u D.what₂.mu0

def KerEntTied.MemSide {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop :=
  ∀ u, (t.memObj u).IsMem → IsMemAt (t.memObj u) (ex.errX.piT u)

structure KerEntTied.ChTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where

  ch_ok : t.Ch.Ok

  muVal : MuValTie t.Ch t.glob

  piT : t.PiSide

  mem : t.MemSide

def InUse (D : D7) (μ : D.what₂.Tup) : Prop := μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w

end Comparison₂

def PiSideVT : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.PiSide → ∀ u (P : HeightOneSpectrum (𝓞 t.X.E)),
      P ∈ t.Pr.vT (t.word u) ↔ ∃ y ∈ P.asIdeal, t.seam.iE ((y : 𝓞 t.X.E) : t.X.E) = ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)

def PiSideNeConj : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.PiSide → ∀ u,
      t.seam.iE ((t.X.conjO (t.Pr.piT (t.word u)) : 𝓞 t.X.E) : t.X.E) ≠ ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)

def PiSideEmb : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex),
      (t.PiSide → ∀ u τ, t.seam.σ₀ (t.X.emb τ ((t.Pr.piT (t.word u) : 𝓞 t.X.E) : t.X.E)) =
        TaylorLogMetric.embT D (t.seam.iT τ) ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)) ∧
      ∀ τ, (∀ u, t.seam.σ₀ (t.X.emb τ ((t.Pr.piT (t.word u) : 𝓞 t.X.E) : t.X.E)) =
        TaylorLogMetric.embT D (t.seam.iT τ) ((ex.errX.piT u : 𝓞 D.host.E) : D.host.E)) → t.PiSide

def QOffG : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) (μ : D.what₂.Tup), InUse D μ →
      ∀ P ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K), OffG t.Pr P

def MuqAtQ : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), MuValTie t.Ch t.glob → ∀ (μ : D.what₂.Tup), InUse D μ →
      ∀ (i : ℕ) (h : i < D.R.m) (P : rowSG t.Pr t.sel (t.tup μ)), P.1 ∉ t.Pr.vGs →
        t.glob.σ₀ ((t.cst μ).muq (i + 1) P) =
          (((t.glob.mu0 ⟨i, h⟩).val P.1 : ℂˣ) : ℂ)⁻¹ * t.glob.σ₀ ((((qValC (t.tup μ : Chr t.X.F t.X.E t.X.K) P.1)⁻¹ : t.X.Kˣ)) : t.X.K)

def MuqAtQLoc : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
    (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), MuValTie t.Ch t.glob → ∀ (μ : D.what₂.Tup), InUse D μ →
      ∀ (i : ℕ) (h : i < D.R.m) (P : rowSG t.Pr t.sel (t.tup μ)), P.1 ∉ t.Pr.vGs → (t.glob.mu0 ⟨i, h⟩).UnrAt P.1 →
        ((qOf P.1 : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal ^ 2 → ∀ qu : t.X.Eˣ, (qu : t.X.E) = (qOf P.1 : t.X.E) →
          t.glob.σ₀ ((t.cst μ).muq (i + 1) P) =
            (((t.glob.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * t.glob.σ₀ ((((qValC (t.tup μ : Chr t.X.F t.X.E t.X.K) P.1)⁻¹ : t.X.Kˣ)) : t.X.K)

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.ThDatRead
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

open Classical in

def cutDat {X : Fields} {a b : ℕ} (σ : X.K →+* ℂ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K) (x : HomE X.E a b) : ℂ :=
  if x ∈ divLat cA (homAt S N N') then σ (Ξ x) else 0

def ThDatCut : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K), A.LaHyp a b S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
      A.thDat S cA cB N N' Ξ =
        thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) (cutDat A.σ₀ S cA N N' Ξ) (A.e a b N N')

def ThDatThC : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K), A.LaHyp a b S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt S N N') → Ξ x = 0) →
      A.thDat S cA cB N N' Ξ =
        thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) (fun x => A.σ₀ (Ξ x)) (A.e a b N N')

def ThDatRead : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1)) (cA cB : ℕ) (Ξ : HomE X.E (D.R.N i) (D.R.N (i + 1)) → X.K),
    A.LaHyp (D.R.N i) (D.R.N (i + 1)) r.SS → IsSdLat (r.N i c) → IsSdLat (r.N (i + 1) c') → 0 < cA → 0 < cB → r.lev = cA * cB →
    (∀ x, r.Xi i c c' x = A.σ₀ (Ξ x)) →
    (∀ x ∈ divLat cA (homAt r.SS (r.N i c) (r.N (i + 1) c')), ∀ y ∈ mulLat cB (homAt r.SS (r.N i c) (r.N (i + 1) c')), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt r.SS (r.N i c) (r.N (i + 1) c')) → Ξ x = 0) →
      s.push (A.thDat r.SS cA cB (r.N i c) (r.N (i + 1) c') Ξ) = r.Th s A i c c'

def ThDatReadNat : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1)) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E (D.R.N i))) (N' : Submodule (𝓞 X.E) (Sp X.E (D.R.N (i + 1))))
    (Ξ : HomE X.E (D.R.N i) (D.R.N (i + 1)) → X.K),
    (ambOf s B χ cD : Amb X).LaHyp (D.R.N i) (D.R.N (i + 1)) S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    r.SS = S → r.lev = cA * cB → r.N i c = N → r.N (i + 1) c' = N' → (∀ x, r.Xi i c c' x = s.σ₀ (Ξ x)) →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt S N N') → Ξ x = 0) →
      s.push ((ambOf s B χ cD : Amb X).thDat S cA cB N N' Ξ) = r.Th s (ambOf s B χ cD) i c c'

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def ThDatEntry : Prop :=
  ∀ (A : Amb X) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)),
    Pr.Ok → 0 < Pr.T u → L.Ok Ch sel mu cst G m2 → i < m2 → A.LaHyp (R.N i) (R.N (i + 1)) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N p'.deco.1.N (XiEntry Ch sel mu cst L i al be p p') =
        thEntry Ch sel mu cst L (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA i al be p p' (A.e _ _ p.deco.1.N p'.deco.1.N)

def ThDatCpl1 : Prop :=
  ∀ (A : Amb X) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (al : L.β m2)
    (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))),
    Pr.Ok → 0 < Pr.T u → L.Ok Ch sel mu cst G m2 → A.LaHyp (R.N m2) (R.N (m2 + 1)) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N p.deco.1.N (XiCpl1 Ch sel mu cst L m2 al p₀ p Y) =
        thCpl1 Ch sel mu cst L (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 al p₀ p Y (A.e _ _ p₀.deco.1.N p.deco.1.N)

def XiCpl2Adm {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu) : Prop :=
  (∀ x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N),
    ∀ y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N),
      XiCpl2 Ch sel mu cst m2 p Y dd (x + y) = XiCpl2 Ch sel mu cst m2 p Y dd x) ∧
  ∀ x, x ∉ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N) → XiCpl2 Ch sel mu cst m2 p Y dd x = 0

def ThDatCpl2 : Prop :=
  ∀ (A : Amb X) (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    0 < Pr.T u → XiCpl2Adm Ch sel mu cst m2 p Y dd → A.LaHyp (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (tilQ sel mu u dd).1.N (XiCpl2 Ch sel mu cst m2 p Y dd) =
        thCpl2 Ch sel mu cst (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 p Y dd (A.e _ _ p.deco.1.N (tilQ sel mu u dd).1.N)

def XiCpl2AdmOf : Prop :=
  ∀ (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    Pr.Ok → cst.Ok → R.m = m2 + 2 → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → PosT sel mu u → Y ∈ ybSet sel mu cst p.deco.1.N →
      XiCpl2Adm Ch sel mu cst m2 p Y dd

def ThDatCpl2Of : Prop :=
  ∀ (A : Amb X) (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    Pr.Ok → 0 < Pr.T u → cst.Ok → R.m = m2 + 2 → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → PosT sel mu u → Y ∈ ybSet sel mu cst p.deco.1.N →
    A.LaHyp (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (tilQ sel mu u dd).1.N (XiCpl2 Ch sel mu cst m2 p Y dd) =
        thCpl2 Ch sel mu cst (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 p Y dd (A.e _ _ p.deco.1.N (tilQ sel mu u dd).1.N)

end Chain

def ReadThDat : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (Pr : Primes X) (Ch : Chars X Pr D.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
    (G : ChGlob X D.R.m) (v : Pr.Word) (m2 : ℕ), r.IsChain Ch sel mu cst L A.σ₀ v m2 → Pr.Ok → 0 < Pr.T v → L.Ok Ch sel mu cst G m2 →
    (∀ i, i ≤ m2 → A.LaHyp (D.R.N i) (D.R.N (i + 1)) (Sall sel mu v)) →
    ∃ (pt : ∀ i, i ≤ m2 + 1 → C.cls i → ChPt (R := D.R) sel mu v i) (ix : ∀ i, i ≤ m2 → C.cls i → L.β i)
      (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (row : C.cls (m2 + 1 + 1) → Option (RowPt Pr D.R sel mu)),
      (∀ i (hi : i ≤ m2 + 1) c, r.N i c = (pt i hi c).deco.1.N) ∧
      (∀ c', yb c' ∈ ybSet sel mu cst (pt (m2 + 1) le_rfl c').deco.1.N) ∧
      (∀ i (hi : i < m2) c c', r.Th s A i c c' = s.push (A.thDat (Sall sel mu v) (cAof sel mu cst) (cBof sel mu cst v)
        (pt i (by omega) c).deco.1.N (pt (i + 1) (by omega) c').deco.1.N
        (XiEntry Ch sel mu cst L i (ix i hi.le c) (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c')))) ∧
      (∀ c c', r.Th s A m2 c c' = s.push (A.thDat (Sall sel mu v) (cAof sel mu cst) (cBof sel mu cst v)
        (pt m2 (Nat.le_succ _) c).deco.1.N (pt (m2 + 1) le_rfl c').deco.1.N
        (XiCpl1 Ch sel mu cst L m2 (ix m2 le_rfl c) (pt m2 (Nat.le_succ _) c) (pt (m2 + 1) le_rfl c') (yb c')))) ∧
      (∀ c' d, row c' = some d → HEq (r.N (m2 + 1 + 1) c') (tilQ sel mu v d).1.N) ∧
      (∀ c c' d, row c' = some d → HEq (r.Xi (m2 + 1) c c') fun x => A.σ₀ (XiCpl2 Ch sel mu cst m2 (pt (m2 + 1) le_rfl c) (yb c) d x)) ∧
      (∀ i, i ≤ m2 + 1 → ∀ c, r.pin i c) ∧ ∀ c', r.pin (m2 + 1 + 1) c' ↔ ∃ d, row c' = some d

end Formalism.L2.Ker
end
end

