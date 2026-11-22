import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalRingCardinality.DataForms
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.ThetaLift
section
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

section Theta
variable {P : Type} [Fintype P]

def piH (z w : P → ℂ) : ℂ := ∑ p, z p * (starRingEnd ℂ) (w p)

def IsTheta (Λ : AddSubgroup (P → ℂ)) (α : (P → ℂ) → ℂ) (Th : (P → ℂ) → ℂ) : Prop :=
  Differentiable ℂ Th ∧ ∀ l ∈ Λ, ‖α l‖ = 1 ∧
    ∀ z, Th (z + l) = α l * Complex.exp (piH z l + piH l l / 2) * Th z

def nTh (Th : (P → ℂ) → ℂ) (z : P → ℂ) : ℝ := ‖Th z‖ ^ 2 * Real.exp (-(piH z z).re)

def HasNormSq (Λ : AddSubgroup (P → ℂ)) (Th : (P → ℂ) → ℂ) (r : ℝ) : Prop :=
  ∃ F : Set (P → ℂ), IsAddFundamentalDomain Λ F volume ∧ IntegrableOn (nTh Th) F volume ∧
    (∫ z in F, nTh Th z) / Real.pi ^ Fintype.card P = r

def transl (t : P → ℂ) (Th : (P → ℂ) → ℂ) (z : P → ℂ) : ℂ :=
  Complex.exp (-piH z t - piH t t / 2) * Th (z + t)

def IsTranslSum (Λ : AddSubgroup (P → ℂ)) (Th0 Th : (P → ℂ) → ℂ) (S : ℝ) : Prop :=
  ∃ (κ : ℂ) (R : Finset (P → ℂ)) (c : (P → ℂ) → ℂ),
    (∀ t ∈ R, ∃ n : ℕ, 0 < n ∧ n • t ∈ Λ) ∧
    ‖κ‖ * ∑ t ∈ R, ‖c t‖ ≤ Real.exp S ∧
    ∀ z, Th z = κ * ∑ t ∈ R, c t * transl t Th0 z

end Theta

section Schur
variable {T : Type} [Fintype T] {n₀ : ℕ}

abbrev Cell (ν : T → Fin n₀ → ℕ) : Type := Σ τ : T, Σ r : Fin n₀, Fin (ν τ r)

abbrev Tens (ν : T → Fin n₀ → ℕ) (n : ℕ) : Type := (Cell ν → Fin n) → ℂ

def tensSq {ν : T → Fin n₀ → ℕ} {n : ℕ} (w : Tens ν n) : ℝ := ∑ a, ‖w a‖ ^ 2

def tpow (ν : T → Fin n₀ → ℕ) {n n' : ℕ} (g : T → Fin n' → Fin n → ℂ) (w : Tens ν n) : Tens ν n' :=
  fun a => ∑ b, (∏ c : Cell ν, g c.1 (a c) (b c)) * w b

def extVec (ν : T → Fin n₀ → ℕ) {n : ℕ} (h : n₀ ≤ n) : Tens ν n :=
  fun a => ∑ σ : Equiv.Perm (Cell ν),
    if (∀ c, (σ c).1 = c.1 ∧ ((σ c).2.2 : ℕ) = (c.2.2 : ℕ)) ∧ (∀ c, a c = Fin.castLE h (σ c).2.1)
    then ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0

def schurSpace (ν : T → Fin n₀ → ℕ) {n : ℕ} (h : n₀ ≤ n) : Submodule ℂ (Tens ν n) :=
  Submodule.span ℂ (Set.range fun g : T → Fin n → Fin n → ℂ => tpow ν g (extVec ν h))

def jetOp (ν : T → Fin n₀ → ℕ) {n₁ : ℕ} (c : T → ℂ) (Th : (T × Fin n₁ × Fin n₀ → ℂ) → ℂ)
    (w : Tens ν n₀) : Tens ν n₁ :=
  fun a => ∑ b, iteratedFDeriv ℂ (Fintype.card (Cell ν)) Th 0
    (fun k => Pi.single (((Fintype.equivFin (Cell ν)).symm k).1, a ((Fintype.equivFin (Cell ν)).symm k),
      b ((Fintype.equivFin (Cell ν)).symm k)) (c ((Fintype.equivFin (Cell ν)).symm k).1)) * w b

end Schur

def hookProd (n : ℕ) (ν : ℕ → ℕ) : ℕ :=
  ∏ r ∈ Finset.range n, ∏ c ∈ Finset.range (ν r),
    ((ν r - c - 1) + ((Finset.Ioo r n).filter (fun r' => c < ν r')).card + 1)

example : hookProd 2 (fun r => if r = 0 then 3 else 1) = 8 := by decide

def IsOrthoFrame {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (τ : E →+* ℂ) {n : ℕ}
    (fr : S.V →ₛₗ[τ] (Fin n → ℂ)) : Prop :=
  ∀ x y, ∑ a, (starRingEnd ℂ) (fr x a) * fr y a = τ (S.hT x y)

def pairLattice {E : Type} [Field E] [NumberField E] [StarRing E] {T : Type} (S S' : HSpace E)
    (pl : T → (E →+* ℂ)) {n₀ n₁ : ℕ} (fr : ∀ τ, S.V →ₛₗ[pl τ] (Fin n₀ → ℂ))
    (fr' : ∀ τ, S'.V →ₛₗ[pl τ] (Fin n₁ → ℂ)) (𝔞 : Submodule (𝓞 E) E) (ξ : E)
    (L : Submodule (𝓞 E) S.V) (L' : Submodule (𝓞 E) S'.V) : AddSubgroup (T × Fin n₁ × Fin n₀ → ℂ) :=
  AddSubgroup.closure {u | ∃ φ : S.V →ₗ[E] S'.V, (∀ x ∈ L, φ x ∈ Formalism.HermitianLatticesTheory.idealSmul 𝔞 L') ∧
    ∀ τ x a, ∑ b, u (τ, a, b) * fr τ x b =
      ((Real.sqrt (2 * Real.pi * ‖pl τ ξ‖) : ℝ) : ℂ) * fr' τ (φ x) a}

variable (D : D7)

theorem N_le_succ (i : ℕ) : D.R.N i ≤ D.R.N (i + 1) := by
  unfold Ranks.N; nlinarith

def nuNat (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ) : ℕ := ⌊DV.nuRow D u j τ r⌋₊

def nuFin (u : D.what₂.Word) (i : ℕ) : D.what₂.Tau → Fin (D.R.N i) → ℕ := fun τ r => nuNat D u (i + 1) τ r

def nuSize (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : ℝ :=
  ∑ r ∈ Finset.range (D.R.N i), DV.nuRow D u (i + 1) τ r

def liftNormSq (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ) : ℝ :=
  Formalism.HN.opNormAt ((D.fm u).lat i).b ((D.fm u).lat i).X ((D.fm u).lat (i + 1)).b ((D.fm u).lat (i + 1)).X
    (InfinitePlace.mk s) ((D.fm u).KL i hK) ^ 2

def conjPlace (s : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  s.comp (D.embE.comp
    (D.host.sigmaOf ((D.eTau τ : D.R.Psi) : D.R.GG) : D.host.E →+* D.host.E))

def datumIdeal (cc : Ideal (𝓞 D.host.K)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0

def datumXi (cc : Ideal (𝓞 D.host.K)) : D.host.E :=
  -1 / ((Ideal.absNorm cc : D.host.E) * D.host.sqrtMinusD)

def classSq (u : D.what₂.Word) (i' : ℕ) {n₀ n : ℕ} {ν : D.what₂.Tau → Fin n₀ → ℕ}
    (φ : (D.mem u).C.cls i' → Tens ν n) : ℝ :=
  ∑ c, ((Nat.card ((D.mem u).C.stab i' c) : ℕ) : ℝ)⁻¹ * tensSq (φ c)

def IsThetaLift (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ) (S r : ℝ) : Prop :=
  letI := D.host.cmStar
  ∃ (s' : D.what₂.LL →+* ℂ) (cc : Ideal (𝓞 D.host.K))
    (fr : ∀ τ, (D.sp.X i).V →ₛₗ[conjPlace D s' τ] (Fin (D.R.N i) → ℂ))
    (fr' : ∀ τ, (D.sp.X (i + 1)).V →ₛₗ[conjPlace D s' τ] (Fin (D.R.N (i + 1)) → ℂ))
    (ζ : D.what₂.Tau → ℂ)
    (e₀ : ((D.fm u).lat i).V →ₛₗ[s'] ((D.mem u).C.cls i → Tens (nuFin D u i) (D.R.N i)))
    (e₁ : ((D.fm u).lat (i + 1)).V →ₛₗ[s'] ((D.mem u).C.cls (i + 1) → Tens (nuFin D u i) (D.R.N (i + 1))))
    (ε : (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → ℂ)
    (Th : (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) →
      (D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i) → ℂ) → ℂ),
    InfinitePlace.mk s' = InfinitePlace.mk s ∧
    s' (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD) ∧
    cc ≠ ⊥ ∧
    (∀ τ, IsOrthoFrame (D.sp.X i) (conjPlace D s' τ) (fr τ)) ∧
    (∀ τ, IsOrthoFrame (D.sp.X (i + 1)) (conjPlace D s' τ) (fr' τ)) ∧
    (∀ τ, ‖ζ τ‖ = 1) ∧
    (∀ x c, e₀ x c ∈ schurSpace (nuFin D u i) le_rfl) ∧
    (∀ x c, e₁ x c ∈ schurSpace (nuFin D u i) (N_le_succ D i)) ∧
    (∀ x, Formalism.HermitianLatticesTheory.normAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk s) x ^ 2 =
      classSq D u i (e₀ x)) ∧
    (∀ x, Formalism.HermitianLatticesTheory.normAt ((D.fm u).lat (i + 1)).b ((D.fm u).lat (i + 1)).X (InfinitePlace.mk s) x ^ 2 =
      classSq D u (i + 1) (e₁ x)) ∧
    (∀ c c', ‖ε c c'‖ = 1) ∧
    (∀ x c', e₁ ((D.fm u).KL i hK x) c' = ∑ c, ((D.mem u).C.wt i c * ε c c') •
      jetOp (nuFin D u i) (fun τ => (((Real.sqrt (D.gx.Om τ s))⁻¹ : ℝ) : ℂ) * ζ τ) (Th c c') (e₀ x c)) ∧
    ∀ c c', ∃ (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) (M' : Submodule (𝓞 D.host.E) (D.sp.X (i + 1)).V)
      (α Th0 : (D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i) → ℂ) → ℂ),
      Submodule.IsLattice D.host.E M ∧ Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X i).hT M ∧
      Submodule.IsLattice D.host.E M' ∧ Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X (i + 1)).hT M' ∧
      IsTheta (pairLattice (D.sp.X i) (D.sp.X (i + 1)) (conjPlace D s') fr fr'
        (datumIdeal D cc : Submodule (𝓞 D.host.E) D.host.E) (datumXi D cc) M M') α Th0 ∧
      HasNormSq (pairLattice (D.sp.X i) (D.sp.X (i + 1)) (conjPlace D s') fr fr'
        (datumIdeal D cc : Submodule (𝓞 D.host.E) D.host.E) (datumXi D cc) M M') Th0 r ∧
      IsTranslSum (pairLattice (D.sp.X i) (D.sp.X (i + 1)) (conjPlace D s') fr fr'
        (datumIdeal D cc : Submodule (𝓞 D.host.E) D.host.E) (datumXi D cc) M M') Th0 (Th c c') S

def mainPh (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ τ, ((∑ r ∈ Finset.range (D.R.N i), phF (DV.nuRow D u (i + 1) τ r)) -
    nuSize D u i τ * Real.log (D.gx.Om τ s))

def mainHook (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ∑ τ, (Real.log (hookProd (D.R.N i) (nuNat D u (i + 1) τ) : ℝ) - nuSize D u i τ * Real.log (D.gx.Om τ s))

def ExactBound : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ) (S r : ℝ),
    IsThetaLift D u i hK s S r →
    liftNormSq D u i hK s ≤ Real.exp (mainPh D u i s) * r *
      Real.exp ((D.R.f : ℝ) * (D.R.N i * D.R.N (i + 1)) *
          Real.log (8 + 32 * ((D.R.f : ℝ) * (D.R.N i * D.R.N (i + 1))) * D.host.v) + 2 * S +
        ∑ τ, (1 + 2 * ((D.R.N i : ℝ) * D.R.N (i + 1)) * Real.log (2 * nuSize D u i τ + 2))) *
      ((Fintype.card ((D.mem u).C.cls i) : ℝ) * Fintype.card ((D.mem u).C.cls (i + 1)))

def logLev (u : D.what₂.Word) : ℝ := Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * (D.mem u).A.T)

def restTerm (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  (D.R.f : ℝ) * D.R.N i * D.R.N (i + 1) * Real.log (D.gx.thOne s ^ 2) +
    C * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 * (L.sc.L + logLev D u)

def BoundPh (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) : Prop :=
  liftNormSq D u i hK s ≤ Real.exp (mainPh D u i s + restTerm D L C u i s)

def BoundHook (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) : Prop :=
  liftNormSq D u i hK s ≤ Real.exp (mainHook D u i s + restTerm D L C u i s)

def Inputs (L : SizeData₂ D) (C' : ℝ) (u : D.what₂.Word) (i : ℕ) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) : Prop :=
  IsThetaLift D u i hK s (C' * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 * logLev D u)
      ((D.gx.thOne s ^ (D.R.f * D.R.N i * D.R.N (i + 1))) ^ 2) ∧
    (Fintype.card ((D.mem u).C.cls i) : ℝ) ≤
      Real.exp (C' * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * (L.sc.L + logLev D u)) ∧
    (Fintype.card ((D.mem u).C.cls (i + 1)) : ℝ) ≤
      Real.exp (C' * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * (L.sc.L + logLev D u))

def SizeAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ),
    BoundPh D L C u i hK s ∧ BoundHook D L C u i hK s

def ParametersSizeBoundAt (L : SizeData₂ D) (C' C : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ),
    Inputs D L C' u i hK s → BoundPh D L C u i hK s ∧ BoundHook D L C u i hK s

def SizeFam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ p : Fm.Ix x, SizeAt (Fm.D x p) (Fm.L x p) C

def InputsFam {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C' x0 : ℝ, ∀ x ≥ x0, ∀ (p : Fm.Ix x) (u : (Fm.D x p).what₂.Word) (i : ℕ), i < (Fm.D x p).R.m →
    ∀ (hK : ((Fm.D x p).fm u).KRat i) (s : (Fm.D x p).what₂.LL →+* ℂ), Inputs (Fm.D x p) (Fm.L x p) C' u i hK s

def LiftSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ C' : ℝ, ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ p : Fm.Ix x, ParametersSizeBoundAt (Fm.D x p) (Fm.L x p) C' C

end GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistedTriples
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable (D : D7)

abbrev Trip (a : D.nd.Loc) : Type := D.ntw.Sig (D.ntw.twOf a)

def rhoTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* GL (Fin D.R.r) (D.nd.O a) :=
  mapRep (D.ntw.twist₂ a) (D.ntw.rhoS (D.ntw.twOf a) s)

def chiTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* (D.nd.O a)ˣ :=
  (Units.map (D.ntw.twist₂ a).toMonoidHom).comp
    (D.ntw.chi1 (D.ntw.twOf a) (D.ntw.jS (D.ntw.twOf a) s) (D.ntw.side (D.ntw.twOf a) s))

def tTrip (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a) :=
  twistM ((Units.coeHom _).comp (rhoTrip D a s)) (chiTrip D a s)⁻¹

def badS (a : D.nd.Loc) : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
  {v | ((∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨ v ∈ D.ntw.pD (D.ntw.twOf a)) ∧
    v ∉ placesOver D.host.E (D.nd.l a)}

def selT (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) :
    Submodule (D.nd.O a) (H1 (WKG (twistM (tTrip D a s) ψ⁻¹))) :=
  Br.selG D.nd.plOm (D.nd.l a) (D.loc (D.nd.l a)) (D.nbr a) (badS D a ∪ ↑(D.nd.Q a))
    (twistM (tTrip D a s) ψ⁻¹)

def sTFin (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) : Prop :=
  Module.length (D.nd.O a) ↥(selT D a s ψ) < ⊤

def sT_vp (a : D.nd.Loc) (s : Trip D a) (ψ : GE D.nd →* (D.nd.O a)ˣ) : ℚ :=
  lenUnit (O := D.nd.O a) (D.nd.l a) ↥(selT D a s ψ)

def psiAt (a : D.nd.Loc) (s : Trip D a) : GE D.nd →* (D.nd.O a)ˣ :=
  if D.ntw.side (D.ntw.twOf a) s = D.ntw.twSide a then D.ntw.psiL a else (D.ntw.psiL a)⁻¹

def IsGoodRow (a : D.nd.Loc) (σ : D.what₂.FT) : Prop :=
  D.what₂.isot (D.nd.j a) σ ≠ ⊥ ∧ D.nd.goodRow σ

def IsRhoOfRow (a : D.nd.Loc) (σ : D.what₂.FT) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  IsSSRep (mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) ρ) ∧
  ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w →
    ∀ (B : ValuationSubring D.nd.Om) (g : GE D.nd), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) g →
      ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).charpoly.map
          (iotaO D.nd D.naut a) =
        galPol D.naut (D.naut.lpTw (D.naut.lpChar (D.naut.locW a σ w) (D.naut.locG D.naut.etaTinv w))
          ((1 - (D.R.nV : ℝ)) / 2))

def IsTripleOf (a : D.nd.Loc) (σ : D.what₂.FT) (s : Trip D a) : Prop :=
  D.ntw.jS (D.ntw.twOf a) s = D.nd.j a ∧ D.ntw.side (D.ntw.twOf a) s = D.ntw.twSide a ∧
    IsRhoOfRow D a σ (rhoTrip D a s)

def TripAll : Prop :=
  ∀ (a : D.nd.Loc) (σ : D.what₂.FT), IsGoodRow D a σ → ∃ s : Trip D a, IsTripleOf D a σ s

def IsRowOf (a : D.nd.Loc) (π : D.nd.X a) (σ : D.what₂.FT) : Prop :=
  IsGoodRow D a σ ∧ ∃ Sg : List (Part D.naut.CG),
    HasParamW D.nd D.naut a σ Sg ∧ HasParamX D.nd D.naut a π Sg

def Attached (a : D.nd.Loc) (π : D.nd.X a) (s : Trip D a) : Prop :=
  ∃ σ, IsRowOf D a π σ ∧ IsTripleOf D a σ s

def IsRhoOfPt (a : D.nd.Loc) (π : D.nd.X a) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a))) ∧
  ∃ r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O a), IsHeckeGalois D.nd a π r ∧
    ∃ e : (Fin D.R.nV → KK D.nd a) ≃ₗ[KK D.nd a] ((Fin D.R.r → KK D.nd a) × (Fin D.R.t → KK D.nd a)),
      ∀ g u, e ((((r g : GL (Fin D.R.nV) (D.nd.O a)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O a)).map
          (toK D.nd a)).mulVec u) =
        ((((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).map
            (toK D.nd a)).mulVec (e u).1,
          fun c : Fin D.R.t =>
            toK D.nd a ((D.nd.chi a ((c : ℕ) + 1) g : (D.nd.O a)ˣ) : D.nd.O a) * (e u).2 c)

def ind2 (l : ℕ) : ℚ := if l = 2 then 1 else 0

def epsL (l : ℕ) : ℚ := ((l : ℚ) ^ 2)⁻¹

def TwistSmallAt (a : D.nd.Loc) : Prop :=
  ∃ ε : Trip D a → ℝ, (∀ s, 0 ≤ ε s) ∧ ∑ s, ε s ≤ (epsL (D.nd.l a) : ℝ) ∧
    ∀ s, sTFin D a s (psiAt D a s) ∧ (sT_vp D a s (psiAt D a s) : ℝ) ≤ (ind2 (D.nd.l a) : ℝ) + ε s

def selEq_at : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a →
    (∃ s, Attached D a π s) ∧
    ∀ (s : Trip D a), Attached D a π s →
      ∀ ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a)), IsRhoOfPt D a π (ρ π) →
        (Br.sFin D.loc D.nbr a ρ π ↔ sTFin D a s (D.ntw.psiL a)) ∧
        Br.sPi D.loc D.nbr a ρ π = sT_vp D a s (D.ntw.psiL a)

def selBound_at : Prop :=
  ∀ (a : D.nd.Loc), TwistSmallAt D a → ∀ (π : D.nd.X a), π ∈ D.nd.Zgood a →
    ∀ ρ : D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a)), IsRhoOfPt D a π (ρ π) →
      Br.sFin D.loc D.nbr a ρ π ∧
      Br.sPi D.loc D.nbr a ρ π ≤ ind2 (D.nd.l a) + epsL (D.nd.l a) ∧
      (D.nd.l a ≠ 2 → Br.sPi D.loc D.nbr a ρ π + epsL (D.nd.l a) ≤ 2 * epsL (D.nd.l a)) ∧
      (D.nd.l a = 2 → Br.sPi D.loc D.nbr a ρ π + epsL (D.nd.l a) ≤ 3 / 2)

def dGood (j : ℕ) (w : D.what₂.places.Pl) : ℕ :=
  ∑ a ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood a, D.nd.mult a π

def selSum_at : Prop :=
  ∀ (j : ℕ) (w : D.what₂.places.Pl), (∀ a ∈ D.nd.locs j w, TwistSmallAt D a) →
    ∀ ρ : ∀ a : D.nd.Loc, D.nd.X a → (GE D.nd →* GL (Fin D.R.r) (D.nd.O a)),
      (∀ a ∈ D.nd.locs j w, ∀ π ∈ D.nd.Zgood a, IsRhoOfPt D a π (ρ a π)) →
      (∀ a ∈ D.nd.locs j w, ∀ π ∈ D.nd.Zgood a, Br.sFin D.loc D.nbr a (ρ a) π) ∧
      ∑ a ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood a, (D.nd.mult a π : ℚ) * Br.sPi D.loc D.nbr a (ρ a) π ≤
        (dGood D j w : ℚ) * (ind2 (D.what₂.places.resChar w) + epsL (D.what₂.places.resChar w))

def tie_at : Prop := TripAll D → selEq_at D ∧ selBound_at D ∧ selSum_at D

def GoodPtHasRow : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a → ∃ σ, IsRowOf D a π σ

def GoodPtResIrr : Prop :=
  ∀ (a : D.nd.Loc) (π : D.nd.X a), π ∈ D.nd.Zgood a →
    ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O a), IsRhoOfPt D a π ρ → AbsIrrSub (redRep D.nd a ρ) ⊤

def tie_step : Prop := GoodPtHasRow D → GoodPtResIrr D → tie_at D

def tieF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, tie_at (Fm.D x i)

def tieClosed (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm _ => tieF Fm)

theorem badS_eq (a : D.nd.Loc) : badS D a = ↑(D.nd.S a) := by
  ext v
  have h := D.ntw.pD_eq (D.ntw.twOf a)
  rw [D.ntw.twOf_l a] at h
  have h' : v ∈ D.ntw.pD (D.ntw.twOf a) ↔
      v ∈ placesOver D.host.E (if D.nd.l a = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← h]; rfl
  simp only [badS, Set.mem_setOf_eq, Finset.mem_coe, D.nd.S_def, h', Fin.exists_fin_two, or_assoc]

example : ind2 2 + epsL 2 + epsL 2 = 3 / 2 := by norm_num [ind2, epsL]

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WeightDictionaryLifting
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeightDictionaryLifting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Param

variable {R : Ranks} (P : HCParam R) (j : Fin R.m)

def run : Multiset ℚ :=
  (Finset.Icc 1 R.t).val.map fun c : ℕ => -P.e j + ((R.t : ℚ) + 1) / 2 - (c : ℚ)

def param : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map P.v +
    (Finset.univ : Finset (Fin R.m)).val.map (fun i => -P.b i) + run P j

end Param

variable (D : D7)

def liftIx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def embOf (ρ : D.what₂.Tau) : D.host.E →+* ℂ :=
  D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)

def Induces (φ : D.host.E →+* ℂ) (ρ : D.what₂.Tau) : Prop :=
  ∀ x : D.host.E, x ∈ D.host.F → φ x = embOf D ρ x

def typeU (ep : Bool) : Set (D.host.E →+* ℂ) :=
  {φ | (if ep then (starRingEnd ℂ).comp φ else φ) ∈
    D.host.cmType}

open Classical in

def sgn (ep : Bool) (φ : D.host.E →+* ℂ) : ℚ := if φ ∈ typeU D ep then 1 else -1

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev LocEmb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def cxEmb (τ : LocEmb D i w hw) : D.host.E →+* ℂ :=
  (D.naut.iotaQC i).toRingHom.comp
    (((D.nbr i w hw).LL.1.val : Br.LL D.nbr i w hw →+* Qbar (D.nd.l i)).comp
      ((τ : Br.Kw D.nbr i w hw →+* Br.LL D.nbr i w hw).comp (Br.cEw D.nbr i w hw)))

def JumpsAre {a : ℕ} (r : GE D.nd →* GL (Fin a) (D.nd.O i)) (τ : LocEmb D i w hw) (M : Multiset ℚ) : Prop :=
  (∀ p ∈ M, ∃ z : ℤ, p = z) ∧
    ∀ z : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ z = (M.count (z : ℚ) : ℤ)

end Local

def chiGL (i : D.nd.Loc) (c : ℕ) : GE D.nd →* GL (Fin 1) (D.nd.O i) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (D.nd.chi i c)

def IsSummand (i : D.nd.Loc) {a : ℕ} (r : GE D.nd →* GL (Fin a) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ) :
    Prop :=
  ∃ (v : Fin a → KK D.nd i) (f : (Fin a → KK D.nd i) →ₗ[KK D.nd i] KK D.nd i), f v = 1 ∧
    (∀ g, (((r g : GL (Fin a) (D.nd.O i)) : Matrix (Fin a) (Fin a) (D.nd.O i)).map (toK D.nd i)).mulVec v =
      toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • v) ∧
    ∀ g u, f ((((r g : GL (Fin a) (D.nd.O i)) : Matrix (Fin a) (Fin a) (D.nd.O i)).map (toK D.nd i)).mulVec u) =
      toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) * f u

def WeightTie : Prop := ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
  D.naut.infWt i (embOf D ρ) = (param (D.hc ρ) (liftIx D i)).map (fun p : ℚ => (p : ℂ) - 1 / 2) ∧
  D.naut.infWt i ((starRingEnd ℂ).comp (embOf D ρ)) =
    (param (D.hc ρ) (liftIx D i)).map (fun p : ℚ => -((p : ℂ) - 1 / 2))

def CharTie : Prop := ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
  D.naut.infG (D.naut.muC i) (embOf D ρ) = {-(((D.hc ρ).e (liftIx D i) : ℚ) : ℂ)} ∧
  D.naut.infG (D.naut.muC i) ((starRingEnd ℂ).comp (embOf D ρ)) = {(((D.hc ρ).e (liftIx D i) : ℚ) : ℂ)} ∧
  D.naut.infG D.naut.etaTinv (embOf D ρ) = {-(1 / 2 : ℂ)} ∧
  D.naut.infG D.naut.etaTinv ((starRingEnd ℂ).comp (embOf D ρ)) = {(1 / 2 : ℂ)}

abbrev Shift : Type := ℕ → D.what₂.places.Pl → (D.host.E →+* ℂ) → ℤ

def toJump (ep : Bool) (c : Shift D) (i : D.nd.Loc) (φ : D.host.E →+* ℂ) (p : ℚ) : ℚ :=
  sgn D ep φ * p + (c (D.nd.j i) (D.nd.w i) φ : ℚ)

def PointJumps (ep : Bool) (c : Shift D) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      Br.IsdRW D.loc D.nbr i w hw r ∧
      ∀ (τ : LocEmb D i w hw) (ρ : D.what₂.Tau), Induces D (cxEmb D i w hw τ) ρ →
        JumpsAre D i w hw r τ
          ((param (D.hc ρ) (liftIx D i)).map (toJump D ep c i (cxEmb D i w hw τ)))

def PointCrys : Prop :=
  ∀ (i : D.nd.Loc), D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
        Br.IsCrysW D.loc D.nbr i w hw r

def BlockSummand : Prop :=
  ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, ∀ (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)),
    IsHeckeGalois D.nd i π r → ∀ k, 1 ≤ k → k ≤ D.R.t → IsSummand D i r (D.nd.chi i k)

def BlockJumps (ep : Bool) (c : Shift D) : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : LocEmb D i w hw) (ρ : D.what₂.Tau), Induces D (cxEmb D i w hw τ) ρ →
    ∃ a : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ D.R.t → JumpsAre D i w hw (chiGL D i k) τ {(a : ℚ) + ((k : ℚ) - 1)}) ∧
      (run (D.hc ρ) (liftIx D i)).map (toJump D ep c i (cxEmb D i w hw τ)) =
        (Multiset.range D.R.t).map fun k : ℕ => (a : ℚ) + (k : ℚ)

def DictConcl : Prop :=
  (∃ (ep : Bool) (c : Shift D), PointJumps D ep c ∧ BlockJumps D ep c) ∧ PointCrys D ∧ BlockSummand D

def Dict_at : Prop := WeightTie D → CharTie D → DictConcl D

def DictF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Dict_at (Fm.D x i)

def DictClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => DictF Fm

example (φ : D.host.E →+* ℂ) : φ ∈ typeU D true ↔ (starRingEnd ℂ).comp φ ∈ typeU D false := Iff.rfl

example (ρ : D.what₂.Tau) : Induces D (embOf D ρ) ρ := fun _ _ => rfl

end GlobalTheory.IndefiniteRowSideFullHecke.WeightDictionaryLifting

end
end

