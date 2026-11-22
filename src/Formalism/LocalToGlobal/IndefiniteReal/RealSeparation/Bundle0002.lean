import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0001

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.BesPerSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scalar

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def PsiRat (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  ∀ x : D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D x)) = 1

def IsEmbHom (ι : A.V →ₗ[D.host.E] B.V) (s : GA D A →* GA D B) : Prop :=
  ∀ h, EmbRel B A ι (s h) h

def IsQuotPair (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 μ

def IsNPair (d : BesDat A B ι) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) : Prop :=
  μN.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B d.e) 𝓕N μN ∧ μN 𝓕N = 1

def besIntd (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (φ : GA D A → ℂ)
    (F : GA D B → ℂ) (h : GA D A) (n : NFlag B d.e) : ℂ :=
  φ h * F ((n : GA D B) * s h * (d.y : GA D B)) * star (besChar ψ d (n : GA D B))

def IsBesPer (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) (φ : GA D A → ℂ) (F : GA D B → ℂ)
    (b : ℂ) : Prop :=
  (∀ h, IntegrableOn (besIntd ψ d s φ F h) 𝓕N μN) ∧
    IntegrableOn (fun h => ∫ n in 𝓕N, besIntd ψ d s φ F h n ∂μN) 𝓕 μ ∧
    b = ∫ h in 𝓕, ∫ n in 𝓕N, besIntd ψ d s φ F h n ∂μN ∂μ

def BesStd (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) : Prop :=
  Continuous ψ ∧ PsiRat ψ ∧ HSpace.IsIsomEmb A B ι ∧ IsAniso A ∧ IsEmbHom ι s ∧ IsQuotPair A μ 𝓕 ∧
    IsNPair d μN 𝓕N

def BesPerConv : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι)
    (s : GA D A →* GA D B) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e))
    (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFun A φ → IsAutFun B F →
      ∃ b, IsBesPer ψ d s μ 𝓕 μN 𝓕N φ F b

def BesPerEqvU : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι)
    (s : GA D A →* GA D B) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e))
    (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFun A φ → IsAutFun B F → ∀ (y' : GA D A) (b : ℂ),
      IsBesPer ψ d s μ 𝓕 μN 𝓕N φ F b →
      IsBesPer ψ d s μ 𝓕 μN 𝓕N (rTr A y' φ) (rTr B ((d.y : GA D B)⁻¹ * s y' * (d.y : GA D B)) F) b

def BesPerEqvN : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι)
    (s : GA D A →* GA D B) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e))
    (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFun A φ → IsAutFun B F → ∀ (n₀ : NFlag B d.e) (b : ℂ),
      IsBesPer ψ d s μ 𝓕 μN 𝓕N φ F b →
      IsBesPer ψ d s μ 𝓕 μN 𝓕N φ (rTr B ((d.y : GA D B)⁻¹ * (n₀ : GA D B) * (d.y : GA D B)) F)
        (besChar ψ d (n₀ : GA D B) * b)

end Scalar

section Vec

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def rTrLin (V : HSp D) (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SobContN {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Lie : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (N : ℕ) (ℓ : H →ₗ[ℂ] ℂ) : Prop :=
  ∃ (L : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ X ∈ l, X ∈ Lie) ∧
    ∀ w, SmoothVec Lie σ w → ‖ℓ w‖ ≤ C * (L.map fun l => ‖l.foldr (dRep σ) w‖).sum

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  {Vt : D.what₂.Tau → Type} [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
  {S : D.what₂.Tau → SPar}

open Classical in

def IsColMap (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ))
    (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) : Prop :=
  (∀ v, IsAutFun A (Φ v)) ∧
    ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∀ v : ∀ τ, Vt τ,
      Φ (Function.update v τ (π τ h (v τ))) = rTr A (atTau θ A τ h) (Φ v)

def IsBesFormAt (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (M : DSModel B S) (τ : D.what₂.Tau) (N : ℕ)
    (L : Vt τ →ₗ[ℂ] M.sm τ →ₗ[ℂ] ℂ) : Prop :=
  (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∀ (a : Vt τ) (x w : M.sm τ),
      (w : M.H τ) = M.rep τ (infMat D.sp.cm.sig B.gram (θ τ) (s (atTau θ A τ h))) x → L (π τ h a) w = L a x) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ), atTau θ B τ g ∈ NFlag B d.e → ∀ (a : Vt τ) (x w : M.sm τ),
      (w : M.H τ) = M.rep τ g x → L a w = besChar ψ d (atTau θ B τ g) * L a x) ∧
    ∀ a : Vt τ, ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, SobContN (lieAt B τ) (M.rep τ) N ℓ ∧ ∀ w : M.sm τ, ℓ w = L a w

def LocUniqAt (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (M : DSModel B S) (τ : D.what₂.Tau) (N : ℕ) : Prop :=
  ∀ L₁ L₂ : Vt τ →ₗ[ℂ] M.sm τ →ₗ[ℂ] ℂ, IsBesFormAt θ ψ d s π M τ N L₁ → IsBesFormAt θ ψ d s π M τ N L₂ →
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • L₁ + b • L₂ = 0

open Classical in

def IsBesForm (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (M : DSModel B S) (N : ℕ)
    (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)) : Prop :=
  (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ), ∀ (v : ∀ τ, Vt τ) (x : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ (infMat D.sp.cm.sig B.gram (θ τ) (s (atTau θ A τ h))) (x τ) →
      ℓ (Function.update v τ (π τ h (v τ))) (Function.update x τ w) = ℓ v x) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ), atTau θ B τ g ∈ NFlag B d.e →
      ∀ (v : ∀ τ, Vt τ) (x : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (x τ) →
      ℓ v (Function.update x τ w) = besChar ψ d (atTau θ B τ g) * ℓ v x) ∧
    ∀ τ (v : ∀ τ, Vt τ) (x : M.Vec), ∃ L : M.H τ →ₗ[ℂ] ℂ, SobContN (lieAt B τ) (M.rep τ) N L ∧
      ∀ w : M.sm τ, L w = ℓ v (Function.update x τ w)

open Classical in

def UnifSob (M : DSModel B S) (N : ℕ) (T : MMap M) : Prop :=
  ∀ Ω : Set (GA D B), IsCompact Ω → ∀ τ (x : M.Vec),
    ∃ (L : List (List (Matrix (Fin B.rank) (Fin B.rank) ℂ))) (C : ℝ), (∀ l ∈ L, l.length ≤ N ∧ ∀ X ∈ l, X ∈ lieAt B τ) ∧
      ∀ g ∈ Ω, ∀ w : M.sm τ, ‖T (Function.update x τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum

def IsBesNum (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)) {M : DSModel B S}
    (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M)
    (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)) (Bn : ℂ) : Prop :=
  ∀ (v : ∀ τ, Vt τ) (x : M.Vec), IsBesPer ψ d s μ 𝓕 μN 𝓕N (Φ v) (T x) (ℓ v x * Bn)

end Vec

def ProdUniq : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B)
    (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S) (N : ℕ),
    (∀ τ, LocUniqAt θ ψ d s π M τ N) →
    ∀ ℓ₁ ℓ₂ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ),
      IsBesForm θ ψ d s π M N ℓ₁ → IsBesForm θ ψ d s π M N ℓ₂ → ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • ℓ₁ + b • ℓ₂ = 0

def BesFormOfPer : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)),
    IsInfFam θ → BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
      (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S)
      (J : Set (GA D B)) (χ : GA D B → ℂ) (N : ℕ) (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M),
      IsColMap θ π Φ → IsMultMap θ M J χ T → UnifSob M N T →
      ∃ ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ),
        IsBesForm θ ψ d s π M N ℓ ∧ ∀ v x, IsBesPer ψ d s μ 𝓕 μN 𝓕N (Φ v) (T x) (ℓ v x)

def BesNumExists : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)),
    IsInfFam θ → BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
      (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S)
      (J : Set (GA D B)) (χ : GA D B → ℂ) (N : ℕ) (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M)
      (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)),
      (∀ τ, LocUniqAt θ ψ d s π M τ N) → IsColMap θ π Φ → IsMultMap θ M J χ T → UnifSob M N T →
      IsBesForm θ ψ d s π M N ℓ → ℓ ≠ 0 → ∃! Bn, IsBesNum ψ d s μ 𝓕 μN 𝓕N Φ T ℓ Bn

def BesNumEqvU : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
      (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S)
      (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M)
      (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)),
      IsColMap θ π Φ → (∀ x, IsAutFun B (T x)) → ∀ (y' : GA D A) (Bn : ℂ),
      IsBesNum ψ d s μ 𝓕 μN 𝓕N Φ T ℓ Bn →
      IsBesNum ψ d s μ 𝓕 μN 𝓕N ((rTrLin A y').compMultilinearMap Φ)
        (postOn M (rTrLin B ((d.y : GA D B)⁻¹ * s y' * (d.y : GA D B))) T) ℓ Bn

def BesNumEqvN : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A →* GA D B) (μ : Measure (GA D A))
    (𝓕 : Set (GA D A)) (μN : Measure (NFlag B d.e)) (𝓕N : Set (NFlag B d.e)), BesStd ψ d s μ 𝓕 μN 𝓕N →
    ∀ (Vt : D.what₂.Tau → Type) [∀ τ, NormedAddCommGroup (Vt τ)] [∀ τ, InnerProductSpace ℂ (Vt τ)]
      (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → (Vt τ →L[ℂ] Vt τ)) (S : D.what₂.Tau → SPar) (M : DSModel B S)
      (Φ : MultilinearMap ℂ (fun τ => Vt τ) (GA D A → ℂ)) (T : MMap M)
      (ℓ : MultilinearMap ℂ (fun τ => Vt τ) (MultilinearMap ℂ (fun τ => M.sm τ) ℂ)),
      IsColMap θ π Φ → (∀ x, IsAutFun B (T x)) → ∀ (n₀ : NFlag B d.e) (Bn : ℂ),
      IsBesNum ψ d s μ 𝓕 μN 𝓕N Φ T ℓ Bn →
      IsBesNum ψ d s μ 𝓕 μN 𝓕N Φ (postOn M (rTrLin B ((d.y : GA D B)⁻¹ * (n₀ : GA D B) * (d.y : GA D B))) T) ℓ
        (besChar ψ d (n₀ : GA D B) * Bn)

end Formalism.IndefR.Mi

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.IterSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def embS (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (M : Mx D T.rank ρ) : WO S T :=
  HMul.hMul M ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))

def embP (S T : HSp D) {ρ : ℕ} (CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (M' : Mx D T.rank ρ) : WO S T :=
  HMul.hMul M' ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS' * S.gram).map (incA D))

def embQ (S T S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (x : WO S0 T) : WO S T :=
  HMul.hMul x ((S0.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) BS * S.gram).map (incA D))

def ellS (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (F : WO S T → ℂ) : ℂ :=
  ∫ M in 𝓕, F (embS S T CS M) ∂μ

def RedS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (F : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ellS S T CS μ 𝓕 (heisO ψ S T w F)

def descS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (S0 : HSp D)
    (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (f : WO S T → ℂ) : WO S0 T → ℂ :=
  fun x => RedS ψ S T CS μ 𝓕 f (embQ S T S0 BS x)

def IsDescSOf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om0 : GA D S0 × GA D T →* Module.End ℂ (WO S0 T → ℂ)) : Prop :=
  ∀ g0 g h, IsLeviEmb S CS CS' S0 BS g0 g → ∀ f, IsThetaFunO ψ S T f →
    descS ψ S T CS μ 𝓕 S0 BS (om (g, h) f) = om0 (g0, h) (descS ψ S T CS μ 𝓕 S0 BS f)

def DescSTheta (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ (ρ : ℕ) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
      (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E), IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S0 T (descS ψ S T CS μ 𝓕 S0 BS f)

def DescSWeil (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (ρ : ℕ) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
      (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E), IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
      ∃ om0 : GA D S0 × GA D T →* Module.End ℂ (WO S0 T → ℂ),
        IsWeilDatumO ψ S0 T χS χT om0 ∧ IsDescSOf ψ S T CS CS' S0 BS μ 𝓕 om om0

def ParabSN (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (ρ : ℕ) (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E), IsIsoFrame S CS →
      ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
        ∀ n ∈ NI S CS, ∀ f, IsThetaFunO ψ S T f → ∀ w,
          RedS ψ S T CS μ 𝓕 (om (n, 1) f) w = RedS ψ S T CS μ 𝓕 f (actO S T n⁻¹ 1 w)

def ParabSM1 (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (ρ : ℕ) (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E), IsIsoFrame S CS →
      ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
        ∀ g : GA D S, IsParI S CS g → ∀ (α : Fin ρ → D.host.E) (β : Fin ρ → AE D),
          ∑ i, β i * incA D (α i) = 0 →
          HMul.hMul (mt S g) (CS.map (incA D)) =
            HMul.hMul (CS.map (incA D)) (1 + Matrix.vecMulVec (fun i => incA D (α i)) β) →
          ∀ f, IsThetaFunO ψ S T f → ∀ w,
            RedS ψ S T CS μ 𝓕 (om (g, 1) f) w = RedS ψ S T CS μ 𝓕 f (actO S T g⁻¹ 1 w)

def MixedLawS (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (ρ : ℕ) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
      (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E), IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
      ∀ om0 : GA D S0 × GA D T →* Module.End ℂ (WO S0 T → ℂ), IsDescSOf ψ S T CS CS' S0 BS μ 𝓕 om om0 →
        ∀ g0 g h, IsLeviEmb S CS CS' S0 BS g0 g → ∀ f, IsThetaFunO ψ S T f →
          ∀ (M' : Mx D T.rank ρ) (x : WO S0 T),
            RedS ψ S T CS μ 𝓕 (om (g, h) f) (embP S T CS' M' + embQ S T S0 BS x) =
              om0 (g0, h) (fun x' => RedS ψ S T CS μ 𝓕 f
                (embP S T CS' (HMul.hMul (mt T h⁻¹) M') + embQ S T S0 BS x')) x

def HeisS (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ρ : ℕ)
    (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E), IsIsoFrame S CS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ (M : Mx D T.rank ρ) w,
        RedS ψ S T CS μ 𝓕 (heisO ψ S T (embS S T CS M) f) w =
          ψ (symplO S T w (embS S T CS M)) * RedS ψ S T CS μ 𝓕 f w

def RedInvS (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∀ (ρ : ℕ) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
      (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E), IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f →
        Summable (fun M' : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
          ‖RedS ψ S T CS μ 𝓕 (heisO ψ S T (embP S T CS' (M'.map (incA D))) f) 0‖) ∧
        ((μ 𝓕).toReal : ℂ) * f 0 =
          ∑' M' : Matrix (Fin T.rank) (Fin ρ) D.host.E,
            RedS ψ S T CS μ 𝓕 (heisO ψ S T (embP S T CS' (M'.map (incA D))) f) 0

def modelA (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r ρ : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (μS : Measure (Mx D T0.rank ρ)) (𝓕S : Set (Mx D T0.rank ρ)) (f : WO S T → ℂ)
    (k : Mx D r ρ) (z : WO S0 T0) : ℂ :=
  RedS ψ S T0 CS μS 𝓕S
    (fun x0 => Red ψ S T C μ 𝓕 f (embI S T C' (HMul.hMul k
      ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))) + embI S T B0 x0))
    (embQ S T0 S0 BS z)

def modelB (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r ρ : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μS' : Measure (Mx D T.rank ρ))
    (𝓕S' : Set (Mx D T.rank ρ)) (μ0 : Measure (Mx D r S0.rank)) (𝓕0 : Set (Mx D r S0.rank)) (f : WO S T → ℂ)
    (p : Mx D r ρ) (z : WO S0 T0) : ℂ :=
  Red ψ S0 T C μ0 𝓕0
    (fun x' => RedS ψ S T CS μS' 𝓕S' f (embP S T CS' (HMul.hMul (C.map (incA D)) p) + embQ S T S0 BS x'))
    (embI S0 T B0 z)

def TwoModel (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r ρ : ℕ)
    (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E),
    IsQuotFrame T C C' T0 B0 →
    ∀ (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E),
    IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → μ 𝓕 = 1 →
    ∀ (μS : Measure (Mx D T0.rank ρ)) (𝓕S : Set (Mx D T0.rank ρ)), μS.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T0.rank ρ) 𝓕S μS → μS 𝓕S = 1 →
    ∀ (μS' : Measure (Mx D T.rank ρ)) (𝓕S' : Set (Mx D T.rank ρ)), μS'.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T.rank ρ) 𝓕S' μS' → μS' 𝓕S' = 1 →
    ∀ (μ0 : Measure (Mx D r S0.rank)) (𝓕0 : Set (Mx D r S0.rank)), μ0.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S0.rank) 𝓕0 μ0 → μ0 𝓕0 = 1 →
    ∀ (ν : Measure (Mx D r ρ)) (𝓕ν : Set (Mx D r ρ)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r ρ) 𝓕ν ν → ν 𝓕ν = 1 →
    ∀ f, IsThetaFunO ψ S T f → ∀ (p : Mx D r ρ) (z : WO S0 T0),
      Integrable (fun k : Mx D r ρ =>
        ψ (symplO S T (embI S T C' (HMul.hMul k
            ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))))
          (embP S T CS' (HMul.hMul (C.map (incA D)) p))) *
        modelA ψ S T C C' T0 B0 CS S0 BS μ 𝓕 μS 𝓕S f k z) ν ∧
      modelB ψ S T C T0 B0 CS CS' S0 BS μS' 𝓕S' μ0 𝓕0 f p z =
        ∫ k, ψ (symplO S T (embI S T C' (HMul.hMul k
            ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))))
          (embP S T CS' (HMul.hMul (C.map (incA D)) p))) *
        modelA ψ S T C C' T0 B0 CS S0 BS μ 𝓕 μS 𝓕S f k z ∂ν

example (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) : IsDescSOf ψ S T CS CS' S0 BS μ 𝓕 1 1 := by
  intro g0 g h _ f _
  simp

end Formalism.IndefR.Mi

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def frame0 (i : ℕ) : Fin (D.sp.Y 0).rank → D.host.E :=
  if h : i < D.R.rS then (D.sp.Y 0).frame.repr (D.sp.hypE ⟨i, h⟩)
  else if i = D.R.rS then (D.sp.Y 0).frame.repr D.sp.zm
  else if h' : 2 * D.R.rS - i < D.R.rS then
    (D.sp.Y 0).frame.repr ((-(D.sp.T : D.host.E)) • D.sp.hypF ⟨2 * D.R.rS - i, h'⟩)
  else 0

open Classical in

def NormalFrame0 (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (S Pg : Finset (Pl D.host.E)) : Prop :=
  ∀ PP ∈ S, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
    (∀ i < D.R.m - 1, ∀ col : Fin (D.sp.Y 0).rank, col.val = D.R.N 0 + i →
      ColAt 0 βY0.val ei col fun r =>
        (if PP ∈ Pg then ((Ideal.absNorm PP.asIdeal : ℕ) : D.host.E) ^ (i + 1) else 1) * frame0 i r) ∧
    (∀ col : Fin (D.sp.Y 0).rank, col.val < D.R.N 0 → XSpanAt 0 βY0.val ei col)

def VertexAt (j : ℕ) (βY0 : GL (Fin (D.sp.Y 0).rank) (EAf D)) (βW : GL (Fin (D.sp.W j).rank) (EAf D))
    (e : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W j).rank)
    (ι : GL (Fin (D.sp.W j).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) : Prop :=
  (∀ k, (e k).val = k.val) ∧
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ι.val *
            (((D.sp.Y 0).gram.reindex e e).map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F))) *
            ι.val =
    (D.sp.W j).gram.map (Formalism.UG.inclE (Formalism.L2.Herm.Af D.host.F)) ∧
  ∀ PP ∈ Pg, ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP →
    IsIntM (toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (EAf D)).val.reindex e e * ι.val * βW.val)) ∧
      redM PP (toEAf D ei • ((βY0⁻¹ : GL (Fin (D.sp.Y 0).rank) (EAf D)).val.reindex e e * ι.val * βW.val)) = 1

end Formalism.IndefR.Mi

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NotRootUnity
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory IsDedekindDomain
  NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsUnifIdele (P : HeightOneSpectrum (𝓞 D.host.E)) (x : (AE D)ˣ) : Prop :=
  ∃ (e f : AE D) (ϖ : 𝓞 D.host.E), IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧
    (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)

def IsUnramAt (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ e f : AE D, IsPrimeIdem P e f ∧ ∀ x : (AE D)ˣ, (x : AE D) = e * (x : AE D) + (1 - e) →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

open Classical in

def chiAt (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) : ℂ :=
  if h : IsUnramAt χ P ∧ ∃ x, IsUnifIdele P x then ((χ h.2.choose : Circle) : ℂ) else 0

def normP (P : HeightOneSpectrum (𝓞 D.host.E)) : ℕ := Ideal.absNorm P.asIdeal

def lfac (χ : (AE D)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 D.host.E)) (s : ℂ) : ℂ :=
  (1 - chiAt χ P * (normP P : ℂ) ^ (-s))⁻¹

def lEuler (χ : (AE D)ˣ →* Circle) (s : ℂ) : ℂ := ∏' P : HeightOneSpectrum (𝓞 D.host.E), lfac χ P s

def satPoly (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (P : HeightOneSpectrum (𝓞 D.host.E)) (r : ℕ) :
    Polynomial ℂ :=
  ∑ k ∈ Finset.range (r + 1), Polynomial.monomial (r - k)
    ((-1 : ℂ) ^ k * ((normP P : ℝ) ^ (-((k * (r - k) : ℕ) : ℝ) / 2) : ℝ) * c P (splitLab r k))

def IsSplitPrime (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ e f : AE D, IsPrimeIdem P e f ∧ IsSplitIdem D e

def LfinHol (D : D7) : Prop :=
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a : (AF D.host.F)ˣ, χ (idF D a) = 1) → χ ≠ 1 →
    ∃ (L : ℂ → ℂ) (ε : ℝ), 0 < ε ∧ DifferentiableOn ℂ L {s | 1 - ε < s.re} ∧
      (∀ s : ℂ, 1 < s.re → Multipliable (fun P : HeightOneSpectrum (𝓞 D.host.E) => lfac χ P s) ∧
        L s = lEuler χ s) ∧
      ∀ n : ℕ, 1 ≤ n → (L n).im = 0 ∧ 0 < (L n).re

def SatakeBound (D : D7) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → SphOff J χ Sb →
    ∀ c ∈ IxFull θ M J χ Sb e, ∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D Sb P → IsSplitPrime P →
      ∀ α : ℂ, (satPoly c P V.rank).IsRoot α →
        (normP P : ℝ) ^ (-((V.rank : ℝ) - 1) / 2) ≤ ‖α‖ ∧ ‖α‖ ≤ (normP P : ℝ) ^ (((V.rank : ℝ) - 1) / 2)

def NotRootUnity (D : D7) : Prop :=
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a : (AF D.host.F)ˣ, χ (idF D a) = 1) →
    (∃ τ a, HasInfExp D χ τ a ∧ a ≠ 0) →
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), Nat.Prime (normP P) →
      ((normP P : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 →
      IsUnramAt χ P → ∀ n : ℕ, 0 < n → chiAt χ P ^ n ≠ 1

end Formalism.IndefR.Mi

end
end

