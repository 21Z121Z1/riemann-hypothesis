import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped TensorProduct

namespace GlobalTheory.ResW

def blkE {r s N : ℕ} (h : r + s = N) : Fin r ⊕ Fin s ≃ Fin N := finSumFinEquiv.trans (finCongr h)

def blkM (R : Type) [CommRing R] {r s N : ℕ} (h : r + s = N) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin s) (Fin s) R →* Matrix (Fin N) (Fin N) R where
  toFun p := Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blk {R : Type} [CommRing R] {r s N : ℕ} (h : r + s = N) : GL (Fin r) R × GL (Fin s) R →* GL (Fin N) R :=
  (Units.map (blkM R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N r s m a : ℕ}

variable (E) in

def nu (t : ℝ) : HChar E := GlobalTheory.HeckeGal.Model.absPow E t

variable (E N r) in

def ctData : @Measure (BlockIx N r → Ad E) (borel _) × Set (BlockIx N r → Ad E) :=
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  Classical.epsilon fun p : Measure (BlockIx N r → Ad E) × Set (BlockIx N r → Ad E) =>
    p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratN E N r) p.2 p.1 ∧ p.1 p.2 = 1

variable (r) in

def ct (f : GA E N → ℂ) (g : GA E N) : ℂ :=
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  ∫ x in (ctData E N r).2, f (unip x * g) ∂(ctData E N r).1

def cl (h : r + s = N) (φ : Sm E N) (p : GA E r × GA E s) : ℂ :=
  ct r φ.1 (blk h p) * ((chiDet r (nu E (-(s : ℝ) / 2)) p.1 : ℂˣ) : ℂ) * ((chiDet s (nu E ((r : ℝ) / 2)) p.2 : ℂˣ) : ℂ)

def evAt (g : GA E N) : Sm E N →ₗ[ℂ] ℂ := (LinearMap.proj g).comp (Sm E N).subtype

def ev2 (T : Sm E r ⊗[ℂ] Sm E s) (p : GA E r × GA E s) : ℂ :=
  TensorProduct.lid ℂ ℂ (TensorProduct.map (evAt p.1) (evAt p.2) T)

variable (E N) in

def Aut : Submodule ℂ (Sm E N) := Submodule.span ℂ {φ | IsAutForm φ}

variable (E N) in

def AutT (M : Type) [AddCommGroup M] [Module ℂ M] : Submodule ℂ (Sm E N ⊗[ℂ] M) :=
  Submodule.map₂ (TensorProduct.mk ℂ (Sm E N) M) (Aut E N) ⊤

def IsCTMap (h : r + s = N) (c : Sm E N →ₗ[ℂ] Sm E r ⊗[ℂ] Sm E s) : Prop :=
  ∀ φ, IsAutForm φ → c φ ∈ Submodule.map₂ (TensorProduct.mk ℂ (Sm E r) (Sm E s)) (Aut E r) (Aut E s) ∧
    ∀ p, ev2 (c φ) p = cl h φ p

def cT (h : r + s = N) : Sm E N →ₗ[ℂ] Sm E r ⊗[ℂ] Sm E s := Classical.epsilon (IsCTMap h)

def AutSp (V : Submodule ℂ (Sm E N)) : Prop := (∀ φ ∈ V, IsAutForm φ) ∧ IsStable V

section Passive

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def con (ℓ : M →ₗ[ℂ] ℂ) : Sm E r ⊗[ℂ] M →ₗ[ℂ] Sm E r :=
  (TensorProduct.rid ℂ (Sm E r)).toLinearMap ∘ₗ LinearMap.lTensor (Sm E r) ℓ

def sl (S : Submodule ℂ (Sm E r ⊗[ℂ] M)) : Submodule ℂ (Sm E r) := ⨆ ℓ : M →ₗ[ℂ] ℂ, S.map (con ℓ)

def Stab1 (S : Submodule ℂ (Sm E r ⊗[ℂ] M)) : Prop := ∀ o : Op E r, ∀ T ∈ S, LinearMap.rTensor M (act o) T ∈ S

def tp (W : Submodule ℂ (Sm E r)) (W' : Submodule ℂ M) : Submodule ℂ (Sm E r ⊗[ℂ] M) :=
  Submodule.map₂ (TensorProduct.mk ℂ (Sm E r) M) W W'

end Passive

def Stab2 (S : Submodule ℂ (Sm E r ⊗[ℂ] Sm E s)) : Prop := ∀ o : Op E s, ∀ T ∈ S, LinearMap.lTensor (Sm E r) (act o) T ∈ S

def slc (h : r + s = N) (g : GA E r) : Sm E N →ₗ[ℂ] Sm E s :=
  (TensorProduct.lid ℂ (Sm E s)).toLinearMap ∘ₗ LinearMap.rTensor (Sm E s) (evAt g) ∘ₗ cT h

variable (E) in

abbrev Letter : Type := Σ a : ℕ, CuspSub E a

def wsize (u : List (Letter E)) : ℕ := (u.map (·.1)).sum

noncomputable def Vec : List (Letter E) → Type
  | [] => PUnit
  | x :: u => x.2.V × Vec u

noncomputable def IsCT : (u : List (Letter E)) → Vec u → (N m : ℕ) → wsize u + m = N → Sm E m → Sm E N → Prop
  | [], _, _, _, _, ψ, φ => HEq ψ φ
  | x :: u, f, _, m, h, ψ, φ => ∀ g : GA E x.1, IsCT u f.2 (wsize u + m) m rfl (f.1.1.1 g • ψ)
      (slc (r := x.1) (s := wsize u + m) (by simpa [wsize, add_assoc] using h) g φ)

theorem IsCT.lin : ∀ (u : List (Letter E)) (f : Vec u) (N m : ℕ) (h : wsize u + m = N) (c : ℂ) (ψ ψ' : Sm E m)
    (φ φ' : Sm E N), IsCT u f N m h ψ φ → IsCT u f N m h ψ' φ' → IsCT u f N m h (c • ψ + ψ') (c • φ + φ')
  | [], _, N, m, h, c, ψ, ψ', φ, φ', h1, h2 => by
    obtain rfl : m = N := by simpa [wsize] using h
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    exact HEq.rfl
  | x :: u, f, N, m, h, c, ψ, ψ', φ, φ', h1, h2 => fun g => by
    have := IsCT.lin u f.2 _ m rfl c _ _ _ _ (h1 g) (h2 g)
    rwa [smul_comm c, ← smul_add, ← map_smul, ← map_add] at this

theorem IsCT.zero : ∀ (u : List (Letter E)) (f : Vec u) (N m : ℕ) (h : wsize u + m = N), IsCT u f N m h 0 0
  | [], _, N, m, h => by
    obtain rfl : m = N := by simpa [wsize] using h
    exact HEq.rfl
  | x :: u, f, N, m, h => fun g => by
    rw [smul_zero, map_zero]
    exact IsCT.zero u f.2 _ m rfl

def DerW (u : List (Letter E)) (h : wsize u + m = N) (V : Submodule ℂ (Sm E N)) : Submodule ℂ (Sm E m) where
  carrier := {ψ | ∀ f : Vec u, ∃ φ ∈ V, IsCT u f N m h ψ φ}
  add_mem' := fun {ψ ψ'} h1 h2 f => by
    obtain ⟨φ, a1, b1⟩ := h1 f
    obtain ⟨φ', a2, b2⟩ := h2 f
    exact ⟨φ + φ', add_mem a1 a2, by simpa using IsCT.lin u f N m h 1 _ _ _ _ b1 b2⟩
  zero_mem' := fun f => ⟨0, zero_mem _, IsCT.zero u f N m h⟩
  smul_mem' := fun c ψ h1 f => by
    obtain ⟨φ, a1, b1⟩ := h1 f
    exact ⟨c • φ, V.smul_mem c a1, by simpa using IsCT.lin u f N m h c _ _ _ _ b1 (IsCT.zero u f N m h)⟩

def Pos (u : List (Letter E)) : Prop := ∀ x ∈ u, 1 ≤ x.1

def HasWord (V : Submodule ℂ (Sm E N)) (u : List (Letter E)) : Prop :=
  Pos u ∧ ∃ h : wsize u + 0 = N, DerW u h V ≠ ⊥

def Wd (V : Submodule ℂ (Sm E N)) (X : List (Letter E)) : Prop := ∀ u, HasWord V u → u.Perm X

variable (E N) in

def zc : Module.End ℂ (Sm E N) := lie E N fun i j => if i = j then 1 else 0

def cex (x : Letter E) : ℂ := Classical.epsilon fun c : ℂ => ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ

def rexp (x : Letter E) : ℝ := (cex x).re / (x.1 * Module.finrank ℚ E)

def tw (x : Letter E) (t : ℝ) : Letter E := ⟨x.1, x.2.twist (nu E t)⟩

def upart (x : Letter E) : Letter E := tw x (-rexp x)

def IntDiff (u : List (Letter E)) : Prop := ∀ x ∈ u, ∀ y ∈ u, ∀ t : ℝ, y = tw x t → ∃ k : ℤ, t = k

def seg (x : Letter E) (d : ℕ) (c : ℝ) : List (Letter E) := List.ofFn fun i : Fin d => tw x (c - spehExp d i)

def IsExp (h : r + s = N) (V : Submodule ℂ (Sm E N)) (c : ℂ) : Prop :=
  ∃ T ∈ V.map (cT h), T ≠ 0 ∧ LinearMap.rTensor (Sm E s) (zc E r) T = c • T

def Neg (t : ℝ) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∀ (r s : ℕ) (h : r + s = N), 0 < r → 0 < s → ∀ c, IsExp h V c → c.re < r * Module.finrank ℚ E * t

def Ess (t : ℝ) (V : Submodule ℂ (Sm E N)) : Prop :=
  AutSp V ∧ (∃ c : ℂ, c.re = N * Module.finrank ℚ E * t ∧ ∀ φ ∈ V, zc E N φ = c • φ) ∧ Neg t V

def SatVec (φ : Sm E N) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop :=
  ∀ᶠ v in Filter.cofinite, GlobalTheory.LFun.IsSatVecGL v ((finRep E N).comp (locGL E N v)) φ (B v)

def SatFam (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop := ∀ φ ∈ V, φ ≠ 0 → SatVec φ B

def SatWord (u : List (Letter E)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) : Prop :=
  ∀ᶠ v in Filter.cofinite, ∃ C : Fin u.length → Multiset ℂˣ,
    (∀ i, (CG.mk (u.get i).2).HasSat v (C i)) ∧ ∑ i, C i = B v

def IsSquareIntegrableAutomorphicSpace (V : Submodule ℂ (Sm E N)) : Prop := AutSp V ∧ ∀ φ ∈ V, IsSqInt φ.1

variable (E N) in

def SegAt : Prop := ∀ (t : ℝ) (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (u : List (Letter E)),
  Ess t V → SatFam V B → HasWord V u → IntDiff u → ∃ (x : Letter E) (d : ℕ), 1 ≤ d ∧ rexp x = 0 ∧ u.Perm (seg x d t)

def IntInf (V : Submodule ℂ (Sm E N)) : Prop :=
  ∃ (τ : E →+* ℂ) (μ : Multiset ℂ), HasInfCharGL V τ μ ∧ ∀ z ∈ μ, ∀ z' ∈ μ, ∃ k : ℤ, z - z' = k

def SpehShape (V : Submodule ℂ (Sm E N)) {a : ℕ} (π : CuspSub E a) (d : ℕ) : Prop :=
  d * a = N ∧ π.IsUnitary ∧ IsNormalised π ∧ HasSpehComp V π d

def DiscSpehInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → ∀ V : Submodule ℂ (Sm E N),
    IsDiscrete V → IntInf V → ∃ (a d : ℕ) (π : CuspSub E a), SpehShape V π d

end GlobalTheory.ResW

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

section Coord

variable {R : Type} [CommRing R] {κ κ₁ : Type}

def ext0 (j : κ₁ → κ) (x : κ₁ → R) : κ → R := Function.extend j x 0

def ev (j : κ₁ → κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ) := LinearMap.funLeft ℂ ℂ (ext0 j)

variable [Fintype κ] [Fintype κ₁] {W W₁ : Type} [AddCommGroup W] [Module R W] [AddCommGroup W₁] [Module R W₁]
  {B : W → W → R} {B₁ : W₁ → W₁ → R}

def Over (j : κ₁ → κ) (d : Darboux B κ) (d₁ : Darboux B₁ κ₁) (v : W) (z : W₁) : Prop :=
  (d.e v).1 = ext0 j (d₁.e z).1 ∧ (d.e v).2 ∘ j = (d₁.e z).2

structure IsAct {G : Type} [Group G] (act : G → W → W) : Prop where
  one : ∀ w, act 1 w = w
  mul : ∀ g h w, act (g * h) w = act g (act h w)
  add : ∀ g w w', act g (w + w') = act g w + act g w'

end Coord

section Frame

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α α₁ ν : Type} [Fintype α] [DecidableEq α] [Fintype α₁] [DecidableEq α₁] [Fintype ν] [DecidableEq ν]

structure IsFrame (J : Matrix α α A) (C D : Matrix α ν A) (ι : Matrix α α₁ A) : Prop where
  cc : Cᵀ * J * C.map c = 0
  dd : Dᵀ * J * D.map c = 0
  cd : Cᵀ * J * D.map c = 1
  ic : ιᵀ * J * C.map c = 0
  ci : Cᵀ * J * ι.map c = 0
  id : ιᵀ * J * D.map c = 0
  di : Dᵀ * J * ι.map c = 0
  basis : ∃ M : Matrix ((ν ⊕ ν) ⊕ α₁) α A, Matrix.fromCols (Matrix.fromCols C D) ι * M = 1 ∧
    M * Matrix.fromCols (Matrix.fromCols C D) ι = 1

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def ratV {κ : Type} (ξ : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (ξ i)

def IsRat {α β κ : Type} [Fintype κ] {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) : Prop :=
  ∀ x : Matrix α β E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

structure IsInter (ψ : AddChar (AF F) ℂ) {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (d : Darboux B κ) (d' : Darboux B κ') (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ))
    (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ'
  pres' : ∀ φ ∈ schA F κ', S' φ ∈ schA F κ
  left : ∀ φ ∈ schA F κ, S' (S φ) = φ
  right : ∀ φ ∈ schA F κ', S (S' φ) = φ
  adm : ∀ l ∈ (adeleClass F).adm κ', l ∘ₗ S ∈ (adeleClass F).adm κ
  adm' : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S' ∈ (adeleClass F).adm κ'
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (d.rho ψ w φ) = d'.rho ψ w (S φ)
  theta : ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F κ, thetaSum F (S φ) = c * thetaSum F φ
  norm : ∀ (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

variable (σ : E →ₐ[F] E)

abbrev sy {n m : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin m) (Fin m) E) :
    Matrix (Fin n) (Fin m) (AE F E) → Matrix (Fin n) (Fin m) (AE F E) → AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)

def unipU {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (C : Matrix (Fin n) (Fin r) E) : Subgroup (UA σ J) :=
  Subgroup.closure {g | (mat g - 1) * incM F C = 0 ∧ (mat g - 1)ᵀ * incM F (J * C.map σ) = 0 ∧
    ∀ x : Fin n → E, x ᵥ* (J * C.map σ) = 0 →
      ∃ a : Fin r → AE F E, (mat g - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = incM F C *ᵥ a}

def IsCuspU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : UA σ J → ℂ) : Prop :=
  ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E), 0 < r → LinearIndependent E C.transpose → Cᵀ * J * C.map σ = 0 →
    ∀ (μ : Measure (unipU σ J C)) (𝓕 : Set (unipU σ J C)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ J).subgroupOf (unipU σ J C)) 𝓕 μ → ∀ g, ∫ u in 𝓕, f (u.1 * g) ∂μ = 0

structure IsMixL {n m n₁ r : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin m) (Fin m) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} (C D : Matrix (Fin n) (Fin r) E) (ι : Matrix (Fin n) (Fin n₁) E) {κ κ₁ : Type}
    [Fintype κ] [Fintype κ₁] (j : κ₁ → κ) (co : Darboux (sy σ JX JW) κ) (co₁ : Darboux (sy σ J₁ JW) κ₁) : Prop where
  frame : IsFrame σ JX C D ι
  gram : J₁ = ιᵀ * JX * ι.map σ
  inj : Function.Injective j
  rat : IsRat co
  rat₁ : IsRat co₁
  ovr : ∀ v z, Over j co co₁ v z ↔ ∃ y : Matrix (Fin r) (Fin m) (AE F E), v = incM F ι * z + incM F C * y
  dual : ∀ v, ((co.e v).2 = 0 ∧ (co.e v).1 ∘ j = 0) ↔ ∃ w : Matrix (Fin r) (Fin m) (AE F E), v = incM F D * w
  dualRat : ∀ ξ : κ → F, ξ ∘ j = 0 → ∃ w : Matrix (Fin r) (Fin m) E, co.e (incM F (D * w)) = (ratV F ξ, 0)

structure IsMixR {n m m₁ r : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin m) (Fin m) E}
    {J₁ : Matrix (Fin m₁) (Fin m₁) E} (C D : Matrix (Fin m) (Fin r) E) (ι : Matrix (Fin m) (Fin m₁) E) {κ κ₁ : Type}
    [Fintype κ] [Fintype κ₁] (j : κ₁ → κ) (co : Darboux (sy σ JX JW) κ) (co₁ : Darboux (sy σ JX J₁) κ₁) : Prop where
  frame : IsFrame σ JW C D ι
  gram : J₁ = ιᵀ * JW * ι.map σ
  inj : Function.Injective j
  rat : IsRat co
  rat₁ : IsRat co₁
  ovr : ∀ v z, Over j co co₁ v z ↔ ∃ y : Matrix (Fin n) (Fin r) (AE F E), v = z * (incM F ι)ᵀ + y * (incM F C)ᵀ

variable {σ}

def term (ψ : AddChar (AF F) ℂ) {n m r : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin m) (Fin m) E}
    (D : Matrix (Fin n) (Fin r) E) {κ κ₁ : Type} [Fintype κ] (j : κ₁ → κ) (co : Darboux (sy σ JX JW) κ)
    (w : Matrix (Fin r) (Fin m) E) (Φ : (κ → AF F) → ℂ) : ℂ :=
  thetaSum F (ev j (co.rho ψ (incM F (D * w)) Φ))

variable (σ) in

abbrev IsoRows {m : ℕ} (JW : Matrix (Fin m) (Fin m) E) (r : ℕ) : Type :=
  {w : Matrix (Fin r) (Fin m) E // w ≠ 0 ∧ w * JW * (w.map σ)ᵀ = 0}

example {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsFrame σ J (0 : Matrix (Fin n) (Fin 0) E) 0 (1 : Matrix (Fin n) (Fin n) E) := by
  refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _, Matrix.fromRows 0 1, ?_, ?_⟩
  · simp [Matrix.fromCols_mul_fromRows]
  · ext (a | a) (b | b)
    · rcases a with a | a <;> exact a.elim0
    · rcases a with a | a <;> exact a.elim0
    · rcases b with b | b <;> exact b.elim0
    · simp [Matrix.one_apply]

end GlobalTheory.TowU

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
section
namespace GlobalTheory.ThK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def KDecay : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → Decay B G om om'

def KConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → OneConst B G X om om' R Rf

def KCoinv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om' R Rf, IsMatched B G X om om' R Rf → Coinv B G X om om' Rf

def KBeta : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepBeta σ e₁ e₂ s

def KAlpha : Prop :=
  ∃ e₁ e₂ s : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    StepAlpha σ e₁ e₂ s

def KReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ R, IsRealMaps B G om om' R

def KFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∃ Rf, IsFinMaps B G X om om' Rf

theorem agree_of_parts (h1 : KDecay) (h2 : KConst) (h3 : KCoinv) (h4 : KBeta) (h5 : KAlpha) : ThetaIntegralsAgree :=
  ⟨fun F E _ _ _ _ _ σ B a a' G X om om' h => ⟨h1 F E σ B a a' G X om om' h,
    fun R Rf m => ⟨h2 F E σ B a a' G X om om' R Rf m, h3 F E σ B a a' G X om om' R Rf m⟩⟩, h4, h5⟩

theorem matching_of_parts (h1 : KReal) (h2 : KFin) : LocalMatching := fun F E _ _ _ _ _ σ B a a' G X om om' h =>
  let ⟨R, r⟩ := h1 F E σ B a a' G X om om' h
  let ⟨Rf, f⟩ := h2 F E σ B a a' G X om om' h
  ⟨R, Rf, h, r, f⟩

end GlobalTheory.ThK
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def SeesIrr (G : HTGroup p) (f : G.GAf → ℂ) : Prop :=
  ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h : G.GAf),
    f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 →
      Irreducible (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
        (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n

def CxCountIrr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (wt : Polynomial G.F → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    SeesIrr G f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      cxTotal G v wt L.K.toSubgroup f K' f' = fullSumIrr G wt L.K.toSubgroup f 1 K' f'

example (G : HTGroup p) (v wt Kf K' f') :
    cxTotal G v wt Kf (fun _ => 0) K' f' = fullSumIrr G wt Kf (fun _ => 0) 1 K' f' := by
  simp [cxTotal, cxSum, cxSumAt, fullSumIrr, Pair.term, Pair.termAt, pointSum]

example (G : HTGroup p) : SeesIrr G (fun _ => 0) := fun _ _ _ _ _ _ hf => absurd rfl hf

end GlobalTheory.LKCx
end
end

