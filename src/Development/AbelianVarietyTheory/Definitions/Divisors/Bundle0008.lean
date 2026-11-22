import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OneSubOfIsIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.TypeTwo

section General

variable {G Γ U W : Type} [Group G] [Group Γ] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

def OneSub (X : Representation ℂ G U) : Prop :=
  ∀ S T : Subrepresentation X, IsAtom S → IsAtom T → S = T

def eqMaps (ρ : Representation ℂ (G × Γ) U) (π : Representation ℂ Γ W) : Submodule ℂ (U →ₗ[ℂ] W) where
  carrier := {f | ∀ (h : Γ) (u : U), f (ρ (1, h) u) = π h (f u)}
  add_mem' := by
    intro f f' hf hf' h u
    simp only [LinearMap.add_apply, map_add, hf h u, hf' h u]
  zero_mem' := by intro h u; simp
  smul_mem' := by
    intro c f hf h u
    simp only [LinearMap.smul_apply, map_smul, hf h u]

def homAct (ρ : Representation ℂ (G × Γ) U) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ G (U →ₗ[ℂ] W) where
  toFun g := LinearMap.lcomp ℂ W (ρ (g⁻¹, 1))
  map_one' := by
    ext f u
    show f (ρ ((1 : G)⁻¹, 1) u) = f u
    rw [inv_one, ← Prod.one_eq_mk, map_one]; rfl
  map_mul' a b := by
    ext f u
    show f (ρ ((a * b)⁻¹, 1) u) = f (ρ (b⁻¹, 1) (ρ (a⁻¹, 1) u))
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_rev]

def eqRep (ρ : Representation ℂ (G × Γ) U) (π : Representation ℂ Γ W) : Representation ℂ G (eqMaps ρ π) :=
  sub (homAct ρ W) (eqMaps ρ π) (by
    intro g f hf h u
    show f (ρ (g⁻¹, 1) (ρ (1, h) u)) = π h (f (ρ (g⁻¹, 1) u))
    rw [← hf h, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp)

variable [TopologicalSpace G] [IsTopologicalGroup G]

def homRep (ρ : Representation ℂ (G × Γ) U) (π : Representation ℂ Γ W) :
    Representation ℂ G (smoothPart (eqRep ρ π)) := smoothRep (eqRep ρ π)

end General

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rkSB (n m j : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) where
  carrier := {Φ | Φ ∈ SB (Matrix (Fin n) (Fin m) k) ∧ ∀ x : Matrix (Fin n) (Fin m) k, x.rank < j → Φ x = 0}
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun x hx => by simp [ha.2 x hx, hb.2 x hx]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun x hx => by simp [hf.2 x hx]⟩

def omAll (n m : ℕ) : Representation ℂ (GL (Fin m) k × GL (Fin n) k) (Matrix (Fin n) (Fin m) k → ℂ) where
  toFun p :=
    { toFun := fun Φ => om 1 p.1 p.2 Φ
      map_add' := fun Φ Ψ => by funext x; simp only [om, Pi.add_apply]; ring
      map_smul' := fun c Φ => by funext x; simp only [om, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := by
    ext Φ x
    simp [om, nabs]
  map_mul' a b := by
    ext Φ x
    have h1 := fun (s : ℝ) (u v : kˣ) => Real.mul_rpow (z := s) (nabs_pos' k u).le (nabs_pos' k v).le
    simp only [om, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, Prod.fst_mul, Prod.snd_mul, map_mul,
      nabs_mul', h1, MonoidHom.one_apply, inv_one, Units.val_one, mul_one, one_mul, mul_inv_rev, Units.val_mul,
      Matrix.mul_assoc, Complex.ofReal_mul]
    ring

def omRk (n m j : ℕ) : Representation ℂ (GL (Fin m) k × GL (Fin n) k) (rkSB k n m j) :=
  sub (omAll k n m) (rkSB k n m j) (by
    intro p Φ hΦ
    refine ⟨Model.om_mem_SB 1 p.1 p.2 hΦ.1, fun x hx => ?_⟩
    have hr : ((p.2⁻¹ : GL (Fin n) k).val * x * p.1.val).rank < j :=
      lt_of_le_of_lt ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)) hx
    show om 1 p.1 p.2 Φ x = 0
    simp only [om, hΦ.2 _ hr, mul_zero])

variable {k}
variable {W : Type} [AddCommGroup W] [Module ℂ W]

abbrev thetaHom {n : ℕ} (m j : ℕ) (π : Representation ℂ (GL (Fin n) k) W) := homRep (omRk k n m j) π

def rkStep {n : ℕ} (m : ℕ) (π : Representation ℂ (GL (Fin n) k) W) (j : ℕ) :
    Subrepresentation (thetaHom m 0 π) where
  toSubmodule :=
    { carrier := {f | ∀ Φ : rkSB k n m 0, Φ.1 ∈ rkSB k n m j → f.1.1 Φ = 0}
      add_mem' := fun {a b} ha hb Φ hΦ => by
        show a.1.1 Φ + b.1.1 Φ = 0
        rw [ha Φ hΦ, hb Φ hΦ, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c f hf Φ hΦ => by
        show c • f.1.1 Φ = 0
        rw [hf Φ hΦ, smul_zero] }
  apply_mem_toSubmodule g f hf Φ hΦ := hf _ (omRk k n m j (g⁻¹, 1) ⟨Φ.1, hΦ⟩).2

def RChar {N : ℕ} (X : Representation ℂ (GL (Fin N) k) W) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (b : ℕ) (h : b + 1 = N) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
    (σ : Representation ℂ (GL (Fin b) k × GL (Fin 1) k) Y),
    σ.IsIrreducible ∧ IsSubquotient σ (jac₂ (stdSum h) X) ∧
      ∀ (g : GL (Fin 1) k) (y : Y), σ (1, g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y

def LChar {N : ℕ} (X : Representation ℂ (GL (Fin N) k) W) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (b : ℕ) (h : 1 + b = N) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
    (σ : Representation ℂ (GL (Fin 1) k × GL (Fin b) k) Y),
    σ.IsIrreducible ∧ IsSubquotient σ (jac₂ (stdSum h) X) ∧
      ∀ (g : GL (Fin 1) k) (y : Y), σ (g, 1) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y

abbrev powChar (a : ℕ) (χ : kˣ →* ℂˣ) := prinSeries (fun _ : Fin a => χ)

abbrev prodAt {r t N : ℕ} (h : r + t = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W) :=
  ind₂ (stdSum h) (extTensor A B)

def Embeds {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (A : Representation ℂ G V)
    (B : Representation ℂ G W) : Prop := ∃ f : A.IntertwiningMap B, Function.Injective f

variable (k) in

def PowIrr : Prop := ∀ (a : ℕ) (χ : kˣ →* ℂˣ), IsSmoothChar χ → (powChar a χ).IsIrreducible

end GlobalTheory.TypeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

def Loc (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

abbrev sgl (F : Shv R) : Cx R := (CochainComplex.singleFunctor (Shv R) 0).obj F

def sglι (F : Shv R) : F ⟶ (sgl F).X 0 := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv

def resAug (F : Shv R) : sgl F ⟶ res R F := (injectiveResolution F).ι'

abbrev cpull {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) : CohomologyClass L I n →+ CohomologyClass K I n :=
  cpre (Cocycle.ofHom f) I n n (zero_add n)

abbrev cpush (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ) : CohomologyClass K I n →+ CohomologyClass K J n :=
  cpost K (Cocycle.ofHom f) n n (add_zero n)

def Sx.face {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) : Sx E p U := (E.δ i).app (op U) x

def Sx.along {E : Spc} {p N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : Sx E p U :=
  (E.map θ.op).app (op U) x

def Sx.res {E : Spc} {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) : Sx E p V := (E.obj (op (SimplexCategory.mk p))).map g.op x

def Sx.map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : Sx E' p U :=
  (f.app (op (SimplexCategory.mk p))).app (op U) x

abbrev Tens (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Type 1 :=
  ⨁ p : {p : ℤ × ℤ // p.1 + p.2 = w}, (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)

def Tens.res {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J V w :=
  DirectSum.lmap fun p => TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom

def Pair.lift {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec (K.X w) U := by
  classical
  exact DirectSum.toModule _ _ _ fun p => TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2)

def Pair.IsTensor {I J K : Cx R} (μ : Pair I J K) : Prop :=
  (∀ (U : Scheme.{0}) (w : ℤ) (y : Sec (K.X w) U), Loc U fun V g => ∃ x, μ.lift V w x = Sec.res g y) ∧
  ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), μ.lift U w x = 0 → Loc U fun _ g => Tens.res g w x = 0

def Pair.Compat {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (m : K ⟶ K') : Prop :=
  ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (m.f w) (μ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

def Pair.IsFlip {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K) : Prop :=
  ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    ν.mul U t s w (by omega) b a = (s * t).negOnePow • μ.mul U s t w h a b

def FlatS (M : Shv R) : Prop :=
  ∃ (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧
    ∀ U : Scheme.{0}, Nonempty U → Module.Flat (ULift.{1} R) (P.obj (op U))

def IsTwRes (q : ℕ) (i : ℤ) (T : Cx (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U) : Prop :=
  T.IsStrictlyGE 0 ∧ ∃ ε : sgl (tw q i) ⟶ T, QuasiIso ε ∧
    ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map (ε.f 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) = e U ζ

def unitSec {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : Sec Gm U := ofRings.sec unitsF U (ULift.up (Additive.ofMul u))

def secClass (F : Shv R) {X : Scheme.{0}} (s : Sec F X) : H R (sch.obj X) F 0 :=
  pick fun c => ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s

def picClass {E : Spc} (L : E ⟶ ofCat (glCat 1)) : H ℤ E Gm 1 :=
  pick fun c => ∃ γ : Cocycle _ _ 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x))

def SemiMap.IsImage {S : Type} [CommRing S] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    (α : Cochain ((chains S).obj E) I n) (β : Cochain ((chains R).obj E) J n) : Prop :=
  ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β p s h U x = ρ.app U s (ev α p s h U x)

abbrev Pr (N : ℕ) : Type := Σ p r : ℕ, (SimplexCategory.mk p ⟶ SimplexCategory.mk N) × (SimplexCategory.mk r ⟶ SimplexCategory.mk N)

def Pr.push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr M →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ fun z => ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩

def Pr.d₁ {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Nat.casesOn (motive := fun p => (SimplexCategory.mk p ⟶ SimplexCategory.mk N) → (Pr N →₀ ℤ)) z.1 (fun _ => 0)
    (fun p a => ∑ i : Fin (p + 2), Finsupp.single ⟨p, z.2.1, SimplexCategory.δ i ≫ a, z.2.2.2⟩ ((-1) ^ (i : ℕ))) z.2.2.1

def Pr.d₂ {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Nat.casesOn (motive := fun r => (SimplexCategory.mk r ⟶ SimplexCategory.mk N) → (Pr N →₀ ℤ)) z.2.1 (fun _ => 0)
    (fun r b => ∑ j : Fin (r + 2), Finsupp.single ⟨z.1, r, z.2.2.1, SimplexCategory.δ j ≫ b⟩ ((-1) ^ (j : ℕ))) z.2.2.2

def Pr.d (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ fun z => z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂

def Pr.aw (N : ℕ) : Pr N →₀ ℤ := ∑ p : Fin (N + 1), Finsupp.single
  ⟨p, N - p, SimplexCategory.subinterval 0 p (by omega), SimplexCategory.subinterval p (N - p) (by omega)⟩ 1

def Pr.wa (N : ℕ) : Pr N →₀ ℤ := ∑ p : Fin (N + 1), Finsupp.single
  ⟨N - p, p, SimplexCategory.subinterval p (N - p) (by omega), SimplexCategory.subinterval 0 p (by omega)⟩ ((-1) ^ ((p : ℕ) * (N - p)))

def Pr.Deg {N : ℕ} (k : ℕ) (c : Pr N →₀ ℤ) : Prop := ∀ z ∈ c.support, z.1 + z.2.1 = k

def Pr.bd {N : ℕ} (c : Pr N →₀ ℤ) : Pr (N + 1) →₀ ℤ := ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • Pr.push (SimplexCategory.δ i) c

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
section
noncomputable section

open MeasureTheory Matrix
open scoped Topology Classical

namespace GlobalTheory.KSp

open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitUnitary

section Abstract

structure Good (X : Type) [AddCommGroup X] [TopologicalSpace X] : Prop where
  grp : IsTopologicalAddGroup X
  t2 : T2Space X
  lc : LocallyCompactSpace X
  sc : SecondCountableTopology X
  large : ∀ K : Set X, IsCompact K → ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ K ⊆ L
  small : ∀ U ∈ 𝓝 (0 : X), ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ (L : Set X) ⊆ U

variable {X : Type} [AddCommGroup X] [TopologicalSpace X]

structure IsPair (e : X → X → ℂ) : Prop where
  add : ∀ x x' y, e (x + x') y = e x y * e x' y
  symm : ∀ x y, e x y = e y x
  norm : ∀ x y, ‖e x y‖ = 1
  lc : IsLocallyConstant fun p : X × X => e p.1 p.2
  small : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ K, e x y = 1) → y ∈ U
  big : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ U, e x y = 1) → y ∈ K

variable [MeasurableSpace X]

def four (μ : Measure X) (e : X → X → ℂ) (φ : X → ℂ) : X → ℂ := fun x => ∫ y, e x y * φ y ∂μ

def HasGauss (μ : Measure X) (f : X → ℂ) (γ : ℂ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ K ⊆ L ∧
    ∫ x in (L : Set X), f x ∂μ = γ

end Abstract

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def sgn (E : Type) [Field E] [Algebra F E] (t : Fˣ) : ℂ :=
  if t ∈ (Units.map (Algebra.norm F : E →* F)).range then 1 else -1

def pr (Q : Matrix α α E) (x y : Matrix α ν E) : F := form c Q (fromCols x 0) (fromCols 0 y)

def weyl (ν : Type) [Fintype ν] [DecidableEq ν] : UG c (stdJ ν E) :=
  ⟨⟨stdJ ν E, -stdJ ν E, by rw [Matrix.mul_neg, stdJ_mul_stdJ, neg_neg], by rw [Matrix.neg_mul, stdJ_mul_stdJ, neg_neg]⟩, by
    rw [mem_UG_iff]
    have h : ((stdJ ν E).map c)ᵀ = -stdJ ν E := by
      ext (i | i) (j | j) <;> simp [stdJ, one_apply, eq_comm]
    change stdJ ν E * stdJ ν E * ((stdJ ν E).map c)ᵀ = stdJ ν E
    rw [h, stdJ_mul_stdJ]
    simp⟩

theorem weyl_val : ((weyl c ν : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = stdJ ν E := rfl

def unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : UG c (stdJ ν E) :=
  ⟨⟨fromBlocks 1 b 0 1, fromBlocks 1 (-b) 0 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
    rw [mem_UG_iff]
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
    simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h1, hb]⟩

theorem unip_val (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    ((unip c b hb : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = fromBlocks 1 b 0 1 := rfl

abbrev mat (g : UG c (stdJ ν E)) : Matrix (ν ⊕ ν) (ν ⊕ ν) E := ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)

theorem mat_inv (g : UG c (stdJ ν E)) : mat c g⁻¹ = -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) := by
  have hg : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c (g : GL (ν ⊕ ν) E)).1 g.2
  have hr : mat c g * -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) = 1 := by
    rw [Matrix.mul_neg, ← mul_assoc, ← mul_assoc, hg, stdJ_mul_stdJ, neg_neg]
  have hl : mat c g⁻¹ * mat c g = 1 := by
    simp [mat]
  calc mat c g⁻¹ = mat c g⁻¹ * (mat c g * -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E)) := by
        rw [hr, mul_one]
    _ = -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) := by
        rw [← mul_assoc, hl, one_mul]

def sieg (ν : Type) [Fintype ν] [DecidableEq ν] : Subgroup (UG c (stdJ ν E)) where
  carrier := {g | (mat c g).toBlocks₂₁ = 0}
  one_mem' := by
    ext i j
    simp [mat, toBlocks₂₁]
  mul_mem' := by
    intro g h hg hh
    change (mat c g * mat c h).toBlocks₂₁ = 0
    rw [← fromBlocks_toBlocks (mat c g), ← fromBlocks_toBlocks (mat c h), fromBlocks_multiply, toBlocks_fromBlocks₂₁,
      show (mat c g).toBlocks₂₁ = 0 from hg, show (mat c h).toBlocks₂₁ = 0 from hh]
    simp
  inv_mem' := by
    intro g hg
    change (mat c g⁻¹).toBlocks₂₁ = 0
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    rw [mat_inv, ← fromBlocks_toBlocks (mat c g), show (mat c g).toBlocks₂₁ = 0 from hg]
    simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg, h0]

theorem mem_sieg {g : UG c (stdJ ν E)} : g ∈ sieg c ν ↔ (mat c g).toBlocks₂₁ = 0 := by
  exact Iff.rfl

def InCell (g : UG c (stdJ ν E)) : Prop := ∃ p ∈ sieg c ν, ∃ q ∈ sieg c ν, g = p * weyl c ν * q

end Group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def sc (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : E) : ℂ :=
  if h : z = 0 then 0 else (χ (Units.mk0 z h) : ℂ) *
    ((nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z h)) ^ ((m : ℝ) / 2) : ℝ) : ℂ)

def parFun (ψ : AddChar F ℂ) (χ : Eˣ →* Circle) (Q : Matrix α α E) (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  fun x => sc F χ (Fintype.card α) g.toBlocks₁₁.det *
    (ψ (2⁻¹ * pr c Q (x * g.toBlocks₁₁) (x * g.toBlocks₁₂)) * φ (x * g.toBlocks₁₁))

def fou [TopologicalSpace E] [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ) (Q : Matrix α α E)
    (μ : Measure (Matrix α ν E)) (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  four μ (fun x y => ψ (pr c Q x y)) φ

structure IsKW [TopologicalSpace E] [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ) (χ : Eˣ →* Circle)
    (Q : Matrix α α E) (μ : Measure (Matrix α ν E)) (κ : ℂ)
    (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))) : Prop where
  par : ∀ p ∈ sieg c ν, ∀ φ : SB (Matrix α ν E), (ω p φ : Matrix α ν E → ℂ) = parFun c ψ χ Q (mat c p) φ
  wey : ∀ φ : SB (Matrix α ν E), (ω (weyl c ν) φ : Matrix α ν E → ℂ) = κ • fou c ψ Q μ φ

end Local

end GlobalTheory.KSp

end
end

