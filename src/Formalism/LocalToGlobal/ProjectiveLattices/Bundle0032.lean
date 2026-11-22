import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def CUnit (c : Comp → ℂ) : Prop := ∀ k, ‖c k‖ = 1

def muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) : GA D V → ℂ :=
  fun g => c (dict g).1 * mu g

theorem adel_muPin (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) (P : FDSec X) (g : GA D V) :
    adel V dict (muPin V dict mu c) P g = c (dict g).1 * mu g * P (dict g).1 (dict g).2 := rfl

def MuVal (V : HSp D) (χ : (AE D)ˣ →* Circle) (mu : GA D V → ℂ) : Prop :=
  (∀ g, ∃ x, IsDetRoot V g x) ∧ ∀ g x, IsDetRoot V g x → mu g = ((χ x : Circle) : ℂ)

theorem MuVal.norm {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) (g : GA D V) :
    ‖mu g‖ = 1 := by
  obtain ⟨x, hx⟩ := h.1 g
  rw [h.2 g x hx]
  first
    | exact Circle.norm_coe _
    | exact Circle.abs_coe _
    | exact mem_sphere_zero_iff_norm.mp (χ x).2

def muRec {X : ThetaX D} (T : ThetaTied D X) (μ : D.what₂.Tup) (j : ℕ) : (AE D)ˣ →* Circle :=
  T.eChr (X.chrOf μ j)

def muRec0 {X : ThetaX D} (T : ThetaTied D X) (j : ℕ) : (AE D)ˣ →* Circle := muRec T D.what₂.mu0 j

def FinUnit (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D

def MuConj {K : Type} [Field K] (σ₀ σ : K →+* ℂ) (χ₀ χσ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x, FinUnit x → ∃ y : K, ((χ₀ x : Circle) : ℂ) = σ₀ y ∧ ((χσ x : Circle) : ℂ) = σ y

def CEquiv (V : HSp D) {K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C] [Module K C]
    {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ k, Frame (X k).Ψ r) (mu : GA D V → ℂ)
    (c : Comp → ℂ) {G0 : Type} [Group G0] (ρ : G0 →* (C →ₗ[K] C)) (chi : G0 →* Kˣ) (ℓ : G0 → GA D V) : Prop :=
  (∃ c' : Comp → ℂ, CUnit c' ∧ EquivariantFiniteGroup V σ rd dict (muPin V dict mu c') ρ chi ℓ) →
    EquivariantFiniteGroup V σ rd dict (muPin V dict mu c) ρ chi ℓ

end Char

section Dict

variable {D : D7}

def finVec (V : HSp D) (v : Fin V.rank → D.host.E) : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => (1 : Af D.host.F) ⊗ₜ v i

def gLat (V : HSp D) (g : GA D V) : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  (finHom V g).1.mulVec '' (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E))

def latG (V : HSp D) (g : GA D V) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v, finVec V v ∈ gLat V g ∧ w = a • v}

def latGHat (V : HSp D) (g : GA D V) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ z ∈ gLat V g,
    w = fun i => ((1 : Af D.host.F) ⊗ₜ a) * z i}

def LatEmb (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latG V 1

def LatIsom (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))

def ModelW (V : HSp D) {r : ℕ} (hr : V.rank = r) (X : Data D.host.E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose ∧ X.ξ0 = -D.host.xi0

def IsOrthogonalFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

open Classical in

def DictLat (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → D.host.E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → D.host.E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : GA D V, ∃ γ ∈ GQ V,
      ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (γ * h)) * x₀ τ.1

end Dict

structure CoreJ (D : D7) : Type 1 extends Core D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)

namespace CoreJ

variable {D : D7} (T : CoreJ D)

def phiJ (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : GA D (T.V j σ) → ℂ :=
  (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
    adel (T.V j σ) (T.dict j σ) (muPin (T.V j σ) (T.dict j σ) (T.mu j σ) (T.cE j σ)) (rdU (T.U j σ) f)

theorem phiJ_apply (j : ℕ) (σ : T.Q.c.F →+* ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D (T.V j σ)) :
    T.phiJ j σ a f g = T.cE j σ (T.dict j σ g).1 * T.toCore.phiAd j σ a f g := by
  have h1 : adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) g =
      T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2 := rfl
  simp only [phiJ, Core.phiAd, Pi.smul_apply, smul_eq_mul, adel_muPin, h1]
  ring

end CoreJ

def halfVec {D : D7} (V : HSp D) (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i => ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * z i

def KfHalf {D : D7} (V : HSp D) (Kf : Subgroup (GA D V)) (M : ℕ) (Mh : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ ∀ b ∈ Mh, ∀ z ∈ latHat V, ∃ y ∈ latHat V,
    (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = M • y

def AdPin {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (ι₀ : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) : Prop :=
  ∃ (hr : (T.V j σ).rank = D.R.r)
    (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
    (F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => relab T.Q.c σ (e i).1))
    (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
    (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    LatEmb (T.V j σ) ι ∧ LatIsom (T.V j σ) (T.Q.Dw j).EF ι ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictLat (T.U j σ) (T.V j σ) hr (T.dict j σ) ι e F ik φ th x₀

structure LawsJ {D : D7} (T : CoreJ D) : Prop extends LawsM T.toCore where

  cUnit : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (T.cE j σ)

  muVal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuVal (T.V j σ) (T.chiW j σ) (T.mu j σ)

  muConj : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → MuConj T.σ₀ σ (T.chiW j T.σ₀) (T.chiW j σ)

  intAll : ∀ j, InR D j → IntAll (T.Q.Xo j) T.Q.c

  modelW : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∃ hr : (T.V j σ).rank = D.R.r,
    ∀ k, ModelW (T.V j σ) hr ((T.U j σ).X k)

  familyUniformisationBasePointOrthogonal : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (T.x₀ j σ)

  kfHalf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    KfHalf (T.V j σ) (T.Kf j σ) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

  adPin : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → AdPin T.toCore j σ (T.x₀ j σ) (T.iota j)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.DIV.Cons
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Top (D : D7) : Type 1 extends Core D where
  G : In66 Q
  nab : ∀ j, NabV (Q.Xo j) Q.c
  dδ : ∀ j n, DeltaDat (Q.Xo j) Q.c n

variable {D : D7}

def badN (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d * ∏ p ∈ D.host.levelPrimes, p

def wEt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

structure LawsP (T : Top D) : Prop extends LawsCore T.toCore where

  allTest : ∀ j, InR D j → AllTest (T.Q.Xo j) T.Q.c

  reg : ∀ j, InR D j → regular₂ (T.Q.Xo j) T.Q.c (T.U j)

  datum_condition : T.G.PinDat
  tower : T.G.PinTower
  hasData_condition : T.G.HasData
  points_condition : T.G.PinPts
  lattice_condition : T.G.PinLat
  bc66 : T.G.BaseChange

  datIndep : ∀ j, 1 ≤ j → j < D.R.m → DatIndep (T.Q.Xo j) T.Q.c

  nabPin : ∀ j, InR D j → ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c (T.nab j)

  nabUniq : ∀ j, InR D j → NabUniq (T.Q.Xo j) T.Q.c

  thTot : ∀ j, InR D j → ThValTot (T.Q.Xo j) T.Q.c (T.nab j)
  thCusp : ∀ j, InR D j → ThInCusp (T.Q.Xo j) T.Q.c (T.nab j) (T.cuspA j)
  thNe : ∀ j, 1 ≤ j → j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c (T.nab j)

  kPsi : ∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c

structure LawsSh (T : Top D) : Prop where
  beta : ∀ j, InR D j → ∀ n, BetaExists (Dw := T.Q.Dw j) T.Q.c n (badN D)
  dLev : ∀ j, InR D j → ∀ n, (T.dδ j n).IsLev
  dNab : ∀ j, InR D j → ∀ n, ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂

  dPd : ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p

  dPhi : ∀ j, InR D j → ∀ n, D.R.r ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ

  dRoot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* (T.dδ j n).c₂.Fˣ)
    (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
    CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false
  shTot : ∀ j, InR D j → ∀ a n, Dom a n →
    ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)
  shCusp : ∀ j, InR D j → ∀ a n, Dom a n → LastPos (T.Q.Dw j) a →
    ShortInCusp (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.cuspA j) a n (T.dδ j n)
  shNe : ∀ j, 1 ≤ j → j < D.R.m → ShortNe0 (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.dδ j) (T.cuspA j)

def Packet66Rest (Q : Par D) : Prop :=
  ∃ G : In66 Q, G.PinDat ∧ G.PinTower ∧ G.HasData ∧ G.PinPts ∧ G.PinLat ∧ G.BaseChange

theorem LawsP.packet66_rest {T : Top D} (h : LawsP T) : Packet66Rest T.Q :=
  ⟨T.G, h.datum_condition, h.tower, h.hasData_condition, h.points_condition, h.lattice_condition, h.bc66⟩

def TopExists (D : D7) : Prop := ∃ T : Top D, LawsP T

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HeightF1OfData
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem extVal_unit_zero (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    apply le_antisymm ((IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one _)
    have h2 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (R := T.V) (K := T.Fr) ((u⁻¹ : T.Vˣ) : T.V)
    have h3 : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    by_contra hlt
    rw [not_le] at hlt
    have : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this
    exact lt_irrefl _ this
  simp [vV, h1]

def OrdTieQZ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 → ordQ Xo c q f = ⊤

theorem height_F1_of_data (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU)
    (hreg : regular₂ Xo c U) (htie : OrdTieQZ h δ)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2)
    (hws : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2) (het : etR ∈ cusp Xo c U uet.1 uet.2)
    (hnz : NoCommonZero Xo c wR) (hnzet : NZAt h etR)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (nuA : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (halg : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v etR ∧
      (v etR ≠ ⊤ → (⨅ k, v (wR k)) ≤ (nuA la : EReal) + ((cc / (2 * i) : ℝ) : EReal) * v etR)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp := by
  classical
  have hc' : (0 : ℝ) ≤ cc / (2 * i) := div_nonneg hcc (by positivity)

  have hR2 := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hws k⟩) ⟨etR, het⟩ nuA (cc / (2 * i)) hc'
    hnz (fun la y => halg la y.1 y.2)).2
  unfold Data.TrivialPlaceHyp
  intro Z v hAdm hTv
  obtain ⟨q, hq1, hq0⟩ := htie Z v hAdm.1 hTv

  have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
    refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
    obtain ⟨u, hu⟩ := q.triv a ha
    rw [← hu]
    exact extVal_unit_zero q.T u
  obtain ⟨hE0, hEb⟩ := hR2 ⟨_, hqT⟩
  dsimp only [dataOf, Data.n1] at *
  rw [← huet]
  have hEq : (((ordC (δ Z v) v (wtZ uet.1 uet.2) (valC h uet.1 uet.2 etR Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q etR :=
    hq1 uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ het) (hnzet Z)
  have hEne : ordQ Xo c q etR ≠ ⊤ := by rw [← hEq]; exact EReal.coe_ne_top _
  have hb := hEb hEne
  obtain ⟨k0, hk0⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin (N + 1) => ordQ Xo c q (wR k))
  have hk0le : ordQ Xo c q (wR k0) ≤ ((cc / (2 * i) : ℝ) : EReal) * ordQ Xo c q etR := by
    rw [hk0]; exact hb
  have hev : evC h Z (wR k0) ≠ 0 := by
    intro h0
    rw [hq0 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) h0, ← hEq, ← EReal.coe_mul] at hk0le
    exact EReal.coe_ne_top _ (top_le_iff.1 hk0le)
  have hval : valC h uL.1 uL.2 (wR k0) Z ≠ 0 := valC_ne_zero hev
  have hk0' := hq1 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) hev
  rw [← hk0', ← hEq, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hk0le
  have hle : (⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) ≤
      ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) :=
    ciInf_le (Set.finite_range _).bddBelow (⟨k0, hval⟩ : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0})
  have hle' : ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2)
      (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) := by
    exact_mod_cast hle
  exact hle'.trans hk0le

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.HeightData NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
  {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra B.KO (A c)]
  [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem lN_nonneg' (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Formalism.MainNotions.Gaps.HeightData.lN K la := by
  unfold Formalism.MainNotions.Gaps.HeightData.lN
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h0

theorem htConcl_toHtData_of (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)
    (hD : (d.htOf hd hs).D = WeightFamilies.dimY D j) (hδ : (d.htOf hd hs).δ = G.del) (hi : (d.htOf hd hs).i = G.iet)
    (hg0 : (d.htOf hd hs).g0 = (g0 D : ℝ)) (hL : (d.htOf hd hs).L = wL.size) (hG : (d.htOf hd hs).G = Gc)
    (hPH : (d.htOf hd hs).PH = PH) (hPrw : (d.htOf hd hs).Prw = Prw) (hPet : (d.htOf hd hs).Pet = Pet)
    (hS : ∑ k, (d.htOf hd hs).S k ≤ ∑ k, WeightFamilies.meanLogSup B (G.th' k))
    (hI : ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Ila la ≤ (d.htOf hd hs).Ila la)
    (hN : ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Net la = (d.htOf hd hs).Net la)
    (h : Formalism.MainNotions.Gaps.HeightData.HtConcl (d.htOf hd hs)) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl (toHtData G Qf Gc PH Prw Pet) := by
  obtain ⟨hfin, hsum, hineq, heta⟩ := h
  have hle : ∀ la : HeightOneSpectrum (𝓞 B.KO),
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la := fun la =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast ENat.toNat_le_toNat (hI la) (hfin la)) (lN_nonneg' _ la)
  have hsum' : Summable fun la : HeightOneSpectrum (𝓞 B.KO) =>
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la :=
    Summable.of_nonneg_of_le (fun la => mul_nonneg (Nat.cast_nonneg _) (lN_nonneg' _ la)) hle hsum
  have hDr : ((d.htOf hd hs).D : ℝ) = (WeightFamilies.dimY D j : ℝ) := by exact_mod_cast hD
  have hδr : ((d.htOf hd hs).δ : ℝ) = (G.del : ℝ) := by exact_mod_cast hδ
  have hir : ((d.htOf hd hs).i : ℝ) = (G.iet : ℝ) := by exact_mod_cast hi
  refine ⟨fun la => ne_top_of_le_ne_top (hfin la) (hI la), hsum', ?_, fun he => ?_⟩
  · have ht := Summable.tsum_le_tsum hle hsum' hsum
    have hineq' : 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
          (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (G.del : ℝ) * Real.log G.del + 2 * ∑ k, (d.htOf hd hs).S k +
        8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
        2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size := by
      rw [hDr, hδr, hL, hG, hPH, hPrw] at hineq
      exact hineq
    show 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
          (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (G.del : ℝ) * Real.log G.del + 2 * ∑ k, WeightFamilies.meanLogSup B (G.th' k) +
        8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
        2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size
    linarith
  · obtain ⟨hsN, hbN⟩ := heta trivial
    rw [hir, hg0, hDr, hδr, hG, hPH, hL, hPrw, hPet] at hbN
    have e : (fun la : HeightOneSpectrum (𝓞 B.KO) =>
          (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la) =
        fun la : HeightOneSpectrum (𝓞 B.KO) => (d.htOf hd hs).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la :=
      funext fun la => by rw [hN la]
    refine ⟨?_, ?_⟩
    · show Summable fun la : HeightOneSpectrum (𝓞 B.KO) =>
        (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la
      rw [e]; exact hsN
    · show (∑' la : HeightOneSpectrum (𝓞 B.KO),
          (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la) / (G.iet : ℝ) ≤
        (g0 D : ℝ) * (((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size +
          4 / 3 * (WeightFamilies.dimY D j : ℝ) * G.del * Prw * wL.size) + G.del * Pet
      rw [e]; exact hbN

section Ties

variable (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)

def IlaTie : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Ila la ≤ (d.htOf hd hs).Ila la

def NetTie : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Net la = (d.htOf hd hs).Net la

end Ties

end Formalism.L2.Pj
end
end

