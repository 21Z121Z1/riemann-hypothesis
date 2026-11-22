import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
import Formalism.LocalToGlobal.Columns.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGLSymmCastGL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Shift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}

def conjBack (J : Subgroup G) (k : G) : J.map (MulAut.conj k).toMonoidHom ≃* J where
  toFun x := ⟨k⁻¹ * x * k, by
    obtain ⟨j, hj, e⟩ := x.2
    have e' : k⁻¹ * (x : G) * k = j := by
      rw [← e]; show k⁻¹ * (k * j * k⁻¹) * k = j; group
    rw [e']; exact hj⟩
  invFun j := ⟨k * j * k⁻¹, ⟨j, j.2, rfl⟩⟩
  left_inv x := Subtype.ext (by show k * (k⁻¹ * (x : G) * k) * k⁻¹ = x; group)
  right_inv j := Subtype.ext (by show k⁻¹ * (k * (j : G) * k⁻¹) * k = j; group)
  map_mul' x y := Subtype.ext (by show k⁻¹ * ((x : G) * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k); group)

theorem conjBack_spec (J : Subgroup G) (k : G) (x : J.map (MulAut.conj k).toMonoidHom) :
    ((conjBack J k x : J) : G) = k⁻¹ * x * k := rfl

def shiftR (A : AdPts S ι J) (k : G) : AdPts S ι (J.map (MulAut.conj k).toMonoidHom) where
  K1 := A.K1.map (MulAut.conj k).toMonoidHom
  principal_congruence_le := Subgroup.map_mono A.principal_congruence_le
  q x := A.q (x * k)
  gl := A.gl.comp (MonoidHom.prodMap (MonoidHom.id Γ) (conjBack J k).toMonoidHom)
  gl_surj := by
    intro g
    obtain ⟨⟨γ, j⟩, rfl⟩ := A.gl_surj g
    refine ⟨(γ, (conjBack J k).symm j), ?_⟩
    show A.gl (γ, conjBack J k ((conjBack J k).symm j)) = _
    rw [MulEquiv.apply_symm_apply]
  gl_ker := by
    intro γ x
    show A.gl (γ, conjBack J k x) = 1 ↔ _
    rw [A.gl_ker, conjBack_spec]
    refine and_congr Iff.rfl ⟨fun h => ⟨_, h, by show k * (k⁻¹ * (x : G) * k) * k⁻¹ = x; group⟩, ?_⟩
    rintro ⟨y, hy, e⟩
    rw [← e]
    have e2 : k⁻¹ * ((MulAut.conj k).toMonoidHom y) * k = y := by
      show k⁻¹ * (k * y * k⁻¹) * k = y; group
    rw [e2]; exact hy
  q_surj := by
    intro d
    obtain ⟨x, rfl⟩ := A.q_surj d
    exact ⟨x * k⁻¹, by simp⟩
  q_eqv := by
    intro γ x y
    show A.q (ι γ * y * (x : G)⁻¹ * k) = A.gl (γ, conjBack J k x) • A.q (y * k)
    rw [← A.q_eqv]
    congr 1
    rw [conjBack_spec]; group
  q_fib := by
    intro x x'
    show A.q (x * k) = A.q (x' * k) ↔ _
    rw [A.q_fib]
    constructor
    · rintro ⟨k1, hk1, e⟩
      refine ⟨k * k1 * k⁻¹, ⟨k1, hk1, rfl⟩, ?_⟩
      calc x' = x' * k * k⁻¹ := by group
        _ = x * k * k1 * k⁻¹ := by rw [e]
        _ = _ := by group
    · rintro ⟨_, ⟨k1, hk1, rfl⟩, e⟩
      refine ⟨k1, hk1, ?_⟩
      rw [e]; show x * (k * k1 * k⁻¹) * k = x * k * k1; group

end Shift

section Read

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem classPresOf_ext (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    (f : (S.toCSD h).Forms) (g : G) :
    (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q g)) := by

  have key : ∀ (γ : Γ) (c : S.Cl) (k : J),
      (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (ι γ * A.y c * k))) := by
    intro γ c k
    have e1 : (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        (χ k : ℂ) • ρ γ (coef ((f : S.Cl → S.V) c)) :=
      ClassPres.ext_eq (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl) f γ c k
    have e2 : A.q (ι γ * A.y c * k) = A.gl (γ, k⁻¹) • S.outSec.rep c := by
      rw [A.q_mul, A.q_y]
    have e3 : (((S.res h).symm f : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
      have := S.resOf_apply h S.outSec ((S.res h).symm f) c
      rw [← this]
      show ((((S.res h) ((S.res h).symm f)).1 : S.Cl → S.V) c) = _
      rw [LinearEquiv.apply_symm_apply]
    have e4 := (S.mem_EqFun _).1 ((S.res h).symm f).2 (A.gl (γ, k⁻¹)) (S.outSec.rep c)
    rw [e1, e2, e4, e3, hgl, map_inv, inv_inv, Units.smul_def]
  rw [(classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).dec_spec g]
  exact key _ _ _

variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'} {ρ : Γ →* Module.End ℂ W} {ρ' : Γ' →* Module.End ℂ W}
  {J' : Subgroup G'} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ} {T : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ}

theorem transport_ext (P : ClassPres ι T σ ρ J χ) (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ) (hJ : J' = J.map eG.toMonoidHom)
    (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k) (f : T.Forms) (g : G) :
    (P.transport eG eΓ hι hρ hJ hχ).ext (f : T.Cl → T.V) (eG g) = P.ext f g := by
  rw [P.dec_spec g]
  have hk : eG (P.decK g : G) ∈ J' := by
    rw [hJ]; exact Subgroup.mem_map_of_mem eG.toMonoidHom (P.decK g).2
  have e : eG (ι (P.decG g) * P.y (P.decC g) * (P.decK g : G)) =
      ι' (eΓ (P.decG g)) * (P.transport eG eΓ hι hρ hJ hχ).y (P.decC g) * ((⟨_, hk⟩ : J') : G') := by
    rw [map_mul, map_mul, hι]; rfl
  rw [e, ClassPres.ext_eq, ClassPres.ext_eq, hχ, hρ]
  rfl

end Read

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'}

def levE (eG : G ≃* G') (k : G) (J' : Subgroup G') (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom) :
    J.map (MulAut.conj k).toMonoidHom ≃* J' :=
  ((J.map (MulAut.conj k).toMonoidHom).equivMapOfInjective eG.toMonoidHom eG.injective).trans
    (MulEquiv.subgroupCongr hJ.symm)

theorem levE_coe (eG : G ≃* G') (k : G) (J' : Subgroup G') (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom)
    (x : J.map (MulAut.conj k).toMonoidHom) : ((levE eG k J' hJ x : J') : G') = eG x := rfl

def presST (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ' : Γ' →* Module.End ℂ W) (k : G) (eG : G ≃* G') (eΓ : Γ ≃* Γ')
    (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (J' : Subgroup G') (χ' : J' →* ℂˣ)
    (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ κ : J, (κ : G) ∈ A.K1 → ∀ hx : eG (k * κ * k⁻¹) ∈ J', χ' ⟨_, hx⟩ = 1)
    (hgl : ∀ (γ : Γ) (κ : J) (v : S.V) (hx : eG (k * κ * k⁻¹) ∈ J'),
      coef (S.ρ (A.gl (γ, κ)) v) = ((χ' ⟨_, hx⟩)⁻¹ : ℂˣ) • ρ' (eΓ γ) (coef v)) :
    ClassPres ι' (S.toCSD h) σ ρ' J' χ' :=
  ClassPres.transport
    (classPresOf (shiftR A k) h σ (ρ'.comp eΓ.toMonoidHom) (χ'.comp (levE eG k J' hJ).toMonoidHom) coef hli hspan hpair
      (fun x hx => by
        obtain ⟨y, hy, e⟩ := hx
        have hκ : k⁻¹ * (x : G) * k ∈ A.K1 := by
          rw [← e]; show k⁻¹ * (k * y * k⁻¹) * k ∈ A.K1
          have e2 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
          rw [e2]; exact hy
        have hx' : eG (k * ((conjBack J k x : J) : G) * k⁻¹) ∈ J' := by
          rw [conjBack_spec]
          have e3 : k * (k⁻¹ * (x : G) * k) * k⁻¹ = x := by group
          rw [e3]; exact (levE eG k J' hJ x).2
        have := hK1 (conjBack J k x) hκ hx'
        rw [← this]
        show χ' (levE eG k J' hJ x) = _
        congr 1
        apply Subtype.ext
        show eG (x : G) = eG (k * (k⁻¹ * (x : G) * k) * k⁻¹)
        congr 1; group)
      (fun γ x v => by
        have hx' : eG (k * ((conjBack J k x : J) : G) * k⁻¹) ∈ J' := by
          rw [conjBack_spec]
          have e3 : k * (k⁻¹ * (x : G) * k) * k⁻¹ = x := by group
          rw [e3]; exact (levE eG k J' hJ x).2
        have := hgl γ (conjBack J k x) v hx'
        show coef (S.ρ (A.gl (γ, conjBack J k x)) v) = ((χ' (levE eG k J' hJ x))⁻¹ : ℂˣ) • ρ' (eΓ γ) (coef v)
        rw [this]
        congr 3
        apply Subtype.ext
        show eG (k * (k⁻¹ * (x : G) * k) * k⁻¹) = eG (x : G)
        congr 1; group))
    eG eΓ hι (fun _ => rfl) hJ (fun x hx => rfl)

variable (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ' : Γ' →* Module.End ℂ W) (k : G) (eG : G ≃* G') (eΓ : Γ ≃* Γ')
    (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (J' : Subgroup G') (χ' : J' →* ℂˣ)
    (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ κ : J, (κ : G) ∈ A.K1 → ∀ hx : eG (k * κ * k⁻¹) ∈ J', χ' ⟨_, hx⟩ = 1)
    (hgl : ∀ (γ : Γ) (κ : J) (v : S.V) (hx : eG (k * κ * k⁻¹) ∈ J'),
      coef (S.ρ (A.gl (γ, κ)) v) = ((χ' ⟨_, hx⟩)⁻¹ : ℂˣ) • ρ' (eΓ γ) (coef v))

end Assemble

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

theorem castGL_symm_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (x : GL (Fin m) R) :
    GlobalTheory.Mem.R3.LiftBrg.castGL h.symm (GlobalTheory.Mem.R3.LiftBrg.castGL h x) = x := by
  subst h
  ext i j
  simp [GlobalTheory.Mem.R3.LiftBrg.castGL]

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

theorem ufGL_ratHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n) :
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  show Formalism.L2.Col.toGLm E n (Formalism.UG.glEquiv (γ : GL (Fin n) E)) = _
  simp only [Formalism.L2.Col.toGLm, Formalism.UG.glEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

def latImg {E : Type} [Field E] [NumberField E] {m n : ℕ} (h : m = n) (B : GL (Fin m) E)
    (N : Submodule (𝓞 E) (Fin m → E)) : Submodule (𝓞 E) (Fin n → E) :=
  N.map (((Matrix.toLin' ((LiftBrg.castGL h B : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) ∘ₗ
    (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)

end GlobalTheory.Mem.R3.LiftPres
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinateLinearRelation
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv plE)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.CellLin

variable {R : Type} [CommRing R] {m a k b N : ℕ}

def pmat (hk : k ≤ m) (w : GPm m a b) : Matrix (Fin k) (Fin m) (MvPolynomial (GVar m a k b) R) :=
  fun l i => gcell MvPolynomial.X (w.1⁻¹ i) (Fin.castLE hk l)

theorem gvec_apply (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R) (w : GPm m a b) (l : Fin k) (r : Fin (N + 1)) :
    gvec (fun l => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ c l) w
        (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) R) (Fin.castLE hk l) r =
      ∑ i, pmat hk w l i * MvPolynomial.C (c i r) := by
  simp only [gvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, pmat]
  refine ((Equiv.sum_comp w.1 fun i =>
    gcell MvPolynomial.X (w.1⁻¹ i) (Fin.castLE hk l) * MvPolynomial.C (c i r)).symm.trans ?_).symm
  simp

theorem gxi_eq (hk : k ≤ m) (c : Fin m → Fin (N + 1) → R) (w : GPm m a b) (q : Fin (plN N k + 1)) :
    gxi a b hk c w q = ∑ S : Set.powersetCard (Fin m) k, ((pmat hk w).submatrix id (subsetEnum S)).det *
      MvPolynomial.C (plk c (subsetEnum S) q) := by
  let B : Matrix (Fin m) (Fin k) (MvPolynomial (GVar m a k b) R) :=
    Matrix.of fun i l' => MvPolynomial.C (c i (plE N k q l'))
  have h : (Matrix.of fun l l' => gvec (fun l => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ c l) w
        (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) R) (Fin.castLE hk l) (plE N k q l')) =
      (pmat (R := R) hk w * B : Matrix (Fin k) (Fin k) (MvPolynomial (GVar m a k b) R)) := by
    ext1 l l'
    rw [Matrix.mul_apply, Matrix.of_apply, gvec_apply]
    rfl
  unfold gxi plk
  rw [h, det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1

theorem sum_gell (hk : k ≤ m) {D c : Fin m → Fin (N + 1) → R} (h : LeftInv D c) (w v : GPm m a b) :
    ∑ q, MvPolynomial.C (gell a b hk D v q) * gxi a b hk c w q =
      ((pmat hk w).submatrix id (v.1 ∘ Fin.castLE hk)).det := by
  have h1 : ∀ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D v q) =
      lform (fun i => (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) ∘ D i) (v.1 ∘ Fin.castLE hk) q := by
    intro q
    simp [gell, lform, map_prod]
  simp only [h1, gxi]
  rw [GlobalTheory.FlagEmb.CauchyBinet.lform_plk]
  congr 1
  ext1 l l'
  simp only [Matrix.of_apply, Matrix.submatrix_apply, id, gvec_apply, Function.comp_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ i, ∑ r, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (D (v.1 (Fin.castLE hk l')) r) *
      (pmat hk w l i * MvPolynomial.C (c i r)) = pmat hk w l i *
        MvPolynomial.C (∑ r, D (v.1 (Fin.castLE hk l')) r * c i r) := by
    intro i
    simp only [map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  simp only [h2, h _ _]
  rw [Finset.sum_eq_single (v.1 (Fin.castLE hk l'))]
  · simp
  · intro i _ hi
    rw [if_neg (Ne.symm hi)]
    simp
  · simp

theorem exists_perm (hk : k ≤ m) (hkb : k ≤ b) (hak : a ≤ k) (f : Fin k → Fin m) (hf : Function.Injective f)
    (h1 : ∀ l : Fin k, (l : ℕ) < a → (f l : ℕ) = l) (h2 : ∀ l, (f l : ℕ) < b) :
    ∃ v : GPm m a b, ∀ l, v.1 (Fin.castLE hk l) = f l := by
  classical
  let p : Fin m → Prop := fun i => (i : ℕ) < k ∨ b ≤ (i : ℕ)
  let g : {i // p i} → Fin m := fun i => if h : (i.1 : ℕ) < k then f ⟨i.1, h⟩ else i.1
  have hg : Function.Injective g := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [g] at hij
    split_ifs at hij with h3 h4 h4
    · have := hf hij
      simp only [Fin.mk.injEq] at this
      exact Subtype.ext (Fin.ext this)
    · have h5 := h2 ⟨i, h3⟩
      rw [hij] at h5
      have := hj.resolve_left h4
      omega
    · have h5 := h2 ⟨j, h4⟩
      rw [← hij] at h5
      have := hi.resolve_left h3
      omega
    · exact Subtype.ext hij
  let e : {i // p i} ≃ {y // y ∈ Set.range g} := Equiv.ofInjective g hg
  have hv : ∀ i (hi : p i), e.extendSubtype i = g ⟨i, hi⟩ := fun i hi => by
    rw [Equiv.extendSubtype_apply_of_mem e i hi]
    rfl
  refine ⟨⟨e.extendSubtype, fun i hi => ?_⟩, fun l => ?_⟩
  · rcases hi with hi | hi
    · have hik : (i : ℕ) < k := by omega
      rw [hv i (Or.inl hik)]
      simp only [g, dif_pos hik]
      exact Fin.ext (h1 ⟨i, hik⟩ hi)
    · have hik : ¬ (i : ℕ) < k := by omega
      rw [hv i (Or.inr hi)]
      simp only [g, dif_neg hik]
  · have hl : ((Fin.castLE hk l : Fin m) : ℕ) < k := l.2
    change e.extendSubtype (Fin.castLE hk l) = f l
    rw [hv _ (Or.inl hl)]
    simp only [g, dif_pos hl]
    rfl

theorem enum_init (hk : k ≤ m) (hak : a ≤ k) (f : Fin k → Fin m) (hf : StrictMono f)
    (h : ∀ i : Fin m, (i : ℕ) < a → i ∈ Set.range f) (n : ℕ) : ∀ (hn : n < k), n < a → (f ⟨n, hn⟩ : ℕ) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hna
    obtain ⟨l', hl'⟩ := h ⟨n, by omega⟩ hna
    have h1 : ¬ (l' : ℕ) < n := fun hlt => by
      have := ih l' hlt l'.2 (by omega)
      have h3 : f ⟨l', l'.2⟩ = f l' := rfl
      rw [h3, hl'] at this
      simp only at this
      omega
    rcases Nat.lt_or_ge n l' with h2 | h2
    · have h3 : f ⟨n, hn⟩ < f l' := hf (by simpa [Fin.lt_def] using h2)
      rw [hl'] at h3
      have h4 : (f ⟨n, hn⟩ : ℕ) < n := h3
      have h5 := hf.injective (Fin.ext (ih _ h4 (by omega) (by omega)))
      simp only [Fin.mk.injEq] at h5
      omega
    · have : (⟨n, hn⟩ : Fin k) = l' := Fin.ext (by simp; omega)
      rw [this, hl']

theorem det_eq_zero_of_lt (hk : k ≤ m) (hak : a ≤ k) (w : GPm m a b) (f : Fin k → Fin m) (i : Fin m) (hi : (i : ℕ) < a)
    (hf : i ∉ Set.range f) : ((pmat (R := R) hk w).submatrix id f).det = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨i, by omega⟩ fun l' => ?_
  simp only [Matrix.submatrix_apply, id, pmat, gcell]
  rw [dif_neg (fun h => by have := h.1; simp at this; omega), if_neg]
  intro he
  apply hf
  refine ⟨l', ?_⟩
  have h1 : Fin.castLE hk (⟨i, by omega⟩ : Fin k) = i := rfl
  rw [h1, Equiv.Perm.inv_eq_iff_eq, w.2 i (Or.inl hi)] at he
  exact he

theorem det_eq_zero_of_ge (hk : k ≤ m) (hkb : k ≤ b) (w : GPm m a b) (f : Fin k → Fin m) (l' : Fin k)
    (hi : b ≤ (f l' : ℕ)) : ((pmat (R := R) hk w).submatrix id f).det = 0 := by
  refine Matrix.det_eq_zero_of_column_eq_zero l' fun l => ?_
  have h1 : w.1⁻¹ (f l') = f l' := by
    rw [Equiv.Perm.inv_eq_iff_eq, w.2 _ (Or.inr hi)]
  simp only [Matrix.submatrix_apply, id, pmat, gcell, h1]
  rw [dif_neg (fun h => by have := h.2.2.2; omega), if_neg]
  intro he
  have h2 := congrArg Fin.val he
  have h3 := l.2
  simp only [Fin.val_castLE] at h2
  omega

theorem main : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R), a ≤ k → k ≤ b → LeftInv D c → ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → GPm m a b) (e : T → R), ∀ w' : GPm m a b, gxi a b hk c w' q = ∑ t, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (e t) * ∑ q', (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D (jj t) q') * gxi a b hk c w' q' := by
  intro R _ m a k b N hk D c hak hkb h q
  classical
  let admitted : Set.powersetCard (Fin m) k → Prop := fun S =>
    (∀ i : Fin m, (i : ℕ) < a → i ∈ Set.range (subsetEnum S)) ∧ ∀ l, (subsetEnum S l).val < b
  have hex : ∀ S : {S // admitted S}, ∃ v : GPm m a b, ∀ l, v.1 (Fin.castLE hk l) = subsetEnum S.1 l := fun S =>
    exists_perm hk hkb hak _ (subsetEnum_injective S.1)
      (fun l hl => enum_init hk hak _ (S.1.1.orderEmbOfFin S.1.2).strictMono S.2.1 l l.2 hl) S.2.2
  choose jj hjj using hex
  refine ⟨{S // admitted S}, inferInstance, jj, fun S => plk c (subsetEnum S.1) q, fun w => ?_⟩
  have h1 : ∀ S, (jj S).1 ∘ Fin.castLE hk = subsetEnum S.1 := fun S => funext (hjj S)
  simp only [sum_gell hk h, h1]
  rw [gxi_eq, ← Finset.sum_subtype (Finset.univ.filter admitted) (by simp)
    (fun S => MvPolynomial.C (plk c (subsetEnum S) q) * ((pmat hk w).submatrix id (subsetEnum S)).det),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs with hS
  · exact mul_comm _ _
  · rw [not_and_or] at hS
    rcases hS with hS | hS
    · push Not at hS
      obtain ⟨i, hi, hf⟩ := hS
      rw [det_eq_zero_of_lt hk hak w _ i hi hf, zero_mul]
    · push Not at hS
      obtain ⟨l, hl⟩ := hS
      rw [det_eq_zero_of_ge hk hkb w _ l hl, zero_mul]

end GlobalTheory.GrCl.CellLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_trivial_on_projective_cover : ∀ (O : Type) [CommRing O] (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp O) (J : Type) (U : J → X.Opens) (n : J → ℕ) (G : ∀ j j', Matrix (Fin (n j)) (Fin (n j')) Γ(X, U j ⊓ U j')), IsProjOver s → (∀ x : X, ∃ j, x ∈ U j) → (∀ (k : Type) [Field k] (w : Sp k ⟶ X) j, ⊤ ≤ w ⁻¹ᵁ U j → (G j j).map (valF w _) = 1) → (∀ (k : Type) [Field k] (w : Sp k ⟶ X) j j' j'', ⊤ ≤ w ⁻¹ᵁ U j → ⊤ ≤ w ⁻¹ᵁ U j' → ⊤ ≤ w ⁻¹ᵁ U j'' → (G j j').map (valF w _) * (G j' j'').map (valF w _) = (G j j'').map (valF w _)) → ∃ (L : FinLB X) (M : ℕ) (σ : Fin L.n → J) (A : ∀ i, Matrix (Fin (M + 1)) (Fin (n (σ i))) Γ(X, L.U i)) (B : ∀ i, Matrix (Fin (n (σ i))) (Fin (M + 1)) Γ(X, L.U i)), (∀ i, IsAffineOpen (L.U i)) ∧ (∀ i, L.U i ≤ U (σ i)) ∧ (∀ i, B i * A i = 1) ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X) i i', ⊤ ≤ w ⁻¹ᵁ L.U i → ⊤ ≤ w ⁻¹ᵁ L.U i' → (A i).map (valF w _) = valF w _ (L.g i i').val • ((A i').map (valF w _) * (G (σ i') (σ i)).map (valF w _)) := by
  first | exact @GlobalTheory.TwistEmb.exists_twist_embedding | exact GlobalTheory.TwistEmb.exists_twist_embedding | (intros; apply GlobalTheory.TwistEmb.exists_twist_embedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem noetherianSpace_cell {X : Scheme.{0}} [IsLocallyNoetherian X] {T : Type} [Finite T] (m : T → ℕ)
    (U : X.affineOpens) : TopologicalSpace.NoetherianSpace (Sp (CR m U)) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing (CR m U) := inferInstance
  exact inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum (CR m U)))

theorem compact_normal_noetherian_of_cells : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (F : Scheme.{0}) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ b w, IsOpenImmersion (i b w)) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → CompactSpace F ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F ∧ TopologicalSpace.NoetherianSpace F := by
  intro X _ T _ m B _ V F i hX hi hc
  have hN : TopologicalSpace.NoetherianSpace F := by
    have h1 : ∀ a : B × Pm m, TopologicalSpace.NoetherianSpace (Set.range (i a.1 a.2)) := fun a => by
      have := noetherianSpace_cell m (V a.1)
      exact TopologicalSpace.NoetherianSpace.range _ (i a.1 a.2).continuous
    have h2 := TopologicalSpace.NoetherianSpace.iUnion (fun a : B × Pm m => Set.range (i a.1 a.2))
    have h3 : (⋃ a : B × Pm m, Set.range (i a.1 a.2)) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨b, w, h⟩ := hc x
      exact Set.mem_iUnion.2 ⟨(b, w), h⟩
    rw [h3] at h2
    exact TopologicalSpace.noetherian_univ_iff.1 h2
  refine ⟨inferInstance, fun x => ?_, hN⟩
  obtain ⟨b, w, y, rfl⟩ := hc x
  have := hi b w
  obtain ⟨_, _⟩ := (cell_smooth_normal X T m (V b) hX).2 y
  let e := (asIso ((i b w).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateHermitianSmoothStatement
section
open AlgebraicGeometry CategoryTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.GradedNorm
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_hermitian_smooth : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D m : ℕ} (R : AnRead p σ D) (S : Set (CxPts p σ)), IsOpen S → ∀ (A M : CxPts p σ → Matrix (Fin m) (Fin m) ℂ), (∀ a b, R.HoloOn S (fun y => A y a b)) → (∀ a b, R.SmoothOn S (fun y => (M y a b).re) ∧ R.SmoothOn S (fun y => (M y a b).im)) → ∀ a b : Fin m, R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).re) ∧ R.SmoothOn S (fun y => (((A y)ᴴ * M y * A y) a b).im) := by
  first | exact @GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul | exact GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul | (intros; apply GlobalTheory.AnRead.smoothOn_conjTranspose_mul_mul <;> assumption)
end

