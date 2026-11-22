import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec

-- bundled from Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
section
noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cF (D : D7) : D.host.E ≃ₐ[D.host.F] D.host.E :=
  AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)

def latC (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.map ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E))

def IsRat (V : HSp D) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E) : Prop :=
  matHom V γ = Formalism.UG.bc (incA D) γ'

def FinCong (V : HSp D) (N : ℕ) (k : GA D V) : Prop :=
  ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

structure IotaOK (Dw : Datum H) (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop where
  rt : (H.rt : D.host.E) = D.host.sqrtMinusD
  rt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD
  emb : LatEmb V ι
  isom : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))

variable {Dw : Datum H} {l : Level H}

structure Ctx (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) : Type 1 where
  hr : V.rank = r
  g : ℕ
  e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  M : GlobalTheory.FrameUnif.ModelsOf F r
  ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)
  θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)
  x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ

namespace Ctx

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ} (C : Ctx Xo c σ V r)

structure OK : Prop where
  iota : IotaOK Dw V C.ι
  pos : 1 ≤ Dw.p + Dw.q
  lA : l.A = 1
  good : GoodEmb c σ
  base : GlobalTheory.FrameUnif.ModelBase C.M
  modelW : ∀ k, ModelW V C.hr (C.M.X k)
  inf : ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (C.θ τ)
  orth : ∀ k, IsOrthogonalFrame (C.M.X k) C.x₀

def th : ∀ k, (C.M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun _ τ => C.θ τ.1

def Mark (h : GA D V) (k : Fin C.F.n) (γ : GA D V) : Prop :=
  γ ∈ GQ V ∧
    ((C.M.X k).Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast C.hr.symm) '' (latG V (γ * h) : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V (γ * h),
        finVec V ((C.M.φ k (C.F.t k a) : Fin r → D.host.E) ∘ Fin.cast C.hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (C.ι a)) = (l.M : ℕ) • w

def fr (h : GA D V) (k : Fin C.F.n) : Frame (C.M.X k).Ψ r :=
  fun τ => (Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) h) * C.x₀ τ.1 :
    Matrix (Fin r) (Fin r) ℂ)

def IsDict (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) : Prop :=
  (∀ h, ∃ γ, C.Mark h (dict h).1 γ ∧ (dict h).2 = C.fr (γ * h) (dict h).1) ∧
    ∀ k, ∃ h, dict h = ⟨k, C.fr 1 k⟩

def unf (un : ∀ k, (C.M.X k).dom → FrPt Xo c (CAt σ)) : Unf Xo c σ r where
  Comp := Fin C.F.n
  X := C.M.X
  un := un

end Ctx

structure PkgLaws {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (Kf : Subgroup (GA D V)) (χ : (AE D)ˣ →* Circle)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop where
  unf : IsUnf U
  unTest : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)
  chi1 : ∀ k la γ, (U.X k).χ la γ = 1
  modelW : ∀ k, ModelW V hr (U.X k)
  familyUniformisationBasePointOrthogonal : ∀ k, IsOrthogonalFrame (U.X k) x₀
  muUnit : MuUnit V dict mu
  muCont : Continuous mu
  muVal : MuVal V χ mu
  adelAut : ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), IsHolCusp U.X la P →
    (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P)
  expo : ∀ ρ, FJ.LatZ U.X ρ ∧ FJ.ExpoMatch U.X 1 ρ l.M
  dictLaws : ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr ∧
      DictLat U V hr dict ι e F ik φ th x₀

theorem cF_apply_eq_complexConj (D : D7) (x : D.host.E) : cF D x = IsCMField.complexConj D.host.E x := rfl

theorem mem_latC_iff_symm_mem (V : HSp D) (v : Fin V.rank → D.host.E) :
    v ∈ latC V ↔ V.frame.equivFun.symm v ∈ V.L0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
    rwa [LinearEquiv.symm_apply_apply]
  · intro hv
    exact ⟨_, hv, V.frame.equivFun.apply_symm_apply v⟩

theorem coe_selfDualLatticeInFrameCoordinates_eq (V : HSp D) : (latC V : Set (Fin V.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D V := by
  ext v
  rw [SetLike.mem_coe, mem_latC_iff_symm_mem, Module.Basis.equivFun_symm_apply]
  rfl

theorem isLevelK_iff_finCong (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)) :
    IsLevelK V N Kf ↔ ∀ k, k ∈ Kf ↔ k ∈ GfC V ∧ FinCong V N k := Iff.rfl

theorem isRat_one_one (V : HSp D) : IsRat V 1 1 := by
  unfold IsRat
  rw [map_one, map_one]

theorem exists_isRat_of_mem_GQ (V : HSp D) {γ : GA D V} (h : γ ∈ GQ V) : ∃ γ', IsRat V γ γ' := by
  obtain ⟨γ', -, e⟩ := h
  exact ⟨γ', e.symm⟩

theorem trace_model_eq_trace_hT (V : HSp D) {r : ℕ} (hr : V.rank = r) (u v : Fin V.rank → D.host.E) :
    Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (GlobalTheory.RecDict.gmW V hr) (u ∘ Fin.cast hr.symm) (v ∘ Fin.cast hr.symm)) =
    -Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm v) (V.frame.equivFun.symm u)) := by
  subst hr
  have h : herm (GlobalTheory.RecDict.gmW V rfl) (u ∘ Fin.cast rfl) (v ∘ Fin.cast rfl) =
      -V.hT (V.frame.equivFun.symm v) (V.frame.equivFun.symm u) := by
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
      herm, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    show u a * (-V.gram b a) * cc (v b) = -(u a * (cc (v b) * V.gram b a))
    ring
  rw [h, neg_neg, mul_neg, map_neg]

theorem isom_iff_model (Dw : Datum H) (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) :
    (∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (ι x)) (V.frame.equivFun.symm (ι y)))) ↔
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (GlobalTheory.RecDict.gmW V hr) (ι x ∘ Fin.cast hr.symm) (ι y ∘ Fin.cast hr.symm)) := by
  have halt : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = -((Dw.EF y x : ℤ) : ℚ) := fun x y => by
    have h := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at h
    have h' : Dw.EF x y = -Dw.EF y x := by linarith
    rw [h', Int.cast_neg]
  simp only [trace_model_eq_trace_hT]
  constructor
  · intro h x y
    rw [halt, h]
  · intro h x y
    rw [halt, h, neg_neg]

namespace Ctx

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ} (C : Ctx Xo c σ V r)

theorem ok_iff_recOK : C.OK ↔ GlobalTheory.RecDict.RecOK C.M V C.hr C.ι C.th C.x₀ ∧
    (H.rt : D.host.E) = D.host.sqrtMinusD ∧ H.rt0 = D.host.φ₀ D.host.sqrtMinusD ∧ 1 ≤ Dw.p + Dw.q ∧ l.A = 1 ∧
    GoodEmb c σ ∧ ∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (C.θ τ) := by
  constructor
  · intro h
    exact ⟨⟨h.base, h.modelW, h.iota.emb, (isom_iff_model Dw V C.hr C.ι).1 h.iota.isom, fun _ τ => h.inf τ.1,
      h.orth⟩, h.iota.rt, h.iota.rt0, h.pos, h.lA, h.good, h.inf⟩
  · rintro ⟨⟨h1, h2, h3, h4, -, h6⟩, k1, k2, k3, k4, k5, k6⟩
    exact ⟨⟨k1, k2, h3, (isom_iff_model Dw V C.hr C.ι).2 h4⟩, k3, k4, k5, h1, h2, k6, h6⟩

theorem markSpec_iff_mark (h : GA D V) (p : Σ k, Frame (C.M.X k).Ψ r) :
    GlobalTheory.RecDict.MarkSpec C.M V C.hr C.ι C.th C.x₀ h p ↔ ∃ γ, C.Mark h p.1 γ ∧ p.2 = C.fr (γ * h) p.1 := by
  constructor
  · rintro ⟨γ, h1, h2, h3, h4⟩
    exact ⟨γ, ⟨h1, h2, h3⟩, funext h4⟩
  · rintro ⟨γ, ⟨h1, h2, h3⟩, h4⟩
    exact ⟨γ, h1, h2, h3, fun τ => congrFun h4 τ⟩

theorem isDict_iff_markSpec (dict : GA D V → Σ k, Frame (C.M.X k).Ψ r) :
    C.IsDict dict ↔ (∀ h, GlobalTheory.RecDict.MarkSpec C.M V C.hr C.ι C.th C.x₀ h (dict h)) ∧
      ∀ k, ∃ h, dict h = ⟨k, C.fr 1 k⟩ := by
  simp only [IsDict, markSpec_iff_mark]

theorem unf_eq_toPj (un : ∀ k, (C.M.X k).dom → FrPt Xo c (CAt σ)) :
    C.unf un = (GlobalTheory.FrameUnif.unfOf C.e C.F C.M un).toPj := rfl

theorem mat_fr_one (k : Fin C.F.n) (τ : (C.M.X k).Ψ) : mat (C.fr 1 k) τ = C.x₀ τ.1 := by
  have h : archM V (C.θ τ.1) 1 = 1 := by
    unfold archM
    rw [map_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  show Matrix.reindex (finCongr C.hr) (finCongr C.hr) (archM V (C.θ τ.1) 1) * C.x₀ τ.1 = _
  rw [h]
  simp

end Ctx

example (V : HSp D) (N : ℕ) : FinCong V N 1 := fun z _ => ⟨0, zero_mem _, by simp⟩

example (D : D7) (x : D.host.E) : cF D (cF D x) = x := star_star x

example (D : D7) : cF D D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [cF_apply_eq_complexConj, IsCMField.complexEmbedding_complexConj, map_neg, hφ]
  simp

end GlobalTheory.Member
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NegBaseElementImNegBaseEmbedding
section
noncomputable section
namespace GlobalTheory.RecDictModel
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RecDict
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

theorem dictLat_iff {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : GlobalTheory.FrameUnif.ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ))
    (hun : ∀ k x, GlobalTheory.FrameUnif.FrameOK e F M k x (un k x))
    (V : HSp D) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀)
    (dict : GA D V → Σ k, Frame (M.X k).Ψ r) :
    DictLat ({ Comp := Fin F.n, X := M.X, un := un } : Formalism.L2.Pj.Unf Xo c σ r) V hr dict io e F id M.φ th x₀ ↔
      ∀ h, MarkSpec M V hr io th x₀ h (dict h) := by
  refine ⟨fun h => h.2, fun h => ⟨⟨hR.1.ef, fun k x => ?_⟩, h⟩⟩
  obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun k x
  exact ⟨Pm, h1, h2, h3, h4⟩

variable {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty}

theorem markSpec_left (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : GA D V) (p : Σ k, Frame (M.X k).Ψ r)
    (δ : GA D V) (hδ : δ ∈ GQ V) :
    MarkSpec M V hr io th x₀ (δ * h) p ↔ MarkSpec M V hr io th x₀ h p := by
  constructor
  · rintro ⟨γ, hγ, h1⟩
    exact ⟨γ * δ, (GQ V).mul_mem hγ hδ, by simpa only [mul_assoc] using h1⟩
  · rintro ⟨γ, hγ, h1⟩
    exact ⟨γ * δ⁻¹, (GQ V).mul_mem hγ ((GQ V).inv_mem hδ), by simpa only [mul_assoc, inv_mul_cancel_left] using h1⟩

theorem herm_gmW (V : HSp D) (hr : V.rank = r) (x y : Fin V.rank → D.host.E) :
    herm (gmW V hr) (x ∘ Fin.cast hr.symm) (y ∘ Fin.cast hr.symm) =
      -V.hT (V.frame.equivFun.symm y) (V.frame.equivFun.symm x) := by
  subst hr
  simp only [herm, gmW, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : (starRingEnd D.host.E) (y b) = cc (y b) := rfl
  simp only [this, smul_eq_mul]
  simp [HSpace.gram]
  ring

theorem recOK_isom (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) (x y : Dw.La) :
    ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (D.host.xi0 * V.hT (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y))) := by
  have h1 : Dw.EF x y = -Dw.EF y x := by
    have h := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at h
    linarith
  rw [h1, Int.cast_neg, hR.2.2.2.1 y x, herm_gmW, ← map_neg]
  congr 1
  ring

theorem recOK_latIsom (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) :
    LatIsom V Dw.EF io :=
  ⟨1, fun x y => by rw [recOK_isom M V hr io th x₀ hR]; simp⟩

theorem recOK_gram (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) (k : Fin F.n) :
    (M.X k).Gm = gmW V hr := (hR.2.1 k).1

theorem neg_baseElement_im_neg_baseEmbedding (D : D7) (τ : D.host.E →+* ℂ) (hτ : τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD) :
    (τ (-D.host.xi0)).im < 0 := by
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hd : (0 : ℝ) < Real.sqrt D.host.d := by
    have : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
    apply Real.sqrt_pos.2
    exact_mod_cast (by omega : 0 < D.host.d)
  have hn : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.pos_of_ne_zero this
  have : τ (-D.host.xi0) = ((-(1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d)) : ℝ) : ℂ) * Complex.I := by
    simp only [Formalism.BasicNotions.Host.xi0, map_neg, map_div₀, map_one, map_mul, map_natCast, hτ, h0]
    have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
    simp
  rw [this, Complex.mul_I_im, Complex.ofReal_re]
  have : 0 < 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by positivity
  linarith

theorem th_conj {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (z : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    θ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ z) := by
  have hτ : ∀ x : D.host.E, τ (star x) = starRingEnd ℂ (τ x) := fun x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hre : ∀ a : Ainf D.host.F, starRingEnd ℂ (θ (a ⊗ₜ[D.host.F] (1 : D.host.E))) = θ (a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro a
    refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
      (isClosed_eq (Complex.continuous_conj.comp h.2) h.2) fun f => ?_
    have e : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
      exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f |>.trans
        ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
    erw [e, h.1, ← hτ]
    rw [(D.sp.cm.fixed _).2 ⟨f, rfl⟩]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul a x =>
    have e : ∀ y : D.host.E, a ⊗ₜ[D.host.F] y = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      intro y; simp
    have e2 : sigR (Ainf D.host.F) D.sp.cm.sig (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] (star x) := rfl
    rw [e2, e (star x), e x, map_mul, map_mul, map_mul, hre, h.1, h.1, hτ]

theorem cT_map {A : Type} [CommRing A] {n : Type} (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M : Matrix n n A) :
    (Formalism.UG.cT s M).map φ = (M.map φ).conjTranspose := by
  ext a b
  exact h _

theorem uni_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) (hM : Formalism.UG.cT s M * J * M = J)
    (J' M' : Matrix n n ℂ) (hJ : J.map φ = J') (hM' : M' = M.map φ) : M'.conjTranspose * J' * M' = J' := by
  subst hJ hM'
  rw [← cT_map s φ h, ← Matrix.map_mul, ← Matrix.map_mul, hM]

set_option maxHeartbeats 800000 in
theorem archM_unitary (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) :
    (archM V θ g).conjTranspose * V.gram.map τ * archM V θ g = V.gram.map τ := by
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).1 * JR (AF D.host.F) V.gram * (matHom V g).1 =
      JR (AF D.host.F) V.gram := g.2
  let π : AF D.host.F ⊗[D.host.F] D.host.E →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hπ : ∀ z, π (sigR (AF D.host.F) D.sp.cm.sig z) = sigR (Ainf D.host.F) D.sp.cm.sig (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul a x => rfl
  have hJ : (JR (AF D.host.F) V.gram).map (θ.comp π) = V.gram.map τ := by
    ext a b
    exact h.1 _
  exact uni_map (sigR (AF D.host.F) D.sp.cm.sig) (θ.comp π) (fun z => (congrArg θ (hπ z)).trans (th_conj h (π z))) _ _ hg
    _ _ hJ rfl

theorem gram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G x = (x.conjTranspose * (G.map τ).transpose * x).transpose := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

variable {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} in

theorem markSpec_orthonormal (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (th : ∀ k, (M.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hR : RecOK M V hr io th x₀) (h : GA D V)
    (p : Σ k, Frame (M.X k).Ψ r) (hp : MarkSpec M V hr io th x₀ h p) (τ : (M.X p.1).Ψ) :
    gram τ.1 (M.X p.1).Gm (mat p.2 τ) = Matrix.diagonal fun a : Fin r => ((sgn (M.X p.1).p0 (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨γ, -, -, -, h3⟩ := hp
  rw [← hR.2.2.2.2.2 p.1 τ.1 τ.2, h3 τ, gram_eq, gram_eq, (hR.2.1 p.1).1]
  have hu := archM_unitary V (hR.2.2.2.2.1 p.1 τ) (γ * h)
  subst hr
  have e1 : ∀ A : Matrix (Fin V.rank) (Fin V.rank) ℂ, Matrix.reindex (finCongr rfl) (finCongr rfl) A = A := fun A => rfl
  have e2 : ((-(Matrix.reindex (finCongr rfl) (finCongr rfl) V.gram).transpose).map τ.1).transpose = -(V.gram.map τ.1) := by
    ext a b; simp
  rw [e1, e2, Matrix.conjTranspose_mul]
  congr 1
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

variable {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (D.host.E →+* ℂ)} {F : FamilyUnif Xo σ' ty} in

theorem exists_base_frame (M : GlobalTheory.FrameUnif.ModelsOf F r) (V : HSp D) (hr : V.rank = r)
    (hB : GlobalTheory.FrameUnif.ModelBase M) (hW : ∀ k, ModelW V hr (M.X k)) :
    ∃ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, ∀ k, IsOrthogonalFrame (M.X k) x₀ := by
  classical
  let k₀ : Fin F.n := ⟨0, F.n_pos⟩
  choose P _ hP using (M.X k₀).signature
  refine ⟨fun τ => if h : τ ∈ (M.X k₀).Ψ then P ⟨τ, h⟩ else 0, fun k τ hτ => ?_⟩
  have h0 : τ ∈ (M.X k₀).Ψ := ((hB.type k₀).2 τ).2 (((hB.type k).2 τ).1 hτ)
  have := hP ⟨τ, h0⟩
  rw [(hW k₀).1, (hB.type k₀).1] at this
  simp only [dif_pos h0]
  rw [(hW k).1, (hB.type k).1]
  exact this

end GlobalTheory.RecDictModel
end
end

