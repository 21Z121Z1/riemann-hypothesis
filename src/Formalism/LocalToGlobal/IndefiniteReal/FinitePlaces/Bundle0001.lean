import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LinIndepOneDelta
section
noncomputable section

open scoped TensorProduct

namespace Formalism.IndefR.Fin.U1

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]

theorem exists_delta (σ : E →ₐ[F] E) (hinv : ∀ e, σ (σ e) = e)
    (hfix : ∀ e, σ e = e ↔ e ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2) :
    ∃ δ : E, σ δ = -δ ∧ δ ≠ 0 := by
  have hex : ∃ e : E, e ∉ (algebraMap F E).range := by
    by_contra hne
    push_neg at hne
    have hsurj : Function.Surjective (Algebra.linearMap F E) := fun e => by
      obtain ⟨x, hx⟩ := hne e
      exact ⟨x, hx⟩
    have hinj : Function.Injective (Algebra.linearMap F E) := (algebraMap F E).injective
    have hfr := (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨hinj, hsurj⟩).finrank_eq
    rw [Module.finrank_self, h2] at hfr
    norm_num at hfr
  obtain ⟨e, he⟩ := hex
  refine ⟨e - σ e, ?_, ?_⟩
  · rw [map_sub, hinv]
    abel
  · intro h0
    apply he
    rw [← hfix]
    exact (sub_eq_zero.mp h0).symm

variable (σ : E →ₐ[F] E) (δ : E)

theorem linIndep_one_delta (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h' : σ (s • (1 : E) + t • δ) = 0 := by rw [h, map_zero]
  rw [map_add, map_smul, map_smul, map_one, hδ] at h'
  have hs : (2 : F) • (s • (1 : E)) = 0 := by
    rw [two_smul]
    calc s • (1 : E) + s • 1 = (s • 1 + t • δ) + (s • 1 + t • -δ) := by rw [smul_neg]; abel
      _ = 0 := by rw [h, h', add_zero]
  have hs0 : s = 0 := by
    rw [smul_smul, smul_eq_zero] at hs
    rcases hs with hs | hs
    · rcases mul_eq_zero.mp hs with h2' | h2'
      · exact absurd h2' two_ne_zero
      · exact h2'
    · exact absurd hs one_ne_zero
  subst hs0
  refine ⟨rfl, ?_⟩
  rw [zero_smul, zero_add, smul_eq_zero] at h
  exact h.resolve_right hδ0

end Gen

section Coords

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
variable (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) (h2 : Module.finrank F E = 2)
variable (R : Type) [CommRing R] [Algebra F R]

def bE : Module.Basis (Fin 2) F E :=
  basisOfLinearIndependentOfCardEqFinrank (linIndep_one_delta σ δ hδ hδ0) (by simp [h2])

theorem bE_zero : bE σ δ hδ hδ0 h2 0 = 1 := by
  simp [bE, coe_basisOfLinearIndependentOfCardEqFinrank]
theorem bE_one : bE σ δ hδ hδ0 h2 1 = δ := by
  simp [bE, coe_basisOfLinearIndependentOfCardEqFinrank]

def bR : Module.Basis (Fin 2) R (R ⊗[F] E) := Algebra.TensorProduct.basis R (bE σ δ hδ hδ0 h2)

def mkE (a b : R) : R ⊗[F] E := a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] δ

theorem mkE_eq (a b : R) :
    mkE δ R a b = a • bR σ δ hδ hδ0 h2 R 0 + b • bR σ δ hδ hδ0 h2 R 1 := by
  simp only [mkE, bR, Algebra.TensorProduct.basis_apply, bE_zero, bE_one, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

def cP : R ⊗[F] E →ₗ[R] R := (bR σ δ hδ hδ0 h2 R).coord 0

def cQ : R ⊗[F] E →ₗ[R] R := (bR σ δ hδ hδ0 h2 R).coord 1

theorem re_mk (a b : R) : cP σ δ hδ hδ0 h2 R (mkE δ R a b) = a := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  simp [cP, Module.Basis.coord_apply, Finsupp.single_apply]

theorem cQ_mkE (a b : R) : cQ σ δ hδ hδ0 h2 R (mkE δ R a b) = b := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  simp [cQ, Module.Basis.coord_apply, Finsupp.single_apply]

theorem mkE_cP_cQ (x : R ⊗[F] E) :
    mkE δ R (cP σ δ hδ hδ0 h2 R x) (cQ σ δ hδ hδ0 h2 R x) = x := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  have hx := (bR σ δ hδ hδ0 h2 R).sum_repr x
  rw [Fin.sum_univ_two] at hx
  simpa [cP, cQ, Module.Basis.coord_apply] using hx

include σ hδ hδ0 h2 in
theorem mkE_inj {a b a' b' : R} (h : mkE (F := F) δ R a b = mkE (F := F) δ R a' b') : a = a' ∧ b = b' := by
  have h1 := congrArg (cP σ δ hδ hδ0 h2 R) h
  have h2' := congrArg (cQ σ δ hδ hδ0 h2 R) h
  rw [re_mk, re_mk] at h1
  rw [cQ_mkE, cQ_mkE] at h2'
  exact ⟨h1, h2'⟩

end Coords

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ) (Δ : F) (hΔ : algebraMap F E Δ = δ * δ)
variable (R : Type) [CommRing R] [Algebra F R]

include hΔ in
theorem mkE_mul (a b a' b' : R) :
    mkE (F := F) δ R a b * mkE (F := F) δ R a' b' =
      mkE (F := F) δ R (a * a' + algebraMap F R Δ * (b * b')) (a * b' + b * a') := by
  simp only [mkE, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [← hΔ, Algebra.algebraMap_eq_smul_one (A := E) Δ, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Algebra.smul_def Δ (b * b'), TensorProduct.add_tmul, TensorProduct.add_tmul]
  abel

theorem mkE_one : mkE (F := F) δ R 1 0 = 1 := by
  simp [mkE, Algebra.TensorProduct.one_def]

theorem mkE_zero : mkE (F := F) δ R 0 0 = 0 := by
  simp [mkE]

theorem mkE_add (a b a' b' : R) :
    mkE (F := F) δ R a b + mkE (F := F) δ R a' b' = mkE (F := F) δ R (a + a') (b + b') := by
  simp only [mkE, TensorProduct.add_tmul]
  abel

theorem mkE_sub (a b a' b' : R) :
    mkE (F := F) δ R a b - mkE (F := F) δ R a' b' = mkE (F := F) δ R (a - a') (b - b') := by
  simp only [mkE, TensorProduct.sub_tmul]
  abel

theorem algebraMap_eq_mkE (a : R) : algebraMap R (R ⊗[F] E) a = mkE (F := F) δ R a 0 := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]
  simp [mkE]

theorem smul_mkE (r a b : R) : algebraMap R (R ⊗[F] E) r * mkE (F := F) δ R a b = mkE (F := F) δ R (r * a) (r * b) := by
  rw [← Algebra.smul_def]
  simp only [mkE, smul_add, TensorProduct.smul_tmul', smul_eq_mul]

include hδ in
theorem conj_mkE (a b : R) :
    (Algebra.TensorProduct.map (AlgHom.id F R) σ) (mkE (F := F) δ R a b) = mkE (F := F) δ R a (-b) := by
  simp only [mkE, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, hδ,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul]

include hΔ in
theorem mkE_norm (a b : R) :
    mkE (F := F) δ R a b * mkE (F := F) δ R a (-b) = mkE (F := F) δ R (a * a - algebraMap F R Δ * (b * b)) 0 := by
  rw [mkE_mul δ Δ hΔ R, show a * a + algebraMap F R Δ * (b * -b) = a * a - algebraMap F R Δ * (b * b) by ring,
    show a * -b + b * a = 0 by ring]

theorem incl_eq_mkE (α β : F) :
    (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) (algebraMap F E α + algebraMap F E β * δ) =
      mkE (F := F) δ R (algebraMap F R α) (algebraMap F R β) := by
  rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add, ← Algebra.smul_def,
    Algebra.algebraMap_eq_smul_one (A := E) α, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one]
  rfl

end Alg

end Formalism.IndefR.Fin.U1

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SelfDualLatticeIsSelfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

namespace Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def crd (V : HSp D) : (Fin V.rank → D.host.E) ≃ₗ[D.host.E] V.V := V.frame.equivFun.symm

def l0s (V : HSp D) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  V.L0.comap ((crd V).toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_self_dual_lattice_set (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ l0s V ↔ x ∈ L0c D V := by
  simp [l0s, crd, L0c, Module.Basis.equivFun_symm_apply]

theorem coe_self_dual_lattice_set (V : HSp D) : (l0s V : Set (Fin V.rank → D.host.E)) = L0c D V := by
  ext x; exact mem_self_dual_lattice_set V x

theorem hT_crd (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (crd V x) (crd V y) = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
  simp only [crd, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

theorem self_dual_lattice_is_self_dual (V : HSp D) : Datum.IsSelfDualC V (l0s V) := by
  refine ⟨?_, fun y => ?_⟩
  · have hL := V.standardTuple_isLattice
    let f : V.V ≃ₗ[D.host.E] (Fin V.rank → D.host.E) := (crd V).symm
    have heq : l0s V = V.L0.map (f.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext x
      simp only [l0s, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, f]
      constructor
      · intro hx; exact ⟨crd V x, hx, by simp⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [heq]
    refine ⟨hL.fg.map _, ?_⟩
    have hc : (↑(Submodule.map (f.toLinearMap.restrictScalars (𝓞 D.host.E)) V.L0) : Set (Fin V.rank → D.host.E)) =
        f.toLinearMap '' (V.L0 : Set V.V) := by ext; simp
    rw [hc, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]
  · have key : ∀ b : 𝓞 D.host.E, LinearMap.toSpanSingleton (𝓞 D.host.E) D.host.E 1 b = (b : D.host.E) := fun b => by
      simp [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
    have hU := V.baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU
    constructor
    · intro hy x hx
      have hy' : crd V y ∈ Formalism.E.hdual V.hT V.L0 := by rw [hU]; exact hy
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy'
      obtain ⟨b, hb⟩ := hy' (crd V x) hx
      exact ⟨b, by rw [← hT_crd, ← hb, key]⟩
    · intro h
      show crd V y ∈ V.L0
      rw [← hU]
      simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro z hz
      obtain ⟨b, hb⟩ := h ((crd V).symm z) (by simpa [l0s] using hz)
      refine ⟨b, ?_⟩
      rw [show z = crd V ((crd V).symm z) by simp, hT_crd, key]
      exact hb

end Formalism.IndefR.Fin.SelfDualLatticeFinitePlaces
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StdCharExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def invDiff (F : Type) [Field F] [NumberField F] : Set F :=
  {d | ∀ y : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (d * (y : F)) = z}

def invDiffAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {α | ∃ (n : ℕ) (d : Fin n → F) (x : Fin n → Af F), (∀ i, d i ∈ invDiff F) ∧ (∀ i, x i ∈ intAf F) ∧
    α = ∑ i, algebraMap F (Af F) (d i) * x i}

def StdCharExists (D : D7) : Prop :=
  (∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1)) ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ α : Af D.host.F,
      ((∀ x ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * x)) = 1) ↔ α ∈ invDiffAf D.host.F)

def CharComplete (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ S T : HSp D,
    (∀ x : WO S T, (∀ γ, ψ (symplO S T x (ratW T S γ)) = 1) → x ∈ ratL T S) ∧
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ φ : WO S T → ℂ, Continuous φ → (∀ γ w, φ (ratW T S γ + w) = φ w) →
        (∀ γ, ∫ w in 𝓕, φ w * ψ (symplO S T w (ratW T S γ)) ∂μ = 0) → φ = 0

def coefO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (f f' : WO S T → ℂ) (w : WO S T) : ℂ :=
  ∫ x in 𝓕, heisO ψ S T w f x * starRingEnd ℂ (f' x) ∂μ

def KernelId (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)),
    μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
    ∀ f₁ f₁' f₂ f₂' : WO S T → ℂ, IsThetaFunO ψ S T f₁ → IsThetaFunO ψ S T f₁' → IsThetaFunO ψ S T f₂ →
      IsThetaFunO ψ S T f₂' → (∀ w, coefO ψ S T μ 𝓕 f₁ f₁' w = coefO ψ S T μ 𝓕 f₂ f₂' w) →
      ∀ x y, f₁ y * starRingEnd ℂ (f₁' x) = f₂ y * starRingEnd ℂ (f₂' x)

def SvNSchurO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∀ A : Module.End ℂ (WO S T → ℂ),
    (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) →
    (∀ w₀ f, IsThetaFunO ψ S T f → A (heisO ψ S T w₀ f) = heisO ψ S T w₀ (A f)) →
    (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f →
        ∫⁻ w in 𝓕, ‖A f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → A f = c • f

def SvNSchurOAll (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ S T : HSp D, SvNSchurO ψ S T

end Formalism.IndefR.Fin

end
end

