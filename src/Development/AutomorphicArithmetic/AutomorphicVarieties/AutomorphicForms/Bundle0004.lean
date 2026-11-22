import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import GroundTheory.AutomorphicForms.AdelicGLn

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped TensorProduct

namespace UpperTheory.V.TR

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in

def regFun : Subalgebra ℂ (GL (Fin a) (Rinf E) → ℂ) :=
  Algebra.adjoin ℂ ({f | ∃ v i j, f = fun y => ((y.val i j v : ℝ) : ℂ)} ∪ {f | ∃ v, f = fun y => ((y.val.det v : ℝ) : ℂ)⁻¹})

variable (E a) in

structure AlgRep where

  d : ℕ

  mat : GL (Fin a) (Rinf E) →* Matrix (Fin d) (Fin d) ℂ
  reg : ∀ i j, (fun y => mat y i j) ∈ regFun E a
  pos : 0 < d
  irred : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

open Classical in

def extGL (f : GL (Fin a) (Rinf E) → ℂ) (x : Lie E a) : ℂ := if h : IsUnit (Matrix.of x) then f h.unit else 0

def AlgRep.dmat (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun X := Matrix.of fun i j => fderiv ℝ (extGL fun y => Ξ.mat y i j) (oneL E a) X
  map_add' X Y := by ext i j; simp
  map_smul' c X := by ext i j; simp

open Classical in

def AlgRep.HasInfChar (Ξ : AlgRep E a) (v : InfinitePlace E) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => Ξ.dmat (toL (Matrix.single i j (Pi.single v 1)))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

variable (E a) in

def AlgRep.triv : AlgRep E a where
  d := 1
  mat := 1
  reg i j := Subalgebra.algebraMap_mem _ ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j)
  pos := one_pos
  irred W _ := by
    have : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
    exact eq_bot_or_eq_top W

variable (E a) in

abbrev Herm : Submodule ℝ (Matrix (Fin a) (Fin a) (Rinf E)) := selfAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) (Rinf E))

def adHerm (k : Kinf E a) (X : Herm E a) : Herm E a := ⟨k.1 * X.1 * star k.1, IsSelfAdjoint.conjugate X.2 k.1⟩

section Complex

omit [NumberField E]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

def IsCochain {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Prop :=
  ∀ (k : Kinf E a), k.1.det = 1 → ∀ X : Fin q → Herm E a, ω (fun i => adHerm k (X i)) = κ k (ω X)

def dCo {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L (toL X.1)).restrictScalars ℝ).compAlternatingMap ω
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L (toL X.1) (toL Y.1)) (ω v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c (toL X.1)) (ω v) }

def HasCohomology : Prop :=
  (∃ ω : Herm E a [⋀^Fin 0]→ₗ[ℝ] M, IsCochain κ ω ∧ dCo L ω = 0 ∧ ω ≠ 0) ∨
    ∃ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M), IsCochain κ ω ∧ dCo L ω = 0 ∧
      ∀ η : Herm E a [⋀^Fin q]→ₗ[ℝ] M, IsCochain κ η → dCo L η ≠ ω

end Complex

variable [IsTotallyReal E]

def lieOp (π : CuspSub E a) : Lie E a →ₗ[ℝ] Module.End ℂ π.V where
  toFun X := π.op (.lie X)
  map_add' X Y := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (map_add (lie E a) X Y) φ.1)
  map_smul' c X := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (map_smul (lie E a) c X) φ.1)

def tensorK (π : CuspSub E a) (Ξ : AlgRep E a) (k : Kinf E a) : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  TensorProduct.map (π.op (.cpt k)) (Matrix.toLin' (Ξ.mat (Unitary.toUnits k)))

def tensorLie (π : CuspSub E a) (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lieOp π X).rTensor _ + (Matrix.toLin' (Ξ.dmat X)).lTensor _
  map_add' X Y := by simp only [map_add, LinearMap.rTensor_add, LinearMap.lTensor_add]; abel
  map_smul' c X := by
    rw [map_smul, map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lieOp π X), ← algebraMap_smul ℂ c (Ξ.dmat X),
      ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), map_smul,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]

def IsCohFor (π : CuspSub E a) (Ξ : AlgRep E a) : Prop := HasCohomology (tensorK π Ξ) (tensorLie π Ξ)

variable (E a) in

def GLplus : Subgroup (GL (Fin a) E) where
  carrier := {γ | ∀ τ : E →+* ℝ, 0 < τ γ.val.det}
  one_mem' τ := by simp
  mul_mem' {x y} hx hy τ := by simpa [Matrix.det_mul] using mul_pos (hx τ) (hy τ)
  inv_mem' {x} hx τ := by
    have h : τ (x⁻¹).val.det * τ x.val.det = 1 := by rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul]; simp
    have h2 := hx τ
    by_contra h3
    nlinarith [not_lt.1 h3]

def AlgRep.rat (Ξ : AlgRep E a) : GL (Fin a) E →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  Ξ.mat.comp ((GeneralLinearGroup.map (pInf E)).comp (ratGL E a))

end UpperTheory.V.TR

namespace UpperTheory.V.Af

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def levelRep (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ ↥Γ ((GL (Fin a) (Af E) ⧸ U) → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f x => ξ γ *ᵥ f ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1)⁻¹ • x)
      map_add' := fun f g => funext fun x => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun x => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f x; simp
  map_mul' γ δ := by ext f x; simp [mul_smul]

def cohDim (Γ : Subgroup (GL (Fin a) E)) (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ}
    (ξ : GL (Fin a) E →* Matrix (Fin d) (Fin d) ℂ) : Cardinal :=
  Cardinal.sum fun q : ℕ => Module.rank ℂ (groupCohomology (Rep.of (levelRep Γ U ξ)) q)

variable [IsTotallyComplex E]

def ratC (Ξ : GlobalTheory.GKCoh.AlgRep E a) : GL (Fin a) E →* Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  Ξ.mat.comp ((GeneralLinearGroup.map (pInf E)).comp (ratGL E a))

omit [IsTotallyComplex E] in

def AlgInfChar (Ξ : GlobalTheory.GKCoh.AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun i j => (1 / 2 : ℂ) • (Ξ.dmat (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • Ξ.dmat (toL (Matrix.single i j (atEmb τ Complex.I))))) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def IsFinComp (π : CuspSub E a) (σ : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.finPart g (f v)

omit [IsTotallyComplex E] in

def IsConjBy (σ : ℂ ≃+* ℂ) (τ τ' : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ T : τ.V ≃+ τ'.V, (∀ (c : ℂ) v, T (c • v) = σ c • T v) ∧ ∀ g v, T (τ.ρ g v) = τ'.ρ g (T v)

end UpperTheory.V.Af
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af

variable {F : Type} [Field F] [NumberField F] {n M N : ℕ}

theorem mem_Ohat {x : Af F} : x ∈ Ohat F ↔ x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  rw [GroundTheory.Global.mem_integralFiniteAdeles, Ohat, Subring.mem_iInf]
  rfl

theorem mem_KLev {g : GL (Fin n) (Af F)} :
    g ∈ KLev F n M ↔ (∀ a b, g a b ∈ Ohat F) ∧ (∀ a b, (g⁻¹ : GL (Fin n) (Af F)) a b ∈ Ohat F) ∧
      ∀ a b, ∃ y ∈ Ohat F, g a b - (1 : Matrix (Fin n) (Fin n) (Af F)) a b = (M : Af F) * y := by
  have h1 : ∀ a b, (((1 : Matrix (Fin n) (Fin n) ↥(Ohat F)) a b : ↥(Ohat F)) : Af F) =
      (1 : Matrix (Fin n) (Fin n) (Af F)) a b := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> rfl
  have h2 : ∀ a b, (1 : Matrix (Fin n) (Fin n) (↥(Ohat F) ⧸ Ideal.span {(M : ↥(Ohat F))})) a b =
      Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) ↥(Ohat F)) a b) := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun a b => (k a b).2, fun a b => ?_, fun a b => ?_⟩
    · rw [← map_inv]; exact ((k⁻¹ : GL (Fin n) ↥(Ohat F)) a b).2
    · have e : Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}) (k a b) = _ :=
        (congrArg (fun x : GL (Fin n) (↥(Ohat F) ⧸ Ideal.span {(M : ↥(Ohat F))}) => x a b) hk).trans (h2 a b)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 e)
      refine ⟨y, y.2, ?_⟩
      rw [← h1]
      exact congrArg Subtype.val hy
  · rintro ⟨ha, hb, hc⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) (Ohat F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin n) ↥(Ohat F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin n) (Af F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, ?_, Units.ext rfl⟩
    refine Units.ext (Matrix.ext fun a b => ?_)
    refine Eq.trans ?_ (h2 a b).symm
    obtain ⟨y, hy, e⟩ := hc a b
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨⟨y, hy⟩, Subtype.ext ?_⟩)
    rw [← h1] at e
    exact e

theorem KLev_le_of_dvd (h : M ∣ N) : KLev F n N ≤ KLev F n M := by
  obtain ⟨c, rfl⟩ := h
  intro g hg
  obtain ⟨ha, hb, hc⟩ := mem_KLev.1 hg
  refine mem_KLev.2 ⟨ha, hb, fun a b => ?_⟩
  obtain ⟨y, hy, e⟩ := hc a b
  exact ⟨c * y, mul_mem (natCast_mem _ c) hy, by rw [e, Nat.cast_mul, mul_assoc]⟩

theorem KLev_le_integral : KLev F n M ≤ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL F n := fun _ hg =>
  (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff F n).2
    ⟨fun a b => mem_Ohat.1 ((mem_KLev.1 hg).1 a b), fun a b => mem_Ohat.1 ((mem_KLev.1 hg).2.1 a b)⟩

theorem isOpen_Ohat : IsOpen (Ohat F : Set (Af F)) := by
  convert GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F) using 1
  exact Set.ext fun _ => mem_Ohat

theorem isOpen_KLev (hM : 1 ≤ M) : IsOpen (KLev F n M : Set (GL (Fin n) (Af F))) := by
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set u : Af F := algebraMap F (Af F) (M : F)⁻¹
  have hu : u * M = 1 := by rw [← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hM', map_one]
  have e : (KLev F n M : Set (GL (Fin n) (Af F))) =
      (⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => g a b) ⁻¹' Ohat F) ∩
      ((⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => (g⁻¹ : GL (Fin n) (Af F)) a b) ⁻¹' Ohat F) ∩
      ⋂ a, ⋂ b, (fun g : GL (Fin n) (Af F) => u * (g a b - (1 : Matrix (Fin n) (Fin n) (Af F)) a b)) ⁻¹' Ohat F) := by
    ext g
    simp only [SetLike.mem_coe, mem_KLev, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun a b => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
    · rintro ⟨y, hy, e⟩
      rwa [e, ← mul_assoc, hu, one_mul]
    · rw [← mul_assoc, mul_comm _ u, hu, one_mul]
  rw [e]
  have c : ∀ a b, Continuous fun g : GL (Fin n) (Af F) => g a b := fun a b =>
    Continuous.matrix_elem Units.continuous_val a b
  refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_) <;>
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => isOpen_Ohat.preimage ?_
  · exact c a b
  · exact (c a b).comp continuous_inv
  · exact continuous_const.mul ((c a b).sub continuous_const)

theorem isCompact_KLev (hM : 1 ≤ M) : IsCompact (KLev F n M : Set (GL (Fin n) (Af F))) :=
  (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL F n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_KLev hM)) KLev_le_integral

theorem HasFixed.mono {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V} {U U' : Subgroup Γ}
    (h : HasFixed ρ U) (hU : U' ≤ U) : HasFixed ρ U' :=
  let ⟨v, h0, hv⟩ := h
  ⟨v, h0, fun u hu => hv u (hU hu)⟩

end UpperTheory.V.Af
end
end

