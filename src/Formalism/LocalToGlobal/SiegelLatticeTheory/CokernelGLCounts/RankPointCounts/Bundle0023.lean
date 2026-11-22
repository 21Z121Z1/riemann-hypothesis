import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0018
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
section
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal

open Matrix

namespace Formalism.L2.SG.CovariantRepresentation

open Formalism.L2.SG.TermOp.Vanish in

def ShiftCore : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (R Γ : Subgroup G) [Countable Γ] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : G → V) (Ω : Set G) (h : G) (ν : Measure G),
    IsClosed (R : Set G) → Γ ≤ R → (∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) →
    (∀ r, r ∈ R ↔ h⁻¹ * r * h ∈ R) →
    SigmaFinite ν → ν ≠ 0 → ν (R : Set G)ᶜ = 0 → (∀ K : Set G, IsCompact K → ν K < ⊤) →
    (∀ r ∈ R, ν.map (fun x => r * x) = ν) → ν.map (fun x => x⁻¹) = ν → ν.map (fun x => h⁻¹ * x * h) = ν →
    (∀ r ∈ R, ∀ x, f (r * x) = f x) → IsSF (Γ : Set G) Ω → IntegrableOn f Ω μ →
    ∫ x in Ω, f x ∂μ = ∫ x in (fun x => h⁻¹ * x) '' Ω, f x ∂μ

open Formalism.L2.SG.TermOp.Vanish in

def FixNormC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∀ r, r ∈ Rset t ↔ h⁻¹ * r * h ∈ Rset t

open Formalism.L2.SG.TermOp.Vanish in

def RHaarC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∃ ν : Measure X.B.I.Ginf, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (Rset t)ᶜ = 0 ∧
      (∀ K : Set X.B.I.Ginf, IsCompact K → ν K < ⊤) ∧ (∀ r ∈ Rset t, ν.map (fun x => r * x) = ν) ∧
      ν.map (fun x => x⁻¹) = ν ∧ ν.map (fun x => h⁻¹ * x * h) = ν

section Plumb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

theorem rv_ratLink {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hl : RatLink X x γ)
    (v : InfinitePlace X.B.I.F) (y : (VS D).V) :
    uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (γ y)) := by
  obtain ⟨M, -, hx, -, hc⟩ := hl
  rw [hc, hx v]
  unfold rv
  have hw : (fun i => X.B.I.φ v (((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) i)) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *ᵥ
        fun i => X.B.I.φ v (X.crd y i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  by_cases hP : IsUnit (X.B.I.P v).det
  · rw [Matrix.mul_assoc _ (X.B.I.P v), Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hP]
    simp

theorem basis_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') (a : Fin D.R.rS) : X.eX a ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative FlagG.Xplus FlagG.X
  refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
  refine Submodule.subset_span ⟨a, ?_⟩
  show (X.Fu u).e a = X.eX a
  rw [X.Fu_e u]

theorem zu_mem_fixedSubspaceOfRepresentative (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : X.zu u ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative FlagG.Xplus
  refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
  show X.zu u ∈ Submodule.span D.host.E {(X.Fu u).z}
  rw [X.flagZVector u]
  exact Submodule.mem_span_singleton_self _

theorem frq_fl (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') :
    (frq X q).fl = mapFlag q.1.2 q.2.2.1 (X.Fu u') := by
  unfold frq mapLF
  split
  · rfl
  · exact absurd q.2.2.1 ‹_›

theorem ge_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') (a : Fin D.R.rS) : q.1.2 (X.eX a) ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative
  refine Submodule.mem_sup_right ?_
  rw [frq_fl]
  unfold FlagG.Xplus FlagG.X
  refine Submodule.mem_sup_left (Submodule.subset_span ⟨a, ?_⟩)
  show q.1.2 ((X.Fu u').e a) = q.1.2 (X.eX a)
  rw [X.Fu_e u']

theorem gz_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : q.1.2 (X.zu u') ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative
  refine Submodule.mem_sup_right ?_
  rw [frq_fl]
  unfold FlagG.Xplus
  refine Submodule.mem_sup_right ?_
  show q.1.2 (X.zu u') ∈ Submodule.span D.host.E {q.1.2 (X.Fu u').z}
  rw [X.flagZVector u']
  exact Submodule.mem_span_singleton_self _

theorem fix_rv {q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'} {h : X.B.I.Ginf} (hh : h ∈ pointwiseStabilizerInfinite X q)
    {y : (VS D).V} (hy : y ∈ fixedSubspaceOfRepresentative X q) (v : InfinitePlace X.B.I.F) :
    uMat (h v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd y) := by
  dsimp [pointwiseStabilizerInfinite, Hset] at hh
  first
  | exact hh _ ⟨y, hy, rfl⟩ v
  | exact hh v _ ⟨y, hy, rfl⟩
  | exact hh.2 _ ⟨y, hy, rfl⟩ v
  | exact hh.2 v _ ⟨y, hy, rfl⟩
  | (clear hy; done)

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by
  delta uMat
  simp

theorem fix'_rv {q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'} {h : X.B.I.Ginf} (hh : h ∈ pointwiseStabilizerInfinite X q)
    {y : (VS D).V} (hy : q.1.2 y ∈ fixedSubspaceOfRepresentative X q) (v : InfinitePlace X.B.I.F) :
    uMat ((q.1.1.1⁻¹ * h * q.1.1.1) v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd y) := by
  have h1 := rv_ratLink q.2.1 v y
  have h2 := fix_rv hh hy v
  have hm : uMat ((q.1.1.1⁻¹ * h * q.1.1.1) v) =
      uMat ((q.1.1.1 v)⁻¹) * uMat (h v) * uMat (q.1.1.1 v) := by
    delta uMat
    simp
  rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, ← h1, Matrix.mulVec_mulVec,
    uMat_inv_mul, Matrix.one_mulVec]

theorem inS_of_fix {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) : InS e z g := by
  delta InS
  exact ⟨fun a => by simp [Matrix.sub_mulVec, he], by simp [Matrix.sub_mulVec, hz]⟩

theorem rootCoord_fix {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) (a : Fin r) :
    rootCoord ε e f z g a = rootCoord ε e f z 1 a := by
  delta rootCoord
  have hn : g *ᵥ nxt e z a = nxt e z a := by
    delta nxt
    split <;> simp [he, hz]
  rw [hn, Matrix.one_mulVec]

theorem psiR_fix {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) :
    psiR ε gg e f z g = psiR ε gg e f z 1 := by
  delta psiR
  simp only [rootCoord_fix ε e f z g he hz]

theorem psiInfU_fix (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) :
    X.psiInfU u s = X.psiInfU u 1 := by
  dsimp [HidaSetting.psiInfU]
  delta psiInf
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [psiR_fix _ _ _ _ _ _ (he v) (hz v)]
  congr 1

theorem one_mem_SinfU (X : HidaSetting D) (u : D.what₂.Word) : (1 : X.B.I.Ginf) ∈ X.SinfU u := by
  dsimp [HidaSetting.SinfU, Sinf]
  intro v
  exact inS_of_fix _ _ _ (fun a => by delta uMat; simp) (by delta uMat; simp)

theorem psiInfU_one (X : HidaSetting D) (u : D.what₂.Word) : X.psiInfU u 1 = 1 := by
  have h1 : ∀ x, X.Wu u x = X.psiInfU u 1 • X.Wu u x := fun x => by
    have e : X.Wu u (1 * x) = X.psiInfU u 1 • X.piU u 1 (X.Wu u x) := (X.Wu_spec u).1 1 (one_mem_SinfU X u) x
    rwa [one_mul, (X.piU_rep u).1, ContinuousLinearMap.one_apply] at e
  by_contra hne
  have h0 : ∀ x, X.Wu u x = 0 := fun x => by
    have h2 : (1 - X.psiInfU u 1) • X.Wu u x = 0 := by rw [sub_smul, one_smul, ← h1 x, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have := (X.Wu_spec u).2.2.2.2
  simp [h0] at this

end Plumb

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.TermOp.Vanish

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

theorem comp_rk1 (A : V →L[ℂ] V) (v : V) (w : V') : A.comp (rk1 v w) = rk1 (A v) w := by
  ext x
  simp [rk1, map_smul]

theorem rankOne_map_left_eq_comp (B : V' ≃ₗᵢ[ℂ] V') (v : V) (w : V') :
    (rk1 v w).comp (B.toContinuousLinearEquiv : V' →L[ℂ] V') = rk1 v (B.symm w) := by
  ext x
  simp only [rk1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  congr 1
  simp
  rw [← B.inner_map_map (B.symm w) x, LinearIsometryEquiv.apply_symm_apply]

end Gen

variable {D : D7} (X : HidaSetting D)

def piIsoT (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u :=
  ((X.piU u s).toLinearMap.isometryOfInner (fun x y => (X.piU_rep u).2.2.1 s hs x y)).toLinearIsometryEquiv rfl

variable {X}

end Main

end Formalism.L2.SG.CovariantRepresentation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlueFwdOf
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Fwd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

set_option maxHeartbeats 800000 in
theorem glueFwd_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) (hE : GlueEta M r) :
    GlueFwd M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ hG₂ hTh
  set t₂ : Term V M r := { abelian₂ := Λ₂, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V),
      w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O) :=
    fun _ _ _ => Iff.rfl
  have memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f') :=
    fun _ _ => Iff.rfl
  have hDl : IsUnit (H.Dl f₂ f₂' (r + 1)) := by
    obtain ⟨⟨_, _, _, hD, _⟩, _⟩ := hG₂
    exact hD
  have hG₁ : H.IsGeneric t₁ := by
    obtain ⟨h, -⟩ := id hT
    exact h
  obtain ⟨ψ, hψh, hψC⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hDl
  have key : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ Λ₂ :=
    fun x hx => hTh x _ ((hψC x _).2 ⟨hx, rfl⟩)
  obtain ⟨η₁, hη₁a, hη₁b⟩ := hE hM V H t₁ hG₁
  obtain ⟨η₂, hη₂a, hη₂b⟩ := hE hM V H t₂ hG₂
  have fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)),
      (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₂ (ThL H t₂) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h1 : (ψ (ψ.symm ⟨n, hnW⟩) : V) = n := by simp
    rw [← h1, hψh]
    refine ((memS _ _ _).1 hw).2 _ ((memL _ _).2 ⟨?_, (ψ.symm ⟨n, hnW⟩).2⟩)
    exact (key _ (ψ.symm ⟨n, hnW⟩).2).2 (by simpa [ht₂] using hnΛ)
  have bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₂ (ThL H t₂)),
      (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h2 := hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ((memS _ _ _).1 hw).2 _ ((memL _ _).2 ⟨(key n hnW).1 hnΛ, (ψ ⟨n, hnW⟩).2⟩)
  let e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₂ (ThL H t₂) :=
    { toFun := fun w => ⟨_, fwd w.1 w.2⟩
      invFun := fun w => ⟨_, bwd w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
        exact h
      map_smul' := by
        intro c a
        apply Subtype.ext
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)
        exact h
      left_inv := by
        intro a
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  have hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₂ (ThL H t₂))
      (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) =
      Submodule.comap (ThSharp H t₂ (ThL H t₂)).subtype (ThL H t₂) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, -⟩ := (memL _ _).1 hy
      exact (memL _ _).2 ⟨(key _ _).1 h1, (ψ _).2⟩
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      obtain ⟨h1, -⟩ := (memL _ _).1 hx
      refine (memL _ _).2 ⟨?_, (ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩).2⟩
      exact (key _ (ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩).2).2 (by simpa [ht₂] using h1)
  let κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₂ (ThL H t₂) := Submodule.Quotient.equiv _ _ e hPQ
  have hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₂ (ThL H t₂) (e w) := fun w => rfl
  have surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))
    exact ⟨w, hw.symm⟩
  have hh : ∀ a b : ThSharp H t₁ (ThL H t₁), H.h (e a : V) (e b : V) = H.h a b :=
    fun a b => hψh ⟨a, ((memS _ _ _).1 a.2).1⟩ ⟨b, ((memS _ _ _).1 b.2).1⟩
  refine ⟨(η₁.trans κ).trans η₂.symm, ?_, ?_⟩
  · intro x y x₂ y₂ hx hy
    obtain ⟨w, hw⟩ := surj x
    obtain ⟨w', hw'⟩ := surj y
    change η₂.symm (κ (η₁ (ddMk H t₁ x))) = _ at hx
    change η₂.symm (κ (η₁ (ddMk H t₁ y))) = _ at hy
    have hx' := (LinearEquiv.symm_apply_eq η₂).1 hx
    have hy' := (LinearEquiv.symm_apply_eq η₂).1 hy
    rw [hw, hκ] at hx'
    rw [hw', hκ] at hy'
    have a1 := hη₁b x y w w' hw hw'
    have a2 := hη₂b x₂ y₂ (e w) (e w') hx'.symm hy'.symm
    rw [hh] at a2
    have a3 := sub_mem a2 a1
    convert a3 using 1
    ring
  · intro m₁ m₂
    obtain ⟨w, hw⟩ := surj m₁
    have hmw : (m₁ : V) + w ∈ t₁.abelian₂ := (hη₁a m₁ w).1 hw
    change η₂.symm (κ (η₁ (ddMk H t₁ m₁))) = _ ↔ _
    rw [hw, hκ]
    constructor
    · intro h
      have h' := (LinearEquiv.symm_apply_eq η₂).1 h
      exact ⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, (hη₂a m₂ (e w)).1 h'.symm⟩
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψC n₁ n₂).1 hc
      have hd : n₁ - w ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1
      have hdL : n₁ - w ∈ t₁.abelian₂ := by
        have h4 := t₁.abelian₂.sub_mem h1 hmw
        simpa using h4
      have hψd : (ψ ⟨n₁ - w, hd⟩ : V) = n₂ - (e w : V) := by
        rw [← hψn]
        exact congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)
      have h3 := (key _ hd).1 hdL
      rw [hψd] at h3
      have h5 := Λ₂.sub_mem h2 h3
      have h6 : (m₂ : V) + (e w : V) ∈ t₂.abelian₂ := by
        convert h5 using 1
        abel
      apply (LinearEquiv.symm_apply_eq η₂).2
      exact ((hη₂a m₂ (e w)).2 h6).symm

end Fwd

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBDefs
section
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Local

variable {D : Formalism.BasicNotions.D7}

abbrev MatP (D : Formalism.BasicNotions.D7) (p : PlF D) : Type :=
  Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ)

def kkOrb (p : PlF D) (Y : MatP D p) : Set (MatP D p) :=
  {Y' | ∃ l ρ : MatP D p, Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧ Y' = l * Y * ρ}

def IntP (p : PlF D) (Y : MatP D p) : Prop := ∀ a b, Y a b ∈ (M p).R

def InOrbP (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Prop :=
  ∃ w₀, modPt δ T T' p w = some w₀ ∧
    ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2

def phL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℂ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    if h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 then
      dfac M δ T T' p w *
        (M p).psiR (Loc.simpleLow (Loc.uLow h.choose.1) + Loc.simpleUp (Loc.uUp w₀ h.choose.2))
    else 0

def wtL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℝ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    (((Measure.pi fun _ : Loc.IL (D.R.rS + 1) => (M p).mu).prod (Measure.pi fun _ : Loc.IN w₀ => (M p).mu))
      {xy | Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y}).toReal

def thL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Option ((M p).Cls D.R.rS) :=
  clsOf (M p) (Y + Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0)

def nIsoO (p : PlF D) (o o' : Option ((M p).Cls D.R.rS)) : ℕ :=
  match o, o' with
  | some c, some c' => (M p).nIso (Quotient.out c) (Quotient.out c')
  | _, _ => 0

def IsLCls (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : Prop :=
  ∃ Y, IntP M p Y ∧ InOrbP δ T T' p w Y ∧ O = kkOrb M p Y

def repL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : MatP D p :=
  if h : IsLCls M δ T T' p w O then h.choose else 0

def fL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ) *
      (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ)
  else 0

def gL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def hL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def kL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ) else 0

def eL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then 1 else 0

def sgnP (p : PlF D) : MatP D p := Matrix.diagonal fun b : Fin (D.R.rS + 1) => (-1) ^ (D.R.rS - b.val)

def x0L (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Set (MatP D p) := kkOrb M p (modMat δ T T' p w)

end Local

section Glob

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def nrep (γ : TermDef.Term D u u' F0 what₂) :
    Option (Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D) :=
  if h : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 then some h.choose else none

def zT (γ : TermDef.Term D u u' F0 what₂) : PairVal.MatR D :=
  match nrep γ with
  | some x => ZhatL (lf D F0) x.2.1
  | none => 0

def ptT (γ : TermDef.Term D u u' F0 what₂) : Point D.host.E (D.R.rS + 1) :=
  match nrep γ with
  | some x => x.1
  | none => PairVal.junkPoint D u u'

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)

def thT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Option ((M p).Cls D.R.rS) :=
  thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ))

def locT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Set (MatP D p) :=
  kkOrb M p (CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p)

def dnT (L : CntLocal.LocSp D M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (γ : TermDef.Term D u u' F0 what₂) : ℝ :=
  ∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') (zT γ) p

end Glob

end Formalism.L2.SG.LsDatumB
end
end

