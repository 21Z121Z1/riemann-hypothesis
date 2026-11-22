import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.Bundle0005

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrD

section Geometry

variable {k r : ℕ}

def InLieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) : Prop :=
  inLieLev k r (Fin.last r) X ∧ X *ᵥ z = 0

theorem exp_uw {z : Fin (2 * r + k + 1) → ℂ} {X : Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UWset k r z := by
  have h := Qx8.exp_lev hX.1 t
  exact ⟨h.1, fun a => h.2 a (by simp), Qx8.exp_fix hX.2 t⟩

theorem unitB_conj_mulVec {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ) (a b : Fin m)
    (v : Fin n → ℂ) (h : herm H v (Bs a) = 0) : (unitB H Bs a b)ᴴ *ᵥ (H *ᵥ v) = 0 := by
  ext q
  have h' : ∑ p, star (Bs a p) * (H *ᵥ v) p = 0 := h
  show ∑ p, star (Bs a p * (star (Bs b) ⬝ᵥ H *ᵥ bvec q)) * (H *ᵥ v) p = 0
  simp_rw [star_mul']
  rw [show ∑ p, star (Bs a p) * star (star (Bs b) ⬝ᵥ H *ᵥ bvec q) * (H *ᵥ v) p
      = star (star (Bs b) ⬝ᵥ H *ᵥ bvec q) * ∑ p, star (Bs a p) * (H *ᵥ v) p from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring, h', mul_zero]

theorem frame_lie {m : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a b : Fin m) :
    InLieW k r z (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      InLieW k r z (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) := by
  have hl := Qx8.unitB_lie Bs hB.1 (Fin.last r) a b
  have h0 : ∀ c, herm (Hpk k r) z (Bs c) = 0 := by
    intro c
    rw [← Qx2.herm_star, hB.2.2 c z (by simp), star_zero]
  have z1 : unitB (Hpk k r) Bs a b *ᵥ z = 0 := by
    rw [Qx8.unitB_mulVec, h0, zero_smul]
  have z2 : ((Hpk k r)⁻¹ * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r) *ᵥ z = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, unitB_conj_mulVec _ _ _ _ _ (h0 a), Matrix.mulVec_zero]
  refine ⟨⟨hl.1, ?_⟩, ⟨hl.2, ?_⟩⟩
  · unfold hpart1; rw [Matrix.smul_mulVec, Matrix.sub_mulVec, z1, z2]; simp
  · unfold hpart2; rw [Matrix.smul_mulVec, Matrix.add_mulVec, z1, z2]; simp

end Geometry

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def dOp (π : Mx k r → (W →L[ℂ] W)) (X : Mx k r) : W →L[ℂ] W :=
  deriv (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) 0

def ecOp (π : Mx k r → (W →L[ℂ] W)) (Z : Mx k r) : W →L[ℂ] W :=
  dOp π (hpart1 (Hpk k r) Z) + Complex.I • dOp π (hpart2 (Hpk k r) Z)

variable [FiniteDimensional ℂ W] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem dOp_hasDeriv (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) (dOp π X) 0 := by
  have hcont : Continuous fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    have h1 := Qx8.lcurve_cont X (1 : Mx k r)
    simp only [Matrix.mul_one] at h1
    exact hc.comp_continuous h1 (exp_uw hX)
  obtain ⟨A, hA⟩ := one_parameter_differentiable W (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)))
    (by simp [NormedSpace.exp_zero, hπ.1])
    (fun s t => by
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      rw [B5.exp_add', hπ.2 _ (exp_uw hX s) _ (exp_uw hX t)]) hcont
  exact (hA 0).differentiableAt.hasDerivAt

theorem dRep_eq (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) (v : W) : dRep π X v = dOp π X v := by
  have h := dOp_hasDeriv hπ hc hX
  have h2 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) (dOp π X v) 0 := by
    have := ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simpa [Function.comp_def] using this
  unfold dRep
  exact h2.deriv

theorem ecRep_eq (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z)) (v : W) :
    EcRep (Hpk k r) π Z v = ecOp π Z v := by
  unfold EcRep ecOp
  rw [dRep_eq hπ hc h1, dRep_eq hπ hc h2]
  rfl

end Rep

section Right

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem mem_right (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hgG.1, hh.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hh.2.1 a).1, (hh.2.1 a).2]
      exact hgG.2 a ha
  · have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ 1 ⟨1, h1z, 1, h1N, by simp⟩ h ⟨h, hh, 1, h1N, by simp⟩
    simpa using hS

theorem J_right (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg 1 h1z h hh
  rw [one_mul, mul_one, hπ'.1] at e1
  have e1' : π 1 ∘SL J g = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [one_mul] at e2
  rw [e2, ← ContinuousLinearMap.comp_assoc, e1']

theorem rd_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : RdV X F g = (J g).comp ((dOp π' X).comp B) := by
  have hfun : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => (J g).comp ((π' (NormedSpace.exp ((t : ℂ) • X))).comp B) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_right hD hg hu), J_right hπ' hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold RdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wq Wp) (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (J g).comp ((π' (NormedSpace.exp ((t : ℂ) • X))).comp B))
      ((J g).comp ((dOp π' X).comp B)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv

theorem rz_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((ecOp π' Z).comp B) := by
  unfold RZ
  rw [rd_right hD hπ' hc hJ hF h1 hg, rd_right hD hπ' hc hJ hF h2 hg]
  ext v
  simp [ecOp]

theorem fold_right (hD : IsDom k r z z' (Fin.last r) D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z' (hpart1 (Hpk k r) p.2) ∧ InLieW k r z' (hpart2 (Hpk k r) p.2)) :
    ∃ B : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r (Fin.last r) ∩ D,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
          (J g).comp B) ∧
      ∀ v, B v = (L.map fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v := by
  induction L with
  | nil => exact ⟨ContinuousLinearMap.id ℂ Wq, fun g _ => by simp, fun v => rfl⟩
  | cons p L ih =>
    obtain ⟨B', hB1, hB2⟩ := ih (fun q hq => hL q (by simp [hq]))
    obtain ⟨h1, h2⟩ := hL p (by simp)
    refine ⟨p.1 • B' + (ecOp π' p.2).comp B', fun g hg => ?_, fun v => ?_⟩
    · simp only [List.map_cons, List.foldr_cons, Pi.add_apply, Pi.smul_apply]
      rw [rz_right hD hπ' hc hJ hB1 h1 h2 hg, hB1 g hg]
      ext v
      simp
    · simp only [List.map_cons, List.foldr_cons, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
      rw [hB2 v, ecRep_eq hπ' hc h1 h2]

end Right

end QrD

theorem right_type_action : Formalism.FourierDecayAlt.Q.RightTypeAction := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ' hc J hJ g hg Bs hB w v
  unfold capR capRep qmF
  have key : ∀ σ : Equiv.Perm (Fin m), ∃ Bσ : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r (Fin.last r) ∩ D,
        ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
            (J g).comp Bσ) ∧
      ∀ v, Bσ v = ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v :=
    fun σ => QrD.fold_right hD hπ' hc hJ _ (by
      intro p hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j)
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at key
  choose Bf hBf1 hBf2 using key
  simp only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_zsmul, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hBf1 σ g hg, ContinuousLinearMap.comp_apply, hBf2 σ v]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictBoxOrder
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.StrictBoxOrder

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem box_strictAnti {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) : StrictAnti M := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ k =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have h1 := (h i.succ).2
    have h2 := (h i.castSucc).1
    rw [Fin.succ_castSucc] at h2
    exact lt_of_le_of_lt h1 h2

theorem sdec_shf {n : ℕ} (β : ℂ) {M : Fin n → ℤ} (h : StrictAnti M) : SDec (shf β M) := by
  intro a b hab
  have h1 := h hab
  refine ⟨(M a - M b - 1).toNat, ?_⟩
  simp only [shf]
  have h2 : ((M a - M b - 1).toNat : ℤ) = M a - M b - 1 := Int.toNat_of_nonneg (by omega)
  have h3 : (((M a - M b - 1).toNat : ℕ) : ℂ) = ((M a - M b - 1 : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, h2]
  rw [h3]
  push_cast
  ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def IsWt {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Prop := ∀ c, ∃ t : ℂ, E c c v = t • v

theorem isWt_vec {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hy : IsVec E y)
    (x : Fin n) (v : V) (h : IsWt E v) : IsWt E (y x v) := by
  intro c
  obtain ⟨t, ht⟩ := h c
  have e := congrArg (fun g : Module.End ℂ V => g v) (hy c c x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, ht, map_smul] at e
  by_cases hcx : c = x
  · subst hcx
    rw [if_pos rfl, LinearMap.neg_apply, sub_eq_iff_eq_add] at e
    refine ⟨t - 1, ?_⟩
    rw [e, sub_smul, one_smul]
    abel
  · rw [if_neg hcx, LinearMap.zero_apply, sub_eq_zero] at e
    exact ⟨t, e⟩

theorem list_prod_pres (P : V → Prop) (l : List (Module.End ℂ V)) (h : ∀ f ∈ l, ∀ v, P v → P (f v)) :
    ∀ v, P v → P (l.prod v) := by
  induction l with
  | nil => intro v hv; simpa using hv
  | cons f l ih =>
    intro v hv
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f (by simp) _ (ih (fun g hg => h g (by simp [hg])) v hv)

theorem pow_pres (P : V → Prop) (f : Module.End ℂ V) (h : ∀ v, P v → P (f v)) (k : ℕ) :
    ∀ v, P v → P ((f ^ k) v) := by
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (h v hv)

theorem isWt_mono {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hy : IsVec E y)
    (a : Fin n → ℕ) (v : V) (h : IsWt E v) : IsWt E (mono y a v) := by
  unfold mono
  refine list_prod_pres (IsWt E) _ (fun f hf => ?_) v h
  simp only [List.mem_ofFn, Set.mem_range] at hf
  obtain ⟨x, rfl⟩ := hf
  exact pow_pres (IsWt E) (y x) (fun w hw => isWt_vec hy x w hw) (a x)

theorem core (hESM : ExistsSingMax) (hCS : CapSing) (hSR : SubRel) (hTW : TopWeightSing) (hDM : DualMinor)
    (hST : SpanTop) (hMO : MultOne) [FiniteDimensional ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hgl : GlRel E) (hirr : Irr E)
    (m : Fin n → ℂ) (hm : SDec m) (O : Submodule ℂ V) (hO : Stab (subA E) O)
    (hS : Stab (subA E) (CapSp (subA E) m)) (hOq : ∀ w, ∀ v ∈ O, qdet (subA E) w v ∈ O)
    (hdis : Disjoint (CapSp (subA E) m) O) (htop : CapSp (subA E) m ⊔ O = ⊤)
    (S' : Submodule ℂ V) (hS'le : S' ≤ CapSp (subA E) m) (hS' : Stab (subA E) S') (hne : S' ≠ ⊥) :
    S' = CapSp (subA E) m := by
  by_contra hcon
  obtain ⟨hgl', -, hvec, -, -, -⟩ := hSR _ n E hgl
  obtain ⟨hglD, hmin⟩ := hDM V n (subA E) hgl'
  have hdis' := Submodule.disjoint_def.1 hdis

  have hT : S' ⊔ O ≠ ⊤ := by
    intro hT
    apply hcon
    apply le_antisymm hS'le
    intro s hs
    have h1 : s ∈ S' ⊔ O := by rw [hT]; trivial
    obtain ⟨s', hs', t, ht, rfl⟩ := Submodule.mem_sup.1 h1
    have ht2 : t ∈ CapSp (subA E) m := by
      have h2 := (CapSp (subA E) m).sub_mem hs (hS'le hs')
      simpa using h2
    rw [hdis' t ht2 ht, add_zero]; exact hs'
  have hTstab : Stab (subA E) (S' ⊔ O) := by
    intro a b v hv
    obtain ⟨s', hs', t, ht, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (hS' a b _ hs') (hO a b _ ht)

  have hAnn : (S' ⊔ O).dualAnnihilator ≠ ⊥ := by
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hT) inferInstance
    intro hbot
    apply hf0
    have h1 : f ∈ (S' ⊔ O).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      have h2 : f w ∈ (S' ⊔ O).map f := Submodule.mem_map_of_mem hw
      rw [hf] at h2
      exact (Submodule.mem_bot ℂ).1 h2
    rw [hbot] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  have hAnnStab : Stab (dualE (subA E)) (S' ⊔ O).dualAnnihilator := by
    intro a b ξ hξ
    rw [Submodule.mem_dualAnnihilator] at hξ ⊢
    intro v hv
    exact hξ _ (hTstab b a v hv)
  obtain ⟨μd, ξ, hξA, hξ0, hξHW, -⟩ := hESM (Module.Dual ℂ V) n (dualE (subA E)) hglD _ hAnnStab hAnn
  rw [Submodule.mem_dualAnnihilator] at hξA

  have hξC : ξ ∈ CapSp (dualE (subA E)) m := by
    rw [mem_CapSp]; intro w
    have h1 : qdet (dualE (subA E)) w = (qdet (subA E) w).dualMap := hmin n id id w
    rw [h1]
    ext v
    have hv : v ∈ CapSp (subA E) m ⊔ O := by rw [htop]; trivial
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, map_add]
    rw [mem_CapSp.1 hs w, hξA _ (Submodule.mem_sup_right (hOq w t ht)), hξA t (Submodule.mem_sup_right ht)]
    simp
  have hμ : ∀ j, μd j = m j + ((j : ℕ) : ℂ) :=
    (hCS (Module.Dual ℂ V) n (dualE (subA E)) m hglD
      (fun hb => hξ0 ((Submodule.mem_bot ℂ).1 (hb ▸ hξC)))).2 hm μd ξ hξC hξ0 hξHW

  have := hirr.1
  obtain ⟨ν, v₀, -, hv₀, hv₀HW, -⟩ := hESM V (n + 1) E hgl ⊤ (fun _ _ _ _ => trivial) top_ne_bot
  have hex : ∃ a, ξ (mono (yK E) a v₀) ≠ 0 := by
    by_contra hno
    push Not at hno
    refine hξ0 (hST V n E ν v₀ hgl hirr hv₀HW hv₀ ξ (fun a b hab v => ?_) hno)
    exact LinearMap.congr_fun (hξHW.2 b a hab) v
  obtain ⟨a, ha⟩ := hex
  have hv₀W : IsWt (subA E) v₀ := fun c => ⟨ν c.castSucc, hv₀HW.1 c.castSucc⟩
  have hxW : IsWt (subA E) (mono (yK E) a v₀) := isWt_mono hvec a v₀ hv₀W
  generalize mono (yK E) a v₀ = x at ha hxW
  have hxμ : ∀ c, subA E c c x = (m c + ((c : ℕ) : ℂ)) • x := by
    intro c
    obtain ⟨t, ht⟩ := hxW c
    have h1 : ξ (subA E c c x) = μd c * ξ x := LinearMap.congr_fun (hξHW.1 c) x
    rw [ht, map_smul, smul_eq_mul] at h1
    rw [ht, mul_right_cancel₀ ha h1, hμ]

  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (show x ∈ CapSp (subA E) m ⊔ O by rw [htop]; trivial)
  have hξs : ξ s ≠ 0 := by
    rw [← hst, map_add, hξA t (Submodule.mem_sup_right ht), add_zero] at ha
    exact ha
  have hsμ : ∀ c, subA E c c s = (m c + ((c : ℕ) : ℂ)) • s := by
    intro c
    have h1 := hxμ c
    rw [← hst, map_add, smul_add] at h1
    have h2 : subA E c c s - (m c + ((c : ℕ) : ℂ)) • s = -(subA E c c t - (m c + ((c : ℕ) : ℂ)) • t) := by
      rw [eq_neg_iff_add_eq_zero, ← sub_eq_zero.2 h1]
      abel
    have h3 : subA E c c s - (m c + ((c : ℕ) : ℂ)) • s ∈ CapSp (subA E) m :=
      Submodule.sub_mem _ (hS c c s hs) (Submodule.smul_mem _ _ hs)
    have h4 : subA E c c s - (m c + ((c : ℕ) : ℂ)) • s ∈ O := by
      rw [h2]
      exact O.neg_mem (O.sub_mem (hO c c t ht) (O.smul_mem _ ht))
    exact sub_eq_zero.1 (hdis' _ h3 h4)
  have hsHW := hTW V n (subA E) m hgl' hm s hs hsμ

  obtain ⟨ν', v', hv'S, hv'0, hv'HW, -⟩ := hESM V n (subA E) hgl' S' hS' hne
  have hν' := (hCS V n (subA E) m hgl'
    (fun hb => hv'0 ((Submodule.mem_bot ℂ).1 (hb ▸ hS'le hv'S)))).2 hm ν' v' (hS'le hv'S) hv'0 hv'HW
  have hν'' : ν' = fun a => m a + ((a : ℕ) : ℂ) := funext hν'
  rw [hν''] at hv'HW
  obtain ⟨c, hc⟩ := hMO V n E _ v' s hgl hirr hv'HW hsHW hv'0
  apply hξs
  rw [hc, map_smul, hξA v' (Submodule.mem_sup_left hv'S), smul_zero]

theorem sup_pres {ι : Type} (f : Module.End ℂ V) (F : ι → Submodule ℂ V) (p : ι → Prop)
    (h : ∀ j, ∀ v ∈ F j, f v ∈ F j) : ∀ v ∈ ⨆ (j) (_ : p j), F j, f v ∈ ⨆ (j) (_ : p j), F j := by
  have hle : (⨆ (j) (_ : p j), F j) ≤ (⨆ (j) (_ : p j), F j).comap f := by
    refine iSup₂_le (fun j hj => ?_)
    intro v hv
    exact (le_iSup₂ (f := fun j (_ : p j) => F j) j hj) (h j v hv)
  intro v hv
  exact hle hv

theorem box_indep (hCI : CapIndep) {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ) :
    iSupIndep (fun M : {M : Fin n → ℤ // Box L M} => CapSp E (shf β M.1)) := by
  have h := (hCI V n E β).comp
    (f := fun M : {M : Fin n → ℤ // Box L M} => (⟨M.1, box_strictAnti M.2⟩ : {M : Fin n → ℤ // StrictAnti M}))
    (by
      intro M M' hMM
      exact Subtype.ext (congrArg (fun z : {M : Fin n → ℤ // StrictAnti M} => z.1) hMM))
  exact h

end Formalism.FourierDecayAlt.P.StrictBoxOrder

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem qr_irredCap_of : Qr.ExistsSingMax → Qr.CapSing → Qr.CapStab → Qr.SubRel → Qr.TopWeightSing → Qr.DualMinor →
    Qr.SpanTop → Qr.MultOne → Qr.Decomp → Qr.CapIndep → Qr.IrredCap := by
  intro hESM hCS hCSt hSR hTW hDM hST hMO hDec hCI V _ _ _ n E β L hyp M hM S' hS'le hS'
  by_cases hne : S' = ⊥
  · exact Or.inl hne
  right
  have hgl' : GlRel (subA E) := (hSR _ n E hyp.gl).1
  have hind := StrictBoxOrder.box_indep hCI (subA E) β L
  have hsup : (⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA E) (shf β M.1)) = ⊤ := by
    rw [← (hDec V n E β L hyp).2, iSup_subtype]
  rw [iSup_split_single _ (⟨M, hM⟩ : {M : Fin n → ℤ // Box L M})] at hsup
  refine StrictBoxOrder.core hESM hCS hSR hTW hDM hST hMO E hyp.gl hyp.irr (shf β M) (StrictBoxOrder.sdec_shf β (StrictBoxOrder.box_strictAnti hM))
    (⨆ (j : {M : Fin n → ℤ // Box L M}) (_ : j ≠ ⟨M, hM⟩), CapSp (subA E) (shf β j.1)) ?_
    (hCSt V n (subA E) (shf β M) hgl').1 ?_ (hind ⟨M, hM⟩) hsup S' hS'le hS' hne
  · intro a b
    exact StrictBoxOrder.sup_pres (subA E a b) _ _ fun j v hv => (hCSt V n (subA E) (shf β j.1) hgl').1 a b v hv
  · intro w
    refine StrictBoxOrder.sup_pres (qdet (subA E) w) _ _ fun j v hv => ?_
    rw [mem_CapSp.1 hv w]
    exact Submodule.smul_mem _ _ hv

theorem qr_branchingAlg_of : Qr.Decomp → Qr.CapIndep → Qr.IrredCap → Qr.BranchingAlg := by
  intro hD hCI hIC V _ _ _ n E β L H
  obtain ⟨hne, htop⟩ := hD V n E β L H
  refine ⟨?_, fun M => ⟨hne M.1 M.2, fun S' hS' hst => hIC V n E β L H M.1 M.2 S' hS' hst⟩⟩
  have hind := StrictBoxOrder.box_indep hCI (subA E) β L
  have hsup : (⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA E) (shf β M.1)) = ⊤ :=
    iSup_subtype.trans htop
  first
  | exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  | exact DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top hind hsup

end Formalism.FourierDecayAlt.P
end
end

