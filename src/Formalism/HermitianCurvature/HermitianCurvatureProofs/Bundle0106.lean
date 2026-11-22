import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0099

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NotCdomRaiseOfLt
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

theorem not_cdom_raise_of_lt {k : ℕ} {Λ : Fin k → ℝ} {a b : Fin k} (hab : a < b)
    (h : PI.UpqRep.CDom (PI.UpqRep.allPos k)
      (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) Λ) : False := by
  obtain ⟨c, hc, heq⟩ := h
  have hsing : ∀ p : Fin k, ∑ j : Fin k, ((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j = ((p : ℕ) : ℝ) := by
    intro p
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have e1 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (Λ - fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) j =
      ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have hj : ∀ j : Fin k,
        (Λ - fun c => Λ c + (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) j =
          (Pi.single b (1 : ℝ) : Fin k → ℝ) j - (Pi.single a (1 : ℝ) : Fin k → ℝ) j := by
      intro j
      simp only [Pi.sub_apply, Pi.single_apply]
      ring
    simp only [hj, mul_sub, Finset.sum_sub_distrib, hsing]
  have e2 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j ≤ 0 := by
    have hj : ∀ j : Fin k, ((j : ℕ) : ℝ) * (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j =
        ∑ p, ∑ q, (c p q : ℝ) * (((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j -
          ((j : ℕ) : ℝ) * (Pi.single q (1 : ℝ) : Fin k → ℝ) j) := by
      intro j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PI.UpqRep.root, Pi.sub_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    apply Finset.sum_nonpos
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_nonpos
    intro q _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsing, hsing]
    by_cases h0 : c p q = 0
    · simp [h0]
    · have hpq : ((p : ℕ) : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast (hc p q h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [heq] at e1
  linarith

theorem core {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} {g : Mx k r} {u : Fin k → ℝ}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : IsRepW k r z π) (hgU : g ∈ UH (Hpk k r))
    (hgfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (s : ℂ) (hgz : g *ᵥ (s • bvec (wI k r (Fin.last k))) = z)
    (hK : PI.UpqRep.IsKTypeOf (PI.UpqRep.allPos k) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) u) ⊤) (w : ℂ) (v : W) :
    qdet (EB π (fr k r g)) w v =
      cpol (fun j : Fin k => ((PI.UpqRep.lowK (PI.UpqRep.allPos k) u j : ℝ) : ℂ) - ((j : ℕ) : ℂ)) w • v := by
  set Bs := fr k r g with hBs
  have hB : IsFrameOf k r [z] Bs := fr_frame hgU hgfix s hgz
  set Λ := PI.UpqRep.lowK (PI.UpqRep.allPos k) u with hΛ
  set E := EB π Bs with hE
  have hgl : GlRel E := (frame_general_linear W k r k z π Bs hR hB).1
  set Ec : Fin k → (W →L[ℂ] W) := fun c => ecOp π (unitB (Hpk k r) Bs c c) with hEc
  have hEE : ∀ c x, E c c x = Ec c x := fun c x => rfl
  have hσ : ∀ θ : Fin k → ℝ, π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) =
      NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • Ec c) := by
    intro θ
    rw [← torus hgU θ]
    exact op_torus hR hB θ
  obtain ⟨-, -, hirr, ⟨v₀, -, hv0, hwt⟩, hdom⟩ := hK

  have hdiag : ∀ c, E c c v₀ = (Λ c : ℂ) • v₀ := by
    intro c
    set A := hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef
    have hA : InLieW k r z A := (QrD.frame_lie hB c c).2
    have hAe : A = (-Complex.I) • unitB (Hpk k r) Bs c c := hpart2_self Bs c
    have hf : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • A)) v₀) =
        fun t : ℝ => Complex.exp (((-t * Λ c : ℝ) : ℂ) * Complex.I) • v₀ := by
      funext t
      set θ : Fin k → ℝ := fun c' => if c' = c then -t else 0 with hθ
      have h1 : (t : ℂ) • A = ∑ c', ((θ c' : ℂ) * Complex.I) • unitB (Hpk k r) Bs c' c' := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        rw [hAe, smul_smul]
        congr 1
        simp only [hθ, if_pos rfl]
        push_cast
        ring
      have hsθ : ∑ a, Λ a * θ a = -t * Λ c := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        simp only [hθ, if_pos rfl]
        ring
      rw [h1, torus hgU θ]
      refine (hwt θ (Dg_mem θ)).trans ?_
      rw [hsθ]
    have hd : dOp π A v₀ = (-(Λ c : ℂ) * Complex.I) • v₀ := by
      rw [← QrD.dRep_eq hR.1 hR.2 hA v₀]
      unfold dRep
      rw [hf]
      exact (deriv_cexp (Λ c) v₀).deriv
    rw [hEE]
    show ecOp π (unitB (Hpk k r) Bs c c) v₀ = _
    unfold ecOp
    rw [hpart1_self, SkewHermitianParts.dOp_zero, zero_add, _root_.smul_apply, hd, smul_smul]
    congr 1
    linear_combination (-(Λ c : ℂ)) * Complex.I_sq

  have hup : ∀ a b, a < b → E a b v₀ = 0 := by
    intro a b hab
    by_contra hne
    set x := E a b v₀ with hx
    have hxw : ∀ c, Ec c x = (((fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) c : ℝ) : ℂ) • x := by
      intro c
      rw [← hEE, hx, CommonEigenvectors.diag_move hgl c a b v₀, hdiag c, map_smul]
      by_cases hca : c = a <;> by_cases hcb : c = b
      · exact absurd (hca.symm.trans hcb) hab.ne
      · rw [if_pos hca, if_neg (fun h => hcb h.symm)]
        simp only [if_pos hca, if_neg hcb]
        push_cast
        module
      · rw [if_neg hca, if_pos hcb.symm]
        simp only [if_neg hca, if_pos hcb]
        push_cast
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm)]
        simp only [if_neg hca, if_neg hcb]
        push_cast
        module
    have hwx : PI.UpqRep.IsWtOn (PI.UpqRep.Kset (PI.UpqRep.allPos k)) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
        (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) x := by
      intro θ _
      show π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) x = _
      rw [hσ θ]
      exact exp_sum_eig Ec θ _ x hxw
    exact not_cdom_raise_of_lt hab (hdom _ x Submodule.mem_top hne hwx)

  have hHW : IsHW E (fun j => (Λ j : ℂ)) v₀ := ⟨hdiag, hup⟩
  set m : Fin k → ℂ := fun j => (Λ j : ℂ) - ((j : ℕ) : ℂ) with hm
  have hq0 : ∀ w', qdet E w' v₀ = cpol m w' • v₀ := by
    intro w'
    rw [quantumDetHighestWeight_holds W k E _ v₀ hgl hHW w']
    congr 1
    unfold cpol
    apply Finset.prod_congr rfl
    intro j _
    simp only [hm]
    ring
  have hmem : v₀ ∈ CapSp E m := mem_CapSp.2 hq0
  have hstab : Stab E (CapSp E m) := (capelli_stabilizer W k E m hgl).1
  have hirrE : ∀ S : Submodule ℂ W, Stab E S → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hU := lie_stabilizer W k r z π Bs hz hT hR hB S hS
    refine hirr S le_top ?_
    intro h hh y hy
    have hu : hᴴ * h = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hU _ (emb_uw hgU hgfix s hgz hu) y hy
  have htop : CapSp E m = ⊤ := by
    rcases hirrE _ hstab with h | h
    · exfalso
      rw [h] at hmem
      exact hv0 ((Submodule.mem_bot ℂ).1 hmem)
    · exact h
  have hv : v ∈ CapSp E m := by
    rw [htop]
    exact Submodule.mem_top
  exact mem_CapSp.1 hv w

end QrCap

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionUnitary
section
open Matrix Filter Topology Set
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.RadicalReductionUnitary

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD Formalism.FourierDecayAlt.P.NFRadRedL

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k r : ℕ}

theorem inv_eq_ring_inverse (A : Q.Mx k r) : A⁻¹ = Ring.inverse A := by
  first
    | exact Matrix.nonsing_inv_eq_ringInverse A
    | exact Matrix.nonsing_inv_eq_ring_inverse A

def lieU (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Q.Mx k r) where
  carrier := {X | InLieW k r z X}
  zero_mem' := ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩
  add_mem' := by
    rintro X Y ⟨⟨hX1, hX2⟩, hX3⟩ ⟨⟨hY1, hY2⟩, hY3⟩
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
          (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX1, hY1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).1, (hY2 a ha).1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).2, (hY2 a ha).2, add_zero]
    · rw [Matrix.add_mulVec, hX3, hY3, add_zero]
  smul_mem' := by
    rintro c X ⟨⟨hX1, hX2⟩, hX3⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_smul]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).2, smul_zero]
    · rw [Matrix.smul_mulVec, hX3, smul_zero]

theorem cinv_eq (g : Q.Mx k r) : cinv g = Ring.inverse (g + 1) * (g - 1) := by
  rw [cinv, inv_eq_ring_inverse]

theorem cinv_contDiffAt {g : Q.Mx k r} (hu : IsUnit (g + 1)) : ContDiffAt ℝ ∞ cinv g := by
  have h1 : ContDiffAt ℝ ∞ (fun x : Q.Mx k r => Ring.inverse (x + 1)) g := by
    obtain ⟨u, hu⟩ := hu
    have : ContDiffAt ℝ ∞ Ring.inverse (u : Q.Mx k r) := contDiffAt_ringInverse ℝ u
    rw [hu] at this
    exact this.comp g (contDiffAt_id.add contDiffAt_const)
  have h2 : ContDiffAt ℝ ∞ (fun x : Q.Mx k r => x - 1) g := contDiffAt_id.sub contDiffAt_const
  have : (cinv : Q.Mx k r → Q.Mx k r) = fun x => Ring.inverse (x + 1) * (x - 1) := funext cinv_eq
  rw [this]
  exact h1.mul h2

theorem two_mul_half : ((1 : Q.Mx k r) + 1) * ((1 / 2 : ℂ) • 1) = 1 := by
  rw [mul_smul_comm, mul_one, ← two_smul ℂ (1 : Q.Mx k r), smul_smul]
  norm_num

theorem half_mul_two : ((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (1 + 1) = 1 := by
  rw [smul_mul_assoc, one_mul, ← two_smul ℂ (1 : Q.Mx k r), smul_smul]
  norm_num

def twoU (k r : ℕ) : (Q.Mx k r)ˣ := ⟨1 + 1, (1 / 2 : ℂ) • 1, two_mul_half, half_mul_two⟩

theorem cinv_hasFDerivAt_one :
    HasFDerivAt (cinv : Q.Mx k r → Q.Mx k r) (ContinuousLinearMap.mul ℝ (Q.Mx k r) ((1 / 2 : ℂ) • 1)) 1 := by
  have hinv : Ring.inverse ((1 : Q.Mx k r) + 1) = (1 / 2 : ℂ) • 1 := Ring.inverse_unit (twoU k r)
  have h1 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (twoU k r)).comp (1 : Q.Mx k r)
    ((hasFDerivAt_id (𝕜 := ℝ) (1 : Q.Mx k r)).add_const 1)
  have h2 : HasFDerivAt (fun x : Q.Mx k r => x - 1) (ContinuousLinearMap.id ℝ (Q.Mx k r)) 1 :=
    (hasFDerivAt_id (1 : Q.Mx k r)).sub_const 1
  have h3 := h1.mul' h2
  have hfun : (cinv : Q.Mx k r → Q.Mx k r) =
      (fun x : Q.Mx k r => Ring.inverse (id x + 1)) * (fun x : Q.Mx k r => x - 1) := by
    funext x; rw [cinv_eq]; rfl
  rw [hfun]
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h => ?_
  simp [hinv]
  change ((2 : ℂ)⁻¹ • (1 : Q.Mx k r)) * h = (2 : ℂ)⁻¹ • h
  rw [smul_mul_assoc, one_mul]

private theorem exp_mulVec_eq_self_of_mulVec_eq_zero {X : Q.Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  let Lv : Q.Mx k r →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    { toFun := fun A => A *ᵥ v
      map_add' := fun A B => Matrix.add_mulVec A B v
      map_smul' := fun c A => Matrix.smul_mulVec c A v }
  let Lc := LinearMap.toContinuousLinearMap Lv
  have hs : Summable (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • X ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) X
  have hpow : ∀ n : ℕ, (X ^ (n + 1)) *ᵥ v = 0 := fun n => by
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have key : Lc (∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • X ^ n) =
      ∑' n : ℕ, Lc (((n.factorial : ℂ))⁻¹ • X ^ n) := Lc.map_tsum hs
  simp only [Lc, LinearMap.coe_toContinuousLinearMap', Lv, LinearMap.coe_mk, AddHom.coe_mk] at key
  rw [NormedSpace.exp_eq_tsum ℂ]
  simp only
  rw [key, tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Matrix.smul_mulVec, hpow, smul_zero]

private theorem exp_mem_uwset_of_inLieW {z : Fin (2 * r + k + 1) → ℂ} {X : Q.Mx k r} (hX : InLieW k r z X) :
    NormedSpace.exp X ∈ UWset k r z := by
  obtain ⟨hX1, hX2⟩ := hX
  have h1 : (1 : Q.Mx k r) ∈ Glev k r (Fin.last r) := by
    simp [Glev, UH]
  have h := Formalism.FourierDecayAlt.P.LeftDerivativeCurves.lcurve_lev h1 hX1 1
  simp only [Complex.ofReal_one, one_smul, mul_one, Glev, Set.mem_setOf_eq] at h
  simp only [UWset, Set.mem_setOf_eq]
  exact ⟨h.1, fun a => h.2 a (by simp), exp_mulVec_eq_self_of_mulVec_eq_zero hX2⟩

theorem locLogOp (z : Fin (2 * r + k + 1) → ℂ) :
    ∃ O : Set (Q.Mx k r), IsOpen O ∧ (1 : Q.Mx k r) ∈ O ∧ ∃ Λ : Q.Mx k r → Q.Mx k r, ContDiffOn ℝ ∞ Λ O ∧
      ∀ g ∈ O, g ∈ UWset k r z → InLieW k r z (Λ g) ∧ NormedSpace.exp (Λ g) = g := by
  classical

  let L := lieU k r z
  haveI : FiniteDimensional ℝ (Q.Mx k r) := inferInstance
  haveI : CompleteSpace L := (Submodule.complete_of_finiteDimensional L).completeSpace_coe
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective L.subtype (Submodule.ker_subtype L)
  let P : Q.Mx k r →L[ℝ] L := LinearMap.toContinuousLinearMap p
  have hP : ∀ Y : L, P (Y : Q.Mx k r) = Y := fun Y => by
    show p (L.subtype Y) = Y
    rw [← LinearMap.comp_apply, hp, LinearMap.id_apply]
  have hPmem : ∀ x, InLieW k r z x → (P x : Q.Mx k r) = x := fun x hx => by
    have := hP ⟨x, hx⟩
    rw [this]

  let Φ : L → L := fun Y => (2 : ℝ) • P (cinv (NormedSpace.exp (Y : Q.Mx k r)))
  have hu1 : IsUnit ((1 : Q.Mx k r) + 1) := ⟨twoU k r, rfl⟩
  have he0 : NormedSpace.exp ((0 : L) : Q.Mx k r) = 1 := by simp
  have hexp : ∀ x : Q.Mx k r, ContDiffAt ℝ ∞ (NormedSpace.exp : Q.Mx k r → Q.Mx k r) x :=
    fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hΦc : ∀ Y : L, IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1) → ContDiffAt ℝ ∞ Φ Y := by
    intro Y hY
    have a1 : ContDiffAt ℝ ∞ (fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y :=
      (hexp _).comp Y L.subtypeL.contDiff.contDiffAt
    have a0 : ContDiffAt ℝ ∞ (cinv : Q.Mx k r → Q.Mx k r) (NormedSpace.exp (Y : Q.Mx k r)) :=
      cinv_contDiffAt (k := k) (r := r) hY
    have a2 : ContDiffAt ℝ ∞ ((cinv : Q.Mx k r → Q.Mx k r) ∘ fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y :=
      ContDiffAt.comp (g := (cinv : Q.Mx k r → Q.Mx k r)) (f := fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y a0 a1
    exact (P.contDiff.contDiffAt.comp Y a2).const_smul (2 : ℝ)
  have hΦ0c : ContDiffAt ℝ ∞ Φ 0 := hΦc 0 (by rw [he0]; exact hu1)
  have hΦ0d : HasFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ L : L ≃L[ℝ] L) : L →L[ℝ] L) 0 := by
    have hE : HasFDerivAt (fun Y : L => NormedSpace.exp (Y : Q.Mx k r))
        ((1 : Q.Mx k r →L[ℝ] Q.Mx k r).comp L.subtypeL) 0 :=
      (hasFDerivAt_exp_zero (𝕂 := ℝ)).comp (0 : L) L.subtypeL.hasFDerivAt
    have hC : HasFDerivAt (cinv : Q.Mx k r → Q.Mx k r)
        (ContinuousLinearMap.mul ℝ (Q.Mx k r) ((1 / 2 : ℂ) • 1))
        (NormedSpace.exp ((0 : L) : Q.Mx k r)) := by
      rw [he0]; exact cinv_hasFDerivAt_one
    have h := ((P.hasFDerivAt).comp (0 : L) (hC.comp (0 : L) hE)).const_smul (2 : ℝ)
    refine HasFDerivAt.congr_fderiv h ?_
    refine ContinuousLinearMap.ext fun Y => ?_
    have hh : ((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (Y : Q.Mx k r) = (1 / 2 : ℝ) • (Y : Q.Mx k r) := by
      rw [smul_mul_assoc, one_mul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      norm_num
    change (2 : ℝ) • P (((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (Y : Q.Mx k r)) = Y
    rw [hh, P.map_smul, hP, smul_smul]
    norm_num
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let f := ContDiffAt.toOpenPartialHomeomorph Φ hΦ0c hΦ0d hn
  have hfc : (f : L → L) = Φ := rfl

  have hU : ∀ᶠ Y : L in 𝓝 (0 : L), IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1) := by
    have hc : ContinuousAt (fun Y : L => NormedSpace.exp (Y : Q.Mx k r) + 1) 0 :=
      (((hexp _).continuousAt).comp L.subtypeL.continuous.continuousAt).add continuousAt_const
    have h0 : IsUnit (NormedSpace.exp ((0 : L) : Q.Mx k r) + 1) := by rw [he0]; exact hu1
    exact hc.eventually_mem (Units.isOpen.mem_nhds h0)
  have hD : ∀ᶠ Y : L in 𝓝 (0 : L), fderiv ℝ Φ Y ∈
      Set.range (ContinuousLinearEquiv.toContinuousLinearMap : (L ≃L[ℝ] L) → L →L[ℝ] L) := by
    have hcont : ContinuousAt (fderiv ℝ Φ) 0 := (hΦ0c.fderiv_right (m := 0) (by simp)).continuousAt
    exact hcont.eventually_mem (ContinuousLinearEquiv.isOpen.mem_nhds
      ⟨ContinuousLinearEquiv.refl ℝ L, hΦ0d.fderiv.symm⟩)
  obtain ⟨V, hVsub, hVo, hV0⟩ := eventually_nhds_iff.mp (hU.and hD)
  have hsym : ∀ a ∈ f.target ∩ f.symm ⁻¹' V, ContDiffAt ℝ ∞ f.symm a := by
    rintro a ⟨ha, haV⟩
    obtain ⟨hu, e, he⟩ := hVsub _ haV
    have hcd := hΦc _ hu
    have hd : HasFDerivAt Φ (e : L →L[ℝ] L) (f.symm a) := by
      rw [show (e : L →L[ℝ] L) = fderiv ℝ Φ (f.symm a) from he]
      exact (hcd.differentiableAt (by simp)).hasFDerivAt
    exact f.contDiffAt_symm ha (by rw [hfc]; exact hd) (by rw [hfc]; exact hcd)

  let w : Q.Mx k r → L := fun g => (2 : ℝ) • P (cinv g)
  have hw : ∀ g : Q.Mx k r, IsUnit (g + 1) → ContDiffAt ℝ ∞ w g := fun g hg =>
    ((P.contDiff.contDiffAt).comp g (cinv_contDiffAt (k := k) (r := r) hg)).const_smul (2 : ℝ)
  have hGU : IsOpen {g : Q.Mx k r | IsUnit (g + 1)} :=
    Units.isOpen.preimage (continuous_id.add continuous_const)
  have hT : IsOpen (f.target ∩ f.symm ⁻¹' V) := f.isOpen_inter_preimage_symm hVo
  have hwc : ContinuousOn w {g : Q.Mx k r | IsUnit (g + 1)} := fun g hg =>
    (hw g hg).continuousAt.continuousWithinAt
  have hΦ00 : Φ 0 = 0 := by simp [Φ, cinv_one]
  have hw1 : w 1 = 0 := by simp [w, cinv_one]
  refine ⟨{g : Q.Mx k r | IsUnit (g + 1)} ∩ w ⁻¹' (f.target ∩ f.symm ⁻¹' V),
    hwc.isOpen_inter_preimage hGU hT, ⟨hu1, ?_⟩, fun g => ((f.symm (w g) : L) : Q.Mx k r), ?_, ?_⟩
  · have h0t : Φ 0 ∈ f.target := ContDiffAt.image_mem_toOpenPartialHomeomorph_target hΦ0c hΦ0d hn
    have h0s : (0 : L) ∈ f.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hΦ0c hΦ0d hn
    rw [hΦ00] at h0t
    refine ⟨?_, ?_⟩
    · show w 1 ∈ f.target
      rw [hw1]; exact h0t
    · show f.symm (w 1) ∈ V
      rw [hw1, ← hΦ00, ← hfc, f.left_inv h0s]
      exact hV0
  · intro g hg
    exact (L.subtypeL.contDiff.contDiffAt.comp g ((hsym (w g) hg.2).comp g (hw g hg.1))).contDiffWithinAt
  · intro g hg hgU
    set Y := f.symm (w g) with hYdef
    have hY : InLieW k r z (Y : Q.Mx k r) := Y.2
    refine ⟨hY, ?_⟩
    obtain ⟨huY, -⟩ := hVsub _ hg.2.2
    have h1 : Φ Y = w g := f.right_inv hg.2.1
    have hdg : IsUnit (g + 1).det := (Matrix.isUnit_iff_isUnit_det _).mp hg.1
    have hdY : IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1).det := (Matrix.isUnit_iff_isUnit_det _).mp huY
    have h2 : P (cinv (NormedSpace.exp (Y : Q.Mx k r))) = P (cinv g) :=
      smul_right_injective L (two_ne_zero' ℝ) h1
    have h3 := congrArg Subtype.val h2
    rw [hPmem _ (cinv_lie (exp_mem_uwset_of_inLieW hY) hdY), hPmem _ (cinv_lie hgU hdg)] at h3
    exact cinv_inj hdY hdg h3

end Formalism.FourierDecayAlt.P.RadicalReductionUnitary
end
end

