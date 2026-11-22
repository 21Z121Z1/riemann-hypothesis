import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0121
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0117

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PlMonoConst
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section poly

variable {A : Type} [Ring A] [Algebra ℂ A]

def PolyLe (t : ℕ) (f : ℂ → A) : Prop :=
  ∃ C : Fin t → A, ∀ u, f u = ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l

theorem pl_congr {t : ℕ} {f g : ℂ → A} (h : ∀ u, f u = g u) (hf : PolyLe t f) : PolyLe t g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun u => by rw [← h u]; exact hC u⟩

theorem pl_zero (t : ℕ) : PolyLe t (fun _ => (0 : A)) := ⟨0, fun u => by simp⟩

theorem pl_add {t : ℕ} {f g : ℂ → A} (hf : PolyLe t f) (hg : PolyLe t g) : PolyLe t (fun u => f u + g u) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun u => ?_⟩
  dsimp only
  rw [hC, hD, ← Finset.sum_add_distrib]
  simp only [Pi.add_apply, mul_add]

theorem pl_sum {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ → A) (hf : ∀ i ∈ s, PolyLe t (f i)) :
    PolyLe t (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact pl_congr (fun u => by simp) (pl_zero t)
  | insert i s hi ih =>
    exact pl_congr (fun u => by simp [Finset.sum_insert hi])
      (pl_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem pl_lmul {t : ℕ} {f : ℂ → A} (c : A) (hf : PolyLe t f) : PolyLe t (fun u => c * f u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨fun l => c * C l, fun u => ?_⟩
  dsimp only
  rw [hC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Algebra.left_comm _ _ _

theorem pl_rmul {t : ℕ} {f : ℂ → A} (e : A) (hf : PolyLe t f) : PolyLe t (fun u => f u * e) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨fun l => C l * e, fun u => ?_⟩
  dsimp only
  rw [hC, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _

theorem pl_mono {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) f := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.snoc (α := fun _ => A) C 0, fun u => ?_⟩
  rw [hC, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem pl_mulu {t : ℕ} {f : ℂ → A} (hf : PolyLe t f) : PolyLe (t + 1) (fun u => f u * algebraMap ℂ A u) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨Fin.cons (α := fun _ => A) 0 C, fun u => ?_⟩
  dsimp only
  rw [hC, Fin.sum_univ_succ, Finset.sum_mul]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, Fin.val_succ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, pow_succ]

theorem pl_mono_const (t : ℕ) (x : A) : PolyLe (t + 1) (fun u => algebraMap ℂ A (u ^ t) * x) := by
  refine ⟨Fin.snoc (α := fun _ => A) 0 x, fun u => ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem prod_poly : ∀ (t : ℕ) (c δ : Fin t → ℂ) (F : Fin t → A),
    PolyLe t (fun u => (List.ofFn fun k => algebraMap ℂ A ((u + c k) * δ k) + F k).prod -
      algebraMap ℂ A (u ^ t * ∏ k, δ k)) := by
  intro t
  induction t with
  | zero =>
    intro c δ F
    exact ⟨Fin.elim0, fun u => by simp⟩
  | succ t ih =>
    intro c δ F
    obtain ⟨C, hC⟩ := ih (fun k => c k.succ) (fun k => δ k.succ) (fun k => F k.succ)
    let Q : ℂ → A := fun u => ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
    have hQpl : PolyLe t Q := ⟨C, fun u => rfl⟩
    have hR : ∀ u, (List.ofFn fun k : Fin t => algebraMap ℂ A ((u + c k.succ) * δ k.succ) + F k.succ).prod =
        algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) + Q u := by
      intro u
      show _ = _ + ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
      have h := hC u
      dsimp only at h
      rw [← h]
      abel
    refine pl_congr (f := fun u => algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) +
        ((algebraMap ℂ A (c 0 * δ 0) + F 0) * Q u + algebraMap ℂ A (u ^ t) *
          ((algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (∏ k : Fin t, δ k.succ)))) ?_
      (pl_add (pl_lmul _ (pl_mulu hQpl)) (pl_add (pl_mono (pl_lmul _ hQpl)) (pl_mono_const t _)))
    intro u
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [hR u]
    have e1 : algebraMap ℂ A (u * δ 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ (t + 1) * (δ 0 * ∏ k : Fin t, δ k.succ)) := by
      rw [← map_mul]
      congr 1
      ring
    have e2 : algebraMap ℂ A (u * δ 0) * Q u = algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) := by
      rw [← Algebra.commutes, ← mul_assoc, ← map_mul, mul_comm (δ 0) u]
    have e3 : (algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ t) * ((algebraMap ℂ A (c 0 * δ 0) + F 0) *
          algebraMap ℂ A (∏ k : Fin t, δ k.succ)) := by
      rw [map_mul (algebraMap ℂ A) (u ^ t), Algebra.left_comm]
    rw [add_mul u (c 0) (δ 0), map_add, add_assoc,
      mul_add (algebraMap ℂ A (u * δ 0) + (algebraMap ℂ A (c 0 * δ 0) + F 0)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (Q u), e1, e2, e3]
    abel

theorem qminor_poly {n t : ℕ} (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (s0 : ℂ) :
    PolyLe t (fun u => qminor E a b (u + s0) - algebraMap ℂ A (u ^ t *
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0))) := by
  classical
  refine pl_congr (f := fun u => ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
      ((List.ofFn fun k : Fin t => algebraMap ℂ A ((u + (s0 - (k : ℂ))) *
          (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k)).prod -
        algebraMap ℂ A (u ^ t * ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0)))) ?_
    (pl_sum _ _ fun σ _ => pl_lmul _ (prod_poly t _ _ _))
  intro u
  have hT : ∀ (σ : Equiv.Perm (Fin t)) (k : Fin t), Tm E (u + s0 - (k : ℂ)) (a (σ k)) (b k) =
      algebraMap ℂ A ((u + (s0 - (k : ℂ))) * (if a (σ k) = b k then (1 : ℂ) else 0)) + E (a (σ k)) (b k) := by
    intro σ k
    unfold Tm
    split_ifs <;> simp [add_sub_assoc]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · unfold qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hT]
  · rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_left_comm (u ^ t) (((Equiv.Perm.sign σ : ℤ) : ℂ)),
      map_mul (algebraMap ℂ A) (((Equiv.Perm.sign σ : ℤ) : ℂ)), map_intCast]

end poly

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightStabilizerMem
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

abbrev RR (k r : ℕ) (w : Equiv.Perm (Fin (r + 1))) : Type :=
  (Mt k r × ((C2.LPidx w → ℂ) × Mt k r)) × (Mt k r × ((G.UT (r + 1) → ℂ) × Mt k r))

section defs

variable (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))

def Xi (x : C2.Lstidx w → ℂ) (q : RR k r w) : B.SS k r :=
  ((q.1.1, Matrix.of.symm (C2.tauM k r S.z (G.upper (e (x, q.1.2.1))) * Matrix.of q.1.2.2)),
   (q.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2)))

def Xi0 (q : RR k r w) : B.SS k r :=
  ((q.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w q.1.2.1)ᴴ * Matrix.of q.1.2.2)),
   (q.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2)))

def rhoX (x : C2.Lstidx w → ℂ) : B.Mat k r := Dx2.Rad.rhoF S γ w x

def rhoP (x : C2.Lstidx w → ℂ) : B.Mat k r := γ⁻¹ * (rhoX S γ w x)⁻¹ * γ

def m0L (x : C2.Lstidx w → ℂ) (y : C2.LPidx w → ℂ) : B.Mat k r :=
  (C2.tauM k r S.z (lowP w y)ᴴ)⁻¹ * (rhoX S γ w x)⁻¹ * C2.tauM k r S.z (G.upper (e (x, y)))

def m0R (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) : B.Mat k r :=
  (C2.tauM k r S.z' (C2.uMap k r S.z' (rhoP S γ w x) * G.upper u))⁻¹ * rhoP S γ w x * C2.tauM k r S.z' (G.upper u)

def Tx (x : C2.Lstidx w → ℂ) (q : RR k r w) : RR k r w :=
  ((q.1.1, (q.1.2.1, Matrix.of.symm (m0L S γ w e x q.1.2.1 * Matrix.of q.1.2.2))),
   (q.2.1, (utc (C2.uMap k r S.z' (rhoP S γ w x) * G.upper q.2.2.1),
     Matrix.of.symm (m0R S γ w x q.2.2.1 * Matrix.of q.2.2.2))))

def nuR (μ0 μ0' : Measure (Mt k r)) : Measure (RR k r w) :=
  (S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0)).prod
    (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))

def Tt (p : (C2.Lstidx w → ℂ) × RR k r w) : (C2.Lstidx w → ℂ) × RR k r w := (p.1, Tx S γ w e p.1 p.2)

end defs

section alg

variable (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) {w : Equiv.Perm (Fin (r + 1))}
  {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hZw : Zhat k r S.z S.z' γ = C2.monoP w d)
  (hpos : 0 < Gf k r S.z S.z' γ)
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))
  (he : ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ)

include hγ hd hZw hpos in
theorem good : Dx2.Rad.Good S γ w d :=
  ⟨fun x => Dx2.Rad.exists_rho S hγ hpos hd hZw x, Dx2.Rad.u_inj S hγ hpos hd hZw,
    fun _ hρ => Dx2.Rad.u_lstg S hγ hpos hd hZw hρ⟩

include hγ hd hZw hpos in
theorem rhoX_spec (x : C2.Lstidx w → ℂ) :
    rhoX S γ w x ∈ C6.Rset γ ∧ C2.uMap k r S.z (rhoX S γ w x) = (lowS w x)ᴴ := by
  have h := Dx2.Rad.exists_rho S hγ hpos hd hZw x
  have e1 : rhoX S γ w x = h.choose := by
    show Formalism.FourierDecayAlt.D.rhoOfU S γ (Dx2.Rad.low w x)ᴴ = _
    unfold Formalism.FourierDecayAlt.D.rhoOfU
    rw [dif_pos h]
  rw [e1, UC.lowS_eq_low]
  exact h.choose_spec

include hγ hd hZw hpos in
theorem rhoP_N (x : C2.Lstidx w → ℂ) : rhoP S γ w x ∈ Nset k r := by
  have h1 := (rhoX_spec S hγ hd hZw hpos x).1
  have hu := PI.StabSplit.GV_unit k r hγ
  have e : rhoP S γ w x = (γ⁻¹ * rhoX S γ w x * γ)⁻¹ := by
    unfold rhoP
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, mul_assoc]
  rw [e]
  exact Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv h1.2

theorem lowPH_UT (y : C2.LPidx w → ℂ) : (lowP w y)ᴴ ∈ C2.UTset (r + 1) :=
  UC.LT_ct (UC.lowerUnipotent_mem w y).1

theorem lowSH_UT (x : C2.Lstidx w → ℂ) : (lowS w x)ᴴ ∈ C2.UTset (r + 1) :=
  UC.LT_ct (UC.lowS_mem w x).1

include he in
theorem upper_e_UT (p : (C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) : G.upper (e p) ∈ C2.UTset (r + 1) := by
  rw [he p]
  exact UC.prod_UT w p

include hγ hd hZw hpos he in
theorem left_stabilizer_mem (x : C2.Lstidx w → ℂ) (y : C2.LPidx w → ℂ) : m0L S γ w e x y ∈ C2.N0set k r S.z := by
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z hz
  obtain ⟨hρR, hρu⟩ := rhoX_spec S hγ hd hZw hpos x
  have hτv := A.tau_N hz (lowPH_UT y)
  have hτe := A.tau_N hz (upper_e_UT e he (x, y))
  have h1 : (C2.tauM k r S.z (lowP w y)ᴴ)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hτv
  have h2 : (rhoX S γ w x)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hρR.1
  have hN : m0L S γ w e x y ∈ Nset k r := WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul h1 h2) hτe
  refine ⟨hN, ?_⟩
  unfold m0L
  rw [(hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul h1 h2))).2.2 _ (A.n_in_S hτe),
    (hUF.1 _ (A.n_in_S h1)).2.2 _ (A.n_in_S h2), A.uMap_inv hz hτv, A.uMap_inv hz hρR.1, hρu,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z hz _ (lowPH_UT y)).2.2,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z hz _ (upper_e_UT e he (x, y))).2.2, he]
  calc ((lowP w y)ᴴ).adjugate * ((lowS w x)ᴴ).adjugate * ((lowS w x)ᴴ * (lowP w y)ᴴ)
      = ((lowP w y)ᴴ).adjugate * (((lowS w x)ᴴ).adjugate * (lowS w x)ᴴ) * (lowP w y)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.adjugate_mul, A.det_UT (lowSH_UT x), one_smul, Matrix.mul_one, Matrix.adjugate_mul,
          A.det_UT (lowPH_UT y), one_smul]

include hγ hd hZw hpos in
theorem uP_UT (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) :
    C2.uMap k r S.z' (rhoP S γ w x) * G.upper u ∈ C2.UTset (r + 1) := by
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z' hz'
  have hρ := rhoP_N S hγ hd hZw hpos x
  have hτ := A.tau_N hz' (UC.upper_mem u)
  rw [← (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (UC.upper_mem u)).2.2,
    ← (hUF.1 _ (A.n_in_S hρ)).2.2 _ (A.n_in_S hτ)]
  exact (hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul hρ hτ))).2.1

include hγ hd hZw hpos in
theorem right_stabilizer_mem (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) : m0R S γ w x u ∈ C2.N0set k r S.z' := by
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z' hz'
  have hρ := rhoP_N S hγ hd hZw hpos x
  have hτa := A.tau_N hz' (uP_UT S hγ hd hZw hpos x u)
  have hτ := A.tau_N hz' (UC.upper_mem u)
  have h1 := WeylGroupFacts.mem_n_inv hτa
  have hN : m0R S γ w x u ∈ Nset k r := WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul h1 hρ) hτ
  refine ⟨hN, ?_⟩
  unfold m0R
  rw [(hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul h1 hρ))).2.2 _ (A.n_in_S hτ),
    (hUF.1 _ (A.n_in_S h1)).2.2 _ (A.n_in_S hρ), A.uMap_inv hz' hτa,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (uP_UT S hγ hd hZw hpos x u)).2.2,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (UC.upper_mem u)).2.2, Matrix.mul_assoc,
    Matrix.adjugate_mul, A.det_UT (uP_UT S hγ hd hZw hpos x u), one_smul]

include hγ hd hZw hpos he in

theorem Xi_eq (x : C2.Lstidx w → ℂ) (q : RR k r w) :
    Xi S w e x q = C6.actR γ (rhoX S γ w x) (Xi0 S w (Tx S γ w e x q)) := by
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hρ := (rhoX_spec S hγ hd hZw hpos x).1
  have hρu : IsUnit (rhoX S γ w x).det := PI.StabSplit.GV_unit k r hρ.1.1
  have hγu : IsUnit γ.det := PI.StabSplit.GV_unit k r hγ
  have hA : IsUnit (C2.tauM k r S.z (lowP w q.1.2.1)ᴴ).det :=
    PI.StabSplit.GV_unit k r (A.tau_N hz (lowPH_UT q.1.2.1)).1
  have hM := uP_UT S hγ hd hZw hpos x q.2.2.1
  have hB : IsUnit (C2.tauM k r S.z' (C2.uMap k r S.z' (rhoP S γ w x) * G.upper q.2.2.1)).det :=
    PI.StabSplit.GV_unit k r (A.tau_N hz' hM).1
  simp only [Xi, Xi0, Tx, C6.actR, Equiv.apply_symm_apply, UC.upper_utc hM, m0L, m0R, ← mul_assoc,
    Matrix.mul_nonsing_inv_cancel_right _ _ hA, Matrix.mul_nonsing_inv_cancel_right _ _ hB,
    Matrix.mul_nonsing_inv _ hρu]
  simp only [rhoP, ← mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hρu,
    Matrix.mul_nonsing_inv_cancel_right _ _ hγu, Matrix.nonsing_inv_mul _ hγu, one_mul]

end alg

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferWordEntriesMem
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Pres

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def presAlg (U : Submodule ℂ V) : StarSubalgebra ℂ (Pr V) where
  carrier := {a | (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ ∀ Φ ∈ U, a.2.unop Φ ∈ U}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ)⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ)⟩
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
    · show (algebraMap ℂ (Module.End ℂ V) a) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · show (algebraMap ℂ (Module.End ℂ V) (conj a)) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
  star_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, ha1⟩

end Pres

section Words

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem entries_mem_transpose {M : M2 (SlopeTestRemainingChoices S A)} (h : E2 𝒜 M) : E2 𝒜 Mᵀ := fun i j => h j i

theorem transfer_word_entries_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : star Y = Y) : E2 𝒜 (TTw QQ w Y) := by
  induction w with
  | nil =>
    intro a b
    show io (QQ Y a b) ∈ entSub 𝒜
    exact io_mem (hQ Y hY a b)
  | cons l w ih =>
    by_cases hp : l.plus
    · rw [TTw, if_pos hp]; exact entries_mem_mul ih (reflection_entries_mem _ _)
    · rw [TTw, if_neg hp]; exact entries_mem_mul (reflection_transpose_entries_mem _ _) ih

theorem rrw_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRw QQ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [RRw]
    refine (entSub 𝒜).mul_mem (ih fun l' hl' => hw l' (by simp [hl'])) (ins_mem _ ?_)
    have hT := transfer_word_entries_mem QQ hQ w l.pt (hw l (by simp))
    split_ifs
    · exact hT
    · exact entries_mem_transpose hT

end Words

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem matrix_two_entries_mem {𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))} {a b c d : Pr (RadSp k r z z' π π')}
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (hd : d ∈ 𝒜) : ∀ i j, (!![a, b; c, d] : M2 _) i j ∈ 𝒜 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem tprod_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π')))
    (Y : ℂ) (i : ℕ) (hS : ∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    tprod L Y i a b ∈ 𝒜 := by
  suffices H : ∀ n i, r - i = n → (∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) →
      ∀ a b, tprod L Y i a b ∈ 𝒜 from H _ i rfl hS a b
  intro n
  induction n with
  | zero =>
    intro i hi _ a b
    unfold tprod
    rw [dif_neg (by omega), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ n ih =>
    intro i hi hS a b
    unfold tprod
    rw [dif_pos (by omega), Matrix.mul_apply]
    refine sum_mem fun e _ => mul_mem (ih (i + 1) (by omega) (fun l hl => hS l (by omega)) a e) ?_
    obtain ⟨hp, hc, hci⟩ := hS ⟨i, by omega⟩ le_rfl
    have h00 : algebraMap ℂ _ Y + L.p ⟨i, by omega⟩ ∈ 𝒜 := add_mem (𝒜.algebraMap_mem Y) hp
    fin_cases e <;> fin_cases b <;> simp [Ts, Formalism.YangianSpanCharacter.T.Tm, site, h00, hc, hci]

theorem QQi_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1))
    (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) :
    ∀ Y : ℂ, star Y = Y → ∀ a b, QQi L st i Y a b ∈ 𝒜 := by
  intro Y hY a b
  unfold QQi
  rw [Matrix.mul_apply]
  refine sum_mem fun e _ => mul_mem ?_ (tprod_mem L 𝒜 Y i.val hS e b)
  rw [Matrix.mul_apply]
  refine sum_mem fun f _ => mul_mem ?_ (hQ Y hY f e)
  rw [Matrix.conjTranspose_apply]
  exact star_mem (tprod_mem L 𝒜 (star Y) i.val hS f a)

def IntLevOn (μ : Measure (Mt k r)) (i : Fin (r + 1)) (U : Submodule ℂ (RadSp k r z z' π π')) : Prop :=
  ∀ c ∈ OmX r, ∀ Φ ∈ U, ∀ Ψ ∈ U,
    (∀ c' : Cf r i, Integrable (fun g : Mt k r =>
      B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ) ∧
    Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * pairAt μ Φ Ψ (glue i c c'))

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formInt_of_cls (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (U : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (hK : ∀ i, K i ≤ U i)
    (hI : ∀ i, IntLevOn μ i (U i))
    (hQ : ∀ i, ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ presAlg (U i))
    (hS : ∀ (i : Fin (P.r + 1)) (l : Fin P.r), i.val ≤ l.val →
      L.p l ∈ presAlg (U i) ∧ L.c l ∈ presAlg (U i) ∧ L.ci l ∈ presAlg (U i)) :
    FormInt S P z z' π π' μ L st l0 K := by
  intro w hw i c hc x y hx hy
  have hRR : RRi L st i w ∈ entSub (presAlg (U i)) :=
    rrw_mem (QQi L st i) (QQi_mem L st _ i (hQ i) (hS i)) w hw.1.2.1
  have hu : ∀ a, act (RRi L st i w) x a ∈ U i := fun a =>
    (U i).sum_mem fun b _ => (hRR a b).1 _ (hK i (hx b))
  have hv : ∀ a, y a ∈ U i := fun a => hK i (hy a)
  refine ⟨fun c' a => ((hI i) c hc _ (hu a) _ (hv a)).1 c', ?_⟩
  simp only [Finset.mul_sum]
  exact integrable_finsetSum _ fun a _ => ((hI i) c hc _ (hu a) _ (hv a)).2

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

