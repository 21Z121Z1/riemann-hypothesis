import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0290
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0136
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0121
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0289
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0288
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0287
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSIpInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSFund
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0291
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0292

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellExpansionOfSubadditive
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ENNReal

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def FamilyDerivativeExpansion (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) : Prop :=
  ∃ (Par : Type) (_ : AddCommGroup Par) (fam : Par → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (lam : Par)
    (N1 Ninf : Par → ℕ) (c0 q0 : ℕ) (Gam : ℝ),
    fam lam = f ∧ 0 ≤ Gam ∧
    (∀ x y, N1 (x + y) ≤ N1 x + N1 y) ∧ (∀ x y, Ninf (x + y) ≤ Ninf x + Ninf y) ∧ N1 0 = 0 ∧ Ninf 0 = 0 ∧
    (∀ μ, N1 (μ - lam) + c0 ≤ q0 → ∃ a : Par →₀ ℂ,
      (fun c => (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (fam μ) (TBB.bigPt P.r c)) =
          a.sum (fun ν z => z • fun c => p.V (fam (μ + ν)) (TBB.bigPt P.r c)) ∧
        (a.sum fun _ z => ‖z‖) ≤ Gam ^ (P.r + 1) ∧ ∀ ν ∈ a.support, N1 ν ≤ P.r + 1 ∧ Ninf ν ≤ 1) ∧
    (P.r + 1) * a₁ + c0 ≤ q0 ∧
    Gam ^ (P.r + 1) ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) ∧
    (∀ μ, TBB.jN2 p (fam μ) ≤ TBB.jN2 p f) ∧
    (∀ μ, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fam μ) (P.r + 1) [] (TBB.bigPt P.r c)))

theorem big_cell_expansion_of_subadditive (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ Gam : ℝ) (a₁ : ℕ)
    (hb : 0 ≤ b) (hGam : 0 ≤ Gam) (Par : Type) [AddCommGroup Par] (fam : Par → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (lam : Par) (hf : fam lam = f) (N1 Ninf : Par → ℕ) (c0 q0 : ℕ)
    (hN1 : ∀ x y, N1 (x + y) ≤ N1 x + N1 y) (hNinf : ∀ x y, Ninf (x + y) ≤ Ninf x + Ninf y)
    (hN10 : N1 0 = 0) (hNinf0 : Ninf 0 = 0)
    (hstep : ∀ μ, N1 (μ - lam) + c0 ≤ q0 → ∃ a : Par →₀ ℂ,
      (fun c => (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • p.V (fam μ) (TBB.bigPt P.r c)) =
          a.sum (fun ν z => z • fun c => p.V (fam (μ + ν)) (TBB.bigPt P.r c)) ∧
        (a.sum fun _ z => ‖z‖) ≤ Gam ^ (P.r + 1) ∧ ∀ ν ∈ a.support, N1 ν ≤ P.r + 1 ∧ Ninf ν ≤ 1)
    (hrange : (P.r + 1) * a₁ + c0 ≤ q0)
    (hGb : Gam ^ (P.r + 1) ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2))
    (hnorm : ∀ μ, TBB.jN2 p (fam μ) ≤ TBB.jN2 p f)
    (hmeas : ∀ μ, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fam μ) (P.r + 1) [] (TBB.bigPt P.r c))) :
    BigCellDerivativeExpansion p f b C₃ a₁ := by
  subst hf
  intro a ha
  let Dop : Unit → Module.End ℂ ((Fin (P.r + 1) → ℂ) → (Wq →L[ℂ] Wp)) := fun _ =>
    { toFun := fun φ c => (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det • φ c
      map_add' := fun φ ψ => by funext c; simp only [Pi.add_apply, smul_add]
      map_smul' := fun z φ => by
        funext c; simp only [Pi.smul_apply, RingHom.id_apply]; rw [smul_comm] }
  have hDop : ∀ (n : ℕ) (φ : (Fin (P.r + 1) → ℂ) → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ),
      ((Dop ()) ^ n) φ c = (D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det ^ n • φ c := by
    intro n
    induction n with
    | zero => intro φ c; simp
    | succ n ih =>
      intro φ c
      rw [pow_succ]
      show ((Dop ()) ^ n) ((Dop ()) φ) c = _
      rw [ih, pow_succ, mul_smul]
      rfl
  have key := Formalism.HermitianLatticeCounting.P.iterated_sum_bound_holds ((Fin (P.r + 1) → ℂ) → (Wq →L[ℂ] Wp)) Par Unit
    (fun μ c => p.V (fam μ) (TBB.bigPt P.r c)) Dop (fun _ => P.r + 1) N1 Ninf lam Gam c0 q0 hGam hN1 hNinf
    hN10 hNinf0 (fun μ _ hμ => hstep μ hμ) lam (List.replicate a ()) (by
      simp only [sub_self, hN10, List.map_replicate, List.sum_replicate, smul_eq_mul, zero_add]
      nlinarith [Nat.mul_le_mul_right (P.r + 1) ha])
  obtain ⟨A, hA, hAn, -⟩ := key
  let e := A.support.equivFin
  refine ⟨A.support.card, fun i => fam (lam + (e.symm i).1), fun i => A (e.symm i).1, ?_,
    fun i => hnorm _, fun i => hmeas _, ?_⟩
  · have h1 : ∑ i : Fin A.support.card, ‖A (e.symm i).1‖ = A.sum fun _ z => ‖z‖ := by
      rw [Finsupp.sum, ← Finset.sum_coe_sort A.support]
      exact e.symm.sum_comp (fun x : A.support => ‖A x.1‖)
    rw [h1]
    refine hAn.trans ?_
    simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
    rw [pow_mul']
    have hGp : 0 ≤ Gam ^ (P.r + 1) := pow_nonneg hGam _
    calc (Gam ^ (P.r + 1)) ^ a ≤ (b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2)) ^ a := by
          first
            | exact pow_le_pow_left₀ hGp hGb a
            | exact pow_le_pow_left hGp hGb a
      _ = b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  · intro c _ _
    have h2 := congrFun hA c
    rw [List.map_replicate, List.prod_replicate, hDop, Finsupp.sum, Finset.sum_apply] at h2
    simp only [Pi.smul_apply] at h2
    refine h2.trans ?_
    rw [← Finset.sum_coe_sort A.support]
    exact (e.symm.sum_comp (fun x : A.support => A x.1 • p.V (fam (lam + x.1)) (TBB.bigPt P.r c))).symm

theorem big_cell_expansion_of_family (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (hb : 0 ≤ b)
    (h : FamilyDerivativeExpansion p f b C₃ a₁) : BigCellDerivativeExpansion p f b C₃ a₁ := by
  obtain ⟨Par, _, fam, lam, N1, Ninf, c0, q0, Gam, hf, hGam, hN1, hNinf, hN10, hNinf0, hstep, hrange, hGb, hnorm,
    hmeas⟩ := h
  exact big_cell_expansion_of_subadditive p f b C₃ Gam a₁ hb hGam Par fam lam hf N1 Ninf c0 q0 hN1 hNinf hN10 hNinf0 hstep hrange hGb
    hnorm hmeas

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ENNReal

noncomputable section

section hs

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_norm_CinL (S : B.RealPlaceData k r Wp Wq) {hA hB : B.Mat k r} (hhA : hA ∈ UWset k r S.z)
    (hhB : hB ∈ UWset k r S.z') (X : Wq →L[ℂ] Wp) :
    ‖B.hsVec (Formalism.FourierDecayAlt.P.Dx2.VV.CinL S hA hB X)‖ = ‖B.hsVec X‖ := by
  have e : B.hsInner (Formalism.FourierDecayAlt.P.Dx2.VV.CinL S hA hB X) (Formalism.FourierDecayAlt.P.Dx2.VV.CinL S hA hB X) =
      B.hsInner X X := by
    rw [Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply]
    unfold Formalism.FourierDecayAlt.P.Dx2.VV.Cin
    rw [Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (S.π_unitary hA hhA),
      Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (S.π'_unitary _ (WeylGroupFacts.uw_inv hhB))]
  rw [TBBx2.Tri.hsInner_self, TBBx2.Tri.hsInner_self] at e
  have e2 := Complex.ofReal_injective e
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e2

end hs

section wt

theorem level_product_of_constant_weights (k r : ℕ) (GG : ℝ) : ∀ (n : ℕ) (d : Fin n → ℂ) (b : ℕ),
    C.nAux k r GG (fun _ _ => 1) b (List.ofFn fun i => ((1 : ℕ), d i)) =
      ∏ i : Fin n, (if b + (i : ℕ) = r + 1 then GG ^ (k - 1)
        else ‖d i‖ ^ (2 * (C.Mlev k r (b + (i : ℕ)) - 2))) := by
  have e : ∀ x y : ℕ, x + 1 + y = x + (y + 1) := fun x y => by omega
  have e2 : ∀ m : ℕ, m + 1 - 3 = m - 2 := fun m => by omega
  intro n
  induction n with
  | zero => intro d b; simp [C.nAux]
  | succ n ih =>
    intro d b
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    simp only [C.nAux]
    simp [ih, e, e2, Fin.val_succ]
    all_goals (by_cases hb : b = r + 1 <;> simp [hb])
    all_goals (left; congr 1; first | ring | omega)
    all_goals clear ih e e2
    all_goals done

theorem ptLast_bigPt (r : ℕ) (c : Fin (r + 1) → ℂ) : D.ptLast (TBB.bigPt r c) = (1, c (Fin.last r)) := by
  have h : ∀ {α : Type} (n : ℕ) (f : Fin (n + 1) → α) (z : α), (List.ofFn f).getLast?.getD z = f (Fin.last n) := by
    intro α n f z
    rw [List.getLast?_eq_getElem?]
    simp only [List.length_ofFn, Nat.add_sub_cancel]
    rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
    rfl
  have h2 := h r (fun i => ((1 : ℕ), c i)) (0, 0)
  simp only [D.ptLast, TBB.bigPt]
  exact h2

theorem nPt_bigPt (k r : ℕ) (T T' : ℝ) (c : Fin (r + 1) → ℂ) (hζ : T * T' ≤ Complex.normSq (c (Fin.last r))) :
    TBB.nPt k r (T * T') (TBB.bigPt r c) = bcWeight k r T T' ((fun j => c j.castSucc), c (Fin.last r)) := by
  have hl : D.ptLast (List.ofFn fun l => ((1 : ℕ), c l)) = (1, c (Fin.last r)) := ptLast_bigPt r c
  have e : ∀ a : Fin r, (2 * (C.Mlev k r (1 + ((Fin.castSucc a : Fin (r + 1)) : ℕ)) - 2) : ℤ) =
      ((2 * (Mdim k r a - 2) : ℕ) : ℤ) := by
    intro a
    have ha := a.isLt
    simp only [C.Mlev, Mdim, Fin.coe_castSucc]
    omega
  simp only [TBB.nPt, TBB.bigPt]
  rw [level_product_of_constant_weights, Fin.prod_univ_castSucc]
  simp only [bcWeight]
  rw [if_pos hζ]
  congr 1
  · apply Finset.prod_congr rfl
    intro a _
    have ha := a.isLt
    rw [if_neg (by simp only [Fin.coe_castSucc]; omega), e a, zpow_natCast]
  · rw [if_pos (by simp only [Fin.val_last]; omega)]
    simp only [D.ptGG, hl]

end wt

section vec

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem hsVec_norm_V_bigPt (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (d : Fin (P.r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) (hG : 0 < TBB.Gp p (TBB.bigPt P.r d)) :
    ‖B.hsVec (p.V F (TBB.bigPt P.r d))‖ =
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))))‖ := by
  have hl : D.IsLocPt (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt d hd
  have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt d) := hG
  have h' := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k P.r Wp Wq p.T.base p.ν' p.m₀ _ p.hF hl hG'
  show ‖B.hsVec (D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt d))‖ = _
  unfold D.vecV
  rw [dif_pos ⟨hl, hG'⟩, dif_pos h']
  obtain ⟨hγ, hZγ, -⟩ := h'.choose_spec
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (d (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ d hG'
  have hc : ∀ a : Fin P.r, d a.castSucc ≠ 0 := fun a => hd _
  have hsec := p.T.base.sec.2 _ hζ
  have hγ' : bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r))) ∈ B.GV P.k P.r :=
    bigCellMem P.k P.r _ _ hc hsec.1
  have hZγ' := Formalism.FourierDecayAlt.P.PBM.zhat_bigCell_pt p.T.base d hζ
  have hpos : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ]; exact hG'
  have hpos' : 0 < Gf P.k P.r p.T.base.z p.T.base.z'
      (bigCell P.k P.r (fun i => d i.castSucc) (p.T.base.μsec (d (Fin.last P.r)))) := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r _ _ (Formalism.FourierDecayAlt.P.PBJ.bigPt d) _ hl hZγ']; exact hG'
  obtain ⟨s, hs, s', hs', hγs⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description P.k P.r p.T.base.z p.T.base.z'
    ⟨p.T.base.k_pos, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base, Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base⟩
    _ hγ _ hγ' hpos (hZγ.trans hZγ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime p.T.base) hs'
  have hlaw := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt p.T.base (Formalism.FourierDecayAlt.P.PBJ.bigPt d) hl hγ hZγ hpos hhA hnA hfA hhB hnB
    hfB F
  rw [← hγs] at hlaw
  rw [← hlaw, hsVec_norm_CinL p.T.base hhA hhB]
  have hw : (hl.2 ▸ D.ptPerm (Formalism.FourierDecayAlt.P.PBJ.bigPt d) : Equiv.Perm (Fin (P.r + 1))) = 1 :=
    Formalism.FourierDecayAlt.P.PBM.cast_perm_eq_one _ _ (Formalism.FourierDecayAlt.P.PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' (Formalism.FourierDecayAlt.P.PBJ.bigPt d) (P.r + 1) hl.2 hl.1
  rw [hw] at hmono
  rw [hw, Formalism.FourierDecayAlt.P.PBM.orbJ_one_eq p.T.base hγ' hpos' hnz (hZγ'.trans hmono) F]

end vec

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem bcWeight_nonneg0 (k r : ℕ) (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.mpr h) _)
  · exact le_refl 0

theorem pt_le (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) :
    ENNReal.ofReal (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) *
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc) (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2) ≤
    ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c)) := by
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  by_cases hw : bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) = 0
  · rw [hw, zero_mul, ENNReal.ofReal_zero]; exact bot_le
  have hk : 2 ≤ P.k := p.hl.2.2
  have hTT : 0 < T * T' := mul_pos p.T.base.T_pos p.T.base.T'_pos
  have hw' := hw
  unfold bcWeight at hw'
  split_ifs at hw' with hle
  · have hprod := left_ne_zero_of_mul hw'
    have hgg := right_ne_zero_of_mul hw'
    have hlt : T * T' < Complex.normSq (c (Fin.last P.r)) := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]
    have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := by
      intro a ha
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      dsimp only
      rw [ha, norm_zero, zero_pow]
      unfold Mdim; have := a.isLt; omega
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    rw [TBBx2.Tri.Ew_top p F hl, hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r T T' ((fun j => c j.castSucc), c (Fin.last P.r)) := nPt_bigPt P.k P.r T T' c hle
    rw [hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]
  · exact absurd rfl hw'

theorem lemB_one (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : LemB p F 1 := by
  unfold LemB
  rw [ENNReal.ofReal_one, one_mul]
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  set g : (Fin P.r → ℂ) × ℂ → ℝ := fun q => bcWeight P.k P.r T T' q *
    ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r q.1 (p.T.base.μsec q.2)))‖ ^ 2 with hg
  have hβ : B.beta p.T.base F F = ∫ q, ((g q : ℝ) : ℂ) := by
    unfold B.beta betaBig
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [hg]
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hβ, integral_complex_ofReal, Complex.ofReal_re]
  have key : ENNReal.ofReal (∫ q, g q) ≤ ∫⁻ q, ENNReal.ofReal (g q) := by
    by_cases hint : Integrable g
    · rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun q => mul_nonneg (bcWeight_nonneg0 _ _ _ _ _) (sq_nonneg _))]
    · rw [integral_undef hint, ENNReal.ofReal_zero]; exact bot_le
  refine le_trans key ?_
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
  unfold TBB.jN2
  refine lintegral_mono fun c => ?_
  rw [he c]
  exact pt_le p F c

end main

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpecAsm
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_open (h0 : RDSOpAv) (h1 : RDSOpR) (h2 : RDSOpRv) (h3 : RDSOpA)
    (hp : RDSPAdj) (hQ : RDSQQAdj) (hX : RDSXiTest) (hP : RDSPair) : RDIdentSpec :=
  rDIdentSpec_of_cut spectral_Y_real h0 h1 h2 h3 spectral_inner_product_linear (rDSCoordAdj_of_p hp) spectral_function_adjoint hQ hX spectral_fundamental_identity spectral_section_identity hP
    radial_residue_formula radial_operator_function_field

end Formalism.FourierDecayAlt.P.CutSE
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSNicePoly
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_nice_polynomial : RDSNicePoly := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ F hF
  obtain ⟨-, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd hgO (not_lt.2 (hFs g hg hne))
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

theorem rDSPolyProp_of_nice : RDSPolyProp := fun k r Wp Wq _ _ _ _ _ _ D _ _ Θ hΘ hC =>
  opProp1_of_poly spectral_nice_polynomial D hΘ hC

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpADone
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_operator_A : RDSOpA :=
  rDSOpA_of_parts spectral_polynomial_property spectral_group_action spectral_radial_action spectral_action_locality

theorem spectral_operator_A_adjoint : RDSOpAv :=
  rDSOpAv_of_parts spectral_polynomial_property spectral_group_action spectral_radial_action spectral_action_locality

end Formalism.FourierDecayAlt.P.CutSE
end

