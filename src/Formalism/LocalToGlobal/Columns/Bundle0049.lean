import Formalism.LocalToGlobal.Columns.Bundle0048
import Formalism.LocalToGlobal.Columns.Bundle0011
import Formalism.LocalToGlobal.Columns.ChainLawPhiPf
import Formalism.LocalToGlobal.Columns.XtSumSingle
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete
import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.LocalToGlobal.Columns.Bundle0041
import Formalism.LocalToGlobal.Columns.Bundle0040
import Formalism.LocalToGlobal.Columns.StabilizerMapMaximalIndex

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawPsi
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Join

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem clPsi_restr {n c : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) :
    LinearMap.funLeft E E (Fin.castAdd c) (clL_ext c κ v) = κ (LinearMap.funLeft E E (Fin.castAdd c) v) := by
  funext l
  show (clL_ext c κ v) (Fin.castAdd c l) = κ (LinearMap.funLeft E E (Fin.castAdd c) v) l
  rw [clL_ext_apply, ciExtM_castAdd,
    show κ (LinearMap.funLeft E E (Fin.castAdd c) v) = κ.toLinearMap (LinearMap.funLeft E E (Fin.castAdd c) v) from rfl,
    ← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, LinearMap.funLeft_apply]

theorem clPsi_atNL {n c : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) :
    atNL E (n + c) n (clL_ext c κ v) = atNL E (n + c) n v := by
  unfold atNL
  split_ifs with h
  · have hc : 0 < c := by omega
    have e : (⟨n, h⟩ : Fin (n + c)) = Fin.natAdd n ⟨0, hc⟩ := rfl
    simp only [LinearMap.proj_apply]
    rw [e, clL_ext_natAdd]
  · rfl

theorem clPsi_joinCol {n' c' n c : ℕ} (κ₀ : Sp E n' ≃ₗ[E] Sp E n') (κ : Sp E n ≃ₗ[E] Sp E n) (x₀ : HomE E n' n) (y' : Sp E n) :
    joinCol (c' := c') (c := c) (κ.symm.toLinearMap ∘ₗ x₀ ∘ₗ κ₀.toLinearMap) (κ.symm y') =
      (clL_ext c κ.symm).toLinearMap ∘ₗ joinCol (c' := c') (c := c) x₀ y' ∘ₗ (clL_ext c' κ₀).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe]
  rw [clL_ext_inX, clPsi_restr, clPsi_atNL]
  simp only [map_add, map_smul]

end Join

section Psi

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem clPsi_phiHyp (hX : X.Ok) (hPr : Pr.Ok) (hm : R.m = m2 + 2) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Pr.vGs) :
    PhiGSLawHyp P (qOf P) R.k R.rS R.r R.t (m2 + 1) (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1)) := by
  obtain ⟨hk0, hr0, hrN0, -⟩ := ranks_frame_inequalities R hm (j := m2) (by omega)
  obtain ⟨hk1, -, hrN1, -⟩ := ranks_frame_inequalities R hm (j := m2 + 1) le_rfl
  exact ⟨ciQ_mem P, ciQ_notMem_sq hX hPr hP, by omega, hk0, hk1, hr0, t_pos R, by simpa using hrN0.symm, hrN1.symm⟩

end Psi

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.CpTopEquivOnOf
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Inv

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word}

open Classical in

theorem xiTop_inv (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {i : ℕ} (hn : TopNum R i)
    (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x z : HomE X.E (R.N i) (R.N (i + 1))) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N)
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiTop Ch sel mu cst i p Y p' (x + z) = XiTop Ch sel mu cst i p Y p' x := by
  obtain ⟨w0, hw0, rfl⟩ := (mem_mulLat _ _ _).1 hz
  have hG := mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ
  have hphi : phiT X.K p.deco.1 p'.deco.1 (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) = phiT X.K p.deco.1 p'.deco.1 x := by
    refine phiT_add_mul X.K p.deco p'.deco (Sall sel mu u) (fun P => Finset.mem_union_left _ P.2) (Pr.T u) (fun P => ?_) x _ ?_
    · have h1 : Pr.piT u ∈ P.1.asIdeal := mem_asIdeal_of_mem_divs P.2
      rw [← hPr.piT_norm u]
      exact P.1.asIdeal.mul_mem_right _ h1
    · refine (mem_mulLat _ _ _).2 ⟨(((∏ P : rowSG Pr sel mu, Col.qOf P.1) ^ cst.B : ℕ) : 𝓞 X.E) • w0,
        Submodule.smul_mem _ _ hw0, ?_⟩
      rw [smul_smul]
      unfold cBof
      push_cast
      rfl
  rw [XiTop_eq, XiTop_eq, hphi]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw := hG w
  have hu := ciQ_notMem_sq hX hPr hw
  have hq0 : ((qOf w.1 : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have ef : frsF sel mu p w = p.deco.1.liftFr ⟨w.1, hw⟩ := by
    unfold frsF
    rw [dif_pos hw]
  obtain ⟨k, hk⟩ : ∃ k, cst.B = k + 1 := ⟨cst.B - 1, by have := hc.B_pos; omega⟩
  refine topDat_congr Ch sel mu cst hX hPr hc hn w hw _ _ _ (fun j => by rw [ef]; exact xtRepY_int sel mu cst p.deco Y hYm w hw j) fun j => ?_

  have h1 : frsF sel mu p w (Pi.single j 1) ∈ p.deco.1.at w.1 := (frame_mem_lattice_iff_std' sel mu p w hw _).2 (ciSingle_mem j)
  have h2 : w0 (frsF sel mu p w (Pi.single j 1)) ∈ localization₂ w.1.asIdeal p'.deco.1.N := hw0 w.1 (Finset.mem_union_right _ w.2) _ h1
  have h3 : (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) ∈ stdAt X.E (R.N (i + 1)) w.1 :=
    (frame_mem_lattice_iff_std' sel mu p' w hw _).1 (by rw [LinearEquiv.apply_symm_apply]; exact h2)
  have e : ∀ l, inFr (frsF sel mu p w) (frsF sel mu p' w) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) (Pi.single j 1) l =
      inFr (frsF sel mu p w) (frsF sel mu p' w) x (Pi.single j 1) l + (qOf w.1 : X.E) *
        ((qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) *
          (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) l) := by
    intro l
    simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smul_apply, map_add, Pi.add_apply]
    rw [← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, Pi.smul_apply, smul_eq_mul, map_natCast, hk]
    congr 1
    field_simp
    ring
  have hd : ∀ l, IntAt w.1 ((qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) *
      (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) l) := fun l =>
    ((xtIntAt_qpow (qOf w.1) k).mul (intAt_inv_qOf_pow_mul_cBof sel mu cst w)).mul ((ciMem_stdAt _ _).1 h3 l)
  refine ⟨forall_congr' fun l => ?_, fun _ l => ?_⟩
  · rw [e l]
    exact ciIntAt_add_iff ((ciIntAt_q (q := qOf w.1)).mul (hd l))
  · rw [e l]
    exact redP_add_natCast_mul (ciQ_mem w.1) (hd l)

end Inv

section Thm

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word} {m2 : ℕ}

def CpTopEquivOn (T : ChTh W sel mu u m2) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (Θm : LevQFam X.E X.K (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) : Prop :=
  CplEq2On (S := midGSD W sel mu L u m2 b) (S₁ := frmGSD (colValF W sel mu u (m2 + 1 + 1)) Λm Θm) (ybCpl W sel mu cst L u m2 b hY)
    (fun p Y p' => cpTopK W Ch sel mu cst T (m2 + 1) p Y p')

variable {W Ch sel mu cst L}

set_option maxHeartbeats 1600000 in

theorem cpTopEquivOn_of (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (hn : TopNum R (m2 + 1))
    (T : ChTh W sel mu u m2)
    (hOk : ThDist.Ok (T.th (m2 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (colValF W sel mu u (m2 + 1)).rho
      (colValF W sel mu u (m2 + 1 + 1)).rho (rhoS Ch sel mu (m2 + 1)) (rhoT Ch sel mu (m2 + 1)))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (Θm : LevQFam X.E X.K (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K)))
    (hLaw : TopLawG Ch sel mu cst L m2 Λm b) (hRow : LastRow Λm) :
    CpTopEquivOn W Ch sel mu cst L T b hY Λm Θm := by
  classical
  intro g g' p (Y : Set (Sp X.E (R.N (m2 + 1)))) p' hYm
  change Y ∈ ybSet sel mu cst p.deco.1.N at hYm
  have hT : 0 < Pr.T u := (hPr.T_prime u).pos
  have hG := mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ
  choose κ hκ hκr using fun w : rowSG Pr sel mu => frsF_smul sel mu p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w (hG w)
  choose κ' hκ' hκr' using fun w : rowSG Pr sel mu => frsF_smul sel mu p' Λm Θm g' w (hG w)
  have hfr : frsF sel mu (g • p) = fun w => g.1.1 * frsF sel mu p w * (κ w).1 := funext hκ
  have hfr' : frsF sel mu (g' • p') = fun w => g'.1.1 * frsF sel mu p' w * (κ' w).1 := funext hκ'
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  have hN' : IsSdLat p'.deco.1.N := ⟨p'.deco.2.lat, p'.deco.2.uni⟩
  have hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco := rfl
  have hdeco' : (g' • p').deco = (g'.1, (g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs)) • p'.deco := rfl
  have hYm1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (gmap g.1.1 p.deco.1.N) := (ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm
  have hcc : (((Λm.chr g'.2.1 * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ)) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (((Λm ⟨w.1, hG w⟩).lam ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hG w⟩, g'.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
          ((((L.levG (m2 + 1) b ⟨w.1, hG w⟩).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hG w⟩, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K) := by
    rw [prod_rowSG_eq_prod_vGs_of_QE_empty sel mu hQ (fun w =>
      (((Λm w).lam ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) w, g'.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
        ((((L.levG (m2 + 1) b w).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) w, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K))]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, levFam_chr_apply_coe, levFam_chr_apply_coe, Finset.prod_mul_distrib]
    simp only [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]
  show cpTopK W Ch sel mu cst T (m2 + 1) (g • p) ((fun v => g.1.1 v) '' (Y : Set (Sp X.E (R.N (m2 + 1))))) (g' • p') =
    (frmGSD (colValF W sel mu u (m2 + 1 + 1)) Λm Θm).ρ g' ∘ₗ cpTopK W Ch sel mu cst T (m2 + 1) p Y p' ∘ₗ (midGSD W sel mu L u m2 b).ρ g⁻¹
  unfold cpTopK
  rw [if_pos (show (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N from hYm1), if_pos hYm, hfr, hfr']
  refine (kerOf_move hOk (cBof_pos sel mu cst u hT) hN hN' (frsF sel mu p) (frsF sel mu p') g.1 g'.1 κ κ'
    _ _ (((Λm.chr g'.2.1 * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ)) : X.K)
    (fun x z hz => xiTop_inv Ch sel mu cst hX hPr hc hQ hn p Y p' x z hYm hz) ?_).trans ?_
  · intro x
    rw [XiTop_eq, XiTop_eq, hdeco, hdeco', phiT_smul]
    simp only [hfr, hfr', inFr_move]
    rw [hcc]
    refine prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ _ fun w => ?_
    have hw := hG w
    obtain ⟨hne, hdiff, hqm⟩ := ybSet_props2 sel mu cst hYm w hw
    have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro z hz
      apply (frame_mem_lattice_iff_std' sel mu p w hw _).1
      rw [LinearEquiv.apply_symm_apply]
      exact hz
    obtain ⟨a, ha, hra⟩ : repY ((fun v => g.1.1 v) '' Y) ∈ (fun v => g.1.1 v) '' Y := representative_mem (hne.image _)
    have hr0 := representative_mem hne
    have e2 : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (g.1.1 a)) = (frsF sel mu p w).symm a := by
      rw [LinearEquiv.eq_symm_apply]
      apply g.1.1.injective
      have := LinearEquiv.apply_symm_apply (g.1.1 * frsF sel mu p w * (κ w).1) (g.1.1 a)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
      exact this
    have hδ : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (repY ((fun v => g.1.1 v) '' Y))) - (frsF sel mu p w).symm (repY Y) ∈
        stdAt X.E (R.N (m2 + 1)) w.1 := by
      rw [← hra, e2, ← map_sub]
      exact hFst _ (hdiff _ ha _ hr0)
    have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      rw [← LinearEquiv.map_smul]
      exact hFst _ (hqm _ hr0)
    exact topDat_law hc hn hLaw hRow w hw ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hw⟩, g.2.1.2 _ (Set.mem_univ _)⟩
      ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, g'.2.1.2 _ (Set.mem_univ _)⟩ (κ w) (κ' w) (hκr w) (hκr' w)
      (ciQ_notMem_sq hX hPr hw) _ _ _ hδ hq
  · show _ = (frmRho (colValF W sel mu u (m2 + 1 + 1)) Λm Θm g') ∘ₗ _ ∘ₗ
      (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g⁻¹)
    simp only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, levQFam_chr_eq_one_of_QE_empty sel mu hQ, mul_one, Prod.fst_inv, Prod.snd_inv, map_inv,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

end Thm

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.OneCosetSymmetricAndNonvanishing
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section J

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem oneCosetSymmetric_and_nonvanishing (σ : X.K →+* ℂ) {m2 : ℕ} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} (hB : OcbBase Ch sel mu cst m2)
    (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) (b3 : LiftFromResidueParabolicProduct Ch sel mu cst m2) (hG : OcbGrpGLoc Ch sel mu cst m2)
    (hC : OcbChrGLoc Ch sel mu cst m2) (hΛ : OcbLevIs Ch Λ m2) : OneCosetSym Ch sel mu cst Λ m2 ∧ NonVanSym Ch sel mu cst m2 :=
  oneCosetSym_of σ hB hQ residueFieldUnfolding_claims_hold.1 residueFieldUnfolding_claims_hold.2 (reductionExistsInLatticeStabilizer_holds Ch sel mu cst σ m2) b3 hG hC hΛ

end J

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.StabilizerMapTopIndexAltAlt
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 : ℕ}
  {Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} {hSG : Pr.vGs ⊆ SG'} {ΛM : LevFam X.E X.K (R.N R.m - 1) SG'} {hm : R.m = m2 + 2}
  (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

attribute [local instance] ptYAct

def stabilizerMapMaximalIndex (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      MulAction.stabilizer ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).G
        (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
          (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
            (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))) where
  toFun s := ⟨(((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))⁻¹ *
      extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
      ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)), by
    have h1 := ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).mv_smul
      (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))
    refine MulAction.mem_stabilizer_iff.2 ?_
    show (_ * _ * _) • ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).sec (topIdx L₀ m2 Λt Θt hm)).rep
      (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))) = _
    rw [mul_smul, mul_smul, h1, extYg_smul, inv_smul_eq_iff, h1]⟩
  map_one' := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ 1 _ * _ = 1
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) 1 (one_smul _ _) = 1 := by
      have e1 : (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)) = 1 := map_one (extR R hSG)
      apply Prod.ext
      · show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1 = 1
        rw [e1]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).2 = 1
          rw [e1]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * ((extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1.1) * frameOfY u P.1 _ = 1
          rw [e1]
          have e2 : ((1 : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs).1 : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) = 1 := rfl
          rw [e2]
          group
    rw [e, mul_one, inv_mul_cancel]
  map_mul' s t := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ (s.1 * t.1) _ * _ =
      (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) * _) *
        (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) * _)
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) (s.1 * t.1) (MulAction.mem_stabilizer_iff.1 (s * t).2) =
        extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
          extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) := by
      have em : extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1) = extR R hSG (s.1.1, s.1.2.1) * extR R hSG (t.1.1, t.1.2.1) :=
        map_mul (extR R hSG) (s.1.1, s.1.2.1) (t.1.1, t.1.2.1)
      apply Prod.ext
      · show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1 = (extR R hSG (s.1.1, s.1.2.1)).1 * (extR R hSG (t.1.1, t.1.2.1)).1
        rw [em]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).2 = (extR R hSG (s.1.1, s.1.2.1)).2 * (extR R hSG (t.1.1, t.1.2.1)).2
          rw [em]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1.1 * frameOfY u P.1 _ =
            ((frameOfY u P.1 _)⁻¹ * (extR R hSG (s.1.1, s.1.2.1)).1.1 * frameOfY u P.1 _) *
              ((frameOfY u P.1 _)⁻¹ * (extR R hSG (t.1.1, t.1.2.1)).1.1 * frameOfY u P.1 _)
          rw [em]
          show _ * ((extR R hSG (s.1.1, s.1.2.1)).1.1 * (extR R hSG (t.1.1, t.1.2.1)).1.1) * _ = _
          group
    rw [e]
    group

def stabMapY (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      FamStabS (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 sec R.m) (tilY W cst L₀ u m2 Λt Θt hSG ΛM hm c) :=
  stabilizerMapMaximalIndex (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) sec hPr hpi hL hQ c

end Top

end Formalism.L2.Col.Sc
end
end

