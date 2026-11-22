import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0281
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0277
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0282
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelAtBadPrimes
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplLev

theorem cong_of_nearAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g₁ g₂ : GL (Fin N) E)
    (hn : 0 < n) (h₁ : NearAt P n x g₁) (h₂ : NearAt P n x g₂) (a b : Fin N) :
    IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) :=
  GlobalTheory.T.rationalApproximations_differ_by_congruent_to_one P n x g₁ g₂ hn h₁ h₂ a b

theorem cong_seam {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (g : Sp X.E N ≃ₗ[X.E] Sp X.E N)
    (h : ∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ *
      (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) :
    ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) :=
  GlobalTheory.T.fieldIso_matrixCongruence_automorphismCongruence s P n g h

section Cong1

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

theorem cong_mem_level_chr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j hj b P k hk
  classical
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 (cst.D P) k (hL.cst_ok.D_pos P) hk
  set κ : GLint X.E (R.N j) P.1 := ⟨k, hkG⟩ with hκdef
  have hψ : cst.psi P (Loc.n1Arg (GlobalTheory.CongLevel.extE (cOf R j) k)) = 1 := by
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords]
    exact hL.cst_ok.psi_int P 0 (by simpa using GlobalTheory.CongLevel.intAt_nat P.1 0)
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  by_cases hP : P.1 ∈ Pr.vGs
  · have hD1 : cst.D P = 1 := hL.depthG P hP
    have hdu := GlobalTheory.Mem.Col2.degOneUnram_of_mem_vGs hX.ok hPr hP
    have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) :=
      fun a ha h0 => GlobalTheory.TopStep.intAt_div_of_redP hdu.2 ha h0
    have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (k x) = redV P.1 x := by
      have h1 := GlobalTheory.TopStep.redGL_of_prinCong (by omega : 0 < cst.D P) hkC
      intro x hx
      have h2 := GlobalTheory.TopStep.redV_redGL κ hx
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have hh := hL.stabG j b P hP
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe cst.sharp j P.1 hP hd (L.h j b P) hh k hkG hred, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    have hh' := hh
    unfold lamYat at hh'
    rw [if_pos hP] at hh'
    have hcong := GlobalTheory.CongLevel.conj_cong (qOf P.1) _ _ (L.h j b P) hh'
      (GlobalTheory.CongLevel.extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd k hkG hred)
    have h1 := GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one Ch mu cst.sharp j P.1 hP ((qOf P.1 : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have hx' := hx
        unfold lamYat at hx' ⊢
        rw [if_pos hP] at hx' ⊢
        have h2 := hcong x hx'
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, hψ, inv_one, one_mul]
  · have hstd : ∀ x, x ∈ lamYat (Pr := Pr) (R := R) j P.1 ↔ x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro x
      unfold lamYat
      rw [if_neg hP]
      unfold LocE.lamY
      rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
      simp only [LocE.scE, Pi.zero_apply, Nat.cast_zero, ite_self, zpow_zero, inv_one, one_mul]
    have hbd := hL.boundQ j b P hP
    have hbd' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
        ((qOf P.1 : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := fun x hx => by
      have h1 := hbd x ((hstd x).2 hx)
      exact ⟨(hstd _).1 h1.1, (hstd _).1 h1.2⟩
    have hjD : j + 1 ≤ cst.D P := by
      have h1 := hL.depthQ' P hP
      have h2 := hL.hm
      omega
    have hg := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ hkC hjD hbd'
    have hginv := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ⁻¹ (inv_mem hkC) hjD hbd'
    have einv : ((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) (κ⁻¹).1 * L.h j b P := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, GlobalTheory.CongLevel.extE_inv, mul_assoc]
      rfl
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ k, ?_⟩, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) =
          (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P := by simp
      show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) ∈ Jat (Pr := Pr) cst.sharp j P.1
      rw [e]
      unfold Jat
      rw [if_neg hP]
      refine GlobalTheory.T.mem_parahoric_of_cong_one_mod_q P.1 (R.k + j) (R.N j) (cOf R j) _ hg ?_
      rw [einv]
      exact hginv
    · unfold chiInv
      rw [hψ, inv_one, one_mul]
      unfold lamRow
      rw [if_neg hP]
      exact GlobalTheory.T.blockDetResidueChar_eq_one_of_cong_mod_q P.1 _ (R.k + j) (R.N j) (R.N j + cOf R j) _ (by omega) hg

end Cong1

section Lift

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col GlobalTheory.TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem levAt_mul {n : ℕ} {Λ : LevFam X.E X.K n Pr.vGs} {Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))} {P : rowSG Pr sel mu}
    {κ κ₂ : GLint X.E n P.1} {c c₂ : X.Kˣ} (h : LevAt Λ Θ P κ c) (h₂ : LevAt Λ Θ P κ₂ c₂) : LevAt Λ Θ P (κ * κ₂) (c * c₂) := by
  refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
  · obtain ⟨h1, e1⟩ := h.1 hP
    obtain ⟨h2, e2⟩ := h₂.1 hP
    refine ⟨by rw [map_mul]; exact mul_mem h1 h2, ?_⟩
    rw [e1, e2, ← map_mul]
    exact congrArg _ (Subtype.ext (map_mul _ _ _).symm)
  · obtain ⟨h1, e1⟩ := h.2 hQ hP
    obtain ⟨h2, e2⟩ := h₂.2 hQ hP
    exact ⟨mul_mem h1 h2, by rw [e1, e2, ← map_mul]; rfl⟩

theorem levAt_of_lift (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (b : L.β j) (P : rowSG Pr sel mu) (κ : GLint X.E (R.N j) P.1)
    (r : AutY X R j) (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P))
    (hrx : ∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (κ.1 x)) :
    ∃ c : X.Kˣ, LevAt (L.levG j b) (L.levQ j b) P κ c ∧ (c : X.K) = chiInv Ch sel mu cst j P (L.h j b P) r := by
  by_cases hP : P.1 ∈ Pr.vGs
  · have hmem : GlobalTheory.TopStep.redGL _ P.1 κ ∈ (L.levG j b ⟨P.1, hP⟩).H :=
      (hL.grpG j b ⟨P.1, hP⟩ _).2 ⟨κ.1, ⟨r, hr, hrx⟩, fun x hx => GlobalTheory.TopStep.redV_redGL κ hx⟩
    refine ⟨(L.levG j b ⟨P.1, hP⟩).lam ⟨_, hmem⟩, ⟨fun hP' => ⟨hmem, rfl⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
    exact hL.chrG j b ⟨P.1, hP⟩ ⟨_, hmem⟩ κ.1 r hr hrx fun x hx => GlobalTheory.TopStep.redV_redGL κ hx
  · have hQ := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
    have hmem : κ ∈ (L.levQ j b ⟨P.1, hQ⟩).H := by
      rw [hL.grpQ, Subgroup.mem_subgroupOf]
      exact ⟨r, hr, hrx⟩
    refine ⟨(L.levQ j b ⟨P.1, hQ⟩).lam ⟨κ, hmem⟩, ⟨fun hP' => absurd hP' hP, fun _ _ => ⟨hmem, rfl⟩⟩, ?_⟩
    exact hL.chrQ j b ⟨P.1, hQ⟩ ⟨κ, hmem⟩ r hr hrx

end Lift

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem levAt_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∃ c : SB t μ → t.X.Kˣ,
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
        ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P) (c P)) ∧
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = ((((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.chi κ' : ℂˣ) : ℂ)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie β' κ' κ'' hfr
  classical
  have hL := t.idx_ok μ
  have hC := hTie.levCpl β'
  have hU := (((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U_eq κ'.1).1 κ'.2
  have hov : ∀ P : SB t μ, IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
    intro P
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  choose g zz hg using fun P : SB t μ => hC.1 P _ (hov P) κ'.1 hU.1 (hU.2 _)
  have hchi := hC.2.2 κ' g zz hg
  have key : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
      ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P)⁻¹ c ∧ (c : t.X.K) = zz P := by
    intro P
    obtain ⟨⟨r, hr, hrx, hz⟩, -⟩ := (hg P).1
    have hgint : g P ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := hL.int _ _ P ⟨r, hr, hrx⟩
    set κg : GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := ⟨g P, hgint⟩ with hκg
    set k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := κg⁻¹ * (κ'' P)⁻¹ with hk
    have hcg := cong_of_nearAt (seamP t.seam P.1) ((t.cst μ).D P) _ _ _ (hL.cst_ok.D_pos P) (hg P).2 (hfr P)
    rw [← map_inv, ← map_mul] at hcg
    have hk1 := cong_seam t.seam P.1 ((t.cst μ).D P) k.1 hcg
    obtain ⟨rk, hrk, hrkx, hchik⟩ := cong_mem_level_chr_one t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hPin.fields t.pr_ok hL
      (t.m2 + 1) le_rfl (A.ib (t.m2 + 1) (cpl_lt t μ) β') P k.1 hk1
    obtain ⟨c1, hl1, hc1⟩ := levAt_of_lift hL (A.ib (t.m2 + 1) (cpl_lt t μ) β') P κg r hr hrx
    obtain ⟨c2, hl2, hc2⟩ := levAt_of_lift hL (A.ib (t.m2 + 1) (cpl_lt t μ) β') P k rk hrk hrkx
    have e : κg * k = (κ'' P)⁻¹ := by rw [hk, mul_inv_cancel_left]
    refine ⟨c1 * c2, e ▸ levAt_mul hl1 hl2, ?_⟩
    rw [Units.val_mul, hc1, hc2, hchik, mul_one, hz]
  choose c hc hcv using key
  refine ⟨fun P => (c P)⁻¹, fun P => by have h := (hc P).inv; rwa [inv_inv] at h, ?_⟩
  have e1 : ((∏ P, (c P)⁻¹ : t.X.Kˣ) : t.X.K) = (∏ P, zz P)⁻¹ := by
    rw [Units.coe_prod, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun P _ => by rw [Units.val_inv_eq_inv_val, hcv P]
  have e2 := eq_inv_of_mul_eq_one_left hchi
  have e3 : t.seam.σ₀ ((∏ P, (c P)⁻¹ : t.X.Kˣ) : t.X.K) = (t.seam.σ₀ (∏ P, zz P))⁻¹ := by
    rw [e1, map_inv₀]
  exact e3.trans e2.symm

end Main

end GlobalTheory.CplLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ErrorDataGeneratorsEqColumnPreDatum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem errXS_pi_of_colT : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z), (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS t.full.1).piT = w.px.piT := by
  intro B f T w Z t
  have hc : t.full.1.cols = t.C.herm := t.full.2
  refine ⟨?_, ?_⟩
  · show (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = _
    rw [hc, ← t.C.piG]
    exact (t.std _).gl.piG
  · funext u
    show (t.full.1.cols.atT u).piU = _
    rw [hc, ← t.C.piU u]
    exact (t.std u).piU

end GlobalTheory.Svd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj) in
open GlobalTheory.HeckeUnrExt in

theorem GlobalTheory.HeckeUnrExt.exists_ext_unr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (b : ℤ), χ.IsAlg (fun _ => b) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧ χ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ w₀ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ GlobalTheory.HeightCounting.Blocks.resReal κ = χ ∧ κ.UnrAt w₀ ∧ ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → κ.UnrAt w := by
  intro E _ _ _ ψ a hψ hns w₀ _
  classical
  obtain ⟨M, hM, hlev⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat _ ψ
  obtain ⟨w₁, hw₁s, hw₁⟩ := GlobalTheory.T.exists_other_split_place_with_distinct_real_place E w₀
  set K : ℕ := Module.finrank ℚ E + 1 with hK
  set Q : ℕ := Ideal.absNorm w₁.asIdeal ^ K with hQ
  have hQ0 : 0 < Q := pow_pos (Nat.pos_of_ne_zero fun h => w₁.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _
  set N : ℕ := 3 * M * Q with hN
  have hN0 : 0 < N := by positivity
  let T : Set (HeightOneSpectrum (𝓞 E)) := {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀}
  let T' : Set (HeightOneSpectrum (𝓞 E)) := {w | ∀ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → w' ∈ T}
  have hw₁T : w₁ ∈ T' := fun w' e => by
    refine ⟨?_, fun h => hw₁ (h ▸ e).symm⟩
    by_cases h : w' = w₁
    · exact h ▸ hw₁s
    · exact ⟨w₁, fun h' => h h'.symm, e.symm⟩
  have hT'T : T' ⊆ T := fun w hw => hw w rfl
  have hF : ∀ b : Ideles (maximalRealSubfield E), ideleMap _ E b ∈ levT E T N → ψ.1 b = kap E a (ideleMap _ E b) := by
    intro b hb
    let z : (InfiniteAdeleRing (maximalRealSubfield E))ˣ := Units.map (MonoidHom.fst _ _) b
    have e : b = Units.map (MonoidHom.inl _ _) z * GlobalTheory.Mem.Chr.finPartI _ b :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h1 : ψ.1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 :=
      GlobalTheory.T.realSubfield_heckeChar_finitePart_eq_one E ψ M hlev (fun w hw => (hns w hw).2) w₀ N ⟨3 * Q, by rw [hN]; ring⟩ b hb
    have h2 : kap E a (ideleMap _ E b) = kap E a (ideleMap _ E (Units.map (MonoidHom.inl _ _) z)) := by
      apply Units.ext
      rw [coe_kap, coe_kap]
      rfl
    rw [h2, ← psi_eq_kap E ψ a hψ z]
    conv_lhs => rw [e, map_mul, h1, mul_one]
  have hprin : ∀ ε : Eˣ, diagUnits E ε ∈ levT E T' N → (∀ φ : E →+* ℂ, ‖φ ε‖ = 1) → ε = 1 := by
    intro ε hε hn
    refine Units.ext (GlobalTheory.T.eq_one_of_norm_one_valuation_sub_one_small E (ε : E) w₁ K (by omega) (fun v => ?_) hn ?_)
    · have e : Valued.v (algebraMap E (v.adicCompletion E) (ε : E)) = 1 := hε.1 v
      rw [GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      exact e.le
    · have e : Valued.v (algebraMap E (w₁.adicCompletion E) (ε : E) - 1) ≤ Valued.v (N : w₁.adicCompletion E) := hε.2 w₁ hw₁T
      rw [← map_one (algebraMap E (w₁.adicCompletion E)), ← map_sub,
        ← map_natCast (algebraMap E (w₁.adicCompletion E)), GlobalTheory.UpIdeleMod.valued_algebraMap,
        GlobalTheory.UpIdeleMod.valued_algebraMap] at e
      refine e.trans ?_
      have eN : ((N : ℕ) : E) = algebraMap (𝓞 E) E ((3 * M : ℕ) : 𝓞 E) * algebraMap (𝓞 E) E ((Q : ℕ) : 𝓞 E) := by
        rw [← map_mul, ← Nat.cast_mul, map_natCast]
      rw [eN, map_mul]
      refine (mul_le_of_le_one_left' (HeightOneSpectrum.valuation_le_one _ _)).trans ?_
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
      rw [hQ, Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.absNorm_mem w₁.asIdeal) K
  obtain ⟨ξ, hξ⟩ := glue
    (((ideleMap (maximalRealSubfield E) E).coprod (levT E T N).subtype).coprod (diagUnits E))
    ((MonoidHom.coprod ψ.1 ((kap E a).comp (levT E T N).subtype)).coprod 1) (by
      rintro ⟨⟨b, u, hu⟩, k⟩ h
      change ideleMap (maximalRealSubfield E) E b * u * diagUnits E k = 1 at h
      change ψ.1 b * kap E a u * 1 = 1
      let c := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E
      have h' := congrArg (ideleConj (maximalRealSubfield E) E) h
      have c1 : ideleConj (maximalRealSubfield E) E (ideleMap _ E b) = ideleMap _ E b :=
        Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _)
      have c2 : ideleConj (maximalRealSubfield E) E (diagUnits E k) =
          diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k) :=
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele _ E k
      have c3 : ideleConj (maximalRealSubfield E) E u ∈ levT E T' N := GlobalTheory.T.cmIdeleConj_mem_congruenceUnitIdeles_conj_places E T N u hu
      rw [map_mul, map_mul, map_one, c1, c2, ← h, mul_assoc, mul_assoc, mul_right_inj] at h'
      have h3 : diagUnits E (Units.map c.toRingEquiv.toRingHom.toMonoidHom k / k) =
          u / ideleConj (maximalRealSubfield E) E u := by
        rw [_root_.map_div, div_eq_div_iff_mul_eq_mul, mul_comm, h']
      have h4 := hprin _ (h3 ▸ div_mem (levT_anti E hT'T N hu) c3) fun φ => by
        rw [Units.val_div_eq_div_val, map_div₀, norm_div]
        have : φ (Units.map c.toRingEquiv.toRingHom.toMonoidHom k : Eˣ) = starRingEnd ℂ (φ k) :=
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
        rw [this, Complex.norm_conj, div_self (by simp)]
      have h5 : IsCMField.complexConj E k = k := congrArg Units.val (div_eq_one.1 h4)
      have h6 : (k : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E (k : E)).1 h5
      let k0 : (maximalRealSubfield E)ˣ := Units.mk0 ⟨k, h6⟩ fun h0 => k.ne_zero (congrArg Subtype.val h0)
      have h7 : ideleMap _ E (diagUnits _ k0) = diagUnits E k :=
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k0).trans (congrArg (diagUnits E) (Units.ext rfl))
      have h8 : ideleMap _ E (b * diagUnits _ k0) = u⁻¹ := by
        rw [map_mul, h7, eq_inv_iff_mul_eq_one, mul_right_comm, h]
      have h9 := hF _ (h8 ▸ inv_mem hu)
      rw [h8, map_mul, ψ.2.2, mul_one, map_inv] at h9
      rw [h9, inv_mul_cancel, one_mul])
  have hu : ∀ u ∈ levT E T N, ξ u = kap E a u := fun u hu => by
    simpa using hξ ((1, ⟨u, hu⟩), 1)
  let κ : HChar E := ⟨ξ, ?_, fun k => by simpa using hξ ((1, 1), k)⟩
  swap
  · refine continuous_of_continuousAt_one ξ ((continuous_kap E a).continuousAt.congr ?_)
    filter_upwards [levT_mem_nhds E T (N := N) (by omega)] with x hx
    exact (hu x hx).symm
  have hloc : ∀ w, w ∉ T → κ.UnrAt w := by
    intro w hw x hx
    have hmem : localIdele E w x ∈ levT E T N := by
      refine ⟨fun v => ?_, fun v hv => ?_⟩
      · by_cases hvw : v = w
        · subst hvw
          rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
          exact hx
        · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]
          exact map_one _
      · have hvw : v ≠ w := fun e => hw (e ▸ hv)
        rw [GlobalTheory.HeckeProduct.localIdele_snd_ne E w v hvw]
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    show ξ (localIdele E w x) = 1
    rw [hu _ hmem]
    apply Units.ext
    rw [kap_of_fst a _ (1 : E) (by rw [GlobalTheory.HeckeProduct.localIdele_fst, map_one])]
    simp
  refine ⟨κ, fun φ => if (InfinitePlace.mk φ).embedding = φ then a else 0, fun k => ?_,
    Subtype.ext (MonoidHom.ext fun b => ?_), hloc w₀ fun h => h.2 rfl, fun w hw => hloc w fun h => hw h.1⟩
  · have h1 : infDiag k ∈ levT E T N := by
      refine lev_le_levT E T N ⟨fun v => ?_, fun v => ?_⟩
      · rw [coe_infDiag']
        exact map_one _
      · rw [coe_infDiag']
        show Valued.v ((1 : v.adicCompletion E) - 1) ≤ _
        rw [sub_self, map_zero]
        exact zero_le
    change ((ξ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hu _ h1, kap_of_fst a _ (k : E) (by rw [coe_infDiag']), prod_type]
  · change ξ (ideleMap _ E b) = ψ.1 b
    simpa using hξ ((b, 1), 1)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOneStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne : ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  first | (exact @GlobalTheory.DegOneChar.exists_charLift) | (exact GlobalTheory.DegOneChar.exists_charLift) | (intros; apply GlobalTheory.DegOneChar.exists_charLift  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupWeilElementCharacterKernelStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_weilElement_characterKernel : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) ∧ commutator (Dec (F := E) A) ≤ V ∧ (⟨(g : G E Ω), Weil_le_Dec h g.2⟩ : Dec (F := E) A) ∈ V ∧ ∀ t : Ine (F := E) A, ∀ x ∈ V, (x : G E Ω) = t → ∀ j, ξ j (a (ineIncl h t)) = 1 := by
  first | (exact @GlobalTheory.RoadU.exists_open_sub_charKer) | (exact GlobalTheory.RoadU.exists_open_sub_charKer) | (intros; apply GlobalTheory.RoadU.exists_open_sub_charKer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalLocalOperators
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.FrobOps
open Polynomial

theorem not_dvd_normV {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) (w : HeightOneSpectrum (𝓞 E))
    (h : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  first
  | exact @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem
  | (apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormDivisibility.not_dvd_norm_of_not_mem ..)

theorem norm_le_one {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (m : ℤ) (q e : ℕ) (hq : ¬ l ∣ q) :
    ‖ι.symm ((m : ℂ) / (q : ℂ) ^ e)‖ ≤ 1 := by
  rw [map_div₀, map_pow, map_intCast, map_natCast, norm_div, norm_pow]
  have h1 : ‖((q : ℕ) : Qbar l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hq
  rw [h1, one_pow, div_one]
  exact IsUltrametricDist.norm_intCast_le_one _ m

theorem trace_pow_of_charpoly {a : ℕ} (M : Matrix (Fin a) (Fin a) ℂ) (B : Multiset ℂ)
    (h : M.charpoly = (B.map fun b => X - C b).prod) (n : ℕ) : (M ^ n).trace = (B.map (· ^ n)).sum := by
  rw [Matrix.trace_eq_sum_roots_charpoly, GlobalTheory.CharpolyPow.roots_charpoly_pow, h, Polynomial.roots_multiset_prod_X_sub_C]

theorem iota_trc {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : Γ →* GL (Fin a) (Qbar l))
    (s : Γ) (n : ℕ) :
    ι (trc r (s ^ n)) = ((((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom) ^ n).trace := by
  rw [← Matrix.map_pow, trc, map_pow, Units.val_pow_eq_pow_val, Matrix.trace, Matrix.trace, map_sum]
  rfl

end GlobalTheory.FrobOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletionStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_solvable_cm_extension_abelianCompletion : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ g ∈ Dec (F := maximalRealSubfield E) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) → ∀ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) → commutator (Dec (F := E) A) ≤ V → ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ ∀ g : Dec (F := E) A, (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ↔ g ∈ V := by
  first | exact @GlobalTheory.AboveL.exists_cm_solvDisj_dec_eq | exact GlobalTheory.AboveL.exists_cm_solvDisj_dec_eq | (intros; apply GlobalTheory.AboveL.exists_cm_solvDisj_dec_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_solvable_cm_extension_split_place : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g ∈ Dec (F := E) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ g ∈ Dec (F := maximalRealSubfield M) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  first | exact @GlobalTheory.AboveL.exists_cm_solvable_split | exact GlobalTheory.AboveL.exists_cm_solvable_split | (intros; apply GlobalTheory.AboveL.exists_cm_solvable_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelCoefficientFieldLeCoefficientFieldStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelCoefficientField_le_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ y : t.X.K, ∃ k : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL k = t.seam.σ₀ y := by
  first | exact @GlobalTheory.TwU.kerField_le_rec | exact GlobalTheory.TwU.kerField_le_rec | (intros; apply GlobalTheory.TwU.kerField_le_rec <;> assumption)
end

