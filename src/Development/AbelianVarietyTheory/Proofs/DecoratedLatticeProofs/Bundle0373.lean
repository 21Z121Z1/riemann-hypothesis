import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusCop

theorem natCoprime_of_zmod_mul_one_sub : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g →
    ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  intro I g T M hg hMg hz
  obtain ⟨t, ht, hc⟩ := hz
  obtain ⟨-, hint, hu, -⟩ := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I g hg
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  set q : ℚ := (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) / (g : ℚ) with hqdef
  have hgq : (g : I.E) * (q : I.E) = (M : I.E) * (1 - (T : I.E)) := by
    have : (g : ℚ) * q = (M : ℚ) * (1 - (T : ℚ)) := by
      rw [hqdef]; field_simp; push_cast; ring
    have := congrArg (fun x : ℚ => (x : I.E)) this
    simpa using this
  have key : Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E) = t := by
    apply hu.mul_left_cancel
    rw [← hc]
    calc (g : I.E ⊗[I.F] Af I.F) * Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E)
        = Formalism.UG.inclE (F := I.F) (Af I.F) ((g : I.E) * (q : I.E)) := by rw [map_mul, map_natCast]
      _ = Formalism.UG.inclE (F := I.F) (Af I.F) ((M : I.E) * (1 - (T : I.E))) := by rw [hgq]
      _ = _ := by rw [map_mul, map_sub, map_one, map_natCast, map_natCast]
  have hq : (q : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := (hint _).1 (key ▸ ht)
  obtain ⟨b, hb⟩ := hq
  have h1 : IsIntegral ℤ (algebraMap ℚ I.E q) := by
    rw [eq_ratCast, ← hb]; exact RingOfIntegers.isIntegral_coe b
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ I.E).injective).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : (M : ℤ) * (1 - (T : ℤ)) = (g : ℤ) * n := by
    have hn' : (n : ℚ) = q := by simpa using hn
    have : (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) = (((g : ℤ) * n : ℤ) : ℚ) := by
      rw [hqdef] at hn'
      push_cast
      rw [hn']
      field_simp
      push_cast; ring
    exact_mod_cast this
  have h5 : (g : ℤ) ∣ 1 - (T : ℤ) := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one ⟨n, h3⟩ ?_
    rw [Int.gcd_natCast_natCast]; exact hMg.symm
  have hd1 : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 := by
    have a : ((Nat.gcd T g : ℕ) : ℤ) ∣ (T : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
    have b : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 - (T : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans h5
    have := dvd_add b a
    simpa using this
  exact Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using hd1))

end GlobalTheory.TorusCop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaQEmpty
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepLevLaw

theorem omegaQ_empty {D : D7} {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dif_pos (fun PP hP => absurd hP (Finset.notMem_empty PP))]
  simp

set_option maxHeartbeats 1000000 in
open Classical in

theorem stepLevLaw : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → ∀ ω, IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω → ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → ∀ κ ∈ levS s.V s.β s.L, κ ∈ GfC s.V ∧ ω (κ, 1) f = Lev.levChi s.V s.β s.L κ • f := by
  intro D c hc k s s' hs hs' ω hW ξ f₀ f hv κ hκ
  refine ⟨hκ.1, ?_⟩
  have hPg : s.L.Pg = c.Pg := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [hL]; rfl
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← hPg, ← Finset.union_empty s.L.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hc k k.isLt
  have hlev : Lev.finE s.V κ ∈ lev D.sp.cm s.V.gram s.β s.L := hκ.2
  have sg : Lev.finE s.V κ ∈ St s.β := parLev_St hlev.1
  have sh : Lev.finE s'.V 1 ∈ St s'.β := by rw [map_one]; exact Subgroup.one_mem _
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
    hs.selfDual hs'.selfDual hs.frame hs'.frame hf he' (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT
    hκ.1 (Subgroup.one_mem _) sg sh
  set G : ∀ PP : Pl D.host.E, GL (Fin s.V.rank) (kP PP) := fun PP => redFn s.β PP (Lev.finE s.V κ) with hG
  have h1' : ω (κ, 1) f₀ = ((∏ PP ∈ c.Pg, c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_inv, mul_one, hG]
  have hoG := GlobalTheory.T.levelPlacesDatum_mul_right_source_level D s.V.rank s'.V.rank s.L (c.chi (↑k + 1)) G (fun PP hP => parLev_g hlev.1 hP) hlev.2
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame κ 1 sg sh) _
    ((s.L.P.chi ⟨_, hlev.2⟩ * (∏ PP ∈ s.L.Pg, ∏ i ∈ Finset.range s.L.s, s.L.cg (i + 1) PP (dBlk (blkOf s.L.r s.L.t) (i + 1) (G PP))) *
      ∏ PP ∈ s.L.Pg, (c.chi (↑k + 1) PP (GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D s.V s'.V s.β s'.β κ 1 sg sh x
      have i0 : IsHalf e (actO s.V s'.V κ⁻¹ 1⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V κ 1 x ▸ GlobalTheory.SplitHecke.isHalf_actO κ 1 H,
          fun H => GlobalTheory.SplitHecke.isHalf_actO _ _ H⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), omegaQ_empty, omegaQ_empty, mul_one, mul_one]
        simp only [map_one, redFn_one, inv_one, Units.val_one, Matrix.one_mul]
        exact hoG (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H => hx ⟨i0.1 H.1, i1.1 H.2⟩, mul_zero])
  rw [h2]
  congr 1
  unfold Lev.levChi levFn
  rw [hQ, Finset.prod_empty, mul_one, extendOne_of_mem _ hlev.2, ← Units.val_mul, ← hPg, Finset.prod_inv_distrib]
  congr 1
  rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]

end GlobalTheory.ChainOnto.StepLevLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanFixesBasisAndIdemp
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ScalW

open Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hA_eV_eV (a b : Fin D.R.rS) : hA X.B.I (eV X a) (eV X b) = 0 := by
  rw [eV, eV, HidaSetting.eR, HidaSetting.eR, hA_crd, X.ee]
  simp

theorem hA_fV_fV (a b : Fin D.R.rS) : hA X.B.I (fV X a) (fV X b) = 0 := by
  rw [fV, fV, HidaSetting.fR, HidaSetting.fR, hA_crd, X.ff]
  simp

theorem hA_eV_fV (a b : Fin D.R.rS) : hA X.B.I (eV X a) (fV X b) = if a = b then 1 else 0 := by
  rw [eV, fV, HidaSetting.eR, HidaSetting.fR, hA_crd, X.ef]
  split_ifs <;> simp

theorem hA_fV_eV (a b : Fin D.R.rS) : hA X.B.I (fV X a) (eV X b) = if b = a then 1 else 0 :=
  hA_f_e X a b

theorem hA_zV_eV (a : Fin D.R.rS) : hA X.B.I (zV X u) (eV X a) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u)
  rw [(X.zu_orth u a).1, map_zero] at h
  rw [zV, eV, HidaSetting.zR, HidaSetting.eR, hA_crd, ← h]
  simp

theorem hA_zV_fV (a : Fin D.R.rS) : hA X.B.I (zV X u) (fV X a) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u)
  rw [(X.zu_orth u a).2, map_zero] at h
  rw [zV, fV, HidaSetting.zR, HidaSetting.fR, hA_crd, ← h]
  simp

theorem hA_eV_zV (a : Fin D.R.rS) : hA X.B.I (eV X a) (zV X u) = 0 := by
  rw [zV, eV, HidaSetting.zR, HidaSetting.eR, hA_crd, (X.zu_orth u a).1]
  simp

theorem hA_fV_zV (a : Fin D.R.rS) : hA X.B.I (fV X a) (zV X u) = 0 := adelicHermitian_hyperbolicF_anisotropic_eq_zero X u a

theorem hA_zV_zV : hA X.B.I (zV X u) (zV X u) =
    -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
  rw [zV, HidaSetting.zR, hA_crd, X.zu_norm]
  simp

theorem divN_zero' : divN X.B.I (D.mem u).A.T 0 = 0 := by
  simp [divN]

theorem prj_eV (b : Fin D.R.rS) : prj X u (eV X b) = eV X b := by
  simp only [prj, hA_fV_eV, hA_eV_eV, hA_zV_eV, divN_zero', ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, sub_zero]

theorem prj_fV (b : Fin D.R.rS) : prj X u (fV X b) = fV X b := by
  simp only [prj, hA_fV_fV, hA_eV_fV, hA_zV_fV, divN_zero', ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, zero_add, sub_zero]

theorem prj_zV : prj X u (zV X u) = zV X u := by
  have hT : ((D.mem u).A.T : ℕ) ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have h : divN X.B.I (D.mem u).A.T (-(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) = -1 := by
    rw [show -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (-1) by ring]
    exact Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul X.B.I _ hT _
  simp only [prj, hA_fV_zV, hA_eV_zV, hA_zV_zV, h, zero_smul, Finset.sum_const_zero, zero_add,
    neg_smul, one_smul, sub_neg_eq_add]

theorem prj_prj (y : VA X.B.I) : prj X u (prj X u y) = prj X u y := by
  have hL : ∀ z, prjL X u z = prj X u z := fun _ => rfl
  rw [← hL (prj X u y)]
  conv_lhs => arg 2; rw [prj]
  simp only [map_sub, map_add, map_sum, map_smul]
  simp only [hL, prj_eV, prj_fV, prj_zV]
  rfl

theorem prj_fix_idem : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧
      GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) ∧
    GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u ∧
    ∀ y, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.prj X u y) = GlobalTheory.ScalW.prj X u y :=
  fun _ X u => ⟨fun a => ⟨prj_eV X u a, prj_fV X u a⟩, prj_zV X u, prj_prj X u⟩

end GlobalTheory.ScalW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanSelfAdjoint
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalW

open Formalism.L2.SG.Pf.unitaryCongruence in

theorem prj_selfAdjoint : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x y : VA X.B.I),
    hA X.B.I (GlobalTheory.ScalW.prj X u x) y = hA X.B.I x (GlobalTheory.ScalW.prj X u y) := by
  intro D X u x y
  have hT : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hsum : ∀ (w : VA X.B.I) (g : Fin D.R.rS → VA X.B.I), hA X.B.I w (∑ a, g a) = ∑ a, hA X.B.I w (g a) :=
    fun w g => map_sum (hL X.B.I w) g Finset.univ
  have hd : ∀ c, divN X.B.I (D.mem u).A.T c = divN X.B.I (D.mem u).A.T 1 * c := by
    intro c; unfold divN; ring
  have hs : sigA X.B.I (divN X.B.I (D.mem u).A.T 1) = divN X.B.I (D.mem u).A.T 1 := by
    have h2 := congrArg (sigA X.B.I) (gmul_divN X.B.I _ hT 1)
    rw [map_mul, map_natCast, map_one] at h2
    rw [← divN_gmul X.B.I _ hT (sigA X.B.I _), h2]
  rw [hA_symm X.B.I y]
  simp only [prj, hA_sub_right, hA_add_right, hA_smul_right, hsum, map_sub, map_add, map_sum, map_mul]
  rw [hd (hA X.B.I (zV X u) x), hd (hA X.B.I (zV X u) y), map_mul, hs]
  simp only [← hA_symm]
  rw [add_comm (∑ a, _ * hA X.B.I x (eV X a))]
  simp only [mul_comm (hA X.B.I x _)]
  ring

end GlobalTheory.ScalW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjReferenceFrameOnFlagBasisModLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RefProjFlag

open Formalism.L2.SG.PoincareInHH.Cut.GU

variable {D : D7} (X : HidaSetting D)

theorem hA_zero_right' (u : VA X.B.I) : hA X.B.I u 0 = 0 := by
  have h := Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right X.B.I u 0 0
  rwa [zero_smul, zero_mul] at h

theorem intsmul_Lf' {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {y : VA X.B.I}
    (hy : y ∈ X.B.I.Lf) : t • y ∈ X.B.I.Lf :=
  X.B.I.Lf.smul_mem ⟨t, ht⟩ hy

theorem orthProjReferenceFrame_mem_finiteAdelicLattice {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf := by
  have he : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hf : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  refine sub_mem (add_mem (Submodule.sum_mem _ fun a _ => ?_) (Submodule.sum_mem _ fun a _ => ?_)) ?_
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (hf a) hy) (he a)
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (he a) hy) (hf a)
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I hz hy) hz

theorem orthProjReferenceFrame_mem_levelMultiple_of_coeff_congr {y : VA X.B.I} (hf : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) y))
    (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) y)) (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 y)) :
    GlobalTheory.ScalW.prj0 X y ∈ mL X.B.I X.B.g :=
  sub_mem (add_mem (sum_mL X _ _ hf fun a => (X.vectorsInLattice.1 a).1) (sum_mL X _ _ he fun a => (X.vectorsInLattice.1 a).2))
    (smul_mL X hz X.vectorsInLattice.2.1)

theorem sub_orthProjReferenceFrame_mem_levelMultiple_of_congr (b : VA X.B.I) (α β : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (γ : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hb : b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0) ∈ mL X.B.I X.B.g)
    (hα : ∀ a, ZMod' X.B.I X.B.g (α a - hA X.B.I (X.f0 a) b))
    (hβ : ∀ a, ZMod' X.B.I X.B.g (β a - hA X.B.I (X.e0 a) b))
    (hγ : ZMod' X.B.I X.B.g (γ - hA X.B.I X.z0 b)) : GlobalTheory.ScalW.prj0 X b - b ∈ mL X.B.I X.B.g := by
  have e : GlobalTheory.ScalW.prj0 X b - b = (γ - hA X.B.I X.z0 b) • X.z0
      - (b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0))
      - ∑ a, (α a - hA X.B.I (X.f0 a) b) • X.e0 a - ∑ a, (β a - hA X.B.I (X.e0 a) b) • X.f0 a := by
    simp only [GlobalTheory.ScalW.prj0, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [e]
  exact sub_mem (sub_mem (sub_mem (smul_mL X hγ X.vectorsInLattice.2.1) hb) (sum_mL X _ _ hα fun a => (X.vectorsInLattice.1 a).1))
    (sum_mL X _ _ hβ fun a => (X.vectorsInLattice.1 a).2)

theorem orthProjReferenceFrame_flagE_sub_mem_levelMultiple (c : Fin D.R.rS) : GlobalTheory.ScalW.prj0 X (X.e0 c) - X.e0 c ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ (fun a => if a = c then sigA X.B.I 1 else 0) 0 0 ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Zsw_ite X 1 (X.gramIntegral c a).2.2
  · intro a; exact Z0 X (X.gramIntegral a c).1
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).1)

theorem orthProjReferenceFrame_flagF_sub_mem_levelMultiple (c : Fin D.R.rS) : GlobalTheory.ScalW.prj0 X (X.f0 c) - X.f0 c ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ 0 (fun a => if a = c then 1 else 0) 0 ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.gramIntegral a c).2.1
  · intro a; exact Zswap X (X.gramIntegral a c).2.2
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).2)

theorem orthProjReferenceFrame_flagZ_sub_mem_levelMultiple : GlobalTheory.ScalW.prj0 X X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ 0 0 (-1) ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.formsAtZero.2 a).2
  · intro a; exact Z0 X (X.formsAtZero.2 a).1
  · have := Zneg X X.formsAtZero.1
    rw [neg_add, add_comm] at this
    rwa [sub_eq_add_neg]

theorem orthProjReferenceFrame_middle_mem_levelMultiple (c c' : Fin D.R.k) : GlobalTheory.ScalW.prj0 X (X.bw c + X.bwd c') ∈ mL X.B.I X.B.g := by
  refine orthProjReferenceFrame_mem_levelMultiple_of_coeff_congr X (fun a => ?_) (fun a => ?_) ?_
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g ((X.weightVectorsIntegral c).2.2 a).2.1 ((X.weightVectorsIntegral c').2.2 a).2.2.2
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g ((X.weightVectorsIntegral c).2.2 a).1 ((X.weightVectorsIntegral c').2.2 a).2.2.1
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g (X.weightVectorsIntegral c).1 (X.weightVectorsIntegral c').2.1

theorem flagVec_Lf (j : ℕ) : flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf := by
  unfold flagVec
  split_ifs
  · exact (X.vectorsInLattice.1 _).1
  · exact add_mem (X.vectorsInLattice.2.2 _).1 (X.vectorsInLattice.2.2 _).2
  · exact X.vectorsInLattice.2.1
  · exact (X.vectorsInLattice.1 _).2
  · exact zero_mem _

theorem prj0_flagVec_mem_mL_or_sub_mem_mL : ∀ (D : D7) (X : HidaSetting D), (∀ y ∈ X.B.I.Lf, GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf) ∧
    ∀ j : ℕ, flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf ∧
      (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) ∈ mL X.B.I X.B.g) ∧
      (¬ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k) →
        GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ mL X.B.I X.B.g) := by
  intro D X
  refine ⟨fun y hy => orthProjReferenceFrame_mem_finiteAdelicLattice X hy, fun j => ⟨flagVec_Lf X j, ?_, ?_⟩⟩
  · rintro ⟨h1, h2⟩
    have h3 : ¬ j < D.R.rS := by omega
    have h4 : j - D.R.rS < D.R.k := by omega
    rw [flagVec, dif_neg h3, dif_pos h4]
    exact orthProjReferenceFrame_middle_mem_levelMultiple X _ _
  · intro h
    unfold flagVec
    split_ifs with h1 h2 h3 h4
    · exact orthProjReferenceFrame_flagE_sub_mem_levelMultiple X _
    · exact absurd ⟨by omega, by omega⟩ h
    · exact orthProjReferenceFrame_flagZ_sub_mem_levelMultiple X
    · exact orthProjReferenceFrame_flagF_sub_mem_levelMultiple X _
    · simp only [GlobalTheory.ScalW.prj0, hA_zero_right', zero_smul, Finset.sum_const_zero, add_zero, sub_zero]
      exact zero_mem _

end GlobalTheory.RefProjFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalAdelicMatricesSelfAnnihilator
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramAnnih

variable {D : D7} {m n : ℕ}

theorem pairing_rat (T : Matrix (Fin m) (Fin m) D.host.E) (ψ : AddChar (AF D.host.F) ℂ)
    (ξ : Matrix (Fin m) (Fin n) D.host.E) (x : Mx D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) x =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (GlobalTheory.MixModel.rat (ξᴴ * T) ⬝ x))) := by
  rw [rat_mul, rat_conjTranspose]
  rfl

theorem rat_single (j : Fin n) (i : Fin m) (e : D.host.E) :
    GlobalTheory.MixModel.rat (D := D) (Matrix.single j i e) = Matrix.single j i (incA D e) :=
  Matrix.map_single j i e (incA D)

theorem trace_tmul_half (t : AF D.host.F) :
    Algebra.trace (AF D.host.F) (AE D) (t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹) = t := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have e : (2 : D.host.E)⁻¹ = algebraMap D.host.F D.host.E 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]
  simp

theorem ratMx_annihilator : ∀ (D : D7) (m n : ℕ) (T : Matrix (Fin m) (Fin m) D.host.E), IsHermND D.sp.cm.sig T → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ x : Mx D m n, (∀ γ ∈ ratMx D m n, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) ↔ x ∈ ratMx D m n) ∧ ∀ γ ∈ ratMx D m n, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ γ x = 1) → γ = 0 := by
  intro D m n T hT ψ hψ
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hU : IsUnit T.det := isUnit_iff_ne_zero.2 hT.2
  refine ⟨fun x => ⟨fun h => ?_, ?_⟩, ?_⟩
  · have key : ∀ i j (e : D.host.E), ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * x i j)) = 1 := by
      intro i j e
      have h1 := h _ (rat_mem (Matrix.single j i e * T⁻¹)ᴴ)
      rw [pairing_rat, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul_cancel_right _ _ hU, rat_single,
        Matrix.trace_single_mul, smul_eq_mul] at h1
      exact h1
    have hent : ∀ i j, ∃ e : D.host.E, x i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e =>
        (GlobalTheory.SWQ.Annihilator.self_annihilator D.host.F inferInstance ψ hψ).2 _ fun c =>
          (congrArg ψ (GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c)).trans (key i j (c • e))
    choose M hM using hent
    exact ⟨Matrix.of M, Matrix.ext fun i j => (hM i j).symm⟩
  · rintro ⟨η, rfl⟩ _ ⟨ξ, rfl⟩
    change GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) (GlobalTheory.MixModel.rat η) = 1
    have e : Matrix.trace (GlobalTheory.MixModel.rat (D := D) (ξᴴ * T * η)) =
        (1 : AF D.host.F) ⊗ₜ[D.host.F] Matrix.trace (ξᴴ * T * η) :=
      (AddMonoidHom.map_trace (incA D) _).symm
    rw [pairing_rat, ← rat_mul, e, GlobalTheory.LatVac.trace_tmul, one_mul]
    exact hψ.2.2.1 _
  · rintro _ ⟨ξ, rfl⟩ h
    change GlobalTheory.MixModel.rat ξ = 0
    have hM : ξᴴ * T = 0 := by
      refine Matrix.ext fun j i => ?_
      by_contra ha
      replace ha : (ξᴴ * T) j i ≠ 0 := ha
      obtain ⟨t, ht⟩ := hψ.2.2.2
      have h1 : GlobalTheory.IndefiniteRowSideFullHecke.GramMatrixBlocks.pairing T ψ (GlobalTheory.MixModel.rat ξ) _ = 1 :=
        h (Matrix.single i j (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)))
      have e : (t ⊗ₜ[D.host.F] ((2 : D.host.E)⁻¹ * ((ξᴴ * T) j i)⁻¹)) * GlobalTheory.MixModel.rat (D := D) (ξᴴ * T) j i =
          t ⊗ₜ[D.host.F] (2 : D.host.E)⁻¹ := by
        change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (ξᴴ * T) j i) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel_right₀ ha]
      rw [pairing_rat, Matrix.trace_mul_comm, Matrix.trace_single_mul, smul_eq_mul, e, trace_tmul_half] at h1
      exact ht h1
    have h0 : ξᴴ = 0 := by
      rw [← Matrix.mul_nonsing_inv_cancel_right T ξᴴ hU, hM, Matrix.zero_mul]
    rw [Matrix.conjTranspose_eq_zero.1 h0, rat_zero]

end GlobalTheory.GramAnnih
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDetRootCharMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_detRootChar_mul : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (n : ℕ), Even n → ResEta D μ n → ∀ e, IsSplitIdem D e → ∀ (s g : GA D V), SuppAt e V s → ∀ x₀ x x₁, IsDetAt e V s x₀ → IsDetRoot V g x → IsDetRoot V (s * g) x₁ → μ x₁ = μ x₀ * μ x := by
  first | exact @GlobalTheory.SplitRootProd.mu_root_mul | exact GlobalTheory.SplitRootProd.mu_root_mul | (intros; apply GlobalTheory.SplitRootProd.mu_root_mul <;> assumption)
end

