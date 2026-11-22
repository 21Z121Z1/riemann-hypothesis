import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0631
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicHermitianSpaceOfNegativeIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

theorem posIndex_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature M p q) : posIndex M = p ∧ posIndex (-M) = q := by
  obtain ⟨e, P, hP⟩ := h
  set A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix _ _ ℂ).map (starRingEnd ℂ) with hA
  have hAc : A.map (starRingEnd ℂ) = (P : Matrix _ _ ℂ) := by
    ext i j; simp [hA]
  have hdet : A.det ≠ 0 := by
    have hu := Matrix.isUnits_det_units P
    have h2 := RingHom.map_det (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    rw [RingHom.mapMatrix_apply] at h2
    rw [hA, ← h2]
    exact (map_ne_zero _).2 hu.ne_zero
  have hc : A.transpose * M.reindex e e * A.map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    rw [hAc, ← hP]; rfl
  have hcn : A.transpose * (-M).reindex e e * A.map (starRingEnd ℂ) = -Formalism.UG.Jpq p q := by
    rw [← hc]
    have : (-M).reindex e e = -(M.reindex e e) := by ext; simp
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  have hJn : -Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (-1 : ℂ)) (fun _ => 1)) := by
    rw [hJ, Matrix.diagonal_neg]
    congr 1
    ext i; rcases i with i | i <;> simp
  have hre : ∀ N : Matrix n n ℂ, posIndex N = posIndex (N.reindex e e) := fun N =>
    (posIndex_submatrix_equiv N e.symm).symm
  constructor
  · rw [hre, ← posIndex_congr _ hdet, hc, hJ, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp
  · rw [hre, ← posIndex_congr _ hdet, hcn, hJn, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp

theorem hT_coords {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (u : Fin S.rank → E) :
    S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = ∑ b, ∑ a, star (u a) * S.gram a b * u b := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [starRingEnd_apply]
  ring

end GlobalTheory.IsoNegIdx

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

theorem exists_isotropic_of_negIdx : ∀ (D : D7) (S : HSp D) (k : ℕ), NegIdx S k → 1 ≤ k → k + 1 ≤ S.rank → 3 ≤ S.rank →
    ∃ x : S.V, x ≠ 0 ∧ S.hT x x = 0 := by
  intro D S k hS hk1 hk2 hn
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, star x = FD.cc x := fun _ => rfl

  have hsig : ∀ φ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S.gram.map φ) (S.rank - k) k := by
    intro φ
    obtain ⟨ρ, h | h⟩ := GlobalTheory.MassLink.tauE_or' D φ
    · subst h
      simpa [gramAt] using hS ρ
    · have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hS ρ)
      rw [Matrix.map_map] at h1
      have e : (⇑(starRingEnd ℂ) ∘ ⇑(tauE D ρ)) = ⇑φ := by
        funext x
        rw [Function.comp_apply, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [e] at h1

  set G : Matrix (Fin S.rank) (Fin S.rank) D.host.E := S.gram.transpose with hGdef
  have hG : ∀ a b, FD.cc (G a b) = G b a := fun a b => by
    simp only [hGdef, Matrix.transpose_apply, ← hst]
    exact S.herm.eq _ _
  have hform : ∀ u, S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = FD.herm G u u := fun u => by
    rw [hT_coords, FD.herm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [hGdef, Matrix.transpose_apply, hst]
    ring
  have hGφ : ∀ φ : D.host.E →+* ℂ, G.map φ = S.gram.map (ComplexEmbedding.conjugate φ) := fun φ => by
    ext a b
    simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq]
    rw [← hG b a, GlobalTheory.Published.embedding_cc]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  have key : ∀ u, FD.herm G (P.mulVec u) (P.mulVec u) = FD.herm (Matrix.diagonal d) u u := fun u => by
    rw [GlobalTheory.Published.LandherrSt.herm_mulVec, hPd]
  have hne : ∀ u, u ≠ 0 → S.frame.equivFun.symm (P.mulVec u) ≠ 0 := fun u hu h => by
    apply hu
    apply Matrix.eq_zero_of_mulVec_eq_zero hP
    have h3 := congrArg S.frame.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h3
  by_cases hz : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨_, hne (Pi.single i 1) (by simp), ?_⟩
    rw [hform, key, GlobalTheory.UTrans.herm_diagonal_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Pi.single_apply, hj]
  push_neg at hz

  have hs : ∀ φ : D.host.E →+* ℂ, (∃ i, 0 < (φ (d i)).re) ∧ ∃ j, (φ (d j)).re < 0 := by
    intro φ
    have hc : (P.map φ).transpose * G.map φ * (P.map φ).map (starRingEnd ℂ) = Matrix.diagonal fun i => φ (d i) := by
      have h1 : (P.map φ).map (starRingEnd ℂ) = (P.map FD.cc).map φ := by
        ext a b
        simp [GlobalTheory.Published.embedding_cc]
      rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPd, Matrix.diagonal_map (map_zero φ)]
    have hdet : (P.map φ).det ≠ 0 := by
      have h2 := RingHom.map_det φ P
      rw [RingHom.mapMatrix_apply] at h2
      rw [← h2]
      exact (map_ne_zero φ).2 hP
    obtain ⟨hp, hq⟩ := posIndex_of_hasSignature (hGφ φ ▸ hsig (ComplexEmbedding.conjugate φ))
    have hcn : (P.map φ).transpose * (-G.map φ) * (P.map φ).map (starRingEnd ℂ) =
        Matrix.diagonal fun i => -φ (d i) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hc, Matrix.diagonal_neg]
    rw [← posIndex_congr _ hdet, hc, posIndex_diagonal] at hp
    rw [← posIndex_congr _ hdet, hcn, posIndex_diagonal] at hq
    constructor
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hp]; omega)
      exact ⟨i, (Finset.mem_filter.1 hi).2⟩
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hq]; omega)
      refine ⟨i, ?_⟩
      have := (Finset.mem_filter.1 hi).2
      simp only [Complex.neg_re] at this
      linarith
  obtain ⟨z, hz0, hzz⟩ := GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hz hs
  exact ⟨_, hne z hz0, by rw [hform, key, hzz]⟩

end GlobalTheory.IsoNegIdx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg GlobalTheory.KeyFourth GlobalTheory.AllWt GlobalTheory.FlatLine
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyRoot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_keySec_of_generic (h : GenFrEx Xo c) (b : ∀ Z : Comp Xo c, Om Z) (hb0 : ∀ Z, b Z ≠ 0)
    (hb : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R) :
    ∃ ρ : KeySec Xo c, ∀ Z, evC h Z (ρ.ρ : Rul Xo c) = b Z := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (keyEx Dw) b fun C => (hb C).1
  obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-keyEx Dw) (fun Z => (b Z)⁻¹) fun C => by
    have := (hb C).2
    rw [mul_inv, ← Units.val_inv_eq_inv_val] at this
    simpa only [kch, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib] using this
  have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
  rw [add_neg_cancel, secZ_zero_eq] at hm
  have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
  rw [secZ_zero_eq] at h1
  have hff : f * f' = 1 := by
    refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
    rw [← GlobalTheory.CompHt.genVal_apply h, map_sub, map_mul, map_one, GlobalTheory.CompHt.genVal_apply h,
      GlobalTheory.CompHt.genVal_apply h, hfb, hfb', mul_inv_cancel₀ (hb0 Z), sub_self]
  exact ⟨⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf⟩, hfb⟩

theorem rule_tied_eq : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g g' : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (e' : Fin g' ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (y : FrPt Xo c K) (Φ Φ' : FibKey Xo K y.x), Tied e y.s y.u Φ → Tied e' y.s y.u Φ' → κ K Φ'.key = κ K Φ.key := by
  classical
  intro κ hH hF E _ _ _ H Dw l Xo c g g' e e' K _ _ _ y Φ Φ' hT hT'
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg hg'
  have hid : y.x = spMap (RingHom.id K) ≫ y.x := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 y.x y.x y.s y.s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ y.x y.x y.x hid hid).2.1 1 y.s y.s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) y.x y.x Φ Φ' y.s y.s hid h1 h1' hss
  let π : Equiv.Perm (Fin Φ'.T.g) := e'.trans (e.symm.trans (finCongr hg2.symm))
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = y.u (e (i.cast hg2)).1 (e (i.cast hg2)).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have hπ : ∀ i, Φ'.v i = v (π i) := fun i => by
    have h2 : e ((π i).cast hg2) = e' i := by simp [π]
    have h3 := hvu (π i)
    rw [h2] at h3
    exact Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext ((hv' i).trans h3.symm) ((Over.w _).trans (Over.w _).symm))
  have hcomb : ∀ i, IsLieComb (π.permMatrix K i) v (Φ'.v i) := fun i => by
    have h2 : π.permMatrix K i = Pi.single (π i) 1 := by
      funext j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, eq_comm]
    have h3 := Formalism.L2.PjFree.isCombAt_single (x := y.x) (v := fun j => (v j).left ≫ Φ'.m.φ)
      (fun j => by rw [hvu]; exact y.tan _ _) (π i)
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h3
    have : w = v (π i) := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext hw ((Over.w _).trans (Over.w _).symm))
    rw [h2, hπ, ← this]
    exact hw'
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have e2 := hH K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen Φ'.th Φ'.th_ne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    1 _ (fun i => by simp [constFn]) hcomb
  have e3 : (π.permMatrix K).det ^ 4 = 1 := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> rw [h] <;> norm_num
  apply Units.ext
  rw [one_pow, _root_.one_mul] at e2
  refine e2.trans ?_
  exact (congrArg₂ (fun a b : K => a * b) e3 e1).trans (_root_.one_mul _)

set_option maxHeartbeats 1000000 in

theorem exists_keySec_pow_four : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ ρ : KeySec Xo c, ∀ Z : Comp Xo c, ∃ a : c.F, a ≠ 0 ∧ idem Z * (ρ.ρ : Rul Xo c) ^ 4 = a • (idem Z * (K : Rul Xo c)) := by
  intro κ k₁ k₂ k₄ k₃ E _ _ _ H Dw l Xo c g e σ r U K hσ hU hF hpq hK hval
  obtain ⟨-, -, -, -, -, g₀, e₀, F, -⟩ := hU
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F _ ξ₀ Gm φ
    hcc him hφ
  have T : ∀ k, ThetaData e₀ F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g₀ e₀ F _ M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g₀ e₀ F _ M k (T k)
  have hok : FramesOK e₀ F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g₀ e₀ F _ M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g₀ e₀ F _ M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g₀ e₀ F _ M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g₀ e₀ F _ M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g₀ e₀ F _ M un hσ hM hξ hok
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e₀ j).1) ξ₀ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e₀ j).1 ξ₀ ≠ 0 := (map_ne_zero _).2 hne
    positivity
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g₀ e₀ (Om Z) (genFr h Z) hpq
  let v : ∀ Z : Comp Xo c, (Om Z)ˣ := fun Z => κ (Om Z) (Ψ Z).key
  have hv : ∀ C : FChart h, ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e₀ C.y.s C.y.u Φ ∧
      GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧ ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
    intro C
    haveI := C.sm
    haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
    haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
    haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g₀ e₀ C.R C.y hpq
    obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g₀ e₀ (Om C.Z) C.yg hpq
    obtain ⟨u, hu⟩ := k₄ C.R Φ.key
    refine ⟨Φ, u, hΦ, hu, ?_⟩
    rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ k₁ k₂ E H Dw l Xo c g₀ e₀ (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
    exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g₀ e₀ _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm
  have hroot : ∀ C : FChart h, ∃ (a : c.F) (b : C.R), a ≠ 0 ∧
      ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) = a • (b : Om C.Z) ^ 4 := by
    intro C
    obtain ⟨Φ, u, hΦ, hu, huv⟩ := hv C
    letI : Algebra c.F ℂ := σ.toAlgebra
    haveI := C.sm
    haveI := GlobalTheory.GeomConn.isDomain_tensor C.R.val Subtype.val_injective (hF C.Z) ℂ
    choose z hz using fun ψ : C.R →ₐ[c.F] CAt σ => hL.bc _ _ ψ C.y
    have hex : ∀ ψ, ∃ w, RootVal (unfOf e₀ F M un) (z ψ) w := fun ψ => by
      obtain ⟨k, x, t, ht⟩ := hU₀.2.2.1 (z ψ)
      exact ⟨_, k, x, t, ht, rfl⟩
    choose ρ hρ using hex
    obtain ⟨a, b, ha, hab⟩ := exists_eq_smul_pow (K := c.F) (A := C.R) (n := 4) (by norm_num) u
      (pow_ne_zero 4 (div_ne_zero hC (pow_ne_zero g₀ Complex.two_pi_I_ne_zero))) ρ
      (fun m V s hV hs => GlobalTheory.T.continuousOn_keySection_complexValue E H Dw l Xo c σ g₀ e₀ F _ M T un hσ hM hξ hun hok C.R C.y m V s
        (fun p => z (s p)) (fun p => ρ (s p)) hV hs (fun p _ => hz _) fun p _ => hρ _)
      (fun ψ => by
        obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : FibKey Xo ℂ (z ψ).x, Tied (S := ℂ) e₀ (z ψ).s (z ψ).u Ψ' :=
          @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g₀ e₀ ℂ _ _ σ.toAlgebra (z ψ) hpq
        exact (rule_eq_of_rootVal k₁ k₂ k₃ T hun hpq hC (fun k => by rw [(hMG k).2]) (hρ ψ) Ψ' hΨ').trans
          (congrArg _ (hu ℂ _ _
            (@GlobalTheory.T.universal_triple_fibres_base_change_key_data E _ _ _ H Dw l Xo c g₀ e₀ _ ℂ _ _ _ _ σ.toAlgebra ψ C.y (z ψ) Φ Ψ' (hz ψ) hΦ hΨ'))))
    exact ⟨a, b, ha, by rw [← huv, hab]; rfl⟩
  have hgen : ∀ Z : Comp Xo c, ∃ (a : c.F) (b : Om Z), a ≠ 0 ∧ (v Z : Om Z) = a • b ^ 4 := by
    intro Z
    obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h (Om Z) (genFr h Z)
    obtain rfl := GlobalTheory.Reg.SecGlue.chart_comp Z C ψ z t h1 h2
    obtain ⟨a, b, ha, hab⟩ := hroot C
    refine ⟨a, b / ((kch C.t : (Om C.Z)ˣ) : Om C.Z), ha, ?_⟩
    rw [div_pow, ← smul_div_assoc, ← hab, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_div_cancel_left₀ _ (pow_ne_zero 4 (kch C.t).ne_zero)]
  choose a b ha hab using hgen
  have hb0 : ∀ Z, b Z ≠ 0 := fun Z h0 => (v Z).ne_zero (by rw [hab, h0]; simp)
  have hbC : ∀ C : FChart h, ((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R ∧
      (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z)⁻¹ ∈ C.R := by
    intro C
    obtain ⟨-, u, -, -, huv⟩ := hv C
    haveI := C.sm
    haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
    haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
    have hint : ∀ (x : Om C.Z) (y : C.R), x ^ 4 = y → x ∈ C.R := fun x y hxy => by
      have hi : IsIntegral C.R (x ^ 4) := hxy ▸ isIntegral_algebraMap (R := C.R) (x := y)
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by norm_num : 0 < 4) hi
      exact hw ▸ w.2
    have hc' : ∀ (x : c.F) (y : C.R), ((algebraMap c.F C.R x * y : C.R) : Om C.Z) = x • (y : Om C.Z) := fun x y => by
      rw [Algebra.smul_def]
      rfl
    have e₁ : (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z) ^ 4 = (a C.Z)⁻¹ • ((u : C.R) : Om C.Z) := by
      rw [huv, Units.val_mul, Units.val_pow_eq_pow_val, hab, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (ha _), one_smul, mul_pow]
    refine ⟨hint _ _ (e₁.trans (hc' _ _).symm),
      hint _ (algebraMap c.F C.R (a C.Z) * ((u⁻¹ : (C.R)ˣ) : C.R)) ?_⟩
    rw [inv_pow, e₁, hc']
    refine inv_eq_of_mul_eq_one_right ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (ha _), one_smul, ← Subalgebra.coe_mul, Units.mul_inv]
    rfl
  obtain ⟨ρ, hρ⟩ := exists_keySec_of_generic h b hb0 hbC
  refine ⟨ρ, fun Z => ⟨(a Z)⁻¹, inv_ne_zero (ha Z), ?_⟩⟩
  have hKZ : evC h Z (K : Rul Xo c) = (v Z : Om Z) := by
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
    refine (hval (Om Z) (genFr h Z) Φ hΦ).trans ?_
    exact congrArg Units.val (rule_tied_eq κ k₁ k₂ E H Dw l Xo c g₀ g e₀ e (Om Z) (genFr h Z) (Ψ Z) Φ (hΨ Z) hΦ)
  have h4 : (ρ.ρ : Rul Xo c) ^ 4 ∈ GlobalTheory.AllWt.secZ Xo c ((4 : ℤ) • keyEx Dw) := by
    have h2 := mul_mem_secZ ρ.mem ρ.mem
    have h3 := mul_mem_secZ h2 h2
    rw [← pow_two, ← pow_two, ← pow_mul] at h3
    have e4 : (4 : ℤ) • keyEx Dw = keyEx Dw + keyEx Dw + (keyEx Dw + keyEx Dw) := by abel
    rw [e4]
    exact h3
  have hq := mul_mem_secZ (mul_mem_secZ h4 (inv_mem_secZ hK)) (idem_mem_secZ Z)
  have hi := idem_mem_secZ Z
  rw [add_neg_cancel, add_zero, secZ_zero_eq] at hq
  rw [secZ_zero_eq] at hi
  have h0 := sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hq (Submodule.smul_mem _ (a Z)⁻¹ hi)) fun Z' => by
      by_cases hZ : Z' = Z
      · subst hZ
        have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
        rw [← GlobalTheory.CompHt.genVal_apply h, map_sub, map_mul, map_mul, map_pow, map_smul, map_units_inv]
        simp only [GlobalTheory.CompHt.genVal_apply h]
        rw [h3, hρ, hKZ, hab, _root_.mul_one, smul_inv₀, mul_smul_comm, mul_inv_cancel₀ (pow_ne_zero 4 (hb0 Z')),
          sub_self]
      · exact evC_eq_zero h hZ (sub_mem (mul_mem_suppOn _ (idem_mem_suppOn Z))
          (Submodule.smul_mem _ _ (idem_mem_suppOn Z))))
  rw [← smul_mul_assoc, ← h0, mul_right_comm, Units.inv_mul_cancel_right, mul_comm]

end GlobalTheory.KeyRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerMatrixFirstOrderDeformation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
open GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.KSFam

theorem conj_embK' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  rw [embK_coe, embK_coe]
  show starRingEnd ℂ (τ ((H.bar z : 𝓞 E) : E)) = τ (z : E)
  rw [H.9 z, NumberField.IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem ksFamily : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  intro E _ _ _ H Dw l Xo c hP S _ _ y x' h1 h2
  suffices hM : ∃ M, GlobalTheory.FlagTan.IsKSR (psiSet H) y x' M by
    obtain ⟨M, hM⟩ := hM
    exact ⟨M, fun K _ _ ψ y' hy => GlobalTheory.FlagTan.isKSR_iff_isKS.mp (GlobalTheory.FlagTan.IsKSR.baseChange hP hy hM)⟩

  letI : GrpObj ((Over.pullback x').obj Xo.univ.t.G) := Functor.grpObjObj (F := Over.pullback x')
  letI : GrpObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    Functor.grpObjObj (F := Over.pullback (GlobalTheory.DeRham.epsRed S))
  have hA' := isGrpPullback_pullback Xo.univ.t.G x'
  have hi := isGrpPullback_pullback ((Over.pullback x').obj Xo.univ.t.G) (GlobalTheory.DeRham.epsRed S)
  have hA : IsGrpPullback ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G))
      Xo.univ.t.G y.x (pullback.fst _ _ ≫ pullback.fst _ _) := (hi.comp hA').congr h2 rfl
  haveI : IsCommMonObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hA
  have hab := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hsm := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA'
  have hab0 := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA
  have hsm' : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback x').obj Xo.univ.t.G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm
  have hsm0 : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm'

  obtain ⟨ψ, hpol, hiso, hperf, hmax⟩ := GlobalTheory.T.exists_polarization_form_isotropic_filtration hP Xo hA

  obtain ⟨a', ha'⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hA'
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a' hi
  have haπ : ∀ z, (a.act z).left ≫ (pullback.fst _ _ ≫ pullback.fst _ _) =
      (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (Xo.univ.t.act.act z).left := by
    intro z
    rw [← Category.assoc, ha z, Category.assoc, ha' z, Category.assoc]
  have hadj := GlobalTheory.T.polarizationForm_adjoint_cmAction_moduli_point hP Xo hA a haπ hpol

  obtain ⟨ub, hub1, hubT, hubE, hubS⟩ := GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing y hA a haπ
  have hex : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), ∃ h, IsLieImage h (ub k.1 k.2) := fun k =>
    (hP.2.1 S _ _ hab0 hsm0).1.2 _ (hubT k.1 k.2)
  choose hb hhb using hex
  obtain ⟨hspan, hlin⟩ := GlobalTheory.T.grp_pullback_basis_lift_compatible hP y hA ub hub1 hb hhb
  have hreg := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing hP hi hab' hsm'
  have hcomp := fun z f w (e : IsKSValue hi f w) => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hi a a' ha z e
  have heig : ∀ (k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ))) (z : 𝓞 E),
      act (dp0 S) (𝟙 _) a z (hb k) - (algebraMap c.F S).comp (embK c k.1) z • hb k ∈
        Fil ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) := by
    intro k z
    haveI := a.hom z
    have e1 := (hhb k).push (a.act z)
    rw [hubE] at e1
    rw [act_apply]
    exact e1.sub_mem ((hhb k).smul _)
  have key : ∀ (τ : psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → S, ∃ w,
      IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hi ψ hb ⟨conjEmb τ.1, j⟩ w := fun τ j =>
    GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_ring hi a (fun z => H.bar z) ψ hiso hmax hperf hadj hreg hcomp
      (fun σ => (algebraMap c.F S).comp (embK c σ)) ub hb hspan hlin heig hubS τ.1 (conjEmb τ.1)
      (fun z => by simp only [RingHom.comp_apply, conj_embK']) j
  choose cf hcf using key
  exact ⟨fun k => cf k.1 k.2.1 k.2.2, _, inferInstance, _, inferInstance, _, _, _, hi, ψ, ub, hb, hA, hA', rfl, hpol,
    hub1, fun σ k => hhb ⟨σ, k⟩, fun τ j => hcf τ j⟩

end GlobalTheory.KSFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationExtensionFieldStatement
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_extension_field : ∀ (F F' : IntermediateField ℚ ℂ) (hle : F ≤ F'), FiniteDimensional ℚ F' → ∀ (W : ValuationSubring ℂ) (K : Type) [Field K] [IsAlgClosed K] (O : ValuationSubring K) (g : F →+* K), (∀ x : F, (x : ℂ) ∈ W ↔ g x ∈ O) → ∃ g' : F' →+* K, (∀ x : F, g' (IntermediateField.inclusion hle x) = g x) ∧ ∀ x : F', (x : ℂ) ∈ W → g' x ∈ O := by
  first | exact @GlobalTheory.PlaceExt.exists_extend_compatible | exact GlobalTheory.PlaceExt.exists_extend_compatible | (intros; apply GlobalTheory.PlaceExt.exists_extend_compatible <;> assumption)
end

