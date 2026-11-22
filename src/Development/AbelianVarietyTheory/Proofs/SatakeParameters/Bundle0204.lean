import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0184
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.B0StandardSeriesAdmissible
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem nP_eq_one_of_hP_eq_zero (D : D7) (p : ℕ) (hC : IsResidueClassZero D p) (h0 : hP D p = 0) : nP D p = 1 := by
  have hS : ¬ IsSg D p := by
    intro hs
    unfold IsResidueClassZero at hC
    unfold IsSg at hs
    rw [hC] at hs
    exact absurd hs (by decide)
  unfold nP
  rw [if_neg hS, h0, addOrderOf_zero]

theorem thetaExpansionRealPlaces_stdSer_of_adm : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → OrbitPlaces.ThetaExpansionRealPlaces D p (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hHost h5 hC hP0 N N' L L' P P' hAdm hS hS' G hG
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hcd, hfam⟩ := hHost
  obtain ⟨r, b, hLB, hON, hInt⟩ := hfam N N' L L' hAdm
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := GlobalTheory.T.unitaryMatrix_of_orthonormal_localBasis_allPlaces D p lam σ hcd.2.2.2.2.2.1 h5 hC hP0 N N' L L' P P' hAdm hS hS' r b hLB hON
  have hU := GlobalTheory.T.subst_unitary_logarithmic_coordinates p g2 g3 s2 ε σ F hcd (Fin r) (OrbitPlaces.Pl D × Fin N × Fin N') γ hγ1 (by convert hγ2) _ (hInt G hG)
  rw [← hγ3 c G] at hU
  exact GlobalTheory.T.exponentShape_of_integralClass_oneLetter D p g2 g3 s2 ε σ F hcd (nP_eq_one_of_hP_eq_zero D p hC hP0) N N' c _ hc hU

end GlobalTheory.KerStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConjDet

open ValuativeRel

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_det_mul_sub_one_lt {r t : ℕ} {h : GL (Fin (r + t)) k} (hh : h ∈ blockGrp k r t) :
    valuation k (((h⁻¹ : GL (Fin (r + t)) k).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
  obtain ⟨g, hg⟩ := hh.1
  have hi := ((blockGrp k r t).inv_mem hh).2
  have hinv : (h⁻¹ : GL (Fin (r + t)) k) = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g⁻¹ := by
    rw [← hg, map_inv]
  have hC : ∀ (i : Fin t) (j : Fin r),
      (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t j) ∈ 𝓂[k] := by
    intro i j
    have := hi (Fin.natAdd r i) j
    have hne : Fin.natAdd r i ≠ Fin.castAdd t j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    rw [hinv, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    change valuation k (algebraMap 𝒪[k] k ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t j))) < 1 at this
    exact (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr this)
  have hres : (((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)) *
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r))).map (IsLocalRing.residue 𝒪[k]) = 1 := by
    ext i j
    have e1 : ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val * g.val) (Fin.natAdd r i) (Fin.natAdd r j) =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) (Fin.natAdd r i) (Fin.natAdd r j) := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_apply, Fin.sum_univ_add] at e1
    have hm : ∑ x : Fin r, (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t x) *
        g.val (Fin.castAdd t x) (Fin.natAdd r j) ∈ 𝓂[k] :=
      Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (hC i x)
    have e2 : (((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)) *
        (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r))) i j =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) (Fin.natAdd r i) (Fin.natAdd r j) -
          ∑ x : Fin r, (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t x) *
            g.val (Fin.castAdd t x) (Fin.natAdd r j) := by
      simp only [Matrix.mul_apply, Matrix.submatrix_apply]; rw [← e1]; ring
    rw [Matrix.map_apply, e2, map_sub, (IsLocalRing.residue_eq_zero_iff _).2 hm, sub_zero]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  have hm : ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply,
      hres, Matrix.det_one, map_one, sub_self]
  have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ∀ G : GL (Fin (r + t)) 𝒪[k],
      ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) G).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
        (((G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) := by
    intro G
    rw [show (((G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) =
      algebraMap 𝒪[k] k (G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det from rfl, RingHom.map_det]
    rfl
  rw [hinv, ← hg, e, e]
  simpa only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] using hv

end

end GlobalTheory.BlockConjDet

namespace GlobalTheory.BlockConjDet

theorem blockChar_eq_inv_detDD : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → ∃ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (u : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r (d * b * d⁻¹) ∧ ∀ μ : (s.w.adicCompletion L)ˣ →* ℂˣ, IsTame μ → blockChar μ (Matrix.GeneralLinearGroup.map c.toRingHom a) = (((μ (Units.map c.toMonoidHom u))⁻¹ : ℂˣ) : ℂ) := by
  intro L _ _ _ s r t c _ a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact (WithZero.exp_ne_zero hϖ.symm).elim
  have hdinv : (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val =
      Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹) := by
    have h1 : d.val * Matrix.diagonal (fun i : Fin (r + t) =>
        if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹) = 1 := by
      rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; ext i; split_ifs <;> simp [hϖ0]
    calc (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val
        = (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val * (d.val * Matrix.diagonal (fun i : Fin (r + t) =>
          if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hDD : NG.detDD s r (d * b * d⁻¹) =
      ((a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    let e : Fin t ≃ {x : Fin (r + t) // r ≤ x.val} :=
      { toFun := fun i => ⟨Fin.natAdd r i, by simp⟩
        invFun := fun x => ⟨x.1.val - r, by omega⟩
        left_inv := fun i => by ext; simp
        right_inv := fun x => by ext; simp; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]
    congr 1
    ext i j
    have hn : ∀ x : Fin t, ¬ ((Fin.natAdd r x : Fin (r + t)) : ℕ) < r := by intro x; simp
    simp only [e, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.coe_fn_mk, Units.val_mul,
      hdinv, hd, Matrix.mul_diagonal, Matrix.diagonal_mul, hb]
    rw [if_neg (hn _), if_neg (hn _), mul_comm ϖ, mul_inv_cancel_right₀ hϖ0]
  have hc : c (NG.detDD s r (d * b * d⁻¹)) =
      (((Matrix.GeneralLinearGroup.map c.toRingHom a)⁻¹ : GL (Fin (r + t)) (s.w.adicCompletion L)).val.submatrix
        (Fin.natAdd r) (Fin.natAdd r)).det := by
    rw [hDD, ← map_inv]
    exact RingHom.map_det c.toRingHom _
  have hv := val_det_mul_sub_one_lt ha
  have hne : ∀ x y : s.w.adicCompletion L, ValuativeRel.valuation _ (x * y - 1) < 1 → x ≠ 0 ∧ y ≠ 0 := by
    intro x y h
    constructor <;> rintro rfl <;> simp at h
  obtain ⟨h1, h2⟩ := hne _ _ hv
  have hF : NG.detDD s r (d * b * d⁻¹) ≠ 0 := fun h0 => h1 (by rw [← hc, h0, map_zero])
  refine ⟨Units.mk0 _ hF, rfl, fun μ hμ => ?_⟩
  rw [blockChar_eq μ _ (Units.mk0 _ h2) rfl]
  have ht := hμ (Units.map c.toMonoidHom (Units.mk0 _ hF) * Units.mk0 _ h2) (by
    simp only [Units.val_mul, Units.coe_map, Units.val_mk0]
    rw [show (c.toMonoidHom : _ →* _) (NG.detDD s r (d * b * d⁻¹)) = c (NG.detDD s r (d * b * d⁻¹)) from rfl, hc]
    exact hv)
  rw [map_mul] at ht
  rw [eq_inv_of_mul_eq_one_right ht]

end GlobalTheory.BlockConjDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectors
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Val

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem val_lt_one_of_norm_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => z ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
  have h2 : Filter.Tendsto (fun n : ℕ => e z ^ n) Filter.atTop (nhds 0) := by
    have := ((he.tendsto 0).comp h1)
    simpa [Function.comp_def, map_pow] using this
  have h3 : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  obtain ⟨n, hn⟩ := (h2.eventually h3).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation F (e z ^ n) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hn (not_lt.2 this)

theorem val_natCast_le_one (c : ℕ) : valuation F (c : F) ≤ 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    push_cast
    exact (valuation F).map_add_le ih (by simp)

theorem val_le_one_of_norm_le_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ ≤ 1) :
    valuation F (e z) ≤ 1 := by
  let zi : ℤ_[g] := ⟨z, hz⟩
  have hm := PadicInt.sub_zmodRepr_mem zi
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hm
  have hm' : ‖z - (zi.zmodRepr : ℚ_[g])‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at hm
    exact hm
  have h1 := val_lt_one_of_norm_lt_one e he hm'
  have hz' : e z = e (z - (zi.zmodRepr : ℚ_[g])) + (zi.zmodRepr : F) := by
    rw [map_sub, map_natCast]; ring
  rw [hz']
  exact (valuation F).map_add_le h1.le (val_natCast_le_one _)

theorem norm_lt_one_of_val_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {y : ℚ_[g]}
    (hy : valuation F (e y) < 1) : ‖y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hy0 : y ≠ 0 := by rintro rfl; simp at hc; exact absurd hc (by norm_num)
  have h1 : ‖y⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hc
  have h2 := val_le_one_of_norm_le_one e he h1
  have h3 : valuation F (e y) * valuation F (e y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  have h4 : valuation F (e y) * valuation F (e y⁻¹) ≤ valuation F (e y) * 1 := by gcongr
  rw [h3, mul_one] at h4
  exact absurd hy (not_lt.2 h4)

theorem entry_of_val (e : ℚ_[g] ≃+* F) (he : Continuous e) (x : F) (c : ℕ) (hx : valuation F (x - c) < 1) :
    ∃ hA : ‖e.symm x‖ ≤ 1, PadicInt.toZMod (⟨e.symm x, hA⟩ : ℤ_[g]) = c := by
  have h1 : ‖e.symm x - c‖ < 1 :=
    norm_lt_one_of_val_lt_one e he (by rwa [map_sub, map_natCast, e.apply_symm_apply])
  have hc : ‖(c : ℚ_[g])‖ ≤ 1 := by
    have := PadicInt.norm_le_one (c : ℤ_[g])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  have hA : ‖e.symm x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (e.symm x - c) (c : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le h1.le hc)
  refine ⟨hA, ?_⟩
  let zi : ℤ_[g] := ⟨e.symm x, hA⟩
  have hm : zi - (c : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def]
    simpa using h1
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at hm
  exact hm

end Val

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Mat

variable {g : ℕ} [Fact g.Prime]

def bm (r t : ℕ) (h : Gn g r) : Mt g (r + t) := fun i j =>
  if (i : ℕ) < r ∧ (j : ℕ) < r then entN (h : Mt g r) i j
  else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then entN ((1 : Gn g t) : Mt g t) (i - r) (j - r) else 0

theorem bm_isUnit (r t : ℕ) (h : Gn g r) : IsUnit (bm r t h) := by
  set M := bm r t h with hM
  have h0 : InPar r M := fun i j hj hi => by
    rw [hM]; show bm r t h i j = 0; unfold bm; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = h := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, entN, hM, bm, hi, hj]
  have h2 : br r t M = 1 := by
    ext i j
    simp [br, entN, hM, bm]
  have hd := LabelDet.det_inPar r t M h0
  rw [h1, h2, Matrix.det_one, mul_one] at hd
  rw [Matrix.isUnit_iff_isUnit_det, hd]
  exact Matrix.isUnits_det_units h

theorem blk_val (r t : ℕ) (h : Gn g r) : ((blk r t (r + t) h 1 : Gn g (r + t)) : Mt g (r + t)) = bm r t h := by
  show ((toG (bm r t h) : Gn g (r + t)) : Mt g (r + t)) = bm r t h
  unfold toG
  rw [dif_pos (bm_isUnit r t h)]
  exact IsUnit.unit_spec _

theorem bm_apply (r t : ℕ) (h : Gn g r) (a b : Fin (r + t)) : bm r t h a b =
    if hab : (a : ℕ) < r ∧ (b : ℕ) < r then (h : Mt g r) ⟨a, hab.1⟩ ⟨b, hab.2⟩ else if a = b then 1 else 0 := by
  unfold bm
  by_cases hab : (a : ℕ) < r ∧ (b : ℕ) < r
  · rw [if_pos hab, dif_pos hab]; simp [entN, hab]
  · rw [if_neg hab, dif_neg hab]
    by_cases h2 : r ≤ (a : ℕ) ∧ r ≤ (b : ℕ)
    · rw [if_pos h2]
      have ha : (a : ℕ) - r < t := by omega
      have hb : (b : ℕ) - r < t := by omega
      simp only [entN, dif_pos (And.intro ha hb), Units.val_one, Matrix.one_apply, Fin.ext_iff]
      congr 1
      apply propext
      omega
    · rw [if_neg h2, if_neg]
      intro e; subst e; omega

end Mat

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

theorem blockLift_act (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (r t : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V)
    (hu : u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) (h : GL (Fin r) (ZMod g))
    (h' : GL (Fin (r + t)) F) (hl : GlobalTheory.PendOf.IsLiftN h h') :
    ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  classical
  have hent : ∀ a b : Fin (r + t), ∃ hA : ‖e.symm (h'.val a b)‖ ≤ 1,
      PadicInt.toZMod (⟨e.symm (h'.val a b), hA⟩ : ℤ_[g]) = bm r t h a b := by
    intro a b
    have hab := hl a b
    rw [bm_apply]
    by_cases hc : (a : ℕ) < r ∧ (b : ℕ) < r
    · rw [dif_pos hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he _ _ hab
      exact ⟨hA, by rw [hA', ZMod.natCast_zmod_val]⟩
    · rw [dif_neg hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he (h'.val a b) (if a = b then 1 else 0)
        (by rw [hab]; split_ifs <;> simp)
      exact ⟨hA, by rw [hA']; split_ifs <;> simp⟩
  choose hA hA' using hent
  let A : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g] := fun a b => ⟨e.symm (h'.val a b), hA a b⟩
  have hmap : (PadicInt.toZMod (p := g)).mapMatrix A = bm r t h := by
    ext a b
    exact hA' a b
  have hdet : IsUnit A.det := by
    by_contra hn
    have h1 : A.det ∈ IsLocalRing.maximalIdeal ℤ_[g] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, hmap] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (bm_isUnit r t h)).ne_zero h1
  let A' : GL (Fin (r + t)) ℤ_[g] := Matrix.GeneralLinearGroup.mk'' A hdet
  have hred : red g (r + t) A' = blk r t (r + t) h 1 := by
    ext a b
    rw [blk_val]
    exact hA' a b
  have hh' : Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) A') = h' := by
    ext a b
    show e (algebraMap ℤ_[g] ℚ_[g] (A a b)) = h'.val a b
    rw [PadicInt.algebraMap_apply]
    exact e.apply_symm_apply _
  have hx0 : red g (r + t) (Function.invFun (red g (r + t)) (blk r t (r + t) h 1)) = blk r t (r + t) h 1 :=
    Function.invFun_eq ⟨A', hred⟩
  have hk : red g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A') = 1 := by
    rw [map_mul, map_inv, hx0, hred, inv_mul_cancel]
  have hfix := (Submodule.mem_iInf _).1 hu ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hfix
  have hsplit : h' = Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1)) *
      Matrix.GeneralLinearGroup.map e.toRingHom
        (inc g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A')) := by
    rw [← hh', lift, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hsplit, map_mul, Module.End.mul_apply]
  congr 1

end GlobalTheory.SerSys.BlockLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlocksLtOfParabolicUnipotentRadicalNeBotStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blocks_lt_of_parabolicUnipotentRadical_ne_bot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := by
  first | exact @GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot | exact GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot | (intros; apply GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainInnerStepIntertwinesMatchedHecke
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainStepHecke

theorem haar_fd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : T) (j : ℕ)
    (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · have := hM.νY t j h
    exact ⟨this.1.1, this.2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    have := hM.νY' t
    exact ⟨this.1.1, this.2⟩

theorem step_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P k, Good R t P → k + 1 < D.R.m → VacFix R.ψ (R.ωY t k) P → ∀ cS cT, Match R.ψ (R.ωY t k) P cS (dualC cT) → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P cT (U.1 v)) → ∀ v, (R.ioY t k U').1 v = hk _ P cS ((R.ioY t k U).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS t P k hG hkk hF cS cT hM U U' hU v
  classical
  have hθ : IsInfFam R.θ := hC.models.inf
  have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev).2.1 t P hG).1
  have hio := hC.chain.ioY t k (by omega)
  obtain ⟨hνH, hνF⟩ := haar_fd R hC.models t (k + 1) hkk
  obtain ⟨hμH, hμF⟩ := haar_fd R hC.models t k (by omega)
  have lo : ∀ j, j < D.R.m → (∀ κ ∈ hyp (Yc D j) P, κ ∈ levG _ (R.βY j) (R.datYt t j R.triv) ∧
        levChi _ (R.βY j) (R.datYt t j R.triv) κ = 1) ∧
      ∀ c, ∀ U ∈ Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)),
        postOn (R.MY j) (hk _ P c) U ∈ Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)) := by
    intro j hj
    obtain ⟨c, hb⟩ := hC.lev.βY j hj
    have h := GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D j) (R.βY j) (R.ΛY j) _ (R.datYt t j R.triv) hb P (by
      rw [Nat.cast_pow]
      exact fun h => hN (P.isPrime.mem_of_pow_mem _ h)) hG
    exact ⟨h.1, fun c U hU => h.2.2.2.2 _ R.θ (R.MY j) c hθ U hU⟩

  have hwm := (lo k (by omega)).2 cS _ ((mem_multT R.θ _ _ _ _).1 (R.ioY t k U).2)
  let w : R.CC t k := ⟨PiTensorProduct.lift (postOn (R.MY k) (hk _ P cS) (PiTensorProduct.lift.symm (R.ioY t k U).1)),
    (mem_multT R.θ _ _ _ _).2 (by simpa using hwm)⟩
  have hw : ∀ x, w.1 x = hk _ P cS ((R.ioY t k U).1 x) := by
    intro x
    have : w.1 = (hk _ P cS) ∘ₗ (R.ioY t k U).1 := PiTensorProduct.ext (MultilinearMap.ext fun y => by
      simp [w, postOn_apply])
    rw [this]; rfl
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT R.θ _ _ _ _).1 U.2)
  have key : ∀ φ x, (R.ioY t k U').1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) = w.1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) := by
    intro φ x
    have hvac := (GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t P hG).1 k hkk φ
    have e' : (R.ioY t k U').1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) =
        Lift.liftInt (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k φ) (U'.1 (PiTensorProduct.tprod ℂ x)) :=
      funext fun g => (hio.eq U' φ _ g).symm
    have e : (R.ioY t k U).1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) =
        Lift.liftInt (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k φ) (U.1 (PiTensorProduct.tprod ℂ x)) :=
      funext fun g => (hio.eq U φ _ g).symm
    have haut : IsAutFunSm R.θ _ (U.1 (PiTensorProduct.tprod ℂ x)) := by simpa using hmap.aut x
    have hcusp : IsCuspFun _ (U.1 (PiTensorProduct.tprod ℂ x)) := by simpa using hmap.cusp x
    have hlev : ∀ κ ∈ levS _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv), ∀ g, U.1 (PiTensorProduct.tprod ℂ x) (g * κ) =
        levChi _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) κ * U.1 (PiTensorProduct.tprod ℂ x) g := by
      simpa using hmap.lev x
    rw [hw, e', e, hU]
    refine GlobalTheory.T.thetaIntegral_vacuum_intertwines_sphericalHecke R.ψ _ _ _ _ (R.ωY t k) P (hC.chain.ωY t k hkk) _ _ hνH hνF hF cS cT hM _ hvac _ haut.left ?_ ?_
    · intro κ hκ h
      obtain ⟨h1, h2⟩ := (lo (k + 1) hkk).1 κ hκ
      rw [hlev κ h1, h2, one_mul]
    · intro g y hy
      refine hI _ _ R.θ R.ψ _ _ (R.ωY t k) hθ (hC.chain.ωY t k hkk) _ _ hνH hνF _ (rTr _ y (U.1 (PiTensorProduct.tprod ℂ x))) hvac.1
        (GlobalTheory.SphericalOps.isAutFunSm_rTr hy haut) ?_ g
      intro r C hC' μ 𝓕 hμ h𝓕 g'
      simp only [rTr, mul_assoc]
      exact hcusp r C hC' μ 𝓕 hμ h𝓕 (g' * y)
  obtain ⟨φ, x, hx⟩ : ∃ φ x, R.ItY k φ (PiTensorProduct.tprod ℂ x) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (hC.chain.ItY t k hkk).ne (LinearMap.ext fun φ => PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
    simpa using h φ x
  have h0 := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY k) _ _ _ _ hθ hμH hμF (hS.1 t k (by omega)) (R.ioY t k U' - w).1 (R.ioY t k U' - w).2 _ hx
    (by simp [key φ x])
  have h1 : (R.ioY t k U').1 = w.1 := sub_eq_zero.1 h0
  rw [h1, hw]

end GlobalTheory.ChainStepHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) k) V) (β : Type) [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (j₀ : β) (ψ : kˣ →* ℂˣ), IsSmooth ρ → IsSubquotient (piTensor fun j => (s j).ρ) (jac f ρ) → InSupport (s j₀).ρ ψ → InSupport ρ ψ := by
  first | exact @GlobalTheory.SuppStage.main | exact GlobalTheory.SuppStage.main | (intros; apply GlobalTheory.SuppStage.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_characterTwist_iff_localEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Loc.Om l)) (c : ↥Gw →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsdRAt P Bw c → (GlobalTheory.Pst.IsdRAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) ↔ GlobalTheory.Pst.IsdRAt P Bw r) := by
  first | exact @GlobalTheory.TwistBridgeDR.isdRAt_twist_iff | exact GlobalTheory.TwistBridgeDR.isdRAt_twist_iff | (intros; apply GlobalTheory.TwistBridgeDR.isdRAt_twist_iff <;> assumption)
end

